(* Tests for Chapter 8: the Hood-Melville real-time queue of Figure 8.1 (section 8.2.1),
   on the schedule of Exercise 8.2 and with the single diff field of Exercise 8.3. Plain
   OCaml, no test framework, matching the earlier chapters. The cons functor of Exercise
   8.4, the banker's deque of Figure 8.3 (section 8.4.2) and the red-black set carried
   into section 8.1 for Exercise 8.1 each have their own preamble further down.

   Figure 8.1 makes the promise of Figure 7.1, every operation in O(1) WORST-CASE time and
   still when used persistently, without laziness. Section 8.2 calls the technique global
   rebuilding: the queue keeps a working copy of its front, and answers every head and
   tail from it, while a secondary copy is built beside it a few steps at a time. The
   secondary copy is the rotation state. A rotation begins when the rear becomes one
   longer than the front, reverses f and r in parallel, then reverses f' onto r', by
   explicit steps. A tail taken meanwhile is buffered the cheapest way there is: it
   invalidates one element of the copy, so that the invalid elements are never placed on
   the answer list to begin with. Everything rests on the sizing argument of p.104. With
   |f| = m and |r| = m + 1 when the rotation begins, it needs at most 2m + 2 steps and the
   working copy lasts m deletions. Figure 8.1 takes two steps on every operation and
   finishes "at most m operations after it begins"; Exercise 8.2 trims that to two steps
   on the operation that starts the rotation and one on each operation after it, and asks
   for a proof that this is still on time. The implementation follows the exercise. There
   is no suspension, no memoisation and nothing to force.

   Exercise 8.3 then replaces the two length fields by one, the difference between them,
   which "may be inaccurate during rebuilding, but must be accurate by the time rebuilding
   is finished". From outside the seal that field is invisible, and its accuracy shows in
   one place only: the moment a rotation is triggered. A difference that is off when a
   rotation ends starts the next one with the wrong shape, one the reversing phase cannot
   finish, and the elements in it are lost. So every check below that runs past a second
   rotation is a check on the difference, and the random runs of the contract are the
   sharpest of them.

   That changes what the clock can see and what persistence can lean on. In test_ch7
   allocation stood in for suspensions being forced. Here it is the work itself: a step is
   a cons or two and a fresh state, an operation is one or two of them and a fresh queue,
   and the only way for an operation to be expensive is to allocate. Persistence has
   nothing to lean on at all: a version reused pays exactly what it paid the first time,
   which is why p.102 can say that "arbitrarily repeating operations has no effect on the
   time bounds". So the checks are those of test_ch7. The behavioural contract first, with
   one item added: the sizing argument above asserted from outside, by exhausting the
   working copy the moment a rotation begins, which under the trimmed schedule is the
   claim of Exercise 8.2 itself. Then every operation of a sequence on the clock by itself
   with the DEAREST asserted, at two sizes a hundred times apart, and the same from every
   version of a build and of a drain and over a random trace of random earlier versions.
   The tests reach the queue only as a functor argument of type QUEUE, so nothing here can
   see the rotation state. Whether the clock can see a lump at all is checked over the
   batched queue of Figure 5.2, which section 8.1 presents as the batched-rebuilding
   version of this very design. *)

open Okasaki.Ch8

(* ------------------------------------------------------------------ harness *)

let checks = ref 0
let failures = ref 0

let check name cond =
  incr checks;
  if not cond
  then (
    incr failures;
    Printf.printf "  FAIL  %s\n" name)
;;

let check_eq name ~expect ~actual to_string =
  incr checks;
  if expect <> actual
  then (
    incr failures;
    Printf.printf
      "  FAIL  %s: expected %s, got %s\n"
      name
      (to_string expect)
      (to_string actual))
;;

let check_int name ~expect ~actual = check_eq name ~expect ~actual string_of_int

(* A refusal on the empty structure: Failure "<op>: empty queue", or "<op>: empty deque"
   from the deques of section 8.4, whose messages say what they are. *)
let check_refuses name op f =
  incr checks;
  let wanted =
    Printf.sprintf "Failure \"%s: empty queue\" or \"%s: empty deque\"" op op
  in
  match f () with
  | _ ->
    incr failures;
    Printf.printf "  FAIL  %s: expected %s, got no exception\n" name wanted
  | exception Failure msg when msg = op ^ ": empty queue" || msg = op ^ ": empty deque" ->
    ()
  | exception e ->
    incr failures;
    Printf.printf "  FAIL  %s: expected %s, got %s\n" name wanted (Printexc.to_string e)
;;

(* Run [f], and hand its result to [k] if it returned one. An exception is that one
   check's failure and not the section's, so the checks after it still get to run. *)
let surviving name f k =
  match f () with
  | v -> k v
  | exception e ->
    incr checks;
    incr failures;
    Printf.printf "  FAIL  %s: raised %s\n" name (Printexc.to_string e)
;;

let section name = Printf.printf "%s\n" name
let string_of_int_list l = "[" ^ String.concat ";" (List.map string_of_int l) ^ "]"
let upto n = List.init n Fun.id

(* head/tail to exhaustion. A queue whose tail does not advance would never come to an
   end, and neither would the list this builds, so a drain past any size used here gives
   up and raises: the checks around it report that as the failure it is. *)
let drain_limit = 100_000

let drain_with ~is_empty ~head ~tail q =
  let rec go n acc q =
    if is_empty q
    then List.rev acc
    else if n = drain_limit
    then failwith "drain: no end in sight"
    else go (n + 1) (head q :: acc) (tail q)
  in
  go 0 [] q
;;

(* ---------------------------------------------------------------- the clock *)

(* Words allocated by [f], read before and after. Sys.opaque_identity stops the optimiser
   discarding the result and with it the allocation being measured. The clock counts in
   integers: a float reading would box, and the two words of the box would land inside the
   measurement. *)
let words () = int_of_float (Gc.minor_words ())

let cost_on clock f =
  let before = clock () in
  let r = Sys.opaque_identity (f ()) in
  r, float_of_int (clock () - before)
;;

let cost f = cost_on words f

(* The most a single operation may allocate, in words. Every operation rebuilds the queue
   record once on the way in and once on the way out of its steps, 5 words each now that
   Exercise 8.3 has left it four fields, and a snoc adds a cons onto the rear. Between
   rotations that is all of it. During one, a step allocates a fresh state, 6 words while
   reversing with two conses pushed, 4 words while appending with one, and the 3-word pair
   that carries the difference through the step. Under Exercise 8.2 an operation takes one
   step, and the operation that begins a rotation takes two, and builds a third queue
   record and the initial state on top of them. The dearest operations measured here are
   those: a snoc at 54 words, a tail at 51. CONSTANT leaves room for those and for the
   probe's own noise, and is nowhere near an operation that is really linear: the reverse
   that batched rebuilding runs in one tail costs three words a cons, and at the sizes
   used here that is out by a factor of thirty. *)
let constant = 96.0

(* ---------------------------------------------------- shared queue contract *)

module Queue_tests (Q : QUEUE) = struct
  let of_list xs = List.fold_left Q.snoc Q.empty xs

  (* That this returns the elements in the order they were snoc'ed is the whole
     behavioural specification of a queue. *)
  let drain q = drain_with ~is_empty:Q.is_empty ~head:Q.head ~tail:Q.tail q

  let run_contract name =
    let t label = Printf.sprintf "%s: %s" name label in
    let eq label expect q =
      surviving
        (t label)
        (fun () -> drain q)
        (fun actual -> check_eq (t label) ~expect ~actual string_of_int_list)
    in
    let head_is label expect q =
      surviving
        (t label)
        (fun () -> Q.head (q ()))
        (fun actual -> check_int (t label) ~expect ~actual)
    in
    check (t "empty is empty") (Q.is_empty Q.empty);
    check (t "a singleton is not empty") (not (Q.is_empty (Q.snoc Q.empty 1)));
    check_refuses (t "head on empty raises") "head" (fun () -> Q.head Q.empty);
    check_refuses (t "tail on empty raises") "tail" (fun () ->
      ignore (Q.is_empty (Q.tail Q.empty)));
    (* The two places the invariant can be lost. is_empty reads lenf, which during a
       rotation counts the front under construction, while head reads the working copy. A
       rotation that never starts, stalls half way, or finishes late leaves the queue
       reporting non-empty with elements it cannot produce: head raises on a queue that
       has elements in it. The smallest rotations, of zero and one element, are the ones
       in which an off-by-one in the trigger shows first. *)
    head_is "snoc onto the empty queue makes its element the head" 7 (fun () ->
      Q.snoc Q.empty 7);
    head_is "tail past the last front element moves on to the rear" 2 (fun () ->
      Q.tail (of_list [ 1; 2; 3 ]));
    head_is "the second rotation delivers its rear" 2 (fun () ->
      Q.tail (of_list [ 1; 2 ]));
    eq "first in, first out" [ 1; 2; 3; 4; 5; 6; 7 ] (of_list [ 1; 2; 3; 4; 5; 6; 7 ]);
    eq "equal elements are all kept, in order" [ 7; 7; 1; 7 ] (of_list [ 7; 7; 1; 7 ]);
    (* Emptiness reached by draining must be as good as the [empty] it started from. *)
    surviving
      (t "a queue can be drained to nothing")
      (fun () -> Q.tail (Q.tail (of_list [ 1; 2 ])))
      (fun drained ->
        check (t "a queue drained to nothing is empty") (Q.is_empty drained);
        check_refuses (t "head on a drained queue raises") "head" (fun () ->
          Q.head drained);
        eq "a drained queue can be refilled" [ 8; 9 ] (Q.snoc (Q.snoc drained 8) 9));
    (* The sizing argument of p.104, from outside. A rotation begins when |r| = |f| + 1,
       with |f| = m, and "the working copy of the front list will be exhausted after just
       m deletions", so the new front must be complete by then. From the empty queue,
       snocs alone begin a rotation at sizes 1, 3, 7, ..., 2^k - 1: a rotation of m ends
       with an empty rear and a front of 2m + 1, and the next begins on the snoc that
       makes the rear one longer than that. So a build of 2m + 1 elements, m = 2^k - 1,
       ends on the very snoc that starts a rotation of m, and the working copy is the old
       front of m elements. Take m tails at once and ask for the head: the answer has to
       come from the rotation's result, and there is no later moment at which it may
       arrive. Under the schedule of Exercise 8.2 this is the exercise's own claim, with
       the tails arriving as fast as they can; a schedule one step short at the start
       fails it at m = 0 already. No check outside the seal can be sharper than this. *)
    let late = ref [] in
    for k = 0 to 12 do
      let m = (1 lsl k) - 1 in
      let n = (2 * m) + 1 in
      let expect = List.init (m + 1) (fun i -> m + 1 + i) in
      let on_time =
        try
          let q = ref (of_list (List.init n (fun i -> i + 1))) in
          for _ = 1 to m do
            q := Q.tail !q
          done;
          (not (Q.is_empty !q)) && Q.head !q = m + 1 && drain !q = expect
        with
        | Failure _ -> false
      in
      if not on_time then late := m :: !late
    done;
    check_eq
      (t "the new front is ready when the working copy runs out, m = 0, 1, 3, ..., 4095")
      ~expect:[]
      ~actual:(List.rev !late)
      string_of_int_list;
    (* Randomised, against the obvious model: a list, snoc at the back, tail at the front.
       Checked after every operation and not only at the end, because a lost invariant
       shows up as a wrong is_empty or head long before it shows up in a drain. *)
    Random.init 20260925;
    let bad_empty = ref 0
    and bad_head = ref 0
    and bad_drain = ref 0
    and raised = ref 0 in
    for _ = 0 to 299 do
      let q = ref Q.empty
      and model = ref [] in
      (* The model is never asked for the head or tail of nothing, so any Failure in here
         is the queue refusing an operation it owes. *)
      try
        for i = 0 to 59 do
          if !model = [] || Random.int 3 > 0
          then (
            q := Q.snoc !q i;
            model := !model @ [ i ])
          else (
            q := Q.tail !q;
            model := List.tl !model);
          if Q.is_empty !q <> (!model = []) then incr bad_empty;
          match !model with
          | x :: _ when Q.head !q <> x -> incr bad_head
          | _ -> ()
        done;
        if drain !q <> !model then incr bad_drain
      with
      | Failure _ -> incr raised
    done;
    check_int
      (t "no operation raises on a non-empty queue, 300 random runs")
      ~expect:0
      ~actual:!raised;
    check_int
      (t "is_empty agrees with a list model, 300 random runs")
      ~expect:0
      ~actual:!bad_empty;
    check_int
      (t "head agrees with a list model, 300 random runs")
      ~expect:0
      ~actual:!bad_head;
    check_int
      (t "drain agrees with a list model, 300 random runs")
      ~expect:0
      ~actual:!bad_drain;
    (* Persistence: no operation may disturb its operand, so every version ever built
       stays correct, and two futures of one queue do not see each other. A rotation in
       progress is the case that matters: two futures of a queue caught mid-rotation each
       carry the state on by their own steps, and neither may see the other's. *)
    surviving
      (t "every earlier version can still be used")
      (fun () ->
        let versions = List.init 20 (fun i -> of_list (upto i)) in
        List.iter
          (fun v ->
            ignore (Q.snoc v 99);
            if not (Q.is_empty v) then ignore (Q.tail v))
          versions;
        List.mapi (fun i v -> if drain v = upto i then 0 else 1) versions
        |> List.fold_left ( + ) 0)
      (fun stale ->
        check_int (t "every earlier version stays correct") ~expect:0 ~actual:stale);
    let q = of_list [ 1; 2; 3 ] in
    let a = Q.snoc q 4
    and b = Q.snoc q 5 in
    eq "one future of a shared queue" [ 1; 2; 3; 4 ] a;
    eq "does not leak into the other" [ 1; 2; 3; 5 ] b;
    let q = of_list (upto 7) in
    let a = drain (Q.snoc (Q.tail q) 7)
    and b = drain (Q.tail (Q.tail q)) in
    check_eq
      (t "one future of a queue mid-rotation")
      ~expect:[ 1; 2; 3; 4; 5; 6; 7 ]
      ~actual:a
      string_of_int_list;
    check_eq
      (t "does not leak into the other, mid-rotation")
      ~expect:[ 2; 3; 4; 5; 6 ]
      ~actual:b
      string_of_int_list
  ;;
end

(* ------------------------------------------ every operation on its own clock *)

(* A sequence is data, built before anything is measured, so that building it cannot land
   on the clock. *)
type op =
  | Snoc of int
  | Tail
  | Head

let describe = function
  | Snoc x -> Printf.sprintf "snoc %d" x
  | Tail -> "tail"
  | Head -> "head"
;;

module Worst_case (Q : QUEUE) = struct
  let of_list xs = List.fold_left Q.snoc Q.empty xs

  (* Runs [ops] from the empty queue with every operation on the clock by itself, and
     reports the dearest: its index, what it was, and what it cost. The queue is threaded
     through a reference and each closure is built before its clock starts, so nothing but
     the operation is measured. *)
  let dearest ops =
    let q = ref Q.empty
    and sum = ref 0
    and dear = ref (0, Tail, 0.0) in
    Array.iteri
      (fun i op ->
        let c =
          match op with
          | Snoc x ->
            let q', c = cost (fun () -> Q.snoc !q x) in
            q := q';
            c
          | Tail ->
            let q', c = cost (fun () -> Q.tail !q) in
            q := q';
            c
          | Head ->
            let x, c = cost (fun () -> Q.head !q) in
            sum := !sum + x;
            c
        in
        let _, _, worst = !dear in
        if c > worst then dear := i, op, c)
      ops;
    ignore (Sys.opaque_identity !q);
    ignore (Sys.opaque_identity !sum);
    !dear
  ;;

  (* ----------------------------------------- sequences: one thread, from empty *)

  (* The sequences of test_ch6 and test_ch7, as data. They differ in where the rotations
     fall: ever larger ones at ever longer intervals, a tiny one at every step, or two
     snocs to every tail so the front never stops growing. In Figure 8.1 a head does no
     work at all, it reads the working copy; the heads sequence is kept so that the clock
     says so. *)
  let fill_then_drain n =
    Array.init (2 * n) (fun i -> if i < n then Snoc (i + 1) else Tail)
  ;;

  let alternate n =
    Array.init (2 * n) (fun i -> if i mod 2 = 0 then Snoc ((i / 2) + 1) else Tail)
  ;;

  let two_snocs_per_tail n =
    Array.init (3 * n) (fun i -> if i mod 3 = 2 then Tail else Snoc ((i / 3) + 1))
  ;;

  let snoc_then_head n =
    Array.init (2 * n) (fun i -> if i mod 2 = 0 then Snoc ((i / 2) + 1) else Head)
  ;;

  let random_mix n =
    Random.init 20260925;
    let size = ref 0 in
    Array.init n (fun i ->
      if !size = 0 || Random.int 3 > 0
      then (
        incr size;
        Snoc i)
      else (
        decr size;
        Tail))
  ;;

  let sequences =
    [ "n snocs then n tails", fill_then_drain
    ; "snoc and tail alternating", alternate
    ; "two snocs to every tail", two_snocs_per_tail
    ; "a head after every snoc", snoc_then_head
    ; "a random mix", random_mix
    ]
  ;;

  (* O(1) worst-case, asserted the only way a worst-case bound can be: on the dearest
     single operation. True if every sequence stayed within the bound. The large size is
     guarded on the small one, as the earlier chapters guard theirs: an operation that is
     secretly linear makes a sequence quadratic, and at n = 100_000 that is not a failure
     but a hang. *)
  let run_sequences name =
    let t label = Printf.sprintf "%s: %s" name label in
    let ok = ref true in
    List.iter
      (fun (sequence, ops) ->
        let within label n =
          let i, op, c = dearest (ops n) in
          let fine = c <= constant in
          check
            (t
               (Printf.sprintf
                  "%s, %s: dearest is #%d (%s) at %.0f words, n=%d"
                  sequence
                  label
                  i
                  (describe op)
                  c
                  n))
            fine;
          fine
        in
        if not (within "O(1) worst-case" 1_000)
        then (
          ok := false;
          Printf.printf
            "  SKIP  %s: %s at n=100000 -- it is not O(1) worst-case at n=1000\n"
            name
            sequence)
        else if not (within "still O(1) worst-case, a hundred times longer" 100_000)
        then ok := false)
      sequences;
    !ok
  ;;

  (* -------------------------------------- versions: several futures of one queue *)

  (* n snocs, every version kept, and every snoc on the clock: the first future of each
     version of a build. A build's versions are the ones on the brink of a rotation, and
     the snoc that makes the next version is the one that starts it. *)
  let build n =
    let v = Array.make (n + 1) Q.empty
    and dear = ref (0, 0.0) in
    for i = 1 to n do
      let q, c = cost (fun () -> Q.snoc v.(i - 1) i) in
      v.(i) <- q;
      if c > snd !dear then dear := i, c
    done;
    v, !dear
  ;;

  (* The same for a drain of a snoc-built queue: every version kept, every tail on the
     clock. In Figure 5.2 one of these tails ran the reverse. *)
  let drain n =
    let v = Array.make (n + 1) Q.empty
    and dear = ref (0, 0.0) in
    v.(0) <- of_list (upto n);
    for i = 1 to n do
      let q, c = cost (fun () -> Q.tail v.(i - 1)) in
      v.(i) <- q;
      if c > snd !dear then dear := i, c
    done;
    v, !dear
  ;;

  (* One operation of each kind from every version in [v] whose size ([size k] for the
     k-th) allows it, each on the clock, and each a second future of its version: the
     future that built the array was the first. For each kind, the version it was dearest
     from and what it cost there. *)
  let short_futures v ~size =
    let opaque x = ignore (Sys.opaque_identity x) in
    let runs =
      [ "tail", (fun q -> opaque (Q.tail q)), 1
      ; "head", (fun q -> opaque (Q.head q)), 1
      ; "snoc", (fun q -> opaque (Q.snoc q 0)), 0
      ]
    in
    List.map
      (fun (run, f, needs) ->
        let worst = ref (0, 0.0) in
        Array.iteri
          (fun k q ->
            if size k >= needs
            then (
              let _, c = cost (fun () -> f q) in
              if c > snd !worst then worst := k, c))
          v;
        run, fst !worst, snd !worst)
      runs
  ;;

  (* The whole drain, d times over from the same starting queue, every tail on the clock.
     p.65 of Chapter 6 called this the branch point where "memoization does not help at
     all". Here there is nothing to memoise and nothing that could have been: each round
     runs its own rotations, step by step, and pays as it goes. *)
  let repeated_drain ~n ~d =
    let q0 = of_list (upto n)
    and dear = ref (0, 0.0) in
    for round = 1 to d do
      let q = ref q0 in
      for _ = 1 to n do
        let q', c = cost (fun () -> Q.tail !q) in
        q := q';
        if c > snd !dear then dear := round, c
      done;
      ignore (Sys.opaque_identity !q)
    done;
    !dear
  ;;

  (* n operations, each applied to a version chosen at random among all built so far, and
     each on the clock. *)
  let random_trace n =
    Random.init 20260926;
    let from = Array.init n (fun i -> Random.int (i + 1)) in
    let wants_snoc = Array.init n (fun _ -> Random.int 3 > 0) in
    let v = Array.make (n + 1) Q.empty
    and dear = ref (0, Tail, 0.0) in
    for i = 1 to n do
      let q = v.(from.(i - 1)) in
      let op = if wants_snoc.(i - 1) || Q.is_empty q then Snoc i else Tail in
      let q', c =
        match op with
        | Snoc x -> cost (fun () -> Q.snoc q x)
        | Tail | Head -> cost (fun () -> Q.tail q)
      in
      v.(i) <- q';
      let _, _, worst = !dear in
      if c > worst then dear := i, op, c
    done;
    ignore (Sys.opaque_identity v);
    !dear
  ;;

  let run_versions name =
    let t label = Printf.sprintf "%s: %s" name label in
    let within label (k, c) =
      check
        (t (Printf.sprintf "%s, dearest from #%d at %.0f words" label k c))
        (c <= constant)
    in
    let n = 2_000 in
    let v, dear = build n in
    within (Printf.sprintf "the snoc that makes each version of a build of %d" n) dear;
    List.iter
      (fun (run, k, c) ->
        within (Printf.sprintf "%s from every version of a build of %d" run n) (k, c))
      (short_futures v ~size:Fun.id);
    let n = 1_000 in
    let v, dear = drain n in
    within (Printf.sprintf "the tail that makes each version of a drain of %d" n) dear;
    List.iter
      (fun (run, k, c) ->
        within (Printf.sprintf "%s from every version of a drain of %d" run n) (k, c))
      (short_futures v ~size:(fun k -> n - k));
    within
      (Printf.sprintf
         "the whole drain of %d repeated 10 times from one queue, dearest round"
         n)
      (repeated_drain ~n ~d:10);
    let n = 100_000 in
    let i, op, c = random_trace n in
    check
      (t
         (Printf.sprintf
            "a random trace of %d operations, each on a random earlier version, dearest \
             is #%d (%s) at %.0f words"
            n
            i
            (describe op)
            c))
      (c <= constant)
  ;;
end

(* -------------------------------------------------------------------- guard *)

(* Whether the clock can see a lump sum at all. Section 8.1 presents the batched queue of
   Figure 5.2 as batched rebuilding: the same two lists, with the rotation run all at once
   by the tail that empties the front. The probe above, run over it, must find that tail:
   in a drain of a queue built by n snocs it reverses n - 1 elements in one go, three
   words a cons. Without this, every check on the Hood-Melville queue could pass by
   measuring nothing. *)
module Control = Worst_case (Okasaki.Ch5.BatchedQueue)

let test_guard () =
  let n = 1_000 in
  let i, op, c = Control.dearest (Control.fill_then_drain n) in
  check
    (Printf.sprintf
       "guard: the same probe over Figure 5.2's queue sees its reverse, #%d (%s) at %.0f \
        words in a fill and drain of %d"
       i
       (describe op)
       c
       n)
    (op = Tail && c >= float_of_int n /. 2.)
;;

(* ---------------------------------------------------- HoodMelvilleQueue (8.2.1) *)

module Contract = Queue_tests (HoodMelvilleQueue)
module Costs = Worst_case (HoodMelvilleQueue)

(* What a queue costs means nothing until it behaves like one, and a queue that raises
   half way through a sequence would take the rest of the section down with it. *)
let test_hood_melville () =
  section "HoodMelvilleQueue (8.2.1)";
  let before = !failures in
  Contract.run_contract "HoodMelvilleQueue";
  if !failures > before
  then
    Printf.printf
      "  SKIP  HoodMelvilleQueue: cost checks -- the contract above does not hold\n"
  else (
    test_guard ();
    if Costs.run_sequences "HoodMelvilleQueue"
    then Costs.run_versions "HoodMelvilleQueue, persistently"
    else
      Printf.printf
        "  SKIP  HoodMelvilleQueue: persistence checks -- not real-time in one thread\n")
;;

(* ------------------------------------- ConstantTimeConsQueue (Exercise 8.4) *)

(* Section 8.4 turns to deques, and 8.4.1 remarks that giving a queue cons, insertion at
   the front, is trivial for the banker's and real-time queues of Chapters 6 and 7: the
   element goes onto the front stream. The Hood-Melville queue has no such place, its
   front is a working copy with a rotation state under construction beside it, so Exercise
   8.4 asks for a functor instead. Any queue Q is paired with a plain list: cons pushes
   onto the list, head and tail serve from the list "whenever it is non-empty", and snoc
   goes through to Q. The pair is an output-restricted deque, and the one requirement the
   exercise adds to the queue contract is that cons is constant-time.

   Two things follow, and both are checked. The pair is still a queue, so the contract and
   the cost probes above run over it unchanged, over the Hood-Melville queue, whose
   worst-case bounds the wrapper must not spoil: it adds one pair to every operation. And
   cons is constant for ANY Q exactly when it never calls into Q at all, which is what the
   exercise's "insert elements into the new list" comes to. That is checked twice: by
   counting the calls the wrapper makes into a queue it was given, and on the clock over
   the batched queue of Figure 5.2, whose own tail is linear. The second is also the
   guard: the same run shows the clock still sees that reverse through the wrapper, so the
   wrapper's cost checks do not pass by measuring nothing. *)

(* The calls a wrapper makes into the queue it was given. *)
type calls =
  { mutable is_empty : int
  ; mutable snoc : int
  ; mutable head : int
  ; mutable tail : int
  }

let inner = { is_empty = 0; snoc = 0; head = 0; tail = 0 }

let reset_inner () =
  inner.is_empty <- 0;
  inner.snoc <- 0;
  inner.head <- 0;
  inner.tail <- 0
;;

let inner_calls () = inner.is_empty + inner.snoc + inner.head + inner.tail

(* The Hood-Melville queue with its calls counted. *)
module Counted : QUEUE = struct
  type 'a queue = 'a HoodMelvilleQueue.queue

  let empty = HoodMelvilleQueue.empty

  let is_empty q =
    inner.is_empty <- inner.is_empty + 1;
    HoodMelvilleQueue.is_empty q
  ;;

  let snoc q x =
    inner.snoc <- inner.snoc + 1;
    HoodMelvilleQueue.snoc q x
  ;;

  let head q =
    inner.head <- inner.head + 1;
    HoodMelvilleQueue.head q
  ;;

  let tail q =
    inner.tail <- inner.tail + 1;
    HoodMelvilleQueue.tail q
  ;;
end

module Delegation = ConstantTimeConsQueue (Counted)

(* The division of labour the exercise states, read off the counters. *)
let test_delegation () =
  let module Q = Delegation in
  let t label = Printf.sprintf "ConstantTimeConsQueue: %s" label in
  let five = List.fold_left Q.snoc Q.empty (upto 5) in
  reset_inner ();
  let three = Q.cons 2 (Q.cons 1 (Q.cons 0 five)) in
  ignore (Sys.opaque_identity (Q.cons 0 Q.empty));
  check_int
    (t
       "cons makes no call into the inner queue: 3 conses onto 5 snocs, and one onto \
        empty")
    ~expect:0
    ~actual:(inner_calls ());
  reset_inner ();
  let q = ref three in
  for _ = 1 to 3 do
    ignore (Sys.opaque_identity (Q.head !q));
    q := Q.tail !q
  done;
  check_int
    (t
       "head and tail serve from the list while it has elements: 3 heads and 3 tails \
        after 3 conses remove nothing from the inner queue")
    ~expect:0
    ~actual:(inner.head + inner.tail);
  reset_inner ();
  ignore (Sys.opaque_identity (Q.head !q));
  q := Q.tail !q;
  check_int
    (t
       "and from the inner queue once the list is used up: the 4th head is one inner head")
    ~expect:1
    ~actual:inner.head;
  check_int
    (t
       "and from the inner queue once the list is used up: the 4th tail is one inner tail")
    ~expect:1
    ~actual:inner.tail;
  ignore (Sys.opaque_identity !q)
;;

module Cons_tests (Q : QUEUE_WITH_CONS) = struct
  let of_list xs = List.fold_left Q.snoc Q.empty xs
  let drain q = drain_with ~is_empty:Q.is_empty ~head:Q.head ~tail:Q.tail q

  (* The elements cons'ed onto the empty queue in order, so the last is in front. *)
  let cons_list xs = List.fold_left (fun q x -> Q.cons x q) Q.empty xs

  let run_contract name =
    let t label = Printf.sprintf "%s: %s" name label in
    let eq label expect q =
      surviving
        (t label)
        (fun () -> drain q)
        (fun actual -> check_eq (t label) ~expect ~actual string_of_int_list)
    in
    let head_is label expect q =
      surviving
        (t label)
        (fun () -> Q.head (q ()))
        (fun actual -> check_int (t label) ~expect ~actual)
    in
    check
      (t "cons onto the empty queue is not empty")
      (not (Q.is_empty (Q.cons 1 Q.empty)));
    head_is "cons onto the empty queue makes its element the head" 7 (fun () ->
      Q.cons 7 Q.empty);
    eq
      "cons puts its element in front of everything snoc'ed"
      [ 0; 1; 2; 3 ]
      (Q.cons 0 (of_list [ 1; 2; 3 ]));
    eq "the last element cons'ed is the first out" [ 3; 2; 1 ] (cons_list [ 1; 2; 3 ]);
    eq
      "snoc after cons still goes to the back"
      [ 0; 1; 2 ]
      (Q.snoc (Q.cons 0 (of_list [ 1 ])) 2);
    eq
      "cons and snoc interleaved"
      [ 4; 2; 1; 3; 5 ]
      (Q.snoc (Q.cons 4 (Q.snoc (Q.cons 2 (of_list [ 1 ])) 3)) 5);
    (* The seam between the two halves, crossed both ways. A queue that is empty in one
       half and not the other is where a wrapper is most easily wrong about itself. *)
    head_is "tail past the cons'ed elements moves on to the snoc'ed" 1 (fun () ->
      Q.tail (Q.cons 0 (of_list [ 1; 2 ])));
    surviving
      (t "tail of the one cons'ed element")
      (fun () -> Q.tail (Q.cons 0 (Q.snoc Q.empty 1)))
      (fun q ->
        check
          (t "leaves the snoc'ed element behind, so the queue is not empty")
          (not (Q.is_empty q));
        eq "and that element is the head" [ 1 ] q);
    surviving
      (t "a queue drained to nothing")
      (fun () -> Q.tail (Q.tail (of_list [ 1; 2 ])))
      (fun drained ->
        eq "takes a cons" [ 5 ] (Q.cons 5 drained);
        eq "takes a cons and then a snoc" [ 5; 6 ] (Q.snoc (Q.cons 5 drained) 6);
        check
          (t "and is empty again after a cons and a tail")
          (Q.is_empty (Q.tail (Q.cons 5 drained))));
    check_refuses
      (t "head after the tail of the only cons'ed element raises")
      "head"
      (fun () -> Q.head (Q.tail (Q.cons 1 Q.empty)));
    (* Randomised, against the obvious model: a list, cons at the front, snoc at the back,
       tail at the front. Checked after every operation, as the queue contract does. *)
    Random.init 20260926;
    let bad_empty = ref 0
    and bad_head = ref 0
    and bad_drain = ref 0
    and raised = ref 0 in
    for _ = 0 to 299 do
      let q = ref Q.empty
      and model = ref [] in
      (* The model is never asked for the head or tail of nothing, so any Failure in here
         is the queue refusing an operation it owes. *)
      try
        for i = 0 to 59 do
          (match if !model = [] then Random.int 2 else Random.int 3 with
           | 0 ->
             q := Q.cons i !q;
             model := i :: !model
           | 1 ->
             q := Q.snoc !q i;
             model := !model @ [ i ]
           | _ ->
             q := Q.tail !q;
             model := List.tl !model);
          if Q.is_empty !q <> (!model = []) then incr bad_empty;
          match !model with
          | x :: _ when Q.head !q <> x -> incr bad_head
          | _ -> ()
        done;
        if drain !q <> !model then incr bad_drain
      with
      | Failure _ -> incr raised
    done;
    check_int
      (t "no operation raises on a non-empty queue, 300 random runs with cons")
      ~expect:0
      ~actual:!raised;
    check_int
      (t "is_empty agrees with a list model, 300 random runs with cons")
      ~expect:0
      ~actual:!bad_empty;
    check_int
      (t "head agrees with a list model, 300 random runs with cons")
      ~expect:0
      ~actual:!bad_head;
    check_int
      (t "drain agrees with a list model, 300 random runs with cons")
      ~expect:0
      ~actual:!bad_drain;
    (* Persistence: a cons may not disturb its operand, and a tail taken from a cons'ed
       queue in one future leaves the element in place in the other. *)
    let q = of_list [ 1; 2; 3 ] in
    let a = Q.cons 0 q
    and b = Q.cons 9 q in
    eq "one future of a shared queue, by cons" [ 0; 1; 2; 3 ] a;
    eq "does not leak into the other" [ 9; 1; 2; 3 ] b;
    eq "nor into the queue they came from" [ 1; 2; 3 ] q;
    let c = Q.cons 0 q in
    eq "a tail taken in one future of a cons'ed queue" [ 1; 2; 3 ] (Q.tail c);
    eq "leaves the cons'ed element in the other" [ 0; 1; 2; 3 ] c;
    surviving
      (t "every earlier version of a cons-build can still be used")
      (fun () ->
        let versions = List.init 20 (fun i -> cons_list (upto i)) in
        List.iter
          (fun v ->
            ignore (Q.cons 99 v);
            ignore (Q.snoc v 99);
            if not (Q.is_empty v) then ignore (Q.tail v))
          versions;
        List.mapi (fun i v -> if drain v = List.rev (upto i) then 0 else 1) versions
        |> List.fold_left ( + ) 0)
      (fun stale ->
        check_int
          (t "every earlier version of a cons-build stays correct")
          ~expect:0
          ~actual:stale)
  ;;

  (* ------------------------------------------------------------- on the clock *)

  type op =
    | Cons of int
    | Snoc of int
    | Tail
    | Head

  let describe = function
    | Cons x -> Printf.sprintf "cons %d" x
    | Snoc x -> Printf.sprintf "snoc %d" x
    | Tail -> "tail"
    | Head -> "head"
  ;;

  (* Runs [ops] from the empty queue with every operation on the clock by itself, and
     returns what each one cost. *)
  let costs ops =
    let q = ref Q.empty
    and sum = ref 0 in
    let costs =
      Array.map
        (fun op ->
          match op with
          | Cons x ->
            let q', c = cost (fun () -> Q.cons x !q) in
            q := q';
            c
          | Snoc x ->
            let q', c = cost (fun () -> Q.snoc !q x) in
            q := q';
            c
          | Tail ->
            let q', c = cost (fun () -> Q.tail !q) in
            q := q';
            c
          | Head ->
            let x, c = cost (fun () -> Q.head !q) in
            sum := !sum + x;
            c)
        ops
    in
    ignore (Sys.opaque_identity !q);
    ignore (Sys.opaque_identity !sum);
    costs
  ;;

  (* The dearest of the operations [among] picks out: its index, what it was, its cost. *)
  let dearest among ops costs =
    let dear = ref (0, Tail, -1.0) in
    Array.iteri
      (fun i c ->
        let _, _, worst = !dear in
        if among ops.(i) && c > worst then dear := i, ops.(i), c)
      costs;
    !dear
  ;;

  let any _ = true

  let a_cons = function
    | Cons _ -> true
    | _ -> false
  ;;

  let a_tail = function
    | Tail -> true
    | _ -> false
  ;;

  (* The list alone: n conses, then n tails. *)
  let cons_then_drain n =
    Array.init (2 * n) (fun i -> if i < n then Cons (n - i) else Tail)
  ;;

  (* n snocs, then n conses, then 2n tails: the tails cross from the list into the inner
     queue half way through, at index 3n. *)
  let both_then_drain n =
    Array.init (4 * n) (fun i ->
      if i < n then Snoc (n + 1 + i) else if i < 2 * n then Cons (n - i + n) else Tail)
  ;;

  (* Two snocs and a cons, then two tails, over and over: the seam is crossed on every
     round while the inner queue grows and rotates underneath. *)
  let two_snocs_a_cons_two_tails n =
    Array.init (5 * n) (fun i ->
      match i mod 5 with
      | 0 | 1 -> Snoc i
      | 2 -> Cons i
      | _ -> Tail)
  ;;

  let head_after_each n =
    Array.init (4 * n) (fun i ->
      match i mod 4 with
      | 0 -> Cons i
      | 2 -> Snoc i
      | _ -> Head)
  ;;

  let random_mix n =
    Random.init 20260926;
    let size = ref 0 in
    Array.init n (fun i ->
      match if !size = 0 then Random.int 2 else Random.int 4 with
      | 0 ->
        incr size;
        Cons i
      | 1 ->
        incr size;
        Snoc i
      | 2 ->
        decr size;
        Tail
      | _ -> Head)
  ;;

  let sequences =
    [ "n conses then n tails", cons_then_drain
    ; "n snocs, n conses, then 2n tails", both_then_drain
    ; "two snocs and a cons to every two tails", two_snocs_a_cons_two_tails
    ; "a head after every cons and every snoc", head_after_each
    ; "a random mix of cons, snoc, tail and head", random_mix
    ]
  ;;

  (* As Worst_case.run_sequences, with cons in the sequences. *)
  let run_sequences name =
    let t label = Printf.sprintf "%s: %s" name label in
    let ok = ref true in
    List.iter
      (fun (sequence, ops) ->
        let within label n =
          let ops = ops n in
          let i, op, c = dearest any ops (costs ops) in
          let fine = c <= constant in
          check
            (t
               (Printf.sprintf
                  "%s, %s: dearest is #%d (%s) at %.0f words, n=%d"
                  sequence
                  label
                  i
                  (describe op)
                  c
                  n))
            fine;
          fine
        in
        if not (within "O(1) worst-case" 1_000)
        then (
          ok := false;
          Printf.printf
            "  SKIP  %s: %s at n=100000 -- it is not O(1) worst-case at n=1000\n"
            name
            sequence)
        else if not (within "still O(1) worst-case, a hundred times longer" 100_000)
        then ok := false)
      sequences;
    !ok
  ;;

  module W = Worst_case (Q)

  (* Every version kept and every cons on the clock, from three kinds of version: each
     step of a build by cons; each step of a build by snoc, which catches the inner queue
     in every phase of a rotation; and each step of a drain. Then the other operations as
     a second future of every version of the cons-build. *)
  let run_versions name =
    let t label = Printf.sprintf "%s: %s" name label in
    let within label (k, c) =
      check
        (t (Printf.sprintf "%s, dearest from #%d at %.0f words" label k c))
        (c <= constant)
    in
    let cons_from v =
      let dear = ref (0, 0.0) in
      Array.iteri
        (fun k q ->
          let _, c = cost (fun () -> Q.cons 0 q) in
          if c > snd !dear then dear := k, c)
        v;
      !dear
    in
    let n = 2_000 in
    let v = Array.make (n + 1) Q.empty
    and dear = ref (0, 0.0) in
    for i = 1 to n do
      let q, c = cost (fun () -> Q.cons i v.(i - 1)) in
      v.(i) <- q;
      if c > snd !dear then dear := i, c
    done;
    within
      (Printf.sprintf "the cons that makes each version of a cons-build of %d" n)
      !dear;
    List.iter
      (fun (run, k, c) ->
        within (Printf.sprintf "%s from every version of a cons-build of %d" run n) (k, c))
      (W.short_futures v ~size:Fun.id);
    let v, _ = W.build n in
    within
      (Printf.sprintf "cons from every version of a snoc-build of %d" n)
      (cons_from v);
    let n = 1_000 in
    let v, _ = W.drain n in
    within (Printf.sprintf "cons from every version of a drain of %d" n) (cons_from v)
  ;;
end

module Over_batched = ConstantTimeConsQueue (Okasaki.Ch5.BatchedQueue)
module Over_batched_tests = Cons_tests (Over_batched)

(* "Any implementation of queues": over Figure 5.2's batched queue, cons is constant
   although the queue under it is not, and the first tail to reach that queue runs its
   reverse, which the clock sees through the wrapper. *)
let test_cons_guard () =
  let module B = Over_batched_tests in
  let n = 1_000 in
  let ops = B.both_then_drain n in
  let costs = B.costs ops in
  let i, op, c = B.dearest B.a_cons ops costs in
  check
    (Printf.sprintf
       "guard: over Figure 5.2's queue the dearest cons of n snocs, n conses and 2n \
        tails is #%d (%s) at %.0f words, n=%d"
       i
       (B.describe op)
       c
       n)
    (c <= constant);
  let i, op, c = B.dearest B.a_tail ops costs in
  check
    (Printf.sprintf
       "guard: and the same probe sees that queue's reverse through the wrapper, on the \
        first tail past the list, #%d (%s) at %.0f words"
       i
       (B.describe op)
       c)
    (i = 3 * n && c >= float_of_int n /. 2.)
;;

module Wrapped = ConstantTimeConsQueue (HoodMelvilleQueue)
module Wrapped_contract = Queue_tests (Wrapped)
module Wrapped_costs = Worst_case (Wrapped)
module Wrapped_cons = Cons_tests (Wrapped)

let test_cons_queue () =
  section "ConstantTimeConsQueue (Exercise 8.4): cons over HoodMelvilleQueue";
  let before = !failures in
  Wrapped_contract.run_contract "ConstantTimeConsQueue";
  Wrapped_cons.run_contract "ConstantTimeConsQueue";
  test_delegation ();
  if !failures > before
  then
    Printf.printf
      "  SKIP  ConstantTimeConsQueue: cost checks -- the contract above does not hold\n"
  else (
    test_cons_guard ();
    let queue_ops = Wrapped_costs.run_sequences "ConstantTimeConsQueue" in
    let with_cons = Wrapped_cons.run_sequences "ConstantTimeConsQueue" in
    if queue_ops && with_cons
    then (
      Wrapped_costs.run_versions "ConstantTimeConsQueue, persistently";
      Wrapped_cons.run_versions "ConstantTimeConsQueue, persistently")
    else
      Printf.printf
        "  SKIP  ConstantTimeConsQueue: persistence checks -- not real-time in one thread\n")
;;

(* ------------------------------------------------------ BankersDeque (8.4.2) *)

(* Section 8.4.2 builds deques the way section 6.3.2 built queues: two streams with their
   lengths, and laziness doing the rebuilding. For a queue, balance meant everything in
   the front; for a deque it means the two streams within a constant factor of each other,
   |f| <= c|r| + 1 and |r| <= c|f| + 1, the "+1" letting a singleton keep its one element
   in either stream. When an operation breaks the invariant, check restores perfect
   balance: the long stream is cut to half of the total, by take, and its remainder goes
   onto the back of the short one, by ++ and the reverse of a drop, all of it suspended,
   so that the operation itself does O(1) work and the operations that follow pay for the
   rest a step at a time, under a debit invariant. p.110 concludes from Theorem 8.1 that
   every operation is O(1) amortised, and by the banker's method that holds when the deque
   is used persistently.

   So the checks are test_ch6's for the banker's queue, behind test_ch5's contract for
   deques. A deque goes wrong at its singletons, at the crossing where a drain from one
   end runs the other side dry, and in the mirror between its two ends, so every check
   that names an end has a twin. The cost checks are amortised, over whole sequences, and
   then over traces, several futures of one deque. The branch point just after a
   rebalance, where every future of one version forces the same suspension, is where lazy
   rebuilding shows, and the same functor over STRICT streams, the same code with every
   suspension forced on creation, is the control: it passes every single-thread sequence,
   since it is batched rebuilding, and fails the branch point, running the reverse again
   on every repeat. It is also the guard that the clock sees a reverse at all.

   Two clocks again. Words, against the constant above: the dearest sequence averages 37
   per operation, and a cons or snoc that rebalances allocates 44, its four suspensions
   and a tuple. And a counting stream, in which two claims are exact: cons and snoc
   execute no step of any stream, "by inspection, every operation has an O(1) unshared
   cost", and a removal repeated from one version executes nothing after the first time,
   which is memoisation. Theorem 8.1's discharge counts, 1 and c + 1 per stream, are not
   made a step budget: the book leaves the proof, and with it what a step of take or drop
   is worth, to the reader. c is a functor argument, so the whole suite runs at c = 2, and
   the contract and the word budgets again at c = 3. *)

(* Figure 4.1's streams with every step counted: one per cell that ++ copies, take keeps,
   drop passes over or reverse moves. *)
module Counting_stream = struct
  type 'a stream_cell =
    | Nil
    | Cons of 'a * 'a stream

  and 'a stream = 'a stream_cell lazy_t

  let steps = ref 0

  let rec ( ++ ) s1 s2 =
    lazy
      (match s1 with
       | (lazy Nil) -> Lazy.force s2
       | (lazy (Cons (x, s))) ->
         incr steps;
         Cons (x, s ++ s2))
  ;;

  let rec take n s =
    lazy
      (match n, s with
       | 0, _ | _, (lazy Nil) -> Nil
       | _, (lazy (Cons (x, s'))) ->
         incr steps;
         Cons (x, take (n - 1) s'))
  ;;

  let drop n s =
    let rec aux n (lazy c) =
      match n, c with
      | 0, _ -> c
      | _, Nil -> Nil
      | _, Cons (_, s') ->
        incr steps;
        aux (n - 1) s'
    in
    lazy (aux n s)
  ;;

  let reverse s =
    let rec aux lhs rhs =
      match lhs with
      | (lazy Nil) -> rhs
      | (lazy (Cons (x, s))) ->
        incr steps;
        aux s (Cons (x, lazy rhs))
    in
    lazy (aux s Nil)
  ;;
end

let steps () = !Counting_stream.steps

(* The same four functions with nothing suspended: each runs on the spot and wraps its
   result as a stream already forced. Figure 8.3 over these is batched rebuilding. *)
module Strict_stream = struct
  type 'a stream_cell =
    | Nil
    | Cons of 'a * 'a stream

  and 'a stream = 'a stream_cell lazy_t

  let rec ( ++ ) s1 s2 =
    match s1 with
    | (lazy Nil) -> s2
    | (lazy (Cons (x, s))) -> Lazy.from_val (Cons (x, s ++ s2))
  ;;

  let rec take n s =
    match n, s with
    | 0, _ | _, (lazy Nil) -> Lazy.from_val Nil
    | _, (lazy (Cons (x, s'))) -> Lazy.from_val (Cons (x, take (n - 1) s'))
  ;;

  let rec drop n s =
    match n, s with
    | 0, _ | _, (lazy Nil) -> s
    | _, (lazy (Cons (_, s'))) -> drop (n - 1) s'
  ;;

  let reverse s =
    let rec aux acc = function
      | (lazy Nil) -> acc
      | (lazy (Cons (x, s))) -> aux (Lazy.from_val (Cons (x, acc))) s
    in
    aux (Lazy.from_val Nil) s
  ;;
end

(* What a run did, for its budget. *)
type deque_ops =
  { conses : int
  ; snocs : int
  ; tails : int
  ; inits : int
  ; heads : int
  ; lasts : int
  }

let nothing = { conses = 0; snocs = 0; tails = 0; inits = 0; heads = 0; lasts = 0 }
let deque_total o = o.conses + o.snocs + o.tails + o.inits + o.heads + o.lasts

let times d o =
  { conses = d * o.conses
  ; snocs = d * o.snocs
  ; tails = d * o.tails
  ; inits = d * o.inits
  ; heads = d * o.heads
  ; lasts = d * o.lasts
  }
;;

(* Amortised O(1) in words: CONSTANT per operation, over the whole run. *)
let deque_budget o = constant *. float_of_int (deque_total o)

let per_operation o c =
  Printf.sprintf "%.2f words per operation" (c /. float_of_int (deque_total o))
;;

(* The least a removal that runs a rebalance's reverse costs in a drain of n, in either
   unit: what the guards ask a clock to see. The reverse moves a fixed fraction of the
   deque, a sixth at c = 2, and the drop before it walks half; measured, some five words
   an element and one step. *)
let reverse_floor n = float_of_int n /. 2.

module Deque_tests (D : DEQUE) = struct
  module As_queue = Queue_tests (D)

  let opaque x = ignore (Sys.opaque_identity x)

  (* Four ways to build the deque that reads [xs] from front to back. *)
  let snocs xs = List.fold_left D.snoc D.empty xs
  let conses xs = List.fold_left (fun q x -> D.cons x q) D.empty (List.rev xs)

  let halves xs =
    let k = List.length xs / 2 in
    List.filteri (fun i _ -> i < k) xs, List.filteri (fun i _ -> i >= k) xs
  ;;

  let builds =
    [ "snoc", snocs
    ; "cons", conses
    ; ( "cons onto snoc"
      , fun xs ->
          let left, right = halves xs in
          List.fold_left (fun q x -> D.cons x q) (snocs right) (List.rev left) )
    ; ( "snoc onto cons"
      , fun xs ->
          let left, right = halves xs in
          List.fold_left D.snoc (conses left) right )
    ]
  ;;

  (* Three ways to take one apart. Each returns the elements front to back. *)
  let drain_front q = drain_with ~is_empty:D.is_empty ~head:D.head ~tail:D.tail q

  let drain_back q =
    List.rev (drain_with ~is_empty:D.is_empty ~head:D.last ~tail:D.init q)
  ;;

  let drain_both_ends q =
    let rec go n front back from_front q =
      if D.is_empty q
      then List.rev_append front back
      else if n = drain_limit
      then failwith "drain: no end in sight"
      else if from_front
      then go (n + 1) (D.head q :: front) back false (D.tail q)
      else go (n + 1) front (D.last q :: back) true (D.init q)
    in
    go 0 [] [] true q
  ;;

  let drains =
    [ "the front", drain_front; "the back", drain_back; "both ends", drain_both_ends ]
  ;;

  let run_contract name =
    let t label = Printf.sprintf "%s: %s" name label in
    check_refuses (t "last on empty raises") "last" (fun () -> D.last D.empty);
    check_refuses (t "init on empty raises") "init" (fun () ->
      ignore (D.is_empty (D.init D.empty)));
    (* One element, by every route: put there from either end, or left behind by a removal
       from either end of each two-element deque. The invariant lets it sit in either
       stream, and every reader has to cope with both. *)
    let routes =
      [ ("snoc", fun () -> D.snoc D.empty 7)
      ; ("cons", fun () -> D.cons 7 D.empty)
      ; ("tail of two snocs", fun () -> D.tail (snocs [ 0; 7 ]))
      ; ("init of two snocs", fun () -> D.init (snocs [ 7; 0 ]))
      ; ("tail of two conses", fun () -> D.tail (conses [ 0; 7 ]))
      ; ("init of two conses", fun () -> D.init (conses [ 7; 0 ]))
      ; ("tail of a cons onto a snoc", fun () -> D.tail (D.cons 0 (D.snoc D.empty 7)))
      ; ("init of a snoc onto a cons", fun () -> D.init (D.snoc (D.cons 7 D.empty) 0))
      ]
    in
    (* The first thing a one-element deque owes that [make ()] does not deliver. *)
    let lacks make =
      match
        let q = make () in
        if D.is_empty q
        then Some "it claims to be empty"
        else if D.head q <> 7
        then Some "head is wrong"
        else if D.last q <> 7
        then Some "last is wrong"
        else if not (D.is_empty (D.tail q))
        then Some "its tail is not empty"
        else if not (D.is_empty (D.init q))
        then Some "its init is not empty"
        else None
      with
      | verdict -> verdict
      | exception Failure why -> Some ("it raised " ^ why)
    in
    let bad =
      List.filter_map
        (fun (route, make) -> Option.map (fun why -> route, why) (lacks make))
        routes
    in
    check
      (t
         (Printf.sprintf
            "one element behaves the same by every route to it%s"
            (match bad with
             | [] -> ""
             | (route, why) :: _ -> Printf.sprintf " -- reached by %s, %s" route why)))
      (bad = []);
    (* The crossing. Every build, read from every end, at every small size: 0 to 20 covers
       the empty deque, both one-element shapes, the two- and three-element rebalances
       where a half is a single element, and odd and even splits after that. *)
    let bad = ref [] in
    for n = 20 downto 0 do
      let xs = upto n in
      List.iter
        (fun (build, make) ->
          List.iter
            (fun (drain, take) ->
              match take (make xs) with
              | got when got = xs -> ()
              | got -> bad := (build, drain, n, string_of_int_list got) :: !bad
              | exception Failure why -> bad := (build, drain, n, "raised " ^ why) :: !bad)
            drains)
        builds
    done;
    check
      (t
         (Printf.sprintf
            "every build reads back correctly from every end, sizes 0 to 20%s"
            (match !bad with
             | [] -> ""
             | (build, drain, n, got) :: _ ->
               Printf.sprintf " -- built by %s, n=%d, read from %s: %s" build n drain got)))
      (!bad = []);
    (* Randomised against a list, with all four writers and all three readers, checked
       after every operation. *)
    Random.init 20260926;
    let bad_empty = ref 0
    and bad_head = ref 0
    and bad_last = ref 0
    and bad_drain = ref 0
    and raised = ref 0 in
    for run = 0 to 299 do
      let q = ref D.empty
      and model = ref [] in
      try
        for i = 0 to 59 do
          (match Random.int 6 with
           | 0 | 1 ->
             q := D.snoc !q i;
             model := !model @ [ i ]
           | 2 | 3 ->
             q := D.cons i !q;
             model := i :: !model
           | 4 when !model <> [] ->
             q := D.tail !q;
             model := List.tl !model
           | 5 when !model <> [] ->
             q := D.init !q;
             model := List.rev (List.tl (List.rev !model))
           | _ -> ());
          if D.is_empty !q <> (!model = []) then incr bad_empty;
          match !model with
          | [] -> ()
          | x :: _ ->
            if D.head !q <> x then incr bad_head;
            if D.last !q <> List.hd (List.rev !model) then incr bad_last
        done;
        let _, take = List.nth drains (run mod 3) in
        if take !q <> !model then incr bad_drain
      with
      | Failure _ -> incr raised
    done;
    check_int
      (t "no operation raises on a non-empty deque, 300 random runs")
      ~expect:0
      ~actual:!raised;
    check_int (t "is_empty agrees with a list model") ~expect:0 ~actual:!bad_empty;
    check_int (t "head agrees with a list model") ~expect:0 ~actual:!bad_head;
    check_int (t "last agrees with a list model") ~expect:0 ~actual:!bad_last;
    check_int (t "every drain agrees with a list model") ~expect:0 ~actual:!bad_drain;
    (* Persistence, with all four writers let loose on every version. *)
    surviving
      (t "every earlier version can still be used")
      (fun () ->
        let versions = List.init 20 (fun i -> snocs (upto i)) in
        List.iter
          (fun v ->
            ignore (D.snoc v 99);
            ignore (D.cons 99 v);
            if not (D.is_empty v)
            then (
              ignore (D.tail v);
              ignore (D.init v)))
          versions;
        List.mapi (fun i v -> if drain_both_ends v = upto i then 0 else 1) versions
        |> List.fold_left ( + ) 0)
      (fun stale ->
        check_int (t "every earlier version stays correct") ~expect:0 ~actual:stale)
  ;;

  (* ---------------------------------------- sequences: one thread, from empty *)

  (* Each driver runs its sequence and reports what it did, keeping its deque alive to the
     end so that nothing it allocated can be optimised away. They differ in where the
     rebalances fall and which way the elements cross. *)
  let cons_then_init n () =
    let q = ref D.empty in
    for i = 1 to n do
      q := D.cons i !q
    done;
    for _ = 1 to n do
      q := D.init !q
    done;
    opaque !q;
    { nothing with conses = n; inits = n }
  ;;

  let cons_then_tail n () =
    let q = ref D.empty in
    for i = 1 to n do
      q := D.cons i !q
    done;
    for _ = 1 to n do
      q := D.tail !q
    done;
    opaque !q;
    { nothing with conses = n; tails = n }
  ;;

  let snoc_then_tail n () =
    let q = ref D.empty in
    for i = 1 to n do
      q := D.snoc !q i
    done;
    for _ = 1 to n do
      q := D.tail !q
    done;
    opaque !q;
    { nothing with snocs = n; tails = n }
  ;;

  let snoc_then_both_ends n () =
    let q = ref D.empty in
    for i = 1 to n do
      q := D.snoc !q i
    done;
    for i = 1 to n do
      q := if i land 1 = 0 then D.tail !q else D.init !q
    done;
    opaque !q;
    { nothing with snocs = n; tails = n / 2; inits = n - (n / 2) }
  ;;

  (* The smallest rebalance there is, over and over: a second element arrives on the side
     that already holds the first, and leaves again from the other. *)
  let smallest_rebalance n () =
    let q = ref (D.cons 0 D.empty) in
    for i = 1 to n do
      q := D.cons i !q;
      q := D.init !q
    done;
    opaque !q;
    { nothing with conses = n + 1; inits = n }
  ;;

  let alternate n () =
    let q = ref D.empty in
    for i = 1 to n do
      q := D.snoc !q i;
      q := D.tail !q
    done;
    opaque !q;
    { nothing with snocs = n; tails = n }
  ;;

  let cons_snoc_init n () =
    let q = ref D.empty in
    for i = 1 to n do
      q := D.cons i !q;
      q := D.snoc !q i;
      q := D.init !q
    done;
    opaque !q;
    { nothing with conses = n; snocs = n; inits = n }
  ;;

  (* Here a head or a last can do work: it opens the front of whatever ++ the rebalances
     have stacked on its stream. *)
  let peeks n () =
    let q = ref D.empty
    and sum = ref 0 in
    for i = 1 to n do
      q := D.cons i !q;
      sum := !sum + D.head !q + D.last !q;
      q := D.snoc !q i;
      sum := !sum + D.head !q + D.last !q
    done;
    opaque !q;
    opaque !sum;
    { nothing with conses = n; snocs = n; heads = 2 * n; lasts = 2 * n }
  ;;

  (* The plan is drawn, and counted, before anything is measured. *)
  let random_mix n =
    Random.init 20260926;
    let size = ref 0 in
    let plan =
      Array.init n (fun _ ->
        let op = if !size = 0 then Random.int 2 else Random.int 6 in
        (match op with
         | 0 | 1 -> incr size
         | 2 | 3 -> decr size
         | _ -> ());
        op)
    in
    let count k =
      Array.fold_left (fun acc op -> if op = k then acc + 1 else acc) 0 plan
    in
    let ops =
      { conses = count 0
      ; snocs = count 1
      ; tails = count 2
      ; inits = count 3
      ; heads = count 4
      ; lasts = count 5
      }
    in
    fun () ->
      let q = ref D.empty
      and sum = ref 0 in
      Array.iteri
        (fun i op ->
          match op with
          | 0 -> q := D.cons i !q
          | 1 -> q := D.snoc !q i
          | 2 -> q := D.tail !q
          | 3 -> q := D.init !q
          | 4 -> sum := !sum + D.head !q
          | _ -> sum := !sum + D.last !q)
        plan;
      opaque !q;
      opaque !sum;
      ops
  ;;

  let sequences =
    [ "n conses then n inits", cons_then_init
    ; "n conses then n tails, a stack", cons_then_tail
    ; "n snocs then n tails, a queue", snoc_then_tail
    ; "n snocs, then tail and init alternating", snoc_then_both_ends
    ; "cons and init alternating on one element", smallest_rebalance
    ; "snoc and tail alternating", alternate
    ; "cons, snoc and init, over and over", cons_snoc_init
    ; "a head and a last after every cons and every snoc", peeks
    ; "a random mix of all six operations", random_mix
    ]
  ;;

  (* Amortised bounds, asserted the only way an amortised bound can be: over whole
     sequences. True if every sequence stayed within the budget. The large size is guarded
     on the small one, as everywhere in these files. *)
  let run_sequences name =
    let t label = Printf.sprintf "%s: %s" name label in
    let ok = ref true in
    List.iter
      (fun (sequence, driver) ->
        let within label n =
          let ops, c = cost (driver n) in
          let fine = c <= deque_budget ops in
          check
            (t
               (Printf.sprintf
                  "%s, %s: %s at n=%d"
                  sequence
                  label
                  (per_operation ops c)
                  n))
            fine;
          fine
        in
        if not (within "amortised O(1)" 1_000)
        then (
          ok := false;
          Printf.printf
            "  SKIP  %s: %s at n=100000 -- it is not amortised O(1) at n=1000\n"
            name
            sequence)
        else if not (within "still amortised O(1), a hundred times longer" 100_000)
        then ok := false)
      sequences;
    !ok
  ;;

  (* -------------------------------------- traces: several futures of one deque *)

  (* Each end: how to build the deque whose drain from that end has to carry elements
     across, the insertion that builds it, the removal, and what one removal is worth in
     the budget. *)
  type direction =
    { direction : string
    ; builder : string
    ; build : int list -> int D.queue
    ; insert : int D.queue -> int -> int D.queue
    ; remove : int D.queue -> int D.queue
    ; per : deque_ops
    }

  let ends =
    [ { direction = "from the front"
      ; builder = "snoc"
      ; build = snocs
      ; insert = D.snoc
      ; remove = D.tail
      ; per = { nothing with tails = 1 }
      }
    ; { direction = "from the back"
      ; builder = "cons"
      ; build = conses
      ; insert = (fun q x -> D.cons x q)
      ; remove = D.init
      ; per = { nothing with inits = 1 }
      }
    ]
  ;;

  (* A drain of n, one removal at a time, each on the clock. The index and cost of the
     dearest: the removal that runs a reverse. *)
  let dearest_removal clock ~build ~remove n =
    let q = ref (build (upto n))
    and dear = ref (0, 0.0) in
    for i = 1 to n do
      let q', c = cost_on clock (fun () -> remove !q) in
      if c > snd !dear then dear := i, c;
      q := q'
    done;
    !dear
  ;;

  (* A fresh deque brought to the version whose removal is the dear one, without taking
     it. *)
  let version_before ~build ~remove ~n ~k =
    let q = ref (build (upto n)) in
    for _ = 1 to k - 1 do
      q := remove !q
    done;
    !q
  ;;

  (* The whole drain, d times over from the same starting deque. *)
  let repeated_drain ~build ~remove ~per ~n ~d =
    let q0 = build (upto n) in
    fun () ->
      for _ = 1 to d do
        let q = ref q0 in
        for _ = 1 to n do
          q := remove !q
        done;
        opaque !q
      done;
      times (d * n) per
  ;;

  (* Every version of a full drain from one end, kept, and so with everything on the
     drain's path already forced. *)
  let versions n e =
    let v = Array.make (n + 1) D.empty in
    v.(0) <- e.build (upto n);
    for i = 1 to n do
      v.(i) <- e.remove v.(i - 1)
    done;
    v
  ;;

  (* Every version of a build by insertions at the far end. *)
  let growth n e =
    let v = Array.make (n + 1) D.empty in
    for i = 1 to n do
      v.(i) <- e.insert v.(i - 1) i
    done;
    v
  ;;

  (* The shortest futures there are, d times over from every version in [v] whose size
     ([size k] for the k-th) allows them: an operation, and then the one that would force
     what it suspended, at either end. One run from each version goes unmeasured first: a
     version may have put off work its own history is due to pay for, and memoisation then
     shares it with every run after. For each run, the version it was dearest from and
     what it cost there. *)
  let short_runs v ~size ~d =
    let runs =
      [ "tail", (fun q -> opaque (D.tail q)), { nothing with tails = 1 }, 1
      ; "init", (fun q -> opaque (D.init q)), { nothing with inits = 1 }, 1
      ; ( "tail then head"
        , (fun q -> opaque (D.head (D.tail q)))
        , { nothing with tails = 1; heads = 1 }
        , 2 )
      ; ( "init then last"
        , (fun q -> opaque (D.last (D.init q)))
        , { nothing with inits = 1; lasts = 1 }
        , 2 )
      ; ( "tail then last"
        , (fun q -> opaque (D.last (D.tail q)))
        , { nothing with tails = 1; lasts = 1 }
        , 2 )
      ; ( "init then head"
        , (fun q -> opaque (D.head (D.init q)))
        , { nothing with inits = 1; heads = 1 }
        , 2 )
      ; ( "cons then last"
        , (fun q -> opaque (D.last (D.cons 0 q)))
        , { nothing with conses = 1; lasts = 1 }
        , 0 )
      ; ( "snoc then head"
        , (fun q -> opaque (D.head (D.snoc q 0)))
        , { nothing with snocs = 1; heads = 1 }
        , 0 )
      ; ( "cons then init"
        , (fun q -> opaque (D.init (D.cons 0 q)))
        , { nothing with conses = 1; inits = 1 }
        , 0 )
      ; ( "snoc then tail"
        , (fun q -> opaque (D.tail (D.snoc q 0)))
        , { nothing with snocs = 1; tails = 1 }
        , 0 )
      ]
    in
    List.map
      (fun (run, f, per, needs) ->
        let worst = ref (0, 0.0) in
        Array.iteri
          (fun k q ->
            if size k >= needs
            then (
              f q;
              let _, c =
                cost (fun () ->
                  for _ = 1 to d do
                    f q
                  done)
              in
              if c > snd !worst then worst := k, c))
          v;
        run, fst !worst, times d per, snd !worst)
      runs
  ;;

  (* n operations by the four writers, each applied to a version chosen at random among
     all built so far. *)
  let random_trace n =
    Random.init 20260926;
    let from = Array.init n (fun i -> Random.int (i + 1)) in
    let draw = Array.init n (fun _ -> Random.int 4) in
    let v = Array.make (n + 1) D.empty in
    fun () ->
      let conses = ref 0
      and snocs = ref 0
      and tails = ref 0
      and inits = ref 0 in
      for i = 1 to n do
        let q = v.(from.(i - 1)) in
        let op = if D.is_empty q then draw.(i - 1) land 1 else draw.(i - 1) in
        v.(i)
        <- (match op with
            | 0 ->
              incr conses;
              D.cons i q
            | 1 ->
              incr snocs;
              D.snoc q i
            | 2 ->
              incr tails;
              D.tail q
            | _ ->
              incr inits;
              D.init q)
      done;
      opaque v;
      { nothing with conses = !conses; snocs = !snocs; tails = !tails; inits = !inits }
  ;;

  let run_traces name =
    let t label = Printf.sprintf "%s: %s" name label in
    let within label (ops, c) =
      check
        (t (Printf.sprintf "%s: %s" label (per_operation ops c)))
        (c <= deque_budget ops)
    in
    let n = 1_000 in
    List.iter
      (fun ({ direction; builder; build; remove; per; _ } as e) ->
        (* The guard, at each end: a drain of a deque built from the other end has one
           removal that runs a reverse, and the clock sees it. *)
        let k, dear = dearest_removal words ~build ~remove n in
        check
          (t
             (Printf.sprintf
                "in a drain of %d %s the dearest removal is #%d, at %.0f words"
                n
                direction
                k
                dear))
          (dear >= reverse_floor n);
        (* p.65's branch point just after the rebalance: the version whose removal is the
           dear one, taken d times. Every future forces the same suspension, so the
           reverse runs once. *)
        let d = 10_000 in
        let v = version_before ~build ~remove ~n ~k in
        let _, first = cost (fun () -> remove v) in
        let _, rest =
          cost (fun () ->
            for _ = 2 to d do
              opaque (remove v)
            done)
        in
        check
          (t
             (Printf.sprintf
                "the first of %d removals of one version %s runs the reverse, %.0f words"
                d
                direction
                first))
          (first >= reverse_floor n);
        within
          (Printf.sprintf "and the other %d find it memoised" (d - 1))
          (times (d - 1) per, rest);
        (* p.65's branch point just before the rebalance: the whole drain, d times over.
           These are different suspensions, so memoisation does not help, and the budget
           holds anyway, because the operations were repeated along with the work. *)
        within
          (Printf.sprintf "the whole drain %s repeated 10 times from one deque" direction)
          (cost (repeated_drain ~build ~remove ~per ~n ~d:10));
        (* Every branch point of a drain from this end, with the shortest futures at both
           ends. *)
        List.iter
          (fun (run, k, ops, c) ->
            within
              (Printf.sprintf
                 "%s, 50 times over from each version of a drain %s, dearest from #%d"
                 run
                 direction
                 k)
              (ops, c))
          (short_runs (versions n e) ~size:(fun k -> n - k) ~d:50);
        (* And every branch point of the build that drain empties: a drain only ever
           shrinks, so its versions have all seen a rebalance some time ago; a build's are
           the ones on the brink of the next, and the ones just past it. *)
        List.iter
          (fun (run, k, ops, c) ->
            within
              (Printf.sprintf
                 "%s, 20 times over from each version of a build by %s, dearest from #%d"
                 run
                 builder
                 k)
              (ops, c))
          (short_runs (growth (2 * n) e) ~size:Fun.id ~d:20))
      ends;
    within
      "a random trace of 100000 operations, each on a random earlier version"
      (cost (random_trace 100_000))
  ;;
end

module C2 = struct
  let c = 2
end

module C3 = struct
  let c = 3
end

module Deque2 = BankersDeque (C2) (Okasaki.Ch4.Stream)
module Deque2_counting = BankersDeque (C2) (Counting_stream)
module Deque2_strict = BankersDeque (C2) (Strict_stream)
module Deque3 = BankersDeque (C3) (Okasaki.Ch4.Stream)
module Deque2_tests = Deque_tests (Deque2)
module Deque2_counting_tests = Deque_tests (Deque2_counting)
module Deque2_strict_tests = Deque_tests (Deque2_strict)
module Deque3_tests = Deque_tests (Deque3)

(* p.110: "by inspection, every operation has an O(1) unshared cost". For cons and snoc
   that is their whole cost: check compares two lengths and, at a rebalance, suspends a
   take, a drop, a reverse and a ++, and forces nothing. So both are O(1) worst-case in
   words, and execute no step of any stream, at any size and however the two streams have
   been growing. *)
module Unshared (D : DEQUE) = struct
  let dearest clock insert n =
    let q = ref D.empty
    and worst = ref 0.0 in
    for i = 1 to n do
      let q', c = cost_on clock (fun () -> insert !q i) in
      q := q';
      worst := Float.max !worst c
    done;
    !worst
  ;;

  let run clock n =
    [ "snoc", dearest clock (fun q i -> D.snoc q i) n
    ; "cons", dearest clock (fun q i -> D.cons i q) n
    ; ( "cons and snoc in turn"
      , dearest clock (fun q i -> if i land 1 = 0 then D.cons i q else D.snoc q i) n )
    ]
  ;;
end

module Unshared_words = Unshared (Deque2)
module Unshared_steps = Unshared (Deque2_counting)

let test_deque_unshared () =
  let n = 20_000 in
  List.iter
    (fun (what, w) ->
      check
        (Printf.sprintf
           "BankersDeque: %s is O(1) worst-case, dearest of %d consecutive %.0f words"
           what
           n
           w)
        (w <= constant))
    (Unshared_words.run words n);
  List.iter
    (fun (what, s) ->
      check
        (Printf.sprintf
           "BankersDeque, in steps: %s executes no step, dearest of %d consecutive %.0f"
           what
           n
           s)
        (s = 0.0))
    (Unshared_steps.run steps n)
;;

(* The branch point after a rebalance, to the step: the first removal from the version
   executes the rebalance, and the same removal repeated executes nothing. *)
let test_deque_steps () =
  let module T = Deque2_counting_tests in
  let t label = Printf.sprintf "BankersDeque, in steps: %s" label in
  let n = 1_000
  and d = 10_000 in
  List.iter
    (fun { T.direction; build; remove; _ } ->
      let k, dear = T.dearest_removal steps ~build ~remove n in
      check
        (t
           (Printf.sprintf
              "in a drain of %d %s the dearest removal is #%d, at %.0f steps"
              n
              direction
              k
              dear))
        (dear >= reverse_floor n);
      let v = T.version_before ~build ~remove ~n ~k in
      let _, first = cost_on steps (fun () -> remove v) in
      let _, rest =
        cost_on steps (fun () ->
          for _ = 2 to d do
            T.opaque (remove v)
          done)
      in
      check
        (t
           (Printf.sprintf
              "the first of %d removals of one version %s executes the rebalance, %.0f \
               steps"
              d
              direction
              first))
        (first >= reverse_floor n);
      check
        (t
           (Printf.sprintf
              "and the other %d removals %s execute no step at all (%.0f)"
              (d - 1)
              direction
              rest))
        (rest = 0.0))
    T.ends
;;

(* The control: Figure 8.3 over strict streams. Batched rebuilding passes every
   single-thread sequence, which is why the sequences alone cannot tell the two apart, and
   its dearest removal is the reverse the clock has to see. At the branch point every
   repeat runs the reverse again: there is no suspension to have remembered it. *)
let test_deque_control () =
  let module T = Deque2_strict_tests in
  let name = "guard, the same functor over strict streams" in
  let t label = Printf.sprintf "%s: %s" name label in
  ignore (T.run_sequences name);
  let n = 1_000
  and d = 100 in
  let { T.build; remove; _ } = List.hd T.ends in
  let k, dear = T.dearest_removal words ~build ~remove n in
  check
    (t
       (Printf.sprintf
          "in a drain of %d from the front the dearest removal is #%d, at %.0f words"
          n
          k
          dear))
    (dear >= reverse_floor n);
  let v = T.version_before ~build ~remove ~n ~k in
  let _, first = cost (fun () -> remove v) in
  let _, rest =
    cost (fun () ->
      for _ = 2 to d do
        T.opaque (remove v)
      done)
  in
  check
    (t
       (Printf.sprintf
          "the first of %d removals of that version runs the reverse, %.0f words, and so \
           does every one of the other %d, %.0f words each"
          d
          first
          (d - 1)
          (rest /. float_of_int (d - 1))))
    (first >= reverse_floor n && rest >= float_of_int (d - 1) *. reverse_floor n)
;;

(* What a deque costs means nothing until it behaves like one, and one that raises half
   way through a sequence would take the rest of the section down with it. *)
let test_bankers_deque () =
  section "BankersDeque (8.4.2), c = 2";
  let before = !failures in
  Deque2_tests.As_queue.run_contract "BankersDeque";
  Deque2_tests.run_contract "BankersDeque";
  Deque2_counting_tests.As_queue.run_contract "BankersDeque over the counting stream";
  Deque2_counting_tests.run_contract "BankersDeque over the counting stream";
  if !failures > before
  then
    Printf.printf
      "  SKIP  BankersDeque: cost checks -- the contract above does not hold\n"
  else if Deque2_tests.run_sequences "BankersDeque"
  then (
    test_deque_unshared ();
    test_deque_control ();
    Deque2_tests.run_traces "BankersDeque, persistently";
    test_deque_steps ())
  else
    Printf.printf
      "  SKIP  BankersDeque: worst-case and persistence checks -- not amortised O(1) in \
       one thread\n";
  section "BankersDeque (8.4.2), c = 3";
  let before = !failures in
  Deque3_tests.As_queue.run_contract "BankersDeque, c = 3";
  Deque3_tests.run_contract "BankersDeque, c = 3";
  if !failures > before
  then
    Printf.printf
      "  SKIP  BankersDeque, c = 3: cost checks -- the contract above does not hold\n"
  else if Deque3_tests.run_sequences "BankersDeque, c = 3"
  then Deque3_tests.run_traces "BankersDeque, c = 3, persistently"
  else
    Printf.printf
      "  SKIP  BankersDeque, c = 3: persistence checks -- not amortised O(1) in one thread\n"
;;

(* ------------------------------------------- red-black trees (8.1, Exercise 8.1) *)

(* Section 8.1 introduces batched rebuilding, and its second example is the red-black tree
   of Section 3.3 with deletion: mark a deleted node instead of removing it, keep
   estimates of how many nodes are valid and how many are not, and rebuild the whole tree
   from its valid elements, by Exercise 3.9, once the invalid ones grow past a fixed
   fraction. Exercise 8.1 asks for that. The set below is Section 3.3's, copied here as
   the starting point, and these checks are its baseline: everything test_ch3 asserted of
   the original, run against the copy before a boolean field, the estimates and delete
   arrive, and kept running after they do. The checks that belong to delete, and to the
   batched rebuild it triggers, follow in their own section below.

   As in test_ch3, SET seals the tree, so its shape is measured from outside through an
   instrumented ORDERED. A search for an element that is NOT in the set walks from the
   root to an empty slot, and counting only the comparisons that answered true gives
   exactly one per node on that path, whichever way the search turned. Probing every gap
   finds the deepest path, which Exercise 3.8 bounds by 2*floor(log2 (n+1)). Node colours
   are invisible and are not asserted; the depth bound is what they exist to support.

   One check is new: the copy answers exactly as Chapter 3's original, gap for gap. The
   two are the same code today, and pinning that down means that when insert is touched
   for the estimates, its shape is known not to have moved. *)

let comparisons = ref 0

(* Comparisons that answered true: one per node on a search path, whichever way the search
   turned, since a step left is one true lt and a step right is one false lt then one true
   one. *)
let steps = ref 0

module Counting_int = struct
  type t = int

  let eq a b =
    incr comparisons;
    a = b
  ;;

  let lt a b =
    incr comparisons;
    let less = a < b in
    if less then incr steps;
    less
  ;;

  let leq a b =
    incr comparisons;
    a <= b
  ;;
end

(* Comparisons performed by [f]. *)
let count_only f =
  comparisons := 0;
  ignore (Sys.opaque_identity (f ()));
  !comparisons
;;

(* floor (log2 n), for n >= 1. *)
let floor_log2 n =
  let rec go acc n = if n <= 1 then acc else go (acc + 1) (n / 2) in
  go 0 n
;;

(* Exercise 3.8's bound on the depth of any node in a red-black tree of size n. *)
let depth_bound n = 2 * floor_log2 (n + 1)

(* Sets are built from even numbers so that every odd number is a gap to probe. *)
let evens n = List.init n (fun i -> 2 * i)

let shuffle seed xs =
  Random.init seed;
  List.map snd (List.sort compare (List.map (fun x -> Random.bits (), x) xs))
;;

let set_sizes = [ 0; 1; 2; 3; 4; 7; 8; 15; 16; 31; 32; 100; 500; 1000 ]

(* The three insertion orders the depth bound is checked over: ascending sends every
   element down the right spine, which is the order that rebalances most. *)
let orders n =
  [ "ascending", evens n
  ; "descending", List.rev (evens n)
  ; "random", shuffle 20260925 (evens n)
  ]
;;

module Set_tests (S : SET with type elem = int) = struct
  let of_list xs = List.fold_left (fun s x -> S.insert x s) S.empty xs

  (* Nodes on the path from the root to the empty slot a failed search for [x] falls into. *)
  let path_to_gap x s =
    steps := 0;
    if S.member x s then invalid_arg "path_to_gap: element is present";
    !steps
  ;;

  (* The depth of every gap of a set holding [evens n], the two outside the range
     included: n + 1 numbers, which is as much of the tree's shape as the seal lets
     through. *)
  let gap_profile n s = List.init (n + 1) (fun i -> path_to_gap ((2 * i) - 1) s)
  let max_path n s = List.fold_left max 0 (gap_profile n s)

  let run_contract name =
    let t label = Printf.sprintf "%s: %s" name label in
    check (t "member on the empty set is false") (not (S.member 0 S.empty));
    let s = of_list (evens 50) in
    check
      (t "every inserted element is found")
      (List.for_all (fun x -> S.member x s) (evens 50));
    check
      (t "elements never inserted are not found")
      (List.init 51 (fun i -> (2 * i) - 1) |> List.for_all (fun x -> not (S.member x s)));
    (* What a set holds cannot depend on the order the elements arrived in. *)
    let s' = of_list (shuffle 20260925 (evens 50)) in
    check
      (t "membership is independent of insertion order")
      (List.init 103 (fun i -> i - 1)
       |> List.for_all (fun x -> S.member x s = S.member x s'));
    (* Against an independent oracle, over many shapes. *)
    Random.init 20260926;
    let disagrees = ref 0 in
    for trial = 0 to 299 do
      let n = 1 + Random.int 40 in
      let xs =
        if trial mod 3 = 0
        then List.init n Fun.id
        else List.init n (fun _ -> Random.int 60)
      in
      let s = of_list xs in
      for q = -2 to 62 do
        if S.member q s <> List.mem q xs then incr disagrees
      done
    done;
    check_int
      (t "member agrees with List.mem over 300 random trees")
      ~expect:0
      ~actual:!disagrees;
    (* Re-inserting an element must leave the set alone. An ins whose equal case returns
       the whole tree rather than the current subtree grafts the tree into itself here,
       dropping elements and duplicating the rest. *)
    let base = evens 7 in
    let once = of_list base in
    let again =
      List.init 3 Fun.id
      |> List.fold_left (fun s _ -> List.fold_left (fun s x -> S.insert x s) s base) once
    in
    check
      (t "re-inserting existing elements keeps every element")
      (List.for_all (fun x -> S.member x again) base);
    check
      (t "re-inserting existing elements adds nothing")
      (List.init 8 (fun i -> (2 * i) - 1)
       |> List.for_all (fun x -> not (S.member x again)));
    check_eq
      (t "re-inserting existing elements leaves the shape alone")
      ~expect:(gap_profile 7 once)
      ~actual:(gap_profile 7 again)
      string_of_int_list;
    (* Exercise 3.8, over orders that stress the shape differently. This is the assertion
       the two colour invariants exist to support: break balance and it fails. *)
    let over = ref [] in
    List.iter
      (fun n ->
        List.iter
          (fun (order, xs) ->
            let d = max_path n (of_list xs) in
            if d > depth_bound n then over := (order, n, d) :: !over)
          (orders n))
      set_sizes;
    check
      (t
         (Printf.sprintf
            "depth stays within Exercise 3.8's 2*floor(log2 (n+1))%s"
            (match !over with
             | [] -> ""
             | (order, n, d) :: _ ->
               Printf.sprintf " -- %s n=%d reached %d, bound %d" order n d (depth_bound n))))
      (!over = []);
    (* member and insert are O(log n): at most two comparisons per level, over a path the
       bound above already limits. *)
    let costly = ref 0 in
    List.iter
      (fun n ->
        let s = of_list (evens n) in
        if count_only (fun () -> S.member ((2 * n) - 1) s) > 2 * depth_bound n
        then incr costly;
        if count_only (fun () -> S.insert ((2 * n) + 1) s) > 2 * depth_bound n
        then incr costly)
      set_sizes;
    check_int (t "member and insert stay O(log n) comparisons") ~expect:0 ~actual:!costly
  ;;

  let run_costs name =
    let t label = Printf.sprintf "%s: %s" name label in
    let allocated f = snd (cost f) in
    (* The defining property of a persistent structure: an insert leaves the old set
       whole, and not merely the previous version but every version ever built. *)
    let s = of_list (evens 50) in
    let s' = S.insert 99 s in
    check
      (t "insert leaves the original set unchanged")
      ((not (S.member 99 s)) && S.member 99 s');
    let versions =
      evens 40
      |> List.fold_left
           (fun (acc, s) x ->
             let s = S.insert x s in
             s :: acc, s)
           ([], S.empty)
      |> fst
      |> List.rev
    in
    let stale = ref 0 in
    List.iteri
      (fun i v ->
        (* version i was built from evens (i+1), so it holds those and nothing beyond *)
        if not (List.for_all (fun x -> S.member x v) (evens (i + 1))) then incr stale;
        if S.member (2 * (i + 1)) v then incr stale)
      versions;
    check_int (t "every intermediate version stays correct") ~expect:0 ~actual:!stale;
    (* member only follows pointers, so it must allocate nothing whatsoever, whether the
       search ends at a node or falls into a gap. *)
    let searching = ref [] in
    List.iter
      (fun n ->
        let s = of_list (evens n) in
        let miss = allocated (fun () -> S.member ((2 * n) + 1) s)
        and hit = allocated (fun () -> S.member (2 * (n - 1)) s) in
        if miss <> 0.0 then searching := (n, miss) :: !searching;
        if hit <> 0.0 then searching := (n, hit) :: !searching)
      [ 10; 100; 1000; 10_000 ];
    check
      (t
         (Printf.sprintf
            "member allocates nothing%s"
            (match !searching with
             | [] -> ""
             | (n, w) :: _ -> Printf.sprintf " -- n=%d allocated %.0f words" n w)))
      (!searching = []);
    (* insert copies the search path and only the search path, so its cost is logarithmic:
       ten thousand times as many elements must not cost ten thousand times as many words.
       And the copying is not waste, it is what the older versions keep pointing at, so a
       fresh insert allocates at least a node per level it rebuilds. *)
    let insert_cost n =
      let s = of_list (evens n) in
      allocated (fun () -> S.insert ((2 * n) + 1) s)
    in
    let small = insert_cost 10
    and large = insert_cost 100_000 in
    check
      (t
         (Printf.sprintf
            "insert allocates O(log n) (%.0f words at n=10, %.0f at n=100000)"
            small
            large))
      (large < 4.0 *. small);
    check
      (t (Printf.sprintf "a fresh insert really does copy the path (%.0f words)" large))
      (large >= float_of_int (depth_bound 100_000));
    (* A duplicate has no new node to thread in and no rotation to do, so it costs less,
       though not nothing: the path is still rebuilt on the way back up. *)
    let s = of_list (evens 1000) in
    let dup = allocated (fun () -> S.insert 0 s)
    and fresh = allocated (fun () -> S.insert 2001 s) in
    check
      (t
         (Printf.sprintf
            "a duplicate insert costs less than a fresh one (%.0f < %.0f)"
            dup
            fresh))
      (dup < fresh)
  ;;
end

module Rb = RedBlackSet (Counting_int)
module Rb_tests = Set_tests (Rb)

(* Chapter 3's original, for the gap-for-gap comparison. *)
module Original = Okasaki.Ch3.RedBlackSet (Counting_int)
module Original_tests = Set_tests (Original)

(* ---------------------------------------------------------- deletion (Exercise 8.1) *)

(* What Exercise 8.1's delete has to do, and what section 8.1 promises for it. The
   contract first: a deleted element is not a member, everything else still is, inserting
   it again brings it back, deleting what is absent changes nothing, and none of it
   disturbs an older version. Then the two conditions of p.99 that make batched rebuilding
   sound, both measured through the seal.

   Condition (2) says a delete must be a weak update: after any number of them short of
   the rebuild, a search still costs O(log n), which is p.100's "even if up to half the
   nodes have been marked as deleted". So a dead node must route a search by its key
   exactly as a live one does. A search that has to look on both sides of a dead node is
   not logarithmic, and the comparison count says so.

   Condition (1) says the O(n) rebuild must be rare: it may run only "whenever half the
   nodes in the tree have been deleted", so that it pays for itself at O(log n) amortised
   per delete. Its cost is allocation, and it makes no comparisons at all, since a sorted
   list has already answered every question insert would ask. So the clock for a delete is
   words, as for the queue, and a rebuild stands out from a path copy by an order of
   magnitude while more than a few dozen elements survive it. Counting those lumps in a
   drain gives the rebuild schedule from outside, and the schedule is what shows the
   estimates being corrected: a rebuild resets the counts to the survivors, so the next
   one comes after about half of THEM have gone, and the lumps come at halving intervals.
   Estimates left uncorrected would put the second rebuild out of reach.

   Deleting an element that is not in the set is specified here as a no-op. The book does
   not say, and raising is a defensible reading, but a total delete is the easier contract
   to hold in a model, and it matches what marking already does for an element deleted
   twice. *)

module Delete_tests (S : SET_WITH_DELETE with type elem = int) = struct
  module Base = Set_tests (S)

  let delete_all xs s = List.fold_left (fun s x -> S.delete x s) s xs
  let range lo hi = List.init (hi - lo + 1) (fun i -> lo + i)
  let first_of k xs = List.filteri (fun i _ -> i < k) xs

  let run_contract name =
    let t label = Printf.sprintf "%s: %s" name label in
    let holds label f = surviving (t label) f (fun ok -> check (t label) ok) in
    let same a b = List.for_all (fun x -> S.member x a = S.member x b) (range (-1) 101) in
    let s = Base.of_list (evens 50) in
    surviving
      (t "deleting one element")
      (fun () -> S.delete 20 s)
      (fun s' ->
        check (t "a deleted element is not a member") (not (S.member 20 s'));
        check
          (t "deleting one element leaves every other")
          (List.for_all (fun x -> x = 20 || S.member x s') (evens 50));
        check (t "the version before the delete still has it") (S.member 20 s);
        holds "inserting a deleted element brings it back" (fun () ->
          S.member 20 (S.insert 20 s'));
        holds "deleting an element twice is a no-op" (fun () -> same s' (S.delete 20 s')));
    (* The root is on every search path, so a dead root is the first place a search that
       cannot pass a dead node shows. *)
    holds "deleting the root leaves both neighbours reachable" (fun () ->
      let s3 = S.delete 2 (Base.of_list [ 0; 2; 4 ]) in
      S.member 0 s3 && S.member 4 s3 && not (S.member 2 s3));
    holds "deleting an absent element is a no-op" (fun () -> same s (S.delete 21 s));
    surviving
      (t "deleting everything")
      (fun () -> delete_all (evens 50) s)
      (fun gone ->
        check
          (t "a set with everything deleted holds nothing")
          (List.for_all (fun x -> not (S.member x gone)) (range (-1) 101));
        holds "and can be refilled" (fun () -> S.member 8 (S.insert 8 gone)));
    (* Every version of a drain stays correct, on both sides of the rebuild that a drain
       of a hundred passes through. *)
    surviving
      (t "every version of a drain stays correct, across rebuilds")
      (fun () ->
        let xs = evens 100 in
        let order = shuffle 20260928 xs in
        let versions =
          List.fold_left
            (fun (acc, s) x ->
              let s = S.delete x s in
              s :: acc, s)
            ([], Base.of_list xs)
            order
          |> fst
          |> List.rev
        in
        let stale = ref 0 in
        List.iteri
          (fun i v ->
            (* version i is after i + 1 deletions: the first i + 1 of [order] are gone *)
            let gone = first_of (i + 1) order in
            if not (List.for_all (fun x -> S.member x v = not (List.mem x gone)) xs)
            then incr stale)
          versions;
        !stale)
      (fun stale ->
        check_int
          (t "every version of a drain stays correct, across rebuilds")
          ~expect:0
          ~actual:stale);
    (* Against a list model, checked after every operation, with runs long enough to cross
       the rebuild threshold many times over. *)
    Random.init 20260929;
    let bad = ref 0
    and raised = ref 0 in
    for _ = 0 to 299 do
      let s = ref S.empty
      and model = ref [] in
      try
        for _ = 1 to 200 do
          let x = Random.int 40 in
          if Random.int 5 < 3
          then (
            s := S.insert x !s;
            if not (List.mem x !model) then model := x :: !model)
          else (
            s := S.delete x !s;
            model := List.filter (fun y -> y <> x) !model);
          for q = -1 to 40 do
            if S.member q !s <> List.mem q !model then incr bad
          done
        done
      with
      | _ -> incr raised
    done;
    check_int
      (t "member agrees with a list model after every operation, 300 random runs")
      ~expect:0
      ~actual:!bad;
    check_int (t "no operation raises, 300 random runs") ~expect:0 ~actual:!raised
  ;;

  (* The most a delete may allocate without having rebuilt: a path of at most depth_bound
     n levels, each a node and its tuple, plus the re-marked pair and the triple. A
     rebuild with L survivors allocates about 13L words on top of that, so while at least
     32 survive it clears this bound by a wide margin and while at least 64 do, so does
     the rebuild after it. *)
  let path_words n = float_of_int (12 * (depth_bound n + 1))

  let run_costs name =
    let t label = Printf.sprintf "%s: %s" name label in
    (* Condition (2): with half the nodes dead and no rebuild yet, every search, hit, dead
       hit or miss, is still two comparisons per level of the tree that was built. *)
    let n = 1024 in
    let xs = shuffle 20260930 (evens n) in
    let s = delete_all (first_of 500 (shuffle 20260931 xs)) (Base.of_list xs) in
    let dearest =
      List.fold_left
        (fun d q -> max d (count_only (fun () -> S.member q s)))
        0
        (range (-1) ((2 * n) + 1))
    in
    check
      (t
         (Printf.sprintf
            "member stays two comparisons per level with half the nodes dead (dearest \
             %d, bound %d)"
            dearest
            (2 * depth_bound n)))
      (dearest <= 2 * depth_bound n);
    (* The drain: every delete of 4096 distinct elements on the clock, comparisons and
       words, in a random order. [rebuilds] holds, for each delete that allocated more
       than a path, its index and how many elements survived it. *)
    let n = 4096 in
    let xs = shuffle 20260932 (evens n) in
    let order = shuffle 20260933 xs in
    let s = ref (Base.of_list xs)
    and total = ref 0.0
    and dear_cmp = ref 0
    and rebuilds = ref [] in
    List.iteri
      (fun i x ->
        comparisons := 0;
        let s', w = cost (fun () -> S.delete x !s) in
        dear_cmp := max !dear_cmp !comparisons;
        total := !total +. w;
        if w > path_words n then rebuilds := (i + 1, n - i - 1) :: !rebuilds;
        s := s')
      order;
    ignore (Sys.opaque_identity !s);
    let rebuilds = List.rev !rebuilds in
    check
      (t
         (Printf.sprintf
            "every delete makes O(log n) comparisons, rebuilds included (dearest %d, \
             bound %d)"
            !dear_cmp
            (2 * depth_bound n)))
      (!dear_cmp <= 2 * depth_bound n);
    (* Condition (1), read off the lumps. *)
    check
      (t
         (Printf.sprintf
            "rebuilds are rare: %d lumps in a drain of %d"
            (List.length rebuilds)
            n))
      (List.length rebuilds <= floor_log2 n + 2);
    let first =
      match rebuilds with
      | [] -> 0
      | (i, _) :: _ -> i
    in
    check
      (t
         (Printf.sprintf
            "the first rebuild comes when about half the nodes are dead (delete #%d of \
             %d)"
            first
            n))
      (first >= n / 4 && first <= (n / 2) + 2);
    (* Each rebuild after the first comes when about half the survivors of the previous
       one are dead. That is the estimates being corrected: a count left at its old value
       would put the next rebuild twice as far off, past the end of the survivors. Only
       lumps with at least 64 survivors are trusted to have a detectable successor. *)
    let rec spacing_ok = function
      | (i, live) :: ((j, _) :: _ as rest) when live >= 64 ->
        j - i >= live / 4 && j - i <= (live / 2) + 2 && spacing_ok rest
      | _ -> true
    in
    let trusted = List.length (List.filter (fun (_, live) -> live >= 32) rebuilds) in
    check
      (t
         (Printf.sprintf
            "each rebuild comes when about half the survivors of the last are dead (%d \
             lumps with 32+ survivors, at deletes %s)"
            trusted
            (String.concat
               ","
               (List.map (fun (i, _) -> string_of_int i) (first_of 8 rebuilds)))))
      (trusted >= floor_log2 n - 6 && spacing_ok rebuilds);
    check
      (t
         (Printf.sprintf
            "delete is O(log n) amortised: %.0f words per delete over the drain, bound \
             %.0f"
            (!total /. float_of_int n)
            (16.0 *. float_of_int (depth_bound n))))
      (!total /. float_of_int n <= 16.0 *. float_of_int (depth_bound n));
    (* A rebuilt tree is a red-black tree: growing it afterwards keeps Exercise 3.8's
       bound. 1024 in, 600 out through a rebuild, 2048 new ones in. Colours stay invisible
       here as in test_ch3, and the bound has a factor of two of slack, so a rebuild that
       mis-colours its nodes but keeps their order can grow a few levels deeper and still
       pass; what this catches is a rebuild that is not a search tree or not balanced. *)
    let n = 1024 in
    let xs = shuffle 20260934 (evens n) in
    let s = delete_all (first_of 600 (shuffle 20260935 xs)) (Base.of_list xs) in
    let extra = 2048 in
    let grown =
      List.fold_left (fun s x -> S.insert x s) s (List.init extra (fun i -> 2 * (n + i)))
    in
    let d = Base.max_path (n + extra) grown in
    check
      (t
         (Printf.sprintf
            "growth after a rebuild keeps the depth bound (depth %d, bound %d)"
            d
            (depth_bound (n + extra))))
      (d <= depth_bound (n + extra))
  ;;
end

module Deletion = Delete_tests (Rb)

let test_redblack () =
  section "RedBlackSet (8.1): the Section 3.3 set, and the delete of Exercise 8.1";
  Rb_tests.run_contract "RedBlackSet";
  Rb_tests.run_costs "RedBlackSet";
  let differs = ref [] in
  List.iter
    (fun n ->
      List.iter
        (fun (order, xs) ->
          let here = Rb_tests.gap_profile n (Rb_tests.of_list xs)
          and there = Original_tests.gap_profile n (Original_tests.of_list xs) in
          if here <> there then differs := (order, n) :: !differs)
        (orders n))
    set_sizes;
  check
    (Printf.sprintf
       "RedBlackSet: the copy has Chapter 3's shape, gap for gap%s"
       (match !differs with
        | [] -> ""
        | (order, n) :: _ -> Printf.sprintf " -- differs for %s n=%d" order n))
    (!differs = []);
  (* What a delete costs means nothing until it behaves like one. *)
  let before = !failures in
  Deletion.run_contract "RedBlackSet delete";
  if !failures > before
  then
    Printf.printf
      "  SKIP  RedBlackSet delete: cost checks -- the contract above does not hold\n"
  else Deletion.run_costs "RedBlackSet delete"
;;

(* ------------------------------------------------------------------- runner *)

(* A regression can make a function raise where the test did not expect it. Report that as
   a failure and carry on rather than hiding it. *)
let run name f =
  match f () with
  | () -> ()
  | exception e ->
    incr failures;
    Printf.printf "  FAIL  %s: unexpected exception %s\n" name (Printexc.to_string e)
;;

let () =
  run "RedBlackSet" test_redblack;
  run "HoodMelvilleQueue" test_hood_melville;
  run "ConstantTimeConsQueue" test_cons_queue;
  run "BankersDeque" test_bankers_deque;
  Printf.printf "\n%d checks, %d failures\n\n" !checks !failures;
  if !failures > 0 then exit 1
;;
