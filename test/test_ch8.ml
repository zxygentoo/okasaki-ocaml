(* Tests for Chapter 8: the Hood-Melville real-time queue of Figure 8.1 (section 8.2.1),
   on the schedule of Exercise 8.2 and with the single diff field of Exercise 8.3. Plain
   OCaml, no test framework, matching the earlier chapters.

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

let check_raises name expected f =
  incr checks;
  match f () with
  | _ ->
    incr failures;
    Printf.printf
      "  FAIL  %s: expected %s, got no exception\n"
      name
      (Printexc.to_string expected)
  | exception e ->
    if e <> expected
    then (
      incr failures;
      Printf.printf
        "  FAIL  %s: expected %s, got %s\n"
        name
        (Printexc.to_string expected)
        (Printexc.to_string e))
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

(* ---------------------------------------------------------------- the clock *)

(* Words allocated by [f], read before and after. Sys.opaque_identity stops the optimiser
   discarding the result and with it the allocation being measured. The clock counts in
   integers: a float reading would box, and the two words of the box would land inside the
   measurement. *)
let words () = int_of_float (Gc.minor_words ())

let cost f =
  let before = words () in
  let r = Sys.opaque_identity (f ()) in
  r, float_of_int (words () - before)
;;

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

  (* head/tail to exhaustion. That this returns the elements in the order they were
     snoc'ed is the whole behavioural specification of a queue. *)
  let drain q =
    let rec go acc q =
      if Q.is_empty q then List.rev acc else go (Q.head q :: acc) (Q.tail q)
    in
    go [] q
  ;;

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
    check_raises (t "head on empty raises") (Failure "head: empty queue") (fun () ->
      Q.head Q.empty);
    check_raises (t "tail on empty raises") (Failure "tail: empty queue") (fun () ->
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
        check_raises
          (t "head on a drained queue raises")
          (Failure "head: empty queue")
          (fun () -> Q.head drained);
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
  run "HoodMelvilleQueue" test_hood_melville;
  Printf.printf "\n%d checks, %d failures\n\n" !checks !failures;
  if !failures > 0 then exit 1
;;
