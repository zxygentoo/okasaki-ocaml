(* Tests for Chapter 7: the real-time queue of Figure 7.1 (section 7.2), the size
   functions of Exercise 7.2 on top of it, the scheduled binomial heap of Figure 7.2
   (section 7.3) and the scheduled bottom-up mergesort of Figure 7.3 (section 7.4). Plain
   OCaml, no test framework, matching the earlier chapters. The queue first; the heap and
   the mergesort have their own preambles further down.

   Figure 7.1 promises what no queue before it could: every operation in O(1) WORST-CASE
   time, and still when used persistently. Chapter 5 asserted amortised bounds over whole
   sequences and Chapter 6 over traces, because their one expensive tail, the reverse, was
   real and had only to be rare. Here it must not exist. Section 7.2 removes it in two
   moves. First, rotate fuses the reverse into the append, so that each cell of the new
   front does one step of the reverse when forced and no suspension has more than O(1)
   intrinsic cost. Second, a schedule: the queue keeps a pointer s to the first
   unevaluated cell of its front, and every snoc and tail forces one cell before
   returning, so that by the time a rotation needs a cell of the old front, the old front
   has been forced through to its end. "No operation forces more than three suspensions",
   and each executes in O(1) time.

   A worst-case bound is a statement about single operations, so the checks below put
   every operation of a sequence on the clock by itself and assert the DEAREST, at two
   sizes a hundred times apart. QUEUE seals the representation, so the clock is
   allocation, as in test_ch5 and test_ch6. It is a faithful proxy here: every step of a
   rotation allocates a cons and a suspension, and the monolithic reverse it replaces
   would allocate three words per element in one operation. Whether the clock can see such
   a lump at all is checked, not assumed: the same probe is run once over the banker's
   queue of Figure 6.1, whose drain must show its reverse. Persistence is checked as
   Chapter 6 checked it, from every version of a build and of a drain, but with the first
   run measured rather than a later one: a real-time bound owes nothing to memoisation.

   The behavioural contract is that of test_ch5 and test_ch6, since this is the same QUEUE
   signature. *)

open Okasaki.Ch7

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

(* The most a single operation may allocate, in words. Outside the schedule an operation
   of Figure 7.1 is a cons onto the rear and a fresh triple, 7 words. The one cell of the
   schedule it forces runs a step of rotate: a cons, the suspended cons pushed onto the
   accumulator and the suspension of the rest of the rotation, about 20 more. The
   operation that starts a rotation suspends the first call to rotate instead, fewer
   still. The dearest operation measured here is a snoc, at 27 words; the dearest tail
   is 24. 48 leaves room for those and for the probe's own noise, and is nowhere near an
   operation that is really linear: at the sizes used here that is out by a factor of a
   hundred. *)
let constant = 48.0

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
    (* The two places the invariant can be lost. is_empty and head look at the front
       alone, so a queue that lets its front run dry while elements wait in the rear
       reports empty, and raises on head, with elements still in it. In this queue that is
       what a snoc or a tail that skips the schedule does: the rotation is triggered by
       the schedule running out, and nothing else moves the rear to the front. *)
    head_is "snoc onto the empty queue makes its element the head" 7 (fun () ->
      Q.snoc Q.empty 7);
    head_is "tail past the last front element moves on to the rear" 2 (fun () ->
      Q.tail (of_list [ 1; 2; 3 ]));
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
    (* Randomised, against the obvious model: a list, snoc at the back, tail at the front.
       Checked after every operation and not only at the end, because a lost invariant
       shows up as a wrong is_empty or head long before it shows up in a drain. *)
    Random.init 20260921;
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
       stays correct, and two futures of one queue do not see each other. *)
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
    eq "does not leak into the other" [ 1; 2; 3; 5 ] b
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

  (* The sequences of test_ch6, as data. They differ in where the rotations fall: ever
     larger ones at ever longer intervals, a tiny one at every step, or two snocs to every
     tail so the front never stops growing. The heads sequence is the one in which a head
     can do work: the head taken right after a rotation forces the first cell of the new
     front, and that cell is a step of rotate. *)
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
    Random.init 20260921;
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
     clock. In Figure 6.1 one of these tails ran the reverse. *)
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
     all": each round builds its own suspensions. Here each round is also its own
     schedule, and pays as it goes. *)
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
    Random.init 20260923;
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

(* Whether the clock can see a lump sum at all. The probe above, run over the banker's
   queue of Figure 6.1, must find the tail that runs the reverse: in a drain of a queue
   built by n snocs, the last rotation moved at least a sixth of the elements and the
   drain reverses them in a single tail, three words a cons. Without this, every check on
   the real-time queue could pass by measuring nothing. *)
module Control = Worst_case (Okasaki.Ch6.BankersQueue (Okasaki.Ch4.Stream))

let test_guard () =
  let n = 1_000 in
  let i, op, c = Control.dearest (Control.fill_then_drain n) in
  check
    (Printf.sprintf
       "guard: the same probe over Figure 6.1's queue sees its reverse, #%d (%s) at %.0f \
        words in a fill and drain of %d"
       i
       (describe op)
       c
       n)
    (op = Tail && c >= float_of_int n /. 2.)
;;

(* -------------------------------------------------------- RealTimeQueue (7.2) *)

module Q = RealTimeQueue (Okasaki.Ch4.Stream)
module Contract = Queue_tests (Q)
module Costs = Worst_case (Q)

(* What a queue costs means nothing until it behaves like one, and a queue that raises
   half way through a sequence would take the rest of the section down with it. The sizes
   of Exercise 7.2 wait on the contract too. *)
let contract_holds = ref false

let test_real_time () =
  section "RealTimeQueue (7.2)";
  let before = !failures in
  Contract.run_contract "RealTimeQueue";
  contract_holds := !failures = before;
  if not !contract_holds
  then
    Printf.printf
      "  SKIP  RealTimeQueue: cost checks -- the contract above does not hold\n"
  else (
    test_guard ();
    if Costs.run_sequences "RealTimeQueue"
    then Costs.run_versions "RealTimeQueue, persistently"
    else
      Printf.printf
        "  SKIP  RealTimeQueue: persistence checks -- not real-time in one thread\n")
;;

(* ------------------------------------------------------ sizes (Exercise 7.2) *)

(* Exercise 7.2 asks for the size of a queue from |s| and |r| alone. The invariant |s| =
   |f| - |r| gives |f| = |s| + |r|, so |f| + |r| is |s| + 2|r|. Its second question, how
   much faster that runs than counting f and r, is a matter of cells walked: |s| + |r| =
   |f| of them against |f| + |r|, with the list walked once either way. The saving is the
   |r| cells of the front that the schedule has already passed: none of the front just
   after a rotation, all of it just before the next. Cells walked is a count the seal
   hides and allocation cannot see, so that comparison is not measured here. Two things
   are.

   The first is what makes the formula valid at all. It gives the right answer exactly
   when the invariant holds, so agreement with a list model after every operation, and on
   every version of a queue, is the invariant asserted from outside for the first time in
   this file. The second is the one cost fact about the formula the clock can see.
   Counting s walks the schedule to its end and forces every cell on it, which is the very
   work the schedule meant to spread over the next |s| operations. Section 7.1 says
   forcing early "does no harm since it can only make an algorithm run faster", and so it
   is: those operations then find their cells memoised and allocate nothing beyond a cons
   and a triple, while the same operations on an untouched twin of the queue pay for their
   rotate steps as usual. *)

module Size_tests (Q : QUEUE_WITH_SIZES) = struct
  let of_list xs = List.fold_left Q.snoc Q.empty xs

  let drain q =
    let rec go acc q =
      if Q.is_empty q then List.rev acc else go (Q.head q :: acc) (Q.tail q)
    in
    go [] q
  ;;

  let run_sizes name =
    let t label = Printf.sprintf "%s: %s" name label in
    let both label expect q =
      surviving
        (t label)
        (fun () -> Q.size_sr q, Q.size_fr q)
        (fun (sr, fr) ->
          check_int (t (label ^ ", from s and r")) ~expect ~actual:sr;
          check_int (t (label ^ ", from f and r")) ~expect ~actual:fr)
    in
    both "empty has size 0" 0 Q.empty;
    both "a singleton has size 1" 1 (Q.snoc Q.empty 1);
    both "a queue drained to nothing has size 0" 0 (Q.tail (Q.tail (of_list [ 1; 2 ])));
    (* Every size from 0 to n, visited on the way up and on the way down, both sizes taken
       at every step. The sizes either side of a rotation are the ones the formula has to
       get right; and taking a size in the middle of a run is itself a test, since it
       forces the schedule ahead of the operations that were going to. *)
    let n = 100 in
    let wrong = ref [] in
    let at step expect q =
      let sr = Q.size_sr q
      and fr = Q.size_fr q in
      if sr <> expect || fr <> expect then wrong := (step, expect, sr, fr) :: !wrong
    in
    surviving
      (t "sizes along a build and a drain")
      (fun () ->
        let q = ref Q.empty in
        for i = 1 to n do
          q := Q.snoc !q i;
          at ("snoc " ^ string_of_int i) i !q
        done;
        for i = 1 to n do
          q := Q.tail !q;
          at ("tail " ^ string_of_int i) (n - i) !q
        done)
      (fun () ->
        check
          (t
             (Printf.sprintf
                "both sizes are right after every step of a build and a drain of %d%s"
                n
                (match List.rev !wrong with
                 | [] -> ""
                 | (step, e, sr, fr) :: _ ->
                   Printf.sprintf
                     " -- after %s expected %d, got %d from s and r, %d from f and r"
                     step
                     e
                     sr
                     fr)))
          (!wrong = []));
    (* Random runs against the list model, as in the contract, both sizes checked after
       every operation. *)
    Random.init 20260924;
    let bad = ref 0
    and raised = ref 0 in
    for _ = 0 to 299 do
      let q = ref Q.empty
      and size = ref 0 in
      try
        for i = 0 to 59 do
          if !size = 0 || Random.int 3 > 0
          then (
            q := Q.snoc !q i;
            incr size)
          else (
            q := Q.tail !q;
            decr size);
          if Q.size_sr !q <> !size || Q.size_fr !q <> !size then incr bad
        done
      with
      | Failure _ -> incr raised
    done;
    check_int
      (t "both sizes agree with a list model after every operation, 300 random runs")
      ~expect:0
      ~actual:!bad;
    check_int (t "no operation raises in those runs") ~expect:0 ~actual:!raised;
    (* Persistence: every version of a build and of a drain keeps its own size after later
       versions have been made from it. *)
    let n = 64 in
    let build = Array.make (n + 1) Q.empty in
    for i = 1 to n do
      build.(i) <- Q.snoc build.(i - 1) i
    done;
    let drain = Array.make (n + 1) Q.empty in
    drain.(0) <- build.(n);
    for i = 1 to n do
      drain.(i) <- Q.tail drain.(i - 1)
    done;
    let stale = ref 0 in
    for k = 0 to n do
      if Q.size_sr build.(k) <> k || Q.size_fr build.(k) <> k then incr stale;
      if Q.size_sr drain.(k) <> n - k || Q.size_fr drain.(k) <> n - k then incr stale
    done;
    check_int
      (t
         (Printf.sprintf
            "every version of a build and a drain of %d still reports its own size"
            n))
      ~expect:0
      ~actual:!stale
  ;;

  (* The most an operation may allocate when every suspension it forces is already
     memoised: a cons onto the rear and a triple, and the triple at most twice over, 11
     words; the snocs measured here take 7. Nothing else in an operation of Figure 7.1
     allocates. *)
  let memoised = 12.0

  (* After 2^k - 1 snocs the queue has just started a rotation: r is empty and the
     schedule is the whole of the new front, none of it forced. Counting s from there
     walks all of it. *)
  let run_forcing name =
    let t label = Printf.sprintf "%s: %s" name label in
    let n = 15 in
    let walked = of_list (upto n)
    and untouched = of_list (upto n) in
    let counted, walking = cost (fun () -> Q.size_sr walked) in
    check_int (t "the count itself is right") ~expect:n ~actual:counted;
    check
      (t
         (Printf.sprintf
            "counting s at the start of a rotation of %d cells forces the schedule to \
             its end, %.0f words: more than any one operation may"
            n
            walking))
      (walking > constant);
    (* n snocs from each queue, one per schedule cell, each on the clock. *)
    let snocs q =
      let q = ref q
      and worst = ref 0.0
      and total = ref 0.0 in
      for i = 1 to n do
        let q', c = cost (fun () -> Q.snoc !q i) in
        q := q';
        worst := Float.max !worst c;
        total := !total +. c
      done;
      !q, !worst, !total
    in
    let walked', w_worst, w_total = snocs walked in
    let _, _, u_total = snocs untouched in
    check
      (t
         (Printf.sprintf
            "the %d snocs after it find every schedule cell memoised, dearest %.0f words"
            n
            w_worst))
      (w_worst <= memoised);
    check
      (t
         (Printf.sprintf
            "the same %d snocs on an untouched twin do that work instead, %.0f words \
             against %.0f"
            n
            u_total
            w_total))
      (u_total > w_total);
    (* And no harm done: the queue that was counted still behaves. *)
    surviving
      (t "the counted queue still drains in order")
      (fun () -> drain walked')
      (fun actual ->
        check_eq
          (t "the counted queue still drains in order")
          ~expect:(upto n @ List.init n (fun i -> i + 1))
          ~actual
          string_of_int_list)
  ;;
end

module Sizes = Size_tests (Q)

let test_sizes () =
  section "Exercise 7.2";
  if not !contract_holds
  then Printf.printf "  SKIP  Exercise 7.2 -- the contract does not hold\n"
  else (
    Sizes.run_sizes "Exercise 7.2";
    Sizes.run_forcing "Exercise 7.2")
;;

(* ------------------------------------------------ ScheduledBinomialHeap (7.3) *)

(* Figure 7.2 is the lazy binomial heap of Figure 6.2 with two changes. The list of trees
   becomes a stream of digits with the zeros written out, so that insTree can hand back
   one digit at a time instead of doing all its links at once; and a schedule of
   unfinished insTree calls is kept, of which every insert executes two steps. p.90
   guesses that "executing two steps per insert will be enough", and Theorem 7.1 makes the
   guess a proof: no unevaluated suspension ever depends on another, so a step is one link
   at most. The claims of p.92 are insert in O(1) worst-case time, and merge, find_min and
   delete_min in O(log n) worst-case time, the last three because a heap never holds more
   than O(log n) unevaluated suspensions and each of them simply forces the lot, merge and
   delete_min through normalize and find_min on its way down.

   Two instruments, as in test_ch6: comparisons, through the counting element type, which
   see every link; and words, which see the suspensions besides. Both bounds are
   worst-case, so both are asserted on the dearest single operation of a run and never on
   a total. For insert the bound has no constant to hide behind: two exec steps, one link
   each, is two comparisons at most, from any heap and from any version. The first digit
   that insTree itself examines is completed, by the theorem's two completed zeros, which
   is Exercise 7.3's point and the reason the port's insTree can look at its argument at
   once. For the other three the bound is a.L + b with L = log2 (n + 1), and it is checked
   at n = 1000 and at n = 100000, where an operation that is really linear is out by a
   factor of thousands. That the probe can tell O(1) from O(log n) is checked on Figure
   3.4's strict heap, whose insert into the all-ones heap of 2^k - 1 elements links k
   times on the spot.

   The contract is test_ch6's. The shape checks read the heap through find_min's
   comparisons, once a merge with the empty heap has normalized it: remove_min_tree
   compares once per tree but the first. *)

let comparisons = ref 0

module Counting_int = struct
  type t = int

  let eq a b =
    incr comparisons;
    a = b
  ;;

  let lt a b =
    incr comparisons;
    a < b
  ;;

  let leq a b =
    incr comparisons;
    a <= b
  ;;
end

(* The result of one call of [f], with the comparisons and the words it spent. *)
let spent f =
  comparisons := 0;
  let before = words () in
  let r = Sys.opaque_identity (f ()) in
  r, (float_of_int !comparisons, float_of_int (words () - before))
;;

let log2 n = log (float_of_int n) /. log 2.

(* floor (log2 n), for n >= 1: a binomial heap of n elements holds at most floor (log2
   (n + 1)) trees. *)
let floor_log2 n =
  let rec go acc n = if n <= 1 then acc else go (acc + 1) (n / 2) in
  go 0 n
;;

let popcount n =
  let rec go acc n = if n = 0 then acc else go (acc + (n land 1)) (n lsr 1) in
  go 0 n
;;

(* The budgets of a single operation, worst case, given the size of the heap it is applied
   to. An insert is a node, the suspended digit insTree returns, a cons onto the schedule
   and a pair, and then two exec steps, each a link -- a node and a cons -- with the digit
   it produces and the suspension of the next; about 60 words all told, and two
   comparisons exactly. A query walks at most L trees comparing once per tree, forces at
   most L outstanding links on the way, and delete_min then merges L children back in, at
   most another 2L links: 4L + 4 comparisons leaves room for all of it. Words follow the
   same shape, a pair, a cons and a suspended digit per level. Both query budgets are
   about twice what the dearest operation measured spends. *)
let insert_comparisons = 2.0
let insert_words = 96.0
let query_comparisons l = (4. *. l) +. 4.
let query_words l = (96. *. l) +. 128.

(* The dearest operation of a run, as a fraction of its budget, kept with what it cost and
   where it was. A run is within its bound when the fraction is at most one. *)
type dear =
  { at : int
  ; op : string
  ; ratio : float
  ; c : float
  ; w : float
  ; size : int
  }

let no_dear = { at = 0; op = ""; ratio = 0.0; c = 0.0; w = 0.0; size = 0 }

let dearer d ~at ~op ~size (c, w) =
  let cb, wb =
    if op = "insert"
    then insert_comparisons, insert_words
    else (
      let l = log2 (size + 1) in
      query_comparisons l, query_words l)
  in
  let ratio = Float.max (c /. cb) (w /. wb) in
  if ratio > d.ratio then { at; op; ratio; c; w; size } else d
;;

let show_dear d =
  Printf.sprintf
    "dearest is #%d (%s on %d elements) at %.0f comparisons and %.0f words"
    d.at
    d.op
    d.size
    d.c
    d.w
;;

module Heap_tests (H : HEAP with type Element.t = int) = struct
  let of_list xs = List.fold_left (fun h x -> H.insert x h) H.empty xs

  (* A merge with the empty heap normalizes: every suspension in the digit stream is
     forced and the schedule is emptied. What the clocks then see is the heap's own. *)
  let normalized h = H.merge h H.empty

  (* find_min/delete_min to exhaustion. That this comes out sorted is the whole
     behavioural specification of a heap. *)
  let drain h =
    let rec go acc h =
      if H.is_empty h then List.rev acc else go (H.find_min h :: acc) (H.delete_min h)
    in
    go [] h
  ;;

  (* ---------------------------------------------------------------- contract *)

  let run_contract name =
    let t label = Printf.sprintf "%s: %s" name label in
    let eq label expect h =
      surviving
        (t label)
        (fun () -> drain h)
        (fun actual -> check_eq (t label) ~expect ~actual string_of_int_list)
    in
    check (t "empty is empty") (H.is_empty H.empty);
    check (t "a singleton is not empty") (not (H.is_empty (H.insert 1 H.empty)));
    check_raises
      (t "find_min on empty raises")
      (Failure "find_min: empty heap")
      (fun () -> H.find_min H.empty);
    check_raises
      (t "delete_min on empty raises")
      (Failure "delete_min: empty heap")
      (fun () -> ignore (H.is_empty (H.delete_min H.empty)));
    check_int (t "find_min of a singleton") ~expect:5 ~actual:(H.find_min (of_list [ 5 ]));
    check
      (t "delete_min of a singleton is empty")
      (H.is_empty (H.delete_min (of_list [ 5 ])));
    eq "drain is sorted" [ 1; 2; 3; 4; 5; 6; 7 ] (of_list [ 4; 2; 6; 1; 3; 5; 7 ]);
    eq "a repeated element is kept when it is the root" [ 5; 5 ] (of_list [ 5; 5 ]);
    eq
      "a repeated element is kept when it is deep on the left"
      [ 1; 2; 3; 4; 5; 5 ]
      (of_list [ 5; 4; 3; 2; 1; 5 ]);
    eq
      "a repeated element is kept when it is deep on the right"
      [ 1; 1; 2; 3; 4; 5 ]
      (of_list [ 1; 2; 3; 4; 5; 1 ]);
    eq "duplicates are all kept" [ 1; 1; 1; 2; 2; 3 ] (of_list [ 2; 1; 3; 1; 2; 1 ]);
    surviving
      (t "the minimum is found after ascending inserts")
      (fun () -> H.find_min (of_list [ 1; 2; 3 ]))
      (fun m ->
        check_int (t "the minimum is found after ascending inserts") ~expect:1 ~actual:m);
    surviving
      (t "the minimum is found after descending inserts")
      (fun () -> H.find_min (of_list [ 3; 2; 1 ]))
      (fun m ->
        check_int (t "the minimum is found after descending inserts") ~expect:1 ~actual:m);
    eq
      "merge is multiset union"
      [ 1; 2; 3; 4; 5; 6 ]
      (H.merge (of_list [ 1; 4; 6 ]) (of_list [ 2; 3; 5 ]));
    eq
      "merge with an empty right operand"
      [ 1; 2; 3 ]
      (H.merge (of_list [ 3; 1; 2 ]) H.empty);
    eq
      "merge with an empty left operand"
      [ 1; 2; 3 ]
      (H.merge H.empty (of_list [ 3; 1; 2 ]));
    check (t "merge of two empties is empty") (H.is_empty (H.merge H.empty H.empty));
    (* Randomised, against List.sort as the reference, with few distinct values so that
       equal elements are everywhere. *)
    Random.init 20260922;
    let bad_insert = ref 0
    and bad_merge = ref 0
    and raised = ref 0 in
    for _ = 0 to 299 do
      let xs = List.init (Random.int 40) (fun _ -> Random.int 25)
      and ys = List.init (Random.int 40) (fun _ -> Random.int 25) in
      match
        if drain (of_list xs) <> List.sort compare xs then incr bad_insert;
        if drain (H.merge (of_list xs) (of_list ys)) <> List.sort compare (xs @ ys)
        then incr bad_merge
      with
      | () -> ()
      | exception Failure _ -> incr raised
    done;
    check_int
      (t "no operation raises on a non-empty heap, 300 random runs")
      ~expect:0
      ~actual:!raised;
    check_int (t "insert then drain, 300 random lists") ~expect:0 ~actual:!bad_insert;
    check_int (t "merge then drain, 300 random pairs") ~expect:0 ~actual:!bad_merge;
    (* Persistence: no operation may disturb its operands. With suspensions in the picture
       that includes forcing: a heap looked at through one future must read the same
       through another. *)
    let h = of_list [ 5; 3; 8; 1 ] in
    let a = H.insert 0 h
    and b = H.insert 4 h
    and c = H.delete_min h
    and d = H.merge h h in
    eq "one future of a shared heap" [ 0; 1; 3; 5; 8 ] a;
    eq "another" [ 1; 3; 4; 5; 8 ] b;
    eq "a third" [ 3; 5; 8 ] c;
    eq "a fourth" [ 1; 1; 3; 3; 5; 5; 8; 8 ] d;
    eq "and the operand is untouched" [ 1; 3; 5; 8 ] h
  ;;

  (* --------------------------------------------------------------- structure *)

  (* Trees in [h]: find_min compares once per tree but the first, once nothing is left to
     force. *)
  let trees h =
    let nh = normalized h in
    let _, (c, _) = spent (fun () -> H.find_min nh) in
    int_of_float c + 1
  ;;

  let run_structure name =
    let t label = Printf.sprintf "%s: %s" name label in
    let bad = ref 0
    and first = ref "" in
    Random.init 20260918;
    for n = 1 to 120 do
      let xs = List.init n (fun _ -> Random.int 1000) in
      let h = ref (of_list xs)
      and left = ref n in
      while not (H.is_empty !h) do
        if trees !h <> popcount !left
        then (
          incr bad;
          if !first = ""
          then
            first
            := Printf.sprintf
                 " -- first at n=%d, %d left, %d trees, popcount %d"
                 n
                 !left
                 (trees !h)
                 (popcount !left));
        h := H.delete_min !h;
        decr left
      done
    done;
    check
      (t (Printf.sprintf "one tree per 1 bit of n, at every step of a drain%s" !first))
      (!bad = 0);
    let over = ref 0 in
    List.iter
      (fun n -> if trees (of_list (upto n)) > floor_log2 (n + 1) then incr over)
      [ 1; 7; 8; 15; 16; 100; 1000; 10_000 ];
    check_int (t "at most floor(log2 (n+1)) trees") ~expect:0 ~actual:!over
  ;;

  (* ------------------------------------------- every operation on its own clock *)

  type hop =
    | Insert of int
    | Delete_min
    | Find_min

  (* Runs [ops] from the empty heap with every operation on the clocks by itself, and
     reports the dearest insert and the dearest query, each against its own budget. The
     size of the heap is tracked alongside, since a query's budget depends on it. *)
  let dearest ops =
    let h = ref H.empty
    and size = ref 0
    and sum = ref 0
    and insert = ref no_dear
    and query = ref no_dear in
    Array.iteri
      (fun i op ->
        match op with
        | Insert x ->
          let h', cw = spent (fun () -> H.insert x !h) in
          h := h';
          insert := dearer !insert ~at:i ~op:"insert" ~size:!size cw;
          incr size
        | Delete_min ->
          let h', cw = spent (fun () -> H.delete_min !h) in
          h := h';
          query := dearer !query ~at:i ~op:"delete_min" ~size:!size cw;
          decr size
        | Find_min ->
          let x, cw = spent (fun () -> H.find_min !h) in
          sum := !sum + x;
          query := dearer !query ~at:i ~op:"find_min" ~size:!size cw)
      ops;
    ignore (Sys.opaque_identity !h);
    ignore (Sys.opaque_identity !sum);
    !insert, !query
  ;;

  let build_then_drain xs n =
    Array.init (2 * n) (fun i -> if i < n then Insert xs.(i) else Delete_min)
  ;;

  let random_ints seed n bound =
    Random.init seed;
    Array.init n (fun _ -> Random.int bound)
  ;;

  (* The sequences of test_ch6, as data. Ascending inserts are the ones whose carries run
     longest; equal elements make every link a tie. *)
  let sequences =
    [ ( "n ascending inserts, then n delete_mins"
      , fun n -> build_then_drain (Array.init n (fun i -> i + 1)) n )
    ; ( "n random inserts, then n delete_mins"
      , fun n -> build_then_drain (random_ints 20260924 n 1_000_000) n )
    ; ("n equal inserts, then n delete_mins", fun n -> build_then_drain (Array.make n 7) n)
    ; ( "a find_min after every insert"
      , fun n ->
          Array.init (2 * n) (fun i ->
            if i mod 2 = 0 then Insert ((i / 2) + 1) else Find_min) )
    ; ( "insert then delete_min at a steady size of 1000, n times over"
      , fun n ->
          Array.init
            (1000 + (2 * n))
            (fun i ->
              if i < 1000 then Insert i else if i mod 2 = 0 then Insert i else Delete_min)
      )
    ]
  ;;

  (* Worst case, asserted the only way a worst-case bound can be: on the dearest single
     operation. True if every sequence stayed within both budgets. The large size is
     guarded on the small one, as before. *)
  let run_sequences name =
    let t label = Printf.sprintf "%s: %s" name label in
    let ok = ref true in
    List.iter
      (fun (sequence, ops) ->
        let within label n =
          let insert, query = dearest (ops n) in
          let fine d = d.ratio <= 1.0 in
          check
            (t (Printf.sprintf "%s, %s at n=%d: %s" sequence label n (show_dear insert)))
            (fine insert);
          check
            (t (Printf.sprintf "%s, %s at n=%d: %s" sequence label n (show_dear query)))
            (fine query);
          fine insert && fine query
        in
        if not (within "O(1) and O(log n) worst-case" 1_000)
        then (
          ok := false;
          Printf.printf
            "  SKIP  %s: %s at n=100000 -- over budget at n=1000\n"
            name
            sequence)
        else if not (within "still so, a hundred times longer" 100_000)
        then ok := false)
      sequences;
    !ok
  ;;

  (* Merges: n singletons merged pairwise into one heap, every merge on the clocks, and
     the result drained. A merge's budget is that of the heap it produces. *)
  let run_merges name n =
    let t label = Printf.sprintf "%s: %s" name label in
    let query = ref no_dear
    and at = ref 0 in
    let rec round = function
      | (a, sa) :: (b, sb) :: rest ->
        incr at;
        let m, cw = spent (fun () -> H.merge a b) in
        query := dearer !query ~at:!at ~op:"merge" ~size:(sa + sb) cw;
        (m, sa + sb) :: round rest
      | l -> l
    in
    let rec go = function
      | [ (h, _) ] -> h
      | [] -> H.empty
      | l -> go (round l)
    in
    let h = go (List.init n (fun i -> H.insert i H.empty, 1)) in
    check
      (t (Printf.sprintf "%d singletons merged pairwise, %s" n (show_dear !query)))
      (!query.ratio <= 1.0);
    let drained = ref no_dear
    and h = ref h in
    for i = 1 to n do
      let h', cw = spent (fun () -> H.delete_min !h) in
      h := h';
      drained := dearer !drained ~at:i ~op:"delete_min" ~size:(n - i + 1) cw
    done;
    check
      (t (Printf.sprintf "and then drained, %s" (show_dear !drained)))
      (!drained.ratio <= 1.0)
  ;;

  (* -------------------------------------- versions: several futures of one heap *)

  (* Every version of a build and of a drain, with one operation of each kind taken from
     each, on the clocks, the first time round. Nothing is forced beforehand: a worst-case
     bound owes nothing to memoisation. *)
  let run_versions name =
    let t label = Printf.sprintf "%s: %s" name label in
    let opaque x = ignore (Sys.opaque_identity x) in
    let sweep label v ~size =
      List.iter
        (fun (op, f, needs) ->
          let d = ref no_dear in
          Array.iteri
            (fun k h ->
              if size k >= needs
              then (
                let (), cw = spent (fun () -> f h) in
                d := dearer !d ~at:k ~op ~size:(size k) cw))
            v;
          check
            (t (Printf.sprintf "%s from every version of %s, %s" op label (show_dear !d)))
            (!d.ratio <= 1.0))
        [ "insert", (fun h -> opaque (H.insert 0 h)), 0
        ; "find_min", (fun h -> opaque (H.find_min h)), 1
        ; "delete_min", (fun h -> opaque (H.delete_min h)), 1
        ; "merge", (fun h -> opaque (H.merge h h)), 0
        ]
    in
    let n = 2_000 in
    let v = Array.make (n + 1) H.empty in
    for i = 1 to n do
      v.(i) <- H.insert i v.(i - 1)
    done;
    sweep (Printf.sprintf "a build of %d" n) v ~size:Fun.id;
    let n = 1_000 in
    let v = Array.make (n + 1) H.empty in
    v.(0) <- of_list (upto n);
    for i = 1 to n do
      v.(i) <- H.delete_min v.(i - 1)
    done;
    sweep (Printf.sprintf "a drain of %d" n) v ~size:(fun k -> n - k);
    (* n operations, each applied to a version chosen at random among all built so far,
       merges included, and each on the clocks against the budget of the heap it makes.
       Sizes are tracked, since merging versions of versions makes heaps far larger than
       the trace is long; they are capped so that L stays a number. *)
    let n = 20_000 in
    Random.init 20260924;
    let from = Array.init n (fun i -> Random.int (i + 1)) in
    let other = Array.init n (fun i -> Random.int (i + 1)) in
    let kind = Array.init n (fun _ -> Random.int 4) in
    let v = Array.make (n + 1) H.empty in
    let size = Array.make (n + 1) 0 in
    let cap = 1 lsl 40 in
    let d = ref no_dear in
    for i = 1 to n do
      let q = v.(from.(i - 1))
      and sq = size.(from.(i - 1)) in
      let op, sz =
        match kind.(i - 1) with
        | 2 when sq + size.(other.(i - 1)) <= cap -> "merge", sq + size.(other.(i - 1))
        | 3 when sq > 0 -> "delete_min", sq - 1
        | _ -> "insert", sq + 1
      in
      let h, cw =
        spent (fun () ->
          match op with
          | "merge" -> H.merge q v.(other.(i - 1))
          | "delete_min" -> H.delete_min q
          | _ -> H.insert i q)
      in
      v.(i) <- h;
      size.(i) <- sz;
      d := dearer !d ~at:i ~op ~size:sz cw
    done;
    ignore (Sys.opaque_identity v);
    check
      (t
         (Printf.sprintf
            "a random trace of %d operations, each on a random earlier version, %s"
            n
            (show_dear !d)))
      (!d.ratio <= 1.0)
  ;;
end

(* -------------------------------------------------------------------- guard *)

(* Whether the probe can tell O(1) from O(log n): over Figure 3.4's strict heap, an insert
   into the all-ones heap of 2^k - 1 elements links k times on the spot, and the same
   clocks must see every one of them. Without this, the insert checks above could pass on
   a probe that sees nothing. *)
module Strict_heap = Okasaki.Ch3.BinomialHeap (Counting_int)
module Strict = Heap_tests (Strict_heap)

let test_heap_guard () =
  let k = 16 in
  let h = Strict.of_list (upto ((1 lsl k) - 1)) in
  let _, (c, _) = spent (fun () -> Strict_heap.insert 0 h) in
  check
    (Printf.sprintf
       "guard: the same probe over Figure 3.4's heap sees the insert into the all-ones \
        heap of 2^%d - 1 link %.0f times"
       k
       c)
    (c >= float_of_int k)
;;

(* ------------------------------------------------ ScheduledBinomialHeap, run *)

module Scheduled = ScheduledBinomialHeap (Counting_int) (Okasaki.Ch4.Stream)
module Heap_checks = Heap_tests (Scheduled)

let test_scheduled_binomial () =
  section "ScheduledBinomialHeap (7.3)";
  let before = !failures in
  Heap_checks.run_contract "ScheduledBinomialHeap";
  Heap_checks.run_structure "ScheduledBinomialHeap";
  if !failures > before
  then
    Printf.printf
      "  SKIP  ScheduledBinomialHeap: cost checks -- the contract or the structure above \
       does not hold\n"
  else (
    test_heap_guard ();
    if Heap_checks.run_sequences "ScheduledBinomialHeap"
    then (
      Heap_checks.run_merges "ScheduledBinomialHeap" 1_000;
      Heap_checks.run_merges "ScheduledBinomialHeap" 100_000;
      Heap_checks.run_versions "ScheduledBinomialHeap, persistently")
    else
      Printf.printf
        "  SKIP  ScheduledBinomialHeap: merge and persistence checks -- over budget in \
         one thread\n")
;;

(* --------------------------------------------- ScheduledBottomUpMergeSort (7.4) *)

(* Figure 7.3 is the sortable collection of Figure 6.5 with its one monolithic suspension,
   the list of segments, replaced by streams and a schedule per segment. mrg is written
   over streams so that a merge can be executed one element at a time; add still merges
   the new singleton into the first k segments when the lowest k bits of n are ones, but
   every merge is now a suspended stream, and the new segment's schedule is the list of
   those partial merges in the order they depend on each other. Every add then runs two
   steps of every segment's schedule, exec2, which is the amortised cost of Section 6.4.3,
   2B' - 1, turned into a fixed instalment. The claims of p.95: add in O(log n) worst-case
   time and sort in O(n) worst-case time. Lemma 7.2 carries both: a segment of size m has
   at most 2m - 2(n mod m + 1) elements left in its schedule, so the segments an add is
   about to merge have been fully evaluated, and the whole collection holds at most 2n
   unevaluated suspensions for a sort to pay for.

   Two instruments, as for the heap: comparisons, which see every merge step that moves an
   element from a non-empty stream against another, and words, which see the cells and
   suspensions besides. Both bounds are worst-case, so both are asserted on the dearest
   single operation of a run. For add the comparison bound is the book's own accounting
   with no constant: two steps per segment, a step at most one comparison, and one segment
   per 1 bit of the new size, so 2B' comparisons at most. For sort it is 4n: at most 2n
   suspensions to force at a comparison each, then at most 2n - k - 1 to merge the
   segments. Lemma 7.2's other consequence is asserted by every add in this file, since
   the pattern match in add_seg raises the moment a segment to be merged still has a
   schedule. That the probe can see a lump at all is checked over Figure 6.5's collection,
   whose first sort after 2^k - 1 adds runs the whole mergesort in one operation, n log n
   comparisons where the scheduled sort is held to 4n.

   The contract is test_ch6's. *)

(* The budgets of a single operation, worst case. An add allocates, per segment, the pair
   and cons that rebuild the list and two forced merge cells with the suspension of the
   rest of each, plus the suspended merges of the new segment and their schedule: under 40
   words per segment, and a segment per bit. A sort allocates a cell and a suspension per
   merge step, up to 4n of them, and a cons per element for the list. *)
let add_comparisons size' = 2. *. float_of_int (popcount size')
let add_words l = (64. *. l) +. 64.
let sort_comparisons n = (4. *. float_of_int n) +. 4.
let sort_words n = (96. *. float_of_int n) +. 128.

let dearer_sortable d ~at ~op ~size (c, w) =
  let cb, wb =
    if op = "add"
    then add_comparisons (size + 1), add_words (log2 (size + 2))
    else sort_comparisons size, sort_words size
  in
  let ratio = Float.max (c /. cb) (w /. wb) in
  if ratio > d.ratio then { at; op; ratio; c; w; size } else d
;;

let show_sortable_dear d =
  Printf.sprintf
    "dearest is #%d (%s on %d elements) at %.0f comparisons and %.0f words"
    d.at
    d.op
    d.size
    d.c
    d.w
;;

module Sortable_tests (S : SORTABLE with type Element.t = int) = struct
  let of_list xs = List.fold_left (fun s x -> S.add x s) S.empty xs

  (* ---------------------------------------------------------------- contract *)

  let run_contract name =
    let t label = Printf.sprintf "%s: %s" name label in
    let eq label expect s =
      surviving
        (t label)
        (fun () -> S.sort s)
        (fun actual -> check_eq (t label) ~expect ~actual string_of_int_list)
    in
    eq "sort of empty is empty" [] S.empty;
    eq "sort of a singleton" [ 5 ] (of_list [ 5 ]);
    eq "sort sorts" [ 1; 2; 3; 4; 5; 6; 7 ] (of_list [ 4; 2; 6; 1; 3; 5; 7 ]);
    eq "duplicates are all kept" [ 1; 1; 1; 2; 2; 3 ] (of_list [ 2; 1; 3; 1; 2; 1 ]);
    eq "ascending input" (upto 20) (of_list (upto 20));
    eq "descending input" (upto 20) (of_list (List.rev (upto 20)));
    (* Sizes on either side of a power of two: every bit set, one bit set, and one more. *)
    eq "31 elements" (upto 31) (of_list (List.rev (upto 31)));
    eq "32 elements" (upto 32) (of_list (List.rev (upto 32)));
    eq "33 elements" (upto 33) (of_list (List.rev (upto 33)));
    (* Randomised, against List.sort, with few distinct values so that equal elements are
       everywhere. *)
    Random.init 20260925;
    let bad = ref 0
    and raised = ref 0 in
    for _ = 0 to 299 do
      let xs = List.init (Random.int 200) (fun _ -> Random.int 50) in
      match S.sort (of_list xs) = List.sort compare xs with
      | true -> ()
      | false -> incr bad
      | exception Failure _ -> incr raised
    done;
    check_int (t "no sort raises, 300 random lists") ~expect:0 ~actual:!raised;
    check_int (t "sort agrees with List.sort, 300 random lists") ~expect:0 ~actual:!bad;
    (* Persistence, in the section's own terms: xs' serves xs, x :: xs and y :: xs. *)
    let xs' = of_list [ 5; 3; 8; 1; 9; 2 ] in
    eq "xs" [ 1; 2; 3; 5; 8; 9 ] xs';
    eq "x :: xs, from the same collection" [ 1; 2; 3; 4; 5; 8; 9 ] (S.add 4 xs');
    eq "y :: xs, from the same collection" [ 0; 1; 2; 3; 5; 8; 9 ] (S.add 0 xs');
    eq "xs again, untouched" [ 1; 2; 3; 5; 8; 9 ] xs'
  ;;

  (* ------------------------------------------- every operation on its own clock *)

  type sop =
    | Add of int
    | Sort

  (* Runs [ops] from the empty collection with every operation on the clocks by itself,
     and reports the dearest add and the dearest sort, each against its own budget. *)
  let dearest ops =
    let s = ref S.empty
    and size = ref 0
    and sum = ref 0
    and add = ref no_dear
    and sort = ref no_dear in
    Array.iteri
      (fun i op ->
        match op with
        | Add x ->
          let s', cw = spent (fun () -> S.add x !s) in
          s := s';
          add := dearer_sortable !add ~at:i ~op:"add" ~size:!size cw;
          incr size
        | Sort ->
          let l, cw = spent (fun () -> S.sort !s) in
          sum := !sum + List.length l;
          sort := dearer_sortable !sort ~at:i ~op:"sort" ~size:!size cw)
      ops;
    ignore (Sys.opaque_identity !s);
    ignore (Sys.opaque_identity !sum);
    !add, !sort
  ;;

  let adds_then_sort xs n =
    Array.init (n + 1) (fun i -> if i < n then Add xs.(i) else Sort)
  ;;

  let random_ints seed n bound =
    Random.init seed;
    Array.init n (fun _ -> Random.int bound)
  ;;

  (* Each sequence with the two sizes it runs at. Ascending input makes every merge step
     take from the same side; a sort after every add is quadratic in total, so it runs at
     smaller sizes. *)
  let sequences =
    [ ( "n ascending adds, then a sort"
      , (1_000, 100_000)
      , fun n -> adds_then_sort (Array.init n (fun i -> i)) n )
    ; ( "n descending adds, then a sort"
      , (1_000, 100_000)
      , fun n -> adds_then_sort (Array.init n (fun i -> n - i)) n )
    ; ( "n random adds, then a sort"
      , (1_000, 100_000)
      , fun n -> adds_then_sort (random_ints 20260925 n 1_000_000) n )
    ; ( "n equal adds, then a sort"
      , (1_000, 100_000)
      , fun n -> adds_then_sort (Array.make n 7) n )
    ; ( "a sort after every add"
      , (500, 2_000)
      , fun n -> Array.init (2 * n) (fun i -> if i mod 2 = 0 then Add (i / 2) else Sort)
      )
    ]
  ;;

  (* Worst case, asserted on the dearest single operation. True if every sequence stayed
     within both budgets. The large size is guarded on the small one, as before. *)
  let run_sequences name =
    let t label = Printf.sprintf "%s: %s" name label in
    let ok = ref true in
    List.iter
      (fun (sequence, (small, large), ops) ->
        let within label n =
          let add, sort = dearest (ops n) in
          let fine d = d.ratio <= 1.0 in
          check
            (t
               (Printf.sprintf
                  "%s, %s at n=%d: %s"
                  sequence
                  label
                  n
                  (show_sortable_dear add)))
            (fine add);
          check
            (t
               (Printf.sprintf
                  "%s, %s at n=%d: %s"
                  sequence
                  label
                  n
                  (show_sortable_dear sort)))
            (fine sort);
          fine add && fine sort
        in
        if not (within "O(log n) adds and O(n) sorts, worst-case" small)
        then (
          ok := false;
          Printf.printf
            "  SKIP  %s: %s at n=%d -- over budget at n=%d\n"
            name
            sequence
            large
            small)
        else if not (within "still so, longer" large)
        then ok := false)
      sequences;
    !ok
  ;;

  (* ---------------------------------- versions: several futures of one collection *)

  let run_versions name =
    let t label = Printf.sprintf "%s: %s" name label in
    let within label d =
      check (t (Printf.sprintf "%s, %s" label (show_sortable_dear d))) (d.ratio <= 1.0)
    in
    (* Every version of a build kept, every add on the clock: the first future of each. *)
    let n = 2_000 in
    let v = Array.make (n + 1) S.empty in
    let d = ref no_dear in
    for i = 1 to n do
      let s, cw = spent (fun () -> S.add i v.(i - 1)) in
      v.(i) <- s;
      d := dearer_sortable !d ~at:i ~op:"add" ~size:(i - 1) cw
    done;
    within (Printf.sprintf "the add that makes each version of a build of %d" n) !d;
    (* A second add from every version, and the first sort of every version. *)
    let d = ref no_dear in
    Array.iteri
      (fun k s ->
        let _, cw = spent (fun () -> S.add 0 s) in
        d := dearer_sortable !d ~at:k ~op:"add" ~size:k cw)
      v;
    within (Printf.sprintf "add from every version of a build of %d" n) !d;
    let first = Array.make (n + 1) (0.0, 0.0)
    and d = ref no_dear in
    Array.iteri
      (fun k s ->
        let _, cw = spent (fun () -> S.sort s) in
        first.(k) <- cw;
        d := dearer_sortable !d ~at:k ~op:"sort" ~size:k cw)
      v;
    within (Printf.sprintf "the first sort of every version of a build of %d" n) !d;
    (* And the second sort of every version: memoisation can only make it cheaper, and the
       merges it cannot memoise, the cleanup, are still within the bound. *)
    let d = ref no_dear
    and dearer_than_first = ref 0 in
    Array.iteri
      (fun k s ->
        let _, ((c, _) as cw) = spent (fun () -> S.sort s) in
        if c > fst first.(k) then incr dearer_than_first;
        d := dearer_sortable !d ~at:k ~op:"sort" ~size:k cw)
      v;
    within (Printf.sprintf "the second sort of every version of a build of %d" n) !d;
    check_int
      (t "no second sort compares more than the first did")
      ~expect:0
      ~actual:!dearer_than_first;
    (* The section's own example, p.74: sorting x :: xs after xs "costs the cleanup and
       the one add, and never the mergesort again". Here the add's merges are scheduled
       rather than suspended whole, and the sort still pays only for them and the cleanup. *)
    let xs = of_list (upto 4_095) in
    ignore (Sys.opaque_identity (S.sort xs));
    let _, (c, _) = spent (fun () -> S.sort (S.add 4_096 xs)) in
    check
      (t
         (Printf.sprintf
            "sorting x :: xs right after xs, xs of 4095: %.0f comparisons, under 2n + \
             the add's merges"
            c))
      (c <= (2. *. 4_096.) +. 4_096. +. 13.);
    (* n operations, each applied to a version chosen at random among all built so far,
       sorts included, each on the clocks against the budget of the collection it meets. *)
    let n = 5_000 in
    Random.init 20260925;
    let from = Array.init n (fun i -> Random.int (i + 1)) in
    let kind = Array.init n (fun _ -> Random.int 4) in
    let v = Array.make (n + 1) S.empty in
    let size = Array.make (n + 1) 0 in
    let d = ref no_dear in
    for i = 1 to n do
      let s = v.(from.(i - 1))
      and sz = size.(from.(i - 1)) in
      if kind.(i - 1) = 0
      then (
        let l, cw = spent (fun () -> S.sort s) in
        ignore (Sys.opaque_identity l);
        v.(i) <- s;
        size.(i) <- sz;
        d := dearer_sortable !d ~at:i ~op:"sort" ~size:sz cw)
      else (
        let s', cw = spent (fun () -> S.add i s) in
        v.(i) <- s';
        size.(i) <- sz + 1;
        d := dearer_sortable !d ~at:i ~op:"add" ~size:sz cw)
    done;
    ignore (Sys.opaque_identity v);
    within
      (Printf.sprintf
         "a random trace of %d operations, each on a random earlier version"
         n)
      !d
  ;;
end

(* -------------------------------------------------------------------- guard *)

(* Whether the probe can see a lump at all. Over Figure 6.5's collection, where the whole
   list of segments is one suspension, the first sort after 2^k - 1 adds runs the
   mergesort itself: every merge of two runs of m compares at least m times, and the
   segments of a collection with every bit set add up to at least (n/2)(k - 2) of those.
   That is n log n in one operation, and must show as over the O(n) budget. *)
module Lazy_sortable = Okasaki.Ch6.BottomUpMergeSort (Counting_int)

let test_sortable_guard () =
  let k = 16 in
  let n = (1 lsl k) - 1 in
  let c =
    List.fold_left (fun s x -> Lazy_sortable.add x s) Lazy_sortable.empty (upto n)
  in
  let _, (comparisons, _) = spent (fun () -> Lazy_sortable.sort c) in
  check
    (Printf.sprintf
       "guard: the same probe over Figure 6.5's collection sees its first sort after %d \
        adds run the mergesort, %.0f comparisons, %.1f times the 4n budget"
       n
       comparisons
       (comparisons /. sort_comparisons n))
    (comparisons >= float_of_int n /. 2. *. float_of_int (k - 2)
     && comparisons > sort_comparisons n)
;;

(* -------------------------------------------- ScheduledBottomUpMergeSort, run *)

module Scheduled_sortable = ScheduledBottomUpMergeSort (Counting_int) (Okasaki.Ch4.Stream)
module Sortable_checks = Sortable_tests (Scheduled_sortable)

let test_scheduled_mergesort () =
  section "ScheduledBottomUpMergeSort (7.4)";
  let before = !failures in
  Sortable_checks.run_contract "ScheduledBottomUpMergeSort";
  if !failures > before
  then
    Printf.printf
      "  SKIP  ScheduledBottomUpMergeSort: cost checks -- the contract above does not hold\n"
  else (
    test_sortable_guard ();
    if Sortable_checks.run_sequences "ScheduledBottomUpMergeSort"
    then Sortable_checks.run_versions "ScheduledBottomUpMergeSort, persistently"
    else
      Printf.printf
        "  SKIP  ScheduledBottomUpMergeSort: persistence checks -- over budget in one \
         thread\n")
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
  run "RealTimeQueue" test_real_time;
  run "Exercise 7.2" test_sizes;
  run "ScheduledBinomialHeap" test_scheduled_binomial;
  run "ScheduledBottomUpMergeSort" test_scheduled_mergesort;
  Printf.printf "\n%d checks, %d failures\n\n" !checks !failures;
  if !failures > 0 then exit 1
;;
