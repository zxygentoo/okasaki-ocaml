(* Tests for Chapter 7: the real-time queue of Figure 7.1 (section 7.2), and the size
   functions of Exercise 7.2 on top of it. Plain OCaml, no test framework, matching the
   earlier chapters.

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
  Printf.printf "\n%d checks, %d failures\n\n" !checks !failures;
  if !failures > 0 then exit 1
;;
