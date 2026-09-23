(* Tests for Chapter 6: the banker's queue of Figure 6.1 (section 6.3.2) and the lazy
   binomial heap of Figure 6.2 (section 6.4.1). Plain OCaml, no test framework, matching
   the earlier chapters. The queue first; the heap's own preamble is further down.

   Figure 6.1 promises what Figure 5.2 promised, every operation in O(1) amortised time,
   and keeps the promise where Figure 5.2 cannot: when a queue is used more than once.
   The batched queue's argument breaks the moment a version is shared, because its one
   expensive tail can then be asked for again and again, and nothing in the queue
   remembers having done the work. Section 6.3.2 answers with lazy evaluation used two
   ways. The reverse is suspended early, while the front still has enough elements to pay
   for it one tail at a time; and the suspension is memoised, so however many futures
   force it, it runs once. The cost checks here therefore go beyond the single-threaded
   sequences of test_ch5 to TRACES: several futures of one queue, with the bound taken
   over every operation in the trace, each counted once. That is the sense in which the
   chapter says its bounds hold "even when used persistently".

   Two instruments. QUEUE seals the representation, so the first is allocation, measured
   from outside as in test_ch5, with the streams of Figure 4.1 (Okasaki.Ch4.Stream)
   underneath. The second exists because the port is a functor over STREAM: a stream whose
   ++ and reverse count their steps, one per cell of the first stream appended and one per
   cell reversed, which is exactly what the chapter's debits stand for. In that unit
   Theorem 6.1 -- snoc and tail discharge one and two debits respectively -- is a bound
   with no constant in it: the steps a trace executes never exceed its snocs plus twice
   its tails. Heads do not enter the budget, because a head only ever forces the first
   cell of the front, and the debit invariant keeps that cell fully paid.

   The behavioural contract and the sequences are those of test_ch5, since this is the
   same QUEUE signature; the constant is not, since every step of a lazy stream allocates
   a suspension where a list allocated a cons. *)

open Okasaki.Ch6

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

(* Run [f] and hand its result to [k], which does the checking. A structure that has lost
   its invariant tends to raise where a working one returns; this makes that the named
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

(* ---------------------------------------------------------- the two clocks *)

(* Figure 4.1's streams, with ++ and reverse counting their steps: one per cell of the
   first stream that ++ copies, one per cell that reverse moves. (take and drop are here
   only to satisfy STREAM; the queue never calls them.) This instruments the queue's
   rotation policy and nothing else: the streams themselves are test_ch4's business. *)
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
       | 0, _ -> Nil
       | _, (lazy Nil) -> Nil
       | _, (lazy (Cons (x, s'))) -> Cons (x, take (n - 1) s'))
  ;;

  let drop n s =
    let rec aux n (lazy c) =
      match n, c with
      | 0, _ -> c
      | _, Nil -> Nil
      | _, Cons (_, s') -> aux (n - 1) s'
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

(* A clock is read before and after a run, and the difference is what the run cost. Words
   are allocation, as in test_ch5; steps are the counting stream's. Sys.opaque_identity
   stops the optimiser discarding a result and with it the allocation being measured. *)
let words () = Gc.minor_words ()
let steps () = float_of_int !Counting_stream.steps

let cost clock f =
  let before = clock () in
  let r = Sys.opaque_identity (f ()) in
  r, clock () -. before
;;

(* What a run did, for its budget. *)
type ops =
  { snocs : int
  ; tails : int
  ; heads : int
  }

let total ops = ops.snocs + ops.tails + ops.heads
let tails n = { snocs = 0; tails = n; heads = 0 }

(* A cost claim in one of the two units: the most a run of these operations may cost, how
   to report what it did cost, and the least the dearest tail of a drain of n must cost.
   The last is the guard that the clock can see a reverse at all: on a queue built by
   snocs alone the last rotation moved a fixed fraction of the elements, in Figure 6.1 at
   least a quarter, and the drain runs that reverse in a single tail. *)
type bound =
  { units : string
  ; claim : string
  ; clock : unit -> float
  ; budget : ops -> float
  ; show : ops -> float -> string
  ; reverse_floor : int -> float
  }

(* The most a single cheap operation may allocate, in words, and the most a sequence may
   average per operation. A snoc of Figure 6.1 is a 4-tuple and a suspended cons, 12
   words, and the snoc that rotates suspends the ++ and the reverse on top of that, 32 in
   all; each step forced later costs about 10 words for ++ (a cons and the suspension of
   the rest) and 6 for reverse, and the dearest sequence, snoc and tail alternating,
   averages about 20. 48 leaves room for that and for the probe's own noise, and is
   nowhere near an operation that is really linear: at the sizes used here that is out by
   a factor of hundreds. *)
let constant = 48.0

let amortised_words =
  { units = "words"
  ; claim = "amortised O(1)"
  ; clock = words
  ; budget = (fun ops -> constant *. float_of_int (total ops))
  ; show =
      (fun ops c ->
        Printf.sprintf "%.2f words per operation" (c /. float_of_int (total ops)))
  ; reverse_floor = (fun n -> float_of_int n /. 2.) (* a sixth of n, 3 words a cons *)
  }
;;

(* Theorem 6.1, to the step. *)
let theorem_6_1 =
  { units = "steps"
  ; claim = "within Theorem 6.1's budget"
  ; clock = steps
  ; budget = (fun ops -> float_of_int (ops.snocs + (2 * ops.tails)))
  ; show =
      (fun ops c -> Printf.sprintf "%.0f steps, budget %d" c (ops.snocs + (2 * ops.tails)))
  ; reverse_floor = (fun n -> float_of_int n /. 6.)
  }
;;

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
       reports empty, and raises on head, with elements still in it. *)
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

  (* ---------------------------------------- sequences: one thread, from empty *)

  (* Each driver runs its sequence and reports what it did, keeping its queue alive to the
     end so that nothing it allocated can be optimised away. They differ in where the
     rotations fall: one huge one, a tiny one at every step, or ever larger ones at ever
     longer intervals. The heads sequence is new to this chapter: here a head can do work,
     opening the front of every ++ the rotations have stacked up. *)
  let fill_then_drain n () =
    let q = ref Q.empty in
    for i = 1 to n do
      q := Q.snoc !q i
    done;
    for _ = 1 to n do
      q := Q.tail !q
    done;
    ignore (Sys.opaque_identity !q);
    { snocs = n; tails = n; heads = 0 }
  ;;

  let alternate n () =
    let q = ref Q.empty in
    for i = 1 to n do
      q := Q.snoc !q i;
      q := Q.tail !q
    done;
    ignore (Sys.opaque_identity !q);
    { snocs = n; tails = n; heads = 0 }
  ;;

  let two_snocs_per_tail n () =
    let q = ref Q.empty in
    for i = 1 to n do
      q := Q.snoc !q i;
      q := Q.snoc !q i;
      q := Q.tail !q
    done;
    ignore (Sys.opaque_identity !q);
    { snocs = 2 * n; tails = n; heads = 0 }
  ;;

  let snoc_then_head n () =
    let q = ref Q.empty
    and sum = ref 0 in
    for i = 1 to n do
      q := Q.snoc !q i;
      sum := !sum + Q.head !q
    done;
    ignore (Sys.opaque_identity !q);
    ignore (Sys.opaque_identity !sum);
    { snocs = n; tails = 0; heads = n }
  ;;

  let random_mix n =
    Random.init 20260921;
    let wants_snoc = Array.init n (fun _ -> Random.int 3 > 0) in
    fun () ->
      let q = ref Q.empty
      and size = ref 0
      and snocs = ref 0 in
      for i = 0 to n - 1 do
        if wants_snoc.(i) || !size = 0
        then (
          q := Q.snoc !q i;
          incr size;
          incr snocs)
        else (
          q := Q.tail !q;
          decr size)
      done;
      ignore (Sys.opaque_identity !q);
      { snocs = !snocs; tails = n - !snocs; heads = 0 }
  ;;

  let sequences =
    [ "n snocs then n tails", fill_then_drain
    ; "snoc and tail alternating", alternate
    ; "two snocs to every tail", two_snocs_per_tail
    ; "a head after every snoc", snoc_then_head
    ; "a random mix", random_mix
    ]
  ;;

  (* Amortised bounds, asserted the only way an amortised bound can be: over whole
     sequences. True if every sequence stayed within the bound. The large size is guarded
     on the small one, as the earlier chapters guard theirs: an operation that is secretly
     linear makes a sequence quadratic, and at n = 100_000 that is not a failure but a
     hang. *)
  let run_sequences bound name =
    let t label = Printf.sprintf "%s: %s" name label in
    let ok = ref true in
    List.iter
      (fun (sequence, driver) ->
        let within label n =
          let ops, c = cost bound.clock (driver n) in
          let fine = c <= bound.budget ops in
          check
            (t (Printf.sprintf "%s, %s: %s at n=%d" sequence label (bound.show ops c) n))
            fine;
          fine
        in
        if not (within bound.claim 1_000)
        then (
          ok := false;
          Printf.printf
            "  SKIP  %s: %s at n=100000 -- it is not %s at n=1000\n"
            name
            sequence
            bound.claim)
        else if not (within (bound.claim ^ ", a hundred times longer") 100_000)
        then ok := false)
      sequences;
    !ok
  ;;

  (* -------------------------------------- traces: several futures of one queue *)

  (* n snocs, then n tails one at a time, each on the clock. The index and cost of the
     dearest: the tail that runs the reverse. *)
  let dearest_tail clock n =
    let q = ref (of_list (upto n))
    and dear = ref (0, 0.0) in
    for i = 1 to n do
      let q', c = cost clock (fun () -> Q.tail !q) in
      if c > snd !dear then dear := i, c;
      q := q'
    done;
    !dear
  ;;

  (* A fresh queue brought to the version whose tail is the dear one -- the book's q_m --
     without taking that tail. *)
  let version_before_the_dear_tail ~n ~k =
    let q = ref (of_list (upto n)) in
    for _ = 1 to k - 1 do
      q := Q.tail !q
    done;
    !q
  ;;

  (* The whole drain, d times over from the same starting queue. *)
  let branch_at_the_start ~n ~d () =
    let q0 = of_list (upto n) in
    for _ = 1 to d do
      let q = ref q0 in
      for _ = 1 to n do
        q := Q.tail !q
      done;
      ignore (Sys.opaque_identity !q)
    done;
    { snocs = n; tails = d * n; heads = 0 }
  ;;

  (* Every version of a full drain, kept, and so with everything on the drain's path
     already forced. *)
  let versions n =
    let v = Array.make (n + 1) Q.empty in
    v.(0) <- of_list (upto n);
    for i = 1 to n do
      v.(i) <- Q.tail v.(i - 1)
    done;
    v
  ;;

  (* The shortest futures there are, d times over from every version of a drain: a
     rotation and then the operation that would force what it suspended. For each kind of
     run, the version it was dearest from and what it cost there. *)
  let short_runs bound ~n ~d =
    let v = versions n in
    let opaque x = ignore (Sys.opaque_identity x) in
    let runs =
      [ ( "tail"
        , (fun q -> opaque (Q.tail q))
        , { snocs = 0; tails = 1; heads = 0 }
        , n - 1 )
      ; ( "tail then head"
        , (fun q -> opaque (Q.head (Q.tail q)))
        , { snocs = 0; tails = 1; heads = 1 }
        , n - 2 )
      ; ( "snoc then head"
        , (fun q -> opaque (Q.head (Q.snoc q 0)))
        , { snocs = 1; tails = 0; heads = 1 }
        , n )
      ]
    in
    List.map
      (fun (run, f, per, last) ->
        let ops = { snocs = d * per.snocs; tails = d * per.tails; heads = d * per.heads } in
        let worst = ref (0, 0.0) in
        for k = 0 to last do
          let _, c =
            cost bound.clock (fun () ->
              for _ = 1 to d do
                f v.(k)
              done)
          in
          if c > snd !worst then worst := k, c
        done;
        run, fst !worst, ops, snd !worst)
      runs
  ;;

  (* n operations, each applied to a version chosen at random among all built so far. *)
  let random_trace n =
    Random.init 20260923;
    let from = Array.init n (fun i -> Random.int (i + 1)) in
    let wants_snoc = Array.init n (fun _ -> Random.int 3 > 0) in
    let v = Array.make (n + 1) Q.empty in
    fun () ->
      let snocs = ref 0 in
      for i = 1 to n do
        let q = v.(from.(i - 1)) in
        v.(i)
        <- (if wants_snoc.(i - 1) || Q.is_empty q
            then (
              incr snocs;
              Q.snoc q i)
            else Q.tail q)
      done;
      ignore (Sys.opaque_identity v);
      { snocs = !snocs; tails = n - !snocs; heads = 0 }
  ;;

  let run_traces bound name =
    let t label = Printf.sprintf "%s: %s" name label in
    let within label (ops, c) =
      check (t (Printf.sprintf "%s: %s" label (bound.show ops c))) (c <= bound.budget ops)
    in
    let n = 1_000 in
    (* The guard: a drain of a snoc-built queue has one tail that runs a reverse, and the
       clock sees it. Without this, every check below could pass by measuring nothing. *)
    let k, dear = dearest_tail bound.clock n in
    check
      (t
         (Printf.sprintf
            "in a drain of %d the dearest tail is #%d, at %.0f %s"
            n
            k
            dear
            bound.units))
      (dear >= bound.reverse_floor n);
    (* p.65, the branch point just after the rotation: the version whose tail is the dear
       one, tailed d times. "Each of these branches forces the reverse suspension, but
       they each force the same suspension, so the reverse is executed only once." *)
    let d = 10_000 in
    let v = version_before_the_dear_tail ~n ~k in
    let _, first = cost bound.clock (fun () -> Q.tail v) in
    let _, rest =
      cost bound.clock (fun () ->
        for _ = 2 to d do
          ignore (Sys.opaque_identity (Q.tail v))
        done)
    in
    check
      (t
         (Printf.sprintf
            "the first of %d tails of one version runs the reverse, %.0f %s"
            d
            first
            bound.units))
      (first >= bound.reverse_floor n);
    within (Printf.sprintf "and the other %d find it memoised" (d - 1)) (tails (d - 1), rest);
    (* p.65, the branch point just before the rotation: the whole drain, d times over.
       "Because these are different suspensions, memoization does not help at all", and
       the bound holds anyway, because the operations were repeated along with the work. *)
    within
      "the whole drain repeated 10 times from one queue"
      (cost bound.clock (branch_at_the_start ~n ~d:10));
    (* Every branch point, with the shortest futures. Rotating early is what makes these
       cheap: a rotation is never forced by the operation after it, unless it was tiny. *)
    List.iter
      (fun (run, k, ops, c) ->
        within
          (Printf.sprintf "%s, 50 times over from each version, dearest from #%d" run k)
          (ops, c))
      (short_runs bound ~n ~d:50);
    within
      "a random trace of 100000 operations, each on a random earlier version"
      (cost bound.clock (random_trace 100_000))
  ;;
end

(* ------------------------------------------------------- BankersQueue (6.3.2) *)

module Q = BankersQueue (Okasaki.Ch4.Stream)
module Qc = BankersQueue (Counting_stream)
module Words_tests = Queue_tests (Q)
module Steps_tests = Queue_tests (Qc)

(* p.66: "By inspection, the unshared cost of every queue operation is O(1)." For snoc
   that is its whole cost, since a snoc forces nothing: it suspends a cons, and at a
   rotation it suspends the ++ and the reverse too. That is where lazy evaluation earns
   its keep -- the batched queue's snoc was O(1) as well, but only because its rotation
   was the tail's problem. So snoc is O(1) worst-case at every size, and executes no step
   at all. head is not asserted O(1) worst-case: the chapter does not claim it, and it is
   not, since the first head after a long run of snocs opens one layer of ++ per rotation.
   tail's worst case is the reverse, which is what the traces are about. *)
let test_snoc_worst_case () =
  let n = 100_000 in
  let dearest clock snoc empty =
    let q = ref empty
    and worst = ref 0.0 in
    for i = 1 to n do
      let q', c = cost clock (fun () -> snoc !q i) in
      q := q';
      worst := Float.max !worst c
    done;
    !worst
  in
  let w = dearest words Q.snoc Q.empty in
  check
    (Printf.sprintf
       "BankersQueue: snoc is O(1) worst-case, dearest of %d consecutive snocs %.0f words"
       n
       w)
    (w <= constant);
  let s = dearest steps Qc.snoc Qc.empty in
  check
    (Printf.sprintf "BankersQueue: snoc never executes a step (dearest %.0f)" s)
    (s = 0.0)
;;

(* What a queue costs means nothing until it behaves like one, and a queue that raises half
   way through a sequence would take the rest of a section down with it. So both cost
   sections wait on the contract. *)
let contract_holds = ref false

let test_bankers () =
  section "BankersQueue (6.3.2)";
  let before = !failures in
  Words_tests.run_contract "BankersQueue";
  Steps_tests.run_contract "BankersQueue over the counting stream";
  contract_holds := !failures = before;
  if not !contract_holds
  then
    Printf.printf
      "  SKIP  BankersQueue: cost checks -- the contract above does not hold\n"
  else if Words_tests.run_sequences amortised_words "BankersQueue"
  then (
    test_snoc_worst_case ();
    Words_tests.run_traces amortised_words "BankersQueue, persistently")
  else
    Printf.printf
      "  SKIP  BankersQueue: worst-case and persistence checks -- not O(1) in one thread\n"
;;

let test_theorem () =
  section "Theorem 6.1";
  if not !contract_holds
  then Printf.printf "  SKIP  Theorem 6.1 -- the contract does not hold\n"
  else if Steps_tests.run_sequences theorem_6_1 "Theorem 6.1"
  then Steps_tests.run_traces theorem_6_1 "Theorem 6.1, persistently"
  else
    Printf.printf
      "  SKIP  Theorem 6.1: persistence checks -- the budget does not hold in one thread\n"
;;

(* ---------------------------------------------------- LazyBinomialHeap (6.4.1) *)

(* Figure 6.2 is the binomial heap of Figure 3.4 with its list of trees suspended, and
   p.70's claim for it is the O(1) amortised insert of Section 5.3 "regardless of whether
   the heaps are used persistently"; Exercise 6.3 puts find_min, delete_min and merge at
   O(log n) amortised. The contract and the structural checks are test_ch3's, since HEAP
   and the shape of the heap are unchanged. What is new is what was new for the queue:
   the bounds are asserted over traces. And laziness changes what a driver has to do,
   because a run of inserts, merges or delete_mins that nobody looks at now does no work
   at all, so every driver ends by forcing what it built.

   Cost is counted two ways: in comparisons, through the instrumented element type of
   test_ch3 and test_ch5, which sees every link and every step of remove_min_tree; and
   in words, which sees those and the suspensions besides. Both are budgeted per
   operation and summed over the trace. An insert gets 2 comparisons and 32 words: p.70's
   amortised cost of two, with a suspension, a node, a cons and two links behind it. A
   query -- find_min, delete_min, merge, and is_empty, which forces too (Exercise 6.5) --
   gets 2 + 2L comparisons and 48 + 16L words, L being log2 of one more than the largest
   heap in the trace. A heap that size holds at most L trees, so that is twice what any
   one query can meet in a chain of links or a walk down the list, with the suspension
   and the pairs remove_min_tree builds on top. The dearest sequence measured uses about
   two thirds of it; a linear operation is out by a factor of fifty at the smallest size
   used. *)

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

(* Comparisons and words spent by [f]. *)
let spent f =
  comparisons := 0;
  let before = Gc.minor_words () in
  ignore (Sys.opaque_identity (f ()));
  float_of_int !comparisons, Gc.minor_words () -. before
;;

let count_only f = int_of_float (fst (spent f))
let log2 n = log (float_of_int n) /. log 2.

(* floor (log2 n), for n >= 1: a binomial heap of n elements holds at most
   floor (log2 (n + 1)) trees. *)
let floor_log2 n =
  let rec go acc n = if n <= 1 then acc else go (acc + 1) (n / 2) in
  go 0 n
;;

let popcount n =
  let rec go acc n = if n = 0 then acc else go (acc + (n land 1)) (n lsr 1) in
  go 0 n
;;

(* An insert links once per trailing 1 bit: the carry chain of a binary increment, stopped
   by the first hole. *)
let trailing_ones n =
  let rec go acc n = if n land 1 = 0 then acc else go (acc + 1) (n lsr 1) in
  go 0 n
;;

(* What a heap trace did, and the largest heap it built. *)
type heap_ops =
  { inserts : int
  ; queries : int
  ; largest : int
  }

let heap_total o = o.inserts + o.queries

(* The comparison and word budgets of a trace. *)
let budgets o =
  let l = log2 (o.largest + 1)
  and i = float_of_int o.inserts
  and q = float_of_int o.queries in
  (2. *. i) +. ((2. +. (2. *. l)) *. q), (32. *. i) +. ((48. +. (16. *. l)) *. q)
;;

(* Comparisons and words spent by [f], which reports what it did. *)
let heap_cost f =
  comparisons := 0;
  let before = Gc.minor_words () in
  let ops = Sys.opaque_identity (f ()) in
  ops, (float_of_int !comparisons, Gc.minor_words () -. before)
;;

(* How far a trace's cost is over its budgets: at most 1 when it is within them. *)
let over_budget (ops, (c, w)) =
  let cb, wb = budgets ops in
  Float.max (c /. cb) (w /. wb)
;;

let within_budget name ((ops, (c, w)) as trace) =
  let cb, wb = budgets ops in
  let per x = x /. float_of_int (heap_total ops) in
  let fine = over_budget trace <= 1.0 in
  check
    (Printf.sprintf
       "%s: %.2f comparisons and %.1f words per operation, budget %.2f and %.1f"
       name
       (per c)
       (per w)
       (per cb)
       (per wb))
    fine;
  fine
;;

module Heap_tests (H : HEAP with type Element.t = int) = struct
  let of_list xs = List.fold_left (fun h x -> H.insert x h) H.empty xs

  (* Run whatever the heap has put off. is_empty forces the list of trees, and nothing
     forces less. *)
  let force h = ignore (Sys.opaque_identity (H.is_empty h))

  (* find_min/delete_min to exhaustion. That this comes out sorted is the whole
     behavioural specification of a heap. *)
  let drain h =
    let rec go acc h =
      if H.is_empty h then List.rev acc else go (H.find_min h :: acc) (H.delete_min h)
    in
    go [] h
  ;;

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
    (* Forced through is_empty: a delete_min that puts everything off, as Figure 6.2's
       does, cannot raise before then. *)
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
    (* Persistence: no operation may disturb its operands. With suspensions in the
       picture that includes forcing: a heap looked at through one future must read the
       same through another. *)
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

  (* ------------------------------------------------------------- structure *)

  (* Trees in [h]: find_min via remove_min_tree compares once per tree but the first.
     Forced first, so that the count sees the walk and not the pending work. *)
  let trees h =
    force h;
    count_only (fun () -> H.find_min h) + 1
  ;;

  (* test_ch3's binomial checks, with the forcing that this chapter makes necessary: an
     insert or a merge does its linking when its result is looked at, not before. *)
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
    check_int (t "at most floor(log2 (n+1)) trees") ~expect:0 ~actual:!over;
    let bad_ins = ref 0 in
    List.iter
      (fun n ->
        let h = of_list (upto n) in
        force h;
        if count_only (fun () -> force (H.insert max_int h)) <> trailing_ones n
        then incr bad_ins)
      [ 1; 2; 3; 7; 8; 15; 31; 100; 255; 1000 ];
    check_int
      (t "insert, once forced, links once per trailing 1 bit of n")
      ~expect:0
      ~actual:!bad_ins;
    let bad_merge = ref 0 in
    List.iter
      (fun (n1, n2) ->
        let a = of_list (upto n1)
        and b = of_list (List.init n2 (fun i -> i + n1)) in
        force a;
        force b;
        if count_only (fun () -> force (H.merge a b)) > floor_log2 (n1 + n2 + 1) + 1
        then incr bad_merge)
      [ 1, 1; 7, 9; 63, 64; 100, 1000; 1023, 1023 ];
    check_int (t "merge, once forced, links O(log n) times") ~expect:0 ~actual:!bad_merge
  ;;

  (* --------------------------------------------- what an operation does when applied *)

  (* p.70: "fun lazy insert (x, $ts) = $insTree (NODE (0, x, []), ts)" -- insert is
     monolithic, and applying it builds a suspension and does nothing else, whatever heap
     it is given. The same holds of merge. The heap given is the adversary of Section
     5.3: 2^k - 1 elements, every bit set, k trees, so that the insert, once it runs,
     links k times. delete_min is not held to this: Exercise 6.4 lets it do its
     remove_min_tree at once, and the budgets above cover both readings. *)
  let run_unshared name =
    let t label = Printf.sprintf "%s: %s" name label in
    let k = 16 in
    let h = of_list (upto ((1 lsl k) - 1)) in
    force h;
    let insert_c, insert_w = spent (fun () -> H.insert 0 h) in
    check_int
      (t "insert compares nothing when applied, on the all-ones heap")
      ~expect:0
      ~actual:(int_of_float insert_c);
    check
      (t (Printf.sprintf "and allocates a suspension and nothing more (%.0f words)" insert_w))
      (insert_w <= 32.0);
    let merge_c, merge_w = spent (fun () -> H.merge h h) in
    check_int
      (t "merge compares nothing when applied, on two all-ones heaps")
      ~expect:0
      ~actual:(int_of_float merge_c);
    check
      (t (Printf.sprintf "and allocates a suspension and nothing more (%.0f words)" merge_w))
      (merge_w <= 32.0);
    (* The work is still there, once, at the first look. *)
    let s = H.insert 0 h in
    check_int
      (t (Printf.sprintf "forcing the insert links once per tree, %d times" k))
      ~expect:k
      ~actual:(count_only (fun () -> force s));
    check_int (t "forcing it again compares nothing") ~expect:0 ~actual:(count_only (fun () -> force s))
  ;;

  (* ---------------------------------------- sequences: one thread, from empty *)

  let drain_all h n =
    let h = ref h in
    for _ = 1 to n do
      h := H.delete_min !h
    done;
    force !h
  ;;

  let random_ints seed n bound =
    Random.init seed;
    List.init n (fun _ -> Random.int bound)
  ;;

  (* Each driver runs its sequence, forces what it built, and reports what it did. They
     differ in how much is put off and for how long: a drain forces at every step, a
     chain of inserts with one find_min at the end forces everything at once, the merge
     tree puts off n - 1 merges in a tree shape. *)
  let sequences =
    [ ( "n random inserts, then n delete_mins"
      , fun n ->
          let xs = random_ints 20260924 n 1_000_000 in
          fun () ->
            drain_all (of_list xs) n;
            { inserts = n; queries = n + 1; largest = n } )
    ; ( "n ascending inserts, then n delete_mins"
      , fun n () ->
          drain_all (of_list (upto n)) n;
          { inserts = n; queries = n + 1; largest = n } )
    ; ( "n equal inserts, then n delete_mins"
      , fun n () ->
          drain_all (of_list (List.init n (fun _ -> 7))) n;
          { inserts = n; queries = n + 1; largest = n } )
    ; ( "a find_min after every insert"
      , fun n () ->
          let h = ref H.empty in
          for i = 1 to n do
            h := H.insert i !h;
            ignore (Sys.opaque_identity (H.find_min !h))
          done;
          { inserts = n; queries = n; largest = n } )
    ; ( "n inserts, then one find_min"
      , fun n () ->
          ignore (Sys.opaque_identity (H.find_min (of_list (upto n))));
          { inserts = n; queries = 1; largest = n } )
    ; ( "n singletons merged pairwise, then n delete_mins"
      , fun n () ->
          let rec round = function
            | a :: b :: rest -> H.merge a b :: round rest
            | l -> l
          in
          let rec go = function
            | [ h ] -> h
            | [] -> H.empty
            | l -> go (round l)
          in
          drain_all (go (List.init n (fun i -> H.insert i H.empty))) n;
          { inserts = n; queries = n - 1 + n + 1; largest = n } )
    ; ( "insert then delete_min at a steady size of 1000, n times over"
      , fun n () ->
          let h = ref (of_list (upto 1000)) in
          force !h;
          for i = 1 to n do
            h := H.delete_min (H.insert i !h)
          done;
          force !h;
          { inserts = n + 1000; queries = n + 2; largest = 1001 } )
    ]
  ;;

  (* True if every sequence stayed within budget. The large size is guarded on the small
     one, as before. *)
  let run_sequences name =
    let t label = Printf.sprintf "%s: %s" name label in
    let ok = ref true in
    List.iter
      (fun (sequence, driver) ->
        let within label n =
          within_budget
            (t (Printf.sprintf "%s, %s at n=%d" sequence label n))
            (heap_cost (driver n))
        in
        if not (within "amortised, within budget" 1_000)
        then (
          ok := false;
          Printf.printf
            "  SKIP  %s: %s at n=100000 -- it is over budget at n=1000\n"
            name
            sequence)
        else if not (within "still within budget a hundred times longer" 100_000)
        then ok := false)
      sequences;
    !ok
  ;;

  (* -------------------------------------- traces: several futures of one heap *)

  let run_traces name =
    let t label = Printf.sprintf "%s: %s" name label in
    let k = 16 in
    let n = (1 lsl k) - 1 in
    let h = of_list (upto n) in
    force h;
    let d = 10_000 in
    let trace label ~inserts ~queries f =
      ignore
        (within_budget
           (t label)
           (heap_cost (fun () ->
              for _ = 1 to d do
                ignore (Sys.opaque_identity (f ()))
              done;
              { inserts = d * inserts; queries = d * queries; largest = n + 2 })))
    in
    (* p.70: the O(1) amortised insert of Section 5.3 "degrades to O(log n) worst-case
       time if the heaps are used persistently". This is that use: the all-ones heap,
       inserted into d times over. Here nothing runs until something looks ... *)
    trace
      (Printf.sprintf "%d inserts into one all-ones heap of %d, nothing forced" d n)
      ~inserts:1
      ~queries:0
      (fun () -> H.insert 0 h);
    (* ... and when something looks, the looking is what pays. *)
    trace "find_min of each of them" ~inserts:1 ~queries:1 (fun () ->
      H.find_min (H.insert 0 h));
    (* The trace that an insert which forced its argument at once would fail: each outer
       insert would run a different inner suspension, log n links apiece, and with
       nothing looking there is nothing to charge them to. *)
    trace
      "an insert on top of each of them, nothing forced"
      ~inserts:2
      ~queries:0
      (fun () -> H.insert 1 (H.insert 0 h));
    trace "find_min of each of those" ~inserts:2 ~queries:1 (fun () ->
      H.find_min (H.insert 1 (H.insert 0 h)));
    trace "delete_min of one heap, each looked at" ~inserts:0 ~queries:2 (fun () ->
      H.find_min (H.delete_min h));
    trace
      "merge of one heap with itself, each looked at"
      ~inserts:0
      ~queries:2
      (fun () -> H.find_min (H.merge h h));
    (* The shortest futures there are, d times over from every version of a drain, all
       of them forced so that what the runs pay is their own. *)
    let n = 1_000 in
    let v = Array.make (n + 1) H.empty in
    v.(0) <- of_list (upto n);
    force v.(0);
    for i = 1 to n do
      v.(i) <- H.delete_min v.(i - 1);
      force v.(i)
    done;
    let d = 20 in
    let opaque x = ignore (Sys.opaque_identity x) in
    List.iter
      (fun (run, f, (inserts, queries), last) ->
        let ops = { inserts = d * inserts; queries = d * queries; largest = n } in
        let worst = ref (0, (0.0, 0.0)) in
        for k = 0 to last do
          let (), cw =
            heap_cost (fun () ->
              for _ = 1 to d do
                f v.(k)
              done)
          in
          if over_budget (ops, cw) > over_budget (ops, snd !worst) then worst := k, cw
        done;
        let k, cw = !worst in
        ignore
          (within_budget
             (t
                (Printf.sprintf
                   "%s, %d times over from each version of a drain, dearest from #%d"
                   run
                   d
                   k))
             (ops, cw)))
      [ "insert", (fun q -> opaque (H.insert 0 q)), (1, 0), n
      ; "find_min of an insert", (fun q -> opaque (H.find_min (H.insert 0 q))), (1, 1), n
      ; ( "find_min of a delete_min"
        , (fun q -> opaque (H.find_min (H.delete_min q)))
        , (0, 2)
        , n - 2 )
      ; ( "find_min of a merge with itself"
        , (fun q -> opaque (H.find_min (H.merge q q)))
        , (0, 2)
        , n - 1 )
      ; ( "is_empty of two inserts"
        , (fun q -> opaque (H.is_empty (H.insert 1 (H.insert 0 q))))
        , (2, 1)
        , n )
      ];
    (* n operations, each applied to a version chosen at random among all built so far,
       and every version forced at the end. *)
    let n = 100_000 in
    Random.init 20260924;
    let from = Array.init n (fun i -> Random.int (i + 1)) in
    let other = Array.init n (fun i -> Random.int (i + 1)) in
    let kind = Array.init n (fun _ -> Random.int 4) in
    let v = Array.make (n + 1) H.empty in
    let inserts = ref 0
    and queries = ref 0 in
    ignore
      (within_budget
         (t
            (Printf.sprintf
               "a random trace of %d operations, each on a random earlier version, all \
                forced"
               n))
         (heap_cost (fun () ->
            for i = 1 to n do
              let q = v.(from.(i - 1)) in
              v.(i)
              <- (match kind.(i - 1) with
                  | 0 | 1 ->
                    incr inserts;
                    H.insert i q
                  | 2 ->
                    incr queries;
                    H.merge q v.(other.(i - 1))
                  | _ ->
                    incr queries;
                    if H.is_empty q
                    then (
                      incr inserts;
                      H.insert i q)
                    else (
                      incr queries;
                      H.delete_min q))
            done;
            Array.iter force v;
            { inserts = !inserts; queries = !queries + n + 1; largest = n })))
  ;;
end

module Lazy_binomial = LazyBinomialHeap (Counting_int)
module Heap_checks = Heap_tests (Lazy_binomial)

let test_lazy_binomial () =
  section "LazyBinomialHeap (6.4.1)";
  let before = !failures in
  Heap_checks.run_contract "LazyBinomialHeap";
  Heap_checks.run_structure "LazyBinomialHeap";
  if !failures > before
  then
    Printf.printf
      "  SKIP  LazyBinomialHeap: cost checks -- the contract or the structure above does \
       not hold\n"
  else (
    Heap_checks.run_unshared "LazyBinomialHeap";
    if Heap_checks.run_sequences "LazyBinomialHeap"
    then Heap_checks.run_traces "LazyBinomialHeap, persistently"
    else
      Printf.printf
        "  SKIP  LazyBinomialHeap: persistence checks -- over budget in one thread\n")
;;

(* ------------------------------------------------------------------- runner *)

(* A regression can make a function raise where the test did not expect it. Report that as
   a failure and carry on to the remaining sections rather than hiding them. *)
let run name f =
  match f () with
  | () -> ()
  | exception e ->
    incr failures;
    Printf.printf "  FAIL  %s: unexpected exception %s\n" name (Printexc.to_string e)
;;

let () =
  run "BankersQueue" test_bankers;
  run "Theorem 6.1" test_theorem;
  run "LazyBinomialHeap" test_lazy_binomial;
  Printf.printf "\n%d checks, %d failures\n\n" !checks !failures;
  if !failures > 0 then exit 1
;;
