(* The checks Chapters 5 to 8, 10 and 11 hold their queues and deques to, written once. Every
   chapter declares QUEUE and DEQUE over again, but as the same signatures, so the functors
   here take the queues of all of them: Contract for what every queue owes, Worst_case for
   one whose every operation is O(1), Amortised for one whose bound is over sequences and
   has to survive persistence. *)

open Harness

(* ------------------------------------------------------- the queue contract *)

module Contract (Q : Okasaki.Ch05.QUEUE) = struct
  let of_list xs = List.fold_left Q.snoc Q.empty xs

  (* head/tail to exhaustion. That this returns the elements in the order they were
     snoc'ed is the whole behavioural specification of a queue. *)
  let drain q = drain_with ~is_empty:Q.is_empty ~head:Q.head ~tail:Q.tail q

  let run_contract name =
    let t label = Printf.sprintf "%s: %s" name label in
    let eq label expect q =
      check_eq (t label) ~expect ~actual:(drain q) string_of_int_list
    in
    let head_is label expect q = check_int (t label) ~expect ~actual:(Q.head q) in
    check (t "empty is empty") (Q.is_empty Q.empty);
    check (t "a singleton is not empty") (not (Q.is_empty (Q.snoc Q.empty 1)));
    check_failure (t "head on empty raises") "head: empty queue" (fun () ->
      Q.head Q.empty);
    check_failure (t "tail on empty raises") "tail: empty queue" (fun () ->
      ignore (Q.is_empty (Q.tail Q.empty)));
    (* The two places the invariant can be lost. is_empty and head look at the front list
       alone, so a queue that lets its front run dry while elements wait in the rear
       reports empty, and raises on head, with elements still in it. *)
    head_is "snoc onto the empty queue makes its element the head" 7 (Q.snoc Q.empty 7);
    head_is
      "tail past the last front element moves on to the rear"
      2
      (Q.tail (of_list [ 1; 2; 3 ]));
    eq "first in, first out" [ 1; 2; 3; 4; 5; 6; 7 ] (of_list [ 1; 2; 3; 4; 5; 6; 7 ]);
    eq "equal elements are all kept, in order" [ 7; 7; 1; 7 ] (of_list [ 7; 7; 1; 7 ]);
    (* Emptiness reached by draining must be as good as the [empty] it started from. *)
    let drained = Q.tail (Q.tail (of_list [ 1; 2 ])) in
    check (t "a queue drained to nothing is empty") (Q.is_empty drained);
    check_failure (t "head on a drained queue raises") "head: empty queue" (fun () ->
      Q.head drained);
    eq "a drained queue can be refilled" [ 8; 9 ] (Q.snoc (Q.snoc drained 8) 9);
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
    let versions = List.init 20 (fun i -> of_list (upto i)) in
    List.iter
      (fun v ->
         ignore (Q.snoc v 99);
         if not (Q.is_empty v) then ignore (Q.tail v))
      versions;
    let stale =
      List.mapi (fun i v -> if drain v = upto i then 0 else 1) versions
      |> List.fold_left ( + ) 0
    in
    check_int (t "every earlier version stays correct") ~expect:0 ~actual:stale;
    let q = of_list [ 1; 2; 3 ] in
    let a = Q.snoc q 4
    and b = Q.snoc q 5 in
    eq "one future of a shared queue" [ 1; 2; 3; 4 ] a;
    eq "does not leak into the other" [ 1; 2; 3; 5 ] b
  ;;
end

(* ------------------------------------------------------- the deque contract *)

(* A DEQUE is a QUEUE, so the queue contract applies to it unchanged; what it adds is the
   other end. *)
module Deque_contract
    (D : Okasaki.Ch05.DEQUE)
    (P : sig
       (* [refused name op f]: [f], [op] on an empty deque, refuses as the deque should. *)
       val refused : string -> string -> (unit -> 'a) -> unit

       (* The seed of the randomised check. *)
       val seed : int
     end) =
struct
  (* Four ways to build the deque that reads [xs] from front to back. *)
  let snocs xs = List.fold_left D.snoc D.empty xs
  let conses xs = List.fold_left (fun q x -> D.cons x q) D.empty (List.rev xs)

  let halves xs =
    let k = List.length xs / 2 in
    List.take k xs, List.drop k xs
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
    P.refused (t "last on empty raises") "last" (fun () -> D.last D.empty);
    P.refused (t "init on empty raises") "init" (fun () ->
      ignore (D.is_empty (D.init D.empty)));
    (* One element, by every route: put there from either end, or left behind by a removal
       from either end of each two-element deque. *)
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
        (List.rev routes)
    in
    check
      (t
         (Printf.sprintf
            "one element behaves the same by every route to it%s"
            (first_of
               (fun (route, why) -> Printf.sprintf "reached by %s, %s" route why)
               bad)))
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
                | exception Failure why ->
                  bad := (build, drain, n, "raised " ^ why) :: !bad)
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
    Random.init P.seed;
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
    let stale =
      List.mapi (fun i v -> if drain_both_ends v = upto i then 0 else 1) versions
      |> List.fold_left ( + ) 0
    in
    check_int (t "every earlier version stays correct") ~expect:0 ~actual:stale
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

module Worst_case
    (Q : Okasaki.Ch05.QUEUE)
    (P : sig
       (* The most a single operation may allocate, in words. *)
       val constant : float

       (* The seeds of the random mix and of the random trace. *)
       val mix_seed : int
       val trace_seed : int
     end) =
struct
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
     tail so the front never stops growing. The heads sequence is for a queue in which a
     head can do work, and for one in which it cannot, so that the clock says so. *)
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
    Random.init P.mix_seed;
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
     single operation. The small size comes first and guards the large one, as in the
     earlier chapters: an operation that is secretly linear makes a sequence quadratic,
     and at n = 100_000 that is not a failure but a hang. The check at n = 1000 ends the
     case instead. *)
  let run_sequences name =
    let t label = Printf.sprintf "%s: %s" name label in
    List.iter
      (fun (sequence, ops) ->
         let within label n =
           let i, op, c = dearest (ops n) in
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
             (c <= P.constant)
         in
         within "O(1) worst-case" 1_000;
         within "still O(1) worst-case, a hundred times longer" 100_000)
      sequences
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
     clock. In the queues of Figures 5.2 and 6.1 one of these tails ran the reverse. *)
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
     all": each round builds its own suspensions. A queue with worst-case bounds runs each
     round's rotations step by step, and pays as it goes. *)
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
    Random.init P.trace_seed;
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
        (c <= P.constant)
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
      (c <= P.constant)
  ;;
end

(* ------------------------------------------------ the amortised contract *)

(* For the queues of Chapter 6 and the bootstrapped queue of Figure 10.2: an amortised
   bound, asserted the only way an amortised bound can be, over whole sequences, and
   asserted again over TRACES, several futures of one queue, with the bound taken over
   every operation in the trace, each counted once. That is the sense in which Chapter 6
   says its bounds hold "even when used persistently": the suspension that does the work
   is memoised, so however many futures force it, it runs once, and the cost checks have
   to go where that matters, the branch points of a drain and of a build. The clock is a
   [bound]: words, or any other unit a chapter can count. *)

(* What a run did, for its budget. *)
type ops =
  { snocs : int
  ; tails : int
  ; heads : int
  }

let total ops = ops.snocs + ops.tails + ops.heads
let tails n = { snocs = 0; tails = n; heads = 0 }

(* A cost claim in one of the two units: the most a run of these operations may cost, how
   to report what it did cost, the least the dearest tail of a drain of n must cost, and
   what that tail does. The floor is the guard that the clock can see a reverse at all: on
   a queue built by snocs alone the last rotation moved a fixed fraction of the elements,
   in Figure 6.1 at least a quarter, and the drain runs that reverse in a single tail. A
   queue with no reverse names the work its dearest tail does instead. *)
type bound =
  { units : string
  ; claim : string
  ; clock : unit -> int
  ; budget : ops -> float
  ; show : ops -> float -> string
  ; reverse_floor : int -> float
  ; dear_work : string
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
  ; dear_work = "runs the reverse"
  }
;;

module Amortised (Q : Okasaki.Ch05.QUEUE) = struct
  include Contract (Q)

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
     sequences. The small size comes first and guards the large one, as in the earlier
     chapters: an operation that is secretly linear makes a sequence quadratic, and at n =
     100_000 that is not a failure but a hang. The check at n = 1000 ends the case
     instead. *)
  let run_sequences bound name =
    let t label = Printf.sprintf "%s: %s" name label in
    List.iter
      (fun (sequence, driver) ->
         let within label n =
           let ops, c = cost_on bound.clock (driver n) in
           check
             (t (Printf.sprintf "%s, %s: %s at n=%d" sequence label (bound.show ops c) n))
             (c <= bound.budget ops)
         in
         within bound.claim 1_000;
         within (bound.claim ^ ", a hundred times longer") 100_000)
      sequences
  ;;

  (* -------------------------------------- traces: several futures of one queue *)

  (* n snocs, then n tails one at a time, each on the clock. The index and cost of the
     dearest: the tail that runs the reverse. *)
  let dearest_tail clock n =
    let q = ref (of_list (upto n))
    and dear = ref (0, 0.0) in
    for i = 1 to n do
      let q', c = cost_on clock (fun () -> Q.tail !q) in
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

  (* The shortest futures there are, d times over from every version in [v] whose size
     ([size k] for the k-th) allows them: a rotation and then the operation that would
     force what it suspended. One run from each version goes unmeasured first: a version
     may have put off work that its own history is due to pay for, and memoisation then
     shares it with every run after. For each kind of run, the version it was dearest
     from and what it cost there. *)
  let short_runs bound v ~size ~d =
    let opaque x = ignore (Sys.opaque_identity x) in
    let runs =
      [ "tail", (fun q -> opaque (Q.tail q)), { snocs = 0; tails = 1; heads = 0 }, 1
      ; ( "tail then head"
        , (fun q -> opaque (Q.head (Q.tail q)))
        , { snocs = 0; tails = 1; heads = 1 }
        , 2 )
      ; ( "snoc then head"
        , (fun q -> opaque (Q.head (Q.snoc q 0)))
        , { snocs = 1; tails = 0; heads = 1 }
        , 0 )
      ; ( "snoc then tail"
        , (fun q -> opaque (Q.tail (Q.snoc q 0)))
        , { snocs = 1; tails = 1; heads = 0 }
        , 0 )
      ]
    in
    List.map
      (fun (run, f, per, needs) ->
         let ops =
           { snocs = d * per.snocs; tails = d * per.tails; heads = d * per.heads }
         in
         let worst = ref (0, 0.0) in
         Array.iteri
           (fun k q ->
              if size k >= needs
              then (
                f q;
                let _, c =
                  cost_on bound.clock (fun () ->
                    for _ = 1 to d do
                      f q
                    done)
                in
                if c > snd !worst then worst := k, c))
           v;
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
    let _, first = cost_on bound.clock (fun () -> Q.tail v) in
    let _, rest =
      cost_on bound.clock (fun () ->
        for _ = 2 to d do
          ignore (Sys.opaque_identity (Q.tail v))
        done)
    in
    check
      (t
         (Printf.sprintf
            "the first of %d tails of one version %s, %.0f %s"
            d
            bound.dear_work
            first
            bound.units))
      (first >= bound.reverse_floor n);
    within
      (Printf.sprintf "and the other %d find it memoised" (d - 1))
      (tails (d - 1), rest);
    (* p.65, the branch point just before the rotation: the whole drain, d times over.
       "Because these are different suspensions, memoization does not help at all", and
       the bound holds anyway, because the operations were repeated along with the work. *)
    within
      "the whole drain repeated 10 times from one queue"
      (cost_on bound.clock (branch_at_the_start ~n ~d:10));
    (* Every branch point of a drain, with the shortest futures. Rotating early is what
       makes these cheap: a rotation is never forced by the operation after it, unless it
       was tiny. *)
    List.iter
      (fun (run, k, ops, c) ->
         within
           (Printf.sprintf
              "%s, 50 times over from each version of a drain, dearest from #%d"
              run
              k)
           (ops, c))
      (short_runs bound (versions n) ~size:(fun k -> n - k) ~d:50);
    (* And every branch point of a build: the queue after k snocs, for every k. A drain
       only ever shrinks, so its versions have all seen a rotation some time ago; a
       build's are the ones on the brink of the next. *)
    let n = 2_000 in
    let build = Array.make (n + 1) Q.empty in
    for i = 1 to n do
      build.(i) <- Q.snoc build.(i - 1) i
    done;
    List.iter
      (fun (run, k, ops, c) ->
         within
           (Printf.sprintf
              "%s, 20 times over from each version of a build, dearest from #%d"
              run
              k)
           (ops, c))
      (short_runs bound build ~size:Fun.id ~d:20);
    within
      "a random trace of 100000 operations, each on a random earlier version"
      (cost_on bound.clock (random_trace 100_000))
  ;;

  (* head at every version of a build of 100000 and its drain, each read as soon as it is
     made, before a later operation can force anything on its behalf: a queue whose head
     is O(1) worst-case reads it where it lies, and allocates nothing. *)
  let run_head name =
    let n = 100_000 in
    let dear = ref (0, 0.0)
    and sum = ref 0 in
    let read i q =
      let x, c = cost (fun () -> Q.head q) in
      sum := !sum + x;
      if c > snd !dear then dear := i, c
    in
    let q = ref Q.empty in
    for i = 1 to n do
      q := Q.snoc !q i;
      read i !q
    done;
    for i = n + 1 to (2 * n) - 1 do
      q := Q.tail !q;
      read i !q
    done;
    ignore (Sys.opaque_identity !sum);
    check
      (Printf.sprintf
         "%s: head allocates nothing at any version of a build of %d and its drain, \
          dearest #%d at %.0f words"
         name
         n
         (fst !dear)
         (snd !dear))
      (snd !dear = 0.0)
  ;;
end
