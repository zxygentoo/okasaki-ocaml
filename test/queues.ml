(* The checks Chapters 5 to 8 hold their queues and deques to, written once. Every chapter
   declares QUEUE and DEQUE over again, but as the same signatures, so the functors here
   take the queues of all of them. *)

open Harness

(* ------------------------------------------------------- the queue contract *)

module Contract (Q : Okasaki.Ch5.QUEUE) = struct
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
    (D : Okasaki.Ch5.DEQUE)
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
    (Q : Okasaki.Ch5.QUEUE)
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
