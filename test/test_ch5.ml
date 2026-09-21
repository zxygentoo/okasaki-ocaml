(* Tests for Chapter 5: the batched queue of Figure 5.2, and the deque of Exercise 5.1.
   Plain OCaml, no test framework, matching the earlier chapters.

   This is the first structure in the book whose costs are AMORTISED, and that changes
   what a cost test has to look like. "tail is O(1) amortised" is not a statement about
   any one tail -- the tail that runs the front list out reverses the whole rear, and is
   as linear as it looks. It is a statement about sequences: however the operations are
   ordered, m of them cost O(m) in total. So the amortised checks below never measure an
   operation. They run a whole sequence from the empty queue and divide by its length.

   Section 5.2 also makes three worst-case claims, and those ARE about single operations:
   snoc and head are O(1) always, and tail is O(n) at its worst. The invariant -- the
   front is empty only if the whole queue is -- exists precisely to buy the second of
   them, "we guarantee that head can always find the first element in O(1) time".

   QUEUE seals its representation, so cost is measured from outside, as allocation. For
   this structure that is a faithful proxy for the book's "steps", because every step
   allocates: a snoc is a cons, and reversing the rear is one cons per element. Nothing
   else in Figure 5.2 grows with the queue.

   The behavioural tests are written against QUEUE alone, in a functor, since this
   signature is about to be implemented many more times. *)

open Okasaki.Ch5

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

(* Words allocated by [f]. Sys.opaque_identity stops the optimiser discarding the result
   and with it the allocation we are trying to measure. *)
let words f =
  let before = Gc.minor_words () in
  ignore (Sys.opaque_identity (f ()));
  Gc.minor_words () -. before
;;

let upto n = List.init n Fun.id

(* The most a cheap operation may allocate, in words, and the most a sequence may average
   per operation. Outside the reversal, an operation of Figure 5.2 allocates a cons and a
   pair at the very most twice over, 12 words; the reversal's 3 words per element are
   charged to the snoc that put the element there, which is the whole amortised argument
   of p.44. The deque's dearest sequence averages 12 as well, a two-element rebalance at
   every other step. 16 leaves room for that and for the probe's own noise, and is nowhere
   near an operation that is really linear: at the sizes used here that is out by a factor
   of hundreds. *)
let constant = 16.0

(* For a check that sweeps many cases and keeps the offenders: say which came first. *)
let first_of describe = function
  | [] -> ""
  | bad -> " -- " ^ describe (List.nth bad (List.length bad - 1))
;;

(* Amortised O(1), asserted the only way an amortised bound can be: over whole sequences.
   Each is (name, operations per unit of n, driver), and a driver runs its sequence from
   scratch, single-threadedly -- the amortised bounds of this chapter promise nothing else
   -- allocating nothing of its own.

   True if every sequence stayed within the bound. The large size is guarded on the small
   one, as the earlier chapters guard theirs: an operation that is secretly linear makes a
   sequence quadratic, and at n = 100_000 that is not a failure but a hang. *)
let run_sequences name sequences =
  let t label = Printf.sprintf "%s: %s" name label in
  let ok = ref true in
  List.iter
    (fun (sequence, per_n, driver) ->
      let per_operation n = words (driver n) /. float_of_int (per_n * n) in
      let within label n =
        let w = per_operation n in
        check
          (t
             (Printf.sprintf
                "%s, %s: %.2f words per operation at n=%d"
                sequence
                label
                w
                n))
          (w <= constant);
        w <= constant
      in
      if not (within "amortised O(1)" 1_000)
      then (
        ok := false;
        Printf.printf
          "  SKIP  %s: %s at n=100000 -- it is not O(1) at n=1000\n"
          name
          sequence)
      else if not (within "still O(1) a hundred times longer" 100_000)
      then ok := false)
    sequences;
  !ok
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
    (* The two places the invariant can be lost. is_empty and head look at the front list
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

  (* ------------------------------------------------- amortised O(1) per operation *)

  (* Sequences of snocs and tails from the empty queue. They differ in where the reversals
     fall: one huge one, a tiny one at every step, or ever larger ones at ever longer
     intervals. *)
  let fill_then_drain n () =
    let q = ref Q.empty in
    for i = 1 to n do
      q := Q.snoc !q i
    done;
    for _ = 1 to n do
      q := Q.tail !q
    done;
    !q
  ;;

  let alternate n () =
    let q = ref Q.empty in
    for i = 1 to n do
      q := Q.snoc !q i;
      q := Q.tail !q
    done;
    !q
  ;;

  let two_snocs_per_tail n () =
    let q = ref Q.empty in
    for i = 1 to n do
      q := Q.snoc !q i;
      q := Q.snoc !q i;
      q := Q.tail !q
    done;
    !q
  ;;

  let random_mix n =
    Random.init 20260921;
    let snocs = Array.init n (fun _ -> Random.int 3 > 0) in
    fun () ->
      let q = ref Q.empty
      and size = ref 0 in
      for i = 0 to n - 1 do
        if snocs.(i) || !size = 0
        then (
          q := Q.snoc !q i;
          incr size)
        else (
          q := Q.tail !q;
          decr size)
      done;
      !q
  ;;

  (* name, operations per unit of n, driver *)
  let sequences =
    [ "n snocs then n tails", 2, fill_then_drain
    ; "snoc and tail alternating", 2, alternate
    ; "two snocs to every tail", 3, two_snocs_per_tail
    ; "a random mix", 1, random_mix
    ]
  ;;

  let run_amortised name = run_sequences name sequences
end

(* --------------------------------------------- BatchedQueue: worst-case costs *)

module Batched = Queue_tests (BatchedQueue)

(* What p.43 says about single operations of THIS queue: "snoc and head run in O(1)
   worst-case time, but tail takes O(n) time in the worst-case". Not part of the shared
   contract, because the queues to come trade these differently. *)
let test_batched_worst_case () =
  let sizes = [ 1; 2; 10; 1_000; 100_000 ] in
  (* A queue built by snocs alone is the adversarial one: its front holds a single element
     and everything else is waiting, reversed, in the rear. *)
  let built = List.map (fun n -> n, Batched.of_list (upto n)) sizes in
  (* head: what the invariant is for. With one element in front and n-1 behind it, a head
     that had to go looking would have to reverse, and reversing allocates. *)
  let bad = ref [] in
  List.iter
    (fun (n, q) ->
      let w = words (fun () -> BatchedQueue.head q) in
      if w <> 0.0 then bad := (n, w) :: !bad)
    built;
  check
    (Printf.sprintf
       "BatchedQueue: head allocates nothing, however long the rear%s"
       (match !bad with
        | [] -> ""
        | (n, w) :: _ -> Printf.sprintf " -- n=%d allocated %.0f words" n w))
    (!bad = []);
  let worst =
    List.fold_left
      (fun acc (_, q) -> Float.max acc (words (fun () -> BatchedQueue.snoc q 0)))
      (words (fun () -> BatchedQueue.snoc BatchedQueue.empty 0))
      built
  in
  check
    (Printf.sprintf "BatchedQueue: snoc is O(1) at every size (worst %.0f words)" worst)
    (worst <= constant);
  (* tail: the expensive one really is linear. This is the other half of what "amortised"
     means, and it is also the guard on everything above: if the probe could not see a
     reversal, the amortised checks would pass without having measured anything. *)
  let n = 100_000 in
  let q = List.assoc n built in
  let expensive = words (fun () -> BatchedQueue.tail q) in
  check
    (Printf.sprintf
       "BatchedQueue: the tail that runs the front out reverses the whole rear (%.0f \
        words at n=%d)"
       expensive
       n)
    (expensive >= 3.0 *. float_of_int (n - 1));
  (* ... and it is the only one. Having paid, the next n-2 tails are as cheap as a tail
     can be, which is where the amortised bound comes from. *)
  let rest = BatchedQueue.tail q in
  let cheap = words (fun () -> BatchedQueue.tail rest) in
  check
    (Printf.sprintf
       "BatchedQueue: and the tail after it is cheap again (%.0f words)"
       cheap)
    (cheap <= constant)
;;

let test_batched () =
  section "BatchedQueue (5.2)";
  let before = !failures in
  Batched.run_contract "BatchedQueue";
  (* What a queue costs means nothing until it behaves like one, and a queue that raises
     half way through a sequence would take the rest of this section down with it. *)
  if !failures > before
  then
    Printf.printf
      "  SKIP  BatchedQueue: cost checks -- the contract above does not hold\n"
  else if Batched.run_amortised "BatchedQueue"
  then test_batched_worst_case ()
  else
    Printf.printf
      "  SKIP  BatchedQueue: worst-case checks -- they build a queue of 100000 elements\n"
;;

(* ------------------------------------------------------ Exercise 5.1: deques *)

(* "The invariant is updated to be symmetric in its treatment of f and r: both are
   required to be non-empty whenever the deque contains two or more elements. When one
   list becomes empty, we split the other list in half and reverse one of the halves."

   A deque goes wrong in one of three places, and the tests are aimed at them.

   - One element. The invariant lets it sit in either list, so there are two one-element
     deques that must be indistinguishable, and every reader has to cope with both. They
     cannot be told apart from outside either, so the test reaches "one element" by every
     route it can think of and holds them all to the same behaviour.
   - The crossing. Filling from one end and emptying from the other is what forces a
     rebalance, and a rebalance that puts a half in the wrong place, or the wrong way
     round, still hands back the right NUMBER of elements.
   - Symmetry. last and init are head and tail in a mirror, and cons is snoc in one. Every
     check below that names an end has a twin that names the other.

   The cost side has its own trap. A deque that carries EVERYTHING across when one side
   runs dry returns every element correctly, and is amortised O(1) for as long as it is
   used as a queue -- it is BatchedQueue. It is a consumer who alternates ends that makes
   it carry the whole deque back and forth. So the sequences here switch ends, and
   [run_rebalance] checks the half directly: after the expensive removal BOTH ends are
   cheap, and the next expensive one is n/2 removals away.

   A DEQUE is a QUEUE, so the whole of Queue_tests applies to it unchanged, and runs
   first. *)

module Deque_tests (D : DEQUE) = struct
  module As_queue = Queue_tests (D)

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
  let drain_front q =
    let rec go acc q =
      if D.is_empty q then List.rev acc else go (D.head q :: acc) (D.tail q)
    in
    go [] q
  ;;

  let drain_back q =
    let rec go acc q = if D.is_empty q then acc else go (D.last q :: acc) (D.init q) in
    go [] q
  ;;

  let drain_both_ends q =
    let rec go front back from_front q =
      if D.is_empty q
      then List.rev_append front back
      else if from_front
      then go (D.head q :: front) back false (D.tail q)
      else go front (D.last q :: back) true (D.init q)
    in
    go [] [] true q
  ;;

  let drains =
    [ "the front", drain_front; "the back", drain_back; "both ends", drain_both_ends ]
  ;;

  let run_contract name =
    let t label = Printf.sprintf "%s: %s" name label in
    check_raises (t "last on empty raises") (Failure "last: empty queue") (fun () ->
      D.last D.empty);
    check_raises (t "init on empty raises") (Failure "init: empty queue") (fun () ->
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
    Random.init 20260921;
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

  (* --------------------------------------------- amortised O(1), switching ends *)

  let cons_then_init n () =
    let q = ref D.empty in
    for i = 1 to n do
      q := D.cons i !q
    done;
    for _ = 1 to n do
      q := D.init !q
    done;
    !q
  ;;

  (* The sequence that a carry-everything rebalance cannot survive. *)
  let snoc_then_both_ends n () =
    let q = ref D.empty in
    for i = 1 to n do
      q := D.snoc !q i
    done;
    for i = 1 to n do
      q := if i land 1 = 0 then D.tail !q else D.init !q
    done;
    !q
  ;;

  (* The smallest rebalance there is, over and over: a second element arrives on the side
     that already holds the first, and leaves again from the other. *)
  let smallest_rebalance n () =
    let q = ref (D.cons 0 D.empty) in
    for i = 1 to n do
      q := D.cons i !q;
      q := D.init !q
    done;
    !q
  ;;

  let random_mix n =
    Random.init 20260921;
    let ops = Array.init n (fun _ -> Random.int 6) in
    fun () ->
      let q = ref D.empty
      and size = ref 0 in
      for i = 0 to n - 1 do
        let op = if !size = 0 then ops.(i) land 3 else ops.(i) in
        if op < 4
        then (
          q := if op < 2 then D.snoc !q i else D.cons i !q;
          incr size)
        else (
          q := if op = 4 then D.tail !q else D.init !q;
          decr size)
      done;
      !q
  ;;

  let sequences =
    [ "n conses then n inits", 2, cons_then_init
    ; "n snocs, then tail and init alternating", 2, snoc_then_both_ends
    ; "cons and init alternating on one element", 2, smallest_rebalance
    ; "a random mix of all four writers", 1, random_mix
    ]
  ;;

  let run_amortised name = run_sequences name sequences

  (* ------------------------------------------------ the rebalance is by halves *)

  (* Fill from one end, then take one element from the other. That removal runs its side
     dry and has to rebalance. Asserted in both directions, as everything here is. *)
  let run_rebalance name =
    let n = 100_000 in
    List.iter
      (fun (side, build, remove, remove_other) ->
        let t label = Printf.sprintf "%s: %s, %s" name side label in
        let q = build (upto n) in
        (* What the invariant is for: both ends readable without going looking. *)
        let looking q = words (fun () -> D.head q) +. words (fun () -> D.last q) in
        check (t "head and last allocate nothing before the rebalance") (looking q = 0.0);
        let expensive = words (fun () -> remove q) in
        (* Linear, because it moves half: at least a cons for each element that crosses.
           It is also the guard on the amortised checks, which would pass unmeasured if
           the probe could not see a rebalance at all. *)
        check
          (t
             (Printf.sprintf
                "the removal that runs a side dry is linear (%.0f words at n=%d)"
                expensive
                n))
          (expensive >= 1.5 *. float_of_int (n - 2));
        let after = remove q in
        check (t "head and last allocate nothing after it") (looking after = 0.0);
        let near = words (fun () -> remove after)
        and far = words (fun () -> remove_other after) in
        check
          (t
             (Printf.sprintf
                "BOTH ends are cheap after it (%.0f and %.0f words)"
                near
                far))
          (near <= constant && far <= constant);
        (* In half: the side that ran dry now holds n/2, so that is how many removals it
           takes to run it dry again. Carrying one element across gives 0 here. *)
        let rec cheap_run count q =
          if count > n || words (fun () -> remove q) > constant
          then count
          else cheap_run (count + 1) (remove q)
        in
        let cheap = cheap_run 0 after in
        check
          (t
             (Printf.sprintf
                "the next rebalance is n/2 removals away (%d cheap ones, n=%d)"
                cheap
                n))
          (cheap >= (n / 2) - 2 && cheap <= (n / 2) + 2))
      [ "front", snocs, D.tail, D.init; "rear", conses, D.init, D.tail ]
  ;;
end

module Deque_checks = Deque_tests (Deque)

let test_deque () =
  section "Deque (Exercise 5.1)";
  let before = !failures in
  Deque_checks.As_queue.run_contract "Deque";
  Deque_checks.run_contract "Deque";
  if !failures > before
  then Printf.printf "  SKIP  Deque: cost checks -- the contract above does not hold\n"
  else if Deque_checks.As_queue.run_amortised "Deque"
          && Deque_checks.run_amortised "Deque"
  then Deque_checks.run_rebalance "Deque"
  else
    Printf.printf
      "  SKIP  Deque: rebalance checks -- they build a deque of 100000 elements\n"
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
  run "BatchedQueue" test_batched;
  run "Deque" test_deque;
  Printf.printf "\n%d checks, %d failures\n\n" !checks !failures;
  if !failures > 0 then exit 1
;;
