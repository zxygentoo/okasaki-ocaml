(* Tests for Chapter 5: the batched queue of Figure 5.2, the deque of Exercise 5.1, the
   splay heap of Figure 5.5 with Exercises 5.4 and 5.7, and the pairing heap of Figure 5.6
   in both its representations (Exercise 5.8). Plain OCaml, no test framework, matching
   the earlier chapters.

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

(* ------------------------------------------------------- splay heaps (5.4) *)

(* "Although any individual operation can take as much as O(n) time, we will show that
   every operation runs in O(log n) amortized time" (p.46). Both halves of that sentence
   are asserted: this is the first structure in the book whose bound is a logarithm rather
   than a constant, and the first whose single operations are linear by design.

   HEAP seals the tree, so its shape is measured from outside, with two instruments that
   see two different things. Comparisons see partition and nothing else: it asks
   Element.leq of the nodes it visits, and "since we always take the left branch, there is
   no need for comparisons" (p.49) in find_min or delete_min. Allocation sees the
   rebuilding: every node on a restructured path is copied, in partition and in delete_min
   alike, so words allocated is the length of the path that was rebuilt.

   The amortised bound is asserted as the queue sections assert theirs, over whole
   sequences from the empty heap, except that the cost per operation is divided by log2 n
   as well. The constants are the book's. Theorem 5.2 bounds partition at 1 + 2 log2(#t)
   recursive calls per insert amortised, each call making at most two comparisons; that is
   doubled here to admit the two-pass partition of Exercise 5.4, whose smaller and bigger
   each earn the bound separately. delete_min's O(log n) is Exercise 5.6 and its constant
   is not derived in the book; the words bound is partition's with room for it. Cheap
   sequences would pass a much tighter bound, so a second check asks that the cost per
   operation per log2 n does not grow from n = 1000 to n = 100_000: that is the shape of
   the claim, whatever the constant.

   One O(n) is left unasserted on purpose: find_min on a spine, which p.51 says "there is
   no way to amortize". It neither compares nor allocates, so no counter sees it.

   The contract is the one test_ch3 holds its five heaps to, plus two checks aimed at
   Exercise 5.4, where a partition can keep every drain of distinct elements sorted while
   quietly losing an element equal to the pivot, or carrying a subtree to the wrong side
   of its parent. *)

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

(* Comparisons performed by [f]. *)
let count f =
  comparisons := 0;
  let r = f () in
  r, !comparisons
;;

let count_only f = snd (count f)
let log2 n = log (float_of_int n) /. log 2.

(* Per operation, amortised, for the O(log n) heaps of this chapter: Theorem 5.2's 1 + 2
   log2(#t) partition calls, two comparisons each, doubled for a two-pass partition; and
   for words, the nodes those calls copy, with room for delete_min's. #t is the size plus
   one. Exercise 5.8(c) carries the same analysis, with the same potential, over to
   pairing heaps, so they are held to the same line. *)
let comparison_bound n = 4. +. (8. *. log2 (n + 1))
let word_bound n = 24. +. (32. *. log2 (n + 1))

(* Amortised O(log n), asserted as [run_sequences] asserts O(1): over whole sequences from
   the empty structure, cost per operation, here measured in comparisons and words both
   and compared to the bounds above. True if every sequence stayed within them. Sizes
   climb by tens, each guarded on the one before: a quadratic that still fits under the
   bound at n = 1000 is caught at n = 10_000, where it costs a fraction of a second,
   instead of at n = 100_000, where it would take the better part of a minute to fail. *)
let run_log_sequences name sequences =
  let t label = Printf.sprintf "%s: %s" name label in
  let ok = ref true in
  List.iter
    (fun (sequence, per_n, driver) ->
      let within n =
        let f = driver n in
        let ops = float_of_int (per_n * n) in
        let c = float_of_int (count_only f) /. ops in
        let w = words f /. ops in
        let fits = c <= comparison_bound n && w <= word_bound n in
        check
          (t
             (Printf.sprintf
                "%s, amortised O(log n): %.1f comparisons and %.0f words per operation \
                 at n=%d"
                sequence
                c
                w
                n))
          fits;
        c, w, fits
      in
      let rec climb first = function
        | [] -> ()
        | n :: larger ->
          let c, w, fits = within n in
          if not fits
          then (
            ok := false;
            List.iter
              (fun m ->
                Printf.printf
                  "  SKIP  %s: %s at n=%d -- it is not O(log n) at n=%d\n"
                  name
                  sequence
                  m
                  n)
              larger)
          else (
            match first with
            | None -> climb (Some (n, c, w)) larger
            | Some (n0, c0, w0) when larger = [] ->
              (* Per operation per log2 n, a hundred times longer: the same or less,
                 within noise. That is the shape of the claim whatever the constant. *)
              let per_log v n = v /. log2 (n + 1) in
              let flat v0 v = per_log v n <= (1.5 *. per_log v0 n0) +. 0.5 in
              check
                (t
                   (Printf.sprintf
                      "%s, the cost per operation grows no faster than log n (%.2f -> \
                       %.2f comparisons, %.1f -> %.1f words, per log2 n)"
                      sequence
                      (per_log c0 n0)
                      (per_log c n)
                      (per_log w0 n0)
                      (per_log w n)))
                (flat c0 c && flat w0 w)
            | first -> climb first larger)
      in
      climb None [ 1_000; 10_000; 100_000 ])
    sequences;
  !ok
;;

module Heap_tests (H : HEAP with type Element.t = int) = struct
  let of_list xs = List.fold_left (fun h x -> H.insert x h) H.empty xs

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
    check_raises
      (t "delete_min on empty raises")
      (Failure "delete_min: empty heap")
      (fun () -> ignore (H.is_empty (H.delete_min H.empty)));
    check_int (t "find_min of a singleton") ~expect:5 ~actual:(H.find_min (of_list [ 5 ]));
    check
      (t "delete_min of a singleton is empty")
      (H.is_empty (H.delete_min (of_list [ 5 ])));
    eq "drain is sorted" [ 1; 2; 3; 4; 5; 6; 7 ] (of_list [ 4; 2; 6; 1; 3; 5; 7 ]);
    (* Aimed at Exercise 5.4. A drain of distinct elements cannot tell which side of the
       partition an element equal to the pivot went to -- but it must go to one of them.
       Sent to neither, it vanishes. The copy is met at the root, at the bottom of the
       left spine and at the bottom of the right spine, so every branch of the partition
       meets it. *)
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
    (* Also aimed at Exercise 5.4. A subtree carried to the wrong side of its parent keeps
       every element, so only the order notices, and it notices first at the minimum:
       find_min follows left branches, and a minimum that has been put on the right is not
       where it looks. *)
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
    (* Persistence: no operation may disturb its operands. A splay heap restructures on
       every insert and delete_min, so this is the check that the restructuring builds new
       nodes rather than reusing old ones in a new place. *)
    let h = of_list [ 5; 3; 8; 1 ] in
    let _ = H.insert 0 h
    and _ = H.insert 4 h
    and _ = H.delete_min h
    and _ = H.merge h h in
    eq "operands are untouched" [ 1; 3; 5; 8 ] h
  ;;

  (* ------------------------------------------------- amortised O(log n) per operation *)

  (* Sequences from the empty heap, each single-threaded, each allocating nothing of its
     own. They differ in the shape they force. Ascending inserts build a left spine of
     depth n at O(1) each and leave every restructuring to the delete_mins; random inserts
     keep the tree shallow on their own, so they measure the ordinary case. Random inserts
     into a spine are not the test they look like: each one cuts a segment of the spine
     off unrestructured, and the segments shorten by themselves, O(n log n) in all even
     for a plain search tree. What separates splaying from a plain tree is walking the
     SAME long path again and again: a left spine, then inserts that climb towards it from
     below, each one walking the whole spine unless the walks before it have halved it. A
     partition that does not restructure is quadratic there and one that does is linear.
     The bigger half of the partition does that halving; its mirror -- a right spine, then
     inserts descending towards it from above -- asks the same of the smaller half, which
     is the half Exercise 5.4 has you write. *)
  let drain_all h n =
    let h = ref h in
    for _ = 1 to n do
      h := H.delete_min !h
    done;
    !h
  ;;

  let random_ints seed n bound =
    Random.init seed;
    List.init n (fun _ -> Random.int bound)
  ;;

  let sequences =
    [ ( "n random inserts, then n delete_mins"
      , 2
      , fun n ->
          let xs = random_ints 20260922 n 1_000_000 in
          fun () -> drain_all (of_list xs) n )
    ; ( "n ascending inserts, then n delete_mins"
      , 2
      , fun n () -> drain_all (of_list (upto n)) n )
    ; ( "n descending inserts, then n delete_mins"
      , 2
      , fun n () -> drain_all (of_list (List.init n (fun i -> n - i))) n )
    ; ( "a spine of n, then n random inserts"
      , 2
      , fun n ->
          let xs = random_ints 20260923 n n in
          fun () -> List.fold_left (fun h x -> H.insert x h) (of_list (upto n)) xs )
    ; ( "a left spine of n, then n inserts climbing towards it from below"
      , 2
      , fun n () ->
          let h = ref (of_list (List.init n (fun i -> n + i))) in
          for i = 0 to n - 1 do
            h := H.insert i !h
          done;
          !h )
    ; ( "a right spine of n, then n inserts descending towards it from above"
      , 2
      , fun n () ->
          let h = ref (of_list (List.init n (fun i -> n - 1 - i))) in
          for i = 0 to n - 1 do
            h := H.insert ((2 * n) - 1 - i) !h
          done;
          !h )
    ; ( "inserts converging on the middle, then n delete_mins"
      , 2
      , fun n () ->
          let h = ref H.empty in
          for i = 0 to (n / 2) - 1 do
            h := H.insert i !h;
            h := H.insert (n - 1 - i) !h
          done;
          drain_all !h n )
    ; ( "n equal inserts, then n delete_mins"
      , 2
      , fun n () -> drain_all (of_list (List.init n (fun _ -> 7))) n )
    ]
  ;;

  let run_amortised name = run_log_sequences name sequences

  (* ------------------------------------------------ single operations: linear *)

  (* The other half of p.46. Ascending inserts build a left spine: each new element is the
     maximum, so partition looks at the root, finds its right child empty, and stops, at
     O(1) a time -- which is exactly why nothing has been restructured and the spine is n
     deep. The first operation to walk it pays for all of that at once, and halves it
     (p.47: "the depth of every node has been reduced by about half"). *)
  let run_worst_case name =
    let t label = Printf.sprintf "%s: %s" name label in
    let n = 100_000 in
    let spine, built = count (fun () -> of_list (upto n)) in
    check
      (t
         (Printf.sprintf
            "ascending inserts cost O(1) each (%d comparisons for %d)"
            built
            n))
      (built <= 2 * n);
    (* find_min and delete_min only ever go left: no comparisons, and find_min copies
       nothing either. *)
    check_int
      (t "find_min compares nothing")
      ~expect:0
      ~actual:(count_only (fun () -> H.find_min spine));
    check (t "find_min allocates nothing") (words (fun () -> H.find_min spine) <= 4.0);
    check_int
      (t "delete_min compares nothing")
      ~expect:0
      ~actual:(count_only (fun () -> H.delete_min spine));
    (* delete_min rebuilds the whole spine ... *)
    let first = words (fun () -> H.delete_min spine) in
    check
      (t
         (Printf.sprintf
            "the first delete_min on the spine is linear (%.0f words at n=%d)"
            first
            n))
      (first >= 3.0 *. float_of_int n);
    (* ... and the next one finds a path about half as long. Halved, not merely shorter: a
       rebuild that did not restructure would cost the same again, and one that flattened
       the path entirely would not be this algorithm. *)
    let after = H.delete_min spine in
    let second = words (fun () -> H.delete_min after) in
    check
      (t
         (Printf.sprintf
            "the delete_min after it walks about half the path (%.0f words)"
            second))
      (second >= 0.4 *. first && second <= 0.6 *. first);
    (* The same for partition: an insert into the middle of the spine walks n/2 nodes
       comparing as it goes, and the insert after it walks about half of that. *)
    let c1 = count_only (fun () -> H.insert (n / 2) spine) in
    check
      (t
         (Printf.sprintf
            "inserting the median into the spine is linear (%d comparisons)"
            c1))
      (c1 >= (n / 2) - 2);
    let mid = H.insert (n / 2) spine in
    let c2 = count_only (fun () -> H.insert ((n / 2) + 1) mid) in
    check
      (t
         (Printf.sprintf
            "the insert after it walks about half the path (%d comparisons)"
            c2))
      (float_of_int c2 >= 0.4 *. float_of_int c1
       && float_of_int c2 <= 0.6 *. float_of_int c1);
    (* And in the mirror, where the walk goes right and the smaller half of the partition
       does the restructuring: descending inserts build a right spine, and the median goes
       in from the other side. *)
    let right = of_list (List.init n (fun i -> n - 1 - i)) in
    let c1 = count_only (fun () -> H.insert (n / 2) right) in
    check
      (t
         (Printf.sprintf
            "inserting the median into the right spine is linear (%d comparisons)"
            c1))
      (c1 >= (n / 2) - 2);
    let mid = H.insert (n / 2) right in
    let c2 = count_only (fun () -> H.insert ((n / 2) - 1) mid) in
    check
      (t
         (Printf.sprintf
            "the insert after it walks about half the path (%d comparisons)"
            c2))
      (float_of_int c2 >= 0.4 *. float_of_int c1
       && float_of_int c2 <= 0.6 *. float_of_int c1)
  ;;
end

module Splay = SplayHeap (Counting_int)
module Splay_checks = Heap_tests (Splay)

let test_splay () =
  section "SplayHeap (5.4)";
  let before = !failures in
  Splay_checks.run_contract "SplayHeap";
  if !failures > before
  then
    Printf.printf "  SKIP  SplayHeap: cost checks -- the contract above does not hold\n"
  else if Splay_checks.run_amortised "SplayHeap"
  then Splay_checks.run_worst_case "SplayHeap"
  else
    Printf.printf
      "  SKIP  SplayHeap: worst-case checks -- they build a heap of 100000 elements\n"
;;

(* ----------------------------------------------- Exercise 5.7: sorting with a splay tree *)

(* "Write a sorting function that inserts elements into a splay tree and then performs an
   inorder traversal of the tree, dumping the elements into a list. Show that this
   function takes only O(n) time on an already sorted list."

   The showing is the exercise. What is asserted is the claim itself, in the only form a
   test can give it: the cost per element of sorting an already sorted list is a constant,
   and stays that constant from n = 1000 to n = 100_000. Whatever the sort does inside, a
   step that is quadratic on the spine the sorted inserts build -- the obvious traversal
   with @ is one -- shows up here as a per-element cost a hundred times larger at the
   larger size. p.52 says splay heaps "excel on both increasing and decreasing sequences",
   so the descending list is held to the same bound. Random input is the contrast: there
   the sort is a comparison sort like any other and costs Theorem 5.2's O(log n) per
   element, which is the bound the splay-heap sequences above use. *)

let test_splay_sort () =
  section "SplayHeap.sort (Exercise 5.7)";
  let sort xs = Splay.sort xs in
  let eq name expect xs =
    surviving
      name
      (fun () -> sort xs)
      (fun actual -> check_eq name ~expect ~actual string_of_int_list)
  in
  eq "sort of the empty list" [] [];
  eq "sort of a singleton" [ 7 ] [ 7 ];
  eq "sort" [ 1; 2; 3; 5; 8; 9 ] [ 5; 3; 8; 1; 9; 2 ];
  eq "sort of a sorted list" [ 1; 2; 3; 4 ] [ 1; 2; 3; 4 ];
  eq "sort of a reversed list" [ 1; 2; 3; 4 ] [ 4; 3; 2; 1 ];
  eq "sort keeps duplicates" [ 1; 1; 2; 2; 3; 3 ] [ 2; 1; 3; 1; 2; 3 ];
  Random.init 20260922;
  let bad = ref 0 in
  for _ = 0 to 299 do
    let xs = List.init (Random.int 40) (fun _ -> Random.int 10) in
    if sort xs <> List.sort compare xs then incr bad
  done;
  check_int "sort agrees with List.sort, 300 random lists" ~expect:0 ~actual:!bad;
  (* Cost per element, at two sizes a hundred apart. *)
  let per_element xs =
    let n = float_of_int (List.length xs) in
    let c = float_of_int (count_only (fun () -> sort xs)) /. n in
    let w = words (fun () -> sort xs) /. n in
    c, w
  in
  let small = 1_000
  and large = 100_000 in
  let linear name make =
    let c1, w1 = per_element (make small) in
    (* Inserting a new maximum, or a new minimum, looks at the root and stops: one
       comparison. Sixty-four words is several nodes' worth per element, far more than a
       linear sort needs and far less than a quadratic one spends at either size. *)
    let fits = c1 <= 4.0 && w1 <= 64.0 in
    check
      (Printf.sprintf
         "an already %s list costs O(1) per element (%.1f comparisons, %.0f words at \
          n=%d)"
         name
         c1
         w1
         small)
      fits;
    (* Guarded, as every large size here is: a quadratic sort takes minutes at n=100000. *)
    if not fits
    then (
      Printf.printf
        "  SKIP  an already %s list at n=%d -- it is not O(1) per element at n=%d\n"
        name
        large
        small;
      None)
    else (
      let c2, w2 = per_element (make large) in
      check
        (Printf.sprintf
           "and stays O(1) per element a hundred times longer (%.1f comparisons, %.0f \
            words at n=%d)"
           c2
           w2
           large)
        (c2 <= 4.0 && w2 <= 64.0 && c2 <= (1.5 *. c1) +. 0.5 && w2 <= (1.5 *. w1) +. 4.0);
      Some c2)
  in
  let sorted_large = linear "sorted" upto in
  ignore (linear "reverse-sorted" (fun n -> List.init n (fun i -> n - i)));
  (* Random input: O(log n) per element, no better, and it must really cost more than the
     sorted case does, or the checks above have measured nothing. *)
  let xs = Splay_checks.random_ints 20260924 large 1_000_000 in
  let c, w = per_element xs in
  check
    (Printf.sprintf
       "a random list costs O(log n) per element (%.1f comparisons, %.0f words at n=%d)"
       c
       w
       large)
    (c <= comparison_bound large && w <= word_bound large);
  match sorted_large with
  | None -> ()
  | Some c_sorted ->
    check
      (Printf.sprintf
         "the sorted list really is the cheap case (%.1f comparisons per element against \
          %.1f)"
         c_sorted
         c)
      (c >= 2.0 *. c_sorted)
;;

(* ------------------------------------------------------- pairing heaps (5.5) *)

(* p.53: "it is easy to see that findMin, insert, and merge all run in O(1) worst-case
   time. However, deleteMin can take up to O(n) time in the worst case. By drawing an
   analogy to splay trees (see Exercise 5.8), we can show that insert, merge, and
   deleteMin all run in O(log n) amortized time. It has been conjectured that insert and
   merge actually run in O(1) amortized time, but no one has yet been able to prove or
   disprove this claim."

   One instrument is enough here, because a pairing heap does exactly one thing that costs
   anything: merge compares the two roots once and makes the loser the leftmost child of
   the winner. So the comparison count IS the merge count -- insert is one merge,
   delete_min of a root with k children is k - 1 of them -- and nothing else compares at
   all. Allocation tells the same story (a node and a cons per merge) and is kept as the
   check that a merge does not quietly do more than that, such as walking a child list.

   Two shapes recur. n ascending inserts leave the first element at the root with the
   other n - 1 as its direct children, each a singleton: a star, and the delete_min that
   follows has all of them to pair up. n descending inserts make each new element the
   root, with the previous heap as its only child: a chain, where delete_min has one child
   and nothing to merge.

   Not asserted: the well-formedness invariant, "E never occurs in the child list of a T
   node" (p.52) -- HEAP seals the tree, and a drain notices a lost element but not a stray

   E. Not asserted either, because it is an open problem: the conjectured O(1) amortised
   insert and merge. The sequences below hold them to the proven O(log n). *)

module Pairing_tests (H : HEAP with type Element.t = int) = struct
  let of_list xs = List.fold_left (fun h x -> H.insert x h) H.empty xs
  let star n = of_list (upto n)
  let chain n = of_list (List.init n (fun i -> n - i))

  (* -------------------------------------------- find_min, insert, merge are O(1) *)

  let run_worst_case name =
    let t label = Printf.sprintf "%s: %s" name label in
    let n = 100_000 in
    let star = star n
    and chain = chain n in
    (* find_min reads the root. *)
    check_int
      (t "find_min compares nothing")
      ~expect:0
      ~actual:
        (count_only (fun () -> H.find_min star) + count_only (fun () -> H.find_min chain));
    check
      (t "find_min allocates nothing")
      (words (fun () -> H.find_min star) <= 4.0
       && words (fun () -> H.find_min chain) <= 4.0);
    (* insert is one merge, whatever the heap looks like and whichever way the comparison
       goes: a new maximum onto the star, a new minimum onto it, anything onto the chain. *)
    let inserts =
      [ ("a larger element into the star", fun () -> H.insert n star)
      ; ("a new minimum into the star", fun () -> H.insert (-1) star)
      ; ("into the chain", fun () -> H.insert n chain)
      ]
    in
    let bad =
      List.filter (fun (_, f) -> count_only f <> 1 || words f > 16.0) (List.rev inserts)
    in
    check
      (t
         (Printf.sprintf
            "insert is one comparison and O(1) words at n=%d%s"
            n
            (first_of
               (fun (how, f) ->
                 Printf.sprintf
                   "%s: %d comparisons, %.0f words"
                   how
                   (count_only f)
                   (words f))
               bad)))
      (bad = []);
    (* merge is one comparison, whatever the two sizes. *)
    let merges =
      [ ("star with chain", fun () -> H.merge star chain)
      ; ("chain with star", fun () -> H.merge chain star)
      ; ("star with a singleton", fun () -> H.merge star (H.insert 5 H.empty))
      ; ("a singleton with the star", fun () -> H.merge (H.insert 5 H.empty) star)
      ]
    in
    let bad =
      List.filter (fun (_, f) -> count_only f <> 1 || words f > 16.0) (List.rev merges)
    in
    check
      (t
         (Printf.sprintf
            "merge is one comparison and O(1) words at n=%d%s"
            n
            (first_of
               (fun (how, f) ->
                 Printf.sprintf
                   "%s: %d comparisons, %.0f words"
                   how
                   (count_only f)
                   (words f))
               bad)))
      (bad = []);
    (* --------------------------------------------------- delete_min is O(n) at worst *)
    (* The star's root has n - 1 children, and pairing them up and merging the pairs is
       n - 2 merges: the linear worst case the book states, and the guard that the
       sequences below have something to amortise. The chain's root has one child, so the
       same operation there merges nothing. *)
    let c = count_only (fun () -> H.delete_min star) in
    check
      (t (Printf.sprintf "delete_min on the star is linear (%d comparisons at n=%d)" c n))
      (c >= n - 2);
    check_int
      (t "delete_min on the chain compares nothing")
      ~expect:0
      ~actual:(count_only (fun () -> H.delete_min chain))
  ;;

  (* ------------------------------------------------- amortised O(log n) per operation *)

  (* Drains of the shapes above, mixes, and -- since pairing heaps are "much faster for
     applications that do [use merge]" (p.53) -- sequences that build the heap by merging
     rather than inserting. *)
  let drain_all h n =
    let h = ref h in
    for _ = 1 to n do
      h := H.delete_min !h
    done;
    !h
  ;;

  let random_ints seed n bound =
    Random.init seed;
    List.init n (fun _ -> Random.int bound)
  ;;

  let sequences =
    [ ( "n random inserts, then n delete_mins"
      , 2
      , fun n ->
          let xs = random_ints 20260925 n 1_000_000 in
          fun () -> drain_all (of_list xs) n )
    ; ("the star of n, then n delete_mins", 2, fun n () -> drain_all (star n) n)
    ; ("the chain of n, then n delete_mins", 2, fun n () -> drain_all (chain n) n)
    ; ( "n equal inserts, then n delete_mins"
      , 2
      , fun n () -> drain_all (of_list (List.init n (fun _ -> 7))) n )
    ; ( "sawtooth inserts, then n delete_mins"
      , 2
      , fun n () ->
          drain_all (of_list (List.init n (fun i -> if i mod 2 = 0 then i else n - i))) n
      )
    ; ( "insert, insert, delete_min, n times over"
      , 3
      , fun n ->
          let xs = Array.of_list (random_ints 20260926 (2 * n) 1_000_000) in
          fun () ->
            let h = ref H.empty in
            for i = 0 to n - 1 do
              h := H.insert xs.(2 * i) !h;
              h := H.insert xs.((2 * i) + 1) !h;
              h := H.delete_min !h
            done;
            !h )
    ; ( "n singletons merged pairwise into one heap, then n delete_mins"
      , 2
      , fun n ->
          let xs = random_ints 20260927 n 1_000_000 in
          fun () ->
            let rec pass = function
              | a :: b :: rest -> H.merge a b :: pass rest
              | short -> short
            in
            let rec rounds = function
              | [] -> H.empty
              | [ h ] -> h
              | hs -> rounds (pass hs)
            in
            drain_all (rounds (List.map (fun x -> H.insert x H.empty) xs)) n )
    ; ( "two random heaps of n/2 merged, then n delete_mins"
      , 2
      , fun n ->
          let xs = random_ints 20260928 (n / 2) 1_000_000
          and ys = random_ints 20260929 (n / 2) 1_000_000 in
          fun () -> drain_all (H.merge (of_list xs) (of_list ys)) (2 * (n / 2)) )
    ]
  ;;

  let run_amortised name = run_log_sequences name sequences
end

module Pairing = PairingHeap (Counting_int)
module Pairing_contract = Heap_tests (Pairing)
module Pairing_checks = Pairing_tests (Pairing)

let test_pairing () =
  section "PairingHeap (5.5)";
  let before = !failures in
  Pairing_contract.run_contract "PairingHeap";
  (* Two heaps of this chapter, two shapes in memory, one behaviour. *)
  Random.init 20260930;
  let disagree = ref 0 in
  for _ = 0 to 299 do
    let xs = List.init (Random.int 60) (fun _ -> Random.int 30) in
    if Pairing_contract.drain (Pairing_contract.of_list xs)
       <> Splay_checks.drain (Splay_checks.of_list xs)
    then incr disagree
  done;
  check_int
    "PairingHeap and SplayHeap drain identically, 300 random lists"
    ~expect:0
    ~actual:!disagree;
  if !failures > before
  then
    Printf.printf "  SKIP  PairingHeap: cost checks -- the contract above does not hold\n"
  else if Pairing_checks.run_amortised "PairingHeap"
  then Pairing_checks.run_worst_case "PairingHeap"
  else
    Printf.printf
      "  SKIP  PairingHeap: worst-case checks -- they build a heap of 100000 elements\n"
;;

(* ------------------------------------------ Exercise 5.8(a): to_binary, the encoding *)

(* "Write a function toBinary that converts pairing heaps from the existing representation
   into the type BinTree." Convert exposes both of its types, so unlike everything else in
   this chapter the trees can be built and read directly.

   The encoding is fixed by the exercise text -- left field: leftmost child; right field:
   the sibling to the immediate right; a missing one is E -- and it is a bijection between
   multiway trees and binary trees whose root has no right sibling. So there are two kinds
   of check. Hand-written cases pin the encoding itself, in particular which field the
   children go into and that the leftmost child comes first. The random cases assert what
   a bijection owes: a round trip through an inverse gives the tree back, nothing is lost
   or duplicated, the root's right field is E, and -- the exercise's own remark -- a
   heap-ordered multiway tree comes out half-ordered, "the element at each node is no
   greater than any element in its left subtree". The right subtree is exempt from that on
   purpose: it holds siblings, which are bounded by the parent, not by the node.

   Not a claim the book makes, but a cost worth pinning: the conversion is one binary node
   per multiway node, so words per node are constant, on a wide tree and on a deep one. *)

module Conv = Convert (Counting_int)

let test_to_binary () =
  section "to_binary (Exercise 5.8a)";
  let open Conv in
  let rec show = function
    | E2 -> "E"
    | T2 (x, a, b) -> Printf.sprintf "T(%d,%s,%s)" x (show a) (show b)
  in
  let eq name ~expect h = check_eq name ~expect ~actual:(to_binary h) show in
  eq "the empty heap" ~expect:E2 E1;
  eq "a singleton" ~expect:(T2 (1, E2, E2)) (T1 (1, []));
  (* Children go LEFT, siblings go RIGHT, the leftmost child first; the root's right field
     is E. 1[3, 2] is what inserting 1, 2, 3 into a pairing heap builds. *)
  eq
    "1[3, 2]: children hang off the left field, leftmost first"
    ~expect:(T2 (1, T2 (3, E2, T2 (2, E2, E2)), E2))
    (T1 (1, [ T1 (3, []); T1 (2, []) ]));
  eq
    "1[6, 2[5], 9[8[7]]]: every node's children left, its right sibling right"
    ~expect:
      (T2
         ( 1
         , T2 (6, E2, T2 (2, T2 (5, E2, E2), T2 (9, T2 (8, T2 (7, E2, E2), E2), E2)))
         , E2 ))
    (T1 (1, [ T1 (6, []); T1 (2, [ T1 (5, []) ]); T1 (9, [ T1 (8, [ T1 (7, []) ]) ]) ]));
  (* The inverse, written here: it fails loudly on a root with a sibling, which no
     multiway tree encodes to. *)
  let rec from_binary = function
    | E2 -> E1
    | T2 (x, a, E2) -> T1 (x, siblings a)
    | T2 _ -> invalid_arg "from_binary: the root has a right sibling"
  and siblings = function
    | E2 -> []
    | T2 (x, a, b) -> T1 (x, siblings a) :: siblings b
  in
  let rec elements1 = function
    | E1 -> []
    | T1 (x, hs) -> x :: List.concat_map elements1 hs
  in
  let rec elements2 = function
    | E2 -> []
    | T2 (x, a, b) -> (x :: elements2 a) @ elements2 b
  in
  let rec all p = function
    | E2 -> true
    | T2 (x, a, b) -> p x && all p a && all p b
  in
  let rec half_ordered = function
    | E2 -> true
    | T2 (x, a, b) -> all (fun y -> x <= y) a && half_ordered a && half_ordered b
  in
  let root_right_empty = function
    | E2 | T2 (_, _, E2) -> true
    | T2 _ -> false
  in
  (* Random heap-ordered multiway trees: every child's element is at least its parent's,
     and E never appears in a child list. *)
  let rec random_tree lo depth =
    let x = lo + Random.int 4 in
    let k = if depth = 0 then 0 else Random.int 4 in
    T1 (x, List.init k (fun _ -> random_tree x (depth - 1)))
  in
  Random.init 20261002;
  let not_bijective = ref 0
  and lost = ref 0
  and sibling_root = ref 0
  and not_half = ref 0 in
  for _ = 0 to 299 do
    let h = random_tree 0 (Random.int 5) in
    let b = to_binary h in
    if try from_binary b <> h with
       | Invalid_argument _ -> true
    then incr not_bijective;
    if List.sort compare (elements2 b) <> List.sort compare (elements1 h) then incr lost;
    if not (root_right_empty b) then incr sibling_root;
    if not (half_ordered b) then incr not_half
  done;
  check_int
    "converting and back gives the tree again, 300 random trees"
    ~expect:0
    ~actual:!not_bijective;
  check_int "every element survives, once" ~expect:0 ~actual:!lost;
  check_int "the root's right field is always E" ~expect:0 ~actual:!sibling_root;
  check_int "a heap-ordered tree comes out half-ordered" ~expect:0 ~actual:!not_half;
  (* One binary node per multiway node, on a wide tree and on a deep one. *)
  let star n = T1 (0, List.init n (fun i -> T1 (i + 1, []))) in
  let rec chain n = if n = 0 then [] else [ T1 (n, chain (n - 1)) ] in
  let per_node shape n =
    let h = shape n in
    words (fun () -> to_binary h) /. float_of_int n
  in
  List.iter
    (fun (name, shape) ->
      let small = per_node shape 1_000 in
      (* A node is a few words. A conversion that copies chains is thousands per node
         already at n=1000, and minutes of work at n=100000, so the large size is guarded. *)
      if small > 32.0
      then
        check
          (Printf.sprintf
             "to_binary is linear on %s (%.1f words per node at n=1000)"
             name
             small)
          false
      else (
        let large = per_node shape 100_000 in
        check
          (Printf.sprintf
             "to_binary is linear on %s (%.1f words per node at n=1000, %.1f at n=100000)"
             name
             small
             large)
          (large <= small +. 0.5)))
    [ "a star", star; ("a chain", fun n -> T1 (0, chain n)) ]
;;

(* ------------------------------------ Exercise 5.8(b): pairing heaps on binary trees *)

(* "Reimplement pairing heaps using this new representation": the child-sibling encoding,
   where a node's left field is its leftmost child and its right field the sibling to its
   right, so that the right field of the root is always E. None of that is visible through
   HEAP, and none of it needs to be. The encoding changes the shape in memory and nothing
   else, so this heap owes exactly what the multiway one owes -- the same contract, the
   same O(1) insert and merge, the same linear delete_min on the star, the same O(log n)
   over sequences -- and one thing more. A faithful transcription performs the same merges
   as the original, and every merge is one comparison, so on any sequence the two versions
   compare exactly as often. That is the check that sees the encoding from outside: a
   merge that recurses down a spine, or a delete_min that skips the pairing pass, cannot
   match the count. *)

module Binary_pairing = BinaryPairingHeap (Counting_int)
module Binary_pairing_contract = Heap_tests (Binary_pairing)
module Binary_pairing_checks = Pairing_tests (Binary_pairing)

let test_binary_pairing () =
  section "BinaryPairingHeap (Exercise 5.8b)";
  let before = !failures in
  Binary_pairing_contract.run_contract "BinaryPairingHeap";
  (* The same heap in two shapes. *)
  Random.init 20261001;
  let disagree = ref 0 in
  for _ = 0 to 299 do
    let xs = List.init (Random.int 60) (fun _ -> Random.int 30) in
    match Binary_pairing_contract.drain (Binary_pairing_contract.of_list xs) with
    | got ->
      if got <> Pairing_contract.drain (Pairing_contract.of_list xs) then incr disagree
    | exception Failure _ -> incr disagree
  done;
  check_int
    "BinaryPairingHeap and PairingHeap drain identically, 300 random lists"
    ~expect:0
    ~actual:!disagree;
  let contract_holds = !failures = before in
  (* And the same merges: the two functors build their sequences from the same seeds, so
     pairing them up compares like with like. This pins the transcription to the multiway
     version's merge order and tie-breaking; a heap that is correct but merges in another
     order is reported here, with the two counts. *)
  let bad =
    List.filter_map
      (fun ((name, _, multiway), (_, _, binary)) ->
        match count_only (multiway 1_000), count_only (binary 1_000) with
        | m, b when m = b -> None
        | m, b -> Some (name, m, b)
        | exception Failure _ -> Some (name, 0, -1))
      (List.combine Pairing_checks.sequences Binary_pairing_checks.sequences)
  in
  check
    (Printf.sprintf
       "BinaryPairingHeap performs exactly the multiway version's comparisons, sequence \
        by sequence%s"
       (first_of
          (fun (name, m, b) ->
            if b < 0
            then Printf.sprintf "%s: raised" name
            else Printf.sprintf "%s: %d against %d" name b m)
          bad))
    (bad = []);
  if not contract_holds
  then
    Printf.printf
      "  SKIP  BinaryPairingHeap: cost checks -- the contract above does not hold\n"
  else if Binary_pairing_checks.run_amortised "BinaryPairingHeap"
  then Binary_pairing_checks.run_worst_case "BinaryPairingHeap"
  else
    Printf.printf
      "  SKIP  BinaryPairingHeap: worst-case checks -- they build a heap of 100000 \
       elements\n"
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
  run "SplayHeap" test_splay;
  run "SplayHeap.sort" test_splay_sort;
  run "PairingHeap" test_pairing;
  run "to_binary" test_to_binary;
  run "BinaryPairingHeap" test_binary_pairing;
  Printf.printf "\n%d checks, %d failures\n\n" !checks !failures;
  if !failures > 0 then exit 1
;;
