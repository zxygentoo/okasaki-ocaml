(* Tests for Chapter 11: the queue of Figure 11.1 (section 11.1), its lookup and update
   of Exercise 11.1 and the deque of Exercise 11.2, each with its own preamble below. Alcotest cases written in the checks of harness.ml, as in the earlier
   chapters. *)

open Okasaki.Ch11
open Harness

(* -------------------------------------------------- ImplicitQueue (Figure 11.1) *)

(* Section 11.1 rebuilds the queue on the non-uniform type of Section 10.1.2: a queue is
   shallow, a digit of none or one element, or deep, a front digit, a suspended middle
   queue of pairs and a rear digit. The front of a deep queue holds one or two elements,
   so head reads it where it lies; the rear none or one, so a snoc onto a rear of one
   pairs the two and snocs the pair onto the middle, suspended; and a tail from a front of
   one forces the middle and borrows its head pair, suspending the middle's own tail. On
   their own snoc is the increment of the lazy binary numbers of Section 9.2.3 and tail
   the decrement of the zeroless ones; Theorem 11.1 adds their debit allowances, one
   debit on the middle for a front of two and one less for a rear of one, and has snoc
   and tail run in O(1) amortised time, by the banker's method and so persistently as
   well, head being O(1) outright.

   The contract, the sequences and the traces are those of the queues of Chapters 6 and
   10, from queues.ml, under Chapter 6's budget of 48 words an operation, with head
   checked to allocate nothing at every version of a build of 100000 and its drain, read
   as each version is made. The traces' guard is Chapter 6's with a lower floor: this
   queue has no reverse, and its dearest tail is the figure's own choice of how much to
   put off. n snocs leave a chain of n/2 suspended snocs, each middle wrapping the one
   before it, and the second tail of the drain forces it all, a linear amount of work
   paid for by the snocs; a queue that forced a little more eagerly would put off less
   and meet the same bound, so the guard asks only for a few words a level, enough to
   show the clock sees the work at all. What the traces do not reach is the branch point
   of a snoc, which Chapter 6's queues never needed, a snoc of theirs doing no work: here
   it is the snoc that would carry through every level, were the carries not suspended,
   and it is taken ten thousand times over from its version of a build of 2^17. Measured:
   the sequences 2 to 21 words an operation at either size; the drain's second tail 6240
   words at n = 1000, the other 9999 tails of its version 14 words each; the random
   trace 9; and the dearest snoc of the build 13 words, every time it is taken. *)

let implicit_words =
  { Queues.amortised_words with
    reverse_floor = (fun n -> 4.0 *. log2 n)
  ; dear_work = "does the work the build put off"
  }
;;

(* The checks of an implicit queue, Figure 11.1's or one built on it. *)
module Implicit_tests (Q : Okasaki.Ch5.QUEUE) = struct
  include Queues.Amortised (Q)

  (* The dearest snoc of a build of n, taken d times over from the version it was made
     from. *)
  let run_snoc_branch bound name =
    let n = 1 lsl 17
    and d = 10_000 in
    let q = ref Q.empty
    and dear = ref (0, 0.0, Q.empty) in
    for i = 1 to n do
      let q', c = cost_on bound.Queues.clock (fun () -> Q.snoc !q i) in
      let _, c', _ = !dear in
      if c > c' then dear := i, c, !q;
      q := q'
    done;
    let k, c, v = !dear in
    let _, rest =
      cost_on bound.clock (fun () ->
        for i = 1 to d do
          ignore (Sys.opaque_identity (Q.snoc v i))
        done)
    in
    let ops = { Queues.snocs = d; tails = 0; heads = 0 } in
    check
      (Printf.sprintf
         "%s: the dearest snoc of a build of %d, #%d at %.0f %s, taken %d times over \
          from its version: %s"
         name
         n
         k
         c
         bound.units
         d
         (bound.show ops rest))
      (rest <= bound.budget ops)
  ;;

  let run bound name =
    run_contract name;
    run_sequences bound name;
    run_head name;
    run_traces bound (name ^ ", persistently");
    run_snoc_branch bound (name ^ ", persistently")
  ;;
end

module Implicit = Implicit_tests (ImplicitQueue)

let test_implicit () = Implicit.run implicit_words "ImplicitQueue"
(* ---------------------------------- ImplicitQueueWithLookupAndUpdate (Exercise 11.1) *)

(* Exercise 11.1 adds lookup and update to Figure 11.1's queue, in O(log i) amortised
   time for index i, with the hint of a size field. The queue keeps its elements in
   order: the front digit, then the middle, pairs of the elements behind it, then the
   rear digit; a deep node that knows its own size, outside the suspension, knows how many
   pairs its middle holds without forcing it, and so whether an index is in the front, the
   middle or the rear. In the middle the index halves and its parity picks the half of
   the pair, as in Figure 10.1; and since the front digits of successive levels hold one
   or two elements, then pairs, then pairs of pairs, an index i is reached within about
   log i levels, whatever the length of the queue. update passes a function down, the
   other half of a pair being needed to rebuild it, and may leave its work on the middle
   suspended.

   The queue is still Figure 11.1's, so first all of its checks, under the same budget.
   Then lookup and update against a list model, on every queue of up to 70 elements that
   n snocs make, n snocs and then k tails, and a random history of snocs and tails: every
   index read, every index updated and the result read back whole, the queue it was
   updated from still as it was, a snoc and a tail after the update agreeing too, and
   -1, n and n + 1 refused with each function's own Failure. Then the claim, in its two
   halves. The clock cannot see lookup, which allocates nothing on a queue whose middles
   are forced, so lookup goes on the stopwatch: a million lookups of index 5 against a
   queue of 16 and of 2^20, limit twice as long, with the middle index of the two as the
   guard that the stopwatch sees a walk grow. update allocates at once only its own top
   level, so it is read with a lookup of the same index after it, which forces what it
   put off: for every index of queues of 2^10 and 2^17, at most 32 words a level, log
   (i + 1) + 1 of them, and for indices up to 1000, the same words at either length.
   Measured: the same stopwatch at 0.9 times and 8 times; an update and a lookup 12 words
   at index 0, 35 at 5, 127 at 100 and 196 at 1000 at both lengths, the dearest some 21 a
   level. *)

module Indexed_queue = ImplicitQueueWithLookupAndUpdate
module Indexed = Implicit_tests (Indexed_queue)

(* The queues a history makes, with the list it should hold: n snocs, then k tails of
   them, and a random history of snocs and tails left at n elements. *)
let indexed_histories n =
  let build n = List.fold_left Indexed_queue.snoc Indexed_queue.empty (upto n) in
  let rec tails k (q, xs) =
    if k = 0 then q, xs else tails (k - 1) (Indexed_queue.tail q, List.tl xs)
  in
  let random () =
    let q = ref Indexed_queue.empty
    and xs = ref []
    and next = ref 0 in
    while List.length !xs < n || Random.int 4 = 0 do
      if !xs <> [] && Random.int 3 = 0
      then (
        q := Indexed_queue.tail !q;
        xs := List.tl !xs)
      else (
        q := Indexed_queue.snoc !q !next;
        xs := !xs @ [ !next ];
        incr next)
    done;
    while List.length !xs > n do
      q := Indexed_queue.tail !q;
      xs := List.tl !xs
    done;
    !q, !xs
  in
  let full = build n, upto n in
  ((Printf.sprintf "%d snocs" n, full)
   :: List.map
        (fun k ->
           ( Printf.sprintf "%d snocs and %d tails" (n + k) k
           , tails k (build (n + k), upto (n + k)) ))
        [ 1; 2; 5 ])
  @ [ Printf.sprintf "a random history left at %d" n, random () ]
;;

let test_indexed_contract name =
  let t label = Printf.sprintf "%s: %s" name label in
  Random.init 20261015;
  let histories = List.concat_map indexed_histories (upto 71) in
  let read q n = List.init n (fun i -> Indexed_queue.lookup i q) in
  all_of
    (t
       "lookup reads every index of every queue of up to 70 elements, after n snocs, k \
        more tails, or a random history")
    (fun note ->
       List.iter
         (fun (how, (q, xs)) ->
            match read q (List.length xs) with
            | ys when ys = xs -> ()
            | ys -> note (Printf.sprintf "%s: read %s" how (string_of_int_list ys))
            | exception e ->
              note (Printf.sprintf "%s: raised %s" how (Printexc.to_string e)))
         histories);
  all_of
    (t
       "and update writes every index, the result read back whole, the queue updated \
        from as it was, and a snoc and a tail after it agreeing")
    (fun note ->
       List.iter
         (fun (how, (q, xs)) ->
            List.iteri
              (fun i _ ->
                 let xs' = List.mapi (fun j x -> if j = i then -1 else x) xs in
                 match Indexed_queue.update i (-1) q with
                 | q' ->
                   if Indexed.drain q' <> xs'
                   then note (Printf.sprintf "%s: update %d read back wrong" how i)
                   else if read q' (List.length xs) <> xs'
                   then note (Printf.sprintf "%s: update %d looked up wrong" how i)
                   else if Indexed.drain q <> xs
                   then
                     note (Printf.sprintf "%s: update %d changed the queue updated" how i)
                   else if
                     Indexed.drain (Indexed_queue.tail (Indexed_queue.snoc q' 99))
                     <> List.tl xs' @ [ 99 ]
                   then
                     note
                       (Printf.sprintf
                          "%s: update %d, then a snoc and a tail, wrong"
                          how
                          i)
                 | exception e ->
                   note
                     (Printf.sprintf
                        "%s: update %d raised %s"
                        how
                        i
                        (Printexc.to_string e)))
              xs)
         histories);
  all_of
    (t
       "and -1, n and n + 1 are refused, lookup with Failure \"lookup: not found\" and \
        update with Failure \"update: not found\"")
    (fun note ->
       List.iter
         (fun (how, (q, xs)) ->
            List.iter
              (fun i ->
                 Rlists.refused
                   note
                   (Printf.sprintf "%s: lookup %d" how i)
                   "lookup: not found"
                   (fun () -> Indexed_queue.lookup i q);
                 Rlists.refused
                   note
                   (Printf.sprintf "%s: update %d" how i)
                   "update: not found"
                   (fun () -> Indexed_queue.update i 0 q))
              [ -1; List.length xs; List.length xs + 1 ])
         histories)
;;

(* At most this many words a level for an update and the lookup that forces it. *)
let per_level = 32.0
let levels i = log2 (i + 1) +. 1.0

(* n snocs, every index of them then read once, so that no suspension is left. *)
let forced n =
  let q = List.fold_left Indexed_queue.snoc Indexed_queue.empty (upto n) in
  List.iter (fun i -> ignore (Indexed_queue.lookup i q)) (upto n);
  q
;;

let update_then_lookup q i =
  cost (fun () -> Indexed_queue.lookup i (Indexed_queue.update i (-1) q))
;;

let test_indexed_costs name =
  let t label = Printf.sprintf "%s: %s" name label in
  let small = forced (1 lsl 10)
  and large = forced (1 lsl 17) in
  List.iter
    (fun (n, q) ->
       let worst = ref (0.0, 0, 0.0) in
       for i = 0 to n - 1 do
         let _, c = update_then_lookup q i in
         let r, _, _ = !worst in
         if c /. levels i > r then worst := c /. levels i, i, c
       done;
       let r, i, c = !worst in
       check
         (t
            (Printf.sprintf
               "an update of each index of %d, and the lookup that forces it, within \
                %.0f words a level, log (i + 1) + 1 levels: the dearest is index %d, \
                %.0f words, %.1f a level"
               n
               per_level
               i
               c
               r))
         (r <= per_level))
    [ 1 lsl 10, small; 1 lsl 17, large ];
  let differ =
    List.filter
      (fun i -> snd (update_then_lookup small i) <> snd (update_then_lookup large i))
      (upto 1001)
  in
  check
    (t
       (Printf.sprintf
          "and for every index up to 1000 the same words at %d elements and at %d%s"
          (1 lsl 10)
          (1 lsl 17)
          (match differ with
           | [] -> ""
           | i :: _ -> Printf.sprintf " -- not at index %d" i)))
    (differ = [])
;;

(* Processor time for a million lookups, the best of three, after one that forces what
   the walk needs. *)
let lookup_stopwatch q i =
  ignore (Indexed_queue.lookup i q);
  let once () =
    let started = Sys.time () in
    for _ = 1 to 1_000_000 do
      ignore (Sys.opaque_identity (Indexed_queue.lookup i q))
    done;
    Sys.time () -. started
  in
  min (once ()) (min (once ()) (once ()))
;;

let lookup_growth_limit = 2.0

let test_indexed_stopwatch name =
  let build n = List.fold_left Indexed_queue.snoc Indexed_queue.empty (upto n) in
  let small = build 16
  and large = build (1 lsl 20) in
  let guard = lookup_stopwatch large (1 lsl 19) /. lookup_stopwatch small 8 in
  check
    (Printf.sprintf
       "guard: the same stopwatch sees %s's lookup of the middle index grow with the \
        length, %.1f times as long at 2^20 as at 16"
       name
       guard)
    (guard > lookup_growth_limit);
  let r = lookup_stopwatch large 5 /. lookup_stopwatch small 5 in
  check
    (Printf.sprintf
       "%s: lookup 5 takes %.1f times as long at 2^20 elements as at 16, limit %.1f"
       name
       r
       lookup_growth_limit)
    (r <= lookup_growth_limit)
;;

let test_indexed () =
  let name = "ImplicitQueueWithLookupAndUpdate" in
  Indexed.run implicit_words name;
  test_indexed_contract name;
  test_indexed_costs name;
  test_indexed_stopwatch name
;;

(* --------------------------------------------------- ImplicitDeque (Exercise 11.2) *)

(* Exercise 11.2 asks for deques by the techniques of the section. Both ends now add and
   remove, which is the last row of p.172's table: each digit of a deep node is ONE, TWO
   or THREE, ZERO being left to the empty deque. TWO is the safe digit, a step from either
   edge: an insertion onto a THREE keeps the new element and one old one and sends the
   other two into the middle as a pair, cons at the front and snoc at the back; a removal
   from a ONE borrows a pair from the middle, its head and tail at the front and its last
   and init at the back; and either leaves the digit at TWO. A shallow deque holds up to
   three elements, a fourth making it deep. These are Section 9.2.3's redundant binary
   numbers, one at each end, under Theorem 11.1's argument, and every operation is O(1)
   amortised, head and last O(1) outright.

   So the checks are Figure 11.1's twice over, once on the deque as a queue, snoc at the
   back and head and tail at the front, and once on its mirror, cons at the front read as
   a snoc, last and init as head and tail: the contract, the sequences, head allocating
   nothing, the traces and the branch point of an insertion, at each end. The mirror
   reports the deque's own refusals in the queue's words, so Chapter 5's deque contract
   comes next, with last and init refusing as "last: empty queue" and "init: empty queue".
   Then what neither direction sees alone, both ends at once: a stack at each end, an
   insertion and a removal at the same end alternating on a digit's edge, and a random
   mix of all six operations, at 1000 and 100000 under the same 48 words an operation;
   a stack worked at its edge, 64 rounds of an insertion and a removal at one end from
   every version of a build by that end, where digits of only ONE and TWO would push and
   borrow a level further down at every step; and a random trace of 100000 of the six,
   each on a random earlier version. Measured: the
   sequences 2 to 25 words an operation in either direction; the drain's dearest removal
   some 7450 words at n = 1000 from either end, the build's chain of pairs forced, and 14
   a time for the other 9999 from its version; the dearest insertion 16 words at either
   end, every time it is taken; the stacks 23, the alternations 8 and 9, the random mix
   of six 8; the stack at its edge 7.5 from its dearest version, where a front of ONE
   and TWO only comes to 138; and the persistent trace of six 3.5. *)

(* The deque read from the back: its cons a snoc, its last a head and its init a tail,
   refusing in a queue's words. *)
module Mirror (D : Okasaki.Ch5.DEQUE) : Okasaki.Ch5.QUEUE = struct
  type 'a queue = 'a D.queue

  let empty = D.empty
  let is_empty = D.is_empty
  let snoc q x = D.cons x q

  let head q =
    try D.last q with
    | Failure _ -> failwith "head: empty queue"
  ;;

  let tail q =
    try D.init q with
    | Failure _ -> failwith "tail: empty queue"
  ;;
end

module Deque_forward = Implicit_tests (ImplicitDeque)
module Deque_mirrored = Implicit_tests (Mirror (ImplicitDeque))

module Deque_contract =
  Queues.Deque_contract
    (ImplicitDeque)
    (struct
      let refused name op f = check_failure name (op ^ ": empty queue") f
      let seed = 20261015
    end)

(* Sequences of the six operations, each reporting how many it ran. *)
module D = ImplicitDeque

let opaque x = ignore (Sys.opaque_identity x)

let cons_then_tail n () =
  let q = ref D.empty in
  for i = 1 to n do
    q := D.cons i !q
  done;
  for _ = 1 to n do
    q := D.tail !q
  done;
  opaque !q;
  2 * n
;;

let snoc_then_init n () =
  let q = ref D.empty in
  for i = 1 to n do
    q := D.snoc !q i
  done;
  for _ = 1 to n do
    q := D.init !q
  done;
  opaque !q;
  2 * n
;;

(* An insertion and a removal at one end, alternating, from each fill a digit can have
   there, so that the pair crosses each digit edge. *)
let same_end_alternating ~insert ~remove n () =
  let q = ref D.empty in
  for i = 1 to n do
    q := insert !q i;
    q := insert !q i;
    q := remove !q
  done;
  for _ = 1 to n do
    q := insert !q 0;
    q := remove !q
  done;
  opaque !q;
  5 * n
;;

let random_six n =
  Random.init 20261015;
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
    n
;;

let deque_sequences =
  [ "n conses then n tails, a stack at the front", cons_then_tail
  ; "n snocs then n inits, a stack at the back", snoc_then_init
  ; ( "two conses and a tail, then a cons and a tail, alternating at the front"
    , same_end_alternating ~insert:(fun q x -> D.cons x q) ~remove:D.tail )
  ; ( "two snocs and an init, then a snoc and an init, alternating at the back"
    , same_end_alternating ~insert:D.snoc ~remove:D.init )
  ; "a random mix of all six operations", random_six
  ]
;;

let per_op c ops = c /. float_of_int ops

let test_deque_sequences name =
  List.iter
    (fun (sequence, driver) ->
       let within label n =
         let ops, c = cost (driver n) in
         check
           (Printf.sprintf
              "%s: %s, %s: %.2f words per operation at n=%d"
              name
              sequence
              label
              (per_op c ops)
              n)
           (c <= Queues.constant *. float_of_int ops)
       in
       within "amortised O(1)" 1_000;
       within "amortised O(1), a hundred times longer" 100_000)
    deque_sequences
;;

(* n of the six operations, each applied to a version chosen at random among all built so
   far, an empty one only ever given an insertion. *)
let test_deque_random_trace name =
  let n = 100_000 in
  Random.init 20261016;
  let from = Array.init n (fun i -> Random.int (i + 1)) in
  let op = Array.init n (fun _ -> Random.int 6) in
  let v = Array.make (n + 1) D.empty in
  let _, c =
    cost (fun () ->
      let sum = ref 0 in
      for i = 1 to n do
        let q = v.(from.(i - 1)) in
        v.(i)
        <- (match if D.is_empty q then op.(i - 1) land 1 else op.(i - 1) with
            | 0 -> D.cons i q
            | 1 -> D.snoc q i
            | 2 -> D.tail q
            | 3 -> D.init q
            | 4 ->
              sum := !sum + D.head q;
              q
            | _ ->
              sum := !sum + D.last q;
              q)
      done;
      opaque !sum;
      v)
  in
  check
    (Printf.sprintf
       "%s, persistently: a random trace of %d of the six operations, each on a random \
        earlier version: %.2f words per operation"
       name
       n
       (per_op c n))
    (c <= Queues.constant *. float_of_int n)
;;

(* A stack worked at its edge: from every version of a build of n by one end's insertion,
   64 rounds of an insertion and a removal at that end, each round carrying on from the
   last. One run from each version goes unmeasured first, so that what the build put off
   is not charged to it. The dearest version's run. *)
let test_deque_stack_edges name =
  let n = 2_000
  and rounds = 64 in
  List.iter
    (fun (which, insert, remove) ->
       let v = Array.make (n + 1) D.empty in
       for i = 1 to n do
         v.(i) <- insert v.(i - 1) i
       done;
       let worst = ref (0, 0.0) in
       Array.iteri
         (fun k q ->
            let run () =
              let q = ref q in
              for i = 1 to rounds do
                q := remove (insert !q i)
              done;
              opaque !q
            in
            run ();
            let _, c = cost run in
            if c > snd !worst then worst := k, c)
         v;
       let k, c = !worst in
       check
         (Printf.sprintf
            "%s: %s, %d rounds from each version of a build of %d, dearest from #%d: \
             %.2f words per operation"
            name
            which
            rounds
            n
            k
            (per_op c (2 * rounds)))
         (c <= Queues.constant *. float_of_int (2 * rounds)))
    [ "a cons and a tail at the front", (fun q x -> D.cons x q), D.tail
    ; "a snoc and an init at the back", D.snoc, D.init
    ]
;;

let test_deque () =
  let name = "ImplicitDeque" in
  Deque_forward.run implicit_words name;
  Deque_mirrored.run implicit_words (name ^ ", mirrored");
  Deque_contract.run_contract name;
  test_deque_sequences name;
  test_deque_stack_edges name;
  test_deque_random_trace name
;;

let tests =
  [ case "[Figure 11.1] ImplicitQueue" test_implicit
  ; case "[Exercise 11.1] ImplicitQueueWithLookupAndUpdate" test_indexed
  ; case "[Exercise 11.2] ImplicitDeque" test_deque
  ]
;;
