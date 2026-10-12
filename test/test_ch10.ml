(* Tests for Chapter 10: the binary random-access list of Figure 10.1 (section 10.1.2),
   its lazy form of Exercise 10.2, and the bootstrapped queue of Figure 10.2 (section
   10.1.3) and its forms without polymorphic recursion of Exercises 10.4 and 10.5, each
   with its own preamble below. Alcotest cases written in the checks of harness.ml, as in the earlier
   chapters. *)

open Okasaki.Ch10
open Harness
open Rlists

(* --------------------------------- AltBinaryRandomAccessList (Figure 10.1) *)

(* Section 10.1.2 writes the list of Figure 9.6 over again as a non-uniform type: a
   sequence of elements is a ONE of an element, or a ZERO, over a sequence of pairs, which
   is over a sequence of pairs of pairs, and so on, a level per digit. The complete leaf
   tree of 2^i elements that the i-th digit of Figure 9.6 held is now a pair nested i deep,
   and what that figure kept as invariants, trees complete and sizes doubling with the
   digit, the type states, so that a function that breaks them does not compile. (The
   figure's own note is that this needs polymorphic recursion, which Standard ML has not
   and OCaml has, given the annotation.) The functions are the same walks down the digits
   read as walks down the levels: cons pairs the new element with a ONE's and carries the
   pair up; uncons reads cons backwards and head and tail are its halves; lookup halves the
   index per level and picks the half of the pair by its parity; and update sends the new
   element down as a function, fupdate, because a level down the element to replace is
   half of a pair that only that level can see. p.144 states the costs, "the functions all
   still run in O(log n) time", and nothing is lazy or amortised, so the contract and the
   clock are those of Figure 9.6, from rlists.ml, with the per-digit budget. Measured, the
   cons that carries through every level costs some 5 words a level, a pair and a ZERO,
   head and tail 6, and update 12, a closure and a ZERO at every level on the way down and
   a pair and a ONE on the way up; a lookup allocates the two words of a ZERO for each ONE
   it passes and nothing else. What the clock cannot see is Exercise 10.1: the update of
   p.145, which fetches the other half of the pair by a lookup at every level, is O(log^2
   n), but at two words a level for the lookups it is well inside the budget too, and the
   exercise is the proof.

   The contract wants little the type does not already give. That a list emptied by tails
   is NIL and not ZERO NIL is uncons's clause for ONE (x, NIL), and is what the check that
   an emptied list is empty again is for. That the transient ZERO ps, which the ONE clauses
   of lookup and fupdate build to recurse on, ends in a refusal and not an assertion is
   what one past the end is for. And the refusal of index -1 at every size is not idle
   here: the figure's div and mod floor, OCaml's / and mod truncate toward zero, so -1 / 2
   is 0, and a negative index that is not refused before the first ZERO lands on the pair
   at index 0 and reads, or writes, its second half. *)

module Alt = Contract (AltBinaryRandomAccessListFigure)

let test_alt () =
  Alt.run_contract "AltBinaryRandomAccessListFigure";
  Alt.run_costs "AltBinaryRandomAccessListFigure"
;;

(* --------------------------------- AltBinaryRandomAccessList (Exercise 10.2) *)

(* Exercise 10.2 asks for the list of Figure 10.1 with cons, head and tail in O(1)
   amortised time, over a type whose digits are ONE, TWO and THREE of elements, each over
   a suspended sequence of pairs. That is Exercise 9.9 over the nested type. A TWO is
   safe, cons and tail both stop at it; a ONE is dangerous for tail and a THREE for cons;
   and the recursive case of each leaves a TWO behind with the level above it suspended,
   where 9.9 suspended the stream, so that section 9.2.3's debit invariant, one debit on a
   TWO and none on a ONE or a THREE, is the proof again. What the type adds is on the way
   down: a THREE's carry pushes a pair up, and a ONE's borrow has to fetch one. The pair
   is the head of the level above, strict in every digit, and the rest of that level is
   what the suspension in the new TWO holds, so a chain of ONEs is walked one level per
   tail, each walk memoised in the version that did it and never done twice for one
   version. lookup and update are Figure 10.1's, forcing each level as they pass it, and
   update strict, so that it refuses an index past the end at the call and leaves no work
   for a later tail to pay; the exercise asks nothing of them, and they are O(log n)
   amortised.

   The behaviour is Contract's, lookup, update and persistence included, and Lite's, the
   two ways of reaching a size and the back and forth over it. The clock for cons, head
   and tail is Lite's amortised one, the same sequences and the same budget as 9.9.
   Measured, the dearest means are some 34 words, a build with its drain and the tails of
   the all-ONEs version, at both sizes. No single operation is held to anything: the
   drain's second tail pays every carry the build put off, six hundred thousand words at 3
   (2^17 - 1), and that is the bound at work. lookup and update have a clock of their own
   below, a mean too, since the first lookup to reach a level pays the carries pending
   there: lookup at every index of a built list, against the per-digit budget, measured
   some 5 words a level; and update at every index of that one version, each read back by
   a lookup at its index, against two digits' worth, since an update over this type builds
   at every level a digit, the closure that carries f up and the suspension it hands on,
   and with the lookup that reads it comes to some 21 words a level. *)

module Alt_lazy = Contract (AltBinaryRandomAccessList)
module Alt_lazy_stack = Lite (AltBinaryRandomAccessList)

(* Two digits' worth a level: an update and the lookup that reads it back. *)
let lazy_update_budget n = 2.0 *. budget n

let test_alt_lazy_index_costs name n =
  let module R = AltBinaryRandomAccessList in
  let t label = Printf.sprintf "%s: %s" name label in
  let within limit label c =
    check
      (t
         (Printf.sprintf
            "%s, %.1f words an operation, n=%d, budget %.0f"
            label
            c
            n
            (limit n)))
      (c <= limit n)
  in
  let full = List.fold_right R.cons (upto n) R.empty in
  within
    budget
    "lookup at every index of a built list"
    (Alt_lazy_stack.mean (fun () ->
       for i = 0 to n - 1 do
         ignore (Sys.opaque_identity (R.lookup i full))
       done;
       n));
  within
    lazy_update_budget
    "update at every index of that one version, each read back by a lookup"
    (Alt_lazy_stack.mean (fun () ->
       for i = 0 to n - 1 do
         ignore (Sys.opaque_identity (R.lookup i (R.update i 0 full)))
       done;
       n))
;;

let test_alt_lazy () =
  let name = "AltBinaryRandomAccessList" in
  Alt_lazy.run_contract name;
  Alt_lazy_stack.run_contract name;
  Alt_lazy_stack.run_costs name;
  test_alt_lazy_index_costs name 1_000;
  test_alt_lazy_index_costs name 100_000
;;

(* ------------------------------------- BootstrappedQueueFigure (Figure 10.2) *)

(* Section 10.1.3 takes the banker's queue of Figure 6.1 apart. Its front stream was f ++
   reverse r1 ++ ... ++ reverse rk, appended left to right, so the elements of f were
   walked once by every ++; here f is a plain list, and the reversed rears are a queue of
   suspended lists, m, in the order they will be wanted. A queue of queues: the first
   decomposition in the chapter that nests the structure itself, ('a list susp) queue
   inside 'a queue, and polymorphic recursion again. lenfm counts f and every list in m,
   the invariant is lenr <= lenfm as in Chapter 6, and f is never empty in a Q, the empty
   queue being its own constructor. checkQ suspends the reverse at the moment Figure 6.1
   did and snocs it onto m; checkF forces the first of m when f runs out, one operation
   before Figure 6.1 would have. p.150: the reverse costs what it cost there, O(1)
   amortised; what is new is that snoc and tail recur into m, a level per nesting, and
   since the lists in m at least double, each level is a logarithm smaller than the one
   before and the depth is O(log* n), five levels needing 2^65536 elements -- "constant in
   practice". The clock is Chapter 6's, moved to queues.ml for the purpose: the contract,
   the sequences, and the traces over the branch points of a drain and of a build, since
   the suspensions here are memoised as Figure 6.1's are and the chapter's argument leans
   on it. The budget is not quite Chapter 6's. Its 48 words an operation was one level's
   worth with room to spare; here a snoc or a tail recurs a level per nesting, the
   recursion plain and so repeated by every future that takes it, and a queue of these
   sizes is nested five deep. Measured, the dearest is a tail from version #126 of a
   build, taken twenty times over, where f runs out at one level after another and each
   moves on to the next list of its m: 102 words. A level's worth for each of the five
   levels leaves room for that, and is nowhere near a reverse run on the spot, which is
   thousands. The sequences come to some 15 words, a build with
   its drain and two snocs to a tail, and under 14 on the drain repeated ten times from
   one queue; the drain of 1000 runs its dearest reverse at tail #511, which is the guard
   inside run_traces. head is O(1) worst-case on top, the first of a list f that is never
   empty: it forces nothing and allocates nothing, and that is checked at every version of
   a build and its drain. The checks are a functor over the queue and the bound, since
   Exercises 10.4 and 10.5 are the same queue over other types and are held to the same
   ones. *)

let bootstrapped_words =
  { Queues.amortised_words with
    claim = "amortised O(log* n)"
  ; budget = (fun ops -> 5.0 *. Queues.constant *. float_of_int (Queues.total ops))
  }
;;

module Bootstrapped (Q : QUEUE) = struct
  include Queues.Amortised (Q)

  let run_head name =
    let n = 100_000 in
    let v = Array.make (2 * n) Q.empty in
    for i = 1 to n do
      v.(i) <- Q.snoc v.(i - 1) i
    done;
    for i = n + 1 to (2 * n) - 1 do
      v.(i) <- Q.tail v.(i - 1)
    done;
    let dear = ref (0, 0.0)
    and sum = ref 0 in
    for i = 1 to (2 * n) - 1 do
      let x, c = cost (fun () -> Q.head v.(i)) in
      sum := !sum + x;
      if c > snd !dear then dear := i, c
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

  let run bound name =
    run_contract name;
    run_sequences bound name;
    run_head name;
    run_traces bound (name ^ ", persistently")
  ;;
end

module Figure = Bootstrapped (BootstrappedQueueFigure)

let test_bootstrapped () = Figure.run bootstrapped_words "BootstrappedQueueFigure"

(* ------------------ BootstrappedQueueNoPolymorphicRecursion (Exercise 10.4) *)

(* Exercise 10.4 asks for the queue of Figure 10.2 without polymorphic recursion, over a
   middle that is an 'a queue and not an 'a list susp queue: the elements of every level
   are of the one type 'a el, an ELEM of an element or a LIST of a suspended list of them,
   so that the level a value belongs to is read off its constructors, ELEMs at the first,
   LISTs of ELEMs at the second and so on, where the figure read it off the type. The
   functions recur at one type and need no annotation; what they need instead is the
   wrapping the figure's types did for free. snoc and head are each two functions, one
   over 'a el that recurs and one over 'a that the signature exports, joined by an ELEM
   on the way in and a match on the way out; checkF opens the LIST at the front of m and
   makes the whole of the list under it the new f, as the figure's force did; and the two
   shapes the types no longer rule out, a LIST at the front of the outer queue and an
   ELEM at the front of an inner one, are assertions. The queue is otherwise the figure's,
   the same rotations at the same moments, so the bound is the figure's and so is the
   clock. The cost is the figure's plus a constructor, two words an element for the ELEM a
   snoc puts on and two a rotation for the LIST: measured, a build with its drain comes to
   16 words an operation where the figure's was 15, and the dearest tail of the traces to
   108 where it was 102. head is the figure's too, the outer f holding ELEMs only, and
   the match that takes the element out of one allocates nothing. *)

module No_poly = Bootstrapped (BootstrappedQueueNoPolymorphicRecursion)

let test_no_poly () =
  No_poly.run bootstrapped_words "BootstrappedQueueNoPolymorphicRecursion"
;;

(* ------------------------------------ BootstrappedQueuePrimQ (Exercise 10.5) *)

(* Exercise 10.5 removes the polymorphic recursion the other way: the middle is a queue of
   some other implementation, PrimQ, so the type 'a list susp PrimQ.queue is not a queue
   of the functor's own and is not recursive at all, and with the recursion gone from the
   type it is gone from the functions, since what the middle's snoc, head and tail cost is
   PrimQ's affair and no function here calls itself. A snoc does at most one PrimQ.snoc,
   the rotation's, and a tail at most one PrimQ.head and one PrimQ.tail, checkF's. Part
   (b) is then Chapter 6's argument with a constant added: the suspended reverse of
   lenfm + 1 elements has lenfm tails to pay for it before checkF forces it, and when
   PrimQ is a real-time queue the one PrimQ operation an operation is O(1) worst-case,
   with no debits of its own to combine with those, so every operation is O(1) amortised.
   That is the claim here, for the two real-time queues of the earlier chapters as PrimQ,
   Figure 7.1's over the streams of Chapter 4 and Figure 8.1's. What the clock can check
   is that the constant is a constant, and whose: a tail does at most three PrimQ
   operations on top of its own, the rotation's snoc and checkF's head and tail, so its
   budget is Chapter 6's constant and three of PrimQ's dearest operation, 24 words for
   the real-time queue by Chapter 7's clock and 54 for Hood-Melville by Chapter 8's.
   Measured, the sequences come to the figure's 15 words an operation with either, and
   the dearest tail of the traces, from the build version whose tail rotates and empties
   f in one go, to 57 with the first and 103 with the second -- the figure's 102, not
   less. At any size a machine holds the figure is five levels deep at most, and O(1)
   against O(log* n) is a difference the clock cannot see; part (b) is for the proof.
   The figure is this functor applied to itself, so it goes through once more with the
   figure's queue as PrimQ and the figure's budget: a level peeled off and the same
   costs under it. *)

(* Chapter 6's constant for this queue's own work and three PrimQ operations' worth on top,
   each at the dearest the earlier chapter measured for that PrimQ. *)
let prim_words prim =
  { Queues.amortised_words with
    budget =
      (fun ops -> (Queues.constant +. (3.0 *. prim)) *. float_of_int (Queues.total ops))
  }
;;

module Prim_real_time =
  Bootstrapped (BootstrappedQueuePrimQ (Okasaki.Ch7.RealTimeQueue (Okasaki.Ch4.Stream)))

module Prim_hood_melville =
  Bootstrapped (BootstrappedQueuePrimQ (Okasaki.Ch8.HoodMelvilleQueue))

module Prim_figure = Bootstrapped (BootstrappedQueuePrimQ (BootstrappedQueueFigure))

let test_prim () =
  Prim_real_time.run (prim_words 24.0) "BootstrappedQueuePrimQ (RealTimeQueue)";
  Prim_hood_melville.run (prim_words 54.0) "BootstrappedQueuePrimQ (HoodMelvilleQueue)";
  Prim_figure.run bootstrapped_words "BootstrappedQueuePrimQ (BootstrappedQueueFigure)"
;;

let tests =
  [ case "[Figure 10.1] AltBinaryRandomAccessListFigure" test_alt
  ; case "[Exercise 10.2] AltBinaryRandomAccessList" test_alt_lazy
  ; case "[Figure 10.2] BootstrappedQueueFigure" test_bootstrapped
  ; case "[Exercise 10.4] BootstrappedQueueNoPolymorphicRecursion" test_no_poly
  ; case "[Exercise 10.5] BootstrappedQueuePrimQ" test_prim
  ]
;;
