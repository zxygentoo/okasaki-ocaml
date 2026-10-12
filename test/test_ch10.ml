(* Tests for Chapter 10: the binary random-access list of Figure 10.1 (section 10.1.2)
   and its lazy form of Exercise 10.2, each with its own preamble below. Alcotest cases
   written in the checks of harness.ml, as in the earlier chapters. *)

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

let tests =
  [ case "[Figure 10.1] AltBinaryRandomAccessListFigure" test_alt
  ; case "[Exercise 10.2] AltBinaryRandomAccessList" test_alt_lazy
  ]
;;
