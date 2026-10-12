(* Tests for Chapter 10: the binary random-access list of Figure 10.1 (section 10.1.2),
   with its own preamble below. Alcotest cases written in the checks of harness.ml, as in
   the earlier chapters. *)

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

let tests = [ case "[Figure 10.1] AltBinaryRandomAccessListFigure" test_alt ]
