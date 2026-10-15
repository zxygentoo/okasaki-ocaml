(* Tests for Chapter 11: the queue of Figure 11.1 (section 11.1), with its own preamble
   below. Alcotest cases written in the checks of harness.ml, as in the earlier
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

module Implicit = struct
  include Queues.Amortised (ImplicitQueue)

  (* The dearest snoc of a build of n, taken d times over from the version it was made
     from. *)
  let run_snoc_branch bound name =
    let n = 1 lsl 17
    and d = 10_000 in
    let q = ref ImplicitQueue.empty
    and dear = ref (0, 0.0, ImplicitQueue.empty) in
    for i = 1 to n do
      let q', c = cost_on bound.Queues.clock (fun () -> ImplicitQueue.snoc !q i) in
      let _, c', _ = !dear in
      if c > c' then dear := i, c, !q;
      q := q'
    done;
    let k, c, v = !dear in
    let _, rest =
      cost_on bound.clock (fun () ->
        for i = 1 to d do
          ignore (Sys.opaque_identity (ImplicitQueue.snoc v i))
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
end

let test_implicit () =
  let name = "ImplicitQueue" in
  Implicit.run_contract name;
  Implicit.run_sequences implicit_words name;
  Implicit.run_head name;
  Implicit.run_traces implicit_words (name ^ ", persistently");
  Implicit.run_snoc_branch implicit_words (name ^ ", persistently")
;;

let tests = [ case "[Figure 11.1] ImplicitQueue" test_implicit ]
