(* Tests for Chapter 10: the binary random-access list of Figure 10.1 (section 10.1.2),
   its lazy form of Exercise 10.2, and the bootstrapped queue of Figure 10.2 (section
   10.1.3) and its forms without polymorphic recursion of Exercises 10.4 and 10.5, and
   the catenable list of Figure 10.6 (section 10.2.1) and its flatten of Exercise 10.6,
   the bootstrapped heap of Figure 10.7 (section 10.2.2), the heaps with info of
   Exercise 10.8, and the trie of Figure 10.10 (section 10.3.1), its prefix-free form of
   Exercise 10.9 and its path-compressed form of Exercise 10.10, and the hash table of
   Exercise 10.11, each with its own preamble below. Alcotest cases written in the
   checks of harness.ml, as in the earlier chapters. *)

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

(* ------------------------------------------------ CatenableList (Figure 10.6) *)

(* Section 10.2 is the other kind of bootstrapping, structural abstraction: a collection
   whose elements are collections, to get the join that single-element insertion does not
   give. The catenable list of Figure 10.3's signature, cons, snoc, ++, head and tail, is
   Figure 10.6: a tree whose node holds an element and whose children sit in a queue of
   suspended trees, the elements in preorder, over any persistent queue Q. ++ makes the
   second list the last child of the first, one Q.snoc; tail discards the root and links
   the children right to left, foldr over the queue, every link but the outermost
   suspended, so that a tail pays for one link and leaves the rest to the tails that
   want them. head is O(1) worst-case; p.156 proves ++, and with it cons and snoc, and
   tail O(1) amortised by the banker's method under the left-linear debit invariant,
   Theorem 10.1, ++ discharging one debit and tail three, persistence included. Of Q the
   book asks only that it be persistent and constant-time, "whether amortized or
   worst-case": here it is Exercise 10.5's bootstrapped queue over the real-time queue,
   and then Chapter 6's banker's queue, and the batched queue of Chapter 5 stands guard
   below as the one that is not persistent.

   The contract builds a list four ways, by cons, by snoc, as the fat tree, singletons
   ++'d left to right so that the root has every other element for a child, and as the
   chain, ++'d right to left so that every node has one; drains each; takes ++ at every
   pair of sizes up to six across the four; checks the two bracketings of a triple;
   that a version is unchanged by what is done to it; that xs ++ xs squared ten times is
   1024 copies of xs over one shared tree; and a random trace of cons, snoc, ++, tail and
   head over random earlier versions, every version against a list model. The clocks are
   means, as for every lazy structure: five sequences from empty at a thousand and a
   hundred thousand, and then persistently, each operation twenty times over from every
   version of a drain of the fat tree of a thousand, where a tail has the most children
   to link; the squared list drained; and a random trace over earlier versions. head is
   held to allocating nothing. One constant serves every clock, twice the dearest
   measured, which is the drain of the squared list at 63 words a tail over the
   bootstrapped queue and 52 over the banker's; the sequences come to between 7 and 31,
   the chain and the snocs, and the repeated tail to 35 and 43. The clocks see what the
   section argues: the book's first linkAll, with nothing suspended, costs 25000 words a
   tail repeated from the root version, the fat tree linked over again every time; and
   linking left to right, the order the book says duplicates the most work, makes a
   drain quadratic, 8000 words an operation at a thousand. *)

let cat_constant = 128.0

module Cat (C : CATENABLE_LIST) = struct
  let ( ++ ) = C.( ++ )
  let to_list xs = drain_with ~is_empty:C.is_empty ~head:C.head ~tail:C.tail xs
  let by_cons l = List.fold_right C.cons l C.empty
  let by_snoc l = List.fold_left C.snoc C.empty l
  let singleton x = C.cons x C.empty

  (* ((s0 ++ s1) ++ s2) ++ ...: one root with every other element a child of it. *)
  let fat_of l = List.fold_left (fun acc x -> acc ++ singleton x) C.empty l

  (* s0 ++ (s1 ++ (s2 ++ ...)): a chain, every node with one child. *)
  let chain_of l = List.fold_right (fun x acc -> singleton x ++ acc) l C.empty
  let fat n = fat_of (upto n)
  let chain n = chain_of (upto n)
  let shifted n = List.init n (fun i -> 100 + i)

  (* xs ++ xs, k times over: 2^k copies of one shared tree. *)
  let rec squared k xs = if k = 0 then xs else squared (k - 1) (xs ++ xs)
  let rec copies k l = if k = 0 then [] else l @ copies (k - 1) l

  let builders =
    [ "cons", by_cons; "snoc", by_snoc; "a fat tree", fat_of; "a chain", chain_of ]
  ;;

  let run_contract name =
    let t label = Printf.sprintf "%s: %s" name label in
    check (t "empty is empty") (C.is_empty C.empty);
    check (t "cons makes it non-empty") (not (C.is_empty (C.cons 1 C.empty)));
    check (t "snoc makes it non-empty") (not (C.is_empty (C.snoc C.empty 1)));
    check (t "empty ++ empty is empty") (C.is_empty (C.empty ++ C.empty));
    check_failure (t "head of empty refuses") "head: empty list" (fun () ->
      C.head C.empty);
    check_failure (t "tail of empty refuses") "tail: empty list" (fun () ->
      C.tail C.empty);
    let sizes = [ 0; 1; 2; 3; 7; 100; 1000 ] in
    all_of (t "built every way, drained in order, at every size") (fun note ->
      List.iter
        (fun n ->
           List.iter
             (fun (how, build) ->
                if to_list (build (upto n)) <> upto n
                then note (Printf.sprintf "%d by %s" n how))
             builders)
        sizes);
    all_of
      (t "xs ++ ys is xs then ys, at every pair of sizes up to 6, built every way")
      (fun note ->
         for a = 0 to 6 do
           for b = 0 to 6 do
             let l1 = upto a
             and l2 = shifted b in
             List.iter
               (fun (h1, b1) ->
                  List.iter
                    (fun (h2, b2) ->
                       if to_list (b1 l1 ++ b2 l2) <> l1 @ l2
                       then note (Printf.sprintf "%d by %s ++ %d by %s" a h1 b h2))
                    builders)
               builders
           done
         done);
    all_of (t "++ is associative: both bracketings drain the same") (fun note ->
      List.iter
        (fun (a, b, c) ->
           let l1 = upto a
           and l2 = shifted b
           and l3 = List.init c (fun i -> 200 + i) in
           let xs = by_cons l1
           and ys = fat_of l2
           and zs = chain_of l3 in
           if
             to_list (xs ++ ys ++ zs) <> l1 @ l2 @ l3
             || to_list (xs ++ (ys ++ zs)) <> l1 @ l2 @ l3
           then note (Printf.sprintf "%d, %d, %d" a b c))
        [ 0, 0, 1; 1, 0, 0; 1, 1, 1; 3, 0, 3; 5, 4, 3; 100, 1, 100 ]);
    (* a version is what it was, whatever is done to it afterwards *)
    let xs = fat 10
    and ys = chain_of (shifted 5) in
    let zs = xs ++ ys in
    ignore
      (Sys.opaque_identity
         (to_list (C.tail zs), to_list (C.tail xs), C.cons 7 ys, C.snoc zs 8));
    check
      (t "xs, ys and xs ++ ys are what they were after a tail, a cons and a snoc on them")
      (to_list xs = upto 10 && to_list ys = shifted 5 && to_list zs = upto 10 @ shifted 5);
    check
      (t "xs ++ xs squared ten times is 1024 copies of xs, one tree shared throughout")
      (to_list (squared 10 (by_cons (upto 10))) = copies 1024 (upto 10));
    (* a random trace over earlier versions, every version against a list model *)
    let steps = 600
    and cap = 2_000 in
    let v = Array.make (steps + 1) (C.empty, []) in
    Random.init 20261013;
    all_of
      (t
         (Printf.sprintf
            "a random trace of %d cons, snoc, ++, tail and head on random earlier \
             versions, every version against a list model"
            steps))
      (fun note ->
         for i = 1 to steps do
           let a, la = v.(Random.int i) in
           v.(i)
           <- (match Random.int 5 with
               | 0 -> C.cons i a, i :: la
               | 1 -> C.snoc a i, la @ [ i ]
               | 2 ->
                 let b, lb = v.(Random.int i) in
                 if List.length la + List.length lb > cap then a, la else a ++ b, la @ lb
               | 3 -> if la = [] then a, la else C.tail a, List.tl la
               | _ ->
                 if la <> [] && C.head a <> List.hd la
                 then note (Printf.sprintf "head at step %d" i);
                 a, la)
         done;
         Array.iteri
           (fun i (c, l) -> if to_list c <> l then note (Printf.sprintf "version #%d" i))
           v)
  ;;

  (* ------------------------------------------- sequences: one thread, from empty *)

  (* Each driver returns the number of operations it did. *)
  let drain n xs =
    for _ = 1 to n do
      xs := C.tail !xs
    done
  ;;

  let sequences n =
    [ ( "cons n then n tails"
      , fun () ->
          let xs = ref C.empty in
          for i = 1 to n do
            xs := C.cons i !xs
          done;
          drain n xs;
          ignore (Sys.opaque_identity !xs);
          2 * n )
    ; ( "snoc n then n tails"
      , fun () ->
          let xs = ref C.empty in
          for i = 1 to n do
            xs := C.snoc !xs i
          done;
          drain n xs;
          ignore (Sys.opaque_identity !xs);
          2 * n )
    ; ( "n singletons ++ left to right, the fat tree, then n tails"
      , fun () ->
          let xs = ref C.empty in
          for i = 1 to n do
            xs := !xs ++ singleton i
          done;
          drain n xs;
          ignore (Sys.opaque_identity !xs);
          3 * n )
    ; ( "n singletons ++ right to left, the chain, then n tails"
      , fun () ->
          let xs = ref C.empty in
          for i = n downto 1 do
            xs := singleton i ++ !xs
          done;
          drain n xs;
          ignore (Sys.opaque_identity !xs);
          3 * n )
    ; ( "a random mix of cons, snoc, ++ with a list of three, tail and head"
      , fun () ->
          Random.init 20261014;
          let xs = ref C.empty
          and ops = ref 0
          and sum = ref 0 in
          for i = 1 to n do
            match Random.int 5 with
            | 0 ->
              xs := C.cons i !xs;
              incr ops
            | 1 ->
              xs := C.snoc !xs i;
              incr ops
            | 2 ->
              xs := !xs ++ by_cons [ i; i + 1; i + 2 ];
              ops := !ops + 4
            | 3 ->
              if not (C.is_empty !xs) then xs := C.tail !xs;
              incr ops
            | _ ->
              if not (C.is_empty !xs) then sum := !sum + C.head !xs;
              incr ops
          done;
          ignore (Sys.opaque_identity !xs);
          ignore (Sys.opaque_identity !sum);
          !ops )
    ]
  ;;

  let mean f =
    let ops, c = cost f in
    c /. float_of_int ops
  ;;

  let run_sequences name =
    let t label = Printf.sprintf "%s: %s" name label in
    List.iter
      (fun (label, n, longer) ->
         List.iter
           (fun (sequence, f) ->
              let c = mean f in
              check
                (t
                   (Printf.sprintf
                      "%s, amortised O(1)%s: %.2f words per operation at n=%d"
                      sequence
                      longer
                      c
                      n))
                (c <= cat_constant))
           (sequences n))
      [ "", 1_000, ""; "", 100_000, ", a hundred times longer" ]
  ;;

  (* ---------------------------------------------------- persistence: versions *)

  (* Every version of a drain of the fat tree of n, which is where tail has the most
     children to link. *)
  let fat_versions n =
    let v = Array.make n C.empty in
    v.(0) <- fat n;
    for i = 1 to n - 1 do
      v.(i) <- C.tail v.(i - 1)
    done;
    v
  ;;

  (* An operation whose result is kept from the optimiser and then dropped. *)
  let op f xs = ignore (Sys.opaque_identity (f xs))
  let tail_op = op C.tail

  (* [op] k times over from each version, the dearest version's mean. *)
  let dearest_repeated v k op =
    let dear = ref (0, 0.0) in
    Array.iteri
      (fun i x ->
         let _, c =
           cost (fun () ->
             for _ = 1 to k do
               op x
             done)
         in
         let c = c /. float_of_int k in
         if c > snd !dear then dear := i, c)
      v;
    !dear
  ;;

  let run_versions name =
    let t label = Printf.sprintf "%s, persistently: %s" name label in
    let n = 1_000
    and k = 20 in
    let v = fat_versions n in
    List.iter
      (fun (label, op) ->
         let i, c = dearest_repeated v k op in
         check
           (t
              (Printf.sprintf
                 "%s, %d times over from each version of a drain of the fat tree of %d, \
                  dearest from #%d: %.2f words per operation"
                 label
                 k
                 n
                 i
                 c))
           (c <= cat_constant))
      [ "tail", tail_op
      ; ( "tail then head"
        , op (fun xs ->
            let ys = C.tail xs in
            if C.is_empty ys then 0 else C.head ys) )
      ; "++ a singleton", op (fun xs -> xs ++ singleton 0)
      ; "cons then tail", op (fun xs -> C.tail (C.cons 0 xs))
      ];
    let i, c = dearest_repeated v 1 (op C.head) in
    check
      (t
         (Printf.sprintf
            "head allocates nothing at any version of the drain, dearest #%d at %.0f \
             words"
            i
            c))
      (c = 0.0);
    let xs = squared 10 (by_cons (upto 10)) in
    let c =
      mean (fun () ->
        let xs = ref xs in
        drain 10_240 xs;
        ignore (Sys.opaque_identity !xs);
        10_240)
    in
    check
      (t
         (Printf.sprintf
            "a list squared ten times, 1024 copies of one tree, drained: %.2f words per \
             tail"
            c))
      (c <= cat_constant);
    let steps = 100_000 in
    let v = Array.make (steps + 1) C.empty in
    Random.init 20261015;
    let c =
      mean (fun () ->
        let sum = ref 0 in
        for i = 1 to steps do
          let a = v.(Random.int i) in
          v.(i)
          <- (match Random.int 5 with
              | 0 -> C.cons i a
              | 1 -> C.snoc a i
              | 2 -> a ++ v.(Random.int i)
              | 3 -> if C.is_empty a then a else C.tail a
              | _ ->
                if not (C.is_empty a) then sum := !sum + C.head a;
                a)
        done;
        ignore (Sys.opaque_identity !sum);
        steps)
    in
    check
      (t
         (Printf.sprintf
            "a random trace of %d operations, each on a random earlier version: %.2f \
             words per operation"
            steps
            c))
      (c <= cat_constant)
  ;;

  let run name =
    run_contract name;
    run_sequences name;
    run_versions name
  ;;
end

(* Whether the persistence clock can see anything: the same probe over the batched
   queue, which is not persistent, must find the root's children reversed again by every
   repeat of the tail, three words a child. Without this the checks above could pass on
   a Q that never shares anything. *)
module Cat_batched = Cat (CatenableList (Okasaki.Ch5.BatchedQueue))

let test_cat_guard () =
  let n = 1_000
  and k = 20 in
  let i, c =
    Cat_batched.dearest_repeated (Cat_batched.fat_versions n) k Cat_batched.tail_op
  in
  check
    (Printf.sprintf
       "guard: over the batched queue the same probe sees the children reversed again: \
        tail %d times over from each version of a drain of the fat tree of %d, dearest \
        from #%d at %.0f words"
       k
       n
       i
       c)
    (c >= float_of_int n)
;;

module Cat_bootstrapped =
  Cat
    (CatenableList (BootstrappedQueuePrimQ (Okasaki.Ch7.RealTimeQueue (Okasaki.Ch4.Stream))))

module Cat_bankers = Cat (CatenableList (Okasaki.Ch6.BankersQueue (Okasaki.Ch4.Stream)))

let test_cat () =
  Cat_bootstrapped.run "CatenableList (BootstrappedQueuePrimQ (RealTimeQueue))";
  test_cat_guard ();
  Cat_bankers.run "CatenableList (BankersQueue)"
;;

(* ---------------------------------------------------- flatten (Exercise 10.6) *)

(* Exercise 10.6 wants flatten, the catenation of a list of k catenable lists, in O(1 + e)
   amortised time, e the number of empty lists among the k. A fold of ++ is k links; the
   function has to do what linkAll does and link the first list to a suspension of the
   flattening of the rest, one link and one suspension whatever k is, leaving the rest to
   the tails that get there, each of which forces one level and finds one link to do.
   What cannot be left to the suspension is the empties: a child is a non-empty tree,
   link's clause for E being the assertion (the figure's SML raises Match), and a
   suspension of the flattening of nothing but empties is a suspended E, harmless as the
   last child, which linkAll returns as it is, but the assertion once anything is ++'d
   after it. So the empties are stepped over on the spot, the ones in front of the first
   non-empty list and the ones after each non-empty list before the next, and the last
   non-empty list is returned as it is when only empties follow; those steps are the e of
   the bound, and the suspension is its amortised 1, a last child of the root with the
   unshared cost of one link, which is what Theorem 10.1's invariant leaves room for.

   The contract flattens every list of up to four parts of sizes 0 to 5, each part built
   a different way round the four builders, against List.concat, which puts the empties
   in front, between and behind; then, for every list of up to three parts of sizes 0 to
   2, goes on from the flattened list with ++ on either side, cons, snoc, tail and a
   flatten of it beside itself, since a suspended empty shows only then; that the parts
   are what they were; and a random trace of cons, snoc, flatten of up to four random
   earlier versions, tail and head, every version against a list model. The clocks are
   words, so of the 1 + e they see the 1: the walk past the empties allocates nothing,
   and a flatten of a hundred thousand singletons is held to the one constant with and
   without an empty before each, 19 words over the bootstrapped queue and 38 over the
   banker's, where the fold of ++ is ten words a list; flatten and then one, two and ten
   tails, each forcing one level, is held per operation, which is also what catches a
   flatten that suspends the whole fold, one suspension doing every link when forced;
   then the means of a drain after a flatten of singletons, of lists of ten with an empty
   between, of fat trees and chains of a hundred, and of ten flattens, counting 1 + e for
   the flatten; and persistently, tail twenty times over from every version of a drain
   of the flatten of a thousand singletons, where every version's last child is the
   suspension of the rest, ++ then tail, and a flatten of the version beside itself then
   tailed, which is the dearest at 94 words, two links and their suspensions over the
   bootstrapped queue. The constant is twice that. *)

let flatten_constant = 192.0

module Flatten (C : CATENABLE_LIST_WITH_FLATTEN) = struct
  include Cat (C)

  let flatten = C.flatten

  (* Every list of up to [k] sizes from [sizes]. *)
  let rec shapes k sizes =
    if k = 0
    then [ [] ]
    else
      [] :: List.concat_map (fun s -> List.map (List.cons s) (shapes (k - 1) sizes)) sizes
  ;;

  (* The parts of a shape, the i-th built the i-th way round and over its own numbers,
     with their model. *)
  let parts shape =
    List.mapi
      (fun i n ->
         let l = List.init n (fun j -> (100 * i) + j) in
         snd (List.nth builders (i mod List.length builders)) l, l)
      shape
    |> List.split
  ;;

  let show shape = String.concat "," (List.map string_of_int shape)

  let run_contract name =
    let t label = Printf.sprintf "%s: %s" name label in
    check (t "flatten of nothing is empty") (C.is_empty (flatten []));
    check
      (t "flatten of three empties is empty")
      (C.is_empty (flatten [ C.empty; C.empty; C.empty ]));
    all_of
      (t "every list of up to four parts of sizes 0 to 5, built every way, flattened")
      (fun note ->
         List.iter
           (fun shape ->
              let cats, ls = parts shape in
              if to_list (flatten cats) <> List.concat ls then note (show shape))
           (shapes 4 [ 0; 1; 2; 3; 5 ]));
    let ys = shifted 3
    and ly = List.map (fun i -> 1000 + i) (upto 3) in
    all_of
      (t
         "gone on from, for every list of up to three parts of sizes 0 to 2: ++ on \
          either side, cons, snoc, tail, and a flatten of it beside itself")
      (fun note ->
         List.iter
           (fun shape ->
              let cats, ls = parts shape in
              let xs = flatten cats
              and l = List.concat ls in
              let after =
                [ "++ ys", to_list (xs ++ by_cons ys), l @ ys
                ; "ys ++", to_list (by_cons ys ++ xs), ys @ l
                ; "cons", to_list (C.cons 7 xs), 7 :: l
                ; "snoc", to_list (C.snoc xs 7), l @ [ 7 ]
                ; "tail", (if l = [] then [] else to_list (C.tail xs)), List.drop 1 l
                ; ( "flatten [xs; E; ys; xs]"
                  , to_list (flatten [ xs; C.empty; by_cons ly; xs ])
                  , l @ ly @ l )
                ]
              in
              List.iter
                (fun (how, got, want) ->
                   if got <> want then note (Printf.sprintf "%s then %s" (show shape) how))
                after)
           (shapes 3 [ 0; 1; 2 ]));
    let cats, ls = parts [ 3; 0; 5; 2 ] in
    let xs = flatten cats in
    ignore (Sys.opaque_identity (to_list xs, to_list (C.tail xs), C.snoc xs 9));
    check
      (t "the parts are what they were after a flatten, a tail and a snoc of it")
      (List.map to_list cats = ls);
    (* a random trace over earlier versions, every version against a list model *)
    let steps = 600
    and cap = 2_000 in
    let v = Array.make (steps + 1) (C.empty, []) in
    Random.init 20261016;
    all_of
      (t
         (Printf.sprintf
            "a random trace of %d cons, snoc, flatten of up to four random earlier \
             versions, tail and head, every version against a list model"
            steps))
      (fun note ->
         for i = 1 to steps do
           let a, la = v.(Random.int i) in
           v.(i)
           <- (match Random.int 5 with
               | 0 -> C.cons i a, i :: la
               | 1 -> C.snoc a i, la @ [ i ]
               | 2 ->
                 let picked = List.init (Random.int 5) (fun _ -> v.(Random.int i)) in
                 let cats, ls = List.split picked in
                 let l = List.concat ls in
                 if List.length l > cap then a, la else flatten cats, l
               | 3 -> if la = [] then a, la else C.tail a, List.tl la
               | _ ->
                 if la <> [] && C.head a <> List.hd la
                 then note (Printf.sprintf "head at step %d" i);
                 a, la)
         done;
         Array.iteri
           (fun i (c, l) -> if to_list c <> l then note (Printf.sprintf "version #%d" i))
           v)
  ;;

  (* ------------------------------------------------------------------ clocks *)

  let singletons n = List.init n singleton

  (* [n] elements as [k] parts of n / k each, each built by [build], with an empty
     between every two when [spaced]. *)
  let split_into ?(spaced = false) build k n =
    List.concat_map
      (fun i ->
         let part = build (List.init (n / k) (fun j -> (i * (n / k)) + j)) in
         if spaced && i > 0 then [ C.empty; part ] else [ part ])
      (upto k)
  ;;

  let run_flatten name =
    let t label = Printf.sprintf "%s: %s" name label in
    let n = 100_000 in
    List.iter
      (fun (label, l) ->
         let c = allocated (fun () -> flatten l) in
         check
           (t (Printf.sprintf "flatten of %s, nothing forced: %.0f words" label c))
           (c <= flatten_constant))
      [ Printf.sprintf "%d singletons" n, singletons n
      ; ( Printf.sprintf "%d singletons with an empty before each" n
        , List.concat_map (fun x -> [ C.empty; x ]) (singletons n) )
      ];
    let l = singletons n in
    List.iter
      (fun j ->
         let c =
           allocated (fun () ->
             let xs = ref (flatten l) in
             drain j xs;
             !xs)
           /. float_of_int (1 + j)
         in
         check
           (t
              (Printf.sprintf
                 "flatten of %d singletons then %d tails: %.2f words per operation"
                 n
                 j
                 c))
           (c <= flatten_constant))
      [ 1; 2; 10 ]
  ;;

  (* The parts of n elements to flatten, built outside the clock, with their e. *)
  let flatten_sequences n =
    [ "n singletons", singletons n, 0
    ; ( "n/10 lists of 10 by cons, an empty between every two"
      , split_into ~spaced:true by_cons (n / 10) n
      , (n / 10) - 1 )
    ; "n/100 fat trees of 100", split_into fat_of (n / 100) n, 0
    ; "n/100 chains of 100", split_into chain_of (n / 100) n, 0
    ; ( "ten flattens of n/10 singletons"
      , List.init 10 (fun i ->
          flatten (List.init (n / 10) (fun j -> singleton ((i * (n / 10)) + j))))
      , 0 )
    ]
  ;;

  (* The flatten, counting 1 + e, and then n tails. *)
  let run_sequences name =
    let t label = Printf.sprintf "%s: %s" name label in
    List.iter
      (fun (n, longer) ->
         List.iter
           (fun (sequence, parts, e) ->
              let c =
                mean (fun () ->
                  let xs = ref (flatten parts) in
                  drain n xs;
                  ignore (Sys.opaque_identity !xs);
                  1 + e + n)
              in
              check
                (t
                   (Printf.sprintf
                      "flatten of %s then n tails, amortised O(1 + e)%s: %.2f words per \
                       operation at n=%d"
                      sequence
                      longer
                      c
                      n))
                (c <= flatten_constant))
           (flatten_sequences n))
      [ 1_000, ""; 100_000, ", a hundred times longer" ]
  ;;

  (* Every version of a drain of the flatten of n singletons: each one's last child is
     the suspension of the rest. *)
  let flatten_versions n =
    let v = Array.make n C.empty in
    v.(0) <- flatten (singletons n);
    for i = 1 to n - 1 do
      v.(i) <- C.tail v.(i - 1)
    done;
    v
  ;;

  let run_versions name =
    let t label = Printf.sprintf "%s, persistently: %s" name label in
    let n = 1_000
    and k = 20 in
    let v = flatten_versions n in
    List.iter
      (fun (label, op) ->
         let i, c = dearest_repeated v k op in
         check
           (t
              (Printf.sprintf
                 "%s, %d times over from each version of a drain of the flatten of %d \
                  singletons, dearest from #%d: %.2f words per operation"
                 label
                 k
                 n
                 i
                 c))
           (c <= flatten_constant))
      [ "tail", tail_op
      ; "++ a singleton then tail", op (fun xs -> C.tail (xs ++ singleton 0))
      ; ( "flatten [xs; E; xs] then tail"
        , op (fun xs -> C.tail (flatten [ xs; C.empty; xs ])) )
      ];
    let i, c = dearest_repeated v 1 (op C.head) in
    check
      (t
         (Printf.sprintf
            "head allocates nothing at any version of the drain, dearest #%d at %.0f \
             words"
            i
            c))
      (c = 0.0);
    let steps = 100_000 in
    let v = Array.make (steps + 1) C.empty in
    Random.init 20261017;
    let c =
      mean (fun () ->
        let sum = ref 0 in
        for i = 1 to steps do
          let a = v.(Random.int i) in
          v.(i)
          <- (match Random.int 5 with
              | 0 -> C.cons i a
              | 1 -> C.snoc a i
              | 2 -> flatten (List.init (Random.int 5) (fun _ -> v.(Random.int i)))
              | 3 -> if C.is_empty a then a else C.tail a
              | _ ->
                if not (C.is_empty a) then sum := !sum + C.head a;
                a)
        done;
        ignore (Sys.opaque_identity !sum);
        steps)
    in
    check
      (t
         (Printf.sprintf
            "a random trace of %d operations, flatten of up to four random earlier \
             versions among them: %.2f words per operation"
            steps
            c))
      (c <= flatten_constant)
  ;;

  let run name =
    run_contract name;
    run_flatten name;
    run_sequences name;
    run_versions name
  ;;
end

module Flatten_bootstrapped =
  Flatten
    (CatenableList (BootstrappedQueuePrimQ (Okasaki.Ch7.RealTimeQueue (Okasaki.Ch4.Stream))))

module Flatten_bankers =
  Flatten (CatenableList (Okasaki.Ch6.BankersQueue (Okasaki.Ch4.Stream)))

let test_flatten () =
  Flatten_bootstrapped.run "flatten over BootstrappedQueuePrimQ (RealTimeQueue)";
  Flatten_bankers.run "flatten over BankersQueue"
;;

(* ---------------------------------------------------- Bootstrap (Figure 10.7) *)

(* Section 10.2.2 bootstraps heaps for the merge: a bootstrapped heap is empty or a node
   of its minimum and a primitive heap whose elements are bootstrapped heaps, ordered by
   their roots, so that merge is one PrimH.insert of the heap with the larger root into
   the other's primitive heap, insert is a merge with a singleton, find_min reads the
   root, and delete_min takes the least child out of the primitive heap, promotes its
   root and merges the two primitive heaps. p.159 states the costs: find_min O(1)
   worst-case "regardless of the underlying implementation", insert and merge the cost
   of PrimH.insert, delete_min that of a PrimH.find_min, delete_min and merge. Over a
   primitive heap with O(1) worst-case insert and O(log n) worst-case queries, the skew
   binomial heap of 9.3.2 or the scheduled binomial heap of 7.3, that is find_min, insert
   and merge in O(1) and delete_min in O(log n), all worst-case; the remark on p.160 adds
   that over the lazy binomial heap of 6.4.1 it is find_min O(1) worst-case, insert and
   merge O(1) amortised and delete_min O(log n) amortised. Figure 10.7 is a higher-order
   functor, a functor over the heap functor and the element structure, with the primitive
   heap and the element structure of bootstrapped heaps declared recursively, which
   Standard ML cannot do and OCaml's module rec can.

   The contract is Chapter 9's heap contract from heaps.ml, with its ties over keyed
   pairs. The clocks are per operation, comparisons through the counting element type
   and words, each applied to a heap of n elements against a budget in L = log2 (n + 1),
   and the dearest single call of each operation is the check, since the claims are
   worst-case: find_min is held to nothing at all, insert and merge to constants, and
   delete_min to a line in L; over the lazy binomial heap it is the mean call of a run
   against its own, smaller, budgets, except find_min's. Four sequences from empty at a
   thousand and a hundred thousand (ascending, random and equal inserts, each followed
   by a find_min, then a drain; insert and delete_min at a steady size), n singletons
   merged pairwise and drained, and a random trace of 20000 operations over earlier
   versions. Measured over the skew heap: insert and merge 3 comparisons, the root's and
   the skew link's two, and 35 and 32 words; delete_min 57 comparisons and 854 words at
   65000 elements, L = 16, about 3L + 9 and 50L; over the scheduled heap an insert is 79
   words, its schedule; over the lazy heap a delete_min comes to 28 comparisons and 437
   words a call at a hundred thousand. The budgets are about twice those. The guard is
   Chapter 3's binomial heap as PrimH, whose insert is O(log n): an insert into the
   all-ones primitive heap of 2^17 - 1 under the root must then be seen to compare 17
   times, and not an insert of a new minimum, which lands in an empty primitive heap
   under the new root whatever PrimH is. *)

(* Comparisons and words one call may spend on a heap of n elements, L = log2 (n + 1). *)
module type HEAP_BUDGETS = sig
  val insert : float -> float * float
  val merge : float -> float * float
  val find_min : float -> float * float
  val delete_min : float -> float * float
end

(* Over a primitive heap with O(1) worst-case insert and O(log n) worst-case queries,
   for the dearest call. *)
module Worst_case_budgets = struct
  let insert _ = 6.0, 160.0
  let merge _ = 6.0, 160.0
  let find_min _ = 0.0, 0.0
  let delete_min l = (6.0 *. l) +. 12.0, (100.0 *. l) +. 200.0
end

(* Over the lazy binomial heap, for the mean call of a run; find_min stays worst-case. *)
module Amortised_budgets = struct
  let insert _ = 2.0, 32.0
  let merge _ = 2.0, 32.0
  let find_min _ = 0.0, 0.0
  let delete_min l = (3.0 *. l) +. 6.0, (40.0 *. l) +. 100.0
end

module Heap_clocks (H : HEAP with type Element.t = int) (B : HEAP_BUDGETS) = struct
  let of_list xs = List.fold_left (fun h x -> H.insert x h) H.empty xs

  (* One operation's clock: the dearest call as a fraction of its budget and what it was,
     and the totals spent and allowed. *)
  type clock =
    { op : string
    ; budget : float -> float * float
    ; mutable ratio : float
    ; mutable what : string
    ; mutable spent : float * float
    ; mutable allowed : float * float
    ; mutable calls : int
    }

  let clock op budget =
    { op
    ; budget
    ; ratio = 0.0
    ; what = ""
    ; spent = 0.0, 0.0
    ; allowed = 0.0, 0.0
    ; calls = 0
    }
  ;;

  let insert = clock "insert" B.insert
  and merge = clock "merge" B.merge
  and find_min = clock "find_min" B.find_min
  and delete_min = clock "delete_min" B.delete_min

  let clocks = [ insert; merge; find_min; delete_min ]

  let reset () =
    List.iter
      (fun k ->
         k.ratio <- 0.0;
         k.what <- "";
         k.spent <- 0.0, 0.0;
         k.allowed <- 0.0, 0.0;
         k.calls <- 0)
      clocks
  ;;

  (* Spent over budget; a budget of nothing is met by spending nothing. *)
  let over spent budget =
    if budget = 0.0 then if spent = 0.0 then 0.0 else infinity else spent /. budget
  ;;

  (* [f], call number [at] of [k], on a heap of [size] elements. *)
  let timed k ~at ~size f =
    let r, (c, w) = spent f in
    let cb, wb = k.budget (log2 (size + 1)) in
    let ratio = Float.max (over c cb) (over w wb) in
    k.spent <- fst k.spent +. c, snd k.spent +. w;
    k.allowed <- fst k.allowed +. cb, snd k.allowed +. wb;
    k.calls <- k.calls + 1;
    if ratio >= k.ratio
    then (
      k.ratio <- ratio;
      k.what
      <- Printf.sprintf
           "#%d on %d elements at %.0f comparisons and %.0f words, budget %.0f and %.0f"
           at
           size
           c
           w
           cb
           wb);
    r
  ;;

  (* The checks of a run: every clock that ran, the dearest call within its budget, or
     the totals within theirs when [amortised], shown per call. *)
  let within ?(amortised = false) name =
    List.iter
      (fun k ->
         if k.calls > 0
         then
           if amortised && k.budget 1.0 <> (0.0, 0.0)
           then (
             let c, w = k.spent
             and cb, wb = k.allowed
             and per x = x /. float_of_int k.calls in
             check
               (Printf.sprintf
                  "%s: %s, amortised over %d calls, %.2f comparisons and %.1f words per \
                   call, budget %.2f and %.1f"
                  name
                  k.op
                  k.calls
                  (per c)
                  (per w)
                  (per cb)
                  (per wb))
               (c <= cb && w <= wb))
           else
             check
               (Printf.sprintf "%s: %s, the dearest is %s" name k.op k.what)
               (k.ratio <= 1.0))
      clocks
  ;;

  type op =
    | Insert of int
    | Find_min
    | Delete_min

  (* [ops] from the empty heap, every call on its clock. *)
  let run ops =
    let h = ref H.empty
    and size = ref 0
    and sum = ref 0 in
    Array.iteri
      (fun i op ->
         match op with
         | Insert x ->
           h := timed insert ~at:i ~size:!size (fun () -> H.insert x !h);
           incr size
         | Find_min ->
           sum := !sum + timed find_min ~at:i ~size:!size (fun () -> H.find_min !h)
         | Delete_min ->
           h := timed delete_min ~at:i ~size:!size (fun () -> H.delete_min !h);
           decr size)
      ops;
    ignore (Sys.opaque_identity !sum)
  ;;

  (* Each insert followed by a find_min, then a drain. *)
  let build_then_drain xs =
    let n = Array.length xs in
    Array.init (3 * n) (fun i ->
      if i < 2 * n
      then if i mod 2 = 0 then Insert xs.(i / 2) else Find_min
      else Delete_min)
  ;;

  let sequences n =
    Random.init n;
    [ ( "n ascending inserts, each then a find_min, then n delete_mins"
      , build_then_drain (Array.init n Fun.id) )
    ; ( "n random inserts, each then a find_min, then n delete_mins"
      , build_then_drain (Array.init n (fun _ -> Random.int 1_000_000)) )
    ; ( "n equal inserts, each then a find_min, then n delete_mins"
      , build_then_drain (Array.make n 7) )
    ; ( "insert then delete_min at a steady size of 1000, n times over"
      , Array.init
          (1000 + (2 * n))
          (fun i ->
             if i < 1000 then Insert i else if i mod 2 = 0 then Insert i else Delete_min)
      )
    ]
  ;;

  let test_sequences ?amortised name n =
    List.iter
      (fun (what, ops) ->
         reset ();
         run ops;
         within ?amortised (Printf.sprintf "%s, n=%d, %s" name n what))
      (sequences n)
  ;;

  (* n singletons merged pairwise, every merge on the clock against the heap it makes, then
     drained. *)
  let test_merges ?amortised name n =
    reset ();
    let at = ref 0 in
    let rec round = function
      | (a, sa) :: (b, sb) :: rest ->
        incr at;
        (timed merge ~at:!at ~size:(sa + sb) (fun () -> H.merge a b), sa + sb)
        :: round rest
      | l -> l
    in
    let rec go = function
      | [ (h, _) ] -> h
      | [] -> H.empty
      | l -> go (round l)
    in
    let h = ref (go (List.init n (fun i -> H.insert i H.empty, 1))) in
    for i = 1 to n do
      h := timed delete_min ~at:i ~size:(n - i + 1) (fun () -> H.delete_min !h)
    done;
    within
      ?amortised
      (Printf.sprintf "%s, %d singletons merged pairwise, then drained" name n)
  ;;

  (* A random trace over earlier versions, each call on its clock against the heap it is
     applied to or makes. Sizes are tracked, since merging versions of versions makes heaps
     far larger than the trace is long. *)
  let test_versions ?amortised name =
    reset ();
    let n = 20_000 in
    Random.init 20261018;
    let v = Array.make (n + 1) H.empty
    and size = Array.make (n + 1) 0
    and sum = ref 0 in
    for i = 1 to n do
      let p = Random.int i
      and q = Random.int i in
      match Random.int 5 with
      | 2 when size.(p) + size.(q) <= 1 lsl 40 ->
        v.(i)
        <- timed merge ~at:i ~size:(size.(p) + size.(q)) (fun () -> H.merge v.(p) v.(q));
        size.(i) <- size.(p) + size.(q)
      | 3 when size.(p) > 0 ->
        v.(i) <- timed delete_min ~at:i ~size:size.(p) (fun () -> H.delete_min v.(p));
        size.(i) <- size.(p) - 1
      | 4 when size.(p) > 0 ->
        sum := !sum + timed find_min ~at:i ~size:size.(p) (fun () -> H.find_min v.(p));
        v.(i) <- v.(p);
        size.(i) <- size.(p)
      | _ ->
        v.(i) <- timed insert ~at:i ~size:size.(p) (fun () -> H.insert i v.(p));
        size.(i) <- size.(p) + 1
    done;
    ignore (Sys.opaque_identity (v, !sum));
    within ?amortised (name ^ ", a random trace of 20000 operations over earlier versions")
  ;;

  let test_clocks ?amortised name =
    test_sequences ?amortised name 1_000;
    test_sequences ?amortised name 100_000;
    test_merges ?amortised name 1_000;
    test_merges ?amortised name 100_000;
    test_versions ?amortised name
  ;;
end

(* Figure 10.7 over a heap functor: the contract over ints and keyed pairs, the clocks
   over the counting ints. *)
module Boot (MakeH : functor (E : ORDERED) -> HEAP with type Element.t = E.t) = struct
  module H = BootstrapFigure (MakeH) (Counting_int)
  module K = BootstrapFigure (MakeH) (Heaps.Keyed)
  module Contract = Heaps.Heap_contract (H) (K)

  let run ?amortised budgets name =
    Contract.run name;
    let module Clocks = Heap_clocks (H) ((val budgets : HEAP_BUDGETS)) in
    Clocks.test_clocks ?amortised name
  ;;
end

module Boot_skew = Boot (Okasaki.Ch9.SkewBinomialHeap)

(* The scheduled binomial heap takes its stream functor too. *)
module Scheduled (E : ORDERED) =
  Okasaki.Ch7.ScheduledBinomialHeap (E) (Okasaki.Ch4.Stream)

module Boot_scheduled = Boot (Scheduled)
module Boot_lazy = Boot (Okasaki.Ch6.LazyBinomialHeap)

(* Whether the insert clock can tell O(1) from O(log n): over Chapter 3's binomial heap,
   an insert into a primitive heap of 2^k - 1 elements, the all-ones heap, links k times.
   Not an insert of a new minimum, which goes into an empty primitive heap under the new
   root whatever PrimH is: the element after 2^k ascending ones, whose primitive heap
   under the root holds the other 2^k - 1. *)
module Boot_strict = BootstrapFigure (Okasaki.Ch3.BinomialHeap) (Counting_int)

let test_boot_guard () =
  let k = 17 in
  let h =
    List.fold_left (fun h x -> Boot_strict.insert x h) Boot_strict.empty (upto (1 lsl k))
  in
  let c = count_only (fun () -> Boot_strict.insert (1 lsl k) h) in
  check
    (Printf.sprintf
       "guard: over Chapter 3's binomial heap the insert after 2^%d ascending ones, into \
        the all-ones primitive heap under the root, is seen to compare %d times, budget \
        %.0f"
       k
       c
       (fst (Worst_case_budgets.insert 0.0)))
    (float_of_int c > fst (Worst_case_budgets.insert 0.0))
;;

let worst_case = (module Worst_case_budgets : HEAP_BUDGETS)
let amortised = (module Amortised_budgets : HEAP_BUDGETS)

let test_boot () =
  Boot_skew.run worst_case "BootstrapFigure (SkewBinomialHeap)";
  test_boot_guard ();
  Boot_scheduled.run worst_case "BootstrapFigure (ScheduledBinomialHeap)";
  Boot_lazy.run ~amortised:true amortised "BootstrapFigure (LazyBinomialHeap)"
;;

(* ------------------------------------- heaps with info (Exercise 10.8, Figure 10.8) *)

(* Exercise 10.8 splits an element in two: the priority, which is all the heap compares,
   fixed with its order at functor application as Priority : ORDERED, and the info that
   travels with it, of a type parameter 'a the heap never looks at. Figure 10.8 is the
   signature: insert takes both, find_min returns both. Part (a) is the lazy binomial
   heap of Figure 6.5 over pairs, every comparison on the priority half, and the claims
   are Chapter 6's: insert O(1) amortised, find_min, merge and delete_min O(log n)
   amortised, laziness making single calls as dear as they like.

   A heap with info is held to the heap contract of Chapter 9 through two adapters: over
   ints, the element its own priority and payload; and over keyed pairs, the key the
   priority and the tag the payload, which is what the contract's ties check wants and
   what shows a payload parted from its priority, since every pair has to come out once
   and whole. One check more reads the pair back directly. The clocks are this chapter's
   per-operation clocks as means, comparisons and words against Chapter 6's budgets with
   room for the pair: an insert 2 comparisons and 32 words, a query 2L + 2 and 24L + 48.
   Measured, an insert is 0 comparisons and 9 words, the suspension and the node it
   wraps, and a delete_min at a hundred thousand elements 20 comparisons and 225 words a
   call. Then p.70's "regardless of whether the heaps are used persistently", held as
   test_ch6 holds it, on the all-ones heap. *)

(* A heap with info as a HEAP, over ints and over keyed pairs. *)
module Info (H : HEAP_WITH_INFO with type Priority.t = int) = struct
  module As_int = struct
    module Element = struct
      type t = int

      let eq = ( = )
      let lt = ( < )
      let leq = ( <= )
    end

    type heap = int H.heap

    let empty = H.empty
    let is_empty = H.is_empty
    let insert x h = H.insert x x h
    let merge = H.merge
    let find_min h = fst (H.find_min h)
    let delete_min = H.delete_min
  end

  module As_keyed = struct
    module Element = Heaps.Keyed

    type heap = int H.heap

    let empty = H.empty
    let is_empty = H.is_empty
    let insert (key, tag) h = H.insert key tag h
    let merge = H.merge
    let find_min = H.find_min
    let delete_min = H.delete_min
  end

  module Contract = Heaps.Heap_contract (As_int) (As_keyed)

  let run_contract name =
    Contract.run name;
    let n = 200 in
    Random.init 20261019;
    let h =
      List.fold_left
        (fun h p -> H.insert p (string_of_int p) h)
        H.empty
        (List.init n (fun _ -> Random.int 50))
    in
    let pairs = drain_with ~is_empty:H.is_empty ~head:H.find_min ~tail:H.delete_min h in
    check
      (Printf.sprintf
         "%s: the payload comes back with its priority, %d random inserts drained"
         name
         n)
      (List.for_all (fun (p, x) -> x = string_of_int p) pairs
       && List.map fst pairs = List.sort compare (List.map fst pairs))
  ;;
end

(* Chapter 6's budgets for the lazy binomial heap, the words with room for the pair. *)
module Lazy_info_budgets = struct
  let insert _ = 2.0, 32.0
  let merge l = (2.0 *. l) +. 2.0, (24.0 *. l) +. 48.0
  let find_min l = (2.0 *. l) +. 2.0, (24.0 *. l) +. 48.0
  let delete_min l = (2.0 *. l) +. 2.0, (24.0 *. l) +. 48.0
end

module Lazy_info = Info (LazyBinomialHeapWithInfo (Counting_int))
module Lazy_info_clocks = Heap_clocks (Lazy_info.As_int) (Lazy_info_budgets)

(* p.70's claim, that the insert is O(1) amortised "regardless of whether the heaps are
   used persistently", as test_ch6 holds it: the all-ones heap of 2^16 - 1, 16 trees,
   which an insert that ran at once would link 16 times, inserted into d times over with
   nothing forced pays nothing but the suspensions, and when each is looked at, the
   looking pays, within the query budget. *)
let test_lazy_info_persistence () =
  let module H = Lazy_info.As_int in
  let module B = Lazy_info_budgets in
  let t label = "LazyBinomialHeapWithInfo, persistently: " ^ label in
  let k = 16 in
  let n = (1 lsl k) - 1 in
  let h = List.fold_left (fun h x -> H.insert x h) H.empty (upto n) in
  ignore (H.find_min h);
  let c, w = spent_only (fun () -> H.insert 0 h) in
  check
    (t
       (Printf.sprintf
          "an insert into the all-ones heap of %d compares nothing and allocates %.0f \
           words"
          n
          w))
    (c = 0.0 && w <= snd (B.insert 0.0));
  let c, _ = spent_only (fun () -> H.merge h h) in
  check (t "a merge of the all-ones heap with itself compares nothing") (c = 0.0);
  let d = 10_000
  and l = log2 (n + 3) in
  let mean f =
    let (), (c, w) =
      spent (fun () ->
        for _ = 1 to d do
          ignore (Sys.opaque_identity (f ()))
        done)
    in
    c /. float_of_int d, w /. float_of_int d
  in
  let ic, iw = B.insert l
  and qc, qw = B.find_min l in
  let c, w = mean (fun () -> H.insert 1 (H.insert 0 h)) in
  check
    (t
       (Printf.sprintf
          "%d times an insert on top of an insert into it, nothing forced: %.2f \
           comparisons and %.1f words a pair, budget %.0f and %.0f"
          d
          c
          w
          (2.0 *. ic)
          (2.0 *. iw)))
    (c <= 2.0 *. ic && w <= 2.0 *. iw);
  let c, w = mean (fun () -> H.find_min (H.insert 1 (H.insert 0 h))) in
  check
    (t
       (Printf.sprintf
          "and each of them looked at: %.2f comparisons and %.1f words, budget %.0f and \
           %.0f"
          c
          w
          ((2.0 *. ic) +. qc)
          ((2.0 *. iw) +. qw)))
    (c <= (2.0 *. ic) +. qc && w <= (2.0 *. iw) +. qw)
;;

let test_lazy_info () =
  let name = "LazyBinomialHeapWithInfo" in
  Lazy_info.run_contract name;
  Lazy_info_clocks.test_clocks ~amortised:true name;
  test_lazy_info_persistence ()
;;

(* ------------------------------------------------ Bootstrap (Exercise 10.8(b)) *)

(* Part (b) is Figure 10.7 over a primitive heap with info, with nothing recursive about
   the modules: the primitive heap's payloads are bootstrapped heaps, each keyed by its
   root's priority, and that is a type 'a heap = E | H of (Priority.t * 'a) * 'a heap
   PrimH.heap, recursive in the ordinary way. The operations are the figure's line for
   line, and so are the claims, with p.160's remark the ones that apply to the one
   PrimH there is, the lazy binomial heap of part (a): find_min O(1) worst-case, insert
   and merge O(1) amortised and delete_min O(log n) amortised.

   The contract is part (a)'s, through the same adapters, and the clocks are Figure
   10.7's means over its lazy heap against its amortised budgets, find_min held to
   nothing on every call. Measured, an insert is 1 comparison, the root's, and 18 words,
   the two nodes, the pair and the primitive heap's suspension, and a delete_min at a
   hundred thousand elements 28 comparisons and 298 words a call. Then part (a)'s
   persistence check over again, which is where the two parts differ: the heap of 2^16
   ascending inserts, its root over the all-ones primitive heap of the rest, inserted
   into d times over with nothing forced pays nothing but the suspensions, as before; a
   find_min of each pays nothing at all, where part (a)'s paid the query; and a
   delete_min of each pays the 16 pending links, 20 comparisons, within its own budget.
   The checks with teeth against a Bootstrap that looks into the primitive heap are
   those two: find_min's budget of nothing, and the inserts with nothing forced, since
   over a trace the suspensions are the same work forced early or late, and only the
   ones never forced tell. *)

module Boot_info = Info (Bootstrap (LazyBinomialHeapWithInfo (Counting_int)))
module Boot_info_clocks = Heap_clocks (Boot_info.As_int) (Amortised_budgets)

let test_boot_info_persistence () =
  let module H = Boot_info.As_int in
  let module B = Amortised_budgets in
  let t label = "Bootstrap (LazyBinomialHeapWithInfo), persistently: " ^ label in
  let k = 16 in
  let n = 1 lsl k in
  let h = List.fold_left (fun h x -> H.insert x h) H.empty (upto n) in
  ignore (H.delete_min h);
  let c, w = spent_only (fun () -> H.insert n h) in
  check
    (t
       (Printf.sprintf
          "an insert under the root of the heap of %d, into the all-ones primitive heap, \
           compares %.0f and allocates %.0f words"
          n
          c
          w))
    (c <= fst (B.insert 0.0) && w <= snd (B.insert 0.0));
  let d = 10_000
  and l = log2 (n + 2) in
  let mean f =
    let (), (c, w) =
      spent (fun () ->
        for _ = 1 to d do
          ignore (Sys.opaque_identity (f ()))
        done)
    in
    c /. float_of_int d, w /. float_of_int d
  in
  let ic, iw = B.insert l
  and dc, dw = B.delete_min l in
  let c, w = mean (fun () -> H.insert (n + 1) (H.insert n h)) in
  check
    (t
       (Printf.sprintf
          "%d times an insert on top of an insert into it, nothing forced: %.2f \
           comparisons and %.1f words a pair, budget %.0f and %.0f"
          d
          c
          w
          (2.0 *. ic)
          (2.0 *. iw)))
    (c <= 2.0 *. ic && w <= 2.0 *. iw);
  let c, w = mean (fun () -> H.find_min (H.insert (n + 1) (H.insert n h))) in
  check
    (t
       (Printf.sprintf
          "and the minimum of each read, for nothing more: %.2f comparisons and %.1f \
           words, budget %.0f and %.0f"
          c
          w
          (2.0 *. ic)
          (2.0 *. iw)))
    (c <= 2.0 *. ic && w <= 2.0 *. iw);
  let c, w = mean (fun () -> H.delete_min (H.insert (n + 1) (H.insert n h))) in
  check
    (t
       (Printf.sprintf
          "and each deleted from, paying the %d pending links: %.2f comparisons and %.1f \
           words, budget %.0f and %.0f"
          k
          c
          w
          ((2.0 *. ic) +. dc)
          ((2.0 *. iw) +. dw)))
    (c <= (2.0 *. ic) +. dc && w <= (2.0 *. iw) +. dw)
;;

let test_boot_info () =
  let name = "Bootstrap (LazyBinomialHeapWithInfo)" in
  Boot_info.run_contract name;
  Boot_info_clocks.test_clocks ~amortised:true name;
  test_boot_info_persistence ()
;;

(* --------------------------------------------------- TrieFigure (Figure 10.10) *)

(* Section 10.3.1 bootstraps a finite map over an aggregate key, a list of elements of
   some base type, out of a finite map over the base type: a trie node is a value slot,
   filled or not, and a base map from one element to a child trie, and a key of length n
   is read one element per level. The functor is over any FINITE_MAP, so the base map may
   be Chapter 2's unbalanced map, or another trie, which gives maps over lists of lists.
   The claims are the structure's: lookup and bind of a key of length n cost n base map
   operations, one per element, and p.165's remark that an unsuccessful search can stop
   early, at the first element with no edge, having read nothing past it.

   The contract is test_ch2's for a finite map, since lookup and bind are all there is:
   over a key universe, every key either looks up to its latest value or fails, and that
   pins the map exactly, so random workloads are swept against an assoc-list reference
   and so is every version of a chain of binds. Then the book's own trie, cat, dog, car
   and cart over characters, where a prefix is a path but not a key and the empty key is
   the root's own slot; and a trie of tries over lists of words. The clocks run over a
   complete trie, every key of length l over 0..b-1, with the base maps built in ascending
   order so each is Chapter 2's spine of depth b, the dearest shape that map can give a
   trie of that branching, and they hold the trie to what the base map spends: a lookup
   of a key of l elements is l base-map lookups and nothing more, in comparisons and in
   words, at most l(b + 1) comparisons by 2.2's bound; a miss at the first element costs
   one base-map lookup whether the key is 10 long or 100000; a bind of n elements
   compares no more than its n base-map lookups and binds, and allocates no more than
   n + 1 levels of those and a three-word node, the level to spare for the node and the
   Some at the end of the key. Measured at b = 4, l = 6: the base map's lookup is 5
   comparisons and 27 words, the candidate boxed a step, its bind 8 and 19, and the
   trie's lookup of the last key exactly 30 and 162; a rebind of it 78 comparisons, six
   levels of 13, and 299 words, six levels of 49 and the leaf's 5, against a budget of
   343; the miss 5 comparisons and 30 words at either length. *)

(* Ordered characters, for the base map of a trie over strings. *)
module Char_ordered = struct
  type t = char

  let eq = Char.equal
  let lt = ( < )
  let leq = ( <= )
end

let explode s = List.init (String.length s) (String.get s)

module Chars = TrieFigure (Okasaki.Ch2.UnbalancedMap (Char_ordered))
module Words = TrieFigure (Chars)
module Ints = TrieFigure (Okasaki.Ch2.UnbalancedMap (Counting_int))

(* A trie as a finite map: what lookup and bind alone can show, over a key universe the
   workloads draw from. *)
module Trie_contract (T : FINITE_MAP) = struct
  let lookup_opt k m =
    match T.lookup k m with
    | v -> Some v
    | exception Failure _ -> None
  ;;

  let of_list kvs = List.fold_left (fun m (k, v) -> T.bind k v m) T.empty kvs

  (* Every key of [universe] against the assoc list [reference]. *)
  let agrees universe m reference =
    List.for_all (fun k -> lookup_opt k m = List.assoc_opt k reference) universe
  ;;

  let run name ~universe =
    let t label = name ^ ": " ^ label in
    Random.init 20261014;
    let n = List.length universe in
    let pick () = List.nth universe (Random.int n) in
    check
      (t "the empty map has no key of the universe")
      (List.for_all (fun k -> lookup_opt k T.empty = None) universe);
    let ok = ref true in
    for _ = 1 to 300 do
      let ops = List.init (1 + Random.int 40) (fun _ -> pick (), Random.int 100) in
      let reference =
        List.fold_left (fun a (k, v) -> (k, v) :: List.remove_assoc k a) [] ops
      in
      if not (agrees universe (of_list ops) reference) then ok := false
    done;
    check
      (t
         (Printf.sprintf
            "agrees with an assoc-list reference over 300 random workloads, the %d keys \
             of the universe swept"
            n))
      !ok;
    (* A chain of binds, every version answering afterwards as it did when made. *)
    let _, _, versions =
      List.fold_left
        (fun (m, reference, vs) i ->
           let k = pick () in
           let m = T.bind k i m
           and reference = (k, i) :: List.remove_assoc k reference in
           m, reference, (m, reference) :: vs)
        (T.empty, [], [])
        (List.init 60 Fun.id)
    in
    check
      (t "every version of 60 binds still answers as it did")
      (List.for_all (fun (m, reference) -> agrees universe m reference) versions)
  ;;
end

module Chars_contract = Trie_contract (Chars)
module Words_contract = Trie_contract (Words)
module Ints_contract = Trie_contract (Ints)

(* Every list of length at most [l] over [alphabet]. *)
let rec lists_upto alphabet l =
  if l = 0
  then [ [] ]
  else
    []
    :: List.concat_map
         (fun k -> List.map (fun c -> c :: k) alphabet)
         (lists_upto alphabet (l - 1))
;;

let test_trie_contract () =
  Chars_contract.run
    "TrieFigure (UnbalancedMap (char))"
    ~universe:(lists_upto [ 'a'; 'b'; 'c' ] 3);
  Words_contract.run
    "TrieFigure (TrieFigure (UnbalancedMap (char)))"
    ~universe:(lists_upto (List.map explode [ "a"; "an"; "cat"; "dog" ]) 2);
  Ints_contract.run
    "TrieFigure (UnbalancedMap (int))"
    ~universe:(lists_upto [ 0; 1; 2 ] 3)
;;

(* The book's trie: cat, dog, car, cart. *)
module Book_trie (T : FINITE_MAP with type key = char list) = struct
  module C = Trie_contract (T)

  let run name =
    let t label = name ^ ", the book's trie: " ^ label in
    let at s m = T.lookup (explode s) m in
    let m =
      C.of_list
        (List.map
           (fun (s, v) -> explode s, v)
           [ "cat", 1; "dog", 2; "car", 3; "cart", 4 ])
    in
    check_int (t "cart") ~expect:4 ~actual:(at "cart" m);
    check_int
      (t "car, a key of its own on the way to cart")
      ~expect:3
      ~actual:(at "car" m);
    check_failure (t "ca is a path but not a key") "lookup: not found" (fun () ->
      at "ca" m);
    check_failure (t "dark leaves the trie at d") "lookup: not found" (fun () ->
      at "dark" m);
    check_failure (t "carts runs past cart") "lookup: not found" (fun () -> at "carts" m);
    check_failure (t "the empty key is not bound") "lookup: not found" (fun () -> at "" m);
    let m' = T.bind [] 0 m in
    check_int
      (t "the empty key, bound, is the root's own slot")
      ~expect:0
      ~actual:(at "" m');
    check_int (t "and cat is still under it") ~expect:1 ~actual:(at "cat" m');
    let m'' = T.bind (explode "ca") 9 m in
    check_int (t "ca bound in the middle of the path") ~expect:9 ~actual:(at "ca" m'');
    check_int (t "keeps cat below it") ~expect:1 ~actual:(at "cat" m'');
    check_int (t "and cart") ~expect:4 ~actual:(at "cart" m'');
    let m3 = T.bind (explode "car") 30 m in
    check_int (t "rebinding car replaces its value") ~expect:30 ~actual:(at "car" m3);
    check_int (t "and keeps cart") ~expect:4 ~actual:(at "cart" m3);
    check_int (t "while the original still has car at 3") ~expect:3 ~actual:(at "car" m);
    check_failure (t "and the original still has no ca") "lookup: not found" (fun () ->
      at "ca" m)
  ;;
end

module Chars_book = Book_trie (Chars)

(* A trie over lists of words: the inner trie's miss under a word is what the outer
   bind handles. *)
module Sentences (T : FINITE_MAP with type key = char list list) = struct
  module C = Trie_contract (T)

  let run name =
    let t label = name ^ ", sentences: " ^ label in
    let sentence s = List.map explode (String.split_on_char ' ' s) in
    let at s m = T.lookup (sentence s) m in
    let m =
      C.of_list
        (List.map
           (fun (s, v) -> sentence s, v)
           [ "the cat", 1; "the cat sat", 2; "the dog", 3; "a cat", 4 ])
    in
    check_int (t "the cat sat") ~expect:2 ~actual:(at "the cat sat" m);
    check_int (t "the cat") ~expect:1 ~actual:(at "the cat" m);
    check_int (t "a cat") ~expect:4 ~actual:(at "a cat" m);
    check_failure (t "the, a prefix") "lookup: not found" (fun () -> at "the" m);
    check_failure (t "the cow, no such word under the") "lookup: not found" (fun () ->
      at "the cow" m);
    check_failure (t "the cat sat down, past the end") "lookup: not found" (fun () ->
      at "the cat sat down" m);
    let m' = T.bind (sentence "the cow") 5 m in
    check_int (t "the cow, bound") ~expect:5 ~actual:(at "the cow" m');
    check_int (t "the cat still") ~expect:1 ~actual:(at "the cat" m');
    check_failure (t "and not in the original") "lookup: not found" (fun () ->
      at "the cow" m)
  ;;
end

module Words_sentences = Sentences (Words)

(* Every key of length [l] over 0..b-1, in an order that binds each node's children
   ascending, so that every base map of the trie they make is Chapter 2's spine. *)
let rec keys b l =
  if l = 0
  then [ [] ]
  else List.concat_map (fun k -> List.init b (fun d -> d :: k)) (keys b (l - 1))
;;

module Base = Okasaki.Ch2.UnbalancedMap (Counting_int)

(* What one level of the complete trie costs the base map: its lookup and its bind of the
   last child of a spine of b, comparisons and words. *)
let base_costs b =
  let spine =
    List.fold_left (fun m d -> Base.bind d () m) Base.empty (List.init b Fun.id)
  in
  ( spent_only (fun () -> ignore (Base.lookup (b - 1) spine))
  , spent_only (fun () -> ignore (Base.bind (b - 1) () spine)) )
;;

(* The trie's own share of a bind: the node it makes at a level. *)
let node_words = 3.0

(* The clocks of a trie keyed by int lists over Chapter 2's map of counting ints, on the
   complete trie. A trie that assumes no key is a prefix of another is clocked without
   the bind under the last key, [prefixes] false; a trie whose node is more than
   Figure 10.10's three words gives its own share of a level, [node_words]. *)
module Trie_clocks (T : FINITE_MAP with type key = int list) = struct
  module C = Trie_contract (T)

  (* The complete trie of those b^l keys, b children at every inner node. *)
  let complete b l = C.of_list (List.map (fun k -> k, 0) (keys b l))

  let run ?(prefixes = true) ?(node_words = node_words) name =
    List.iter
      (fun (b, l) ->
         let t label =
           Printf.sprintf "%s, the complete trie b=%d l=%d: %s" name b l label
         in
         let m = complete b l in
         let lf = float_of_int l in
         let (lc, lw), (bc, bw) = base_costs b in
         let deepest = List.init l (fun _ -> b - 1) in
         let c, w = spent_only (fun () -> ignore (T.lookup deepest m)) in
         check
           (t
              (Printf.sprintf
                 "a lookup of the last key is l base-map lookups and nothing more: %.0f \
                  comparisons and %.0f words, the base map's %.0f and %.0f a level"
                 c
                 w
                 lc
                 lw))
           (c <= lf *. lc && w <= lf *. lw);
         let lookup_budget = l * (b + 1) in
         let dearest =
           List.fold_left
             (fun acc k -> max acc (count_only (fun () -> ignore (T.lookup k m))))
             0
             (keys b l)
         in
         check
           (t
              (Printf.sprintf
                 "the dearest lookup of all %d keys compares %d times, budget l(b+1) = %d"
                 (List.length (keys b l))
                 dearest
                 lookup_budget))
           (dearest <= lookup_budget);
         (* A miss at the first element: the same few comparisons whatever is behind it. *)
         let miss n = b :: List.init (n - 1) (fun _ -> 0) in
         let short = miss 10
         and long = miss 100_000 in
         let c10 = count_only (fun () -> C.lookup_opt short m)
         and c100k, w100k = spent_only (fun () -> C.lookup_opt long m) in
         check
           (t
              (Printf.sprintf
                 "a miss at the first element compares %d times for a key of 10 and %.0f \
                  for one of 100000, budget b+1 = %d, and the long one allocates %.0f \
                  words, budget %.0f"
                 c10
                 c100k
                 (b + 1)
                 w100k
                 (lw +. 4.0)))
           (float_of_int c10 = c100k && c10 <= b + 1 && w100k <= lw +. 4.0);
         (* A bind of a key of n elements: n base-map lookups and binds, and n + 1 nodes. *)
         List.iter
           (fun (what, k) ->
              let n = float_of_int (List.length k) in
              let c, w = spent_only (fun () -> ignore (T.bind k 1 m)) in
              let cb = n *. (lc +. bc)
              and wb = (n +. 1.0) *. (lw +. bw +. node_words) in
              check
                (t
                   (Printf.sprintf
                      "%s is a base-map lookup and bind an element and a node a level: \
                       %.0f comparisons and %.0f words, budget %.0f and %.0f"
                      what
                      c
                      w
                      cb
                      wb))
                (c <= cb && w <= wb))
           ([ "a rebind of the last key", deepest ]
            @ (if prefixes
               then [ "a bind of a new key under the last node", deepest @ [ 0 ] ]
               else [])
            @ [ "a bind of a new key off the root", [ b ] ]))
      [ 4, 6; 2, 12 ]
  ;;
end

module Ints_clocks = Trie_clocks (Ints)

let test_trie () =
  test_trie_contract ();
  Chars_book.run "TrieFigure (UnbalancedMap (char))";
  Words_sentences.run "TrieFigure (TrieFigure (UnbalancedMap (char)))";
  Ints_clocks.run "TrieFigure (UnbalancedMap (int))"
;;

(* ---------------------------------------------------- EntryTrie (Exercise 10.9) *)

(* Exercise 10.9 rewrites the trie for keys none of which is a proper prefix of another,
   which the book illustrates as keys all of one length, or keys all ended by a character
   that occurs nowhere else. Then no key ends where another goes on, so a node is either
   an Entry, a value at the end of a key, or a TRIE of children, with no value slot at
   the inner nodes; and what a key that breaks the assumption does is the
   implementation's own affair, so no check here binds one. EntryTrie is that trie over
   any base map, and Int32KeyTrie keys any map over int lists by Int32.t, each key cut
   into its four bytes, all four always: a fixed width, and so a prefix-free code.

   The contract is Figure 10.10's over universes the assumption allows: the words of up
   to three letters over a, b and c each ended by '.', and the lists of three elements
   over 0..2. Then the book's trie with every key ended by '.', where car, a prefix of
   cart in Figure 10.10, is a key of its own by its end marker. The Int32 tries, over
   EntryTrie and over Figure 10.10's TrieFigure, run the contract on the 625 keys whose
   bytes are each one of 00, 01, 7F, 80 and FF: 0, -1, and the least and the greatest
   Int32 are among them, and so are keys that differ in one byte, and the pairs that an
   encoding dropping a zero byte would make one key or one a prefix of the other. Their
   base map counts its calls, and every key, small or large, must be found in exactly
   four lookups and rebound in four lookups and four binds. The clocks are Figure 10.10's
   on the complete trie, without the bind under the last key, which the assumption rules
   out. Measured at b = 4, l = 6: a lookup as Figure 10.10's, 30 comparisons and 162
   words; a rebind 290 words to Figure 10.10's 299, a word less at each of the six levels,
   where no option is kept, and three less at the leaf, an Entry where Figure 10.10 has a
   node and a Some. *)

module Chars_entry = EntryTrie (Okasaki.Ch2.UnbalancedMap (Char_ordered))
module Ints_entry = EntryTrie (Okasaki.Ch2.UnbalancedMap (Counting_int))
module Chars_entry_contract = Trie_contract (Chars_entry)
module Ints_entry_contract = Trie_contract (Ints_entry)
module Ints_entry_clocks = Trie_clocks (Ints_entry)

(* A word ended by the marker '.', which no key has anywhere else. *)
let ended s = explode s @ [ '.' ]

let test_entry_contract () =
  Chars_entry_contract.run
    "EntryTrie (UnbalancedMap (char)), keys ended by '.'"
    ~universe:(List.map (fun k -> k @ [ '.' ]) (lists_upto [ 'a'; 'b'; 'c' ] 3));
  Ints_entry_contract.run
    "EntryTrie (UnbalancedMap (int)), keys of length 3"
    ~universe:(keys 3 3)
;;

(* The book's trie, cat, dog, car and cart, every key ended by '.'. *)
let test_entry_strings () =
  let t label =
    "EntryTrie (UnbalancedMap (char)), the book's trie, keys ended by '.': " ^ label
  in
  let at s m = Chars_entry.lookup (ended s) m in
  let m =
    Chars_entry_contract.of_list
      (List.map (fun (s, v) -> ended s, v) [ "cat", 1; "dog", 2; "car", 3; "cart", 4 ])
  in
  check_int (t "cart") ~expect:4 ~actual:(at "cart" m);
  check_int
    (t "car, a key of its own beside cart by its end marker")
    ~expect:3
    ~actual:(at "car" m);
  check_failure (t "ca is a path but not a key") "lookup: not found" (fun () -> at "ca" m);
  check_failure (t "dark leaves the trie at d") "lookup: not found" (fun () ->
    at "dark" m);
  check_failure (t "carts runs past cart") "lookup: not found" (fun () -> at "carts" m);
  check_failure
    (t "car without its end marker stops at an inner node, which holds no value")
    "lookup: not found"
    (fun () -> Chars_entry.lookup (explode "car") m);
  let m' = Chars_entry.bind (ended "car") 30 m in
  check_int (t "rebinding car replaces its value") ~expect:30 ~actual:(at "car" m');
  check_int (t "and keeps cart") ~expect:4 ~actual:(at "cart" m');
  check_int (t "and cat") ~expect:1 ~actual:(at "cat" m');
  check_int (t "while the original still has car at 3") ~expect:3 ~actual:(at "car" m)
;;

(* A base map that counts the calls made to it. *)
module Counting_map (M : FINITE_MAP) = struct
  include M

  let lookups = ref 0
  let binds = ref 0

  let lookup k m =
    incr lookups;
    M.lookup k m
  ;;

  let bind k x m =
    incr binds;
    M.bind k x m
  ;;
end

module Byte_map = Counting_map (Base)

(* The 625 keys whose four bytes are each one of 00, 01, 7F, 80 and FF. *)
let int32_universe =
  let bytes = [| 0x00; 0x01; 0x7F; 0x80; 0xFF |] in
  List.map
    (fun k -> Int32.of_int (List.fold_left (fun acc i -> (acc lsl 8) lor bytes.(i)) 0 k))
    (keys 5 4)
;;

(* An Int32 trie: the contract, and the base-map calls each key costs. *)
module Int32_trie (T : FINITE_MAP with type key = Int32.t) = struct
  module C = Trie_contract (T)

  (* The base-map lookups and binds [f] makes. *)
  let calls f =
    Byte_map.lookups := 0;
    Byte_map.binds := 0;
    ignore (f ());
    !Byte_map.lookups, !Byte_map.binds
  ;;

  let run name =
    C.run name ~universe:int32_universe;
    let m = C.of_list (List.map (fun k -> k, 0) int32_universe) in
    let off expect f =
      List.filter (fun k -> calls (fun () -> f k) <> expect) int32_universe
    and first = function
      | [] -> ""
      | k :: _ -> Printf.sprintf ", but not 0x%08lx" k
    in
    let lookups = off (4, 0) (fun k -> T.lookup k m)
    and binds = off (4, 4) (fun k -> T.bind k 1 m) in
    check
      (Printf.sprintf
         "%s: every one of the %d keys, 0, -1 and the least and greatest Int32 among \
          them, is found in exactly 4 base-map lookups%s"
         name
         (List.length int32_universe)
         (first lookups))
      (lookups = []);
    check
      (Printf.sprintf
         "%s: and rebound in exactly 4 base-map lookups and 4 base-map binds%s"
         name
         (first binds))
      (binds = [])
  ;;
end

module Int32_entry = Int32_trie (Int32KeyTrie (EntryTrie (Byte_map)))
module Int32_figure = Int32_trie (Int32KeyTrie (TrieFigure (Byte_map)))

let test_entry_trie () =
  test_entry_contract ();
  test_entry_strings ();
  Int32_entry.run "Int32KeyTrie (EntryTrie (UnbalancedMap (int)))";
  Int32_figure.run "Int32KeyTrie (TrieFigure (UnbalancedMap (int)))";
  Ints_entry_clocks.run ~prefixes:false "EntryTrie (UnbalancedMap (int))"
;;

(* ----------------------------------------- PathCompressionTrie (Exercise 10.10) *)

(* Exercise 10.10 collapses the trie's chains of single children: every node carries a
   string, the longest common prefix of the keys below it, which a key must read before
   the node's value slot and its edges, so that the base map is consulted only where keys
   part. The invariant the book asks for, no node both invalid and an only child, is
   what the prefix rule already forces, read at the parent: a node without a value has
   two children or more, the empty trie aside, since a single edge would belong in the
   string. Together they leave one trie per set of keys: its nodes sit at the longest
   common prefixes of pairs of keys, a key paired with itself included, and nowhere else.
   The base map must also say whether two of its keys are equal, to read a string, and
   whether a map is empty, to recognise the empty trie, and the trie says both of its
   own keys and maps, so that it can be the base map of another.

   Chapter 2's map is sealed as a FINITE_MAP, so the base map here wraps it in an option,
   None the empty map, takes its key's own eq, and counts the calls made to it: a lookup
   is an edge passed, a bind an edge made or remade, a key_eq one element of a string
   read. The contract is Figure 10.10's, over its universes and the keys of up to six
   letters over a and b, where sparse workloads leave long strings; then the book's
   trie, the sentences over a trie of these tries, and the trie's own key_eq and
   is_empty. The shape is checked through the counts against the unique trie computed
   from the keys: after every bind of random workloads over that universe of 127 keys,
   every key bound is found through exactly as many base-map lookups as nodes sit above
   it, comparing each other element once, and the bind remade the edges on its key's
   way, and one more when it hung an old node under a new one. The clocks hold the
   trie to what the exercise is for, on four keys of n elements, 0..3 then zeros, at n =
   10 and 100000: a lookup passes one edge and reads the rest one comparison an element,
   and allocates the same at both lengths; a miss at the second element, a new key off
   the root and a key parting from a string at its sixth element cost the same at both
   lengths, the rest of each key and of each string kept as it is rather than read or
   copied; and Figure 10.10's clocks over the complete trie, where nothing is collapsed,
   with the node's share of a level twelve words to Figure 10.10's three. Measured: the
   lookup 14 comparisons at n = 10 and 100004 at n = 100000, 27 words at both; the miss
   6 comparisons and 30 words, the new key 13 and 68, the parting key 20 and 116; the
   rebind 22 and 100012 comparisons and 64 words at both, the walk counting what it
   matches and only a split or a branch copying that much of the string; on the
   complete trie at b = 4, l = 6, a lookup as Figure 10.10's, 30 comparisons and 162
   words, and a rebind 339 words to its 299, against a budget of 406. *)

(* Chapter 2's map widened to what Exercise 10.10 asks of a base map, counting the calls
   made to it. *)
module Widened (K : Okasaki.Ch2.ORDERED) = struct
  module B = Okasaki.Ch2.UnbalancedMap (K)

  type key = K.t
  type 'a map = 'a B.map option

  let lookups = ref 0
  let binds = ref 0
  let eqs = ref 0
  let empty = None
  let is_empty = Option.is_none

  let key_eq a b =
    incr eqs;
    K.eq a b
  ;;

  let lookup k m =
    incr lookups;
    match m with
    | None -> raise (Failure "lookup: not found")
    | Some m -> B.lookup k m
  ;;

  let bind k x m =
    incr binds;
    Some (B.bind k x (Option.value m ~default:B.empty))
  ;;

  (* The lookups, binds and key comparisons [f] makes. *)
  let calls f =
    lookups := 0;
    binds := 0;
    eqs := 0;
    ignore (f ());
    !lookups, !binds, !eqs
  ;;
end

module Chars_wide = Widened (Char_ordered)
module Ints_wide = Widened (Counting_int)
module Chars_compressed = PathCompressionTrie (Chars_wide)
module Words_compressed = PathCompressionTrie (Chars_compressed)
module Ints_compressed = PathCompressionTrie (Ints_wide)
module Chars_compressed_contract = Trie_contract (Chars_compressed)
module Words_compressed_contract = Trie_contract (Words_compressed)
module Ints_compressed_contract = Trie_contract (Ints_compressed)
module Chars_compressed_book = Book_trie (Chars_compressed)
module Words_compressed_sentences = Sentences (Words_compressed)
module Ints_compressed_clocks = Trie_clocks (Ints_compressed)

(* The compressed trie's own share of a level: a four-word node, the walk's answer, up to
   six words when it carries the string read, and the two-word option the base map here
   is wrapped in. *)
let compressed_node_words = 12.0

let test_compressed_contract () =
  Chars_compressed_contract.run
    "PathCompressionTrie (UnbalancedMap (char))"
    ~universe:(lists_upto [ 'a'; 'b'; 'c' ] 3);
  Chars_compressed_contract.run
    "PathCompressionTrie (UnbalancedMap (char)), keys of up to six over a and b"
    ~universe:(lists_upto [ 'a'; 'b' ] 6);
  Words_compressed_contract.run
    "PathCompressionTrie (PathCompressionTrie (UnbalancedMap (char)))"
    ~universe:(lists_upto (List.map explode [ "a"; "an"; "cat"; "dog" ]) 2);
  Ints_compressed_contract.run
    "PathCompressionTrie (UnbalancedMap (int))"
    ~universe:(lists_upto [ 0; 1; 2 ] 3)
;;

(* What makes the trie a base map itself: equality of its keys, and emptiness. *)
let test_compressed_wide () =
  let t label = "PathCompressionTrie (UnbalancedMap (char)), as a base map: " ^ label in
  let module T = Chars_compressed in
  let eq a b = T.key_eq (explode a) (explode b) in
  check (t "the empty trie is empty") (T.is_empty T.empty);
  check
    (t "a trie holding only the empty key is not")
    (not (T.is_empty (T.bind [] 0 T.empty)));
  check (t "nor is one holding cat") (not (T.is_empty (T.bind (explode "cat") 0 T.empty)));
  check (t "cat equals cat, and the empty key itself") (eq "cat" "cat" && eq "" "");
  check
    (t "but not cut, ca, cats or the empty key, either way round")
    (not (List.exists (fun s -> eq "cat" s || eq s "cat") [ "cut"; "ca"; "cats"; "" ]))
;;

(* The longest common prefix of two keys. *)
let rec common a b =
  match a, b with
  | x :: xs, y :: ys when x = y -> x :: common xs ys
  | _ -> []
;;

(* Where the nodes of the compressed trie of [keys] sit: at the longest common prefix of
   each pair of keys, a key paired with itself included. *)
let sites keys =
  List.sort_uniq compare (List.concat_map (fun a -> List.map (common a) keys) keys)
;;

(* The edges on the way to [k]: one out of every node above it. *)
let edges sites k = List.length (List.filter (fun s -> s <> k && common s k = s) sites)

let test_compressed_shape () =
  let name =
    "PathCompressionTrie (UnbalancedMap (char)), keys of up to six over a and b"
  in
  let universe = lists_upto [ 'a'; 'b' ] 6 in
  let pick () = List.nth universe (Random.int (List.length universe)) in
  let show k = Printf.sprintf "%S" (String.of_seq (List.to_seq k)) in
  let lookups_off = ref []
  and binds_off = ref [] in
  Random.init 20261015;
  for _ = 1 to 200 do
    let m = ref Chars_compressed.empty
    and keys = ref [] in
    for i = 1 to 30 do
      let k = pick () in
      if not (List.mem k !keys) then keys := k :: !keys;
      let sites = sites !keys in
      let e = edges sites k in
      let _, b, _ = Chars_wide.calls (fun () -> m := Chars_compressed.bind k i !m) in
      if b < e || b > e + 1
      then
        binds_off
        := Printf.sprintf
             "bound %s in %d base-map binds, %d edges on its way"
             (show k)
             b
             e
           :: !binds_off;
      List.iter
        (fun k ->
           let l, _, c = Chars_wide.calls (fun () -> Chars_compressed.lookup k !m) in
           let e = edges sites k in
           if l <> e || c > List.length k - e
           then
             lookups_off
             := Printf.sprintf
                  "found %s in %d base-map lookups and %d comparisons, %d edges on its \
                   way"
                  (show k)
                  l
                  c
                  e
                :: !lookups_off)
        !keys
    done
  done;
  check
    (Printf.sprintf
       "%s: after every bind of 200 random workloads, every key bound is found in one \
        base-map lookup for every node of the compressed trie above it, its other \
        elements compared once each%s"
       name
       (first_of Fun.id !lookups_off))
    (!lookups_off = []);
  check
    (Printf.sprintf
       "%s: and every bind remakes the edges on its key's way, and one more when it \
        hangs an old node under a new one%s"
       name
       (first_of Fun.id !binds_off))
    (!binds_off = [])
;;

(* A key of [n] elements, [head] and then zeros. *)
let zeros_after head n = head :: List.init (n - 1) (fun _ -> 0)

(* [k] with its element at [i] made [x]. *)
let with_at i x k = List.mapi (fun j y -> if j = i then x else y) k

let test_compressed_long_keys () =
  let t label =
    "PathCompressionTrie (UnbalancedMap (int)), four keys of n elements, 0..3 then \
     zeros, at n = 10 and 100000: "
    ^ label
  in
  let module T = Ints_compressed in
  let trie n =
    Ints_compressed_contract.of_list (List.init 4 (fun d -> zeros_after d n, 0))
  in
  let tries = [ 10, trie 10; 100_000, trie 100_000 ] in
  (* [f] on the trie of each length with its key, the key built outside the clocks:
     the comparisons and words it spends, and its base-map calls. *)
  let at key f =
    List.map
      (fun (n, m) ->
         let k = key n in
         let c, w = spent_only (fun () -> f k m) in
         let l, b, _ = Ints_wide.calls (fun () -> f k m) in
         c, w, l, b)
      tries
  in
  let report (c, w, l, b) =
    Printf.sprintf "%.0f comparisons, %.0f words, %d lookups, %d binds" c w l b
  in
  let both = function
    | [ short; long ] -> short, long
    | _ -> assert false
  in
  (* A lookup of the last key: one edge, and the rest read one comparison an element. *)
  let ((c10, w10, l10, _) as short), ((c100k, w100k, l100k, _) as long) =
    both (at (zeros_after 3) (fun k m -> T.lookup k m))
  in
  check
    (t
       (Printf.sprintf
          "a lookup of the last key passes one edge and reads the rest of the key one \
           comparison an element, allocating the same at both lengths: %s, and %s"
          (report short)
          (report long)))
    (l10 = 1 && l100k = 1 && c100k -. c10 = 99_990.0 && w10 = w100k);
  List.iter
    (fun (what, key, f, binds) ->
       let ((c10, w10, _, b10) as short), ((c100k, w100k, _, b100k) as long) =
         both (at key f)
       in
       check
         (t
            (Printf.sprintf
               "%s costs the same at both lengths: %s, and %s"
               what
               (report short)
               (report long)))
         (c10 = c100k && w10 = w100k && b10 = binds && b100k = binds))
    [ ( "a miss at the second element"
      , (fun n -> with_at 1 1 (zeros_after 3 n))
      , (fun k m -> ignore (Ints_compressed_contract.lookup_opt k m))
      , 0 )
    ; ( "a bind of a new key off the root, one edge made"
      , zeros_after 4
      , (fun k m -> ignore (T.bind k 1 m))
      , 1 )
    ; ( "a bind of a key parting from a string at its sixth element, an edge remade and \
         two made"
      , (fun n -> with_at 5 1 (zeros_after 3 n))
      , (fun k m -> ignore (T.bind k 1 m))
      , 3 )
    ];
  (* A rebind of the last key: the whole key read once. *)
  let ((c10, _, _, b10) as short), ((c100k, _, _, b100k) as long) =
    both (at (zeros_after 3) (fun k m -> ignore (T.bind k 1 m)))
  in
  check
    (t
       (Printf.sprintf
          "a rebind of the last key remakes one edge and reads the rest of the key one \
           comparison an element: %s, and %s"
          (report short)
          (report long)))
    (b10 = 1 && b100k = 1 && c100k -. c10 = 99_990.0)
;;

let test_compressed () =
  test_compressed_contract ();
  Chars_compressed_book.run "PathCompressionTrie (UnbalancedMap (char))";
  Words_compressed_sentences.run
    "PathCompressionTrie (PathCompressionTrie (UnbalancedMap (char)))";
  test_compressed_wide ();
  test_compressed_shape ();
  test_compressed_long_keys ();
  Ints_compressed_clocks.run
    ~node_words:compressed_node_words
    "PathCompressionTrie (UnbalancedMap (int))"
;;

(* ------------------------------------------------ HashTable (Exercise 10.11) *)

(* Exercise 10.11 (Schwenke) stacks two finite maps: an Approx map keyed by the hash of
   a key, whose every entry is a bucket, an Exact map keyed by the key itself, holding
   the keys that share that hash. A lookup hashes its key, finds the bucket in Approx and
   the key in the bucket; a bind does the same and puts the bucket back, a fresh one when
   the hash had none. The advantage the book claims is the division of labour: Approx can
   be keyed by something cheap to compare, integers, and Exact can be trivial, an
   association list, since all it ever sees is one bucket.

   Here Approx is Chapter 2's map over integers and Exact an association list over
   strings that tells keys apart by equality alone, both counting the calls made to them,
   the list its string comparisons too; the hash counts its calls. Four hashes: the
   length of the string, so that buckets are shared; OCaml's Hashtbl.hash, which spreads
   the keys out; the same modulo 64, buckets that fill as the table grows; and a
   constant, one bucket for all, which makes the table its association list. The contract
   is Figure 10.10's, any finite map's, over every string of up to three letters over a,
   b and c, for three of the hashes. Then collisions spelled out: two keys of one bucket,
   a miss inside a bucket and a miss with no bucket, a rebind, and a new key in a shared
   bucket. Then the structure, by its calls, under the same three: every lookup and every
   bind hashes its key once and makes one Approx lookup; a lookup that finds its key
   makes one Exact lookup, a miss at most one; a bind makes one Exact bind and one
   Approx bind, whether the bucket was there or not, and no Exact lookup. Last the claim
   itself, over n decimal strings at n = 100 and 10000: a lookup or a rebind compares its
   key with the keys of its own bucket and no others. Measured: under Hashtbl.hash no two
   of the strings share a bucket and every lookup and rebind compares one string at
   either size; modulo 64 the widest bucket holds 6 keys at n = 100 and 183 at 10000,
   and the dearest lookup or rebind compares exactly that many. *)

(* Exercise 10.11's trivial Exact map: an association list over strings, its keys told
   apart by equality alone, every comparison counted. *)
let string_eqs = ref 0

module Assoc = struct
  type key = string
  type 'a map = (string * 'a) list

  let empty = []

  let same a b =
    incr string_eqs;
    String.equal a b
  ;;

  let lookup k m =
    match List.find_opt (fun (k', _) -> same k k') m with
    | Some (_, v) -> v
    | None -> raise (Failure "lookup: not found")
  ;;

  let bind k x m = (k, x) :: List.filter (fun (k', _) -> not (same k k')) m
end

module Approx = Counting_map (Base)
module Exact = Counting_map (Assoc)

let hashes = ref 0

(* A hash that counts its calls. *)
module Hashing (F : sig
    val hash : string -> int
  end) =
struct
  let hash k =
    incr hashes;
    F.hash k
  ;;
end

module Length_hash = struct
  let hash = String.length
end

module Spread_hash = struct
  let hash = Hashtbl.hash
end

module Hash_64 = struct
  let hash k = Hashtbl.hash k mod 64
end

module Constant_hash = struct
  let hash _ = 0
end

module By_length = HashTable (Approx) (Exact) (Hashing (Length_hash))
module By_spread = HashTable (Approx) (Exact) (Hashing (Spread_hash))
module By_64 = HashTable (Approx) (Exact) (Hashing (Hash_64))
module One_bucket = HashTable (Approx) (Exact) (Hashing (Constant_hash))

(* Figure 10.10's contract is any finite map's. *)
module By_length_contract = Trie_contract (By_length)
module By_spread_contract = Trie_contract (By_spread)
module One_bucket_contract = Trie_contract (One_bucket)

let implode k = String.of_seq (List.to_seq k)
let hash_universe = List.map implode (lists_upto [ 'a'; 'b'; 'c' ] 3)

let test_hash_contract () =
  By_length_contract.run "HashTable, hashed by length" ~universe:hash_universe;
  By_spread_contract.run "HashTable, hashed by Hashtbl.hash" ~universe:hash_universe;
  One_bucket_contract.run "HashTable, one bucket for all" ~universe:hash_universe
;;

(* Collisions spelled out, hashed by length: ab and ba share a bucket. *)
let test_hash_collisions () =
  let t label = "HashTable, hashed by length: " ^ label in
  let at = By_length.lookup in
  let m = By_length_contract.of_list [ "ab", 1; "ba", 2; "abc", 3 ] in
  check_int (t "ab") ~expect:1 ~actual:(at "ab" m);
  check_int (t "ba, in the same bucket") ~expect:2 ~actual:(at "ba" m);
  check_failure
    (t "ca, missing from a bucket that is there")
    "lookup: not found"
    (fun () -> at "ca" m);
  check_failure (t "abcd, with no bucket at all") "lookup: not found" (fun () ->
    at "abcd" m);
  let m' = By_length.bind "ab" 10 m in
  check_int (t "rebinding ab replaces its value") ~expect:10 ~actual:(at "ab" m');
  check_int (t "and keeps ba beside it") ~expect:2 ~actual:(at "ba" m');
  let m'' = By_length.bind "cc" 5 m in
  check_int (t "cc, bound into the shared bucket") ~expect:5 ~actual:(at "cc" m'');
  check_int (t "keeps ab") ~expect:1 ~actual:(at "ab" m'');
  check_int (t "and ba") ~expect:2 ~actual:(at "ba" m'');
  check_int (t "while the original still has ab at 1") ~expect:1 ~actual:(at "ab" m);
  check_failure (t "and no cc") "lookup: not found" (fun () -> at "cc" m)
;;

(* The calls [f] makes: hashes, Approx lookups and binds, Exact lookups and binds. *)
let hash_calls f =
  hashes := 0;
  Approx.lookups := 0;
  Approx.binds := 0;
  Exact.lookups := 0;
  Exact.binds := 0;
  ignore (f ());
  !hashes, (!Approx.lookups, !Approx.binds), (!Exact.lookups, !Exact.binds)
;;

let show_calls (h, (al, ab), (el, eb)) =
  Printf.sprintf
    "%d hashes, Approx %d lookups and %d binds, Exact %d lookups and %d binds"
    h
    al
    ab
    el
    eb
;;

(* What a table spends on each kind of key, by its calls. *)
module Hash_calls (T : FINITE_MAP with type key = string) = struct
  module C = Trie_contract (T)

  let run name =
    let t label = name ^ ": " ^ label in
    let m = C.of_list (List.map (fun k -> k, 0) hash_universe) in
    let each what keys f ok =
      all_of (t what) (fun note ->
        List.iter
          (fun k ->
             let c = hash_calls (fun () -> f k) in
             if not (ok c) then note (Printf.sprintf "%S: %s" k (show_calls c)))
          keys)
    in
    let found k = T.lookup k m
    and missed k = C.lookup_opt k m
    and bound k = T.bind k 1 m in
    each
      "every key bound is found in one hash, one Approx lookup and one Exact lookup"
      hash_universe
      found
      (fun c -> c = (1, (1, 0), (1, 0)));
    each
      "a key not bound misses in one hash and one Approx lookup, and at most one Exact \
       lookup"
      [ "d"; "dd"; "ddd"; "abcd"; "dddd" ]
      missed
      (fun (h, (al, ab), (el, eb)) -> h = 1 && al = 1 && ab = 0 && el <= 1 && eb = 0);
    each
      "every bind, of a key bound or not, is one hash, one Approx lookup, one Exact bind \
       and one Approx bind"
      (hash_universe @ [ "d"; "dd"; "ddd"; "abcd"; "dddd" ])
      bound
      (fun c -> c = (1, (1, 1), (0, 1)))
  ;;
end

module By_length_calls = Hash_calls (By_length)
module By_spread_calls = Hash_calls (By_spread)
module One_bucket_calls = Hash_calls (One_bucket)

(* The claim: Exact sees one bucket. Over n decimal strings, every lookup and every
   rebind compares its key with no more keys than share its hash. *)
module Hash_buckets
    (T : FINITE_MAP with type key = string)
    (F : sig
       val hash : string -> int
     end) =
struct
  module C = Trie_contract (T)

  let run name =
    List.iter
      (fun n ->
         let t label = Printf.sprintf "%s, %d decimal strings: %s" name n label in
         let keys = List.init n string_of_int in
         let m = C.of_list (List.map (fun k -> k, 0) keys) in
         let sizes = Hashtbl.create n in
         List.iter
           (fun k ->
              let h = F.hash k in
              Hashtbl.replace
                sizes
                h
                (1 + Option.value (Hashtbl.find_opt sizes h) ~default:0))
           keys;
         let size k = Hashtbl.find sizes (F.hash k) in
         let eqs f =
           string_eqs := 0;
           ignore (f ());
           !string_eqs
         in
         let widest = ref 0
         and dearest = ref 0 in
         all_of
           (t
              "every lookup and every rebind compares its key only with its bucket's keys")
           (fun note ->
              List.iter
                (fun k ->
                   let s = size k
                   and l = eqs (fun () -> T.lookup k m)
                   and b = eqs (fun () -> T.bind k 1 m) in
                   widest := max !widest s;
                   dearest := max !dearest (max l b);
                   if l > s || b > s
                   then
                     note
                       (Printf.sprintf
                          "%S, in a bucket of %d, compared %d times to look up and %d to \
                           rebind"
                          k
                          s
                          l
                          b))
                keys);
         check
           (t
              (Printf.sprintf
                 "the dearest of them compares %d, the widest bucket holding %d keys"
                 !dearest
                 !widest))
           (!dearest <= !widest))
      [ 100; 10_000 ]
  ;;
end

module By_spread_buckets = Hash_buckets (By_spread) (Spread_hash)
module By_64_buckets = Hash_buckets (By_64) (Hash_64)

let test_hash_table () =
  test_hash_contract ();
  test_hash_collisions ();
  By_length_calls.run "HashTable, hashed by length";
  By_spread_calls.run "HashTable, hashed by Hashtbl.hash";
  One_bucket_calls.run "HashTable, one bucket for all";
  By_spread_buckets.run "HashTable, hashed by Hashtbl.hash";
  By_64_buckets.run "HashTable, hashed by Hashtbl.hash mod 64"
;;

let tests =
  [ case "[Figure 10.1] AltBinaryRandomAccessListFigure" test_alt
  ; case "[Exercise 10.2] AltBinaryRandomAccessList" test_alt_lazy
  ; case "[Figure 10.2] BootstrappedQueueFigure" test_bootstrapped
  ; case "[Exercise 10.4] BootstrappedQueueNoPolymorphicRecursion" test_no_poly
  ; case "[Exercise 10.5] BootstrappedQueuePrimQ" test_prim
  ; case "[Figure 10.6] CatenableList" test_cat
  ; case "[Exercise 10.6] flatten" test_flatten
  ; case "[Figure 10.7] BootstrapFigure" test_boot
  ; case "[Exercise 10.8(a)] LazyBinomialHeapWithInfo" test_lazy_info
  ; case "[Exercise 10.8(b)] Bootstrap" test_boot_info
  ; case "[Figure 10.10] TrieFigure" test_trie
  ; case "[Exercise 10.9] EntryTrie" test_entry_trie
  ; case "[Exercise 10.10] PathCompressionTrie" test_compressed
  ; case "[Exercise 10.11] HashTable" test_hash_table
  ]
;;
