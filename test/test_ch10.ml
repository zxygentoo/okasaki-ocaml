(* Tests for Chapter 10: the binary random-access list of Figure 10.1 (section 10.1.2),
   its lazy form of Exercise 10.2, and the bootstrapped queue of Figure 10.2 (section
   10.1.3) and its forms without polymorphic recursion of Exercises 10.4 and 10.5, and
   the catenable list of Figure 10.6 (section 10.2.1), each with its own preamble below. Alcotest cases written in the checks of harness.ml, as in the earlier
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

let tests =
  [ case "[Figure 10.1] AltBinaryRandomAccessListFigure" test_alt
  ; case "[Exercise 10.2] AltBinaryRandomAccessList" test_alt_lazy
  ; case "[Figure 10.2] BootstrappedQueueFigure" test_bootstrapped
  ; case "[Exercise 10.4] BootstrappedQueueNoPolymorphicRecursion" test_no_poly
  ; case "[Exercise 10.5] BootstrappedQueuePrimQ" test_prim
  ; case "[Figure 10.6] CatenableList" test_cat
  ]
;;
