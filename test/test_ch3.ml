(* Tests for Chapter 3, section 3.1: leftist heaps, and the weight-biased variant of
   Exercise 3.4. Alcotest cases written in the checks of harness.ml, as in test_ch2.ml.

   Both heaps are sealed behind HEAP, so a test cannot look at a tree. It does not need
   to. Every cost the book states in this section is a statement about the length of a
   right spine, and merge spends exactly one element comparison per step down that spine,
   so an instrumented ORDERED measures the shape from outside.

   That gives the central measurement, [rank_of]: merging h with a singleton holding
   max_int walks h's right spine to the bottom, comparing once per node, and stops without
   comparing when it reaches Empty. The comparison count IS the spine length. Exercise 3.1
   bounds that by floor(log2 (n+1)) for leftist heaps and Exercise 3.4(a) by the same for
   weight-biased ones -- and the leftist property is precisely what makes the bound hold,
   so asserting it is how a sealed heap gets its invariant checked.

   Costs asserted here, because they are the exercise rather than a nicety: the 3.1 spine
   bound, O(log n) for merge, insert and delete_min, O(1) for find_min, and 3.3's O(n) for
   from_list -- which is the whole point of merging in log n passes instead of folding. *)

open Okasaki.Ch3
open Harness

(* The bound Exercises 3.1 and 3.4(a) both put on a right spine. *)
let spine_bound n = floor_log2 (n + 1)

(* Insertion orders that stress the shape differently. Ascending sends every element down
   the right spine, which is the order that grows it; descending sends every element
   straight to the root; equal elements exercise the leq boundary. *)
let orders n =
  let seeded f =
    Random.init 20260918;
    List.init n f
  in
  [ "ascending", upto n
  ; "descending", List.init n (fun i -> n - i)
  ; "all equal", List.init n (fun _ -> 7)
  ; "sawtooth", List.init n (fun i -> if i mod 2 = 0 then i else n - i)
  ; "random", seeded (fun _ -> Random.int 1000)
  ]
;;

(* ------------------------------------------------------ shared heap contract *)

(* Every test below is written against HEAP alone, so both implementations are held to the
   same behaviour and the same bounds. *)
module Heap_tests (H : HEAP with type Element.t = int) = struct
  let of_list xs = List.fold_left (fun h x -> H.insert x h) H.empty xs

  (* find_min/delete_min to exhaustion. That this comes out sorted is the whole
     behavioural specification of a heap. *)
  let drain h = drain_with ~is_empty:H.is_empty ~head:H.find_min ~tail:H.delete_min h

  (* The length of h's right spine, measured through the sealed signature. max_int is >=
     every element, so merge takes the h side at every step and walks the spine to Empty,
     comparing exactly once per node on the way. The singleton is built before [count]
     resets the counter, and insert into an empty heap compares nothing anyway. *)
  let rank_of h =
    let big = H.insert max_int H.empty in
    count_only (fun () -> H.merge h big)
  ;;

  (* Every heap owes this, whatever its shape. *)
  let run_contract name =
    let t label = Printf.sprintf "%s: %s" name label in
    check (t "empty is empty") (H.is_empty H.empty);
    check (t "a singleton is not empty") (not (H.is_empty (H.insert 1 H.empty)));
    check_failure (t "find_min on empty raises") "find_min: empty heap" (fun () ->
      H.find_min H.empty);
    check_failure (t "delete_min on empty raises") "delete_min: empty heap" (fun () ->
      ignore (H.is_empty (H.delete_min H.empty)));
    check_int (t "find_min of a singleton") ~expect:5 ~actual:(H.find_min (of_list [ 5 ]));
    check
      (t "delete_min of a singleton is empty")
      (H.is_empty (H.delete_min (of_list [ 5 ])));
    check_eq
      (t "drain is sorted")
      ~expect:[ 1; 2; 3; 4; 5; 6; 7 ]
      ~actual:(drain (of_list [ 4; 2; 6; 1; 3; 5; 7 ]))
      string_of_int_list;
    (* A heap is a multiset, not a set: an implementation that quietly drops a duplicate
       still passes every distinct-element test. *)
    check_eq
      (t "duplicates are all kept")
      ~expect:[ 1; 1; 1; 2; 2; 3 ]
      ~actual:(drain (of_list [ 2; 1; 3; 1; 2; 1 ]))
      string_of_int_list;
    check_eq
      (t "merge is multiset union")
      ~expect:[ 1; 2; 3; 4; 5; 6 ]
      ~actual:(drain (H.merge (of_list [ 1; 4; 6 ]) (of_list [ 2; 3; 5 ])))
      string_of_int_list;
    check_eq
      (t "merge with an empty right operand")
      ~expect:[ 1; 2; 3 ]
      ~actual:(drain (H.merge (of_list [ 3; 1; 2 ]) H.empty))
      string_of_int_list;
    check_eq
      (t "merge with an empty left operand")
      ~expect:[ 1; 2; 3 ]
      ~actual:(drain (H.merge H.empty (of_list [ 3; 1; 2 ])))
      string_of_int_list;
    check (t "merge of two empties is empty") (H.is_empty (H.merge H.empty H.empty));
    (* Randomised, against List.sort as the reference. *)
    Random.init 20260918;
    let bad_insert = ref 0
    and bad_merge = ref 0 in
    for _ = 0 to 299 do
      let n = Random.int 40 in
      let xs = List.init n (fun _ -> Random.int 50) in
      let sorted = List.sort compare xs in
      if drain (of_list xs) <> sorted then incr bad_insert;
      let m = Random.int 40 in
      let ys = List.init m (fun _ -> Random.int 50) in
      if drain (H.merge (of_list xs) (of_list ys)) <> List.sort compare (xs @ ys)
      then incr bad_merge
    done;
    check_int (t "insert then drain, 300 random lists") ~expect:0 ~actual:!bad_insert;
    check_int (t "merge then drain, 300 random pairs") ~expect:0 ~actual:!bad_merge;
    (* Persistence: no operation may disturb its operands. *)
    let h = of_list [ 5; 3; 8; 1 ] in
    let expect = [ 1; 3; 5; 8 ] in
    let _ = H.insert 0 h
    and _ = H.delete_min h
    and _ = H.merge h h in
    check_eq (t "operands are untouched") ~expect ~actual:(drain h) string_of_int_list
  ;;

  (* Leftist heaps only: rank_of measures a RIGHT SPINE by merging with a large singleton.
     Against a binomial heap the same call counts carries instead, so the bound it is
     compared to would be measuring the wrong thing. *)
  let run_structure name =
    let t label = Printf.sprintf "%s: %s" name label in
    (* ------------------------------------------ 3.1 / 3.4(a): the spine bound *)
    (* This is the structural invariant. A heap that lost the leftist property would keep
       draining in sorted order but grow a spine past the bound, so this is the check that
       the behavioural tests above cannot make. *)
    let over = ref [] in
    List.iter
      (fun n ->
        List.iter
          (fun (how, xs) ->
            let r = rank_of (of_list xs) in
            if r > spine_bound n
            then
              over
              := Printf.sprintf "%s/insert n=%d rank=%d>%d" how n r (spine_bound n)
                 :: !over)
          (orders n))
      [ 1; 2; 3; 4; 7; 8; 15; 16; 17; 100; 511; 512; 1000 ];
    check
      (t
         (Printf.sprintf
            "right spine <= floor(log2 (n+1)) over every shape%s"
            (match !over with
             | [] -> ""
             | b :: _ -> " -- " ^ b)))
      (!over = []);
    (* The bound must survive deletion, not just construction: delete_min merges the two
       children, so a merge that picks the wrong side shows up here and nowhere in a
       drain, which stays sorted regardless. Every shape is swept, because which side is
       wrong depends on the tree. *)
    let rec shrink h remaining bad =
      if H.is_empty h
      then bad
      else
        shrink
          (H.delete_min h)
          (remaining - 1)
          (bad + if rank_of h > spine_bound remaining then 1 else 0)
    in
    check_int
      (t "the bound holds after every delete_min")
      ~expect:0
      ~actual:
        (List.fold_left
           (fun acc n ->
             List.fold_left
               (fun acc (_, xs) -> acc + shrink (of_list xs) n 0)
               acc
               (orders n))
           0
           [ 33; 300 ]);
    (* -------------------------------------- O(log n) for merge, insert, delete *)
    (* Every cost below is logarithmic only because that bound holds, and the two checks
       above are the guard on them: a case ends at its first failure. Without the leftist
       property of_list builds a linear spine, insert degrades to O(n), and a
       100_000-element heap takes O(n^2) to build -- a cost check that ran anyway would
       answer a regression by hanging for minutes instead of reporting it. *)
    (* merge walks the two right spines and merges them like sorted lists, so it cannot
       cost more than their combined length -- which the bound above makes logarithmic. *)
    let pairs = [ 1, 1; 1, 100; 100, 1; 63, 64; 64, 64; 1000, 7; 500, 500 ] in
    let bad_sum = ref 0
    and bad_log = ref 0 in
    List.iter
      (fun (n1, n2) ->
        let h1 = of_list (upto n1)
        and h2 = of_list (upto n2) in
        let r1 = rank_of h1
        and r2 = rank_of h2 in
        let c = count_only (fun () -> H.merge h1 h2) in
        if c > r1 + r2 then incr bad_sum;
        if c > spine_bound n1 + spine_bound n2 then incr bad_log)
      pairs;
    check_int (t "merge costs at most rank h1 + rank h2") ~expect:0 ~actual:!bad_sum;
    check_int (t "merge is O(log n)") ~expect:0 ~actual:!bad_log;
    (* insert walks the right spine until the new element settles; the worst case is an
       element larger than every other, which reaches the bottom. *)
    let bad_insert_cost = ref 0 in
    List.iter
      (fun n ->
        let h = of_list (upto n) in
        let c = count_only (fun () -> H.insert max_int h) in
        if c > spine_bound n then incr bad_insert_cost)
      [ 1; 7; 8; 100; 1000; 10_000 ];
    check_int (t "insert is O(log n), worst case") ~expect:0 ~actual:!bad_insert_cost;
    (* delete_min merges the two children, each with a spine bounded by the parent's. *)
    let bad_delete = ref 0 in
    List.iter
      (fun n ->
        let h = of_list (upto n) in
        let c = count_only (fun () -> H.delete_min h) in
        if c > 2 * spine_bound n then incr bad_delete)
      [ 1; 7; 8; 100; 1000; 10_000 ];
    check_int (t "delete_min is O(log n)") ~expect:0 ~actual:!bad_delete;
    (* find_min reads the root: no comparison and no allocation, at any size. *)
    let bad_find = ref 0 in
    List.iter
      (fun n ->
        let h = of_list (upto n) in
        if count_only (fun () -> H.find_min h) <> 0 then incr bad_find;
        if allocated (fun () -> H.find_min h) > 4.0 then incr bad_find)
      [ 1; 100; 100_000 ];
    check_int (t "find_min is O(1)") ~expect:0 ~actual:!bad_find
  ;;
end

(* from_list is Exercise 3.3, a leftist-heap exercise, and deliberately not part of HEAP:
   only the modules that actually implement it are held to this contract. *)
module From_list_tests (H : HEAP_WITH_FROM_LIST with type Element.t = int) = struct
  module Base = Heap_tests (H)

  let of_list = Base.of_list
  let drain = Base.drain

  let run name =
    let t label = Printf.sprintf "%s: %s" name label in
    check (t "from_list []") (H.is_empty (H.from_list []));
    check_eq
      (t "from_list [7]")
      ~expect:[ 7 ]
      ~actual:(drain (H.from_list [ 7 ]))
      string_of_int_list;
    (* An odd length is where a pairwise pass can drop the unpaired heap. *)
    check_eq
      (t "from_list of an odd number of elements")
      ~expect:[ 1; 2; 3; 4; 5 ]
      ~actual:(drain (H.from_list [ 3; 1; 5; 2; 4 ]))
      string_of_int_list;
    (* Randomised against List.sort. Sizes straddle the powers of two where the pairwise
       passes leave an odd heap over. *)
    Random.init 20260918;
    let bad = ref 0 in
    for _ = 0 to 299 do
      let n = Random.int 40 in
      let xs = List.init n (fun _ -> Random.int 50) in
      if drain (H.from_list xs) <> List.sort compare xs then incr bad
    done;
    check_int (t "from_list then drain, 300 random lists") ~expect:0 ~actual:!bad
  ;;

  (* ------------------------------------------------------- 3.3: from_list is O(n) *)

  (* Merging in log n passes costs sum over k of (n/2^k) merges of O(k) each, which
     converges: about 2n comparisons in total, independent of n. Folding insert over the
     list instead -- the approach the exercise rules out -- costs sum of log i, which is
     Theta(n log n). Comparisons are the right unit here because they count exactly the
     steps down the spines that both approaches are made of. *)
  let scrambled n =
    Random.init 20260918;
    List.init n (fun _ -> Random.int 1_000_000)
  ;;

  let from_list_cost n = count_only (fun () -> H.from_list (scrambled n))
  let fold_cost n = count_only (fun () -> of_list (scrambled n))

  let run_cost name =
    let t label = Printf.sprintf "%s: %s" name label in
    let per n c = float_of_int c /. float_of_int n in
    let small = 1_000 in
    let c_small = from_list_cost small in
    check
      (t
         (Printf.sprintf
            "from_list does O(n) comparisons at n=%d (%.2f per element)"
            small
            (per small c_small)))
      (c_small <= 4 * small);
    (* The small size guards the large one, as in test_ch2: if from_list is not linear,
       the check above has ended the case rather than spend minutes proving it again. *)
    let large = 100_000 in
    let c_large = from_list_cost large in
    check
      (t
         (Printf.sprintf
            "from_list stays O(n) at n=%d (%.2f per element)"
            large
            (per large c_large)))
      (c_large <= 4 * large);
    (* The cost per element must not grow with n. An O(n log n) from_list would rise by a
       factor of log(100000)/log(1000) here, about 1.66. *)
    check
      (t
         (Printf.sprintf
            "cost per element is flat from n=%d to n=%d (%.2f -> %.2f)"
            small
            large
            (per small c_small)
            (per large c_large)))
      (per large c_large <= per small c_small *. 1.3);
    (* And it must actually beat the fold the exercise rules out. *)
    let c_fold = fold_cost large in
    check
      (t
         (Printf.sprintf
            "from_list beats folding insert at n=%d (%d vs %d comparisons)"
            large
            c_large
            c_fold))
      (c_large * 3 <= c_fold)
  ;;
end

(* Binomial heaps keep a different invariant, so they need a different instrument. There
   is no spine to measure; the structure IS the binary representation of n, so a heap of
   size n holds exactly popcount n trees -- one per 1 bit -- and at most floor(log2 (n+1))
   of them.

   remove_min_tree compares once per tree beyond the first, so find_min's comparison count
   is (trees - 1). That reads the tree count from outside the sealed signature, the way
   rank_of reads a spine length for leftist heaps. *)
module Binomial_tests (H : HEAP with type Element.t = int) = struct
  module Base = Heaps.Contract (H)

  let of_list = Base.of_list
  let trees h = count_only (fun () -> H.find_min h) + 1

  let run name =
    Base.run_tree_counts ~trees name;
    let t label = Printf.sprintf "%s: %s" name label in
    let bad_ins = ref 0 in
    List.iter
      (fun n ->
        let h = of_list (upto n) in
        if count_only (fun () -> H.insert max_int h) <> trailing_ones n then incr bad_ins)
      [ 1; 2; 3; 7; 8; 15; 31; 100; 255; 1000 ];
    check_int (t "insert links once per trailing 1 bit of n") ~expect:0 ~actual:!bad_ins;
    let bad_merge = ref 0 in
    List.iter
      (fun (n1, n2) ->
        let a = of_list (upto n1)
        and b = of_list (List.init n2 (fun i -> i + n1)) in
        if count_only (fun () -> H.merge a b) > spine_bound (n1 + n2) + 1
        then incr bad_merge)
      [ 1, 1; 7, 9; 63, 64; 100, 1000; 1023, 1023 ];
    check_int (t "merge is O(log n)") ~expect:0 ~actual:!bad_merge
  ;;
end

module L = LeftistHeap (Counting_int)
module W = WeightBiasedLeftistHeap (Counting_int)
module B = BinomialHeap (Counting_int)
module R = RanklessBinomialHeap (Counting_int)

(* Exercise 3.7 over a BINOMIAL base: that is the only setting where the functor's claim
   bites, since the wrapped find_min costs one comparison per tree. *)
module X = ExplicitMin (B)
module Leftist = Heap_tests (L)
module Weighted = Heap_tests (W)
module Binom = Heap_tests (B)
module Rankless = Heap_tests (R)
module Explicit = Heap_tests (X)
module Binom_struct = Binomial_tests (B)
module Rankless_struct = Binomial_tests (R)
module Leftist_from_list = From_list_tests (L)

let test_leftist () =
  Leftist.run_contract "LeftistHeap";
  Leftist.run_structure "LeftistHeap"
;;

let test_weighted () =
  Weighted.run_contract "WeightBiasedLeftistHeap";
  Weighted.run_structure "WeightBiasedLeftistHeap"
;;

let test_binomial () =
  Binom.run_contract "BinomialHeap";
  Binom_struct.run "BinomialHeap"
;;

(* PERFORMANCE (3.5): "define findMin directly rather than via a call to removeMinTree".
   Comparisons cannot tell the two apart -- both compare once per tree -- so the claim has
   to be asserted as allocation. remove_min_tree rebuilds the residual list on the way
   back up, which grows with the number of trees; a direct scan builds nothing, so its
   cost stays flat as the heap grows. Only BinomialHeap is held to this: Rankless keeps
   the remove_min_tree route on purpose, to exercise its new signature. *)
let test_find_min_direct () =
  let heap_of n = Binom.of_list (List.init n (fun i -> i * 7919 mod 100_000)) in
  (* Guard against a vacuous check: if the probe cannot see allocation at all, everything
     below passes for the wrong reason. Building a heap certainly allocates. *)
  let probe = allocated (fun () -> heap_of 64) in
  check
    (Printf.sprintf
       "the allocation probe registers work (building a heap costs %.0f words)"
       probe)
    (probe > 0.0);
  (* one tree versus sixteen *)
  let h_small = heap_of 1
  and h_large = heap_of 65_535 in
  let w_small = allocated (fun () -> B.find_min h_small)
  and w_large = allocated (fun () -> B.find_min h_large) in
  check
    (Printf.sprintf
       "find_min allocation does not grow with the tree count (%.0f -> %.0f words)"
       w_small
       w_large)
    (w_large <= w_small +. 4.0);
  let worst =
    List.fold_left
      (fun acc n ->
        let h = heap_of n in
        Float.max acc (allocated (fun () -> B.find_min h)))
      0.0
      [ 1; 7; 255; 4095; 65_535 ]
  in
  check
    (Printf.sprintf "find_min allocates O(1) at every size (worst %.0f words)" worst)
    (worst <= 16.0)
;;

let test_rankless () =
  Rankless.run_contract "RanklessBinomialHeap";
  Rankless_struct.run "RanklessBinomialHeap"
;;

(* 3.7 asks for find_min in O(1) while insert, merge and delete_min stay O(log n). The
   first half is the claim worth asserting: zero comparisons at any size, against a base
   that pays one per tree. *)
let test_explicit_min () =
  Explicit.run_contract "ExplicitMin";
  Random.init 20260918;
  let bad = ref 0
  and base_paid = ref 0 in
  List.iter
    (fun n ->
      let xs = List.init n (fun _ -> Random.int 1_000_000) in
      let hx = Explicit.of_list xs
      and hb = Binom.of_list xs in
      if count_only (fun () -> X.find_min hx) <> 0 then incr bad;
      base_paid := !base_paid + count_only (fun () -> B.find_min hb))
    [ 1; 7; 15; 255; 4095; 65_535 ];
  check_int
    "ExplicitMin: find_min costs no comparisons at any size"
    ~expect:0
    ~actual:!bad;
  check
    (Printf.sprintf
       "ExplicitMin: the wrapped binomial find_min really does pay (%d comparisons)"
       !base_paid)
    (!base_paid > 0);
  (* insert and delete_min must stay logarithmic despite maintaining the cached min *)
  let over = ref 0 in
  List.iter
    (fun n ->
      let h = Explicit.of_list (upto n) in
      if count_only (fun () -> X.insert max_int h) > spine_bound n + 1 then incr over;
      if count_only (fun () -> X.delete_min h) > (2 * spine_bound n) + 2 then incr over)
    [ 1; 7; 8; 100; 1000; 10_000 ];
  check_int "ExplicitMin: insert and delete_min stay O(log n)" ~expect:0 ~actual:!over
;;

let test_from_list () =
  Leftist_from_list.run "LeftistHeap";
  Leftist_from_list.run_cost "LeftistHeap"
;;

(* Five implementations, five different shapes in memory, one observable behaviour. *)
let drains : (string * (int list -> int list)) list =
  [ ("LeftistHeap", fun xs -> Leftist.drain (Leftist.of_list xs))
  ; ("WeightBiasedLeftistHeap", fun xs -> Weighted.drain (Weighted.of_list xs))
  ; ("BinomialHeap", fun xs -> Binom.drain (Binom.of_list xs))
  ; ("RanklessBinomialHeap", fun xs -> Rankless.drain (Rankless.of_list xs))
  ; ("ExplicitMin", fun xs -> Explicit.drain (Explicit.of_list xs))
  ]
;;

let test_agreement () =
  Random.init 20260918;
  let bad = ref [] in
  for _ = 0 to 299 do
    let n = Random.int 60 in
    let xs = List.init n (fun _ -> Random.int 100) in
    let sorted = List.sort compare xs in
    List.iter (fun (nm, drain) -> if drain xs <> sorted then bad := nm :: !bad) drains
  done;
  check
    (Printf.sprintf
       "all %d implementations drain identically, 300 random lists%s"
       (List.length drains)
       (match !bad with
        | [] -> ""
        | b :: _ -> " -- " ^ b ^ " disagrees"))
    (!bad = [])
;;

(* ------------------------------------------ red-black trees (3.3) and 3.9 *)

(* RedBlackSet seals [set], so a test cannot look at a tree -- the same situation as the
   heaps above, and the same answer: measure it from outside through an instrumented
   ORDERED.

   The measurement is [path_to_gap]. Searching for an element that is NOT in the set walks
   from the root to an empty slot and stops there, and [steps] counts one per node on that
   path regardless of which way the search turned. So the number it returns is an exact
   depth. Probing every gap therefore finds the deepest path in the tree, which is exactly
   what Exercise 3.8 bounds: at most 2*floor(log2 (n+1)).

   Node colours are not asserted anywhere here, and cannot be: they are invisible through
   SET. Because from_ord_list fixes the shape from n alone, colouring every node black --
   or every node red, or dropping the root-blackening -- leaves every measurement below
   unchanged. What the colours buy is the depth bound as the tree keeps growing, so that
   is what gets asserted instead. Pinning Invariants 1 and 2 down directly would mean
   letting a test see the tree.

   Exercise 3.9 wants from_ord_list in O(n). Both halves of that are asserted in a
   deterministic form rather than by timing: it performs ZERO comparisons -- a sorted list
   has already answered every question insert would ask -- and its allocation per element
   does not grow with n. *)

module Rb = RedBlackSet (Counting_int)

let rb_of_list xs = List.fold_left (fun s x -> Rb.insert x s) Rb.empty xs

(* Nodes on the path from the root to the empty slot a failed search for [x] falls into. *)
let path_to_gap x s =
  steps := 0;
  if Rb.member x s then invalid_arg "path_to_gap: element is present";
  !steps
;;

(* The deepest path in a set holding [evens n]: probe all n+1 gaps, the two outside the
   range included. *)
let max_path n s =
  List.init (n + 1) (fun i -> (2 * i) - 1)
  |> List.fold_left (fun deepest x -> max deepest (path_to_gap x s)) 0
;;

(* Every path in a perfectly balanced tree of n nodes holds this many nodes, or one fewer. *)
let perfect_depth n = if n = 0 then 0 else floor_log2 n + 1

(* Exercise 3.8's bound on the depth of any node in a red-black tree of size n. *)
let depth_bound n = 2 * spine_bound n
let rb_sizes = [ 0; 1; 2; 3; 4; 7; 8; 15; 16; 31; 32; 100; 500; 1000 ]

let test_redblack () =
  check "member on the empty set is false" (not (Rb.member 0 Rb.empty));
  let s = rb_of_list (evens 50) in
  check
    "every inserted element is found"
    (List.for_all (fun x -> Rb.member x s) (evens 50));
  check
    "elements never inserted are not found"
    (List.init 51 (fun i -> (2 * i) - 1) |> List.for_all (fun x -> not (Rb.member x s)));
  (* What a set holds cannot depend on the order the elements arrived in. *)
  let s' = rb_of_list (shuffle 20260918 (evens 50)) in
  check
    "membership is independent of insertion order"
    (List.init 103 (fun i -> i - 1)
     |> List.for_all (fun x -> Rb.member x s = Rb.member x s'));
  (* Against an independent oracle, over many shapes. Everything above builds sets whose
     contents the test already knows by construction; this asks instead that whatever tree
     an arbitrary insertion order produced still answers like the list it came from. *)
  Random.init 20260919;
  let disagrees = ref 0 in
  for trial = 0 to 299 do
    let n = 1 + Random.int 40 in
    let xs =
      if trial mod 3 = 0
      then upto n (* ascending: the order that rebalances most *)
      else List.init n (fun _ -> Random.int 60)
    in
    let s = rb_of_list xs in
    for q = -2 to 62 do
      if Rb.member q s <> List.mem q xs then incr disagrees
    done
  done;
  check_int
    "member agrees with List.mem over 300 random trees"
    ~expect:0
    ~actual:!disagrees;
  (* Re-inserting an element must leave the set alone. An [ins] whose equal case returns
     the whole tree rather than the current subtree grafts the tree into itself here,
     dropping elements and duplicating the rest. *)
  let base = evens 7 in
  let once = rb_of_list base in
  let again =
    upto 20
    |> List.fold_left (fun s _ -> List.fold_left (fun s x -> Rb.insert x s) s base) once
  in
  check
    "re-inserting existing elements keeps every element"
    (List.for_all (fun x -> Rb.member x again) base);
  check
    "re-inserting existing elements adds nothing"
    (List.init 8 (fun i -> (2 * i) - 1) |> List.for_all (fun x -> not (Rb.member x again)));
  check_int
    "re-inserting existing elements leaves the shape alone"
    ~expect:(max_path 7 once)
    ~actual:(max_path 7 again);
  (* Exercise 3.8, over orders that stress the shape differently. This is the assertion
     that the two colour invariants exist to support: break balance and it fails. *)
  let over = ref [] in
  List.iter
    (fun n ->
      [ "ascending", evens n
      ; "descending", List.rev (evens n)
      ; "random", shuffle 20260918 (evens n)
      ]
      |> List.iter (fun (order, xs) ->
        let d = max_path n (rb_of_list xs) in
        if d > depth_bound n then over := (order, n, d) :: !over))
    rb_sizes;
  check
    (Printf.sprintf
       "depth stays within Exercise 3.8's 2*floor(log2 (n+1))%s"
       (match !over with
        | [] -> ""
        | (order, n, d) :: _ ->
          Printf.sprintf " -- %s n=%d reached %d, bound %d" order n d (depth_bound n)))
    (!over = []);
  (* member and insert are O(log n): at most two comparisons per level, over a path the
     bound above already limits. *)
  let costly = ref 0 in
  List.iter
    (fun n ->
      let s = rb_of_list (evens n) in
      if count_only (fun () -> Rb.member ((2 * n) - 1) s) > 2 * depth_bound n
      then incr costly;
      if count_only (fun () -> Rb.insert ((2 * n) + 1) s) > 2 * depth_bound n
      then incr costly)
    rb_sizes;
  check_int "member and insert stay O(log n)" ~expect:0 ~actual:!costly
;;

let test_from_ord_list () =
  check "from_ord_list [] is empty" (not (Rb.member 0 (Rb.from_ord_list [])));
  check "from_ord_list [x] holds x" (Rb.member 0 (Rb.from_ord_list [ 0 ]));
  (* Correctness: everything given is present, everything else is not. *)
  let wrong = ref 0 in
  List.iter
    (fun n ->
      let xs = evens n in
      let s = Rb.from_ord_list xs in
      if not (List.for_all (fun x -> Rb.member x s) xs) then incr wrong;
      if List.init (n + 1) (fun i -> (2 * i) - 1) |> List.exists (fun x -> Rb.member x s)
      then incr wrong)
    rb_sizes;
  check_int
    "from_ord_list holds exactly the elements it was given"
    ~expect:0
    ~actual:!wrong;
  (* Indistinguishable from a fold of insert, through the whole interface. *)
  let disagree = ref 0 in
  List.iter
    (fun n ->
      let xs = evens n in
      let built = Rb.from_ord_list xs
      and folded = rb_of_list xs in
      List.init ((2 * n) + 3) (fun i -> i - 1)
      |> List.iter (fun x ->
        if Rb.member x built <> Rb.member x folded then incr disagree))
    rb_sizes;
  check_int "from_ord_list agrees with a fold of insert" ~expect:0 ~actual:!disagree;
  (* Stronger than Exercise 3.8: from_ord_list does not merely respect the red-black
     bound, it produces a perfectly balanced tree. A sorted list fixes the shape exactly,
     so anything less than optimal is a bug rather than a tolerable outcome. *)
  let unbalanced = ref [] in
  List.iter
    (fun n ->
      let d = max_path n (Rb.from_ord_list (evens n)) in
      if d <> perfect_depth n then unbalanced := (n, d) :: !unbalanced)
    rb_sizes;
  check
    (Printf.sprintf
       "from_ord_list is perfectly balanced%s"
       (match !unbalanced with
        | [] -> ""
        | (n, d) :: _ ->
          Printf.sprintf " -- n=%d has depth %d, optimal %d" n d (perfect_depth n)))
    (!unbalanced = []);
  (* Exercise 3.9's O(n), first half. The list is already sorted, so from_ord_list has
     nothing to ask: any comparison at all means it is still searching for a position it
     was handed. This is the test that a fold of insert cannot pass. *)
  let compared = ref [] in
  List.iter
    (fun n ->
      let xs = evens n in
      let c = count_only (fun () -> Rb.from_ord_list xs) in
      if c <> 0 then compared := (n, c) :: !compared)
    (rb_sizes @ [ 10_000 ]);
  check
    (Printf.sprintf
       "from_ord_list performs no comparisons%s"
       (match !compared with
        | [] -> ""
        | (n, c) :: _ -> Printf.sprintf " -- n=%d cost %d" n c))
    (!compared = []);
  let folded_cost = count_only (fun () -> rb_of_list (evens 1000)) in
  check
    (Printf.sprintf
       "a fold of insert, by contrast, compares %d times at n=1000"
       folded_cost)
    (folded_cost > 1000);
  (* Exercise 3.9's O(n), second half: allocation per element must not grow with n. The
     list is built outside the closure so that only the construction is measured. *)
  let per_element n =
    let xs = evens n in
    allocated (fun () -> Rb.from_ord_list xs) /. float_of_int n
  in
  let small = per_element 1000
  and large = per_element 16_000 in
  check
    (Printf.sprintf
       "from_ord_list allocates O(1) per element (%.1f words at n=1000, %.1f at n=16000)"
       small
       large)
    (Float.abs (small -. large) < 0.5);
  (* The exercise says "a sorted list with no duplicates", not "a range". Sparse gaps and
     negative elements have to work the same, so check against an oracle rather than
     against the construction. *)
  Random.init 20260919;
  let arbitrary = ref 0 in
  List.iter
    (fun n ->
      let xs =
        List.sort_uniq compare (List.init n (fun _ -> Random.int 100_000 - 50_000))
      in
      let s = Rb.from_ord_list xs in
      let probes = List.init 400 (fun i -> i - 200) in
      if List.exists (fun q -> Rb.member q s <> List.mem q xs) (xs @ probes)
      then incr arbitrary)
    [ 1; 2; 5; 50; 500 ];
  check_int
    "from_ord_list handles sparse and negative sorted lists"
    ~expect:0
    ~actual:!arbitrary;
  (* from_ord_list is a constructor, not a terminus: the tree it returns has to keep
     behaving as elements continue to arrive one at a time. Seed with a sorted prefix,
     insert the rest, and Exercise 3.8's bound must still hold. *)
  let grown = ref [] in
  List.iter
    (fun (seed, extra) ->
      let s =
        List.init extra (fun i -> 2 * (seed + i))
        |> List.fold_left (fun s x -> Rb.insert x s) (Rb.from_ord_list (evens seed))
      in
      let total = seed + extra in
      let d = max_path total s in
      if d > depth_bound total then grown := (seed, extra, d) :: !grown)
    [ 1, 50; 10, 100; 100, 100; 100, 1000; 1000, 1000 ];
  check
    (Printf.sprintf
       "a from_ord_list tree stays balanced as inserts continue%s"
       (match !grown with
        | [] -> ""
        | (seed, extra, d) :: _ ->
          Printf.sprintf
            " -- %d seeded + %d inserted reached %d, bound %d"
            seed
            extra
            d
            (depth_bound (seed + extra))))
    (!grown = [])
;;

(* PERFORMANCE (3.3): member follows one path and builds nothing; insert copies one path
   and nothing else. The first is what makes member cheap in space as well as time, the
   second is what makes the structure persistent -- the old version keeps every node the
   insert did not rebuild, which is only sound because those nodes are never mutated. Both
   are visible through the seal with [words].

   Exercise 3.10 is not tested here and cannot be: insert_basic and insert_further_split
   are not in SET, so nothing outside the functor can reach them. The exported [insert] is
   (a), and the cases above hold it to the same behaviour and the same bounds. *)

let test_redblack_cost () =
  (* The defining property of a persistent structure: an insert leaves the old set whole. *)
  let s = rb_of_list (evens 50) in
  let s' = Rb.insert 99 s in
  check
    "insert leaves the original set unchanged"
    ((not (Rb.member 99 s)) && Rb.member 99 s');
  (* And not merely the previous version -- every version ever built stays correct, which
     is the part that would break if insert rebuilt a node any earlier version shares. *)
  let versions =
    evens 40
    |> List.fold_left
         (fun (acc, s) x ->
           let s = Rb.insert x s in
           s :: acc, s)
         ([], Rb.empty)
    |> fst
    |> List.rev
  in
  let stale = ref 0 in
  List.iteri
    (fun i v ->
      (* version i was built from evens (i+1), so it holds those and nothing beyond *)
      if not (List.for_all (fun x -> Rb.member x v) (evens (i + 1))) then incr stale;
      if Rb.member (2 * (i + 1)) v then incr stale)
    versions;
  check_int "every intermediate version stays correct" ~expect:0 ~actual:!stale;
  (* member only follows pointers, so it must allocate nothing whatsoever. *)
  let searching = ref [] in
  List.iter
    (fun n ->
      let s = rb_of_list (evens n) in
      let w = allocated (fun () -> Rb.member ((2 * n) + 1) s) in
      if w <> 0.0 then searching := (n, w) :: !searching)
    [ 10; 100; 1000; 10_000 ];
  check
    (Printf.sprintf
       "member allocates nothing%s"
       (match !searching with
        | [] -> ""
        | (n, w) :: _ -> Printf.sprintf " -- n=%d allocated %.0f words" n w))
    (!searching = []);
  (* insert copies the search path and only the search path, so its cost is logarithmic:
     ten thousand times as many elements must not cost ten thousand times as many words. *)
  let cost n =
    let s = rb_of_list (evens n) in
    allocated (fun () -> Rb.insert ((2 * n) + 1) s)
  in
  let small = cost 10
  and large = cost 100_000 in
  check
    (Printf.sprintf
       "insert allocates O(log n) (%.0f words at n=10, %.0f at n=100000)"
       small
       large)
    (large < 4.0 *. small);
  (* That copying is not waste: it is exactly what the older versions keep pointing at. A
     fresh insert has to allocate at least a node for each level it rebuilds. *)
  check
    (Printf.sprintf "a fresh insert really does copy the path (%.0f words)" large)
    (large >= float_of_int (depth_bound 100_000));
  (* A duplicate has no new node to thread in and no rotation to do, so it costs less --
     but not nothing. RedBlackSet does not implement Exercise 2.3's trick of abandoning
     the copy altogether, which is one of the optimisations the Hint to Practitioners
     means. *)
  let s = rb_of_list (evens 1000) in
  let dup = allocated (fun () -> Rb.insert 0 s)
  and fresh = allocated (fun () -> Rb.insert 2001 s) in
  check
    (Printf.sprintf
       "a duplicate insert costs less than a fresh one (%.0f < %.0f)"
       dup
       fresh)
    (dup < fresh)
;;

(* -------------------------------------------------------------------- cases *)

let tests =
  [ case "[Exercise 3.1, 3.2] LeftistHeap" test_leftist
  ; case "[Exercise 3.4] WeightBiasedLeftistHeap" test_weighted
  ; case "[Figure 3.4] BinomialHeap" test_binomial
  ; case "[Exercise 3.5] BinomialHeap: find_min allocates nothing" test_find_min_direct
  ; case "[Exercise 3.6] RanklessBinomialHeap" test_rankless
  ; case "[Exercise 3.7] ExplicitMin" test_explicit_min
  ; case "[Exercise 3.3] from_list" test_from_list
  ; case "[Example 3.1-3.2] all five heaps agree" test_agreement
  ; case "[Exercise 3.8] RedBlackSet" test_redblack
  ; case "[Exercise 3.9] from_ord_list" test_from_ord_list
  ; case "[Figure 3.6] RedBlackSet: persistence and cost" test_redblack_cost
  ]
;;
