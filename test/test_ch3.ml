(* Tests for Chapter 3, section 3.1: leftist heaps, and the weight-biased variant of
   Exercise 3.4. Plain OCaml, no test framework, matching test_ch2.ml: the switch has none
   installed and the library is stdlib-only, so the tests stay that way too.

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

let section name = Printf.printf "%s\n" name
let string_of_int_list l = "[" ^ String.concat ";" (List.map string_of_int l) ^ "]"

(* Words allocated by [f]. Sys.opaque_identity stops the optimiser discarding the result
   and with it the allocation we are trying to measure. *)
let words f =
  let before = Gc.minor_words () in
  ignore (Sys.opaque_identity (f ()));
  Gc.minor_words () -. before
;;

(* ---------------------------------------------- an instrumented element type *)

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

(* floor (log2 n), for n >= 1. *)
let floor_log2 n =
  let rec go acc n = if n <= 1 then acc else go (acc + 1) (n / 2) in
  go 0 n
;;

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
  [ "ascending", List.init n Fun.id
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
  let drain h =
    let rec go acc h =
      if H.is_empty h then List.rev acc else go (H.find_min h :: acc) (H.delete_min h)
    in
    go [] h
  ;;

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
            List.iter
              (fun (built, h) ->
                let r = rank_of h in
                if r > spine_bound n
                then
                  over
                  := Printf.sprintf "%s/%s n=%d rank=%d>%d" how built n r (spine_bound n)
                     :: !over)
              [ "insert", of_list xs ])
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
    (* Every cost below is logarithmic only because that bound holds, so guard them on it,
       as test_ch2 guards its deep checks. Without the leftist property of_list builds a
       linear spine, insert degrades to O(n), and a 100_000-element heap takes O(n^2) to
       build -- an unguarded check answers a regression by hanging for minutes instead of
       reporting it. *)
    if !over <> []
    then
      Printf.printf
        "  SKIP  %s: cost checks -- without the spine bound they are O(n^2)\n"
        name
    else (
      (* merge walks the two right spines and merges them like sorted lists, so it cannot
         cost more than their combined length -- which the bound above makes logarithmic. *)
      let pairs = [ 1, 1; 1, 100; 100, 1; 63, 64; 64, 64; 1000, 7; 500, 500 ] in
      let bad_sum = ref 0
      and bad_log = ref 0 in
      List.iter
        (fun (n1, n2) ->
          let h1 = of_list (List.init n1 Fun.id)
          and h2 = of_list (List.init n2 Fun.id) in
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
          let h = of_list (List.init n Fun.id) in
          let c = count_only (fun () -> H.insert max_int h) in
          if c > spine_bound n then incr bad_insert_cost)
        [ 1; 7; 8; 100; 1000; 10_000 ];
      check_int (t "insert is O(log n), worst case") ~expect:0 ~actual:!bad_insert_cost;
      (* delete_min merges the two children, each with a spine bounded by the parent's. *)
      let bad_delete = ref 0 in
      List.iter
        (fun n ->
          let h = of_list (List.init n Fun.id) in
          let c = count_only (fun () -> H.delete_min h) in
          if c > 2 * spine_bound n then incr bad_delete)
        [ 1; 7; 8; 100; 1000; 10_000 ];
      check_int (t "delete_min is O(log n)") ~expect:0 ~actual:!bad_delete;
      (* find_min reads the root: no comparison and no allocation, at any size. *)
      let bad_find = ref 0 in
      List.iter
        (fun n ->
          let h = of_list (List.init n Fun.id) in
          if count_only (fun () -> H.find_min h) <> 0 then incr bad_find;
          if words (fun () -> H.find_min h) > 4.0 then incr bad_find)
        [ 1; 100; 100_000 ];
      check_int (t "find_min is O(1)") ~expect:0 ~actual:!bad_find)
  ;;
end

(* from_list is Exercise 3.3, a leftist-heap exercise, and deliberately not part of HEAP:
   only the modules that actually implement it are held to this contract. *)
module From_list_tests (H : HEAP_WITH_FROM_LIST with type Element.t = int) = struct
  let of_list xs = List.fold_left (fun h x -> H.insert x h) H.empty xs

  let drain h =
    let rec go acc h =
      if H.is_empty h then List.rev acc else go (H.find_min h :: acc) (H.delete_min h)
    in
    go [] h
  ;;

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
    (* Guard the large sizes on the small one, as test_ch2 does: if from_list is not
       linear, report that rather than spending minutes proving it again. *)
    if c_small > 4 * small
    then Printf.printf "  SKIP  %s: large-n checks, from_list is not linear\n" name
    else (
      let large = 100_000 in
      let c_large = from_list_cost large in
      check
        (t
           (Printf.sprintf
              "from_list stays O(n) at n=%d (%.2f per element)"
              large
              (per large c_large)))
        (c_large <= 4 * large);
      (* The cost per element must not grow with n. An O(n log n) from_list would rise by
         a factor of log(100000)/log(1000) here, about 1.66. *)
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
        (c_large * 3 <= c_fold))
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
  let of_list xs = List.fold_left (fun h x -> H.insert x h) H.empty xs
  let trees h = count_only (fun () -> H.find_min h) + 1

  let popcount n =
    let rec go acc n = if n = 0 then acc else go (acc + (n land 1)) (n lsr 1) in
    go 0 n
  ;;

  (* An insert links once per trailing 1 bit: the carry chain of a binary increment,
     stopped by the first hole. *)
  let trailing_ones n =
    let rec go acc n = if n land 1 = 0 then acc else go (acc + 1) (n lsr 1) in
    go 0 n
  ;;

  let run name =
    let t label = Printf.sprintf "%s: %s" name label in
    (* Checked at EVERY step of a drain, not merely after construction: a mislabelled tree
       stays self-consistent until it is itself opened, so a single delete_min is not
       enough to expose it. *)
    let bad = ref 0
    and first = ref "" in
    Random.init 20260918;
    for n = 1 to 120 do
      let xs = List.init n (fun _ -> Random.int 1000) in
      let h = ref (of_list xs)
      and left = ref n in
      while not (H.is_empty !h) do
        if trees !h <> popcount !left
        then (
          incr bad;
          if !first = ""
          then
            first
            := Printf.sprintf
                 " -- first at n=%d, %d left, %d trees, popcount %d"
                 n
                 !left
                 (trees !h)
                 (popcount !left));
        h := H.delete_min !h;
        decr left
      done
    done;
    check
      (t (Printf.sprintf "one tree per 1 bit of n, at every step of a drain%s" !first))
      (!bad = 0);
    (* That count is what makes every operation logarithmic. *)
    let over = ref 0 in
    List.iter
      (fun n -> if trees (of_list (List.init n Fun.id)) > spine_bound n then incr over)
      [ 1; 7; 8; 15; 16; 100; 1000; 10_000 ];
    check_int (t "at most floor(log2 (n+1)) trees") ~expect:0 ~actual:!over;
    let bad_ins = ref 0 in
    List.iter
      (fun n ->
        let h = of_list (List.init n Fun.id) in
        if count_only (fun () -> H.insert max_int h) <> trailing_ones n then incr bad_ins)
      [ 1; 2; 3; 7; 8; 15; 31; 100; 255; 1000 ];
    check_int (t "insert links once per trailing 1 bit of n") ~expect:0 ~actual:!bad_ins;
    let bad_merge = ref 0 in
    List.iter
      (fun (n1, n2) ->
        let a = of_list (List.init n1 Fun.id)
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
  section "LeftistHeap (3.1-3.2)";
  Leftist.run_contract "LeftistHeap";
  Leftist.run_structure "LeftistHeap"
;;

let test_weighted () =
  section "WeightBiasedLeftistHeap (3.4)";
  Weighted.run_contract "WeightBiasedLeftistHeap";
  Weighted.run_structure "WeightBiasedLeftistHeap"
;;

let test_binomial () =
  section "BinomialHeap (3.2)";
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
  section "BinomialHeap: find_min is allocation-free (3.5)";
  let heap_of n = Binom.of_list (List.init n (fun i -> i * 7919 mod 100_000)) in
  (* Guard against a vacuous check: if the probe cannot see allocation at all, everything
     below passes for the wrong reason. Building a heap certainly allocates. *)
  let probe = words (fun () -> heap_of 64) in
  check
    (Printf.sprintf
       "the allocation probe registers work (building a heap costs %.0f words)"
       probe)
    (probe > 0.0);
  (* one tree versus sixteen *)
  let h_small = heap_of 1
  and h_large = heap_of 65_535 in
  let w_small = words (fun () -> B.find_min h_small)
  and w_large = words (fun () -> B.find_min h_large) in
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
        Float.max acc (words (fun () -> B.find_min h)))
      0.0
      [ 1; 7; 255; 4095; 65_535 ]
  in
  check
    (Printf.sprintf "find_min allocates O(1) at every size (worst %.0f words)" worst)
    (worst <= 16.0)
;;

let test_rankless () =
  section "RanklessBinomialHeap (3.6)";
  Rankless.run_contract "RanklessBinomialHeap";
  Rankless_struct.run "RanklessBinomialHeap"
;;

(* 3.7 asks for find_min in O(1) while insert, merge and delete_min stay O(log n). The
   first half is the claim worth asserting: zero comparisons at any size, against a base
   that pays one per tree. *)
let test_explicit_min () =
  section "ExplicitMin (3.7)";
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
      let h = Explicit.of_list (List.init n Fun.id) in
      if count_only (fun () -> X.insert max_int h) > spine_bound n + 1 then incr over;
      if count_only (fun () -> X.delete_min h) > (2 * spine_bound n) + 2 then incr over)
    [ 1; 7; 8; 100; 1000; 10_000 ];
  check_int "ExplicitMin: insert and delete_min stay O(log n)" ~expect:0 ~actual:!over
;;

let test_from_list () =
  section "from_list (3.3)";
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
  section "all five heaps agree";
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
  run "LeftistHeap" test_leftist;
  run "WeightBiasedLeftistHeap" test_weighted;
  run "BinomialHeap" test_binomial;
  run "find_min is direct (3.5)" test_find_min_direct;
  run "RanklessBinomialHeap" test_rankless;
  run "ExplicitMin" test_explicit_min;
  run "from_list" test_from_list;
  run "agreement" test_agreement;
  Printf.printf "\n%d checks, %d failures\n" !checks !failures;
  if !failures > 0 then exit 1
;;
