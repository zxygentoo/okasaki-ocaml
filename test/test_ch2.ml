(* Tests for Chapter 2, as Alcotest cases written in the checks of harness.ml.

   Alongside the behavioural tests there are performance tests, because several exercises
   specify a *cost*, not just a result: 2.1 wants O(n) space, 2.2 and 2.4 want d+1
   comparisons, 2.3 wants no copying, 2.5 wants O(d) and O(log n). Those bounds are the
   exercise, so they are asserted rather than assumed. Comparisons are counted with an
   instrumented ORDERED; allocation is measured with Gc.minor_words, which counts words
   allocated rather than words retained. *)

open Okasaki.Ch2
open Harness

let string_of_int_list_list l =
  "[" ^ String.concat "; " (List.map string_of_int_list l) ^ "]"
;;

(* ------------------------------------------------------------- stacks (2.1) *)

(* Drive a stack only through STACK, so both implementations are held to the same
   observable behaviour. *)
module Stack_tests (S : STACK) = struct
  let of_list l = List.fold_right S.cons l S.empty
  let to_list s = drain_with ~is_empty:S.is_empty ~head:S.head ~tail:S.tail s

  let run name =
    let t label = Printf.sprintf "%s: %s" name label in
    check_eq
      (t "of_list/to_list round trip")
      ~expect:[ 1; 2; 3 ]
      ~actual:(to_list (of_list [ 1; 2; 3 ]))
      string_of_int_list;
    check_int (t "head") ~expect:1 ~actual:(S.head (of_list [ 1; 2; 3 ]));
    check_eq
      (t "tail")
      ~expect:[ 2; 3 ]
      ~actual:(to_list (S.tail (of_list [ 1; 2; 3 ])))
      string_of_int_list;
    check (t "is_empty empty") (S.is_empty S.empty);
    check (t "is_empty non-empty") (not (S.is_empty (of_list [ 1 ])));
    (* Regression: an accumulator-shaped (++) reverses its left operand and still passes
       the [s ++ empty] case, so the mixed cases carry the weight. *)
    let cat a b = to_list S.(of_list a ++ of_list b) in
    check_eq
      (t "(++) [1;2;3] [4;5]")
      ~expect:[ 1; 2; 3; 4; 5 ]
      ~actual:(cat [ 1; 2; 3 ] [ 4; 5 ])
      string_of_int_list;
    check_eq
      (t "(++) [1] [2]")
      ~expect:[ 1; 2 ]
      ~actual:(cat [ 1 ] [ 2 ])
      string_of_int_list;
    check_eq
      (t "(++) with empty right")
      ~expect:[ 1; 2; 3 ]
      ~actual:(cat [ 1; 2; 3 ] [])
      string_of_int_list;
    check_eq
      (t "(++) with empty left")
      ~expect:[ 1; 2; 3 ]
      ~actual:(cat [] [ 1; 2; 3 ])
      string_of_int_list;
    check_eq (t "(++) empty empty") ~expect:[] ~actual:(cat [] []) string_of_int_list;
    (* (++) starts with '+', so OCaml parses it left-associatively; the value is the same
       either way. *)
    let a = of_list [ 1; 2 ]
    and b = of_list [ 3; 4 ]
    and c = of_list [ 5; 6 ] in
    check_eq
      (t "(++) associates left")
      ~expect:[ 1; 2; 3; 4; 5; 6 ]
      ~actual:(to_list S.(a ++ b ++ c))
      string_of_int_list;
    check_eq
      (t "(++) associates right")
      ~expect:[ 1; 2; 3; 4; 5; 6 ]
      ~actual:(to_list S.(a ++ (b ++ c)))
      string_of_int_list;
    (* Both implementations must fail identically, or the signature is a lie. These are
       the library's own names, not Stdlib's "hd"/"tl". *)
    check_failure (t "head empty raises") "head" (fun () -> S.head S.empty);
    check_failure (t "tail empty raises") "tail" (fun () ->
      ignore (to_list (S.tail S.empty)));
    (* update: replace the element at an index, copying the path to it. *)
    let xs = of_list [ 1; 2; 3; 4; 5 ] in
    let updated i = to_list (S.update i 99 xs) in
    check_eq
      (t "update at the head")
      ~expect:[ 99; 2; 3; 4; 5 ]
      ~actual:(updated 0)
      string_of_int_list;
    (* The head index is the case a head-dropping implementation still gets right, so the
       interior and last indices are the ones that carry the weight. *)
    check_eq
      (t "update in the middle")
      ~expect:[ 1; 2; 99; 4; 5 ]
      ~actual:(updated 2)
      string_of_int_list;
    check_eq
      (t "update at the last index")
      ~expect:[ 1; 2; 3; 4; 99 ]
      ~actual:(updated 4)
      string_of_int_list;
    check_int (t "update keeps the length") ~expect:5 ~actual:(List.length (updated 2));
    check_failure (t "update past the end raises") "update" (fun () ->
      ignore (to_list (S.update 5 99 xs)));
    check_failure (t "update far past the end raises") "update" (fun () ->
      ignore (to_list (S.update 99 99 xs)));
    check_failure (t "update at a negative index raises") "update" (fun () ->
      ignore (to_list (S.update (-1) 99 xs)));
    check_failure (t "update on the empty stack raises") "update" (fun () ->
      ignore (to_list (S.update 0 99 S.empty)));
    (* PERFORMANCE: the point of update is path copying -- only the nodes from the head to
       index i are rebuilt, and everything past i is SHARED with the original. Physical
       equality states that directly; structural equality would pass even for an
       implementation that copied the whole stack. *)
    let rec drop n s = if n = 0 then s else drop (n - 1) (S.tail s) in
    check
      (t "update shares every node past the updated index")
      (drop 3 (S.update 2 99 xs) == drop 3 xs);
    check
      (t "update at the head shares all but one node")
      (drop 1 (S.update 0 99 xs) == drop 1 xs);
    (* Persistence: nothing observes a change to the original. *)
    let s = of_list [ 1; 2; 3 ] in
    let _ = S.cons 0 s
    and _ = S.tail s in
    check_eq
      (t "original unchanged")
      ~expect:[ 1; 2; 3 ]
      ~actual:(to_list s)
      string_of_int_list;
    check_eq
      (t "update leaves the original alone")
      ~expect:[ 1; 2; 3; 4; 5 ]
      ~actual:(to_list xs)
      string_of_int_list
  ;;
end

module List_stack_tests = Stack_tests (ListStack)
module Custom_stack_tests = Stack_tests (CustomStack)

(* ----------------------------------------------------------- suffixes (2.1) *)

let test_suffixes () =
  check_eq
    "suffixes [1;2;3;4]"
    ~expect:[ [ 1; 2; 3; 4 ]; [ 2; 3; 4 ]; [ 3; 4 ]; [ 4 ]; [] ]
    ~actual:(suffixes [ 1; 2; 3; 4 ])
    string_of_int_list_list;
  check_eq
    "suffixes [1;2]"
    ~expect:[ [ 1; 2 ]; [ 2 ]; [] ]
    ~actual:(suffixes [ 1; 2 ])
    string_of_int_list_list;
  check_eq
    "suffixes [1]"
    ~expect:[ [ 1 ]; [] ]
    ~actual:(suffixes [ 1 ])
    string_of_int_list_list;
  (* The empty list has exactly one suffix: itself. *)
  check_eq "suffixes []" ~expect:[ [] ] ~actual:(suffixes []) string_of_int_list_list;
  for n = 0 to 50 do
    let xs = upto n in
    check_int
      (Printf.sprintf "suffixes length for n=%d" n)
      ~expect:(n + 1)
      ~actual:(List.length (suffixes xs))
  done
;;

(* PERFORMANCE (2.1): O(n) space holds only because each suffix IS a tail of the original
   rather than a copy. Physical equality checks that directly; structural equality would
   pass even for a copying implementation. *)
let test_suffixes_share () =
  let xs = upto 200 in
  let s = suffixes xs in
  check "first suffix is the original list" (List.hd s == xs);
  let rec tails_shared = function
    | a :: (b :: _ as rest) ->
      (match a with
       | _ :: t -> t == b && tails_shared rest
       | [] -> false)
    | _ -> true
  in
  check "each suffix is physically the previous one's tail" (tails_shared s);
  (* Only the n+1 cons cells of the outer list are new. A copying implementation would
     allocate O(n^2). *)
  let n = 300 in
  let ys = upto n in
  let w = allocated (fun () -> suffixes ys) in
  check
    (Printf.sprintf "suffixes allocates O(n) words (n=%d, got %.0f)" n w)
    (w <= 6.0 *. float_of_int (n + 1))
;;

(* ------------------------------------------------- ordered modules for trees *)

module S = UnbalancedSet (Counting_int)
module M = UnbalancedMap (Counting_int)

(* Inserting 0,1,..,n-1 in order sends every element right, giving a right spine of known
   depth n. Knowing d without inspecting the tree matters because UnbalancedSet.set is
   abstract. *)
let spine_set n = List.fold_left (fun s x -> S.insert x s) S.empty (upto n)
let spine_map n = List.fold_left (fun m k -> M.bind k (k * 10) m) M.empty (upto n)

(* An insertion order that builds a balanced tree of depth ceil(log2 (n+1)). *)
let balanced_order n =
  let rec go lo hi =
    if lo > hi
    then []
    else (
      let mid = lo + ((hi - lo) / 2) in
      mid :: (go lo (mid - 1) @ go (mid + 1) hi))
  in
  go 0 (n - 1)
;;

let ceil_log2 n =
  let rec go acc p = if p >= n then acc else go (acc + 1) (p * 2) in
  go 0 1
;;

(* ------------------------------------------------- UnbalancedSet (2.2 - 2.4) *)

let test_set () =
  let elems = [ 4; 2; 6; 1; 3; 5; 7 ] in
  let s = List.fold_left (fun s x -> S.insert x s) S.empty elems in
  List.iter (fun x -> check (Printf.sprintf "member %d (present)" x) (S.member x s)) elems;
  List.iter
    (fun x -> check (Printf.sprintf "member %d (absent)" x) (not (S.member x s)))
    [ -1; 0; 8; 100 ];
  check "member on empty" (not (S.member 1 S.empty));
  (* Randomised: member agrees with List.mem for every query, over many shapes. *)
  Random.init 20260917;
  let ok = ref true in
  for trial = 0 to 299 do
    let n = 1 + Random.int 25 in
    let xs =
      if trial mod 3 = 0
      then upto n (* degenerate *)
      else List.init n (fun _ -> Random.int 40)
    in
    let s = List.fold_left (fun s x -> S.insert x s) S.empty xs in
    for q = -2 to 42 do
      if S.member q s <> List.mem q xs then ok := false
    done
  done;
  check "member agrees with List.mem over 300 random trees" !ok;
  (* Persistence: inserting into a set leaves the original alone. *)
  let s1 = S.insert 99 s in
  check
    "insert leaves the original set unchanged"
    ((not (S.member 99 s)) && S.member 99 s1)
;;

(* PERFORMANCE (2.2, 2.4): no more than d+1 comparisons, for member and insert, present or
   absent. Trees of known depth are used so d is exact. *)
let test_set_comparisons () =
  let n = 60 in
  let deep = spine_set n in
  let d = n in
  let _, c = count (fun () -> S.member (n - 1) deep) in
  check_int "member, present at the deepest node" ~expect:(d + 1) ~actual:c;
  let _, c = count (fun () -> S.member 1000 deep) in
  check (Printf.sprintf "member, absent: %d <= d+1 = %d" c (d + 1)) (c <= d + 1);
  let _, c = count (fun () -> S.insert (n - 1) deep) in
  check_int "insert, duplicate at the deepest node" ~expect:(d + 1) ~actual:c;
  let _, c = count (fun () -> S.insert 1000 deep) in
  check (Printf.sprintf "insert, new element: %d <= d+1 = %d" c (d + 1)) (c <= d + 1);
  (* Same bound on a balanced tree, where d is logarithmic. *)
  let m = 127 in
  let bal = List.fold_left (fun s x -> S.insert x s) S.empty (balanced_order m) in
  let d = ceil_log2 (m + 1) in
  let worst = ref 0 in
  for q = -1 to m do
    let _, c = count (fun () -> S.member q bal) in
    if c > !worst then worst := c
  done;
  check
    (Printf.sprintf "member on a balanced tree: worst %d <= d+1 = %d" !worst (d + 1))
    (!worst <= d + 1)
;;

(* PERFORMANCE (2.3): inserting an element that is already present must copy nothing.
   Physical equality of the result with the input is the strongest statement of that: not
   one node of the search path was rebuilt. *)
let test_set_no_copying () =
  let n = 60 in
  let deep = spine_set n in
  for x = 0 to n - 1 do
    check (Printf.sprintf "insert %d returns the original set" x) (S.insert x deep == deep)
  done;
  let dup = allocated (fun () -> S.insert (n - 1) deep) in
  let fresh = allocated (fun () -> S.insert 1000 deep) in
  check
    (Printf.sprintf
       "duplicate insert allocates less than a fresh one (%.0f < %.0f)"
       dup
       fresh)
    (dup < fresh);
  (* A fresh insert copies the path; that copying is necessary for persistence. *)
  check "fresh insert allocates the search path" (fresh >= 4.0 *. float_of_int n)
;;

(* ----------------------------------------------------- complete, create (2.5) *)

let rec tree_size = function
  | Empty -> 0
  | Tree (l, _, r) -> 1 + tree_size l + tree_size r
;;

let rec tree_height = function
  | Empty -> 0
  | Tree (l, _, r) -> 1 + max (tree_height l) (tree_height r)
;;

let rec tree_balanced = function
  | Empty -> true
  | Tree (l, _, r) ->
    abs (tree_size l - tree_size r) <= 1 && tree_balanced l && tree_balanced r
;;

let test_complete () =
  (* Depth counts edges here: complete x 0 is a single node. *)
  List.iter
    (fun d ->
      check_int
        (Printf.sprintf "complete _ %d has 2^(d+1)-1 nodes" d)
        ~expect:((1 lsl (d + 1)) - 1)
        ~actual:(tree_size (complete 'x' d)))
    [ 0; 1; 2; 3; 8 ];
  check_int "complete _ 5 height" ~expect:6 ~actual:(tree_height (complete 'x' 5));
  check_raises
    "complete rejects a negative depth"
    (Invalid_argument "complete: negative d")
    (fun () -> complete 'x' (-1));
  (* complete needs no comparisons, so it works for any element type. *)
  check_int "complete is polymorphic" ~expect:7 ~actual:(tree_size (complete "s" 2))
;;

(* PERFORMANCE (2.5a): O(d) time and space. That holds only because each level points at
   ONE subtree twice; two recursive calls would make it O(2^d). *)
let test_complete_sharing () =
  let rec all_levels_alias = function
    | Empty -> true
    | Tree (Empty, _, Empty) -> true
    | Tree (l, _, r) -> l == r && all_levels_alias l
  in
  (* Probe sharing at a trivial depth FIRST: a check that fails ends the case, and that is
     the guard on everything expensive below. Without sharing, complete _ d allocates 2^d
     nodes: d=22 is 256 MiB and d=40 is 64 TiB, so a deep check that ran anyway would
     answer a regression by exhausting memory instead of reporting a failure. *)
  check "every level aliases its two children" (all_levels_alias (complete 0 8));
  check "aliasing holds all the way down at depth 40" (all_levels_alias (complete 0 40));
  List.iter
    (fun d ->
      let w = allocated (fun () -> complete 0 d) in
      (* one node per level; a naive version would allocate 2^d of them *)
      check
        (Printf.sprintf "complete _ %d allocates O(d) words (got %.0f)" d w)
        (w <= 20.0 *. float_of_int (d + 1)))
    [ 4; 10; 22; 40 ];
  (* Representing 2^61 logical nodes has to stay instant. *)
  let w = allocated (fun () -> complete 0 60) in
  check (Printf.sprintf "complete _ 60 stays small (%.0f words)" w) (w <= 2000.0)
;;

let test_create () =
  let bad_size = ref 0
  and bad_bal = ref 0
  and bad_height = ref 0 in
  for n = 0 to 500 do
    let t = create 0 n in
    if tree_size t <> n then incr bad_size;
    if not (tree_balanced t) then incr bad_bal;
    if tree_height t <> ceil_log2 (n + 1) then incr bad_height
  done;
  check_int
    "create builds a tree of exactly n nodes, n=0..500"
    ~expect:0
    ~actual:!bad_size;
  check_int "subtree sizes differ by at most 1, n=0..500" ~expect:0 ~actual:!bad_bal;
  check_int "height is ceil(log2(n+1)), n=0..500" ~expect:0 ~actual:!bad_height;
  check_raises
    "create rejects a negative size"
    (Invalid_argument "create: negative n")
    (fun () -> create 0 (-1))
;;

(* PERFORMANCE (2.5b): O(log n). The tree has n logical nodes but only O(log n) distinct
   ones, so allocation grows logarithmically. *)
let test_create_cost () =
  let bound_for n = 40.0 *. float_of_int (ceil_log2 (n + 1) + 1) in
  let cost n =
    let w = allocated (fun () -> create 0 n) in
    check
      (Printf.sprintf
         "create _ %d allocates O(log n) words (got %.0f, bound %.0f)"
         n
         w
         (bound_for n))
      (w <= bound_for n);
    w
  in
  (* Same guard as complete: probe at sizes that are cheap even for a linear
     implementation, and only then reach for n = 10^8, where an O(n) create would allocate
     gigabytes and recurse 10^8 deep. A probe over its bound ends the case. *)
  let small = cost 100 in
  ignore (cost 10_000);
  ignore (cost 1_000_000);
  let huge = cost 100_000_000 in
  (* Growing n by six orders of magnitude must barely move allocation. *)
  check
    (Printf.sprintf "allocation grows logarithmically (%.0f -> %.0f)" small huge)
    (huge <= small *. 6.0)
;;

(* ----------------------------------------------------- UnbalancedMap (2.6) *)

(* UnbalancedMap seals 'a map, so the tests reach it only through lookup/bind. That is
   enough to pin a map down completely: over a known key universe, every key either looks
   up to the expected value or raises Not_found, which also rules out bindings the map
   should not have. *)
let lookup_opt k m =
  match M.lookup k m with
  | v -> Some v
  | exception Not_found -> None
;;

let test_map () =
  let m =
    List.fold_left
      (fun m (k, v) -> M.bind k v m)
      M.empty
      [ 4, "four"; 2, "two"; 6, "six"; 1, "one"; 3, "three" ]
  in
  check_eq "lookup 3" ~expect:"three" ~actual:(M.lookup 3 m) Fun.id;
  check_eq "lookup 6" ~expect:"six" ~actual:(M.lookup 6 m) Fun.id;
  check_raises "lookup of a missing key raises Not_found" Not_found (fun () ->
    M.lookup 9 m);
  check_raises "lookup on the empty map raises Not_found" Not_found (fun () ->
    M.lookup 1 M.empty);
  (* The difference from a set: rebinding an existing key must REPLACE the value. A bind
     that reuses insert's "already present, nothing to do" logic silently keeps the old
     one. *)
  let m2 = M.bind 3 "THREE" m in
  check_eq
    "bind replaces the value of an existing key"
    ~expect:"THREE"
    ~actual:(M.lookup 3 m2)
    Fun.id;
  check_eq "the original map is untouched" ~expect:"three" ~actual:(M.lookup 3 m) Fun.id;
  (* The ordinary use that a non-replacing bind breaks. *)
  let tally =
    List.fold_left
      (fun acc w ->
        let n =
          try M.lookup w acc with
          | Not_found -> 0
        in
        M.bind w (n + 1) acc)
      M.empty
      [ 1; 2; 1; 1; 3; 2 ]
  in
  let show_tally m =
    String.concat
      " "
      (List.map
         (fun k ->
           match lookup_opt k m with
           | Some v -> Printf.sprintf "%d->%d" k v
           | None -> Printf.sprintf "%d->_" k)
         [ 1; 2; 3; 4 ])
  in
  check_eq
    "repeated rebinding accumulates"
    ~expect:"1->3 2->2 3->1 4->_"
    ~actual:(show_tally tally)
    Fun.id;
  (* Randomised against an assoc-list reference. *)
  Random.init 20260917;
  let ok = ref true in
  for _ = 0 to 299 do
    let ops = List.init (1 + Random.int 40) (fun _ -> Random.int 20, Random.int 100) in
    let m = List.fold_left (fun m (k, v) -> M.bind k v m) M.empty ops in
    let reference =
      List.fold_left (fun a (k, v) -> (k, v) :: List.remove_assoc k a) [] ops
    in
    (* Sweep the whole key universe: a bound key must yield its latest value, and an
       unbound one must raise. Together those pin the map exactly, with no need to see
       inside it. *)
    for k = 0 to 19 do
      if lookup_opt k m <> List.assoc_opt k reference then ok := false
    done
  done;
  check "map agrees with an assoc-list reference over 300 random workloads" !ok;
  (* Values are unconstrained: no comparison is ever performed on them. *)
  let fm = M.bind 1 (fun x -> x * 10) M.empty in
  check_int "a map can hold closures" ~expect:50 ~actual:(M.lookup 1 fm 5)
;;

(* PERFORMANCE (2.6): lookup inherits 2.2's bound by carrying the pair as the candidate.
   bind cannot: it must recognise the key while standing on its node in order to replace
   the value, which is exactly what a single-comparison descent withholds. So bind costs
   2d, and that is expected, not a regression. *)
let test_map_comparisons () =
  let n = 60 in
  let deep = spine_map n in
  let d = n in
  let _, c = count (fun () -> M.lookup (n - 1) deep) in
  check_int "lookup, present at the deepest node" ~expect:(d + 1) ~actual:c;
  let _, c =
    count (fun () ->
      try Some (M.lookup 1000 deep) with
      | Not_found -> None)
  in
  check (Printf.sprintf "lookup, absent: %d <= d+1 = %d" c (d + 1)) (c <= d + 1);
  let _, c = count (fun () -> M.bind (n - 1) 0 deep) in
  check (Printf.sprintf "bind, rebind: %d <= 2d+1 = %d" c ((2 * d) + 1)) (c <= (2 * d) + 1);
  let _, c = count (fun () -> M.bind 1000 0 deep) in
  check
    (Printf.sprintf "bind, new key: %d <= 2d+1 = %d" c ((2 * d) + 1))
    (c <= (2 * d) + 1);
  (* A rebind changes the tree, so copying the path is necessary work. *)
  let w = allocated (fun () -> M.bind (n - 1) 0 deep) in
  check
    (Printf.sprintf "rebind copies the search path (%.0f words)" w)
    (w >= 4.0 *. float_of_int n)
;;

(* -------------------------------------------------------------------- cases *)

let tests =
  [ case "[Figure 2.2] ListStack" (fun () -> List_stack_tests.run "ListStack")
  ; case "[Figure 2.3] CustomStack" (fun () -> Custom_stack_tests.run "CustomStack")
  ; case "[Exercise 2.1] suffixes" test_suffixes
  ; case "[Exercise 2.1] suffixes: O(n) space via sharing" test_suffixes_share
  ; case "[Figure 2.9] UnbalancedSet" test_set
  ; case "[Exercise 2.2, 2.4] UnbalancedSet: d+1 comparisons" test_set_comparisons
  ; case "[Exercise 2.3] UnbalancedSet: no copying on re-insert" test_set_no_copying
  ; case "[Exercise 2.5 (a)] complete" test_complete
  ; case "[Exercise 2.5 (a)] complete: O(d) via sharing" test_complete_sharing
  ; case "[Exercise 2.5 (b)] create" test_create
  ; case "[Exercise 2.5 (b)] create: O(log n)" test_create_cost
  ; case "[Exercise 2.6] UnbalancedMap" test_map
  ; case "[Exercise 2.6] UnbalancedMap: comparison bounds" test_map_comparisons
  ]
;;
