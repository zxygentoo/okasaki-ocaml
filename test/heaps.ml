(* The checks Chapters 3 to 7 hold their heaps and sortable collections to, written once.
   Every chapter declares HEAP and SORTABLE over again, but as the same signatures, so the
   functors here take the structures of all of them. *)

open Harness

(* -------------------------------------------------------- the heap contract *)

module Contract (H : Okasaki.Ch5.HEAP with type Element.t = int) = struct
  let of_list xs = List.fold_left (fun h x -> H.insert x h) H.empty xs

  (* find_min/delete_min to exhaustion. That this comes out sorted is the whole
     behavioural specification of a heap. *)
  let drain h = drain_with ~is_empty:H.is_empty ~head:H.find_min ~tail:H.delete_min h

  (* What every heap owes, persistence aside: what a chapter asks of persistence depends
     on what its heaps put off. *)
  let run_core name =
    let t label = Printf.sprintf "%s: %s" name label in
    let eq label expect h =
      check_eq (t label) ~expect ~actual:(drain h) string_of_int_list
    in
    check (t "empty is empty") (H.is_empty H.empty);
    check (t "a singleton is not empty") (not (H.is_empty (H.insert 1 H.empty)));
    check_failure (t "find_min on empty raises") "find_min: empty heap" (fun () ->
      H.find_min H.empty);
    (* Forced through is_empty: a delete_min that puts everything off, as Figure 6.2's
       does, cannot raise before then. *)
    check_failure (t "delete_min on empty raises") "delete_min: empty heap" (fun () ->
      ignore (H.is_empty (H.delete_min H.empty)));
    check_int (t "find_min of a singleton") ~expect:5 ~actual:(H.find_min (of_list [ 5 ]));
    check
      (t "delete_min of a singleton is empty")
      (H.is_empty (H.delete_min (of_list [ 5 ])));
    eq "drain is sorted" [ 1; 2; 3; 4; 5; 6; 7 ] (of_list [ 4; 2; 6; 1; 3; 5; 7 ]);
    (* Aimed at Exercise 5.4. A drain of distinct elements cannot tell which side of the
       partition an element equal to the pivot went to -- but it must go to one of them.
       Sent to neither, it vanishes. The copy is met at the root, at the bottom of the
       left spine and at the bottom of the right spine, so every branch of the partition
       meets it. *)
    eq "a repeated element is kept when it is the root" [ 5; 5 ] (of_list [ 5; 5 ]);
    eq
      "a repeated element is kept when it is deep on the left"
      [ 1; 2; 3; 4; 5; 5 ]
      (of_list [ 5; 4; 3; 2; 1; 5 ]);
    eq
      "a repeated element is kept when it is deep on the right"
      [ 1; 1; 2; 3; 4; 5 ]
      (of_list [ 1; 2; 3; 4; 5; 1 ]);
    eq "duplicates are all kept" [ 1; 1; 1; 2; 2; 3 ] (of_list [ 2; 1; 3; 1; 2; 1 ]);
    (* Also aimed at Exercise 5.4. A subtree carried to the wrong side of its parent keeps
       every element, so only the order notices, and it notices first at the minimum:
       find_min follows left branches, and a minimum that has been put on the right is not
       where it looks. *)
    check_int
      (t "the minimum is found after ascending inserts")
      ~expect:1
      ~actual:(H.find_min (of_list [ 1; 2; 3 ]));
    check_int
      (t "the minimum is found after descending inserts")
      ~expect:1
      ~actual:(H.find_min (of_list [ 3; 2; 1 ]));
    eq
      "merge is multiset union"
      [ 1; 2; 3; 4; 5; 6 ]
      (H.merge (of_list [ 1; 4; 6 ]) (of_list [ 2; 3; 5 ]));
    eq
      "merge with an empty right operand"
      [ 1; 2; 3 ]
      (H.merge (of_list [ 3; 1; 2 ]) H.empty);
    eq
      "merge with an empty left operand"
      [ 1; 2; 3 ]
      (H.merge H.empty (of_list [ 3; 1; 2 ]));
    check (t "merge of two empties is empty") (H.is_empty (H.merge H.empty H.empty));
    (* Randomised, against List.sort as the reference, with few distinct values so that
       equal elements are everywhere. *)
    Random.init 20260922;
    let bad_insert = ref 0
    and bad_merge = ref 0
    and raised = ref 0 in
    for _ = 0 to 299 do
      let xs = List.init (Random.int 40) (fun _ -> Random.int 25)
      and ys = List.init (Random.int 40) (fun _ -> Random.int 25) in
      match
        if drain (of_list xs) <> List.sort compare xs then incr bad_insert;
        if drain (H.merge (of_list xs) (of_list ys)) <> List.sort compare (xs @ ys)
        then incr bad_merge
      with
      | () -> ()
      | exception Failure _ -> incr raised
    done;
    check_int
      (t "no operation raises on a non-empty heap, 300 random runs")
      ~expect:0
      ~actual:!raised;
    check_int (t "insert then drain, 300 random lists") ~expect:0 ~actual:!bad_insert;
    check_int (t "merge then drain, 300 random pairs") ~expect:0 ~actual:!bad_merge
  ;;

  (* The core, and persistence with several futures of one heap. *)
  let run_contract name =
    run_core name;
    let t label = Printf.sprintf "%s: %s" name label in
    let eq label expect h =
      check_eq (t label) ~expect ~actual:(drain h) string_of_int_list
    in
    (* Persistence: no operation may disturb its operands. With suspensions in the picture
       that includes forcing: a heap looked at through one future must read the same
       through another. *)
    let h = of_list [ 5; 3; 8; 1 ] in
    let a = H.insert 0 h
    and b = H.insert 4 h
    and c = H.delete_min h
    and d = H.merge h h in
    eq "one future of a shared heap" [ 0; 1; 3; 5; 8 ] a;
    eq "another" [ 1; 3; 4; 5; 8 ] b;
    eq "a third" [ 3; 5; 8 ] c;
    eq "a fourth" [ 1; 1; 3; 3; 5; 5; 8; 8 ] d;
    eq "and the operand is untouched" [ 1; 3; 5; 8 ] h
  ;;

  (* The shape of a binomial heap: the binary representation of its size, one tree per 1
     bit. [trees h] counts the trees from outside the sealed signature. *)
  let run_tree_counts ~trees name =
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
      (fun n -> if trees (of_list (upto n)) > floor_log2 (n + 1) then incr over)
      [ 1; 7; 8; 15; 16; 100; 1000; 10_000 ];
    check_int (t "at most floor(log2 (n+1)) trees") ~expect:0 ~actual:!over
  ;;
end

(* -------------------------------------------- the sortable collection contract *)

module Sortable_contract (S : Okasaki.Ch6.SORTABLE with type Element.t = int) = struct
  let of_list xs = List.fold_left (fun s x -> S.add x s) S.empty xs

  let run_contract name =
    let t label = Printf.sprintf "%s: %s" name label in
    let eq label expect s =
      check_eq (t label) ~expect ~actual:(S.sort s) string_of_int_list
    in
    eq "sort of empty is empty" [] S.empty;
    eq "sort of a singleton" [ 5 ] (of_list [ 5 ]);
    eq "sort sorts" [ 1; 2; 3; 4; 5; 6; 7 ] (of_list [ 4; 2; 6; 1; 3; 5; 7 ]);
    eq "duplicates are all kept" [ 1; 1; 1; 2; 2; 3 ] (of_list [ 2; 1; 3; 1; 2; 1 ]);
    eq "ascending input" (upto 20) (of_list (upto 20));
    eq "descending input" (upto 20) (of_list (List.rev (upto 20)));
    (* Sizes on either side of a power of two: every bit set, one bit set, and one more. *)
    eq "31 elements" (upto 31) (of_list (List.rev (upto 31)));
    eq "32 elements" (upto 32) (of_list (List.rev (upto 32)));
    eq "33 elements" (upto 33) (of_list (List.rev (upto 33)));
    (* Randomised, against List.sort, with few distinct values so that equal elements are
       everywhere. *)
    Random.init 20260925;
    let bad = ref 0
    and raised = ref 0 in
    for _ = 0 to 299 do
      let xs = List.init (Random.int 200) (fun _ -> Random.int 50) in
      match S.sort (of_list xs) = List.sort compare xs with
      | true -> ()
      | false -> incr bad
      | exception Failure _ -> incr raised
    done;
    check_int (t "no sort raises, 300 random lists") ~expect:0 ~actual:!raised;
    check_int (t "sort agrees with List.sort, 300 random lists") ~expect:0 ~actual:!bad;
    (* Persistence, in the section's own terms: xs' serves xs, x :: xs and y :: xs. *)
    let xs' = of_list [ 5; 3; 8; 1; 9; 2 ] in
    eq "xs" [ 1; 2; 3; 5; 8; 9 ] xs';
    eq "x :: xs, from the same collection" [ 1; 2; 3; 4; 5; 8; 9 ] (S.add 4 xs');
    eq "y :: xs, from the same collection" [ 0; 1; 2; 3; 5; 8; 9 ] (S.add 0 xs');
    eq "xs again, untouched" [ 1; 2; 3; 5; 8; 9 ] xs'
  ;;
end
