module type ORDERED = sig
  type t

  val eq : t -> t -> bool
  val lt : t -> t -> bool
  val leq : t -> t -> bool
end

module type HEAP = sig
  module Element : ORDERED

  type heap

  val empty : heap
  val is_empty : heap -> bool
  val insert : Element.t -> heap -> heap
  val merge : heap -> heap -> heap
  val find_min : heap -> Element.t (* raises Failure if heap is empty *)
  val delete_min : heap -> heap (* raises Failure if heap is empty *)
end

module type HEAP_WITH_FROM_LIST = sig
  include HEAP

  val from_list : Element.t list -> heap
end

(* Leftist heaps [Cra72, Knu73a] are heap-ordered binary trees that satisfy the leftist
   property: the rank of any left child is at least as large as the rank of its right
   sibling. The rank of a node is defined to be the length of its right spine (i.e., the
   rightmost path from the node in question to an empty node). A simple consequence of the
   leftist property is that the right spine of any node is always the shortest path to an
   empty node. *)

module LeftistHeap (Element : ORDERED) :
  HEAP_WITH_FROM_LIST with module Element = Element = struct
  module Element = Element

  type elem = Element.t

  type heap =
    | Empty
    | Heap of
        { rank : int
        ; value : elem
        ; left : heap
        ; right : heap
        }

  let heap r v a b = Heap { rank = r; value = v; left = a; right = b }
  let heap1 x = heap 1 x Empty Empty

  let rank = function
    | Empty -> 0
    | Heap { rank } -> rank
  ;;

  let make x a b =
    let ra = rank a
    and rb = rank b in
    if ra >= rb then heap (rb + 1) x a b else heap (ra + 1) x b a
  ;;

  let empty = Empty

  let is_empty = function
    | Empty -> true
    | Heap _ -> false
  ;;

  let rec merge h1 h2 =
    match h1, h2 with
    | _, Empty -> h1
    | Empty, _ -> h2
    | Heap a, Heap b ->
      if Element.leq a.value b.value
      then make a.value a.left (merge a.right h2)
      else make b.value b.left (merge h1 b.right)
  ;;

  (* Exercise 3.2 Define insert directly rather than via a call to merge. *)

  let rec insert x = function
    | Empty -> heap1 x
    | Heap { value; left; right } as h ->
      if Element.leq x value then make x Empty h else make value left (insert x right)
  ;;

  let find_min = function
    | Empty -> raise (Failure "find_min: empty heap")
    | Heap { value } -> value
  ;;

  let delete_min = function
    | Empty -> raise (Failure "delete_min: empty heap")
    | Heap { left; right } -> merge left right
  ;;

  (* Exercise 3.3 Implement a function fromList of type Elem.T list ->• Heap that produces
     a leftist heap from an unordered list of elements by first converting each element
     into a singleton heap and then merging the heaps until only one heap remains. Instead
     of merging the heaps in one right-to-left or left-to-right pass using foldr or foldl,
     merge the heaps in [logn] passes, where each pass merges adjacent pairs of heaps.
     Show that fromList takes only O(n) time. *)

  let from_list xs =
    let rec pass acc = function
      | [] -> acc
      | [ h ] -> h :: acc
      | h1 :: h2 :: hs -> pass (merge h1 h2 :: acc) hs
    in
    let rec go = function
      | [] -> Empty
      | [ h ] -> h
      | hs -> pass [] hs |> go
    in
    List.map heap1 xs |> go
  ;;
end

(* Exercise 3.4 (Cho and Sahni [CS96]) Weight-biased leftist heaps are an alternative to
   leftist heaps that replace the leftist property with the weight-biased leftist
   property: the size of any left child is at least as large as the size of its right
   sibling. *)

(* (b) Modify the implementation in Figure 3.2 to obtain weight-biased leftist heaps. *)

module WeightBiasedLeftistHeap (Element : ORDERED) : HEAP with module Element = Element =
struct
  module Element = Element

  type elem = Element.t

  type heap =
    | Empty
    | Heap of
        { size : int
        ; value : elem
        ; left : heap
        ; right : heap
        }

  let size = function
    | Empty -> 0
    | Heap { size } -> size
  ;;

  let heap z v a b = Heap { size = z; value = v; left = a; right = b }
  let heap1 x = heap 1 x Empty Empty
  let empty = Empty

  let is_empty = function
    | Empty -> true
    | Heap _ -> false
  ;;

  (* (c) Currently, merge operates in two passes: a top-down pass consisting of calls to
     merge, and a bottom-up pass consisting of calls to the helper function makeT. Modify
     merge for weight-biased leftist heaps to operate in a single, top-down pass. *)

  let rec merge h1 h2 =
    match h1, h2 with
    | _, Empty -> h1
    | Empty, _ -> h2
    | Heap a, Heap b ->
      let new_size = size h1 + size h2 in
      if Element.leq a.value b.value
      then
        if size a.left >= size a.right + size h2
        then heap new_size a.value a.left (merge a.right h2)
        else heap new_size a.value (merge a.right h2) a.left
      else if size b.left >= size b.right + size h1
      then heap new_size b.value b.left (merge h1 b.right)
      else heap new_size b.value (merge h1 b.right) b.left
  ;;

  let rec insert x = function
    | Empty -> heap1 x
    | Heap { value; left; right } as h ->
      let new_size = size h + 1 in
      if Element.leq x value
      then heap new_size x h Empty
      else if size left >= size right + 1
      then heap new_size value left (insert x right)
      else heap new_size value (insert x right) left
  ;;

  let find_min = function
    | Empty -> raise (Failure "find_min: empty heap")
    | Heap { value } -> value
  ;;

  let delete_min = function
    | Empty -> raise (Failure "delete_min: empty heap")
    | Heap { left; right } -> merge left right
  ;;
end

module BinomialHeap (Element : ORDERED) : HEAP with module Element = Element = struct
  module Element = Element

  type elem = Element.t
  type tree = Node of (int * elem * tree list)
  type heap = tree list

  let empty = []

  let is_empty = function
    | [] -> true
    | _ -> false
  ;;

  let rank (Node (r, _, _)) = r
  let root (Node (_, x, _)) = x

  let link (Node (r, v1, c1) as t1) (Node (_, v2, c2) as t2) =
    if Element.leq v1 v2 then Node (r + 1, v1, t2 :: c1) else Node (r + 1, v2, t1 :: c2)
  ;;

  let rec ins_tree t = function
    | [] -> [ t ]
    | t' :: ts' as ts -> if rank t < rank t' then t :: ts else ins_tree (link t t') ts'
  ;;

  let insert x h = ins_tree (Node (0, x, [])) h

  let rec merge h1 h2 =
    match h1, h2 with
    | _, [] -> h1
    | [], _ -> h2
    | t1 :: t1s, t2 :: t2s ->
      if rank t1 < rank t2
      then t1 :: merge t1s h2
      else if rank t1 > rank t2
      then t2 :: merge h1 t2s
      else ins_tree (link t1 t2) (merge t1s t2s)
  ;;

  let rec remove_min_tree = function
    | [] -> raise (Failure "remove_min_tree: empty tree")
    | [ t ] -> t, []
    | t :: ts ->
      let t', ts' = remove_min_tree ts in
      if Element.leq (root t) (root t') then t, ts else t', t :: ts'
  ;;

  (* Exercise 3.5 Define findMin directly rather than via a call to removeMinTree. *)

  let find_min = function
    | [] -> raise (Failure "find_min: empty heap")
    | t :: ts ->
      let rec go acc = function
        | [] -> acc
        | x :: xs ->
          let r = root x in
          go (if Element.lt r acc then r else acc) xs
      in
      go (root t) ts
  ;;

  let delete_min h =
    let Node (_, _, ts), h' =
      try remove_min_tree h with
      | Failure _ -> raise (Failure "delete_min: empty heap")
    in
    merge (List.rev ts) h'
  ;;
end

(* Exercise 3.6 Most of the rank annotations in this representation of binomial heaps are
   redundant because we know that the children of a node of rank r have ranks r - 1,...,
   0. Thus, we can remove the rank annotations from each node and instead pair each tree
   at the top-level with its rank, i.e.,

   datatype Tree = Node of Elem x Tree list

   type Heap = (int x Tree) list

   Reimplement binomial heaps with this new representation. *)

module RanklessBinomialHeap (Element : ORDERED) : HEAP with module Element = Element =
struct
  module Element = Element

  type elem = Element.t
  type tree = Node of (elem * tree list)
  type heap = (int * tree) list

  let empty = []

  let is_empty = function
    | [] -> true
    | _ -> false
  ;;

  let root (Node (x, _)) = x

  let link r (Node (v1, c1) as t1) (Node (v2, c2) as t2) =
    if Element.leq v1 v2 then r + 1, Node (v1, t2 :: c1) else r + 1, Node (v2, t1 :: c2)
  ;;

  let rec ins_tree (r, t) = function
    | [] -> [ r, t ]
    | (r', t') :: ts' as ts -> if r < r' then (r, t) :: ts else ins_tree (link r t t') ts'
  ;;

  let insert x h = ins_tree (0, Node (x, [])) h

  let rec merge h1 h2 =
    match h1, h2 with
    | _, [] -> h1
    | [], _ -> h2
    | ((r1, tr1) as t1) :: t1s, ((r2, tr2) as t2) :: t2s ->
      if r1 < r2
      then t1 :: merge t1s h2
      else if r1 > r2
      then t2 :: merge h1 t2s
      else ins_tree (link r1 tr1 tr2) (merge t1s t2s)
  ;;

  let rec remove_min_tree = function
    | [] -> raise (Failure "remove_min_tree: empty tree")
    | [ rt ] -> rt, []
    | ((_, t) as rt) :: ts ->
      let ((_, t') as rt'), ts' = remove_min_tree ts in
      if Element.leq (root t) (root t') then rt, ts else rt', rt :: ts'
  ;;

  let find_min h =
    let (_, t), _ =
      try remove_min_tree h with
      | Failure _ -> raise (Failure "find_min: empty heap")
    in
    root t
  ;;

  let delete_min h =
    let (_, Node (_, ts)), h' =
      try remove_min_tree h with
      | Failure _ -> raise (Failure "delete_min: empty heap")
    in
    merge (ts |> List.rev |> List.mapi (fun i t -> i, t)) h'
  ;;
end

(* Exercise 3.7 One clear advantage of leftist heaps over binomial heaps is that findMin
   takes only 0(1) time, rather than O(log n) time. The following functor skeleton
   improves the running time of findMin to 0(1) by storing the minimum element separately
   from the rest of the heap. *)

module ExplicitMin (H : HEAP) : HEAP with module Element = H.Element = struct
  module Element = H.Element

  type elem = H.Element.t

  type heap =
    | Empty
    | Heap of (elem * H.heap)

  let empty = Empty

  let is_empty = function
    | Empty -> true
    | _ -> false
  ;;

  let insert x = function
    | Empty -> Heap (x, H.insert x H.empty)
    | Heap (e, h) -> Heap ((if H.Element.leq x e then x else e), H.insert x h)
  ;;

  let merge h1 h2 =
    match h1, h2 with
    | _, Empty -> h1
    | Empty, _ -> h2
    | Heap (e1, h1'), Heap (e2, h2') ->
      Heap ((if H.Element.leq e1 e2 then e1 else e2), H.merge h1' h2')
  ;;

  let find_min = function
    | Empty -> raise (Failure "find_min: empty heap")
    | Heap (e, _) -> e
  ;;

  let delete_min = function
    | Empty -> raise (Failure "delete_min: empty heap")
    | Heap (_, h) ->
      let h' = H.delete_min h in
      if H.is_empty h' then Empty else Heap (H.find_min h', h')
  ;;
end

module type SET = sig
  type elem
  type set

  val empty : set
  val member : elem -> set -> bool
  val insert : elem -> set -> set
end

module RedBlackSet (Element : ORDERED) : SET = struct
  type elem = Element.t

  type color =
    | R
    | B

  type tree =
    | E
    | T of (color * tree * elem * tree)

  type set = tree

  let empty = E

  let rec member x = function
    | E -> false
    | T (_, a, y, b) ->
      if Element.lt x y then member x a else if Element.lt y x then member x b else true
  ;;

  let balance = function
    | B, T (R, T (R, a, x, b), y, c), z, d
    | B, a, x, T (R, T (R, b, y, c), z, d)
    | B, a, x, T (R, b, y, T (R, c, z, d)) -> T (R, T (B, a, x, b), y, T (B, c, z, d))
    | body -> T body
  ;;

  let insert x s =
    let rec ins = function
      | E -> T (R, E, x, E)
      | T (color, a, y, b) ->
        if Element.lt x y
        then balance (color, ins a, y, b)
        else if Element.lt y x
        then balance (color, a, y, ins b)
        else s
    in
    match ins s with
    | E -> E
    | T (_, a, y, b) -> T (B, a, y, b)
  ;;
end
