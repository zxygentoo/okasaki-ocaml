module type ORDERED = sig
  type t

  val eq : t -> t -> bool
  val lt : t -> t -> bool
  val leq : t -> t -> bool
end

module type HEAP = sig
  type elem
  type heap

  val empty : heap
  val is_empty : heap -> bool
  val insert : elem -> heap -> heap
  val merge : heap -> heap -> heap
  val find_min : heap -> elem (* raises Failure if heap is empty *)
  val delete_min : heap -> heap (* raises Failure if heap is empty *)
  val from_list : elem list -> heap
end

(* Leftist heaps [Cra72, Knu73a] are heap-ordered binary trees that satisfy the leftist
   property: the rank of any left child is at least as large as the rank of its right
   sibling. The rank of a node is defined to be the length of its right spine (i.e., the
   rightmost path from the node in question to an empty node). A simple consequence of the
   leftist property is that the right spine of any node is always the shortest path to an
   empty node. *)

module LeftistHeap (Element : ORDERED) : HEAP with type elem = Element.t = struct
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
    | Empty -> raise (Failure "find_min")
    | Heap { value } -> value
  ;;

  let delete_min = function
    | Empty -> raise (Failure "delete_min")
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

module WeightBiasedLeftistHeap (Element : ORDERED) : HEAP with type elem = Element.t =
struct
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
    | Empty -> raise (Failure "find_min")
    | Heap { value } -> value
  ;;

  let delete_min = function
    | Empty -> raise (Failure "delete_min")
    | Heap { left; right } -> merge left right
  ;;

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
