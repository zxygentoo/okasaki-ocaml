module type QUEUE = sig
  type 'a queue

  val empty : 'a queue
  val is_empty : 'a queue -> bool
  val snoc : 'a queue -> 'a -> 'a queue
  val head : 'a queue -> 'a
  val tail : 'a queue -> 'a queue
end

module BatchedQueue : QUEUE = struct
  type 'a queue = 'a list * 'a list

  let checkf = function
    | [], r -> List.rev r, []
    | q -> q
  ;;

  let empty = [], []
  let is_empty (f, _) = List.is_empty f
  let snoc (f, r) x = checkf (f, x :: r)

  let head = function
    | [], _ -> raise (Failure "head: empty queue")
    | x :: _, _ -> x
  ;;

  let tail = function
    | [], _ -> raise (Failure "tail: empty queue")
    | _ :: f, r -> checkf (f, r)
  ;;
end

(* Exercise 5.1 (Hoogerwoord [Hoo92]) This design can easily be extended to support the
   double-ended queue, or deque, abstraction, which allows reads and writes to both ends
   of the queue (see Figure 5.3). The invariant is updated to be symmetric in its
   treatment of f and r: both are required to be non-empty whenever the deque contains two
   or more elements. When one list becomes empty, we split the other list in half and
   reverse one of the halves.

   (a) Implement this version of deques.
*)
module type DEQUE = sig
  include QUEUE

  val cons : 'a -> 'a queue -> 'a queue
  val last : 'a queue -> 'a
  val init : 'a queue -> 'a queue
end

module Deque : DEQUE = struct
  type 'a queue = 'a list * 'a list

  let rec split_at k xs =
    match k, xs with
    | 0, _ | _, [] -> [], xs
    | _, x :: xs ->
      let f, r = split_at (k - 1) xs in
      x :: f, r
  ;;

  let checkf = function
    | [], [] -> [], []
    | [ x ], [] -> [ x ], []
    | [], [ x ] -> [], [ x ]
    | f, [] ->
      let a, b = split_at (List.length f / 2) f in
      a, List.rev b
    | [], r ->
      let a, b = split_at (List.length r / 2) r in
      List.rev b, a
    | f, r -> f, r
  ;;

  let empty = [], []

  let is_empty = function
    | [], [] -> true
    | _ -> false
  ;;

  let snoc (f, r) x = checkf (f, x :: r)

  let head = function
    | [], [ x ] -> x
    | x :: _, _ -> x
    | _ -> raise (Failure "head: empty queue")
  ;;

  let tail = function
    | [ _ ], [] | [], [ _ ] -> [], []
    | _ :: f, r -> checkf (f, r)
    | _ -> raise (Failure "tail: empty queue")
  ;;

  let cons x (f, r) = checkf (x :: f, r)

  let last = function
    | [ x ], [] -> x
    | _, x :: _ -> x
    | _ -> raise (Failure "last: empty queue")
  ;;

  let init = function
    | [], [ _ ] | [ _ ], [] -> [], []
    | f, _ :: r -> checkf (f, r)
    | _ -> raise (Failure "init: empty queue")
  ;;
end

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

module type HEAP_WITH_SORT = sig
  include HEAP

  val sort : Element.t list -> Element.t list
end

module SplayHeap (E : ORDERED) : HEAP_WITH_SORT with module Element = E = struct
  module Element = E

  type heap =
    | E
    | T of heap * Element.t * heap

  let empty = E

  let is_empty = function
    | E -> true
    | _ -> false
  ;;

  let rec bigger k = function
    | E -> E
    | T (a, x, b) ->
      if Element.leq x k
      then bigger k b
      else (
        match a with
        | E -> T (E, x, b)
        | T (a1, y, a2) ->
          if Element.leq y k
          then T (bigger k a2, x, b)
          else T (bigger k a1, y, T (a2, x, b)))
  ;;

  (* Exercise 5.4 Implement smaller. Keep in mind that smaller should retain equal
     elements (but do not make a separate test for equality!). *)

  let rec smaller k = function
    | E -> E
    | T (a, x, b) ->
      if Element.lt k x
      then smaller k a
      else (
        match b with
        | E -> T (a, x, E)
        | T (b1, y, b2) ->
          if Element.lt k y
          then T (a, x, smaller k b1)
          else T (T (a, x, b1), y, smaller k b2))
  ;;

  let rec partition k = function
    | E -> E, E
    | T (a, x, b) as h ->
      if Element.leq x k
      then (
        match b with
        | E -> h, E
        | T (b1, y, b2) ->
          if Element.leq y k
          then (
            let small, big = partition k b2 in
            T (T (a, x, b1), y, small), big)
          else (
            let small, big = partition k b1 in
            T (a, x, small), T (big, y, b2)))
      else (
        match a with
        | E -> E, h
        | T (a1, y, a2) ->
          if Element.leq y k
          then (
            let small, big = partition k a2 in
            T (a1, y, small), T (big, x, b))
          else (
            let small, big = partition k a1 in
            small, T (big, y, T (a2, x, b))))
  ;;

  let partition x h = smaller x h, bigger x h

  let insert x h =
    let a, b = partition x h in
    T (a, x, b)
  ;;

  let rec merge h1 h2 =
    match h1, h2 with
    | E, _ -> h2
    | T (a, x, b), _ ->
      let ha, hb = partition x h2 in
      T (merge ha a, x, merge hb b)
  ;;

  let rec find_min = function
    | E -> raise (Failure "find_min: empty heap")
    | T (E, x, _) -> x
    | T (a, _, _) -> find_min a
  ;;

  let rec delete_min = function
    | E -> raise (Failure "delete_min: empty heap")
    | T (E, _, b) -> b
    | T (T (E, _, b), y, c) -> T (b, y, c)
    | T (T (a, x, b), y, c) -> T (delete_min a, x, T (b, y, c))
  ;;

  (* Exercise 5.7 Write a sorting function that inserts elements into a splay tree and
     then performs an inorder traversal of the tree, dumping the elements into a list.
     Show that this function takes only O(n) time on an already sorted list. *)

  let sort xs =
    let rec go acc = function
      | E -> acc
      | T (E, x, b) -> go (x :: acc) b
      | T (T (a, x, b), y, c) -> go (x :: go acc a) (T (b, y, c))
    in
    List.fold_left (fun h x -> insert x h) E xs |> go [] |> List.rev
  ;;
end

module PairingHeap (E : ORDERED) : HEAP with module Element = E = struct
  module Element = E

  type heap =
    | E
    | T of Element.t * heap list

  let empty = E

  let is_empty = function
    | E -> true
    | _ -> false
  ;;

  let merge h1 h2 =
    match h1, h2 with
    | _, E -> h1
    | E, _ -> h2
    | T (x, hs1), T (y, hs2) ->
      if Element.leq x y then T (x, h2 :: hs1) else T (y, h1 :: hs2)
  ;;

  let insert x h = merge (T (x, [])) h

  let find_min = function
    | E -> raise (Failure "find_min: empty heap")
    | T (x, _) -> x
  ;;

  let rec merge_pairs = function
    | [] -> E
    | [ h ] -> h
    | h1 :: h2 :: hs -> merge (merge h1 h2) (merge_pairs hs)
  ;;

  let delete_min = function
    | E -> raise (Failure "delete_min: empty heap")
    | T (_, hs) -> merge_pairs hs
  ;;
end

(* Exercise 5.8 Binary trees are often more convenient than multiway trees. Fortunately,
   there is an easy way to represent any multiway tree as a binary tree. Simply convert
   every multiway node into a binary node whose left child represents the leftmost child
   of the multiway node and whose right child represents the sibling to the immediate
   right of the multiway node. If either the leftmost child or the right sibling of the
   multiway node is missing, then the corresponding field in the binary node is empty.
   (Note that this implies that the right child of the root is always empty in the binary
   representation.) Applying this transformation to pairing heaps yields half-ordered
   binary trees in which the element at each node is no greater than any element in its
   left subtree. *)

(* (a) Write a function toBinary that converts pairing heaps from the existing
       representation into the type

   datatype BinTree = E' | T of Elem.T x BinTree x BinTree
*)
module Convert (Element : ORDERED) = struct
  type heap1 =
    | E1
    | T1 of Element.t * heap1 list

  type heap2 =
    | E2
    | T2 of Element.t * heap2 * heap2

  let to_binary h1 =
    let rec go = function
      | [] -> E2
      | E1 :: hs -> go hs
      | T1 (x, hs1) :: hs2 -> T2 (x, go hs1, go hs2)
    in
    match h1 with
    | E1 -> E2
    | T1 (x, hs) -> T2 (x, go hs, E2)
  ;;
end

(* (b) Reimplement pairing heaps using this new representation.

   (c) Adapt the analysis of splay trees to prove that deleteMin and merge run in O(log n)
   amortized time for this new representation (and hence for the old representation as
   well). Use the same potential function as for splay trees.
*)

module BinaryPairingHeap (E : ORDERED) : HEAP with module Element = E = struct
  module Element = E

  type heap =
    | E
    | T of Element.t * heap * heap

  let empty = E

  let is_empty = function
    | E -> true
    | _ -> false
  ;;

  let merge h1 h2 =
    match h1, h2 with
    | _, E -> h1
    | E, _ -> h2
    | T (x, ha, _), T (y, hb, _) ->
      if Element.leq x y then T (x, T (y, hb, ha), E) else T (y, T (x, ha, hb), E)
  ;;

  let insert x h = merge (T (x, E, E)) h

  let find_min = function
    | E -> raise (Failure "find_min: empty heap")
    | T (x, _, _) -> x
  ;;

  let delete_min h =
    let rec go = function
      | E -> E
      | T (_, _, E) as h -> h
      | T (x, a, T (y, b, rest)) -> merge (merge (T (x, a, E)) (T (y, b, E))) (go rest)
    in
    match h with
    | E -> raise (Failure "delete_min: empty heap")
    | T (_, h, _) -> go h
  ;;
end
