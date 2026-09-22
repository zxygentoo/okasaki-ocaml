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

module SplayHeap (Element : ORDERED) : HEAP_WITH_SORT with module Element = Element =
struct
  module Element = Element

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
