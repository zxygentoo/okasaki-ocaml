module type STACK = sig
  type 'a stack

  val empty : 'a stack
  val is_empty : 'a stack -> bool
  val cons : 'a -> 'a stack -> 'a stack
  val head : 'a stack -> 'a
  val tail : 'a stack -> 'a stack
  val update : int -> 'a -> 'a stack -> 'a stack
  val ( ++ ) : 'a stack -> 'a stack -> 'a stack
end

module ListStack : STACK = struct
  type 'a stack = 'a list

  let empty = []
  let is_empty = List.is_empty
  let cons x s = x :: s

  let head = function
    | [] -> raise (Failure "head")
    | hd :: _ -> hd
  ;;

  let tail = function
    | [] -> raise (Failure "tail")
    | _ :: tl -> tl
  ;;

  let rec update i v s =
    if i < 0
    then raise (Failure "update")
    else (
      match s, i with
      | [], _ -> raise (Failure "update")
      | _ :: xs, 0 -> cons v xs
      | x :: xs, _ -> cons x (update (i - 1) v xs))
  ;;

  let ( ++ ) = ( @ )
end

module CustomStack : STACK = struct
  type 'a stack =
    | Nil
    | Cons of 'a * 'a stack

  let empty = Nil

  let is_empty = function
    | Nil -> true
    | Cons _ -> false
  ;;

  let cons x s = Cons (x, s)

  let head = function
    | Nil -> raise (Failure "head")
    | Cons (hd, _) -> hd
  ;;

  let tail = function
    | Nil -> raise (Failure "tail")
    | Cons (_, tl) -> tl
  ;;

  let rec update i v s =
    if i < 0
    then raise (Failure "update")
    else (
      match s, i with
      | Nil, _ -> raise (Failure "update")
      | Cons (_, tl), 0 -> cons v tl
      | Cons (hd, tl), _ -> cons hd (update (i - 1) v tl))
  ;;

  let rec ( ++ ) s1 s2 =
    match s1 with
    | Nil -> s2
    | Cons (hd, tl) -> cons hd (tl ++ s2)
  ;;
end

(* Exercise 2.1 Write a function suffixes of type a list -» a list list that takes a list
   xs and returns a list of all the suffixes of xs in decreasing order of length. For
   example, suffixes [1,2,3,4] = [[1,2,3,4], [2,3,4], [3,4], [4], []] Show that the
   resulting list of suffixes can be generated in O(n) time and represented in O(n) space.
*)

let rec suffixes = function
  | [] -> [ [] ]
  | _ :: tl as xs -> xs :: suffixes tl
;;

type 'a tree =
  | Empty
  | Tree of 'a tree * 'a * 'a tree

module type ORDERED = sig
  type t

  val eq : t -> t -> bool
  val lt : t -> t -> bool
  val leq : t -> t -> bool
end

module type SET = sig
  type elem
  type set

  val empty : set
  val member : elem -> set -> bool
  val insert : elem -> set -> set
end

exception Already_present

module UnbalancedSet (Element : ORDERED) : SET with type elem = Element.t = struct
  type elem = Element.t
  type set = elem tree

  let empty = Empty

  (* Exercise 2.2 (Andersson [And91]) In the worst case, member performs approximately 2d
     comparisons, where d is the depth of the tree. Rewrite member to take no more than
     d + 1 comparisons by keeping track of a candidate element that might be equal to the
     query element (say, the last element for which < returned false or < returned true)
     and checking for equality only when you hit the bottom of the tree.
  *)

  let member x s =
    let rec go x candidate = function
      | Empty ->
        (match candidate with
         | None -> false
         | Some v -> Element.eq x v)
      | Tree (l, v, r) -> if Element.lt x v then go x candidate l else go x (Some v) r
    in
    go x None s
  ;;

  (* Exercise 2.3 Inserting an existing element into a binary search tree copies the
     entire search path even though the copied nodes are indistinguishable from the
     originals. Rewrite insert using exceptions to avoid this copying. Establish only one
     handler per insertion rather than one handler per iteration.

     Exercise 2.4 Combine the ideas of the previous two exercises to obtain a version of
     insert that performs no unnecessary copying and uses no more than d + 1 comparisons. *)

  let insert x s =
    let rec go candidate = function
      | Empty ->
        (match candidate with
         | None -> Tree (Empty, x, Empty)
         | Some v ->
           if Element.eq x v then raise Already_present else Tree (Empty, x, Empty))
      | Tree (l, v, r) ->
        if Element.lt x v then Tree (go candidate l, v, r) else Tree (l, v, go (Some v) r)
    in
    try go None s with
    | Already_present -> s
  ;;
end

(* Exercise 2.5 Sharing can also be useful within a single object, not just between
   objects. For example, if the two subtrees of a given node are identical, then they can
   be represented by the same tree. *)

(* (a) Using this idea, write a function complete of type Elem x int -> Tree where
       complete (x, d) creates a complete binary tree of depth d with x stored in every
       node. (Of course, this function makes no sense for the set abstraction, but it can
       be useful as an auxiliary function for other abstractions, such as bags.) This
       function should run in O(d) time. *)

let complete x d =
  let rec go v d =
    if d = 0
    then Tree (Empty, v, Empty)
    else (
      let t = go v (d - 1) in
      Tree (t, v, t))
  in
  if d < 0 then invalid_arg "complete: negative d" else go x d
;;

(* (b) Extend this function to create balanced trees of arbitrary size. These trees will
   not always be complete binary trees, but should be as balanced as possible: for any
   given node, the two subtrees should differ in size by at most one. This function should
   run in 0(log n) time. (Hint: use a helper function create2 that, given a size m,
   creates a pair of trees, one of size m and one of size m+1.) *)

let create x n =
  if n < 0
  then invalid_arg "create: negative n"
  else (
    let rec create2 m =
      if m = 0
      then Empty, Tree (Empty, x, Empty)
      else if m mod 2 = 1
      then (
        let a, b = create2 (m / 2) in
        Tree (a, x, a), Tree (b, x, a))
      else (
        let a, b = create2 ((m - 2) / 2) in
        Tree (b, x, a), Tree (b, x, b))
    in
    fst (create2 n))
;;

(* Exercise 2.6 Adapt the UnbalancedSet functor to support finite maps rather than sets.
   Figure 2.10 gives a minimal signature for finite maps. (Note that the NOTFOUND
   exception is not predefined in Standard ML—you will have to define it yourself.
   Although this exception could be made part of the FINITEMAP signature, with every
   implementation defining its own NOTFOUND exception, it is convenient for all finite
   maps to use the same exception.) *)

module type FINITE_MAP = sig
  type key
  type 'a map

  val empty : 'a map
  val lookup : key -> 'a map -> 'a (* raises Not_found *)
  val bind : key -> 'a -> 'a map -> 'a map
end

module UnbalancedMap (Key : ORDERED) :
  FINITE_MAP with type key = Key.t and type 'a map = (Key.t * 'a) tree = struct
  type key = Key.t
  type 'a map = (key * 'a) tree

  let empty = Empty

  let lookup key m =
    let rec go candidate = function
      | Empty ->
        (match candidate with
         | Some (k, v) -> if Key.eq key k then v else raise Not_found
         | None -> raise Not_found)
      | Tree (l, (k, v), r) -> if Key.lt key k then go candidate l else go (Some (k, v)) r
    in
    go None m
  ;;

  let rec bind key value = function
    | Empty -> Tree (Empty, (key, value), Empty)
    | Tree (l, ((k, _) as kv), r) ->
      if Key.lt key k
      then Tree (bind key value l, kv, r)
      else if Key.lt k key
      then Tree (l, kv, bind key value r)
      else Tree (l, (key, value), r)
  ;;
end
