(* Figure 9.1 dense representation *)

module Dense = struct
  type digit =
    | Zero
    | One

  type nat = digit list

  let rec inc = function
    | [] -> [ One ]
    | Zero :: ds -> One :: ds
    | One :: ds -> Zero :: inc ds
  ;;

  let rec dec = function
    | [ One ] -> []
    | One :: ds -> Zero :: ds
    | Zero :: ds -> One :: dec ds
    | _ -> raise (Failure "dec: zero")
  ;;

  let rec add a b =
    match a, b with
    | _, [] -> a
    | [], _ -> b
    | x :: xs, Zero :: ys -> x :: add xs ys
    | Zero :: xs, y :: ys -> y :: add xs ys
    | One :: xs, One :: ys -> Zero :: inc (add xs ys)
  ;;
end

(* Figure 9.1 spare representation by weight *)

module SparseByWeight = struct
  type nat = int list

  let rec carry w = function
    | [] -> [ w ]
    | x :: xs as ws -> if w < x then w :: ws else carry (2 * w) xs
  ;;

  let rec borrow w = function
    | x :: xs as ws -> if w = x then xs else w :: borrow (2 * w) ws
    | _ -> raise (Failure "borrow: zero")
  ;;

  let inc w = carry 1 w
  let dec w = borrow 1 w

  let rec add a b =
    match a, b with
    | _, [] -> a
    | [], _ -> b
    | x :: xs, y :: ys ->
      if x < y
      then x :: add xs b
      else if y < x
      then y :: add a ys
      else carry (2 * x) (add xs ys)
  ;;
end

module type RANDOM_ACCESS_LIST = sig
  type 'a rlist

  val empty : 'a rlist
  val is_empty : 'a rlist -> bool
  val cons : 'a -> 'a rlist -> 'a rlist
  val head : 'a rlist -> 'a
  val tail : 'a rlist -> 'a rlist
  val lookup : int -> 'a rlist -> 'a
  val update : int -> 'a -> 'a rlist -> 'a rlist
end

module type RANDOM_ACCESS_LIST_WITH_DROP_AND_CREATE = sig
  include RANDOM_ACCESS_LIST

  val drop : int -> 'a rlist -> 'a rlist
  val create : int -> 'a -> 'a rlist
end

module BinaryRandomAccessList : RANDOM_ACCESS_LIST_WITH_DROP_AND_CREATE = struct
  type 'a tree =
    | Leaf of 'a
    | Node of int * 'a tree * 'a tree

  type 'a digit =
    | Zero
    | One of 'a tree

  type 'a rlist = 'a digit list

  let empty = []

  let is_empty = function
    | [] -> true
    | _ -> false
  ;;

  let size = function
    | Leaf _ -> 1
    | Node (w, _, _) -> w
  ;;

  let link t1 t2 = Node (size t1 + size t2, t1, t2)

  let rec cons_tree t1 = function
    | [] -> [ One t1 ]
    | Zero :: ts -> One t1 :: ts
    | One t2 :: ts -> Zero :: cons_tree (link t1 t2) ts
  ;;

  let cons e ds = cons_tree (Leaf e) ds

  let rec uncons = function
    | [] -> raise (Failure "uncons: empty list")
    | [ One t ] -> t, []
    | One t :: ts -> t, Zero :: ts
    | Zero :: ts ->
      (match uncons ts with
       | Node (_, t1, t2), ts' -> t1, One t2 :: ts'
       | _ -> raise (Failure "uncons: invalid tree"))
  ;;

  let head ds =
    if is_empty ds
    then raise (Failure "head: empty list")
    else (
      match uncons ds with
      | Leaf e, _ -> e
      | _ -> raise (Failure "head: invalid tree"))
  ;;

  let tail ds =
    if is_empty ds
    then raise (Failure "tail: empty list")
    else (
      let _, ts = uncons ds in
      ts)
  ;;

  let rec lookup_tree i = function
    | Leaf x when i = 0 -> x
    | Node (w, t1, t2) ->
      if i < w / 2 then lookup_tree i t1 else lookup_tree (i - (w / 2)) t2
    | _ -> raise (Failure "lookup: not found")
  ;;

  let rec lookup i = function
    | [] -> raise (Failure "lookup: not found")
    | Zero :: ts -> lookup i ts
    | One t :: ts -> if i < size t then lookup_tree i t else lookup (i - size t) ts
  ;;

  let rec update_tree i e = function
    | Leaf _ when i = 0 -> Leaf e
    | Node (w, t1, t2) ->
      if i < w / 2
      then Node (w, update_tree i e t1, t2)
      else Node (w, t1, update_tree (i - (w / 2)) e t2)
    | _ -> raise (Failure "update: not found")
  ;;

  let rec update i e = function
    | [] -> raise (Failure "update: not found")
    | Zero :: ts -> Zero :: update i e ts
    | One t :: ts ->
      if i < size t
      then One (update_tree i e t) :: ts
      else One t :: update (i - size t) e ts
  ;;

  (* Exercise 9.1 Write a function drop of type int x a RList ->- a RList that deletes the
     first k elements of a binary random-access list. Your function should run in O(log n)
     time. *)

  let rec pad n ds =
    match n, ds with
    | 0, _ | _, [] -> ds
    | _ -> pad (n - 1) (Zero :: ds)
  ;;

  let rec drop_tree i p k r =
    match k with
    | _ when i = 0 -> pad p (One k :: r)
    | Node (w, t1, t2) ->
      let p' = p - 1 in
      if i < w / 2
      then drop_tree i p' t1 (One t2 :: r)
      else if i > w / 2
      then drop_tree (i - (w / 2)) p' t2 (pad 1 r)
      else drop_tree 0 p' t2 r
    | _ -> raise (Failure "drop: invalid tree")
  ;;

  let drop n ds =
    let rec go i p = function
      | ts when i = 0 -> pad p ts
      | Zero :: ts -> go i (p + 1) ts
      | One t :: ts ->
        if i < size t then drop_tree i p t (pad 1 ts) else go (i - size t) (p + 1) ts
      | _ -> raise (Failure "drop: not enough elements")
    in
    go n 0 ds
  ;;

  (* Exercise 9.2 Write a function create of type int x a -> a RList that creates a binary
     random-access list containing n copies of some value x. This function should also run
     in O(log n) time. (You may find it helpful to review Exercise 2.5.) *)

  let pow n = 1 lsl n

  let rank x =
    let rec go acc x = if x = 0 then acc else go (acc + 1) (x lsr 1) in
    go 0 x
  ;;

  let rec create_tree e r =
    if r = 0
    then Leaf e
    else (
      let t = create_tree e (r - 1) in
      Node (pow r, t, t))
  ;;

  let half_tree = function
    | Leaf _ -> raise (Failure "half_tree")
    | Node (_, a, _) -> a
  ;;

  let create_top_down n e =
    let rec build w t m acc =
      if w / 2 = 0
      then (if n mod 2 = 0 then Zero else One (Leaf e)) :: acc
      else
        build
          (w / 2)
          (half_tree t)
          (if m >= w then m - w else m)
          ((if m >= w then One t else Zero) :: acc)
    in
    if n < 0
    then raise (Failure "create: negative size")
    else if n = 0
    then empty
    else (
      let r = rank n - 1 in
      let t = create_tree e r in
      build (pow r) t n [])
  ;;

  (* Building things bottom-up is way simpler.. *)

  let create_bottom_up n e =
    let rec go n t =
      if n = 0 then [] else (if n mod 2 = 0 then Zero else One t) :: go (n / 2) (link t t)
    in
    if n < 0 then raise (Failure "create: negative size") else go n (Leaf e)
  ;;

  let create = create_bottom_up
end

(* Exercise 9.3 Reimplement BinaryRandomAccessList using a sparse representation such as

   datatype a Tree = LEAF of a | NODE of int x a Tree x a Tree

   type a RList = a Tree list
*)

module SparseBinaryRandomAccessList : RANDOM_ACCESS_LIST_WITH_DROP_AND_CREATE = struct
  type 'a tree =
    | Leaf of 'a
    | Node of int * 'a tree * 'a tree

  type 'a rlist = 'a tree list

  let empty = []

  let is_empty = function
    | [] -> true
    | _ -> false
  ;;

  let size = function
    | Leaf _ -> 1
    | Node (w, _, _) -> w
  ;;

  let link t1 t2 = Node (size t1 + size t2, t1, t2)

  let rec merge = function
    | [] -> []
    | [ x ] -> [ x ]
    | x :: y :: rest as xs -> if size x = size y then merge (link x y :: rest) else xs
  ;;

  let cons e xs = merge (Leaf e :: xs)

  let rec uncons t ts =
    match t with
    | Leaf e -> e, ts
    | Node (_, a, b) -> uncons a (b :: ts)
  ;;

  let head = function
    | [] -> raise (Failure "head: empty list")
    | t :: ts -> fst (uncons t ts)
  ;;

  let tail = function
    | [] -> raise (Failure "tail: empty list")
    | t :: ts -> snd (uncons t ts)
  ;;

  let rec lookup_tree i = function
    | Leaf e when i = 0 -> e
    | Node (w, a, b) -> if i < w / 2 then lookup_tree i a else lookup_tree (i - (w / 2)) b
    | _ -> raise (Failure "lookup: not found")
  ;;

  let rec lookup i = function
    | [] -> raise (Failure "lookup: not found")
    | x :: xs -> if i < size x then lookup_tree i x else lookup (i - size x) xs
  ;;

  let rec update_tree i e = function
    | Leaf _ when i = 0 -> Leaf e
    | Node (w, a, b) ->
      if i < w / 2
      then Node (w, update_tree i e a, b)
      else Node (w, a, update_tree (i - (w / 2)) e b)
    | _ -> raise (Failure "update: not found")
  ;;

  let rec update i e = function
    | [] -> raise (Failure "update: not found")
    | x :: xs ->
      if i < size x then update_tree i e x :: xs else x :: update (i - size x) e xs
  ;;

  let rec drop_tree i x xs =
    match x with
    | _ when i = 0 -> x :: xs
    | Node (w, a, b) ->
      if i < w / 2 then drop_tree i a (b :: xs) else drop_tree (i - (w / 2)) b xs
    | _ -> raise (Failure "drop: invalid tree")
  ;;

  let rec drop n = function
    | xs when n = 0 -> xs
    | [] -> raise (Failure "drop: not enough elements")
    | x :: xs -> if n < size x then drop_tree n x xs else drop (n - size x) xs
  ;;

  let create n e =
    let rec go n t =
      if n = 0
      then []
      else (
        let ts = go (n / 2) (link t t) in
        if n mod 2 = 0 then ts else t :: ts)
    in
    if n < 0 then raise (Failure "create: negative size") else go n (Leaf e)
  ;;
end

(* Exercise 9.4 Write decrement and addition functions for zeroless binary numbers. Note
   that carries during additions can involve either ones or twos. *)

module Zeroless = struct
  type digit =
    | One
    | Two

  type nat = digit list

  let rec inc = function
    | [] -> [ One ]
    | One :: ds -> Two :: ds
    | Two :: ds -> One :: inc ds
  ;;

  let rec dec = function
    | [] -> raise (Failure "dec: zero")
    | [ One ] -> []
    | Two :: ds -> One :: ds
    | One :: Two :: ds -> Two :: One :: ds
    | One :: One :: ds -> Two :: dec (One :: ds)
  ;;

  let rec add a b =
    match a, b with
    | _, [] -> a
    | [], _ -> b
    | One :: xs, One :: ys -> Two :: add xs ys
    | Two :: xs, One :: ys | One :: xs, Two :: ys -> One :: inc (add xs ys)
    | Two :: xs, Two :: ys -> Two :: inc (add xs ys)
  ;;
end
