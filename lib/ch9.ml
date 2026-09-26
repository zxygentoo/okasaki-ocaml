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

module BinaryRandomAccessList : RANDOM_ACCESS_LIST = struct
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

  let rec uncons_tree = function
    | [] -> raise (Failure "uncons_tree: empty list")
    | [ One t ] -> t, []
    | One t :: ts -> t, Zero :: ts
    | Zero :: ts ->
      (match uncons_tree ts with
       | Node (_, t1, t2), ts' -> t1, One t2 :: ts'
       | _ -> raise (Failure "uncons_tree: invalid tree"))
  ;;

  let head ds =
    if ds = []
    then raise (Failure "head: empty list")
    else (
      match uncons_tree ds with
      | Leaf e, _ -> e
      | _ -> raise (Failure "head: invalid tree"))
  ;;

  let tail ds =
    if ds = []
    then raise (Failure "tail: empty list")
    else (
      let _, ts = uncons_tree ds in
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
end
