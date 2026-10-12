module type RANDOM_ACCESS_LIST_LITE = sig
  type 'a rlist

  val empty : 'a rlist
  val is_empty : 'a rlist -> bool
  val cons : 'a -> 'a rlist -> 'a rlist
  val head : 'a rlist -> 'a
  val tail : 'a rlist -> 'a rlist
end

module type RANDOM_ACCESS_LIST = sig
  include RANDOM_ACCESS_LIST_LITE

  val lookup : int -> 'a rlist -> 'a
  val update : int -> 'a -> 'a rlist -> 'a rlist
end

module AltBinaryRandomAccessListFigure : RANDOM_ACCESS_LIST = struct
  type 'a rlist =
    | Nil
    | Zero of ('a * 'a) rlist
    | One of 'a * ('a * 'a) rlist

  let empty = Nil

  let is_empty = function
    | Nil -> true
    | _ -> false
  ;;

  let rec cons : 'a. 'a -> 'a rlist -> 'a rlist =
    fun x -> function
    | Nil -> One (x, Nil)
    | Zero ps -> One (x, ps)
    | One (y, ps) -> Zero (cons (x, y) ps)
  ;;

  let rec uncons : 'a. 'a rlist -> 'a * 'a rlist = function
    | One (x, Nil) -> x, Nil
    | One (x, ps) -> x, Zero ps
    | Zero ps ->
      let (x, y), ps' = uncons ps in
      x, One (y, ps')
    | _ -> assert false
  ;;

  let head xs =
    if is_empty xs
    then raise (Failure "head: empty list")
    else (
      let x, _ = uncons xs in
      x)
  ;;

  let tail xs =
    if is_empty xs
    then raise (Failure "tail: empty list")
    else (
      let _, xs' = uncons xs in
      xs')
  ;;

  let rec lookup : 'a. int -> 'a rlist -> 'a =
    fun i xs ->
    if i < 0
    then raise (Failure "lookup: not found")
    else (
      match xs with
      | Nil -> raise (Failure "lookup: not found")
      | One (x, _) when i = 0 -> x
      | One (_, ps) -> lookup (i - 1) (Zero ps)
      | Zero ps ->
        let x, y = lookup (i / 2) ps in
        if i mod 2 = 0 then x else y)
  ;;

  let rec fupdate : 'a. ('a -> 'a) -> int -> 'a rlist -> 'a rlist =
    fun f i xs ->
    if i < 0
    then raise (Failure "update: not found")
    else (
      match xs with
      | Nil -> raise (Failure "update: not found")
      | One (x, ps) when i = 0 -> One (f x, ps)
      | One (x, ps) -> cons x (fupdate f (i - 1) (Zero ps))
      | Zero ps ->
        let f' (x, y) = if i mod 2 = 0 then f x, y else x, f y in
        Zero (fupdate f' (i / 2) ps))
  ;;

  let update i y xs = fupdate (fun _ -> y) i xs
end
