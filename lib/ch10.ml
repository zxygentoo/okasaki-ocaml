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
    let err () = raise (Failure "lookup: not found") in
    if i < 0
    then err ()
    else (
      match xs with
      | Nil -> err ()
      | One (x, _) when i = 0 -> x
      | One (_, ps) -> lookup (i - 1) (Zero ps)
      | Zero ps ->
        let x, y = lookup (i / 2) ps in
        if i mod 2 = 0 then x else y)
  ;;

  let rec fupdate : 'a. ('a -> 'a) -> int -> 'a rlist -> 'a rlist =
    fun f i xs ->
    let err () = raise (Failure "update: not found") in
    if i < 0
    then err ()
    else (
      match xs with
      | Nil -> err ()
      | One (x, ps) when i = 0 -> One (f x, ps)
      | One (x, ps) -> cons x (fupdate f (i - 1) (Zero ps))
      | Zero ps ->
        let f' (x, y) = if i mod 2 = 0 then f x, y else x, f y in
        Zero (fupdate f' (i / 2) ps))
  ;;

  let update i e xs = fupdate (fun _ -> e) i xs
end

(* Exercise 10.2 Reimplement AltBinaryRandomAccessList so that cons, head, and tail all
  run in 0(1) amortized time, using the type

    datatype a RList = 
          NIL
        | ONE of a x (a x a) RList susp
        | Two of a x a x (a x a) RList susp
        | THREE of a x a x a x (a x a) RList susp
*)

module AltBinaryRandomAccessList : RANDOM_ACCESS_LIST = struct
  type 'a rlist =
    | Nil
    | One of 'a * ('a * 'a) rlist lazy_t
    | Two of 'a * 'a * ('a * 'a) rlist lazy_t
    | Three of 'a * 'a * 'a * ('a * 'a) rlist lazy_t

  let empty = Nil

  let is_empty = function
    | Nil -> true
    | _ -> false
  ;;

  let rec cons : 'a. 'a -> 'a rlist -> 'a rlist =
    fun x -> function
    | Nil -> One (x, lazy Nil)
    | One (a, ps) -> Two (x, a, ps)
    | Two (a, b, ps) -> Three (x, a, b, ps)
    | Three (a, b, c, ps) -> Two (x, a, lazy (cons (b, c) (Lazy.force ps)))
  ;;

  let rec uncons : 'a. 'a rlist lazy_t -> 'a * 'a rlist lazy_t =
    fun xs ->
    match Lazy.force xs with
    | Nil -> assert false
    | One (a, (lazy Nil)) -> a, lazy Nil
    | One (a, ps) ->
      ( a
      , lazy
          (let (b, c), ps' = uncons ps in
           Two (b, c, ps')) )
    | Two (a, b, ps) -> a, lazy (One (b, ps))
    | Three (a, b, c, ps) -> a, lazy (Two (b, c, ps))
  ;;

  let head xs =
    if is_empty xs
    then raise (Failure "head: empty list")
    else (
      let x, _ = uncons (lazy xs) in
      x)
  ;;

  let tail xs =
    if is_empty xs
    then raise (Failure "tail: empty list")
    else (
      let _, xs' = uncons (lazy xs) in
      Lazy.force xs')
  ;;

  let rec lookup : 'a. int -> 'a rlist -> 'a =
    fun i xs ->
    let err () = raise (Failure "lookup: not found") in
    if i < 0
    then err ()
    else (
      match xs with
      | Nil -> err ()
      | One (a, (lazy Nil)) -> if i = 0 then a else err ()
      | One (a, (lazy ps)) ->
        if i = 0
        then a
        else (
          let b, c = lookup ((i - 1) / 2) ps in
          if i mod 2 = 1 then b else c)
      | Two (a, b, ps) -> if i = 0 then a else lookup (i - 1) (One (b, ps))
      | Three (a, b, c, ps) -> if i = 0 then a else lookup (i - 1) (Two (b, c, ps)))
  ;;

  let rec fupdate : 'a. ('a -> 'a) -> int -> 'a rlist -> 'a rlist =
    fun f i xs ->
    let err () = raise (Failure "update: not found") in
    if i < 0
    then err ()
    else (
      match xs with
      | Nil -> err ()
      | One (a, (lazy Nil)) -> if i = 0 then One (f a, lazy Nil) else err ()
      | One (a, (lazy ps)) ->
        if i = 0
        then One (f a, lazy ps)
        else (
          let f' (x, y) = if i mod 2 = 1 then f x, y else x, f y in
          let ps' = fupdate f' ((i - 1) / 2) ps in
          One (a, lazy ps'))
      | Two (a, b, ps) ->
        if i = 0 then Two (f a, b, ps) else cons a (fupdate f (i - 1) (One (b, ps)))
      | Three (a, b, c, ps) ->
        if i = 0
        then Three (f a, b, c, ps)
        else cons a (fupdate f (i - 1) (Two (b, c, ps))))
  ;;

  let update i e xs = fupdate (fun _ -> e) i xs
end
