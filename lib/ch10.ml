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

module type QUEUE = sig
  type 'a queue

  val empty : 'a queue
  val is_empty : 'a queue -> bool
  val snoc : 'a queue -> 'a -> 'a queue
  val head : 'a queue -> 'a
  val tail : 'a queue -> 'a queue
end

(* Figure 10.2 *)

module BootstrappedQueueFigure : QUEUE = struct
  type 'a queue =
    | E
    | Q of int * 'a list * 'a list lazy_t queue * int * 'a list

  let empty = E

  let is_empty = function
    | E -> true
    | _ -> false
  ;;

  let rec check : 'a. int * 'a list * 'a list lazy_t queue * int * 'a list -> 'a queue =
    fun ((lenfm, f, m, lenr, r) as q) ->
    if lenr <= lenfm
    then checkf q
    else checkf (lenfm + lenr, f, snoc m (lazy (List.rev r)), 0, [])

  and checkf : 'a. int * 'a list * 'a list lazy_t queue * int * 'a list -> 'a queue =
    fun (lenfm, f, m, lenr, r) ->
    match f, m with
    | [], E -> E
    | [], _ -> Q (lenfm, Lazy.force (head m), tail m, lenr, r)
    | _ -> Q (lenfm, f, m, lenr, r)

  and snoc : 'a. 'a queue -> 'a -> 'a queue =
    fun q x ->
    match q with
    | E -> Q (1, [ x ], E, 0, [])
    | Q (lenfm, f, m, lenr, r) -> check (lenfm, f, m, lenr + 1, x :: r)

  and head : 'a. 'a queue -> 'a = function
    | E -> raise (Failure "head: empty queue")
    | Q (_, x :: _, _, _, _) -> x
    | _ -> assert false

  and tail : 'a. 'a queue -> 'a queue = function
    | E -> raise (Failure "tail: empty queue")
    | Q (lenfm, _ :: f', m, lenr, r) -> check (lenfm - 1, f', m, lenr, r)
    | _ -> assert false
  ;;
end

(* Exercise 10.4 Implement these queues without polymorphic recursion using the types 
  datatype a EL = ELEM of a | LIST of a EL list susp
  datatype a Queue = E | Q of int x a EL list x a Queue x int x a EL list
*)

module BootstrappedQueueNoPolymorphicRecursion : QUEUE = struct
  type 'a el =
    | El of 'a
    | L of 'a el list lazy_t

  type 'a queue =
    | E
    | Q of int * 'a el list * 'a queue * int * 'a el list

  let empty = E

  let is_empty = function
    | E -> true
    | _ -> false
  ;;

  let head_el = function
    | E -> raise (Failure "head: empty queue")
    | Q (_, el :: _, _, _, _) -> el
    | _ -> assert false
  ;;

  let head q =
    match head_el q with
    | El x -> x
    | _ -> assert false
  ;;

  let rec check ((lenfm, f, m, lenr, r) as q) =
    if lenr <= lenfm
    then checkf q
    else checkf (lenfm + lenr, f, snoc_el m (L (lazy (List.rev r))), 0, [])

  and checkf (lenfm, f, m, lenr, r) =
    match f, m with
    | [], E -> E
    | [], _ ->
      (match head_el m with
       | L (lazy xs) -> Q (lenfm, xs, tail m, lenr, r)
       | _ -> assert false)
    | _ -> Q (lenfm, f, m, lenr, r)

  and tail = function
    | E -> raise (Failure "tail: empty queue")
    | Q (lenfm, _ :: f', m, lenr, r) -> check (lenfm - 1, f', m, lenr, r)
    | _ -> assert false

  and snoc_el q el =
    match q with
    | E -> Q (1, [ el ], E, 0, [])
    | Q (lenfm, f, m, lenr, r) -> check (lenfm, f, m, lenr + 1, el :: r)
  ;;

  let snoc q x = snoc_el q (El x)
end
