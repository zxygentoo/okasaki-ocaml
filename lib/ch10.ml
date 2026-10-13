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

(* Exercise 10.5 Another way to eliminate the need for polymorphic recursion is to
  represent the middle using some other implementation of queues.

  Then the type of bootstrapped queues is

    datatype a Queue =
    E | Q of int x a list x a list susp PrimQ.Queue x int x a list
  
  where PrimQ is the other implementation of queues.

(a) Implement this variation of bootstrapped queues as a functor of the form functor
  BootstrapQueue (PrimQ : QUEUE) : QUEUE = ...
*)

module BootstrappedQueuePrimQ (PrimQ : QUEUE) : QUEUE = struct
  type 'a queue =
    | E
    | Q of int * 'a list * 'a list lazy_t PrimQ.queue * int * 'a list

  let empty = E

  let is_empty = function
    | E -> true
    | _ -> false
  ;;

  let checkf (lenfm, f, m, lenr, r) =
    match f with
    | [] when PrimQ.is_empty m -> E
    | [] -> Q (lenfm, Lazy.force (PrimQ.head m), PrimQ.tail m, lenr, r)
    | _ -> Q (lenfm, f, m, lenr, r)
  ;;

  let check ((lenfm, f, m, lenr, r) as q) =
    if lenr <= lenfm
    then checkf q
    else checkf (lenfm + lenr, f, PrimQ.snoc m (lazy (List.rev r)), 0, [])
  ;;

  let snoc q x =
    match q with
    | E -> Q (1, [ x ], PrimQ.empty, 0, [])
    | Q (lenfm, f, m, lenr, r) -> check (lenfm, f, m, lenr + 1, x :: r)
  ;;

  let head = function
    | E -> raise (Failure "head: empty queue")
    | Q (_, x :: _, _, _, _) -> x
    | _ -> assert false
  ;;

  let tail = function
    | E -> raise (Failure "tail: empty queue")
    | Q (lenfm, _ :: f', m, lenr, r) -> check (lenfm - 1, f', m, lenr, r)
    | _ -> assert false
  ;;
end

(* Figure 10.3 *)

module type CATENABLE_LIST = sig
  type 'a cat

  val empty : 'a cat
  val is_empty : 'a cat -> bool
  val cons : 'a -> 'a cat -> 'a cat
  val snoc : 'a cat -> 'a -> 'a cat
  val ( ++ ) : 'a cat -> 'a cat -> 'a cat
  val head : 'a cat -> 'a
  val tail : 'a cat -> 'a cat
end

module type CATENABLE_LIST_WITH_FLATTEN = sig
  include CATENABLE_LIST

  val flatten : 'a cat list -> 'a cat
end

(* Figure 10.6 *)

module CatenableList (Q : QUEUE) : CATENABLE_LIST_WITH_FLATTEN = struct
  type 'a cat =
    | E
    | C of 'a * 'a cat lazy_t Q.queue

  let empty = E

  let is_empty = function
    | E -> true
    | _ -> false
  ;;

  let link xs ys =
    match xs with
    | C (x, q) -> C (x, Q.snoc q ys)
    | _ -> assert false
  ;;

  let ( ++ ) xs ys =
    match xs, ys with
    | _, E -> xs
    | E, _ -> ys
    | _ -> link xs (lazy ys)
  ;;

  let cons x xs = C (x, Q.empty) ++ xs
  let snoc xs x = xs ++ C (x, Q.empty)

  let head = function
    | E -> raise (Failure "head: empty list")
    | C (x, _) -> x
  ;;

  let rec link_all q =
    let (lazy t) = Q.head q
    and q' = Q.tail q in
    if Q.is_empty q' then t else link t (lazy (link_all q'))
  ;;

  let tail = function
    | E -> raise (Failure "tail: empty list")
    | C (_, q) -> if Q.is_empty q then E else link_all q
  ;;

  (* Exercise 10.6 Write a function flatten of type a Cat list -> a Cat that catenates
    all the elements in a list of catenable lists.
    Show that your function runs in 0(1 + e) amortized time, where e is the number of
    empty catenable lists in the list.
   *)

  let rec flatten = function
    | [] -> E
    | E :: xs -> flatten xs
    | x :: xs ->
      (match List.drop_while is_empty xs with
       | [] -> x
       | ys -> link x (lazy (flatten ys)))
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

(* Figure 10.7 *)

module Bootstrap
    (MakeH : functor (E : ORDERED) -> HEAP with type Element.t = E.t)
    (E : ORDERED) : HEAP with module Element = E = struct
  module Element = E

  module rec BootstrappedElem : sig
    type t =
      | E
      | H of Element.t * PrimH.heap

    val leq : t -> t -> bool
    val eq : t -> t -> bool
    val lt : t -> t -> bool
  end = struct
    type t =
      | E
      | H of Element.t * PrimH.heap

    let leq a b =
      match a, b with
      | H (x, _), H (y, _) -> Element.leq x y
      | _ -> assert false
    ;;

    let eq a b =
      match a, b with
      | H (x, _), H (y, _) -> Element.eq x y
      | _ -> assert false
    ;;

    let lt a b =
      match a, b with
      | H (x, _), H (y, _) -> Element.lt x y
      | _ -> assert false
    ;;
  end

  and PrimH : (HEAP with type Element.t = BootstrappedElem.t) = MakeH (BootstrappedElem)

  open BootstrappedElem

  type heap = BootstrappedElem.t

  let empty = E

  let is_empty = function
    | E -> true
    | _ -> false
  ;;

  let merge h1 h2 =
    match h1, h2 with
    | _, E -> h1
    | E, _ -> h2
    | H (x, p1), H (y, p2) ->
      if Element.leq x y then H (x, PrimH.insert h2 p1) else H (y, PrimH.insert h1 p2)
  ;;

  let insert x h = merge (H (x, PrimH.empty)) h

  let find_min = function
    | E -> raise (Failure "find_min: empty heap")
    | H (x, _) -> x
  ;;

  let delete_min = function
    | E -> raise (Failure "delete_min: empty heap")
    | H (_, p) ->
      if PrimH.is_empty p
      then E
      else (
        match PrimH.find_min p with
        | H (y, p1) -> H (y, PrimH.merge p1 (PrimH.delete_min p))
        | _ -> assert false)
  ;;
end

(* Figure 10.8 *)

module type HEAP_WITH_INFO = sig
  module Priority : ORDERED

  type 'a heap

  val empty : 'a heap
  val is_empty : 'a heap -> bool
  val insert : Priority.t -> 'a -> 'a heap -> 'a heap
  val merge : 'a heap -> 'a heap -> 'a heap
  val find_min : 'a heap -> Priority.t -> 'a
  val delete_min : 'a heap -> 'a heap
end
