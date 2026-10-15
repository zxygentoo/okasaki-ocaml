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

module BootstrapFigure
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

(* Exercise 10.7 Inlining the LazyBinomialHeap functor of Section 6.4.1 as described above
  yields the types

    datatype Tree = Node of int x Heap x Tree list
    datatype Heap = E | NE of Elem.T x Tree list susp

  Complete this implementation of bootstrapped heaps.
*)

module BootstrappedLazyBinomialHeapStub (E : ORDERED) = struct
  (* here is only the type, full exercise is omitted as f10.7 does compile in OCaml *)
  type heap =
    | E
    | NE of E.t * tree list lazy_t

  and tree = Node of int * heap * tree list
end

(* Exercise 10.8 Elements in a heap frequently contain other information besides the
  priority. For these kinds of elements, it is often more convenient to use heaps that
  separate the priority from the rest of the element. Figure 10.8 gives an alternate
  signature for this kind of heap.
*)

(* Figure 10.8 *)

module type HEAP_WITH_INFO = sig
  module Priority : ORDERED

  type 'a heap

  val empty : 'a heap
  val is_empty : 'a heap -> bool
  val insert : Priority.t -> 'a -> 'a heap -> 'a heap
  val merge : 'a heap -> 'a heap -> 'a heap
  val find_min : 'a heap -> Priority.t * 'a
  val delete_min : 'a heap -> 'a heap
end

(* (a) Adapt either LazyBinomialHeap or SkewBinomialHeap to this new signature. *)

module LazyBinomialHeapWithInfo (E : ORDERED) : HEAP_WITH_INFO with module Priority = E =
struct
  module Priority = E

  type 'a tree = Node of int * (Priority.t * 'a) * 'a tree list
  type 'a heap = 'a tree list lazy_t

  let empty = lazy []

  let is_empty = function
    | (lazy []) -> true
    | _ -> false
  ;;

  let rank (Node (r, _, _)) = r
  let priority (Node (_, (p, _), _)) = p
  let root (Node (_, x, _)) = x

  let link (Node (r, ((p1, _) as pv1), c1) as t1) (Node (_, ((p2, _) as pv2), c2) as t2) =
    if Priority.leq p1 p2 then Node (r + 1, pv1, t2 :: c1) else Node (r + 1, pv2, t1 :: c2)
  ;;

  let rec ins_tree t = function
    | [] -> [ t ]
    | t' :: ts' as ts -> if rank t < rank t' then t :: ts else ins_tree (link t t') ts'
  ;;

  let rec mrg h1 h2 =
    match h1, h2 with
    | _, [] -> h1
    | [], _ -> h2
    | t1 :: t1s, t2 :: t2s ->
      if rank t1 < rank t2
      then t1 :: mrg t1s h2
      else if rank t1 > rank t2
      then t2 :: mrg h1 t2s
      else ins_tree (link t1 t2) (mrg t1s t2s)
  ;;

  let insert p x h = lazy (ins_tree (Node (0, (p, x), [])) (Lazy.force h))
  let merge h1 h2 = lazy (mrg (Lazy.force h1) (Lazy.force h2))

  let rec remove_min_tree = function
    | [] -> raise (Failure "remove_min_tree: empty tree")
    | [ t ] -> t, []
    | t :: ts ->
      let t', ts' = remove_min_tree ts in
      if Priority.leq (priority t) (priority t') then t, ts else t', t :: ts'
  ;;

  let find_min h =
    let t, _ =
      try remove_min_tree (Lazy.force h) with
      | Failure _ -> raise (Failure "find_min: empty heap")
    in
    root t
  ;;

  let delete_min h =
    let Node (_, _, ts), h' =
      try remove_min_tree (Lazy.force h) with
      | Failure _ -> raise (Failure "delete_min: empty heap")
    in
    lazy (mrg (List.rev ts) h')
  ;;
end

(* (b) Rewrite the Bootstrap functor as 
    functor Bootstrap (PrimH : HEAPWITHINFO) : HEAPWITHINFO = ...
  You will need neither higher-order functors nor recursive structures.
*)

module Bootstrap (PrimH : HEAP_WITH_INFO) :
  HEAP_WITH_INFO with module Priority = PrimH.Priority = struct
  module Priority = PrimH.Priority

  type 'a heap =
    | E
    | H of (Priority.t * 'a) * 'a heap PrimH.heap

  let empty = E

  let is_empty = function
    | E -> true
    | _ -> false
  ;;

  let merge h1 h2 =
    match h1, h2 with
    | _, E -> h1
    | E, _ -> h2
    | H (((p1, _) as pv1), h1'), H (((p2, _) as pv2), h2') ->
      if Priority.leq p1 p2
      then H (pv1, PrimH.insert p2 h2 h1')
      else H (pv2, PrimH.insert p1 h1 h2')
  ;;

  let insert p x h = merge (H ((p, x), PrimH.empty)) h

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
        match snd (PrimH.find_min p) with
        | H (pv, p') -> H (pv, PrimH.merge p' (PrimH.delete_min p))
        | _ -> assert false)
  ;;
end

(* Figure 10.9 *)

module type FINITE_MAP = sig
  type key
  type 'a map

  val empty : 'a map
  val lookup : key -> 'a map -> 'a
  val bind : key -> 'a -> 'a map -> 'a map
end

(* Figure 10.10 *)

module TrieFigure (M : FINITE_MAP) : FINITE_MAP with type key = M.key list = struct
  type key = M.key list
  type 'a map = Trie of 'a option * 'a map M.map

  let empty = Trie (None, M.empty)

  let rec lookup k m =
    match k, m with
    | [], Trie (None, _) -> raise (Failure "lookup: not found")
    | [], Trie (Some x, _) -> x
    | k' :: ks, Trie (_, m') -> lookup ks (M.lookup k' m')
  ;;

  let rec bind k x m =
    match k, m with
    | [], Trie (_, m') -> Trie (Some x, m')
    | k' :: ks, Trie (v, m') ->
      let t =
        try M.lookup k' m' with
        | Failure _ -> empty
      in
      let t' = bind ks x t in
      Trie (v, M.bind k' t' m')
  ;;
end

(* Exercise 10.9 Very often, the set of keys to be stored in a trie has the property
  that no key is a proper prefix of another. For example, the keys might all be
  the same length, or the keys might all end in a unique character that occurs in
  no other position. Reimplement tries under this assumption, using the type

    datatype a Map = Entry of a | TRIE of a Map M.Map
*)

module EntryTrie (M : FINITE_MAP) : FINITE_MAP with type key = M.key list = struct
  type key = M.key list

  type 'a map =
    | Entry of 'a
    | Trie of 'a map M.map

  let empty = Trie M.empty

  let rec lookup k m =
    match k, m with
    | [], Entry v -> v
    | d :: ds, Trie m' -> lookup ds (M.lookup d m')
    | _ -> raise (Failure "lookup: not found")
  ;;

  let rec bind k x m =
    match k, m with
    | [], Entry _ -> Entry x
    | [], Trie _ -> Entry x
    | d :: ds, Trie m' ->
      let t =
        try M.lookup d m' with
        | Failure _ -> empty
      in
      let t' = bind ds x t in
      Trie (M.bind d t' m')
    | _ -> assert false
  ;;
end

module Int32KeyTrie (T : FINITE_MAP with type key = int list) :
  FINITE_MAP with type key = Int32.t = struct
  type key = Int32.t (* fixed length *)
  type 'a map = 'a T.map

  let chunk k n = Int32.(to_int (logand (shift_right_logical k (8 * n)) 0xFFl))
  let digits k = [ chunk k 3; chunk k 2; chunk k 1; chunk k 0 ]
  let empty = T.empty
  let lookup k m = T.lookup (digits k) m
  let bind k x m = T.bind (digits k) x m
end

(* Exercise 10.10 Tries frequently contain long paths of nodes that each have
  only a single child. A common optimization is to collapse such paths into a
  single node. We accomplish this by storing with every node a substring that
  is the longest common prefix of every key in that subtrie. The type of tries is
  then

    datatype a Map = TRIE of M.Key list x a option x a Map M.Map
  
  Reimplement tries using this type. You should maintain the invariant that no
  node is both invalid and an only child. You may assume that the structure M
  provides an isEmpty function.
*)

module type FINITE_MAP_WITH_EQ_AND_IS_EMPTY = sig
  include FINITE_MAP

  val key_eq : key -> key -> bool
  val is_empty : 'a map -> bool
end

module PathCompressionTrie (M : FINITE_MAP_WITH_EQ_AND_IS_EMPTY) :
  FINITE_MAP_WITH_EQ_AND_IS_EMPTY with type key = M.key list = struct
  type key = M.key list
  type 'a map = Trie of M.key list * 'a option * 'a map M.map

  let empty = Trie ([], None, M.empty)
  let is_empty (Trie (_, v, m')) = Option.is_none v && M.is_empty m'

  let rec key_eq k1 k2 =
    match k1, k2 with
    | [], [] -> true
    | x :: xs, y :: ys when M.key_eq x y -> key_eq xs ys
    | _ -> false
  ;;

  let rec lookup_compare_keys k lcp =
    match k, lcp with
    | _, [] -> k
    | x :: xs, y :: ys when M.key_eq x y -> lookup_compare_keys xs ys
    | _ -> raise (Failure "lookup: not found")
  ;;

  let rec lookup xs (Trie (ys, v, m')) =
    match lookup_compare_keys xs ys with
    | [] ->
      (match v with
       | None -> raise (Failure "lookup: not found")
       | Some v' -> v')
    | z :: zs -> lookup zs (M.lookup z m')
  ;;

  let rec bind_compare_keys n k lcp =
    match k, lcp with
    | _, [] -> `Bind k
    | [], p :: ps -> `Split (n, (p, ps))
    | x :: xs, y :: ys when M.key_eq x y -> bind_compare_keys (n + 1) xs ys
    | x :: xs, y :: ys -> `Branch (n, (x, xs), (y, ys))
  ;;

  let rec bind xs x (Trie (ys, v, m') as m) =
    if is_empty m
    then Trie (xs, Some x, M.empty)
    else (
      match bind_compare_keys 0 xs ys with
      | `Bind [] -> Trie (ys, Some x, m')
      | `Bind (k :: ks) ->
        let t =
          try M.lookup k m' with
          | Failure _ -> empty
        in
        let t' = bind ks x t in
        Trie (ys, v, M.bind k t' m')
      | `Split (n, (p, ps)) ->
        let t = Trie (ps, v, m') in
        Trie (List.take n ys, Some x, M.bind p t M.empty)
      | `Branch (n, (k, ks), (p, ps)) ->
        let t1 = Trie (ps, v, m') in
        let t2 = Trie (ks, Some x, M.empty) in
        Trie (List.take n ys, None, M.bind k t2 (M.bind p t1 M.empty)))
  ;;
end

(* Exercise 10.11 (Schwenke [Sch97]) Another common data structure that involves
  multiple layers of finite maps is the hash table. Complete the following
  implementation of abstract hash tables.

    functor HashTable (structure Approx : FINITEMAP
                      structure Exact : FINITEMAP
                      val hash : Exact.Key ->• Approx.Key): FINITEMAP =
    struct
      type Key = Exact.Key
      type a Map = a Exact.Map Approx.Map
      ...
      fun lookup (k, m) = Exact.lookup (k, Approx.lookup (hash k, m))
      ...
    end

  The advantage of this representation is that Approx can use an efficient key
  type (such as integers) and Exact can use a trivial implementation (such as
  association lists).
*)

module HashTable
    (Approx : FINITE_MAP)
    (Exact : FINITE_MAP)
    (H : sig
       val hash : Exact.key -> Approx.key
     end) : FINITE_MAP with type key = Exact.key = struct
  type key = Exact.key
  type 'a map = 'a Exact.map Approx.map

  let empty = Approx.empty
  let lookup k m = Exact.lookup k (Approx.lookup (H.hash k) m)

  let bind k x m =
    let h = H.hash k in
    let t =
      try Approx.lookup h m with
      | Failure _ -> Exact.empty
    in
    Approx.bind h (Exact.bind k x t) m
  ;;
end

(* Figure 10.11 *)

type 'a tree =
  | E
  | T of 'a * 'a tree * 'a tree

module TrieOfTrees (M : FINITE_MAP) : FINITE_MAP with type key = M.key tree = struct
  type key = M.key tree
  type 'a map = Trie of 'a option * 'a map map M.map

  let empty = Trie (None, M.empty)

  let rec lookup : 'a. key -> 'a map -> 'a =
    fun k m ->
    match k, m with
    | E, Trie (None, _) -> raise (Failure "lookup: not found")
    | E, Trie (Some x, _) -> x
    | T (k, a, b), Trie (_, m) -> lookup b (lookup a (M.lookup k m))
  ;;

  let rec bind : 'a. key -> 'a -> 'a map -> 'a map =
    fun k x m ->
    match k, m with
    | E, Trie (_, m) -> Trie (Some x, m)
    | T (k, a, b), Trie (v, m) ->
      let tt =
        try M.lookup k m with
        | Failure _ -> empty
      in
      let t =
        try lookup a tt with
        | Failure _ -> empty
      in
      let t' = bind b x t in
      let tt' = bind a t' tt in
      Trie (v, M.bind k tt' m)
  ;;
end

(* Exercise 10.12 Reimplement the TrieOfTrees functor without polymorphic recursion
  using the types
    datatype a Map = TRIE of a EM option x a Map M.Map
    and a EM = ELEM of a | MAP of a Map
*)

module TrieOfTreesWithoutPolymorphicRecursion (M : FINITE_MAP) :
  FINITE_MAP with type key = M.key tree = struct
  type key = M.key tree

  type 'a map = Trie of 'a em option * 'a map M.map

  and 'a em =
    | Elem of 'a
    | Map of 'a map

  let empty = Trie (None, M.empty)
  let lookup_err () = raise (Failure "lookup: not found")

  let rec find : key -> 'a map -> 'a em =
    fun k m ->
    match k, m with
    | E, Trie (None, _) -> lookup_err ()
    | E, Trie (Some em, _) -> em
    | T (k, a, b), Trie (_, m') ->
      (match find a (M.lookup k m') with
       | Elem _ -> lookup_err ()
       | Map t -> find b t)
  ;;

  let lookup k m =
    match find k m with
    | Elem x -> x
    | Map _ -> lookup_err ()
  ;;

  let rec update : key -> 'a em -> 'a map -> 'a map =
    fun k em m ->
    match k, m with
    | E, Trie (_, m) -> Trie (Some em, m)
    | T (k, a, b), Trie (v, m') ->
      let tt =
        try M.lookup k m' with
        | Failure _ -> empty
      in
      let t =
        match find a tt with
        | Elem _ -> empty
        | Map t -> t
        | exception Failure _ -> empty
      in
      let t' = update b em t in
      let tt' = update a (Map t') tt in
      Trie (v, M.bind k tt' m')
  ;;

  let bind k x m = update k (Elem x) m
end

(* Exercise 10.13 Implement tries whose keys are multiway trees of type
    datatype a Tree = T of a x a Tree list
*)

type 'a mtree = MT of 'a * 'a mtree list

module MultiwayTreesKeyTrie (M : FINITE_MAP) : FINITE_MAP with type key = M.key mtree =
struct
  type key = M.key mtree

  type 'a map = Trie of 'a forest M.map
  and 'a forest = Forest of 'a option * 'a forest map

  let empty = Trie M.empty
  let empty_forest = Forest (None, empty)

  let rec lookup : 'a. key -> 'a map -> 'a =
    fun k m ->
    match k, m with
    | MT (t, ts), Trie m -> find ts (M.lookup t m)

  and find : 'a. key list -> 'a forest -> 'a =
    fun ks f ->
    match ks, f with
    | [], Forest (None, _) -> raise (Failure "lookup: not found")
    | [], Forest (Some x, _) -> x
    | k :: ks, Forest (_, m) -> find ks (lookup k m)
  ;;

  let rec bind : 'a. key -> 'a -> 'a map -> 'a map =
    fun k x m ->
    match k, m with
    | MT (t, ts), Trie m' ->
      let tt =
        try M.lookup t m' with
        | Failure _ -> empty_forest
      in
      Trie (M.bind t (update ts x tt) m')

  and update : 'a. key list -> 'a -> 'a forest -> 'a forest =
    fun ks x f ->
    match ks, f with
    | [], Forest (_, m) -> Forest (Some x, m)
    | k :: ks, Forest (v, m) ->
      let tt =
        try lookup k m with
        | Failure _ -> empty_forest
      in
      let t = update ks x tt in
      Forest (v, bind k t m)
  ;;
end

(* Exercise 10.14 Complete the following functors that implement the above
  rules for products and sums.

    functor ProductMap (M1 : FINITEMAP) (M2 : FINITEMAP): FINITEMAP =
    struct
      type Key = M1.Key x M2.Key
      ...
    end
    datatype (a, b) Sum = LEFT of a | RIGHT of b
    functor SumMap (M1 : FINITEMAP) (M2 : FINITEMAP) : FINITEMAP =
    struct
      type Key = (M1.Key, M2.Key) Sum
      ...
    end
*)

module ProductMap (M1 : FINITE_MAP) (M2 : FINITE_MAP) :
  FINITE_MAP with type key = M1.key * M2.key = struct
  type key = M1.key * M2.key
  type 'a map = 'a M2.map M1.map

  let empty = M1.empty
  let lookup (k1, k2) m = M2.lookup k2 (M1.lookup k1 m)

  let bind (k1, k2) x m =
    let t =
      try M1.lookup k1 m with
      | Failure _ -> M2.empty
    in
    let tt = M2.bind k2 x t in
    M1.bind k1 tt m
  ;;
end

type ('a, 'b) sum =
  | Left of 'a
  | Right of 'b

module SumMap (M1 : FINITE_MAP) (M2 : FINITE_MAP) :
  FINITE_MAP with type key = (M1.key, M2.key) sum = struct
  type key = (M1.key, M2.key) sum
  type 'a map = 'a M1.map * 'a M2.map

  let empty = M1.empty, M2.empty

  let lookup k (m1, m2) =
    match k with
    | Left a -> M1.lookup a m1
    | Right b -> M2.lookup b m2
  ;;

  let bind k x (m1, m2) =
    match k with
    | Left a -> M1.bind a x m1, m2
    | Right b -> m1, M2.bind b x m2
  ;;
end

(* Exercise 10.15 Given a structure M that implements finite maps over the type
  Id of identifiers, implement tries over the type Exp of lambda expressions,
  where
    datatype Exp = VAR of Id | LAM of Id x Exp | APP of Exp x Exp
  You may find it helpful to extend the type of tries with a separate constructor
  for the empty map.
*)

type 'id exp =
  | Var of 'id
  | Lam of 'id * 'id exp
  | App of 'id exp * 'id exp

module ExpTrie (M : FINITE_MAP) : FINITE_MAP with type key = M.key exp = struct
  type key = M.key exp

  type 'a map =
    | Empty
    | Trie of 'a M.map * 'a map M.map * 'a map map

  let empty = Empty
  let empty_trie = Trie (M.empty, M.empty, empty)

  let rec lookup : 'a. key -> 'a map -> 'a =
    fun k m ->
    match k, m with
    | _, Empty -> raise (Failure "lookup: not found")
    | Var id, Trie (m1, _, _) -> M.lookup id m1
    | Lam (id, e), Trie (_, m2, _) -> lookup e (M.lookup id m2)
    | App (e1, e2), Trie (_, _, m3) -> lookup e2 (lookup e1 m3)
  ;;

  let rec bind : 'a. key -> 'a -> 'a map -> 'a map =
    fun k x m ->
    match k, m with
    | _, Empty -> bind k x empty_trie
    | Var id, Trie (m1, m2, m3) -> Trie (M.bind id x m1, m2, m3)
    | Lam (id, e), Trie (m1, m2, m3) ->
      let t =
        try M.lookup id m2 with
        | Failure _ -> empty
      in
      let tt = bind e x t in
      Trie (m1, M.bind id tt m2, m3)
    | App (e1, e2), Trie (m1, m2, m3) ->
      let t =
        try lookup e1 m3 with
        | Failure _ -> empty
      in
      let tt = bind e2 x t in
      Trie (m1, m2, bind e1 tt m3)
  ;;
end
