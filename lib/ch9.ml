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

module type RANDOM_ACCESS_LIST_LITE = sig
  type 'a rlist

  val empty : 'a rlist
  val is_empty : 'a rlist -> bool
  val cons : 'a -> 'a rlist -> 'a rlist
  val head : 'a rlist -> 'a
  val tail : 'a rlist -> 'a rlist
end

(* Figure 9.4 *)

module type RANDOM_ACCESS_LIST = sig
  include RANDOM_ACCESS_LIST_LITE

  val lookup : int -> 'a rlist -> 'a
  val update : int -> 'a -> 'a rlist -> 'a rlist
end

module type RANDOM_ACCESS_LIST_WITH_DROP_AND_CREATE = sig
  include RANDOM_ACCESS_LIST

  val drop : int -> 'a rlist -> 'a rlist
  val create : int -> 'a -> 'a rlist
end

(* Figure 9.6 *)

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

  let _create_top_down n e =
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

(* Exercise 9.5 Implement the remaining functions for this type. *)

module ZerolessBinaryRandomAccessList : RANDOM_ACCESS_LIST = struct
  type 'a tree =
    | Leaf of 'a
    | Node of int * 'a tree * 'a tree

  type 'a digit =
    | One of 'a tree
    | Two of 'a tree * 'a tree

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

  let rec carry = function
    | One a :: One b :: xs -> Two (a, b) :: xs
    | (One _ as x) :: Two (a, b) :: xs -> x :: carry (One (link a b) :: xs)
    | xs -> xs
  ;;

  let rec borrow = function
    | Two (Node (_, a, b), (Node _ as c)) :: xs -> Two (a, b) :: One c :: xs
    | One (Node (_, a, b)) :: xs -> Two (a, b) :: borrow xs
    | xs -> xs
  ;;

  let cons e xs = carry (One (Leaf e) :: xs)

  let head = function
    | [] -> raise (Failure "head: empty list")
    | One (Leaf e) :: _ -> e
    | Two (Leaf e, _) :: _ -> e
    | _ -> assert false
  ;;

  let rec tail = function
    | [] -> raise (Failure "tail: empty list")
    | One (Leaf _) :: xs -> borrow xs
    | Two (a, b) :: xs -> tail (One a :: One b :: xs)
    | _ -> assert false
  ;;

  let rec lookup_tree i = function
    | Leaf e when i = 0 -> e
    | Node (w, a, b) -> if i < w / 2 then lookup_tree i a else lookup_tree (i - (w / 2)) b
    | _ -> raise (Failure "lookup: not found")
  ;;

  let rec lookup i = function
    | [] -> raise (Failure "lookup: not found")
    | One x :: xs -> if i < size x then lookup_tree i x else lookup (i - size x) xs
    | Two (a, b) :: xs ->
      let sa = size a
      and sb = size b in
      if i < sa
      then lookup_tree i a
      else if i < sa + sb
      then lookup_tree (i - sa) b
      else lookup (i - sa - sb) xs
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
    | One x :: xs ->
      if i < size x
      then One (update_tree i e x) :: xs
      else One x :: update (i - size x) e xs
    | (Two (a, b) as x) :: xs ->
      let sa = size a
      and sb = size b in
      if i < sa
      then Two (update_tree i e a, b) :: xs
      else if i < sa + sb
      then Two (a, update_tree (i - sa) e b) :: xs
      else x :: update (i - sa - sb) e xs
  ;;
end

module type STREAM = sig
  type 'a stream_cell =
    | Nil
    | Cons of 'a * 'a stream

  and 'a stream = 'a stream_cell lazy_t

  val ( ++ ) : 'a stream -> 'a stream -> 'a stream
  val take : int -> 'a stream -> 'a stream
  val drop : int -> 'a stream -> 'a stream
  val reverse : 'a stream -> 'a stream
end

module LazyRepresentation (S : STREAM) = struct
  open S

  type digit =
    | Zero
    | One
    | Two

  type nat = digit stream

  let rec inc = function
    | (lazy Nil) -> Lazy.from_val (Cons (One, lazy Nil))
    | (lazy (Cons (Zero, ds))) -> Lazy.from_val (Cons (One, ds))
    | (lazy (Cons (One, ds))) -> Lazy.from_val (Cons (Two, ds))
    | (lazy (Cons (Two, ds))) -> lazy (Cons (One, inc ds))
  ;;

  let rec dec = function
    | (lazy (Cons (One, (lazy Nil)))) -> lazy Nil
    | (lazy (Cons (One, ds))) -> Lazy.from_val (Cons (Zero, ds))
    | (lazy (Cons (Two, ds))) -> Lazy.from_val (Cons (One, ds))
    | (lazy (Cons (Zero, ds))) -> lazy (Cons (One, dec ds))
    | _ -> assert false
  ;;
end

(* Exercise 9.9 Implement cons, head, and tail for random-access lists based on zeroless
   redundant binary numbers, using the type

   datatype a Digit = ONE of a Tree | Two of a Tree x a Tree | THREE of a Tree x a Tree x
   a Tree

   type a RList = Digit Stream

   Show that all three functions run in 0(1) amortized time.
*)

module ZerolessRedundantBinaryRandomAccessList (S : STREAM) : RANDOM_ACCESS_LIST_LITE =
struct
  open S

  let ( ^:: ) a b = Cons (a, b)

  type 'a tree =
    | Leaf of 'a
    | Node of int * 'a tree * 'a tree

  type 'a digit =
    | One of 'a tree
    | Two of 'a tree * 'a tree
    | Three of 'a tree * 'a tree * 'a tree

  type 'a rlist = 'a digit stream

  let empty = lazy Nil

  let is_empty = function
    | (lazy Nil) -> true
    | _ -> false
  ;;

  let size = function
    | Leaf _ -> 1
    | Node (w, _, _) -> w
  ;;

  let link t1 t2 = Node (size t1 + size t2, t1, t2)

  let rec carry x s =
    lazy
      (match s with
       | (lazy Nil) -> One x ^:: empty
       | (lazy (Cons (One a, rest))) -> Two (x, a) ^:: rest
       | (lazy (Cons (Two (a, b), rest))) -> Three (x, a, b) ^:: rest
       | (lazy (Cons (Three (a, b, c), rest))) -> Two (x, a) ^:: carry (link b c) rest)
  ;;

  let rec borrow s =
    lazy
      (match s with
       | (lazy (Cons (Three (Node (_, a, b), c, d), rest))) ->
         Two (a, b) ^:: Lazy.from_val (Two (c, d) ^:: rest)
       | (lazy (Cons (Two (Node (_, a, b), c), rest))) ->
         Two (a, b) ^:: Lazy.from_val (One c ^:: rest)
       | (lazy (Cons (One (Node (_, a, b)), rest))) -> Two (a, b) ^:: borrow rest
       | (lazy Nil) -> Nil
       | _ -> assert false)
  ;;

  let cons e s = carry (Leaf e) s

  let head = function
    | (lazy Nil) -> raise (Failure "head: empty list")
    | (lazy (Cons (One (Leaf e), _))) -> e
    | (lazy (Cons (Two (Leaf e, _), _))) -> e
    | (lazy (Cons (Three (Leaf e, _, _), _))) -> e
    | _ -> assert false
  ;;

  let tail = function
    | (lazy Nil) -> raise (Failure "tail: empty list")
    | (lazy (Cons (One _, rest))) -> borrow rest
    | (lazy (Cons (Two (_, b), rest))) -> Lazy.from_val (One b ^:: rest)
    | (lazy (Cons (Three (_, b, c), rest))) -> Lazy.from_val (Two (b, c) ^:: rest)
  ;;
end

(* Exercise 9.10 As demonstrated by scheduled binomial heaps in Section 7.3, we can apply
   scheduling to lazy binary numbers to achieve O(l) worst-case bounds. Re-implement cons,
   head, and tail from the preceding exercise so that each runs in 0(1) worst-case time.
   You may find it helpful to have two distinct Two constructors (say, Two and Two' ) so
   that you can distinguish between recursive and non-recursive cases of cons and tail. *)

module ScheduledZerolessRedundantBinaryRandomAccessList (S : STREAM) :
  RANDOM_ACCESS_LIST_LITE = struct
  open S

  let ( ^:: ) a b = Cons (a, b)

  type 'a tree =
    | Leaf of 'a
    | Node of int * 'a tree * 'a tree

  type 'a digit =
    | One of 'a tree
    | Two of 'a tree * 'a tree (* non-recursive case *)
    | TwoR of 'a tree * 'a tree (* recursive case *)
    | Three of 'a tree * 'a tree * 'a tree

  type 'a schedule = 'a digit stream list
  type 'a rlist = 'a digit stream * 'a schedule

  let empty = lazy Nil, []

  let is_empty = function
    | (lazy Nil), _ -> true
    | _ -> false
  ;;

  let size = function
    | Leaf _ -> 1
    | Node (w, _, _) -> w
  ;;

  let link t1 t2 = Node (size t1 + size t2, t1, t2)

  let exec = function
    | [] -> []
    | (lazy (Cons (TwoR _, job))) :: sched -> job :: sched
    | _ :: sched -> sched
  ;;

  let scheduled s sched = s, exec (exec (s :: sched))

  let rec carry x s =
    lazy
      (match s with
       | (lazy Nil) -> One x ^:: lazy Nil
       | (lazy (Cons (One a, rest))) -> Two (x, a) ^:: rest
       | (lazy (Cons ((Two (a, b) | TwoR (a, b)), rest))) -> Three (x, a, b) ^:: rest
       | (lazy (Cons (Three (a, b, c), rest))) -> TwoR (x, a) ^:: carry (link b c) rest)
  ;;

  let rec borrow s =
    lazy
      (match s with
       | (lazy (Cons (Three (Node (_, a, b), c, d), rest))) ->
         Two (a, b) ^:: Lazy.from_val (Two (c, d) ^:: rest)
       | (lazy (Cons ((Two (Node (_, a, b), c) | TwoR (Node (_, a, b), c)), rest))) ->
         Two (a, b) ^:: Lazy.from_val (One c ^:: rest)
       | (lazy (Cons (One (Node (_, a, b)), rest))) -> TwoR (a, b) ^:: borrow rest
       | (lazy Nil) -> Nil
       | _ -> assert false)
  ;;

  let cons e (s, sched) = scheduled (carry (Leaf e) s) sched

  let head (s, _) =
    match s with
    | (lazy Nil) -> raise (Failure "head: empty list")
    | (lazy (Cons (One (Leaf e), _))) -> e
    | (lazy (Cons ((Two (Leaf e, _) | TwoR (Leaf e, _)), _))) -> e
    | (lazy (Cons (Three (Leaf e, _, _), _))) -> e
    | _ -> assert false
  ;;

  let tail_tree = function
    | (lazy Nil) -> raise (Failure "tail: empty list")
    | (lazy (Cons (One _, rest))) -> borrow rest
    | (lazy (Cons ((Two (_, b) | TwoR (_, b)), rest))) -> Lazy.from_val (One b ^:: rest)
    | (lazy (Cons (Three (_, b, c), rest))) -> Lazy.from_val (Two (b, c) ^:: rest)
  ;;

  let tail (s, sched) = scheduled (tail_tree s) sched
end

module SegmentedRepresentationOne = struct
  type digit_block =
    | Zeros of int
    | Ones of int

  type nat = digit_block list

  let zeros i bks =
    if i = 0
    then bks
    else (
      match bks with
      | [] -> []
      | Zeros j :: bks -> Zeros (i + j) :: bks
      | _ -> Zeros i :: bks)
  ;;

  let ones i bks =
    if i = 0
    then bks
    else (
      match bks with
      | Ones j :: bks -> Ones (i + j) :: bks
      | bks -> Ones i :: bks)
  ;;

  let rec inc = function
    | [] -> [ Ones 1 ]
    | Zeros i :: bks -> ones 1 (zeros (i - 1) bks)
    | Ones i :: bks -> Zeros i :: inc bks
  ;;

  let rec dec = function
    | [] -> raise (Failure "dec: zero")
    | Ones i :: bks -> zeros 1 (ones (i - 1) bks)
    | Zeros i :: bks -> Ones i :: dec bks
  ;;
end

module SegmentedRepresentationTwo = struct
  type digits =
    | Zero
    | Ones of int
    | Two

  type nat = digits list

  let ones i ds =
    if i = 0
    then ds
    else (
      match ds with
      | Ones j :: ds' -> Ones (i + j) :: ds'
      | _ -> Ones i :: ds)
  ;;

  let simple_inc = function
    | [] -> [ Ones 1 ]
    | Zero :: ds -> ones 1 ds
    | Ones i :: ds' -> Two :: ones (i - 1) ds'
    | _ -> assert false
  ;;

  let fixup = function
    | Two :: ds -> Zero :: simple_inc ds
    | Ones i :: Two :: ds -> Ones i :: Zero :: simple_inc ds
    | ds -> ds
  ;;

  let inc ds = fixup (simple_inc ds)
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
  val find_min : heap -> Element.t
  val delete_min : heap -> heap
end

(* Exercise 9.11 Extend binomial heaps with segmentation so that insert runs in 0(1)
   worst-case time. Use the type

   datatype Tree = NODE of Elem.T x Tree list

   datatype Digit = ZERO | ONES of Tree list | Two of Tree x Tree

   type Heap = Digit list

   Restore the invariant after a merge by eliminating all Twos.
*)

module SegmentedBinomialHeap (E : ORDERED) : HEAP with module Element = E = struct
  module Element = E

  type tree = Node of E.t * tree list

  type digit =
    | Zero
    | Ones of tree list
    | Two of tree * tree

  type heap = digit list

  (* empty and is_empty *)

  let empty = []

  let is_empty = function
    | [] -> true
    | _ -> false
  ;;

  (* helpers *)

  let smaller a b = if Element.leq a b then a else b

  let smaller_opt a b =
    match a, b with
    | _, None -> a
    | None, _ -> b
    | Some x, Some y -> Some (smaller x y)
  ;;

  (* tree stuff *)

  let root (Node (e, _)) = e
  let children (Node (_, xs)) = xs

  let link (Node (e1, ts1) as t1) (Node (e2, ts2) as t2) =
    if Element.leq e1 e2 then Node (e1, t2 :: ts1) else Node (e2, t1 :: ts2)
  ;;

  (* tree <-> digit stuff *)

  let add_zero = function
    | [] -> []
    | ds -> Zero :: ds
  ;;

  let add_ones ts ds =
    match ts, ds with
    | [], _ -> ds
    | _, Ones os :: ds' -> Ones (ts @ os) :: ds'
    | _, _ -> Ones ts :: ds
  ;;

  let cons_step ts ds =
    match ts with
    | [] -> add_zero ds
    | [ _ ] -> add_ones ts ds
    | [ a; b ] -> Two (a, b) :: ds
    | _ -> assert false
  ;;

  let uncons_step = function
    | Zero :: ts -> [], ts
    | Ones [ o ] :: ts -> [ o ], ts
    | Ones (o :: os) :: ts -> [ o ], Ones os :: ts
    | Two (a, b) :: ts -> [ a; b ], ts
    | _ -> assert false
  ;;

  let uncons_step_or_empty h = if is_empty h then [], [] else uncons_step h

  let remove_root e = function
    | [ x ] when Element.eq (root x) e -> Some (children x, [])
    | [ a; b ] when Element.eq (root a) e -> Some (children a, [ b ])
    | [ a; b ] when Element.eq (root b) e -> Some (children b, [ a ])
    | _ -> None
  ;;

  (* insert *)

  let insert_tree t = function
    | [] -> [ Ones [ t ] ]
    | Zero :: Ones os :: ds -> Ones (t :: os) :: ds
    | Zero :: ds -> Ones [ t ] :: ds
    | Ones [ x ] :: ds -> Two (t, x) :: ds
    | Ones (o :: os) :: ds -> Two (t, o) :: Ones os :: ds
    | _ -> assert false
  ;;

  let fixup = function
    | Two (x, y) :: ds -> Zero :: insert_tree (link x y) ds
    | (Ones _ as d) :: Two (x, y) :: ds -> d :: Zero :: insert_tree (link x y) ds
    | ds -> ds
  ;;

  let insert e ds = fixup (insert_tree (Node (e, [])) ds)

  (* merge *)

  let merge_step x y carry =
    match x @ y @ carry with
    | [] -> [], []
    | [ _ ] as t -> t, []
    | [ a; b ] -> [], [ link a b ]
    | [ a; b; c ] -> [ a ], [ link b c ]
    | [ a; b; c; d ] -> [], [ link a b; link c d ]
    | [ a; b; c; d; e ] -> [ a ], [ link b c; link d e ]
    | _ -> assert false (* the invariant keeps the pool length <= 5 *)
  ;;

  let rec merge_steps ha hb carry =
    match ha, hb, carry with
    | [], [], [] -> []
    | _ ->
      let a, ha' = uncons_step_or_empty ha in
      let b, hb' = uncons_step_or_empty hb in
      let r, carry' = merge_step a b carry in
      cons_step r (merge_steps ha' hb' carry')
  ;;

  let merge h1 h2 =
    if is_empty h1 then h2 else if is_empty h2 then h1 else merge_steps h1 h2 []
  ;;

  (* find_min *)

  (* O(log n), spelled out with option type yet less allocation *)

  let find_digit_min = function
    | Zero -> None
    | Ones os -> List.fold_left (fun acc x -> smaller_opt acc (Some (root x))) None os
    | Two (a, b) -> Some (smaller (root a) (root b))
  ;;

  let _find_min_opt ds =
    match List.fold_left (fun e' d -> smaller_opt e' (find_digit_min d)) None ds with
    | Some e -> e
    | None -> raise (Failure "find_min: empty heap")
  ;;

  (* O(log n), shorter, reads nicer, but does around twice allocations *)

  let decode = function
    | Zero -> []
    | Ones ts -> ts
    | Two (a, b) -> [ a; b ]
  ;;

  let flatten = List.concat_map decode

  let find_min_flatten h =
    match List.map root (flatten h) with
    | [] -> raise (Failure "find_min: empty heap")
    | r :: rs -> List.fold_left smaller r rs
  ;;

  let find_min = find_min_flatten

  (* delete_min *)

  let rec remove_min_tree e h =
    if is_empty h
    then assert false
    else (
      let s, rest = uncons_step_or_empty h in
      match remove_root e s with
      | Some (children, left) -> children, cons_step left rest
      | None ->
        let children, rest' = remove_min_tree e rest in
        children, cons_step s rest')
  ;;

  let delete_min h =
    if is_empty h
    then raise (Failure "delete_min: empty heap")
    else (
      let e = find_min h in
      let children, rest = remove_min_tree e h in
      merge (add_ones (List.rev children) []) rest)
  ;;
end

(* Exercise 9.12 The example implementation of binary numbers based on recursive slowdown
   supports inc in O(1) worst-case time, but might require up to O(log n) for dec.
   Reimplement segmented, redundant binary numbers to support both inc and dec in O(1)
   worst-case time by allowing each digit to be 0, 1, 2, 3, or 4, where 0 and 4 are red, 1
   and 3 are yellow, and 2 is green. *)

(* O(log n) dense representation version *)

module DenseRepresentation = struct
  type digits =
    | Zero
    | One
    | Two
    | Three
    | Four

  type nat = digits list

  let simple_inc = function
    | [] -> [ One ]
    | Zero :: s -> One :: s
    | One :: s -> Two :: s
    | Two :: s -> Three :: s
    | Three :: s -> Four :: s
    | _ -> assert false
  ;;

  let simple_dec = function
    | [] -> raise (Failure "dec: zero")
    | [ One ] -> []
    | One :: s -> Zero :: s
    | Two :: s -> One :: s
    | Three :: s -> Two :: s
    | Four :: s -> Three :: s
    | _ -> assert false
  ;;

  let rec fixup = function
    | Zero :: ds -> Two :: simple_dec ds
    | Four :: ds -> Two :: simple_inc ds
    | ((One | Three) as d) :: ds -> d :: fixup ds
    | ds -> ds
  ;;

  let inc ds = fixup (simple_inc ds)
  let dec ds = fixup (simple_dec ds)
end

(* O(1) segmented representation version *)

module SegmentedRepresentation = struct
  type yellow =
    | One
    | Three

  type digits =
    | Zero
    | Yellows of yellow list
    | Two
    | Four

  type nat = digits list

  let zero = function
    | [] -> []
    | ds -> Zero :: ds
  ;;

  let yellow y = function
    | Yellows ys :: ds -> Yellows (y :: ys) :: ds
    | ds -> Yellows [ y ] :: ds
  ;;

  let block ys ds =
    match ys with
    | [] -> ds
    | _ -> Yellows ys :: ds
  ;;

  let simple_inc = function
    | [] -> [ Yellows [ One ] ]
    | Zero :: ds -> yellow One ds
    | Two :: ds -> yellow Three ds
    | Yellows (Three :: ys) :: ds -> Four :: block ys ds
    | Yellows (One :: ys) :: ds -> Two :: block ys ds
    | _ -> assert false
  ;;

  let simple_dec = function
    | [] -> raise (Failure "dec: zero")
    | Two :: ds -> yellow One ds
    | Yellows (Three :: ys) :: ds -> Two :: block ys ds
    | Yellows (One :: ys) :: ds -> zero (block ys ds)
    | Four :: ds -> yellow Three ds
    | _ -> assert false
  ;;

  let rec fixup = function
    | Zero :: ds -> Two :: simple_dec ds
    | Four :: ds -> Two :: simple_inc ds
    | (Yellows _ as d1) :: ((Zero | Four) as d2) :: ds -> d1 :: fixup (d2 :: ds)
    | ds -> ds
  ;;

  let inc ds = fixup (simple_inc ds)
  let dec ds = fixup (simple_dec ds)
end

(* Exercise 9.13 Implement cons, head, tail, and lookup for a numerical representation of
   random-access lists based on the number system of the previous exercise. Your
   implementation should support cons, head, and tail in O(1) worst-case time, and lookup
   in O(log i) worst-case time. *)

module type RANDOM_ACCESS_LIST_LITE_WITH_LOOKUP = sig
  include RANDOM_ACCESS_LIST_LITE

  val lookup : int -> 'a rlist -> 'a
end

module SegmentedRandomAccessList : RANDOM_ACCESS_LIST_LITE_WITH_LOOKUP = struct
  type 'a tree =
    | Leaf of 'a
    | Node of int * 'a tree * 'a tree

  type 'a yellow =
    | One of 'a tree
    | Three of 'a tree * 'a tree * 'a tree

  type 'a digit =
    | Zero
    | Yellows of 'a yellow list
    | Two of 'a tree * 'a tree
    | Four of 'a tree * 'a tree * 'a tree * 'a tree

  type 'a rlist = 'a digit list

  (* tree helpers *)

  let size = function
    | Leaf _ -> 1
    | Node (w, _, _) -> w
  ;;

  let link a b = Node (size a + size b, a, b)

  let split = function
    | Node (_, a, b) -> a, b
    | Leaf _ -> assert false
  ;;

  (* digit helpers *)

  let zero = function
    | [] -> []
    | ds -> Zero :: ds
  ;;

  let yellow y = function
    | Yellows ys :: ds -> Yellows (y :: ys) :: ds
    | ds -> Yellows [ y ] :: ds
  ;;

  let block ys ds =
    match ys with
    | [] -> ds
    | _ -> Yellows ys :: ds
  ;;

  (* rlist helpers *)

  let push t = function
    | [] -> [ Yellows [ One t ] ]
    | Zero :: ds -> yellow (One t) ds
    | Two (a, b) :: ds -> yellow (Three (t, a, b)) ds
    | Yellows (Three (a, b, c) :: ys) :: ds -> Four (t, a, b, c) :: block ys ds
    | Yellows (One a :: ys) :: ds -> Two (t, a) :: block ys ds
    | _ -> assert false
  ;;

  let pop = function
    | Two (a, b) :: ds -> a, yellow (One b) ds
    | Yellows (Three (a, b, c) :: ys) :: ds -> a, Two (b, c) :: block ys ds
    | Yellows (One a :: ys) :: ds -> a, zero (block ys ds)
    | Four (a, b, c, d) :: ds -> a, yellow (Three (b, c, d)) ds
    | _ -> assert false
  ;;

  let rec fixup = function
    | Zero :: ds ->
      let hd, rest = pop ds in
      let a, b = split hd in
      Two (a, b) :: rest
    | Four (a, b, c, d) :: ds -> Two (a, b) :: push (link c d) ds
    | (Yellows _ as d1) :: ((Zero | Four _) as d2) :: ds -> d1 :: fixup (d2 :: ds)
    | ds -> ds
  ;;

  (* interface *)

  let empty = []

  let is_empty = function
    | [] -> true
    | _ -> false
  ;;

  let cons e ds = fixup (push (Leaf e) ds)

  let head = function
    | [] -> raise (Failure "head: empty list")
    | Yellows (One (Leaf e) :: _) :: _ -> e
    | Two (Leaf e, _) :: _ -> e
    | Yellows (Three (Leaf e, _, _) :: _) :: _ -> e
    | _ -> assert false
  ;;

  let tail = function
    | [] -> raise (Failure "tail: empty list")
    | ds -> fixup (snd (pop ds))
  ;;

  let uncons_step = function
    | Zero :: ds -> [], ds
    | Yellows (One a :: ys) :: ds -> [ a ], block ys ds
    | Two (a, b) :: ds -> [ a; b ], ds
    | Yellows (Three (a, b, c) :: ys) :: ds -> [ a; b; c ], block ys ds
    | Four (a, b, c, d) :: ds -> [ a; b; c; d ], ds
    | _ -> assert false
  ;;

  let rec lookup_tree i = function
    | Leaf x when i = 0 -> Some x
    | Node (w, t1, t2) ->
      if i < w / 2 then lookup_tree i t1 else lookup_tree (i - (w / 2)) t2
    | _ -> None
  ;;

  let lookup_trees i ts =
    List.fold_left
      (fun ((r, sz) as res) t ->
         if Option.is_some r
         then res
         else (if i < sz + size t then lookup_tree (i - sz) t else r), sz + size t)
      (None, 0)
      ts
  ;;

  let rec lookup i = function
    | [] -> raise (Failure "lookup: not found")
    | ds ->
      let ts, ds' = uncons_step ds in
      (match lookup_trees i ts with
       | Some e, _ -> e
       | None, sz -> lookup (i - sz) ds')
  ;;
end

(* Figure 9.7 *)

module SkewBinaryRandomAccessList : RANDOM_ACCESS_LIST = struct
  type 'a tree =
    | Leaf of 'a
    | Node of 'a * 'a tree * 'a tree

  type 'a rlist = (int * 'a tree) list

  let empty = []

  let is_empty = function
    | [] -> true
    | _ -> false
  ;;

  let cons x = function
    | (w1, t1) :: (w2, t2) :: ts' as ts ->
      if w1 = w2 then (1 + w1 + w2, Node (x, t1, t2)) :: ts' else (1, Leaf x) :: ts
    | ts -> (1, Leaf x) :: ts
  ;;

  let head = function
    | [] -> raise (Failure "head: empty list")
    | (1, Leaf x) :: _ -> x
    | (_, Node (x, _, _)) :: _ -> x
    | _ -> assert false
  ;;

  let tail = function
    | [] -> raise (Failure "tail: empty list")
    | (1, Leaf _) :: ts -> ts
    | (w, Node (_, t1, t2)) :: ts -> (w / 2, t1) :: (w / 2, t2) :: ts
    | _ -> assert false
  ;;

  let rec lookup_tree w i xs =
    match w, i, xs with
    | 1, 0, Leaf x -> x
    | 1, _, Leaf _ -> raise (Failure "lookup: not found")
    | _, 0, Node (x, _, _) -> x
    | w, i, Node (_, t1, t2) ->
      if i <= w / 2
      then lookup_tree (w / 2) (i - 1) t1
      else lookup_tree (w / 2) (i - 1 - (w / 2)) t2
    | _ -> assert false
  ;;

  let rec update_tree w i x xs =
    match w, i, x, xs with
    | 1, 0, y, Leaf _ -> Leaf y
    | 1, _, _, Leaf _ -> raise (Failure "update: not found")
    | _, 0, y, Node (_, t1, t2) -> Node (y, t1, t2)
    | w, i, y, Node (x, t1, t2) ->
      if i <= w / 2
      then Node (x, update_tree (w / 2) (i - 1) y t1, t2)
      else Node (x, t1, update_tree (w / 2) (i - 1 - (w / 2)) y t2)
    | _ -> assert false
  ;;

  let rec lookup i = function
    | [] -> raise (Failure "lookup: not found")
    | (w, t) :: ts -> if i < w then lookup_tree w i t else lookup (i - w) ts
  ;;

  let rec update i y = function
    | [] -> raise (Failure "update: not found")
    | (w, t) :: ts ->
      if i < w then (w, update_tree w i y t) :: ts else (w, t) :: update (i - w) y ts
  ;;
end

(* Exercise 9.14 Rewrite the HoodMelvilleQueue structure from Section 8.2.1 to use skew
  binary random-access lists instead of regular lists. Implement lookup and update
  functions on these queues. *)

module type QUEUE = sig
  type 'a queue

  val empty : 'a queue
  val is_empty : 'a queue -> bool
  val snoc : 'a queue -> 'a -> 'a queue
  val head : 'a queue -> 'a
  val tail : 'a queue -> 'a queue
end

module type QUEUE_WITH_LOOKUP_AND_UPDATE = sig
  include QUEUE

  val lookup : int -> 'a queue -> 'a
  val update : int -> 'a -> 'a queue -> 'a queue
end

module SkewHoodMelvilleQueue : QUEUE_WITH_LOOKUP_AND_UPDATE = struct
  module A = SkewBinaryRandomAccessList

  type 'a rotation_state =
    (* Idle *)
    | I
    (* Reversing *)
    | R of
        { k : int (* valid element count *)
        ; f : 'a A.rlist
        ; f' : 'a A.rlist
        ; r : 'a A.rlist
        ; lenr : int
        ; r' : 'a A.rlist
        ; lenr' : int
        }
    (* Append *)
    | A of
        { k : int (* valid element count *)
        ; f' : 'a A.rlist
        ; r' : 'a A.rlist
        ; n : int
        }
    (* Done *)
    | D of 'a A.rlist

  type 'a queue =
    { f : 'a A.rlist
    ; lenf : int
    ; r : 'a A.rlist
    ; lenr : int
    ; state : 'a rotation_state
    }

  let noemp xs = not (A.is_empty xs)

  let invalidate = function
    | R st -> R { st with k = st.k - 1 }
    | A { k = 0; r' } when noemp r' -> D (A.tail r')
    | A st -> A { st with k = st.k - 1 }
    | st -> st
  ;;

  let conshd a b = A.cons (A.head a) b

  let step = function
    | R { k; f; f'; r; lenr; r'; lenr' } when noemp f && lenr > 0 ->
      R
        { k = k + 1
        ; f = A.tail f
        ; f' = conshd f f'
        ; r = A.tail r
        ; lenr = lenr - 1
        ; r' = conshd r r'
        ; lenr' = lenr' + 1
        }
    | R { k; f; f'; r; lenr; r'; lenr' } when A.is_empty f && lenr = 1 ->
      A { k; f'; r' = conshd r r'; n = lenr + lenr' }
    | A { k = 0; r' } -> D r'
    | A { k; f'; r'; n } when noemp f' ->
      A { k = k - 1; f' = A.tail f'; r' = conshd f' r'; n }
    | st -> st
  ;;

  let commit q = function
    | D newf -> { q with f = newf; state = I }
    | newstate -> { q with state = newstate }
  ;;

  let step_up q = q.state |> step |> commit q

  let start_rebuild { f; lenf; r; lenr } =
    let state = R { k = 0; f; f' = A.empty; r; lenr; r' = A.empty; lenr' = 0 } in
    let q = { f; lenf = lenf + lenr; r = A.empty; lenr = 0; state } in
    q.state |> step |> step |> commit q
  ;;

  let check q = if q.lenr <= q.lenf then step_up q else start_rebuild q
  let empty = { f = A.empty; lenf = 0; r = A.empty; lenr = 0; state = I }
  let is_empty q = A.is_empty q.f
  let snoc q x = check { q with r = A.cons x q.r; lenr = q.lenr + 1 }
  let head q = if is_empty q then raise (Failure "head: empty queue") else A.head q.f

  let tail q =
    if is_empty q
    then raise (Failure "tail: empty queue")
    else check { q with f = A.tail q.f; lenf = q.lenf - 1; state = invalidate q.state }
  ;;

  let lookup i q =
    let notfound () = raise (Failure "lookup: not found") in
    let lookup_r_exn () =
      if i < q.lenf + q.lenr then A.lookup (q.lenf + q.lenr - i - 1) q.r else notfound ()
    in
    if is_empty q
    then notfound ()
    else (
      match q.state with
      | I -> if i < q.lenf then A.lookup i q.f else lookup_r_exn ()
      | R { r; lenr; r'; lenr' } ->
        if i < q.lenf - lenr - lenr'
        then A.lookup i q.f
        else if i < q.lenf - lenr'
        then A.lookup (q.lenf - lenr' - i - 1) r
        else if i < q.lenf
        then A.lookup (i - q.lenf + lenr') r'
        else lookup_r_exn ()
      | A { k; r' } ->
        if i < k
        then A.lookup i q.f
        else if i < q.lenf
        then A.lookup (i - k) r'
        else lookup_r_exn ()
      | _ -> assert false)
  ;;

  let update i x q =
    let notfound () = raise (Failure "update: not found") in
    let update_r_exn () =
      if i < q.lenf + q.lenr
      then { q with r = A.update (q.lenf + q.lenr - i - 1) x q.r }
      else notfound ()
    in
    if is_empty q
    then notfound ()
    else (
      match q.state with
      | I -> if i < q.lenf then { q with f = A.update i x q.f } else update_r_exn ()
      | R ({ k; f; f'; r; lenr; r'; lenr' } as st) ->
        if i < q.lenf - lenr - lenr'
        then
          { q with
            f = A.update i x q.f
          ; state =
              (if i < k
               then R { st with f' = A.update (k - i - 1) x f' }
               else R { st with f = A.update (i - k) x f })
          }
        else if i < q.lenf - lenr'
        then { q with state = R { st with r = A.update (q.lenf - lenr' - i - 1) x r } }
        else if i < q.lenf
        then { q with state = R { st with r' = A.update (i - q.lenf + lenr') x r' } }
        else update_r_exn ()
      | A ({ k; f'; r'; n } as st) ->
        if i < k
        then
          { q with
            f = A.update i x q.f
          ; state = A { st with f' = A.update (k - i - 1) x f' }
          }
        else if i < q.lenf
        then
          { q with
            f = (if i < q.lenf - n then A.update i x q.f else q.f)
          ; state = A { st with r' = A.update (i - k) x r' }
          }
        else update_r_exn ()
      | _ -> assert false)
  ;;
end

(* Figure 9.8 *)

module SkewBinomialHeap (E : ORDERED) : HEAP with module Element = E = struct
  module Element = E

  type tree = Node of int * Element.t * Element.t list * tree list
  type heap = tree list

  let empty = []

  let is_empty = function
    | [] -> true
    | _ -> false
  ;;

  let rank (Node (r, _, _, _)) = r
  let root (Node (_, x, _, _)) = x

  let link (Node (r, x1, xs1, c1) as t1) (Node (_, x2, xs2, c2) as t2) =
    if Element.leq x1 x2
    then Node (r + 1, x1, xs1, t2 :: c1)
    else Node (r + 1, x2, xs2, t1 :: c2)
  ;;

  let skew_link x t1 t2 =
    let (Node (r, y, ys, c)) = link t1 t2 in
    if Element.leq x y then Node (r, x, y :: ys, c) else Node (r, y, x :: ys, c)
  ;;

  let rec ins_tree t1 = function
    | [] -> [ t1 ]
    | t2 :: ts -> if rank t1 < rank t2 then t1 :: t2 :: ts else ins_tree (link t1 t2) ts
  ;;

  let rec merge_trees ts1 ts2 =
    match ts1, ts2 with
    | _, [] -> ts1
    | [], _ -> ts2
    | t1 :: ts1', t2 :: ts2' ->
      if rank t1 < rank t2
      then t1 :: merge_trees ts1' ts2
      else if rank t2 < rank t1
      then t2 :: merge_trees ts1 ts2'
      else ins_tree (link t1 t2) (merge_trees ts1' ts2')
  ;;

  let normalize = function
    | [] -> []
    | t :: ts -> ins_tree t ts
  ;;

  let insert x = function
    | t1 :: t2 :: rest as ts ->
      if rank t1 = rank t2 then skew_link x t1 t2 :: rest else Node (0, x, [], []) :: ts
    | ts -> Node (0, x, [], []) :: ts
  ;;

  let merge ts1 ts2 = merge_trees (normalize ts1) (normalize ts2)

  let rec remove_min_tree = function
    | [ t ] -> t, []
    | t :: ts ->
      let t', ts' = remove_min_tree ts in
      if Element.leq (root t) (root t') then t, ts else t', t :: ts'
    | _ -> assert false
  ;;

  let find_min = function
    | [] -> raise (Failure "find_min: empty heap")
    | ts ->
      let t, _ = remove_min_tree ts in
      root t
  ;;

  let rec insert_all xs ts =
    match xs with
    | [] -> ts
    | x :: xs -> insert_all xs (insert x ts)
  ;;

  let delete_min = function
    | [] -> raise (Failure "delete_min: empty heap")
    | ts ->
      let Node (_, _, xs, ts1), ts2 = remove_min_tree ts in
      insert_all xs (merge (List.rev ts1) ts2)
  ;;
end

(* Exercise 9.16 Suppose we want a delete function of type Elem.T x Heap —> Heap. Write a
  functor that takes an implementation H of heaps and produces an implementation of heaps
  that supports delete as well as all the other usual heap functions. Use the type type

  Heap = H.Heap x H.Heap

  where one of the primitive heaps represents positive occurrences of elements and the
  other represents negative occurrences. A negative occurrence of an element means that
  that element has been deleted, but not yet physically removed from the heap. Positive
  and negative occurrences of the same element cancel each other out and are physically
  removed when both become the minimum elements of their respective heaps. Maintain the
  invariant that the minimum element of the positive heap is strictly smaller than the
  minimum element of the negative heap. (This implementation has the curious property
  that an element can be deleted before it has been inserted, but this is acceptable for
  many applications.)
 *)

module type HEAP_WITH_DELETE = sig
  include HEAP

  val delete : Element.t -> heap -> heap
end

module HeapWithDelete (E : ORDERED) (H : HEAP with module Element = E) :
  HEAP_WITH_DELETE with module Element = E = struct
  module Element = E

  type heap = H.heap * H.heap

  let empty = H.empty, H.empty
  let is_empty (pos, _) = H.is_empty pos

  let rec check ((pos, neg) as h) =
    if H.is_empty pos || H.is_empty neg
    then h
    else (
      let p = H.find_min pos
      and n = H.find_min neg in
      if Element.lt p n
      then h
      else if Element.eq p n
      then check (H.delete_min pos, H.delete_min neg)
      else check (pos, H.delete_min neg))
  ;;

  let insert e (pos, neg) =
    let h' = H.insert e pos, neg in
    if H.is_empty pos then check h' else h'
  ;;

  let delete e (pos, neg) = check (pos, H.insert e neg)
  let merge (pos1, neg1) (pos2, neg2) = check (H.merge pos1 pos2, H.merge neg1 neg2)
  let find_min (pos, _) = H.find_min pos
  let delete_min (pos, neg) = check (H.delete_min pos, neg)
end
