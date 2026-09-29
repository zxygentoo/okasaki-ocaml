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
