module type QUEUE = sig
  type 'a queue

  val empty : 'a queue
  val is_empty : 'a queue -> bool
  val snoc : 'a queue -> 'a -> 'a queue
  val head : 'a queue -> 'a
  val tail : 'a queue -> 'a queue
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

module BankersQueue (Stream : STREAM) : QUEUE = struct
  open Stream

  type 'a queue = int * 'a stream * int * 'a stream

  let empty = 0, lazy Nil, 0, lazy Nil
  let is_empty (lenf, _, _, _) = lenf = 0

  let check ((lenf, f, lenr, r) as q) =
    if lenr <= lenf then q else lenf + lenr, f ++ reverse r, 0, lazy Nil
  ;;

  let snoc (lenf, f, lenr, r) x = check (lenf, f, lenr + 1, lazy (Cons (x, r)))

  let head = function
    | _, (lazy Nil), _, _ -> raise (Failure "head: empty queue")
    | _, (lazy (Cons (x, _))), _, _ -> x
  ;;

  let tail = function
    | _, (lazy Nil), _, _ -> raise (Failure "tail: empty queue")
    | lenf, (lazy (Cons (_, f))), lenr, r -> check (lenf - 1, f, lenr, r)
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

module LazyBinomialHeap (Element : ORDERED) : HEAP with module Element = Element = struct
  module Element = Element

  type tree = Node of int * Element.t * tree list
  type heap = tree list lazy_t

  let empty = lazy []

  let is_empty = function
    | (lazy []) -> true
    | _ -> false
  ;;

  let rank (Node (r, _, _)) = r
  let root (Node (_, x, _)) = x

  let link (Node (r, v1, c1) as t1) (Node (_, v2, c2) as t2) =
    if Element.leq v1 v2 then Node (r + 1, v1, t2 :: c1) else Node (r + 1, v2, t1 :: c2)
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

  let insert x h = lazy (ins_tree (Node (0, x, [])) (Lazy.force h))
  let merge h1 h2 = lazy (mrg (Lazy.force h1) (Lazy.force h2))

  let rec remove_min_tree = function
    | [] -> raise (Failure "remove_min_tree: empty tree")
    | [ t ] -> t, []
    | t :: ts ->
      let t', ts' = remove_min_tree ts in
      if Element.leq (root t) (root t') then t, ts else t', t :: ts'
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

module PhysicistsQueue : QUEUE = struct
  type 'a queue = 'a list * int * 'a list lazy_t * int * 'a list

  let empty = [], 0, lazy [], 0, []

  let is_empty = function
    | _, 0, _, _, _ -> true
    | _ -> false
  ;;

  let checkw = function
    | [], lenf, f, lenr, r -> Lazy.force f, lenf, f, lenr, r
    | q -> q
  ;;

  let check ((_, lenf, f, lenr, r) as q) =
    if lenr <= lenf
    then checkw q
    else (
      let f' = Lazy.force f in
      checkw (f', lenf + lenr, lazy (f' @ List.rev r), 0, []))
  ;;

  let snoc (w, lenf, f, lenr, r) x = check (w, lenf, f, lenr + 1, x :: r)

  let head = function
    | [], _, _, _, _ -> raise (Failure "head: empty queue")
    | x :: _, _, _, _, _ -> x
  ;;

  let tail = function
    | [], _, _, _, _ -> raise (Failure "tail: empty queue")
    | _ :: w, lenf, f, lenr, r ->
      check (w, lenf - 1, lazy (List.tl (Lazy.force f)), lenr, r)
  ;;
end

module type SORTABLE = sig
  module Element : ORDERED

  type sortable

  val empty : sortable
  val add : Element.t -> sortable -> sortable
  val sort : sortable -> Element.t list
end

module BottomUpMergeSort (Element : ORDERED) : SORTABLE with module Element = Element =
struct
  module Element = Element

  type sortable = int * Element.t list list lazy_t

  let rec mrg a b =
    match a, b with
    | _, [] -> a
    | [], _ -> b
    | x :: xs, y :: ys -> if Element.leq x y then x :: mrg xs b else y :: mrg a ys
  ;;

  let empty = 0, lazy []

  let add x (size, segs) =
    let rec add_seg s ss sz =
      if sz mod 2 = 0 then s :: ss else add_seg (mrg s (List.hd ss)) (List.tl ss) (sz / 2)
    in
    size + 1, lazy (add_seg [ x ] (Lazy.force segs) size)
  ;;

  let sort (_, segs) =
    let rec mrg_all a b =
      match a, b with
      | _, [] -> a
      | _, s :: ss -> mrg_all (mrg a s) ss
    in
    mrg_all [] (Lazy.force segs)
  ;;
end

module LazyPairingHeap (Element : ORDERED) : HEAP with module Element = Element = struct
  module Element = Element

  type heap =
    | E
    | T of Element.t * heap * heap lazy_t

  let empty = E

  let is_empty = function
    | E -> true
    | _ -> false
  ;;

  let rec merge a b =
    match a, b with
    | a, E -> a
    | E, b -> b
    | T (x, _, _), T (y, _, _) -> if Element.leq x y then link a b else link b a

  and link a b =
    match a with
    | E -> raise (Failure "merge")
    | T (x, E, m) -> T (x, b, m)
    | T (x, a', m) -> T (x, E, lazy (merge (merge b a') (Lazy.force m)))
  ;;

  let insert x a = merge (T (x, E, lazy E)) a

  let find_min = function
    | E -> raise (Failure "find_min: empty heap")
    | T (x, _, _) -> x
  ;;

  let delete_min = function
    | E -> raise (Failure "delete_min: empty heap")
    | T (_, a, (lazy b)) -> merge a b
  ;;
end
