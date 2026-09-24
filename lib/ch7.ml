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

module type QUEUE = sig
  type 'a queue

  val empty : 'a queue
  val is_empty : 'a queue -> bool
  val snoc : 'a queue -> 'a -> 'a queue
  val head : 'a queue -> 'a
  val tail : 'a queue -> 'a queue
end

module type QUEUE_WITH_SIZES = sig
  include QUEUE

  val size_sr : 'a queue -> int
  val size_fr : 'a queue -> int
end

module RealTimeQueue (Strem : STREAM) : QUEUE_WITH_SIZES = struct
  module S = Strem

  type 'a queue = 'a S.stream * 'a list * 'a S.stream

  let empty = lazy S.Nil, [], lazy S.Nil

  let is_empty = function
    | (lazy S.Nil), _, _ -> true
    | _ -> false
  ;;

  let[@ocaml.warning "-partial-match"] rec rotate x y a =
    match x, y with
    | (lazy S.Nil), y :: _ -> lazy (S.Cons (y, a))
    | (lazy (S.Cons (x, xs))), y :: ys ->
      lazy (S.Cons (x, rotate xs ys (lazy (S.Cons (y, a)))))
  ;;

  let exec (f, r, s) =
    match s with
    | (lazy S.Nil) ->
      let f' = rotate f r s in
      f', [], f'
    | (lazy (S.Cons (_, s'))) -> f, r, s'
  ;;

  let snoc (f, r, s) x = exec (f, x :: r, s)

  let head = function
    | (lazy S.Nil), _, _ -> raise (Failure "head: empty queue")
    | (lazy (S.Cons (x, _))), _, _ -> x
  ;;

  let tail = function
    | (lazy S.Nil), _, _ -> raise (Failure "tail: empty queue")
    | (lazy (S.Cons (_, f'))), r, s -> exec (f', r, s)
  ;;

  (* Exercise 7.2 Compute the size of a queue from the sizes of s and r. How much faster
     might such a function run than one that measures the sizes of f andr? *)

  let rec qlen = function
    | (lazy S.Nil) -> 0
    | (lazy (S.Cons (_, q))) -> 1 + qlen q
  ;;

  let size_sr (_, r, s) = qlen s + (2 * List.length r)
  let size_fr (f, r, _) = qlen f + List.length r
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

module ScheduledBinomialHeap (Elem : ORDERED) (Stream : STREAM) :
  HEAP with module Element = Elem = struct
  module Element = Elem
  module S = Stream

  type tree = Node of Element.t * tree list

  type digit =
    | Zero
    | One of tree

  type schedule = digit S.stream list
  type heap = digit S.stream * schedule

  let empty = lazy S.Nil, []

  let is_empty = function
    | (lazy S.Nil), _ -> true
    | _ -> false
  ;;

  let link (Node (x1, c1) as t1) (Node (x2, c2) as t2) =
    if Element.leq x1 x2 then Node (x1, t2 :: c1) else Node (x2, t1 :: c2)
  ;;

  let rec ins_tree t = function
    | (lazy S.Nil) -> lazy (S.Cons (One t, lazy S.Nil))
    | (lazy (S.Cons (Zero, ds))) -> lazy (S.Cons (One t, ds))
    | (lazy (S.Cons (One t', ds))) -> lazy (S.Cons (Zero, ins_tree (link t t') ds))
  ;;

  let rec mrg ds1 ds2 =
    match ds1, ds2 with
    | _, (lazy S.Nil) -> ds1
    | (lazy S.Nil), _ -> ds2
    | (lazy (S.Cons (Zero, ds1'))), (lazy (S.Cons (d, ds2')))
    | (lazy (S.Cons (d, ds1'))), (lazy (S.Cons (Zero, ds2'))) ->
      lazy (S.Cons (d, mrg ds1' ds2'))
    | (lazy (S.Cons (One t1, ds1'))), (lazy (S.Cons (One t2, ds2'))) ->
      lazy (S.Cons (Zero, ins_tree (link t1 t2) (mrg ds1' ds2')))
  ;;

  let rec normalize ds =
    match ds with
    | (lazy S.Nil) -> ds
    | (lazy (S.Cons (_, ds'))) ->
      ignore (normalize ds');
      ds
  ;;

  let exec = function
    | [] -> []
    | (lazy (S.Cons (Zero, job))) :: sched -> job :: sched
    | _ :: sched -> sched
  ;;

  let insert x (ds, sched) =
    let ds' = ins_tree (Node (x, [])) ds in
    ds', exec (exec (ds' :: sched))
  ;;

  let merge (ds1, _) (ds2, _) =
    let ds = normalize (mrg ds1 ds2) in
    ds, []
  ;;

  let rec remove_min_tree = function
    | (lazy S.Nil) -> raise (Failure "empty heap")
    | (lazy (S.Cons (One t, (lazy S.Nil)))) -> t, lazy S.Nil
    | (lazy (S.Cons (Zero, ds))) ->
      let t', ds' = remove_min_tree ds in
      t', lazy (S.Cons (Zero, ds'))
    | (lazy (S.Cons (One (Node (x, _) as t), ds))) ->
      let (Node (x', _) as t'), ds' = remove_min_tree ds in
      if Element.leq x x'
      then t, lazy (S.Cons (Zero, ds))
      else t', lazy (S.Cons (One t, ds'))
  ;;

  let find_min (ds, _) =
    let Node (x, _), _ =
      try remove_min_tree ds with
      | Failure _ -> raise (Failure "find_min: empty heap")
    in
    x
  ;;

  (* Exercise 7.4 Write an efficient, specialized version of mrg, called mrgWithList, so
     that deleteMin can call

     mrgWithList (rev c, ds')

     instead of

     mrg (listToStream (map ONE (rev c)), ds')
  *)

  let rec mrg_with_list xs ds =
    match xs, ds with
    | [], _ -> ds
    | x :: xs, (lazy S.Nil) -> Lazy.from_val (S.Cons (One x, mrg_with_list xs ds))
    | x :: xs', (lazy (S.Cons (Zero, ds'))) ->
      Lazy.from_val (S.Cons (One x, mrg_with_list xs' ds'))
    | x :: xs', (lazy (S.Cons (One t, ds'))) ->
      Lazy.from_val (S.Cons (Zero, ins_tree (link x t) (mrg_with_list xs' ds')))
  ;;

  let delete_min (ds, _) =
    let Node (_, c), ds' =
      try remove_min_tree ds with
      | Failure _ -> raise (Failure "delete_min: empty heap")
    in
    normalize (mrg_with_list (List.rev c) ds'), []
  ;;
end

module type SORTABLE = sig
  module Element : ORDERED

  type sortable

  val empty : sortable
  val add : Element.t -> sortable -> sortable
  val sort : sortable -> Element.t list
end

module ScheduledBottomUpMergeSort (Elem : ORDERED) (Stream : STREAM) :
  SORTABLE with module Element = Elem = struct
  module Element = Elem
  module S = Stream

  type schedule = Element.t S.stream list
  type sortable = int * (Element.t S.stream * schedule) list

  let rec mrg xs ys =
    lazy
      (match xs, ys with
       | _, (lazy S.Nil) -> Lazy.force xs
       | (lazy S.Nil), _ -> Lazy.force ys
       | (lazy (S.Cons (x, xs'))), (lazy (S.Cons (y, ys'))) ->
         if Element.leq x y then S.Cons (x, mrg xs' ys) else S.Cons (y, mrg xs ys'))
  ;;

  let rec exec1 = function
    | [] -> []
    | (lazy S.Nil) :: sched -> exec1 sched
    | (lazy (S.Cons (_, xs))) :: sched -> xs :: sched
  ;;

  let exec2 (xs, sched) = xs, exec1 (exec1 sched)
  let empty = 0, []

  let add x (size, segs) =
    let rec add_seg xs ss sz rsched =
      if sz mod 2 = 0
      then (xs, List.rev rsched) :: ss
      else (
        let[@ocaml.warning "-partial-match"] ((xs', []) :: ss') = ss in
        let xs'' = mrg xs xs' in
        add_seg xs'' ss' (sz / 2) (xs'' :: rsched))
    in
    let segs' = add_seg (lazy (S.Cons (x, lazy S.Nil))) segs size [] in
    size + 1, List.map exec2 segs'
  ;;

  let rec stream_to_list = function
    | (lazy S.Nil) -> []
    | (lazy (S.Cons (x, xs))) -> x :: stream_to_list xs
  ;;

  let sort (_, segs) =
    let rec mrg_all xs = function
      | [] -> xs
      | (xs', _) :: ss -> mrg_all (mrg xs xs') ss
    in
    stream_to_list (mrg_all (lazy S.Nil) segs)
  ;;
end
