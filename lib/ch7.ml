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
