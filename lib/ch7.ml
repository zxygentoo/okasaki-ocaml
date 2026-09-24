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

module RealTimeQueue (Strem : STREAM) : QUEUE = struct
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
end
