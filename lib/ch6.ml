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
