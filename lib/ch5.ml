module type QUEUE = sig
  type 'a queue

  val empty : 'a queue
  val is_empty : 'a queue -> bool
  val snoc : 'a queue -> 'a -> 'a queue
  val head : 'a queue -> 'a
  val tail : 'a queue -> 'a queue
end

module BatchedQueue : QUEUE = struct
  type 'a queue = 'a list * 'a list

  let empty = [], []
  let is_empty (f, _) = List.is_empty f

  let checkf = function
    | [], r -> List.rev r, []
    | q -> q
  ;;

  let snoc (f, r) x = checkf (f, x :: r)

  let head = function
    | [], _ -> raise (Failure "head: empty queue")
    | x :: _, _ -> x
  ;;

  let tail = function
    | [], _ -> raise (Failure "tail: empty queue")
    | _ :: f, r -> checkf (f, r)
  ;;
end
