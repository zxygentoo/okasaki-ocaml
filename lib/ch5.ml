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

  let checkf = function
    | [], r -> List.rev r, []
    | q -> q
  ;;

  let empty = [], []
  let is_empty (f, _) = List.is_empty f
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

(* Exercise 5.1 (Hoogerwoord [Hoo92]) This design can easily be extended to support the
   double-ended queue, or deque, abstraction, which allows reads and writes to both ends
   of the queue (see Figure 5.3). The invariant is updated to be symmetric in its
   treatment of f and r: both are required to be non-empty whenever the deque contains two
   or more elements. When one list becomes empty, we split the other list in half and
   reverse one of the halves.

   (a) Implement this version of deques.
*)
module type DEQUE = sig
  include QUEUE

  val cons : 'a -> 'a queue -> 'a queue
  val last : 'a queue -> 'a
  val init : 'a queue -> 'a queue
end

module Deque : DEQUE = struct
  type 'a queue = 'a list * 'a list

  let rec split_at k xs =
    match k, xs with
    | 0, _ | _, [] -> [], xs
    | _, x :: xs ->
      let f, r = split_at (k - 1) xs in
      x :: f, r
  ;;

  let checkf = function
    | [], [] -> [], []
    | [ x ], [] -> [ x ], []
    | [], [ x ] -> [], [ x ]
    | f, [] ->
      let a, b = split_at (List.length f / 2) f in
      a, List.rev b
    | [], r ->
      let a, b = split_at (List.length r / 2) r in
      List.rev b, a
    | f, r -> f, r
  ;;

  let empty = [], []

  let is_empty = function
    | [], [] -> true
    | _ -> false
  ;;

  let snoc (f, r) x = checkf (f, x :: r)

  let head = function
    | [], [ x ] -> x
    | x :: _, _ -> x
    | _ -> raise (Failure "head: empty queue")
  ;;

  let tail = function
    | [ _ ], [] | [], [ _ ] -> [], []
    | _ :: f, r -> checkf (f, r)
    | _ -> raise (Failure "tail: empty queue")
  ;;

  let cons x (f, r) = checkf (x :: f, r)

  let last = function
    | [ x ], [] -> x
    | _, x :: _ -> x
    | _ -> raise (Failure "last: empty queue")
  ;;

  let init = function
    | [], [ _ ] | [ _ ], [] -> [], []
    | f, _ :: r -> checkf (f, r)
    | _ -> raise (Failure "init: empty queue")
  ;;
end
