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

(* Figure 11.1 *)

module ImplicitQueue : QUEUE = struct
  type 'a digit =
    | Zero
    | One of 'a
    | Two of 'a * 'a

  type 'a queue =
    | Shallow of 'a digit
    | Deep of 'a digit * ('a * 'a) queue lazy_t * 'a digit

  let empty = Shallow Zero

  let is_empty = function
    | Shallow Zero -> true
    | _ -> false
  ;;

  let rec snoc : 'a. 'a queue -> 'a -> 'a queue =
    fun q y ->
    match q with
    | Shallow Zero -> Shallow (One y)
    | Shallow (One x) -> Deep (Two (x, y), lazy empty, Zero)
    | Deep (f, m, Zero) -> Deep (f, m, One y)
    | Deep (f, m, One x) -> Deep (f, lazy (snoc (Lazy.force m) (x, y)), Zero)
    | _ -> assert false
  ;;

  let head : 'a. 'a queue -> 'a = function
    | Shallow Zero -> raise (Failure "head: empty queue")
    | Shallow (One x) -> x
    | Deep (One x, _, _) -> x
    | Deep (Two (x, _), _, _) -> x
    | _ -> assert false
  ;;

  let rec tail : 'a. 'a queue -> 'a queue = function
    | Shallow Zero -> raise (Failure "tail: empty queue")
    | Shallow (One _) -> empty
    | Deep (Two (_, y), m, r) -> Deep (One y, m, r)
    | Deep (One _, (lazy q), r) ->
      if is_empty q
      then Shallow r
      else (
        let y, z = head q in
        Deep (Two (y, z), lazy (tail q), r))
    | _ -> assert false
  ;;
end

(* Exercise 11.1 Implement lookup and update functions for these queues.
Your functions should run in O(logi) amortized time. You may find it helpful
to augment each queue with a size field. *)

module ImplicitQueueWithLookupAndUpdate : QUEUE_WITH_LOOKUP_AND_UPDATE = struct
  type 'a digit =
    | Zero
    | One of 'a
    | Two of 'a * 'a

  type 'a queue =
    | Shallow of 'a digit
    | Deep of int * 'a digit * ('a * 'a) queue lazy_t * 'a digit

  let empty = Shallow Zero

  let size = function
    | Zero -> 0
    | One _ -> 1
    | Two _ -> 2
  ;;

  let is_empty = function
    | Shallow Zero -> true
    | _ -> false
  ;;

  let rec snoc : 'a. 'a queue -> 'a -> 'a queue =
    fun q y ->
    match q with
    | Shallow Zero -> Shallow (One y)
    | Shallow (One x) -> Deep (2, Two (x, y), lazy empty, Zero)
    | Deep (sz, f, m, Zero) -> Deep (sz + 1, f, m, One y)
    | Deep (sz, f, m, One x) -> Deep (sz + 1, f, lazy (snoc (Lazy.force m) (x, y)), Zero)
    | _ -> assert false
  ;;

  let head : 'a. 'a queue -> 'a = function
    | Shallow Zero -> raise (Failure "head: empty queue")
    | Shallow (One x) -> x
    | Deep (_, One x, _, _) -> x
    | Deep (_, Two (x, _), _, _) -> x
    | _ -> assert false
  ;;

  let rec tail : 'a. 'a queue -> 'a queue = function
    | Shallow Zero -> raise (Failure "tail: empty queue")
    | Shallow (One _) -> empty
    | Deep (sz, Two (_, y), m, r) -> Deep (sz - 1, One y, m, r)
    | Deep (sz, One _, (lazy q), r) ->
      if is_empty q
      then Shallow r
      else (
        let y, z = head q in
        Deep (sz - 1, Two (y, z), lazy (tail q), r))
    | _ -> assert false
  ;;

  let look i d =
    match i, d with
    | 0, (One x | Two (x, _)) -> x
    | 1, Two (_, y) -> y
    | _ -> raise (Failure "lookup: not found")
  ;;

  let rec lookup : 'a. int -> 'a queue -> 'a =
    fun i -> function
    | Shallow (One x) when i = 0 -> x
    | Deep (sz, f, m, r) ->
      if i < size f
      then look i f
      else (
        let i' = i - size f
        and ms = (sz - size f - size r) / 2 in
        if i' < 2 * ms
        then (
          let x, y = lookup (i' / 2) (Lazy.force m) in
          if i' mod 2 = 0 then x else y)
        else look (i' - (2 * ms)) r)
    | _ -> raise (Failure "lookup: not found")
  ;;

  let put i f d =
    match i, d with
    | 0, One x -> One (f x)
    | 0, Two (x, y) -> Two (f x, y)
    | 1, Two (x, y) -> Two (x, f y)
    | _ -> raise (Failure "update: not found")
  ;;

  let rec fupdate : 'a. ('a -> 'a) -> int -> 'a queue -> 'a queue =
    fun g i q ->
    let err () = raise (Failure "update: not found") in
    if i < 0
    then err ()
    else (
      match q with
      | Shallow (One x) when i = 0 -> Shallow (One (g x))
      | Deep (sz, f, m, r) ->
        if i < size f
        then Deep (sz, put i g f, m, r)
        else (
          let i' = i - size f
          and ms = (sz - size f - size r) / 2 in
          if i' < 2 * ms
          then (
            let g' (x, y) = if i' mod 2 = 0 then g x, y else x, g y in
            Deep (sz, f, lazy (fupdate g' (i' / 2) (Lazy.force m)), r))
          else Deep (sz, f, m, put (i' - (2 * ms)) g r))
      | _ -> raise (Failure "update: not found"))
  ;;

  let update : 'a. int -> 'a -> 'a queue -> 'a queue =
    fun i x q -> fupdate (fun _ -> x) i q
  ;;
end

(* Exercise 11.2 Implement double-ended queues using the techniques of this section. *)

module type DEQUE = sig
  include QUEUE

  val cons : 'a -> 'a queue -> 'a queue
  val last : 'a queue -> 'a
  val init : 'a queue -> 'a queue
end

module ImplicitDeque : DEQUE = struct
  type 'a digit =
    | Zero
    | One of 'a
    | Two of 'a * 'a
    | Three of 'a * 'a * 'a

  type 'a queue =
    | Shallow of 'a digit
    | Deep of 'a digit * ('a * 'a) queue lazy_t * 'a digit

  let empty = Shallow Zero

  let is_empty = function
    | Shallow Zero -> true
    | _ -> false
  ;;

  let rec snoc : 'a. 'a queue -> 'a -> 'a queue =
    fun q y ->
    match q with
    | Shallow Zero -> Shallow (One y)
    | Shallow (One x) -> Shallow (Two (x, y))
    | Shallow (Two (a, b)) -> Shallow (Three (a, b, y))
    | Shallow (Three (a, b, c)) -> Deep (Three (a, b, c), lazy empty, One y)
    | Deep (f, m, One x) -> Deep (f, m, Two (x, y))
    | Deep (f, m, Two (a, b)) -> Deep (f, m, Three (a, b, y))
    | Deep (f, m, Three (a, b, c)) ->
      Deep (f, lazy (snoc (Lazy.force m) (a, b)), Two (c, y))
    | _ -> assert false
  ;;

  let rec cons : 'a. 'a -> 'a queue -> 'a queue =
    fun x q ->
    match q with
    | Shallow Zero -> Shallow (One x)
    | Shallow (One y) -> Shallow (Two (x, y))
    | Shallow (Two (a, b)) -> Shallow (Three (x, a, b))
    | Shallow (Three (a, b, c)) -> Deep (Three (x, a, b), lazy empty, One c)
    | Deep (One y, m, r) -> Deep (Two (x, y), m, r)
    | Deep (Two (a, b), m, r) -> Deep (Three (x, a, b), m, r)
    | Deep (Three (a, b, c), m, r) ->
      Deep (Two (x, a), lazy (cons (b, c) (Lazy.force m)), r)
    | _ -> assert false
  ;;

  let head = function
    | Shallow Zero -> raise (Failure "head: empty queue")
    | Shallow (One x) -> x
    | Shallow (Two (x, _)) -> x
    | Shallow (Three (x, _, _)) -> x
    | Deep (One x, _, _) -> x
    | Deep (Two (x, _), _, _) -> x
    | Deep (Three (x, _, _), _, _) -> x
    | _ -> assert false
  ;;

  let last = function
    | Shallow Zero -> raise (Failure "last: empty queue")
    | Shallow (One x) -> x
    | Shallow (Two (_, y)) -> y
    | Shallow (Three (_, _, z)) -> z
    | Deep (_, _, One x) -> x
    | Deep (_, _, Two (_, y)) -> y
    | Deep (_, _, Three (_, _, z)) -> z
    | _ -> assert false
  ;;

  let rec tail : 'a. 'a queue -> 'a queue = function
    | Shallow Zero -> raise (Failure "tail: empty queue")
    | Shallow (One _) -> empty
    | Shallow (Two (_, y)) -> Shallow (One y)
    | Shallow (Three (_, y, z)) -> Shallow (Two (y, z))
    | Deep (One _, (lazy q), r) ->
      if is_empty q
      then Shallow r
      else (
        let y, z = head q in
        Deep (Two (y, z), lazy (tail q), r))
    | Deep (Two (_, y), m, r) -> Deep (One y, m, r)
    | Deep (Three (_, x, y), m, r) -> Deep (Two (x, y), m, r)
    | _ -> assert false
  ;;

  let rec init : 'a. 'a queue -> 'a queue = function
    | Shallow Zero -> raise (Failure "init: empty queue")
    | Shallow (One _) -> empty
    | Shallow (Two (x, _)) -> Shallow (One x)
    | Shallow (Three (x, y, _)) -> Shallow (Two (x, y))
    | Deep (f, (lazy q), One _) ->
      if is_empty q
      then Shallow f
      else (
        let x, y = last q in
        Deep (f, lazy (init q), Two (x, y)))
    | Deep (f, m, Two (x, _)) -> Deep (f, m, One x)
    | Deep (f, m, Three (x, y, _)) -> Deep (f, m, Two (x, y))
    | _ -> assert false
  ;;
end
