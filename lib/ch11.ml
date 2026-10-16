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

(* Figure 11.2 *)

module type CATENABLE_DEQUE = sig
  type 'a cat

  val empty : 'a cat
  val is_empty : 'a cat -> bool
  val cons : 'a -> 'a cat -> 'a cat
  val head : 'a cat -> 'a
  val tail : 'a cat -> 'a cat
  val snoc : 'a cat -> 'a -> 'a cat
  val last : 'a cat -> 'a
  val init : 'a cat -> 'a cat
  val ( ++ ) : 'a cat -> 'a cat -> 'a cat
end

(* Figure 11.3 *)

module SimpleCatenableDeque (D : DEQUE) : CATENABLE_DEQUE = struct
  type 'a cat =
    | Shallow of 'a D.queue
    | Deep of 'a D.queue * 'a D.queue cat lazy_t * 'a D.queue

  let too_small d = D.is_empty d || D.is_empty (D.tail d)
  let dappendl d1 d2 = if D.is_empty d1 then d2 else D.cons (D.head d1) d2
  let dappendr d1 d2 = if D.is_empty d2 then d1 else D.snoc d1 (D.head d2)
  let empty = Shallow D.empty

  let is_empty = function
    | Shallow d -> D.is_empty d
    | _ -> false
  ;;

  let cons x = function
    | Shallow d -> Shallow (D.cons x d)
    | Deep (f, m, r) -> Deep (D.cons x f, m, r)
  ;;

  let snoc q x =
    match q with
    | Shallow d -> Shallow (D.snoc d x)
    | Deep (f, m, r) -> Deep (f, m, D.snoc r x)
  ;;

  let head = function
    | Shallow d -> D.head d
    | Deep (f, _, _) -> D.head f
  ;;

  let last = function
    | Shallow d -> D.last d
    | Deep (_, _, r) -> D.last r
  ;;

  let rec tail : 'a. 'a cat -> 'a cat = function
    | Shallow d -> Shallow (D.tail d)
    | Deep (f, m, r) ->
      let f' = D.tail f in
      if not (too_small f')
      then Deep (f', m, r)
      else if is_empty (Lazy.force m)
      then Shallow (dappendl f' r)
      else Deep (dappendl f' (head (Lazy.force m)), lazy (tail (Lazy.force m)), r)
  ;;

  let rec init : 'a. 'a cat -> 'a cat = function
    | Shallow d -> Shallow (D.init d)
    | Deep (f, m, r) ->
      let r' = D.init r in
      if not (too_small r')
      then Deep (f, m, r')
      else if is_empty (Lazy.force m)
      then Shallow (dappendr f r')
      else Deep (f, lazy (init (Lazy.force m)), dappendr (last (Lazy.force m)) r')
  ;;

  let rec ( ++ ) : 'a. 'a cat -> 'a cat -> 'a cat =
    fun q1 q2 ->
    match q1, q2 with
    | Shallow d1, Shallow d2 ->
      if too_small d1
      then Shallow (dappendl d1 d2)
      else if too_small d2
      then Shallow (dappendr d1 d2)
      else Deep (d1, lazy empty, d2)
    | Shallow d, Deep (f, m, r) ->
      if too_small d
      then Deep (dappendl d f, m, r)
      else Deep (d, lazy (cons f (Lazy.force m)), r)
    | Deep (f, m, r), Shallow d ->
      if too_small d
      then Deep (f, m, dappendr r d)
      else Deep (f, lazy (snoc (Lazy.force m) r), d)
    | Deep (f1, m1, r1), Deep (f2, m2, r2) ->
      Deep (f1, lazy (snoc (Lazy.force m1) r1 ++ cons f2 (Lazy.force m2)), r2)
  ;;
end

(* Figure 11.4 *)

module type DEQUE_WITH_SIZE = sig
  include DEQUE

  val size : 'a queue -> int
end

module ImplicitCatenableDeque (D : DEQUE_WITH_SIZE) : CATENABLE_DEQUE = struct
  type 'a cat =
    | Shallow of 'a D.queue
    | Deep of
        'a D.queue
        * 'a cmpd_elem cat lazy_t
        * 'a D.queue
        * 'a cmpd_elem cat lazy_t
        * 'a D.queue

  and 'a cmpd_elem =
    | Simple of 'a D.queue
    | Cmpd of 'a D.queue * 'a cmpd_elem cat lazy_t * 'a D.queue

  let empty = Shallow D.empty

  let is_empty = function
    | Shallow d -> D.is_empty d
    | _ -> false
  ;;

  let cons x = function
    | Shallow d -> Shallow (D.cons x d)
    | Deep (f, a, m, b, r) -> Deep (D.cons x f, a, m, b, r)
  ;;

  let snoc q x =
    match q with
    | Shallow d -> Shallow (D.snoc d x)
    | Deep (f, a, m, b, r) -> Deep (f, a, m, b, D.snoc r x)
  ;;

  let head = function
    | Shallow d -> D.head d
    | Deep (f, _, _, _, _) -> D.head f
  ;;

  let last = function
    | Shallow d -> D.last d
    | Deep (_, _, _, _, r) -> D.last r
  ;;

  let share f r =
    let m = D.cons (D.last f) (D.cons (D.head r) D.empty) in
    D.init f, m, D.tail r
  ;;

  let rec dappendl d1 d2 =
    if D.is_empty d1 then d2 else dappendl (D.init d1) (D.cons (D.last d1) d2)
  ;;

  let rec dappendr d1 d2 =
    if D.is_empty d2 then d1 else dappendr (D.snoc d1 (D.head d2)) (D.tail d2)
  ;;

  let ( ++ ) : 'a. 'a cat -> 'a cat -> 'a cat =
    fun q1 q2 ->
    match q1, q2 with
    | Shallow d1, Shallow d2 ->
      if D.size d1 < 4
      then Shallow (dappendl d1 d2)
      else if D.size d2 < 4
      then Shallow (dappendr d1 d2)
      else (
        let f, m, r = share d1 d2 in
        Deep (f, lazy empty, m, lazy empty, r))
    | Shallow d, Deep (f, a, m, b, r) ->
      if D.size d < 4
      then Deep (dappendl d f, a, m, b, r)
      else Deep (d, lazy (cons (Simple f) (Lazy.force a)), m, b, r)
    | Deep (f, a, m, b, r), Shallow d ->
      if D.size d < 4
      then Deep (f, a, m, b, dappendr r d)
      else Deep (f, a, m, lazy (snoc (Lazy.force b) (Simple r)), d)
    | Deep (f1, a1, m1, b1, r1), Deep (f2, a2, m2, b2, r2) ->
      let r1', m, f2' = share r1 f2 in
      let a1' = lazy (snoc (Lazy.force a1) (Cmpd (m1, b1, r1'))) in
      let b2' = lazy (cons (Cmpd (f2', a2, m2)) (Lazy.force b2)) in
      Deep (f1, a1', m, b2', r2)
  ;;

  let replace_head x = function
    | Shallow d -> Shallow (D.cons x (D.tail d))
    | Deep (f, a, m, b, r) -> Deep (D.cons x (D.tail f), a, m, b, r)
  ;;

  let rec tail : 'a. 'a cat -> 'a cat = function
    | Shallow d -> Shallow (D.tail d)
    | Deep (f, a, m, b, r) ->
      if D.size f > 3
      then Deep (D.tail f, a, m, b, r)
      else if not (is_empty (Lazy.force a))
      then (
        match head (Lazy.force a) with
        | Simple d ->
          let f' = dappendl (D.tail f) d in
          Deep (f', lazy (tail (Lazy.force a)), m, b, r)
        | Cmpd (f', c', r') ->
          let f'' = dappendl (D.tail f) f' in
          let a'' = lazy (Lazy.force c' ++ replace_head (Simple r') (Lazy.force a)) in
          Deep (f'', a'', m, b, r))
      else if not (is_empty (Lazy.force b))
      then (
        match head (Lazy.force b) with
        | Simple d ->
          let f' = dappendl (D.tail f) m in
          Deep (f', lazy empty, d, lazy (tail (Lazy.force b)), r)
        | Cmpd (f', c', r') ->
          let f'' = dappendl (D.tail f) m in
          let a'' = lazy (cons (Simple f') (Lazy.force c')) in
          Deep (f'', a'', r', lazy (tail (Lazy.force b)), r))
      else Shallow (dappendl (D.tail f) m) ++ Shallow r
  ;;

  let replace_last x = function
    | Shallow d -> Shallow (D.snoc (D.init d) x)
    | Deep (f, a, m, b, r) -> Deep (f, a, m, b, D.snoc (D.init r) x)
  ;;

  let rec init : 'a. 'a cat -> 'a cat = function
    | Shallow d -> Shallow (D.init d)
    | Deep (f, a, m, b, r) ->
      if D.size r > 3
      then Deep (f, a, m, b, D.init r)
      else if not (is_empty (Lazy.force b))
      then (
        match last (Lazy.force b) with
        | Simple d ->
          let r' = dappendr d (D.init r) in
          Deep (f, a, m, lazy (init (Lazy.force b)), r')
        | Cmpd (f', c', r') ->
          let r'' = dappendr r' (D.init r) in
          let b'' = lazy (replace_last (Simple f') (Lazy.force b) ++ Lazy.force c') in
          Deep (f, a, m, b'', r''))
      else if not (is_empty (Lazy.force a))
      then (
        match last (Lazy.force a) with
        | Simple d ->
          let r' = dappendr m (D.init r) in
          Deep (f, lazy (init (Lazy.force a)), d, lazy empty, r')
        | Cmpd (f', c', r') ->
          let r'' = dappendr m (D.init r) in
          let b'' = lazy (snoc (Lazy.force c') (Simple r')) in
          Deep (f, lazy (init (Lazy.force a)), f', b'', r''))
      else Shallow f ++ Shallow (dappendr m (D.init r))
  ;;
end
