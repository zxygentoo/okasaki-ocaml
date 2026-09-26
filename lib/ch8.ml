(* Exercise 8.1 Extend the red-black trees of Section 3.3 with a delete function using
   these ideas. Add a boolean field to the T constructor and maintain es- timates of the
   numbers of valid and invalid elements in the tree. Assume for the purposes of these
   estimates that every insertion adds a new valid element and that every deletion
   invalidates a previously valid element. Correct the estimates during rebuilding. You
   will find Exercise 3.9 helpful in rebuilding the tree. *)

module type ORDERED = sig
  type t

  val eq : t -> t -> bool
  val lt : t -> t -> bool
  val leq : t -> t -> bool
end

module type SET = sig
  type elem
  type set

  val empty : set
  val member : elem -> set -> bool
  val insert : elem -> set -> set
end

module type SET_WITH_DELETE = sig
  include SET

  val delete : elem -> set -> set
end

module RedBlackSet (Element : ORDERED) : SET_WITH_DELETE with type elem = Element.t =
struct
  type elem = Element.t

  type color =
    | R
    | B

  type tree =
    | E
    | T of (color * tree * (elem * bool) * tree)

  type set = int * int * tree

  let empty = 0, 0, E

  let rec member x (m, n, t) =
    match t with
    | E -> false
    | T (_, a, (y, deleted), b) ->
      if Element.lt x y
      then member x (m, n, a)
      else if Element.lt y x
      then member x (m, n, b)
      else not deleted
  ;;

  let balance = function
    | B, T (R, T (R, a, x, b), y, c), z, d
    | B, T (R, a, x, T (R, b, y, c)), z, d
    | B, a, x, T (R, T (R, b, y, c), z, d)
    | B, a, x, T (R, b, y, T (R, c, z, d)) -> T (R, T (B, a, x, b), y, T (B, c, z, d))
    | body -> T body
  ;;

  let insert x (m, n, s) =
    let rec ins = function
      | E -> T (R, E, (x, false), E)
      | T (color, a, ((y, _) as elem), b) ->
        if Element.lt x y
        then balance (color, ins a, elem, b)
        else if Element.lt y x
        then balance (color, a, elem, ins b)
        else T (color, a, (y, false), b)
    in
    let[@ocaml.warning "-partial-match"] (T (_, a, elem, b)) = ins s in
    m + 1, n, T (B, a, elem, b)
  ;;

  let from_ord_list xs =
    let bit_length x =
      let rec go acc x = if x = 0 then acc else go (acc + 1) (x lsr 1) in
      go 0 x
    in
    let rec build xs c = function
      | 0 -> E, xs
      | n ->
        let next_c = c / 2 in
        let lhs, xs_lhs = build xs next_c (n / 2) in
        (match xs_lhs with
         | [] -> raise (Failure "from_ord_list: invalid length")
         | x :: xs ->
           let rhs, xs_rhs = build xs next_c ((n - 1) / 2) in
           T ((if c = 0 then R else B), lhs, x, rhs), xs_rhs)
    in
    let n = List.length xs in
    let cores = (1 lsl bit_length (n lsr 1)) - 1 in
    let tree =
      match build xs cores n with
      | T (_, E, x, E), _ -> T (B, E, x, E)
      | s, _ -> s
    in
    n, 0, tree
  ;;

  let rebuild t =
    let rec walk acc = function
      | E -> acc
      | T (_, a, (_, true), b) -> walk (walk acc b) a
      | T (_, a, ((_, false) as elem), b) -> walk (elem :: walk acc b) a
    in
    walk [] t |> from_ord_list
  ;;

  let delete x (m, n, s) =
    let rec del = function
      | E -> E
      | T (color, a, ((y, _) as elem), b) ->
        if Element.lt x y
        then T (color, del a, elem, b)
        else if Element.lt y x
        then T (color, a, elem, del b)
        else T (color, a, (y, true), b)
    in
    let t = del s in
    if n >= m / 2 then rebuild t else m, n + 1, t
  ;;
end

module type QUEUE = sig
  type 'a queue

  val empty : 'a queue
  val is_empty : 'a queue -> bool
  val snoc : 'a queue -> 'a -> 'a queue
  val head : 'a queue -> 'a
  val tail : 'a queue -> 'a queue
end

module HoodMelvilleQueue = struct
  type 'a rotation_state =
    (* Idle *)
    | I
    (* Reversing *)
    | R of
        { k : int (* valid element count *)
        ; f : 'a list
        ; f' : 'a list
        ; r : 'a list
        ; r' : 'a list
        }
    (* Append *)
    | A of
        { k : int (* valid element count *)
        ; f' : 'a list
        ; r' : 'a list
        }
    (* Done *)
    | D of 'a list

  (* Exercise 8.3 Replace the lent and lenr fields with a single diff field that maintains
     the difference between the lengths of f and r. diff may be inaccurate during
     rebuilding, but must be accurate by the time rebuilding is finished. *)

  type 'a queue =
    { f : 'a list
    ; r : 'a list
    ; state : 'a rotation_state
    ; diff : int
    }

  let invalidate = function
    | R st -> R { st with k = st.k - 1 }
    | A { k = 0; r' = _ :: r' } -> D r'
    | A st -> A { st with k = st.k - 1 }
    | st -> st
  ;;

  let step (st, d) =
    match st with
    | R ({ f = x :: xs; r = y :: ys } as st) ->
      R { k = st.k + 1; f = xs; f' = x :: st.f'; r = ys; r' = y :: st.r' }, d + 2
    | R ({ f = []; r = [ y ] } as st) ->
      A { k = st.k; f' = st.f'; r' = y :: st.r' }, d + 1
    | A { k = 0; r' } -> D r', d
    | A ({ f' = x :: xs } as st) -> A { k = st.k - 1; f' = xs; r' = x :: st.r' }, d
    | _ -> st, d
  ;;

  (* Exercise 8.2 Prove that calling exec twice at the beginning of each rotation, and
     once for every remaining insertion or deletion is enough to finish the rotation on
     time. Modify the code accordingly. *)

  let commit q = function
    | D newf, d -> { q with f = newf; state = I; diff = d }
    | newstate, d -> { q with state = newstate; diff = d }
  ;;

  let step_up q = (q.state, q.diff) |> step |> commit q

  let start_rebuild { f; r } =
    let q = { f; r = []; state = R { k = 0; f; f' = []; r; r' = [] }; diff = -1 } in
    (q.state, 0) |> step |> step |> commit q
  ;;

  let check q = if q.diff >= 0 then step_up q else start_rebuild q
  let empty = { f = []; r = []; state = I; diff = 0 }
  let is_empty q = q.f = []
  let snoc q x = check { q with r = x :: q.r; diff = q.diff - 1 }

  let head q =
    match q.f with
    | [] -> raise (Failure "head: empty queue")
    | x :: _ -> x
  ;;

  let tail q =
    match q.f with
    | [] -> raise (Failure "tail: empty queue")
    | _ :: f -> check { q with f; state = invalidate q.state; diff = q.diff - 1 }
  ;;
end

module type DEQUE = sig
  include QUEUE

  val cons : 'a -> 'a queue -> 'a queue
  val last : 'a queue -> 'a
  val init : 'a queue -> 'a queue
end

(* Exercise 8.4 Unfortunately, we cannot extend Hood and Melville's real-time queues with
   a cons function quite so easily, because there is no easy way to insert the new element
   into the rotation state. Instead, write a functor that extends any implementation of
   queues with a constant-time cons function, using the type

   type a Queue = a list x a Q.Queue

   where Q is the parameter to the functor, cons should insert elements into the new list,
   and head and tail should remove elements from the new list whenever it is non-empty.
*)

module type QUEUE_WITH_CONS = sig
  include QUEUE

  val cons : 'a -> 'a queue -> 'a queue
end

module ConstantTimeConsQueue (Q : QUEUE) : QUEUE_WITH_CONS = struct
  type 'a queue = 'a list * 'a Q.queue

  let empty = [], Q.empty

  let is_empty (xs, q) =
    match xs with
    | [] -> Q.is_empty q
    | _ -> false
  ;;

  let snoc (xs, q) x = xs, Q.snoc q x
  let cons x (xs, q) = x :: xs, q

  let head (xs, q) =
    match xs with
    | [] -> Q.head q
    | x :: _ -> x
  ;;

  let tail (xs, q) =
    match xs with
    | [] -> [], Q.tail q
    | _ :: xs' -> xs', q
  ;;
end
