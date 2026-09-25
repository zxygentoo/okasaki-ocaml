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
