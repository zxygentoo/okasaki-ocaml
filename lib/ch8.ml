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
        { k : int
        ; f : 'a list
        ; f' : 'a list
        ; r : 'a list
        ; r' : 'a list
        }
    (* Append *)
    | A of
        { k : int
        ; f' : 'a list
        ; r' : 'a list
        }
    (* Done *)
    | D of 'a list

  type 'a queue =
    { lenf : int
    ; f : 'a list
    ; state : 'a rotation_state
    ; lenr : int
    ; r : 'a list
    }

  let invalidate = function
    | R st -> R { st with k = st.k - 1 }
    | A { k = 0; r' = _ :: r' } -> D r'
    | A st -> A { st with k = st.k - 1 }
    | st -> st
  ;;

  let exec = function
    | R ({ f = x :: xs; r = y :: ys } as st) ->
      R { k = st.k + 1; f = xs; f' = x :: st.f'; r = ys; r' = y :: st.r' }
    | R ({ f = []; r = [ y ] } as st) -> A { k = st.k; f' = st.f'; r' = y :: st.r' }
    | A { k = 0; r' } -> D r'
    | A ({ f' = x :: xs } as st) -> A { k = st.k - 1; f' = xs; r' = x :: st.r' }
    | st -> st
  ;;

  let exec2 q =
    match exec (exec q.state) with
    | D newf -> { q with f = newf; state = I }
    | newstate -> { q with state = newstate }
  ;;

  let check ({ lenf; f; lenr; r } as q) =
    if lenr <= lenf
    then exec2 q
    else
      exec2
        { lenf = lenf + lenr
        ; f
        ; state = R { k = 0; f; f' = []; r; r' = [] }
        ; lenr = 0
        ; r = []
        }
  ;;

  let empty = { lenf = 0; f = []; state = I; lenr = 0; r = [] }
  let is_empty q = q.lenf = 0
  let snoc q x = check { q with lenr = q.lenr + 1; r = x :: q.r }

  let head q =
    match q.f with
    | [] -> raise (Failure "head: empty queue")
    | x :: _ -> x
  ;;

  let tail q =
    match q.f with
    | [] -> raise (Failure "tail: empty queue")
    | _ :: f -> check { q with lenf = q.lenf - 1; f; state = invalidate q.state }
  ;;
end
