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

module type STREAM_WITH_SORT = sig
  include STREAM

  val sort : ('a -> 'a -> int) -> 'a stream -> 'a stream
end

module Stream : STREAM_WITH_SORT = struct
  type 'a stream_cell =
    | Nil
    | Cons of 'a * 'a stream

  and 'a stream = 'a stream_cell lazy_t

  let rec ( ++ ) s1 s2 =
    lazy
      (match s1 with
       | (lazy Nil) -> Lazy.force s2
       | (lazy (Cons (x, s))) -> Cons (x, s ++ s2))
  ;;

  let rec take n s =
    lazy
      (match n, s with
       | 0, _ -> Nil
       | _, (lazy Nil) -> Nil
       | _, (lazy (Cons (x, s'))) -> Cons (x, take (n - 1) s'))
  ;;

  let drop n s =
    let rec aux x (lazy r) =
      match x, r with
      | 0, _ -> r
      | _, Nil -> Nil
      | _, Cons (_, s') -> aux (x - 1) s'
    in
    lazy (aux n s)
  ;;

  let reverse s =
    let rec aux lhs rhs =
      match lhs with
      | (lazy Nil) -> rhs
      | (lazy (Cons (c, s))) -> aux s (Cons (c, lazy rhs))
    in
    lazy (aux s Nil)
  ;;

  (* Exercise 4.2 Implement insertion sort on streams. Show that extracting the first k
     elements of sort xs takes only O(n·k) time, where n is the length of xs, rather than
     O(n²) time, as might be expected of insertion sort. *)

  let sort cmp s =
    let rec insert x = function
      | (lazy Nil) -> Cons (x, lazy Nil)
      | (lazy (Cons (y, r))) as m ->
        if cmp x y <= 0 then Cons (x, m) else Cons (y, lazy (insert x r))
    in
    let rec aux = function
      | (lazy Nil) -> Nil
      | (lazy (Cons (x, xs))) -> insert x (lazy (aux xs))
    in
    lazy (aux s)
  ;;
end
