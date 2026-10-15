module type QUEUE = sig
  type 'a queue

  val empty : 'a queue
  val is_empty : 'a queue -> bool
  val snoc : 'a queue -> 'a -> 'a queue
  val head : 'a queue -> 'a
  val tail : 'a queue -> 'a queue
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
    match q, y with
    | Shallow Zero, _ -> Shallow (One y)
    | Shallow (One x), _ -> Deep (Two (x, y), lazy empty, Zero)
    | Deep (f, m, Zero), _ -> Deep (f, m, One y)
    | Deep (f, m, One x), _ -> Deep (f, lazy (snoc (Lazy.force m) (x, y)), Zero)
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
