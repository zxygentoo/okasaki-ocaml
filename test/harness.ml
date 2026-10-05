(* The checks every test_chN.ml is written in, on top of Alcotest.

   A check that holds logs its name: Alcotest writes an ASSERT line to the case's log, and
   on a failure the tail of that log shows how far the case got. A check that does not
   hold fails the case there and then, so nothing after it in the case runs. Cost checks
   lean on that. They come after the contract they depend on, in the same case, and need
   no guard of their own: on an implementation that has lost its contract the case is over
   before a cost check can hang or exhaust memory on it. An exception nobody expected ends
   the case the same way.

   A failure goes through Alcotest.fail and not through Alcotest.check, which would report
   a line of this file as the place the check was made. *)

let pass name = Alcotest.(check pass) name () ()
let check name cond = if cond then pass name else Alcotest.fail name

let check_eq name ~expect ~actual to_string =
  if expect = actual
  then pass name
  else Alcotest.failf "%s: expected %s, got %s" name (to_string expect) (to_string actual)
;;

let check_int name ~expect ~actual = check_eq name ~expect ~actual string_of_int

(* [f] must raise exactly [expected]. *)
let check_raises name expected f =
  let wanted = Printexc.to_string expected in
  match f () with
  | _ -> Alcotest.failf "%s: expected %s, got no exception" name wanted
  | exception e when e = expected -> pass name
  | exception e ->
    Alcotest.failf "%s: expected %s, got %s" name wanted (Printexc.to_string e)
;;

(* [f] must raise Failure [msg]. *)
let check_failure name msg f = check_raises name (Failure msg) f

(* [f] must refuse with a Failure, whatever it says after [prefix]: for refusals whose
   wording the implementation is free to choose. *)
let refuses ~prefix name f =
  match f () with
  | _ -> Alcotest.failf "%s: expected Failure \"%s ...\", got no exception" name prefix
  | exception Failure m when String.starts_with ~prefix m -> pass name
  | exception e ->
    Alcotest.failf
      "%s: expected Failure \"%s ...\", got %s"
      name
      prefix
      (Printexc.to_string e)
;;

(* A loop of checks as one check: [f] calls [note] on every failure, and the first is the
   one reported, with the count. *)
let all_of name f =
  let first = ref None
  and count = ref 0 in
  let note why =
    incr count;
    if !first = None then first := Some why
  in
  (try f note with
   | e -> note ("raised " ^ Printexc.to_string e));
  check
    (match !first with
     | None -> name
     | Some why -> Printf.sprintf "%s -- %d wrong, the first: %s" name !count why)
    (!first = None)
;;

(* For a check that sweeps many cases and keeps the offenders, newest first: say which
   came first. *)
let first_of describe = function
  | [] -> ""
  | bad -> " -- " ^ describe (List.nth bad (List.length bad - 1))
;;

let string_of_int_list l = "[" ^ String.concat ";" (List.map string_of_int l) ^ "]"

(* One Alcotest case. *)
let case name f = Alcotest.test_case name `Quick f

(* ------------------------------------------------------------- instruments *)

(* What the checks measure with, the same in every chapter. *)

let upto n = List.init n Fun.id

(* Sets are built from even numbers so that every odd number is a gap to probe. *)
let evens n = List.init n (fun i -> 2 * i)

let shuffle seed xs =
  Random.init seed;
  List.map snd (List.sort compare (List.map (fun x -> Random.bits (), x) xs))
;;

let log2 n = log (float_of_int n) /. log 2.

(* floor (log2 n), for n >= 1. *)
let floor_log2 n =
  let rec go acc n = if n <= 1 then acc else go (acc + 1) (n / 2) in
  go 0 n
;;

let popcount n =
  let rec go acc n = if n = 0 then acc else go (acc + (n land 1)) (n lsr 1) in
  go 0 n
;;

(* An insert links once per trailing 1 bit: the carry chain of a binary increment, stopped
   by the first hole. *)
let trailing_ones n =
  let rec go acc n = if n land 1 = 0 then acc else go (acc + 1) (n lsr 1) in
  go 0 n
;;

(* head/tail to exhaustion. A structure whose tail does not advance would never come to an
   end, and neither would the list this builds, so a drain past any size used here gives
   up and raises, and the case it is in ends there as the failure it is. *)
let drain_limit = 100_000

let drain_with ~is_empty ~head ~tail q =
  let rec go n acc q =
    if is_empty q
    then List.rev acc
    else if n = drain_limit
    then failwith "drain: no end in sight"
    else go (n + 1) (head q :: acc) (tail q)
  in
  go 0 [] q
;;

(* A clock is read before and after a run, and the difference is what the run cost. Words
   are allocation, counted by Gc.minor_words, which counts words allocated rather than
   words retained. Sys.opaque_identity stops the optimiser discarding a result and with it
   the allocation being measured. A clock counts in integers: a float reading would box,
   and the two words of the box would land inside the measurement. *)
let words () = int_of_float (Gc.minor_words ())

let cost_on clock f =
  let before = clock () in
  let r = Sys.opaque_identity (f ()) in
  r, float_of_int (clock () - before)
;;

let cost f = cost_on words f

(* Words allocated by [f]. *)
let allocated f = snd (cost f)

(* An element type that counts its comparisons. *)
let comparisons = ref 0

(* Comparisons that answered true. A search tree's [member] spends one comparison to step
   left (lt x y is true) and two to step right (lt x y false, then lt y x true), so a raw
   comparison count conflates depth with direction. Counting only the true answers gives
   exactly one per step, whichever way the search turned. *)
let steps = ref 0

module Counting_int = struct
  type t = int

  let eq a b =
    incr comparisons;
    a = b
  ;;

  let lt a b =
    incr comparisons;
    let less = a < b in
    if less then incr steps;
    less
  ;;

  let leq a b =
    incr comparisons;
    a <= b
  ;;
end

(* The result of [f], with the comparisons it performed. *)
let count f =
  comparisons := 0;
  let r = f () in
  r, !comparisons
;;

let count_only f = snd (count f)

(* The result of [f], with the comparisons and the words it spent. *)
let spent f =
  comparisons := 0;
  let r, w = cost f in
  r, (float_of_int !comparisons, w)
;;

let spent_only f = snd (spent f)

(* Figure 4.1's streams, with every step counted: one per cell of the first stream that ++
   copies, one per cell that reverse moves, one per cell take copies or drop skips. They
   instrument a queue's rotation policy and nothing else: the streams themselves are
   test_ch4's business. *)
module Counting_stream = struct
  type 'a stream_cell =
    | Nil
    | Cons of 'a * 'a stream

  and 'a stream = 'a stream_cell lazy_t

  let steps = ref 0

  let rec ( ++ ) s1 s2 =
    lazy
      (match s1 with
       | (lazy Nil) -> Lazy.force s2
       | (lazy (Cons (x, s))) ->
         incr steps;
         Cons (x, s ++ s2))
  ;;

  let rec take n s =
    lazy
      (match n, s with
       | 0, _ | _, (lazy Nil) -> Nil
       | _, (lazy (Cons (x, s'))) ->
         incr steps;
         Cons (x, take (n - 1) s'))
  ;;

  let drop n s =
    let rec aux n (lazy c) =
      match n, c with
      | 0, _ -> c
      | _, Nil -> Nil
      | _, Cons (_, s') ->
        incr steps;
        aux (n - 1) s'
    in
    lazy (aux n s)
  ;;

  let reverse s =
    let rec aux lhs rhs =
      match lhs with
      | (lazy Nil) -> rhs
      | (lazy (Cons (x, s))) ->
        incr steps;
        aux s (Cons (x, lazy rhs))
    in
    lazy (aux s Nil)
  ;;
end

let stream_steps () = !Counting_stream.steps
