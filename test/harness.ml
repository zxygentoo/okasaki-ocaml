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

(* ------------------------------------------------------------- properties *)

(* What [agrees] raises: the property does not hold, for the reason given. *)
exception Disagrees of string

(* A property as one check: [prop] must hold on [count] inputs drawn from [arb]. The seed
   fixes the inputs, so every run draws the same ones. When an input fails, QCheck shrinks
   it to a smaller one that still fails, and that is the one the check reports, printed by
   [arb]'s printer, with what [agrees] said about it. A property that raises fails the same
   way, saying what it raised. That is said and not left to QCheck, which on an exception
   met while shrinking stops and reports the input it started from as the one that
   raised.

   The inputs are QCheck's arbitraries and not QCheck2's generators. An input here is
   mostly a workload, a list of operations. QCheck2 shrinks a list of bounded length only
   to a prefix of it, so the operations that do not matter stay in the counterexample;
   QCheck drops elements before the end too, and takes a shrinker of our own, which
   [run_of] below gives it. *)
let check_prop ~count ~seed name arb prop =
  let law x =
    match prop x with
    | holds -> holds
    | exception Disagrees why -> QCheck.Test.fail_report why
    | exception e -> QCheck.Test.fail_reportf "raised %s" (Printexc.to_string e)
  in
  let cell = QCheck.Test.make_cell ~count ~name arb law in
  let shown (c : _ QCheck.TestResult.counter_ex) =
    let input = QCheck.Test.print_instance cell c.instance in
    String.concat
      "; "
      ((if c.shrink_steps > 0
        then Printf.sprintf "%s (shrunk in %d steps)" input c.shrink_steps
        else input)
       :: c.msg_l)
  in
  match
    QCheck.TestResult.get_state
      (QCheck.Test.check_cell ~rand:(Random.State.make [| seed |]) cell)
  with
  | Success -> pass name
  | Failed { instances = c :: _ } -> Alcotest.failf "%s -- fails on %s" name (shown c)
  | Failed_other { msg } -> Alcotest.failf "%s -- %s" name msg
  (* Neither comes about: QCheck records the input that failed, and [law] raises nothing
     but its failures. *)
  | Failed { instances = [] } | Error _ -> Alcotest.failf "%s -- fails" name
;;

(* Shrinking a run. First its prefixes, shortest first, which cut it off where it first
   fails: every one of them for a short run, and for a long one the half, three quarters
   and so on, which comes near in a few steps. Then the run with stretches of it dropped,
   halves first: at every position for a short run, which takes out a pair of operations
   that only fail together, and at a few for a long one. Last, for a short run, one
   operation dropped at a time. QCheck's own list shrinker halves a list and shrinks only
   the front half, so it can neither cut a run short of its end nor drop an operation from
   the back half. *)
let shrink_run ops yield =
  let n = List.length ops in
  let short = n <= 128 in
  let without i c = List.filteri (fun j _ -> j < i || j >= i + c) ops in
  if short
  then
    for k = 0 to n - 1 do
      yield (List.take k ops)
    done
  else (
    let k = ref (n / 2) in
    while !k < n do
      yield (List.take !k ops);
      k := !k + max 1 ((n - !k) / 2)
    done);
  let c = ref (n / 2) in
  while !c >= if short then 2 else max 1 (n / 64) do
    let step = if short then 1 else !c in
    let i = ref 0 in
    while !i + !c <= n do
      yield (without !i !c);
      i := !i + step
    done;
    c := !c / 2
  done;
  if short
  then
    for i = 0 to n - 1 do
      yield (without i 1)
    done
;;

(* A random run: [length] operations drawn from [ops] by weight. What a property runs is
   [plan] of the draw, which drops or adjusts what the model cannot take at that point (a
   removal from nothing, an index past the end), and that is what a counterexample prints,
   each operation by [show]. The draw shrinks by [shrink_run]; the operations themselves
   stay as drawn. *)
let run_of ~length ~plan ~show ops =
  QCheck.make
    ~print:(fun draw -> QCheck.Print.list show (plan draw))
    ~shrink:shrink_run
    QCheck.Gen.(list_size (return length) (oneof_weighted ops))
;;

(* A random trace over versions, for persistence. Version 0 is the empty structure and
   step i makes version i by an operation on versions made before it. A draw is the steps
   with the numbers they were drawn as, and [gen i] draws step i, naming the versions it
   works on by those numbers, all below i. A draw shrinks as a run does; a step dropped
   takes its version with it, and a step that worked on that version works on the one
   drawn before it instead, so that nothing else in the trace moves. [plan] makes the
   trace that is run, and printed, from a draw, most often by [plan_trace]. *)
let trace_of ~length ~plan ~show gen =
  QCheck.make
    ~print:(fun draw ->
      String.concat
        "; "
        (List.mapi (fun i op -> Printf.sprintf "v%d = %s" (i + 1) (show op)) (plan draw)))
    ~shrink:shrink_run
    (fun st -> List.init length (fun i -> i + 1, gen (i + 1) st))
;;

(* The steps of a draw, with the versions they work on numbered as the steps that are
   left make them. [rename f op] is [op] working on version [f v] for each [v] it names. *)
let renumber ~rename draw =
  let kept = Array.of_list (List.map fst draw) in
  (* The new number of the latest step drawn as [v] or before: how many of them are left. *)
  let now v =
    let rec go lo hi =
      if lo = hi
      then lo
      else (
        let mid = (lo + hi) / 2 in
        if kept.(mid) <= v then go (mid + 1) hi else go lo mid)
    in
    go 0 (Array.length kept)
  in
  List.map (fun (_, op) -> rename now op) draw
;;

(* The trace a draw makes, [renumber]ed, with what the model cannot take adjusted, and the
   state of the model at every version, version 0's [start]. Step by step, [admit state op]
   says what [op] becomes and the state of the version it makes, [state v] being that of
   a version made before it. *)
let plan_trace ~rename ~start admit draw =
  let ops = renumber ~rename draw in
  let state = Array.make (List.length ops + 1) start in
  let ops =
    List.mapi
      (fun i op ->
         let op, s = admit (Array.get state) op in
         state.(i + 1) <- s;
         op)
      ops
  in
  ops, state
;;

(* Inside a property, what check_eq is outside one: [expect] and [actual] agree, or the
   property fails on the input at hand, saying how. [what] is a format, followed by its
   arguments, and is only formatted when they do not agree: a property makes thousands of
   these checks, nearly all of which hold. *)
let agrees what =
  Format.kdprintf
    (fun what ~expect ~actual to_string ->
       expect = actual
       || raise
            (Disagrees
               (Format.asprintf
                  "%t: expected %s, got %s"
                  what
                  (to_string expect)
                  (to_string actual))))
    what
;;

(* And what check is: [cond], the last argument, holds, or the property fails, saying
   [what]. *)
let holds what =
  Format.kdprintf
    (fun what cond -> cond || raise (Disagrees (Format.asprintf "%t" what)))
    what
;;

(* member agrees with List.mem, for every query from -2 to [below] + 2, over 300 random
   lists of 1 to [size] elements under [below], a third of them ascending, each made a set
   by [of_list]. The random lists come first: their printer and shrinker serve both. *)
let member_agrees ~seed ~size ~below name of_list member =
  check_prop
    ~count:300
    ~seed
    name
    QCheck.(
      oneof_weighted
        [ 2, list_size Gen.(int_range 1 size) (int_bound (below - 1))
        ; 1, map upto (int_range 1 size)
        ])
    (fun xs ->
       let s = of_list xs in
       List.for_all
         (fun q ->
            agrees
              "member %d"
              q
              ~expect:(List.mem q xs)
              ~actual:(member q s)
              string_of_bool)
         (List.init (below + 5) (fun i -> i - 2)))
;;
