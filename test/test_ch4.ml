(* Tests for Chapter 4, section 4.2: the streams package of Figure 4.1, and the insertion
   sort of Exercise 4.2. Plain OCaml, no test framework, matching test_ch2.ml and
   test_ch3.ml.

   A stream function can return every element correctly and still be wrong, because what
   section 4.2 specifies is not only WHAT each function computes but WHEN. All four are
   `fun lazy`, so applying one does no work at all; ++ and take are incremental, so each
   cell of the result costs one cell of the input; drop and reverse are monolithic, so the
   first cell of the result pays for everything. Comparing results against a list oracle
   sees none of that. A Stream that forces its arguments on application passes every
   equality test here and breaks the amortised bounds of every structure in chapter 6.

   So the instrument is a stream that reports being looked at. [source] builds a stream
   whose cells bump a counter as they are computed. Suspensions are memoised, so each cell
   reports once however often it is forced, and the counter reads as "distinct cells of
   the input opened so far", the final Nil included. Every claim in the section turns into
   an exact count, taken at a chosen moment: straight after the call, after forcing k
   cells of the result, after walking all of it.

   The second instrument is a poisoned stream, which raises Opened instead of yielding a
   cell. Where a counter says how much was opened, poison says that a particular cell was
   never touched at all: [take 0] owes that to its argument, and [s ++ t] owes it to t for
   as long as s lasts.

   STREAM exposes its representation on purpose (p.36: "we deliberately expose the
   internal representation in order to support pattern matching on streams"), so the tests
   build and take apart streams directly and never use one function under test to observe
   another.

   Exercise 4.2 states its cost as time, and the only thing an insertion sort does that
   grows with its input is compare, so there the unit is comparisons, counted with an
   instrumented comparator as test_ch3 counts them with an instrumented ORDERED.

   Not asserted, because it cannot fail: memoisation. The signature fixes a stream as a
   lazy_t, and the runtime memoises those, so no implementation of STREAM can recompute a
   cell. *)

open Okasaki.Ch4
open Stream

(* ------------------------------------------------------------------ harness *)

let checks = ref 0
let failures = ref 0

let check name cond =
  incr checks;
  if not cond
  then (
    incr failures;
    Printf.printf "  FAIL  %s\n" name)
;;

let check_eq name ~expect ~actual to_string =
  incr checks;
  if expect <> actual
  then (
    incr failures;
    Printf.printf
      "  FAIL  %s: expected %s, got %s\n"
      name
      (to_string expect)
      (to_string actual))
;;

let check_int name ~expect ~actual = check_eq name ~expect ~actual string_of_int

let check_raises name expected f =
  incr checks;
  match f () with
  | _ ->
    incr failures;
    Printf.printf
      "  FAIL  %s: expected %s, got no exception\n"
      name
      (Printexc.to_string expected)
  | exception e ->
    if e <> expected
    then (
      incr failures;
      Printf.printf
        "  FAIL  %s: expected %s, got %s\n"
        name
        (Printexc.to_string expected)
        (Printexc.to_string e))
;;

let section name = Printf.printf "%s\n" name
let string_of_int_list l = "[" ^ String.concat ";" (List.map string_of_int l) ^ "]"

(* Words allocated by [f]. Sys.opaque_identity stops the optimiser discarding the result
   and with it the allocation we are trying to measure. *)
let words f =
  let before = Gc.minor_words () in
  ignore (Sys.opaque_identity (f ()));
  Gc.minor_words () -. before
;;

(* -------------------------------------------------------------- instruments *)

(* [xs] as a stream, ending in [last]. Every cell is already a value, so forcing one
   computes nothing and allocates nothing: whatever a measurement sees is the function
   under test and not its input. *)
let stream_ending last xs =
  List.fold_right (fun x s -> Lazy.from_val (Cons (x, s))) xs last
;;

let of_list xs = stream_ending (Lazy.from_val Nil) xs
let upto n = List.init n Fun.id

(* The counter. A stream over [xs] whose cells report to [opened] as they are computed --
   once each, since a suspension runs once -- so [!opened] is the number of distinct cells
   anything has looked at so far, the final Nil included. *)
let source xs =
  let opened = ref 0 in
  let rec from xs =
    lazy
      (incr opened;
       match xs with
       | [] -> Nil
       | x :: rest -> Cons (x, from rest))
  in
  from xs, opened
;;

(* The poison. [xs], followed by a cell that raises when it is looked at. *)
exception Opened

let poisoned_after xs = stream_ending (lazy (raise Opened)) xs
let poison () = poisoned_after []

(* [check_eq] on a list that can only be computed while the poison stays untouched. Opened
   is then this check's failure and not the section's, so the checks after it still get to
   run. *)
let check_unopened name ~expect actual =
  match actual () with
  | got -> check_eq name ~expect ~actual:got string_of_int_list
  | exception Opened ->
    incr checks;
    incr failures;
    Printf.printf "  FAIL  %s: the poisoned cell was opened\n" name
;;

(* The first [k] elements of [s], forcing exactly [k] cells. This is the consumer's own
   take, so that no check leans on the [take] under test. *)
let rec prefix k s =
  if k = 0
  then []
  else (
    match Lazy.force s with
    | Nil -> []
    | Cons (x, rest) -> x :: prefix (k - 1) rest)
;;

let force_cells k s = ignore (prefix k s)

let to_list s =
  let rec go acc s =
    match Lazy.force s with
    | Nil -> List.rev acc
    | Cons (x, rest) -> go (x :: acc) rest
  in
  go [] s
;;

(* [s] with its first [k] cells walked past. *)
let rec nth_tail k s =
  if k = 0
  then s
  else (
    match Lazy.force s with
    | Nil -> s
    | Cons (_, rest) -> nth_tail (k - 1) rest)
;;

(* The list oracles. *)
let rec list_take n = function
  | x :: xs when n > 0 -> x :: list_take (n - 1) xs
  | _ -> []
;;

let rec list_drop n = function
  | _ :: xs when n > 0 -> list_drop (n - 1) xs
  | l -> l
;;

(* For a check that sweeps many cases and keeps the offenders: say which came first. *)
let first_of describe = function
  | [] -> ""
  | bad -> " -- " ^ describe (List.nth bad (List.length bad - 1))
;;

(* ------------------------------------------------------------------- values *)

let test_values () =
  section "values";
  let l = [ 1; 2; 3; 4; 5 ] in
  let s = of_list l
  and nil = of_list [] in
  let eq name expect actual =
    check_eq name ~expect ~actual:(to_list actual) string_of_int_list
  in
  eq "s ++ t" [ 1; 2; 3; 4; 5; 6; 7 ] (s ++ of_list [ 6; 7 ]);
  eq "[] ++ t" l (nil ++ s);
  eq "s ++ []" l (s ++ nil);
  eq "[] ++ []" [] (nil ++ nil);
  let twice = [ 1; 2; 3; 4; 5; 1; 2; 3; 4; 5; 9 ] in
  eq "(s ++ t) ++ u" twice (s ++ s ++ of_list [ 9 ]);
  eq "s ++ (t ++ u)" twice (s ++ (s ++ of_list [ 9 ]));
  (* take 0 is the clause that is easiest to get wrong and hardest to notice: every other
     take bottoms out in it, so returning the stream there makes take the identity. *)
  eq "take 0" [] (take 0 s);
  eq "take 3" [ 1; 2; 3 ] (take 3 s);
  eq "take exactly the length" l (take 5 s);
  eq "take beyond the length" l (take 9 s);
  eq "take from the empty stream" [] (take 3 nil);
  eq "drop 0" l (drop 0 s);
  eq "drop 3" [ 4; 5 ] (drop 3 s);
  eq "drop exactly the length" [] (drop 5 s);
  eq "drop beyond the length" [] (drop 9 s);
  eq "drop from the empty stream" [] (drop 3 nil);
  eq "reverse" [ 5; 4; 3; 2; 1 ] (reverse s);
  eq "reverse of the empty stream" [] (reverse nil);
  eq "reverse of a singleton" [ 1 ] (reverse (of_list [ 1 ]));
  eq "reverse is an involution" l (reverse (reverse s));
  (* Randomised, against the list functions each one mirrors. *)
  Random.init 20260920;
  let bad_append = ref 0
  and bad_take = ref 0
  and bad_drop = ref 0
  and bad_reverse = ref 0
  and bad_split = ref 0 in
  for _ = 0 to 299 do
    let xs = List.init (Random.int 30) (fun _ -> Random.int 100)
    and ys = List.init (Random.int 30) (fun _ -> Random.int 100)
    and n = Random.int 35 in
    let s = of_list xs
    and t = of_list ys in
    if to_list (s ++ t) <> xs @ ys then incr bad_append;
    if to_list (take n s) <> list_take n xs then incr bad_take;
    if to_list (drop n s) <> list_drop n xs then incr bad_drop;
    if to_list (reverse s) <> List.rev xs then incr bad_reverse;
    if to_list (take n s ++ drop n s) <> xs then incr bad_split
  done;
  check_int "++ agrees with @, 300 random pairs" ~expect:0 ~actual:!bad_append;
  check_int "take agrees with the list take, 300 random cases" ~expect:0 ~actual:!bad_take;
  check_int "drop agrees with the list drop, 300 random cases" ~expect:0 ~actual:!bad_drop;
  check_int
    "reverse agrees with List.rev, 300 random lists"
    ~expect:0
    ~actual:!bad_reverse;
  check_int "take n s ++ drop n s is s, 300 random cases" ~expect:0 ~actual:!bad_split
;;

(* ------------------------------------------ fun lazy: a call does no work *)

(* Every function in Figure 4.1 is `fun lazy`, which p.33 expands to

   fun f x = $case x of p => force e

   The argument arrives as a plain variable and the whole match sits inside the $. So
   applying the function looks at nothing: it wraps the work up and returns. Forcing even
   the first cell of an argument on application is the `plus` that p.33 calls "not the
   function that we probably intended", and it is invisible to every test above.

   This is the property the rest of the book leans on. The banker's queue of chapter 6
   writes `f ++ reverse r` and charges the call O(1), leaving the reversal as a debt to be
   paid off later; a reverse that runs when called makes that accounting false while every
   queue still returns the right elements. *)

let calls : (string * (int stream -> int stream -> int stream)) list =
  [ ("s ++ t", fun s t -> s ++ t)
  ; ("take 0 s", fun s _ -> take 0 s)
  ; ("take 3 s", fun s _ -> take 3 s)
  ; ("drop 0 s", fun s _ -> drop 0 s)
  ; ("drop 3 s", fun s _ -> drop 3 s)
  ; ("reverse s", fun s _ -> reverse s)
  ]
;;

let test_call_is_free () =
  section "fun lazy: applying a function does no work";
  List.iter
    (fun (name, call) ->
      let s, opened_s = source (upto 5)
      and t, opened_t = source (upto 5) in
      ignore (Sys.opaque_identity (call s t));
      check_int
        (Printf.sprintf "%s opens no cell until its result is forced" name)
        ~expect:0
        ~actual:(!opened_s + !opened_t);
      (* The same claim with nowhere to hide: an argument that cannot be looked at. *)
      check
        (Printf.sprintf
           "%s returns a suspension even when its arguments cannot be opened"
           name)
        (match call (poison ()) (poison ()) with
         | _ -> true
         | exception Opened -> false))
    calls
;;

(* ------------------------------------------------- ++ and take: incremental *)

(* "Forcing a stream executes only enough of the computation to produce the outermost cell
   and suspends the rest" (p.34). In counts: k cells of the result cost k cells of the
   input, for every k, and not one more. *)

let test_incremental () =
  section "++ and take are incremental";
  let n = 20 in
  (* s ++ t walks s one cell per cell demanded, and has no business in t until s is
     exhausted. *)
  let bad = ref [] in
  for k = 1 to n do
    let s, opened_s = source (upto n)
    and t, opened_t = source [ 100; 101 ] in
    force_cells k (s ++ t);
    if !opened_s <> k || !opened_t <> 0 then bad := (k, !opened_s, !opened_t) :: !bad
  done;
  check
    (Printf.sprintf
       "k cells of s ++ t open k cells of s and none of t%s"
       (first_of
          (fun (k, a, b) -> Printf.sprintf "k=%d opened %d of s and %d of t" k a b)
          !bad))
    (!bad = []);
  (* Crossing over costs s its Nil and t its first cell, which is the `force t` of the
     first clause; after that t is walked on demand like s was. *)
  let s, opened_s = source (upto n)
  and t, opened_t = source [ 100; 101; 102 ] in
  force_cells (n + 1) (s ++ t);
  check_int "the first cell of t costs s its Nil" ~expect:(n + 1) ~actual:!opened_s;
  check_int "and costs t exactly one cell" ~expect:1 ~actual:!opened_t;
  let r = of_list [ 1; 2; 3 ] ++ poison () in
  check_unopened
    "every element of s can be read while t stays unopened"
    ~expect:[ 1; 2; 3 ]
    (fun () -> prefix 3 r);
  check_raises "and t is opened once s has run out" Opened (fun () -> force_cells 4 r);
  (* take, the same way. *)
  let bad = ref [] in
  for k = 1 to n do
    let s, opened = source (upto (2 * n)) in
    force_cells k (take n s);
    if !opened <> k then bad := (k, !opened) :: !bad
  done;
  check
    (Printf.sprintf
       "k cells of take n s open k cells of s%s"
       (first_of (fun (k, a) -> Printf.sprintf "k=%d opened %d" k a) !bad))
    (!bad = []);
  (* take never looks past what it returns. The clause order of Figure 4.1 is what
     guarantees it: take (0, s) comes first and has no $ on s, so by the time n reaches 0
     the rest of the stream is simply dropped, unopened. Matching on the stream before
     looking at n opens one cell too many -- harmless for a list, but here that cell can
     be a suspended reverse, and then one cell is the whole O(n). *)
  let bad = ref [] in
  List.iter
    (fun m ->
      let s, opened = source (upto n) in
      ignore (to_list (take m s));
      if !opened <> m then bad := (m, !opened) :: !bad)
    [ 0; 1; 2; 5; n - 1 ];
  check
    (Printf.sprintf
       "all of take n s opens n cells of s, never n+1%s"
       (first_of (fun (m, a) -> Printf.sprintf "n=%d opened %d" m a) !bad))
    (!bad = []);
  check_unopened "take 0 never opens its argument" ~expect:[] (fun () ->
    to_list (take 0 (poison ())));
  check_unopened "take n stops short of cell n+1" ~expect:[ 1; 2; 3 ] (fun () ->
    to_list (take 3 (poisoned_after [ 1; 2; 3 ])));
  (* Only when the stream is the shorter of the two does take reach its Nil. *)
  let s, opened = source (upto 5) in
  ignore (to_list (take 9 s));
  check_int "take beyond the length opens the whole stream" ~expect:6 ~actual:!opened
;;

(* ------------------------------------------- drop and reverse: monolithic *)

(* "Calculating the first cell of the result requires executing the entire function"
   (p.35). Monolithic is a statement about what happens once the result is forced, not
   about the call, which test_call_is_free has already pinned at zero: `fun lazy` is used
   here "to delay the initial call to drop' rather than to delay pattern matching". *)

let test_monolithic () =
  section "drop and reverse are monolithic";
  (* The first cell of drop n s pays for the whole skip: min n |s| cells to walk past,
     plus the one it hands back. *)
  let bad = ref [] in
  List.iter
    (fun (n, len) ->
      let s, opened = source (upto len) in
      force_cells 1 (drop n s);
      let expect = min n len + 1 in
      if !opened <> expect then bad := (n, len, !opened, expect) :: !bad)
    [ 0, 5; 1, 5; 3, 5; 5, 5; 9, 5; 0, 0; 3, 0; 100, 1000; 1000, 100 ];
  check
    (Printf.sprintf
       "the first cell of drop n s opens min n |s| + 1 cells%s"
       (first_of
          (fun (n, len, a, e) ->
            Printf.sprintf "drop %d of %d opened %d, expected %d" n len a e)
          !bad))
    (!bad = []);
  (* drop' (0, s) = s: what comes back is the suffix of s itself, the very same cells, not
     a copy of them. *)
  let s = of_list (upto 10) in
  check
    "drop n s is the suffix of s itself, not a copy"
    (Lazy.force (drop 4 s) == Lazy.force (nth_tail 4 s));
  (* reverse cannot produce its first element without having seen the last. *)
  let bad_first = ref []
  and bad_rest = ref [] in
  List.iter
    (fun len ->
      let s, opened = source (upto len) in
      let r = reverse s in
      force_cells 1 r;
      if !opened <> len + 1 then bad_first := (len, !opened) :: !bad_first;
      (* ... and having paid, owes nothing more. What is left of the result is the `$Cons
         (x, r)` cells of reverse', which p.35 calls trivial: no function application
         inside, so nothing of the input left to look at. *)
      let got = to_list r in
      if !opened <> len + 1 || got <> List.rev (upto len)
      then bad_rest := (len, !opened) :: !bad_rest)
    [ 0; 1; 2; 5; 100; 1000 ];
  check
    (Printf.sprintf
       "the first cell of reverse s opens all of s%s"
       (first_of
          (fun (len, a) -> Printf.sprintf "|s|=%d opened %d, expected %d" len a (len + 1))
          !bad_first))
    (!bad_first = []);
  check
    (Printf.sprintf
       "the rest of reverse s is already paid for%s"
       (first_of
          (fun (len, a) -> Printf.sprintf "|s|=%d ended at %d opened" len a)
          !bad_rest))
    (!bad_rest = [])
;;

(* --------------------------------------------------------------------- cost *)

(* PERFORMANCE. The counters above say how much of the INPUT a function looks at; they
   cannot see work the function makes for itself. Two statements in section 4.2 are of
   that kind, so they are asserted as allocation, over inputs that are already values.

   drop: p.35 gives drop twice, the second time "more efficiently". The first suspends
   every recursive call only to force it at once, so skipping n cells builds n
   suspensions; drop' is a plain loop under a single suspension and builds none. Exercise
   4.1 shows the two agree on every result, which is exactly why only a cost check can
   tell them apart.

   reverse: linear, over the WHOLE result. The tempting one-liner over ++ (reverse the
   tail, append the head) opens the same |s| + 1 cells, returns the same elements, and
   even produces its first cell in O(n). The rest is where it hides the bill: every later
   cell has to come up through a tower of suspended appends, O(n) each, O(n^2) in all. So
   the measurement walks the result to the end rather than stopping at the first cell --
   which is also the honest reading of "monolithic": once reverse has been forced there
   should be nothing expensive left in it. *)

(* Force every cell of [s]. Builds nothing, so [words] sees only what the stream does. *)
let rec walk s =
  match Lazy.force s with
  | Nil -> ()
  | Cons (_, rest) -> walk rest
;;

let test_cost () =
  section "cost";
  (* Guard against a vacuous check: if the probe cannot see allocation at all, everything
     below passes for the wrong reason. Building a stream certainly allocates. *)
  let probe = words (fun () -> of_list (upto 64)) in
  check
    (Printf.sprintf
       "the allocation probe registers work (building a stream costs %.0f words)"
       probe)
    (probe > 0.0);
  let drop_cost n =
    let r = drop n (of_list (upto (n + 1))) in
    words (fun () -> Lazy.force r)
  in
  let small = drop_cost 10
  and large = drop_cost 100_000 in
  check
    (Printf.sprintf
       "forcing drop n s allocates O(1), whatever n is (%.0f words at n=10, %.0f at \
        n=100000)"
       small
       large)
    (large <= small +. 4.0);
  let reverse_cost n =
    let r = reverse (of_list (upto n)) in
    words (fun () -> walk r) /. float_of_int n
  in
  let small = reverse_cost 500
  and large = reverse_cost 4000 in
  check
    (Printf.sprintf
       "all of reverse s allocates O(1) per element (%.1f words at n=500, %.1f at n=4000)"
       small
       large)
    (Float.abs (small -. large) < 0.5)
;;

(* ----------------------------------------------- Exercise 4.2: insertion sort *)

(* "Show that extracting the first k elements of sort xs takes only O(n·k) time, where n
   is the length of xs, rather than O(n²) time, as might be expected of insertion sort."

   The showing is the exercise and is left where it belongs. What a test can do is hold
   the implementation to the claim, and the claim is sharp enough to check as stated: walk
   the result, and after every cell -- every k from 1 to n, not a sample of them -- the
   comparisons spent so far must be within n·k. The constant is 1 on purpose: the
   comparator is three-way, so one call settles where an element goes, and an insert that
   asks twice fails here at double the bound.

   A strict insertion sort fails that at k = 1, since it finishes all O(n²) of its work
   before it can return anything. So does any sort that merely hides a strict one inside a
   suspension, which is why "the call is free" is necessary here but nowhere near enough. *)

let comparisons = ref 0

let counting_compare a b =
  incr comparisons;
  compare a b
;;

(* Input orders that push an insertion sort in different directions. Which of ascending
   and descending is the expensive one depends on the direction the inserts are folded in,
   so both are here and no check below cares which is which. *)
let sort_orders n =
  Random.init 20260920;
  let random = List.init n (fun _ -> Random.int 1000) in
  [ "ascending", upto n
  ; "descending", List.init n (fun i -> n - i)
  ; "all equal", List.init n (fun _ -> 7)
  ; "sawtooth", List.init n (fun i -> if i mod 2 = 0 then i else n - i)
  ; "random", random
  ]
;;

let string_of_pairs l =
  "[" ^ String.concat ";" (List.map (fun (a, b) -> Printf.sprintf "(%d,%d)" a b) l) ^ "]"
;;

let test_sort () =
  section "sort (Exercise 4.2)";
  let eq name expect actual =
    check_eq name ~expect ~actual:(to_list actual) string_of_int_list
  in
  let l = [ 5; 3; 8; 1; 9; 2 ] in
  eq "sort of the empty stream" [] (sort compare (of_list []));
  eq "sort of a singleton" [ 7 ] (sort compare (of_list [ 7 ]));
  eq "sort" [ 1; 2; 3; 5; 8; 9 ] (sort compare (of_list l));
  eq "sort of a sorted stream" [ 1; 2; 3; 4 ] (sort compare (of_list [ 1; 2; 3; 4 ]));
  eq "sort of a reversed stream" [ 1; 2; 3; 4 ] (sort compare (of_list [ 4; 3; 2; 1 ]));
  (* A stream is a sequence, not a set: duplicates all survive. *)
  eq
    "sort keeps duplicates"
    [ 1; 1; 2; 2; 3; 3 ]
    (sort compare (of_list [ 2; 1; 3; 1; 2; 3 ]));
  (* The order is the comparator's, not the built-in one. *)
  eq
    "sort follows the comparator it is given"
    [ 9; 8; 5; 3; 2; 1 ]
    (sort (fun a b -> compare b a) (of_list l));
  (* Insertion sort is stable, and a caller-supplied comparator makes that observable:
     compare on the key alone, and equal keys must come out in the order they went in. The
     payload is the position in the input, so the oracle is List.stable_sort. *)
  let by_key (a, _) (b, _) = compare a b in
  let keyed = [ 2, 0; 1, 1; 2, 2; 1, 3; 2, 4; 1, 5 ] in
  check_eq
    "sort is stable"
    ~expect:(List.stable_sort by_key keyed)
    ~actual:(to_list (sort by_key (of_list keyed)))
    string_of_pairs;
  (* Randomised, on keyed elements with few distinct keys, so that one oracle answers for
     ordering, duplicates and stability together. *)
  Random.init 20260920;
  let bad = ref 0 in
  for _ = 0 to 299 do
    let xs = List.init (Random.int 40) (fun i -> Random.int 10, i) in
    if to_list (sort by_key (of_list xs)) <> List.stable_sort by_key xs then incr bad
  done;
  check_int "sort agrees with List.stable_sort, 300 random lists" ~expect:0 ~actual:!bad;
  (* fun lazy, exactly as for the four functions of Figure 4.1. *)
  let s, opened = source (upto 5) in
  comparisons := 0;
  ignore (Sys.opaque_identity (sort counting_compare s));
  check_int "sort opens no cell until its result is forced" ~expect:0 ~actual:!opened;
  check_int
    "sort compares nothing until its result is forced"
    ~expect:0
    ~actual:!comparisons;
  check
    "sort returns a suspension even when its argument cannot be opened"
    (match sort compare (poison ()) with
     | _ -> true
     | exception Opened -> false);
  (* The exercise's claim, for every k at once and over every order. *)
  let n = 1000 in
  let over = ref []
  and dearest = ref 0 in
  List.iter
    (fun (order, xs) ->
      comparisons := 0;
      let rec walk_counting k s =
        match Lazy.force s with
        | Nil -> ()
        | Cons (_, rest) ->
          let k = k + 1 in
          if !comparisons > n * k then over := (order, k, !comparisons) :: !over;
          walk_counting k rest
      in
      walk_counting 0 (sort counting_compare (of_list xs));
      dearest := max !dearest !comparisons)
    (sort_orders n);
  check
    (Printf.sprintf
       "the first k elements cost at most n*k comparisons, for every k and every order%s"
       (first_of
          (fun (order, k, c) ->
            Printf.sprintf "%s: first %d of %d cost %d, bound %d" order k n c (n * k))
          !over))
    (!over = []);
  (* And the saving is laziness, not a better algorithm. Taken all the way to the end this
     is still insertion sort and still quadratic in its worst order: the bound above holds
     because a consumer who stops at k never pays for the rest, not because the rest got
     cheap. The same check keeps the one above honest -- a sort that never called the
     comparator it was handed would pass that one with a count of zero. *)
  check
    (Printf.sprintf
       "sorting all n elements is still quadratic in the worst order (%d comparisons at \
        n=%d)"
       !dearest
       n)
    (!dearest >= n * n / 4)
;;

(* ------------------------------------------------------------------- runner *)

(* A regression can make a function raise where the test did not expect it. Report that as
   a failure and carry on to the remaining sections rather than hiding them. *)
let run name f =
  match f () with
  | () -> ()
  | exception e ->
    incr failures;
    Printf.printf "  FAIL  %s: unexpected exception %s\n" name (Printexc.to_string e)
;;

let () =
  run "values" test_values;
  run "a call does no work" test_call_is_free;
  run "incremental" test_incremental;
  run "monolithic" test_monolithic;
  run "cost" test_cost;
  run "sort" test_sort;
  Printf.printf "\n%d checks, %d failures\n\n" !checks !failures;
  if !failures > 0 then exit 1
;;
