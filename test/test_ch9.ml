(* Tests for Chapter 9: the binary random-access list of Figure 9.6 (section 9.2.1), the
   drop of Exercise 9.1, the create of Exercise 9.2, the sparse list of Exercise 9.3 with
   its own drop and create, the zeroless numbers and list of Exercises 9.4 and 9.5, and
   the zeroless redundant list of Exercise 9.9 and its scheduled form of Exercise 9.10,
   and the segmented binary numbers of section 9.2.4, each with its own preamble further
   down. Plain OCaml, no test framework, matching the earlier chapters.

   Section 9.2.1 builds a list out of a binary number. A list of n elements holds one
   complete binary leaf tree for every one in the binary representation of n, in
   increasing order of size, with the elements in order left to right, so that the head is
   the leftmost leaf of the smallest tree. cons is increment: consTree follows inc, with
   link for the carry. tail is decrement: unconsTree follows dec, splitting a tree for the
   borrow. lookup and update find the tree by the sizes and then the leaf by halving.
   p.122 states the costs: "cons, head, and tail perform at most O(1) work per digit and
   so run in O(log n) worst-case time", and lookup and update take O(log n) to find the
   tree and O(log n) more to find the element, O(log n) worst-case in all. Nothing here is
   lazy and nothing is amortised, so every operation goes on the clock by itself and the
   DEAREST is asserted, against a budget of a constant per digit, at two sizes a hundred
   times apart.

   The contract is aimed where the digits go wrong. A digit list may not end in a ZERO,
   which is what unconsTree's clause for the last ONE is for: emptying a list by tails has
   to give back the empty list, or isEmpty lies and every later head walks the zeros. The
   sizes 0 to 70 cross six powers of two, so every carry cascade and every borrow split of
   that length is exercised, and every index of every size is looked up. And update has to
   copy the whole path it walks, the ZEROs it passes in the list and the NODEs it passes
   in the tree, where lookup may skip both: a list read back after an update, and after an
   update and a cons, has to be the list that was meant, and the version that was updated
   has to read as it did, which is the whole of persistence here.

   The clock is allocation, as in the earlier chapters. It sees cons, head, tail and
   update, which allocate along the path they walk, and it cannot see a lookup that
   allocates nothing, so a lookup that scanned every leaf would read as free. lookup is
   held to the same budget all the same, which catches a lookup that copies, and its
   O(log n) rests on walking the path that update is measured on. The guard that the clock
   sees a linear operation at all is the update of a plain list. *)

open Okasaki.Ch9

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

(* [f] must raise Failure [msg]: the implementation's own message for an empty list or an
   index out of bounds, where the book raises EMPTY and SUBSCRIPT. *)
let check_raises name msg f =
  incr checks;
  match f () with
  | _ ->
    incr failures;
    Printf.printf "  FAIL  %s: expected Failure \"%s\", got no exception\n" name msg
  | exception Failure m when m = msg -> ()
  | exception e ->
    incr failures;
    Printf.printf
      "  FAIL  %s: expected Failure \"%s\", got %s\n"
      name
      msg
      (Printexc.to_string e)
;;

(* [f] must refuse with the implementation's own Failure, whatever it says after [prefix]:
   for refusals whose wording the implementation is free to choose. *)
let refuses ~prefix name f =
  incr checks;
  match f () with
  | _ ->
    incr failures;
    Printf.printf
      "  FAIL  %s: expected Failure \"%s ...\", got no exception\n"
      name
      prefix
  | exception Failure m when String.starts_with ~prefix m -> ()
  | exception e ->
    incr failures;
    Printf.printf
      "  FAIL  %s: expected Failure \"%s ...\", got %s\n"
      name
      prefix
      (Printexc.to_string e)
;;

(* Run [f], and hand its result to [k] if it returned one. An exception is that one
   check's failure and not the section's, so the checks after it still get to run. *)
let surviving name f k =
  match f () with
  | v -> k v
  | exception e ->
    incr checks;
    incr failures;
    Printf.printf "  FAIL  %s: raised %s\n" name (Printexc.to_string e)
;;

let section name = Printf.printf "%s\n" name
let string_of_int_list l = "[" ^ String.concat ";" (List.map string_of_int l) ^ "]"
let upto n = List.init n Fun.id

(* head/tail to exhaustion. A list whose tail does not advance would never come to an end,
   and neither would the list this builds, so a drain past any size used here gives up and
   raises: the checks around it report that as the failure it is. *)
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

(* ---------------------------------------------------------------- the clock *)

(* Words allocated by [f], read before and after. Sys.opaque_identity stops the optimiser
   discarding the result and with it the allocation being measured. The clock counts in
   integers: a float reading would box, and the two words of the box would land inside the
   measurement. *)
let words () = int_of_float (Gc.minor_words ())

let cost f =
  let before = words () in
  let r = Sys.opaque_identity (f ()) in
  r, float_of_int (words () - before)
;;

(* floor (log2 n), for n >= 1. *)
let floor_log2 n =
  let rec go acc n = if n <= 1 then acc else go (acc + 1) (n / 2) in
  go 0 n
;;

(* p.120: a list of n elements has at most floor (log (n + 1)) trees, and no tree is
   deeper than floor (log n). The budget for one operation is PER_DIGIT words for each
   digit it may pass and one more for its own records. Measured, the dearest operations
   are the cons that carries through every digit, a node and a list cell per digit, some 8
   words, and the tail and the update that walk every digit and copy every node on the
   way, under 10 a digit; 24 leaves room for those and the probe's own noise and is
   nowhere near an operation that is really linear, which at the sizes used here is out by
   a factor of ten and more. *)
let digits n = floor_log2 (n + 1)
let per_digit = 24.0
let budget n = per_digit *. float_of_int (digits n + 1)

(* ---------------------------------------------------- the random-access list *)

module Rlist_tests (R : RANDOM_ACCESS_LIST) = struct
  (* The list whose index i holds List.nth xs i. *)
  let of_list xs = List.fold_right R.cons xs R.empty
  let to_list r = drain_with ~is_empty:R.is_empty ~head:R.head ~tail:R.tail r
  let lookups n r = List.init n (fun i -> R.lookup i r)
  let rec tails k r = if k = 0 then r else tails (k - 1) (R.tail r)

  let run_contract name =
    let t label = Printf.sprintf "%s: %s" name label in
    let eq label expect r =
      surviving
        (t label)
        (fun () -> to_list (r ()))
        (fun actual -> check_eq (t label) ~expect ~actual string_of_int_list)
    in
    check (t "empty is empty") (R.is_empty R.empty);
    check (t "a singleton is not empty") (not (R.is_empty (R.cons 1 R.empty)));
    check_raises (t "head on empty raises") "head: empty list" (fun () -> R.head R.empty);
    check_raises (t "tail on empty raises") "tail: empty list" (fun () ->
      ignore (R.is_empty (R.tail R.empty)));
    check_raises (t "lookup on empty raises") "lookup: not found" (fun () ->
      R.lookup 0 R.empty);
    check_raises (t "update on empty raises") "update: not found" (fun () ->
      ignore (R.is_empty (R.update 0 1 R.empty)));
    (* A stack at the front. *)
    surviving
      (t "head is the element cons'ed last")
      (fun () -> R.head (R.cons 3 (R.cons 2 (R.cons 1 R.empty))))
      (fun h -> check_int (t "head is the element cons'ed last") ~expect:3 ~actual:h);
    eq "tail removes it and nothing else" [ 2; 1 ] (fun () ->
      R.tail (of_list [ 3; 2; 1 ]));
    eq "equal elements are all kept, in order" [ 7; 7; 1; 7 ] (fun () ->
      of_list [ 7; 7; 1; 7 ]);
    (* Every size from 0 to 70: read back by head and tail, looked up at every index, and
       refused one past the end and before the start. *)
    let bad = ref [] in
    let note n what = bad := (n, what) :: !bad in
    for n = 70 downto 0 do
      try
        let xs = upto n in
        let r = of_list xs in
        (match to_list r with
         | got when got = xs -> ()
         | got -> note n ("read back " ^ string_of_int_list got)
         | exception Failure why -> note n ("read back raised " ^ why));
        (match lookups n r with
         | got when got = xs -> ()
         | got -> note n ("lookups " ^ string_of_int_list got)
         | exception Failure why -> note n ("lookup raised " ^ why));
        (match R.lookup n r with
         | _ -> note n "lookup one past the end did not raise"
         | exception Failure m when m = "lookup: not found" -> ()
         | exception e -> note n ("lookup one past the end raised " ^ Printexc.to_string e));
        match R.lookup (-1) r with
        | _ -> note n "lookup at -1 did not raise"
        | exception Failure m when m = "lookup: not found" -> ()
        | exception e -> note n ("lookup at -1 raised " ^ Printexc.to_string e)
      with
      | e -> note n ("raised " ^ Printexc.to_string e)
    done;
    check
      (t
         (Printf.sprintf
            "every size from 0 to 70 reads back and looks up correctly%s"
            (match !bad with
             | [] -> ""
             | (n, what) :: _ -> Printf.sprintf " -- n=%d: %s" n what)))
      (!bad = []);
    (* A list emptied by tails is the empty list again, at every size: the borrow out of
       the last tree must not leave a zero behind. *)
    let bad = ref [] in
    let note n what = bad := (n, what) :: !bad in
    for n = 70 downto 1 do
      try
        match tails n (of_list (upto n)) with
        | r ->
          if not (R.is_empty r) then note n "is not empty";
          (match R.head r with
           | _ -> note n "head did not raise"
           | exception Failure m when m = "head: empty list" -> ()
           | exception e -> note n ("head raised " ^ Printexc.to_string e));
          (match R.tail r with
           | _ -> note n "tail did not raise"
           | exception Failure m when m = "tail: empty list" -> ()
           | exception e -> note n ("tail raised " ^ Printexc.to_string e));
          (match to_list (R.cons 7 r) with
           | [ 7 ] -> ()
           | got -> note n ("cons onto it reads back " ^ string_of_int_list got)
           | exception Failure why -> note n ("cons onto it raised " ^ why))
        | exception Failure why -> note n ("emptying raised " ^ why)
      with
      | e -> note n ("raised " ^ Printexc.to_string e)
    done;
    check
      (t
         (Printf.sprintf
            "a list emptied by tails is empty again, sizes 1 to 70%s"
            (match !bad with
             | [] -> ""
             | (n, what) :: _ -> Printf.sprintf " -- n=%d: %s" n what)))
      (!bad = []);
    (* update at every index of every size up to 40, read back by both readers, and read
       back again after a cons: an update that drops a digit or a subtree hands back a
       list that may still read correctly until the next carry. *)
    let bad = ref [] in
    let note n what = bad := (n, what) :: !bad in
    for n = 40 downto 0 do
      try
        let xs = upto n in
        let r = of_list xs in
        for i = 0 to n - 1 do
          let expect = List.mapi (fun k x -> if k = i then 100 + i else x) xs in
          match R.update i (100 + i) r with
          | r' ->
            if to_list r' <> expect
            then note n (Printf.sprintf "update %d reads back wrong" i);
            if lookups n r' <> expect
            then note n (Printf.sprintf "update %d looks up wrong" i);
            let r'' = R.cons (-1) r' in
            if to_list r'' <> -1 :: expect || lookups (n + 1) r'' <> -1 :: expect
            then note n (Printf.sprintf "update %d then cons reads back wrong" i)
          | exception Failure why -> note n (Printf.sprintf "update %d raised %s" i why)
        done;
        (match R.update (-1) 0 r with
         | _ -> note n "update at -1 did not raise"
         | exception Failure m when m = "update: not found" -> ()
         | exception e -> note n ("update at -1 raised " ^ Printexc.to_string e));
        match R.update n 0 r with
        | _ -> note n "update one past the end did not raise"
        | exception Failure m when m = "update: not found" -> ()
        | exception e -> note n ("update one past the end raised " ^ Printexc.to_string e)
      with
      | e -> note n ("raised " ^ Printexc.to_string e)
    done;
    check
      (t
         (Printf.sprintf
            "update at every index of every size up to 40 reads back correctly, and -1 \
             and one past the end are refused%s"
            (match !bad with
             | [] -> ""
             | (n, what) :: _ -> Printf.sprintf " -- n=%d: %s" n what)))
      (!bad = []);
    (* Randomised, against the obvious model: a list. Checked after every operation, with
       a lookup at a random index each time. *)
    Random.init 20260926;
    let bad_empty = ref 0
    and bad_head = ref 0
    and bad_lookup = ref 0
    and bad_final = ref 0
    and raised = ref 0 in
    for _ = 0 to 299 do
      let r = ref R.empty
      and model = ref [] in
      try
        for i = 0 to 59 do
          let n = List.length !model in
          (match if n = 0 then 0 else Random.int 4 with
           | 0 ->
             r := R.cons i !r;
             model := i :: !model
           | 1 ->
             r := R.tail !r;
             model := List.tl !model
           | 2 ->
             let k = Random.int n in
             r := R.update k (1000 + i) !r;
             model := List.mapi (fun j x -> if j = k then 1000 + i else x) !model
           | _ ->
             let k = Random.int n in
             if R.lookup k !r <> List.nth !model k then incr bad_lookup);
          if R.is_empty !r <> (!model = []) then incr bad_empty;
          match !model with
          | x :: _ when R.head !r <> x -> incr bad_head
          | _ -> ()
        done;
        if to_list !r <> !model || lookups (List.length !model) !r <> !model
        then incr bad_final
      with
      | _ -> incr raised
    done;
    check_int
      (t "no operation raises on a valid index of a non-empty list, 300 random runs")
      ~expect:0
      ~actual:!raised;
    check_int (t "is_empty agrees with a list model") ~expect:0 ~actual:!bad_empty;
    check_int (t "head agrees with a list model") ~expect:0 ~actual:!bad_head;
    check_int (t "lookup agrees with a list model") ~expect:0 ~actual:!bad_lookup;
    check_int
      (t "the whole list agrees with the model at the end of each run")
      ~expect:0
      ~actual:!bad_final;
    (* Persistence: an update copies its path and leaves the version it came from as it
       was, and so do cons and tail. *)
    let v = of_list (upto 10) in
    eq
      "an updated version reads the update"
      (List.mapi (fun k x -> if k = 3 then 99 else x) (upto 10))
      (fun () -> R.update 3 99 v);
    eq "the version it came from does not" (upto 10) (fun () ->
      ignore (R.update 3 99 v);
      v);
    surviving
      (t "every earlier version can still be used")
      (fun () ->
        let versions = List.init 40 (fun i -> of_list (upto i)) in
        List.iter
          (fun v ->
            ignore (R.cons 99 v);
            if not (R.is_empty v)
            then (
              ignore (R.tail v);
              ignore (R.update 0 99 v)))
          versions;
        List.mapi
          (fun i v -> if to_list v = upto i && lookups i v = upto i then 0 else 1)
          versions
        |> List.fold_left ( + ) 0)
      (fun stale ->
        check_int (t "every earlier version stays correct") ~expect:0 ~actual:stale)
  ;;

  (* ------------------------------------------ every operation on its own clock *)

  (* Every version of a build by cons, each cons on the clock; then head from every
     version, tail down the whole drain, and lookup and update at every index of the full
     list. The dearest of each is what the bound is about. True if all five stayed within
     the budget. *)
  let run_costs_at name n =
    let t label = Printf.sprintf "%s: %s" name label in
    let ok = ref true in
    let within label (k, c) =
      let fine = c <= budget n in
      check
        (t
           (Printf.sprintf
              "%s, dearest is #%d at %.0f words, n=%d, budget %.0f"
              label
              k
              c
              n
              (budget n)))
        fine;
      if not fine then ok := false
    in
    let v = Array.make (n + 1) R.empty
    and dear = ref (0, 0.0) in
    for i = 1 to n do
      let r, c = cost (fun () -> R.cons i v.(i - 1)) in
      v.(i) <- r;
      if c > snd !dear then dear := i, c
    done;
    within "cons, at every size of a build" !dear;
    let dear = ref (0, 0.0)
    and sum = ref 0 in
    for k = 1 to n do
      let x, c = cost (fun () -> R.head v.(k)) in
      sum := !sum + x;
      if c > snd !dear then dear := k, c
    done;
    within "head, at every size of a build" !dear;
    let r = ref v.(n)
    and dear = ref (0, 0.0) in
    for i = 1 to n do
      let r', c = cost (fun () -> R.tail !r) in
      r := r';
      if c > snd !dear then dear := i, c
    done;
    ignore (Sys.opaque_identity !r);
    within "tail, at every size of a drain" !dear;
    let full = v.(n) in
    let dear = ref (0, 0.0) in
    for i = 0 to n - 1 do
      let x, c = cost (fun () -> R.lookup i full) in
      sum := !sum + x;
      if c > snd !dear then dear := i, c
    done;
    ignore (Sys.opaque_identity !sum);
    within "lookup, at every index" !dear;
    let dear = ref (0, 0.0) in
    for i = 0 to n - 1 do
      let r', c = cost (fun () -> R.update i 0 full) in
      ignore (Sys.opaque_identity r');
      if c > snd !dear then dear := i, c
    done;
    within "update, at every index" !dear;
    !ok
  ;;

  (* O(log n) worst-case, at two sizes a hundred times apart. The large size is guarded on
     the small one, as everywhere in these files: an operation that is secretly linear
     makes the large run quadratic, and that is not a failure but a hang. *)
  let run_costs name =
    if run_costs_at name 1_000
    then ignore (run_costs_at name 100_000)
    else Printf.printf "  SKIP  %s: costs at n=100000 -- over budget at n=1000\n" name
  ;;
end

(* -------------------------------------------------------------------- guard *)

(* A random-access list as a plain list: the contract holds of it, which shows the
   contract asks for behaviour and nothing else, and its update copies the whole prefix,
   which is the lump the clock has to be able to see. Without this, every cost check above
   could pass by measuring nothing. *)
module Plain : RANDOM_ACCESS_LIST = struct
  type 'a rlist = 'a list

  let empty = []
  let is_empty l = l = []
  let cons x l = x :: l

  let head = function
    | [] -> raise (Failure "head: empty list")
    | x :: _ -> x
  ;;

  let tail = function
    | [] -> raise (Failure "tail: empty list")
    | _ :: l -> l
  ;;

  let rec lookup i = function
    | [] -> raise (Failure "lookup: not found")
    | x :: l -> if i = 0 then x else lookup (i - 1) l
  ;;

  let rec update i y = function
    | [] -> raise (Failure "update: not found")
    | x :: l -> if i = 0 then y :: l else x :: update (i - 1) y l
  ;;
end

module Plain_tests = Rlist_tests (Plain)

let test_guard () =
  Plain_tests.run_contract "guard: a plain list";
  let n = 1_000 in
  let l = Plain_tests.of_list (upto n) in
  let _, c = cost (fun () -> Plain.update (n - 1) 0 l) in
  check
    (Printf.sprintf
       "guard: the clock sees a plain list's update of its last element, %.0f words at \
        n=%d"
       c
       n)
    (c >= 3. *. float_of_int (n - 1))
;;

(* ------------------------------------------ BinaryRandomAccessList (9.2.1) *)

module Binary = Rlist_tests (BinaryRandomAccessList)

(* What a list costs means nothing until it behaves like one. *)
let test_binary () =
  section "BinaryRandomAccessList (9.2.1)";
  let before = !failures in
  Binary.run_contract "BinaryRandomAccessList";
  if !failures > before
  then
    Printf.printf
      "  SKIP  BinaryRandomAccessList: cost checks -- the contract above does not hold\n"
  else (
    test_guard ();
    Binary.run_costs "BinaryRandomAccessList")
;;

(* --------------------------------------------------------- drop (Exercise 9.1) *)

(* Exercise 9.1 asks for drop, which deletes the first k elements, in O(log n) time. The
   number is the guide again. After the drop the list holds n - k elements, so its digits
   are the binary representation of n - k, one tree of each size in its place and the
   elements in order, and the way there is in two steps, like lookup: down the digits,
   past the whole trees that go, then down the tree in which the k-th element falls. What
   that second walk leaves is not a tree, and how its pieces become the new low digits is
   the exercise; the tests pin only what must come out. Every size up to 70 is dropped by
   every k and read back both ways. Then, because a tree left one position out of place
   reads back correctly until head or a carry finds it, every result up to size 40 takes
   eight more conses with every index looked up after each, an update at either end, a
   tail, and a second drop of every remaining length, which has to agree with one drop of
   the sum. The cost is the dearest single drop over every k, at two sizes a hundred times
   apart, against the budget above: one walk down the digits and one down a tree. Written
   before the implementation was right, in the manner of Exercise 8.1's tests, so the
   message for a refused drop is only required to begin with "drop:". *)

module type WITH_DROP = sig
  include RANDOM_ACCESS_LIST

  val drop : int -> 'a rlist -> 'a rlist
end

let list_drop k xs = List.filteri (fun i _ -> i >= k) xs

module Drop_tests (R : WITH_DROP) = struct
  module Base = Rlist_tests (R)

  let of_list = Base.of_list
  let to_list = Base.to_list
  let lookups = Base.lookups

  (* A refusal: drop's own Failure, whatever it says after "drop:". *)
  let refuses name f = refuses ~prefix:"drop:" name f

  let run_contract name =
    let t label = Printf.sprintf "%s: %s" name label in
    let eq label expect r =
      surviving
        (t label)
        (fun () -> to_list (r ()))
        (fun actual -> check_eq (t label) ~expect ~actual string_of_int_list)
    in
    eq "drop 0 of empty is empty" [] (fun () -> R.drop 0 R.empty);
    eq "drop 0 changes nothing" [ 1; 2; 3 ] (fun () -> R.drop 0 (of_list [ 1; 2; 3 ]));
    eq "drop 1 of two" [ 2 ] (fun () -> R.drop 1 (of_list [ 1; 2 ]));
    eq "drop 2 of two is empty" [] (fun () -> R.drop 2 (of_list [ 1; 2 ]));
    surviving
      (t "drop 2 of two")
      (fun () -> R.drop 2 (of_list [ 1; 2 ]))
      (fun r -> check (t "drop 2 of two is empty by is_empty too") (R.is_empty r));
    eq "drop 3 of five" [ 4; 5 ] (fun () -> R.drop 3 (of_list [ 1; 2; 3; 4; 5 ]));
    refuses (t "drop 1 of empty refuses") (fun () -> R.drop 1 R.empty);
    refuses (t "drop past the end refuses") (fun () -> R.drop 4 (of_list [ 1; 2; 3 ]));
    refuses (t "drop of a negative count refuses") (fun () ->
      R.drop (-1) (of_list [ 1; 2; 3 ]));
    (* Every k of every size from 0 to 70: the survivors, by both readers, and emptiness. *)
    let bad = ref [] in
    let note n what = bad := (n, what) :: !bad in
    for n = 70 downto 0 do
      try
        let xs = upto n in
        let r = of_list xs in
        for k = 0 to n do
          let expect = list_drop k xs in
          match R.drop k r with
          | r' ->
            (match to_list r' with
             | got when got = expect -> ()
             | got ->
               note n (Printf.sprintf "drop %d reads back %s" k (string_of_int_list got))
             | exception e ->
               note
                 n
                 (Printf.sprintf
                    "drop %d then reading back raised %s"
                    k
                    (Printexc.to_string e)));
            (match lookups (n - k) r' with
             | got when got = expect -> ()
             | got ->
               note n (Printf.sprintf "drop %d looks up %s" k (string_of_int_list got))
             | exception e ->
               note
                 n
                 (Printf.sprintf "drop %d then lookup raised %s" k (Printexc.to_string e)));
            if R.is_empty r' <> (expect = [])
            then note n (Printf.sprintf "drop %d: is_empty is wrong" k)
          | exception e ->
            note n (Printf.sprintf "drop %d raised %s" k (Printexc.to_string e))
        done;
        match R.drop (n + 1) r with
        | _ -> note n "drop one past the end did not raise"
        | exception Failure m when String.starts_with ~prefix:"drop:" m -> ()
        | exception e -> note n ("drop one past the end raised " ^ Printexc.to_string e)
      with
      | e -> note n ("raised " ^ Printexc.to_string e)
    done;
    check
      (t
         (Printf.sprintf
            "every k of every size from 0 to 70 drops correctly%s"
            (match !bad with
             | [] -> ""
             | (n, what) :: _ -> Printf.sprintf " -- n=%d: %s" n what)))
      (!bad = []);
    (* The shape of what is left, sizes up to 40: it has to carry, update, tail and drop
       again like any list of its size. *)
    let bad = ref [] in
    let note n what = bad := (n, what) :: !bad in
    for n = 40 downto 0 do
      try
        let xs = upto n in
        let r = of_list xs in
        for k = 0 to n do
          let survivors = list_drop k xs in
          let m = n - k in
          match R.drop k r with
          | r' ->
            (try
               let q = ref r'
               and model = ref survivors in
               for c = 1 to 8 do
                 q := R.cons (100 + c) !q;
                 model := (100 + c) :: !model;
                 if lookups (m + c) !q <> !model
                 then note n (Printf.sprintf "drop %d then %d conses looks up wrong" k c)
               done;
               if to_list !q <> !model
               then note n (Printf.sprintf "drop %d then 8 conses reads back wrong" k)
             with
             | e ->
               note
                 n
                 (Printf.sprintf "drop %d then conses raised %s" k (Printexc.to_string e)));
            if m > 0
            then (
              try
                let first = List.mapi (fun i x -> if i = 0 then 200 else x) survivors in
                let last =
                  List.mapi (fun i x -> if i = m - 1 then 300 else x) survivors
                in
                if to_list (R.update 0 200 r') <> first
                then note n (Printf.sprintf "drop %d then update 0 reads back wrong" k);
                if to_list (R.update (m - 1) 300 r') <> last
                then
                  note
                    n
                    (Printf.sprintf "drop %d then update of the last reads back wrong" k);
                if to_list (R.tail r') <> List.tl survivors
                then note n (Printf.sprintf "drop %d then tail reads back wrong" k)
              with
              | e ->
                note
                  n
                  (Printf.sprintf
                     "drop %d then update or tail raised %s"
                     k
                     (Printexc.to_string e)));
            (try
               for j = 0 to m do
                 if to_list (R.drop j r') <> list_drop (k + j) xs
                 then note n (Printf.sprintf "drop %d then drop %d reads back wrong" k j)
               done
             with
             | e ->
               note
                 n
                 (Printf.sprintf
                    "drop %d then a second drop raised %s"
                    k
                    (Printexc.to_string e)))
          | exception e ->
            note n (Printf.sprintf "drop %d raised %s" k (Printexc.to_string e))
        done
      with
      | e -> note n ("raised " ^ Printexc.to_string e)
    done;
    check
      (t
         (Printf.sprintf
            "what a drop leaves behaves like a list of its size, sizes up to 40%s"
            (match !bad with
             | [] -> ""
             | (n, what) :: _ -> Printf.sprintf " -- n=%d: %s" n what)))
      (!bad = []);
    (* Randomised, against a list, with drop among the operations. *)
    Random.init 20260927;
    let bad_model = ref 0
    and raised = ref 0 in
    for _ = 0 to 299 do
      let r = ref R.empty
      and model = ref [] in
      try
        for i = 0 to 59 do
          let n = List.length !model in
          (match if n = 0 then 0 else Random.int 6 with
           | 0 | 1 ->
             r := R.cons i !r;
             model := i :: !model
           | 2 ->
             r := R.tail !r;
             model := List.tl !model
           | 3 ->
             let k = Random.int n in
             r := R.update k (1000 + i) !r;
             model := List.mapi (fun j x -> if j = k then 1000 + i else x) !model
           | 4 ->
             let k = Random.int n in
             if R.lookup k !r <> List.nth !model k then incr bad_model
           | _ ->
             let k = Random.int (n + 1) in
             r := R.drop k !r;
             model := list_drop k !model);
          if R.is_empty !r <> (!model = []) then incr bad_model;
          match !model with
          | x :: _ when R.head !r <> x -> incr bad_model
          | _ -> ()
        done;
        if to_list !r <> !model || lookups (List.length !model) !r <> !model
        then incr bad_model
      with
      | _ -> incr raised
    done;
    check_int
      (t "no operation raises on valid arguments, 300 random runs with drop")
      ~expect:0
      ~actual:!raised;
    check_int
      (t "everything agrees with a list model, 300 random runs with drop")
      ~expect:0
      ~actual:!bad_model;
    (* Persistence: a drop leaves the version it came from as it was, and both go on. *)
    let v = of_list (upto 10) in
    eq
      "a dropped version reads the survivors"
      (list_drop 3 (upto 10))
      (fun () -> R.drop 3 v);
    eq "the version it came from does not change" (upto 10) (fun () ->
      ignore (R.drop 3 v);
      v);
    eq "and the original can still be cons'ed onto" (42 :: upto 10) (fun () ->
      let w = R.drop 3 v in
      ignore (R.cons 99 w);
      R.cons 42 v);
    eq
      "as can the dropped version"
      (99 :: list_drop 3 (upto 10))
      (fun () ->
        let w = R.drop 3 v in
        ignore (R.cons 42 v);
        R.cons 99 w)
  ;;

  (* ------------------------------------------------ every drop on its own clock *)

  let run_costs_at name n =
    let t label = Printf.sprintf "%s: %s" name label in
    let r = of_list (upto n) in
    let dear = ref (0, 0.0) in
    for k = 0 to n do
      let r', c = cost (fun () -> R.drop k r) in
      ignore (Sys.opaque_identity r');
      if c > snd !dear then dear := k, c
    done;
    let fine = snd !dear <= budget n in
    check
      (t
         (Printf.sprintf
            "drop, at every k of %d, dearest is k=%d at %.0f words, budget %.0f"
            n
            (fst !dear)
            (snd !dear)
            (budget n)))
      fine;
    fine
  ;;

  let run_costs name =
    if run_costs_at name 1_000
    then ignore (run_costs_at name 100_000)
    else Printf.printf "  SKIP  %s: costs at n=100000 -- over budget at n=1000\n" name
  ;;
end

module Binary_drop = Drop_tests (BinaryRandomAccessList)

let test_drop () =
  section "drop (Exercise 9.1)";
  let before = !failures in
  Binary_drop.run_contract "BinaryRandomAccessList.drop";
  if !failures > before
  then Printf.printf "  SKIP  drop: cost checks -- the contract above does not hold\n"
  else Binary_drop.run_costs "BinaryRandomAccessList.drop"
;;

(* ------------------------------------------------------- create (Exercise 9.2) *)

(* Exercise 9.2 asks for create, which makes a list of n copies of one value, in O(log n)
   time, and points back at Exercise 2.5. The number is the guide again: the result is the
   binary representation of n, a complete tree of each size under every one in its place
   and nothing above the highest one, since a list that ends in a ZERO makes isEmpty lie.
   Exercise 2.5 is what makes the bound possible at all: a complete tree of 2^k copies is
   one node over two references to one tree of 2^(k-1) copies, so n copies need only
   O(log n) nodes.

   All the elements are equal, and that changes what reading back can see: a lookup that
   walks to the wrong leaf still finds a copy, so a tree whose size field disagrees with
   its leaves can read back perfectly. Every n up to 70 is read back both ways all the
   same, and refused one past the end, and 0 has to give the empty list; but the weight of
   the contract is on what comes out behaving like any list of its size. An update at
   every index has to change that index and no other, eight conses have to carry into it
   with every index looked up after each, and tail and a drop of every length have to
   leave the copies they should. Then 300 random runs that start from a created list. A
   negative n is refused with create's own message, as drop refuses a negative count.

   The cost is the dearest create over every size up to n, against the budget above, and
   the created list of size n is held to the same budget for lookup, update and tail. Then
   the ladder: 2^20 - 1 and 2^20 copies, 2^21 - 1 and 2^21, and so on up to 2^50, each
   create on the clock and on a stopwatch, and each list read where reading costs O(log n)
   too: at both ends, one past the end, after a drop of everything, and after an update of
   its last element and a tail. The budget of a constant per digit leaves no room there
   for a tree built afresh for every digit, which is O(log^2 n), and the stopwatch catches
   a create that does linear work without allocating, which the clock cannot see. That is
   also why the sweep at n=100000 comes after the ladder and not before: such a create
   would make it quadratic. The reads are on the stopwatch as well, since they lean on
   drop, whose own tests stop at n=100000. *)

module type WITH_CREATE = sig
  include WITH_DROP

  val create : int -> 'a -> 'a rlist
end

let replicate n x = List.init n (fun _ -> x)

module Create_tests (R : WITH_CREATE) = struct
  module Base = Rlist_tests (R)

  let to_list = Base.to_list
  let lookups = Base.lookups
  let refuses name f = refuses ~prefix:"create:" name f

  let run_contract name =
    let t label = Printf.sprintf "%s: %s" name label in
    let eq label expect r =
      surviving
        (t label)
        (fun () -> to_list (r ()))
        (fun actual -> check_eq (t label) ~expect ~actual string_of_int_list)
    in
    eq "create 0 is empty" [] (fun () -> R.create 0 7);
    surviving
      (t "create 0")
      (fun () -> R.create 0 7)
      (fun r -> check (t "create 0 is empty by is_empty too") (R.is_empty r));
    eq "create 1 is a singleton" [ 7 ] (fun () -> R.create 1 7);
    eq "create 2 is a pair" [ 7; 7 ] (fun () -> R.create 2 7);
    eq "create 5, a one, a zero and a one" (replicate 5 7) (fun () -> R.create 5 7);
    eq "create 8, a single tree" (replicate 8 7) (fun () -> R.create 8 7);
    refuses (t "create of a negative count refuses") (fun () ->
      ignore (R.is_empty (R.create (-1) 7)));
    (* Every size from 0 to 70: n copies by both readers, emptiness, and the end. *)
    let bad = ref [] in
    let note n what = bad := (n, what) :: !bad in
    for n = 70 downto 0 do
      try
        let expect = replicate n n in
        match R.create n n with
        | r ->
          (match to_list r with
           | got when got = expect -> ()
           | got -> note n ("reads back " ^ string_of_int_list got)
           | exception e -> note n ("reading back raised " ^ Printexc.to_string e));
          (match lookups n r with
           | got when got = expect -> ()
           | got -> note n ("looks up " ^ string_of_int_list got)
           | exception e -> note n ("lookup raised " ^ Printexc.to_string e));
          if R.is_empty r <> (n = 0) then note n "is_empty is wrong";
          (match R.lookup n r with
           | _ -> note n "lookup one past the end did not raise"
           | exception Failure m when m = "lookup: not found" -> ()
           | exception e ->
             note n ("lookup one past the end raised " ^ Printexc.to_string e))
        | exception e -> note n ("create raised " ^ Printexc.to_string e)
      with
      | e -> note n ("raised " ^ Printexc.to_string e)
    done;
    check
      (t
         (Printf.sprintf
            "every size from 0 to 70 is n copies%s"
            (match !bad with
             | [] -> ""
             | (n, what) :: _ -> Printf.sprintf " -- n=%d: %s" n what)))
      (!bad = []);
    (* The shape of what create makes, sizes up to 40, seen through the operations that
       trust it: update, cons, tail and drop. *)
    let bad = ref [] in
    let note n what = bad := (n, what) :: !bad in
    for n = 40 downto 0 do
      try
        let copies = replicate n 0 in
        let r = R.create n 0 in
        (try
           for i = 0 to n - 1 do
             let expect = List.mapi (fun k x -> if k = i then 1 + i else x) copies in
             let r' = R.update i (1 + i) r in
             if to_list r' <> expect
             then note n (Printf.sprintf "update %d reads back wrong" i);
             if lookups n r' <> expect
             then note n (Printf.sprintf "update %d looks up wrong" i)
           done;
           match R.update n 1 r with
           | _ -> note n "update one past the end did not raise"
           | exception Failure m when m = "update: not found" -> ()
           | exception e ->
             note n ("update one past the end raised " ^ Printexc.to_string e)
         with
         | e -> note n ("update raised " ^ Printexc.to_string e));
        (try
           let q = ref r
           and model = ref copies in
           for c = 1 to 8 do
             q := R.cons c !q;
             model := c :: !model;
             if lookups (n + c) !q <> !model
             then note n (Printf.sprintf "%d conses looks up wrong" c)
           done;
           if to_list !q <> !model then note n "8 conses reads back wrong"
         with
         | e -> note n ("conses raised " ^ Printexc.to_string e));
        try
          if n > 0 && to_list (R.tail r) <> replicate (n - 1) 0
          then note n "tail reads back wrong";
          for k = 0 to n do
            if to_list (R.drop k r) <> replicate (n - k) 0
            then note n (Printf.sprintf "drop %d reads back wrong" k)
          done
        with
        | e -> note n ("tail or drop raised " ^ Printexc.to_string e)
      with
      | e -> note n ("raised " ^ Printexc.to_string e)
    done;
    check
      (t
         (Printf.sprintf
            "what create makes behaves like a list of its size, sizes up to 40%s"
            (match !bad with
             | [] -> ""
             | (n, what) :: _ -> Printf.sprintf " -- n=%d: %s" n what)))
      (!bad = []);
    (* Randomised, against a list, from a created list of a random size. *)
    Random.init 20260927;
    let bad_model = ref 0
    and raised = ref 0 in
    for run = 0 to 299 do
      try
        let n0 = Random.int 40 in
        let r = ref (R.create n0 (-1 - run))
        and model = ref (replicate n0 (-1 - run)) in
        for i = 0 to 59 do
          let n = List.length !model in
          (match if n = 0 then 0 else Random.int 6 with
           | 0 | 1 ->
             r := R.cons i !r;
             model := i :: !model
           | 2 ->
             r := R.tail !r;
             model := List.tl !model
           | 3 ->
             let k = Random.int n in
             r := R.update k (1000 + i) !r;
             model := List.mapi (fun j x -> if j = k then 1000 + i else x) !model
           | 4 ->
             let k = Random.int n in
             if R.lookup k !r <> List.nth !model k then incr bad_model
           | _ ->
             let k = Random.int (n + 1) in
             r := R.drop k !r;
             model := list_drop k !model);
          if R.is_empty !r <> (!model = []) then incr bad_model;
          match !model with
          | x :: _ when R.head !r <> x -> incr bad_model
          | _ -> ()
        done;
        if to_list !r <> !model || lookups (List.length !model) !r <> !model
        then incr bad_model
      with
      | _ -> incr raised
    done;
    check_int
      (t "no operation raises on valid arguments, 300 random runs from a created list")
      ~expect:0
      ~actual:!raised;
    check_int
      (t "everything agrees with a list model, 300 random runs from a created list")
      ~expect:0
      ~actual:!bad_model;
    (* Persistence: a created list is a version like any other. Made inside each check, so
       that a create that raises fails the check and not the section. *)
    eq
      "an updated version reads the update"
      (List.mapi (fun k x -> if k = 3 then 99 else x) (replicate 10 0))
      (fun () -> R.update 3 99 (R.create 10 0));
    eq
      "the version it came from does not, nor after a cons and a tail of it"
      (replicate 10 0)
      (fun () ->
         let v = R.create 10 0 in
         ignore (R.update 3 99 v);
         ignore (R.cons 1 v);
         ignore (R.tail v);
         v)
  ;;

  (* ---------------------------------------------- every create on its own clock *)

  (* create at every size up to n; then lookup and update at every index of the created
     list of size n, and a drain of it by tail. The dearest of each is what the bound is
     about. True if all four stayed within the budget. *)
  let run_costs_at name n =
    let t label = Printf.sprintf "%s: %s" name label in
    let ok = ref true in
    let within label (k, c) =
      let fine = c <= budget n in
      check
        (t
           (Printf.sprintf
              "%s, dearest is #%d at %.0f words, n=%d, budget %.0f"
              label
              k
              c
              n
              (budget n)))
        fine;
      if not fine then ok := false
    in
    let dear = ref (0, 0.0) in
    for m = 0 to n do
      let r, c = cost (fun () -> R.create m 0) in
      ignore (Sys.opaque_identity r);
      if c > snd !dear then dear := m, c
    done;
    within "create, at every size up to n" !dear;
    let full = R.create n 0 in
    let dear = ref (0, 0.0)
    and sum = ref 0 in
    for i = 0 to n - 1 do
      let x, c = cost (fun () -> R.lookup i full) in
      sum := !sum + x;
      if c > snd !dear then dear := i, c
    done;
    ignore (Sys.opaque_identity !sum);
    within "lookup, at every index of a created list" !dear;
    let dear = ref (0, 0.0) in
    for i = 0 to n - 1 do
      let r', c = cost (fun () -> R.update i 1 full) in
      ignore (Sys.opaque_identity r');
      if c > snd !dear then dear := i, c
    done;
    within "update, at every index of a created list" !dear;
    let r = ref full
    and dear = ref (0, 0.0) in
    for i = 1 to n do
      let r', c = cost (fun () -> R.tail !r) in
      r := r';
      if c > snd !dear then dear := i, c
    done;
    ignore (Sys.opaque_identity !r);
    within "tail, at every size of a drain from a created list" !dear;
    !ok
  ;;

  (* ------------------------------------------------------------------ the ladder *)

  (* Half a second of processor time for one create, and as much again for the reads that
     follow it: some hundred thousand times what either takes at any size here. With the
     rungs a factor of two apart, anything linear in n is stopped within a second or so of
     the first rung it cannot climb. The reads go on the stopwatch too because they lean
     on drop, tail and update, whose own tests stop at n=100000: a drop that is linear
     would otherwise climb to 2^50 and never come back. *)
  let rung_limit = 0.5

  (* n copies, made on the clock and the stopwatch and then used, on the stopwatch again,
     where using them costs O(log n) too. [None] if every check held, or [Some why] for
     the first that did not; a wrong answer is reported before a slow one. *)
  let rung n =
    let started = Sys.time () in
    match cost (fun () -> R.create n 0) with
    | exception e -> Some ("create raised " ^ Printexc.to_string e)
    | r, c ->
      let took = Sys.time () -. started in
      let over what c =
        Some (Printf.sprintf "%s costs %.0f words, budget %.0f" what c (budget n))
      in
      if took > rung_limit
      then Some (Printf.sprintf "create took %.2f s of processor time" took)
      else if c > budget n
      then over "create" c
      else (
        let started = Sys.time () in
        let verdict =
          try
            let refused =
              match R.lookup n r with
              | _ -> false
              | exception Failure m -> m = "lookup: not found"
            in
            if R.head r <> 0 || R.lookup (n - 1) r <> 0
            then Some "an end is not a copy"
            else if not refused
            then Some "lookup one past the end is not refused"
            else if not (R.is_empty (R.drop n r))
            then Some "a drop of all of them is not empty"
            else (
              let r', cu = cost (fun () -> R.update (n - 1) 1 r) in
              let r'', ct = cost (fun () -> R.tail r) in
              if cu > budget n
              then over "the update of the last" cu
              else if ct > budget n
              then over "tail" ct
              else if R.lookup (n - 1) r' <> 1
                      || R.lookup (n - 2) r' <> 0
                      || R.lookup (n - 1) r <> 0
              then Some "the update of the last does not read back"
              else if R.head r'' <> 0 || not (R.is_empty (R.drop (n - 1) r''))
              then Some "the tail does not read back"
              else None)
          with
          | e -> Some ("using it raised " ^ Printexc.to_string e)
        in
        let took = Sys.time () -. started in
        match verdict with
        | Some _ -> verdict
        | None when took > rung_limit ->
          Some (Printf.sprintf "using it took %.2f s of processor time" took)
        | None -> None)
  ;;

  (* 2^20 - 1 and 2^20 copies, 2^21 - 1 and 2^21, and so on to 2^50, up to the first rung
     that does not hold. True if they all did. *)
  let run_ladder name =
    let rec climb k =
      if k > 50
      then None
      else (
        let at label n = Option.map (fun why -> label, why) (rung n) in
        match at (Printf.sprintf "2^%d - 1" k) ((1 lsl k) - 1) with
        | Some _ as bad -> bad
        | None ->
          (match at (Printf.sprintf "2^%d" k) (1 lsl k) with
           | Some _ as bad -> bad
           | None -> climb (k + 1)))
    in
    let bad = climb 20 in
    check
      (Printf.sprintf
         "%s: every rung of the ladder holds, 2^20 - 1 to 2^50 copies%s"
         name
         (match bad with
          | None -> ""
          | Some (label, why) -> Printf.sprintf " -- %s copies: %s" label why))
      (bad = None);
    bad = None
  ;;

  (* O(log n) worst-case: the sweep at n=1000, the ladder, and the sweep at n=100000, each
     guarded on the one before. *)
  let run_costs name =
    let skip what why = Printf.printf "  SKIP  %s: %s -- %s\n" name what why in
    if not (run_costs_at name 1_000)
    then skip "the ladder and costs at n=100000" "over budget at n=1000"
    else if not (run_ladder name)
    then skip "costs at n=100000" "the ladder did not hold"
    else ignore (run_costs_at name 100_000)
  ;;
end

module Binary_create = Create_tests (BinaryRandomAccessList)

let test_create () =
  section "create (Exercise 9.2)";
  let before = !failures in
  Binary_create.run_contract "BinaryRandomAccessList.create";
  if !failures > before
  then Printf.printf "  SKIP  create: cost checks -- the contract above does not hold\n"
  else Binary_create.run_costs "BinaryRandomAccessList.create"
;;

(* --------------------------- SparseBinaryRandomAccessList (Exercise 9.3) *)

(* Exercise 9.3 asks for the same list in a sparse representation. The ZEROs are gone: the
   list holds only the trees, smallest first, and the size stored in each tree is now the
   only record of which digit it stands for. Nothing a user of the list can see is
   different, and the bounds are the same, so the contract and the clock are the ones
   above, unchanged.

   What the sparse form can get wrong without any read-back noticing is the order and the
   uniqueness of the sizes. head and tail never look at a size, and lookup walks the trees
   by subtracting sizes, which finds every element in any order of trees and however many
   share a size. So a cons that stops carrying too early reads back perfectly while the
   number of trees grows with n. The clock sees it in update, which copies a cell for
   every tree before the one it changes, at the last index of a list built by cons. *)

module Sparse = Rlist_tests (SparseBinaryRandomAccessList)

let test_sparse () =
  section "SparseBinaryRandomAccessList (Exercise 9.3)";
  let before = !failures in
  Sparse.run_contract "SparseBinaryRandomAccessList";
  if !failures > before
  then
    Printf.printf
      "  SKIP  SparseBinaryRandomAccessList: cost checks -- the contract above does not \
       hold\n"
  else Sparse.run_costs "SparseBinaryRandomAccessList"
;;

(* ------------------------------------------ sparse drop and create (Exercise 9.3) *)

(* drop and create for the sparse list, through the same tests as the dense ones above.
   Both are simpler here, and for the same reason: there are no ZEROs. drop keeps, in the
   order it meets them, the right halves it turns away from and the subtree where the
   count runs out, which leaves the sizes ascending with nothing to pad. create is the
   numeral with its zeros left out. What the tests ask of them is unchanged: the survivors
   in order, and a result that carries, updates, tails and drops again like any list of
   its size; n copies that behave the same way; and every call within the budget, create
   all the way up the ladder to 2^50. *)

module Sparse_drop = Drop_tests (SparseBinaryRandomAccessList)
module Sparse_create = Create_tests (SparseBinaryRandomAccessList)

let test_sparse_drop () =
  section "SparseBinaryRandomAccessList.drop (Exercises 9.1 and 9.3)";
  let before = !failures in
  Sparse_drop.run_contract "SparseBinaryRandomAccessList.drop";
  if !failures > before
  then
    Printf.printf "  SKIP  sparse drop: cost checks -- the contract above does not hold\n"
  else Sparse_drop.run_costs "SparseBinaryRandomAccessList.drop"
;;

let test_sparse_create () =
  section "SparseBinaryRandomAccessList.create (Exercises 9.2 and 9.3)";
  let before = !failures in
  Sparse_create.run_contract "SparseBinaryRandomAccessList.create";
  if !failures > before
  then
    Printf.printf
      "  SKIP  sparse create: cost checks -- the contract above does not hold\n"
  else Sparse_create.run_costs "SparseBinaryRandomAccessList.create"
;;

(* ------------------------------------------- zeroless binary numbers (Exercise 9.4) *)

(* Exercise 9.4 asks for dec and add on zeroless binary numbers, whose digits are ONE and
   TWO, the i-th weighing 2^i. Every n has exactly one such numeral, and every list of
   ONEs and TWOs is the numeral of some n, so there is no shape to get wrong apart from
   the value: an answer is right exactly when it is the numeral of the right number. The
   tests hold dec and add to that against a model that writes the numeral of an int by
   halving it, and knows nothing of inc or dec: every n up to 1022 decremented, and
   incremented to keep the book's inc honest alongside, and every pair up to 254 added,
   which is every numeral of up to nine digits and every pair of up to seven. Numerals too
   long for an int are held to what holds of any numbers: dec undoes inc and inc undoes
   dec, add commutes and associates, and adding a small k is k increments.

   The book states no bound for these, but inc and dec on ordinary binary numbers take
   O(log n) worst case, one step per digit, and add need only walk both numerals once. So
   each is held to the per-digit budget above, counted in digits of the longer argument:
   the dearest call over every numeral, and every pair, of up to eight digits, then long
   families at a thousand and a hundred thousand digits, all TWOs being the dearest for
   add and all ONEs the longest borrow for dec. Nothing about long numerals runs until the
   short ones are within budget: an add that counted up by increments would be correct,
   and would never finish a pair of thousand-digit numerals. *)

module Z = Zeroless

(* The numeral of n, by halving: an odd n has a ONE at the bottom, an even one a TWO. *)
let rec z_of_int n =
  if n = 0
  then []
  else if n mod 2 = 1
  then Z.One :: z_of_int ((n - 1) / 2)
  else Z.Two :: z_of_int ((n - 2) / 2)
;;

(* Lowest digit first, as the book writes them. *)
let string_of_z = function
  | [] -> "[]"
  | ds ->
    String.concat
      ""
      (List.map
         (function
           | Z.One -> "1"
           | Z.Two -> "2")
         ds)
;;

(* Every numeral of exactly k digits. *)
let rec numerals k =
  if k = 0
  then [ [] ]
  else List.concat_map (fun ds -> [ Z.One :: ds; Z.Two :: ds ]) (numerals (k - 1))
;;

let digit_budget k = per_digit *. float_of_int (k + 1)

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

let test_zeroless_contract () =
  let t label = "Zeroless: " ^ label in
  let z = string_of_z in
  all_of (t "inc of every n up to 1022 is the numeral of n + 1") (fun note ->
    for n = 0 to 1022 do
      match Z.inc (z_of_int n) with
      | r when r = z_of_int (n + 1) -> ()
      | r -> note (Printf.sprintf "inc %s = %s" (z (z_of_int n)) (z r))
      | exception e ->
        note (Printf.sprintf "inc %s raised %s" (z (z_of_int n)) (Printexc.to_string e))
    done);
  refuses ~prefix:"dec:" (t "dec of zero refuses") (fun () -> Z.dec []);
  all_of (t "dec of every n from 1 to 1022 is the numeral of n - 1") (fun note ->
    for n = 1 to 1022 do
      match Z.dec (z_of_int n) with
      | r when r = z_of_int (n - 1) -> ()
      | r ->
        note
          (Printf.sprintf
             "dec %s = %s, want %s"
             (z (z_of_int n))
             (z r)
             (z (z_of_int (n - 1))))
      | exception e ->
        note (Printf.sprintf "dec %s raised %s" (z (z_of_int n)) (Printexc.to_string e))
    done);
  all_of (t "add of every pair up to 254 is the numeral of the sum") (fun note ->
    for a = 0 to 254 do
      for b = 0 to 254 do
        match Z.add (z_of_int a) (z_of_int b) with
        | r when r = z_of_int (a + b) -> ()
        | r ->
          note
            (Printf.sprintf
               "add %s %s = %s, want %s"
               (z (z_of_int a))
               (z (z_of_int b))
               (z r)
               (z (z_of_int (a + b))))
        | exception e ->
          note
            (Printf.sprintf
               "add %s %s raised %s"
               (z (z_of_int a))
               (z (z_of_int b))
               (Printexc.to_string e))
      done
    done)
;;

(* Numerals of about a thousand digits, far past any int: random ones, and the three whose
   carries and borrows run the whole length. *)
let test_zeroless_long () =
  let t label = "Zeroless, a thousand digits: " ^ label in
  Random.init 20260928;
  let random () =
    List.init (900 + Random.int 200) (fun _ -> if Random.bool () then Z.One else Z.Two)
  in
  let ones = List.init 1000 (fun _ -> Z.One)
  and twos = List.init 1000 (fun _ -> Z.Two)
  and alternate = List.init 1000 (fun i -> if i mod 2 = 0 then Z.One else Z.Two) in
  let samples = ones :: twos :: alternate :: List.init 40 (fun _ -> random ()) in
  let guarded note what f =
    match f () with
    | true -> ()
    | false -> note what
    | exception e -> note (what ^ " raised " ^ Printexc.to_string e)
  in
  all_of (t "dec undoes inc, and inc undoes dec") (fun note ->
    List.iteri
      (fun i x ->
        guarded note (Printf.sprintf "dec (inc x) for sample %d" i) (fun () ->
          Z.dec (Z.inc x) = x);
        guarded note (Printf.sprintf "inc (dec x) for sample %d" i) (fun () ->
          Z.inc (Z.dec x) = x))
      samples);
  all_of (t "add commutes and associates") (fun note ->
    List.iteri
      (fun i x ->
        let y = List.nth samples ((i + 1) mod List.length samples)
        and w = List.nth samples ((i + 2) mod List.length samples) in
        guarded note (Printf.sprintf "add x y = add y x for sample %d" i) (fun () ->
          Z.add x y = Z.add y x);
        guarded
          note
          (Printf.sprintf "add (add x y) w = add x (add y w) for sample %d" i)
          (fun () -> Z.add (Z.add x y) w = Z.add x (Z.add y w)))
      samples);
  all_of (t "adding k, on either side, is k increments, for k up to 40") (fun note ->
    List.iteri
      (fun i x ->
        let r = ref x in
        for k = 0 to 40 do
          guarded note (Printf.sprintf "add of %d to sample %d" k i) (fun () ->
            Z.add x (z_of_int k) = !r && Z.add (z_of_int k) x = !r);
          r := Z.inc !r
        done)
      samples)
;;

(* The dearest dec over every numeral of exactly k digits, and the dearest add over every
   pair in which the longer has exactly k, for k from 1 to 8, stopping at the first k that
   is over budget. True if none was. *)
let test_zeroless_short_costs () =
  let t label = "Zeroless: " ^ label in
  let upto k = List.concat (List.init (k + 1) numerals) in
  let rec sweep k =
    if k > 8
    then None
    else (
      let exact = numerals k
      and within = upto k
      and dearest = ref (0.0, "") in
      let see what c = if c > fst !dearest then dearest := c, what in
      List.iter
        (fun a ->
          (match cost (fun () -> Z.dec a) with
           | _, c -> see ("dec " ^ string_of_z a) c
           | exception _ -> ());
          List.iter
            (fun b ->
              (match cost (fun () -> Z.add a b) with
               | _, c ->
                 see (Printf.sprintf "add %s %s" (string_of_z a) (string_of_z b)) c
               | exception _ -> ());
              match cost (fun () -> Z.add b a) with
              | _, c -> see (Printf.sprintf "add %s %s" (string_of_z b) (string_of_z a)) c
              | exception _ -> ())
            within)
        exact;
      if fst !dearest > digit_budget k then Some (k, !dearest) else sweep (k + 1))
  in
  let over = sweep 1 in
  check
    (t
       (match over with
        | None -> "dec and add within budget on every numeral and pair of up to 8 digits"
        | Some (k, (c, what)) ->
          Printf.sprintf
            "dec and add within budget on every numeral and pair of up to 8 digits -- %s \
             costs %.0f words at %d digits, budget %.0f"
            what
            c
            k
            (digit_budget k)))
    (over = None);
  over = None
;;

(* Long families at k digits: each call on the clock by itself, inputs made beforehand. *)
let test_zeroless_long_costs k =
  let ones = List.init k (fun _ -> Z.One)
  and twos = List.init k (fun _ -> Z.Two)
  and alternate = List.init k (fun i -> if i mod 2 = 0 then Z.One else Z.Two)
  and other = List.init k (fun i -> if i mod 2 = 0 then Z.Two else Z.One) in
  Random.init k;
  let random () = List.init k (fun _ -> if Random.bool () then Z.One else Z.Two) in
  let r1 = random ()
  and r2 = random () in
  let calls =
    [ ("add of all TWOs to all TWOs", fun () -> Z.add twos twos)
    ; ("add of all ONEs to all TWOs", fun () -> Z.add ones twos)
    ; ("add of all TWOs to all ONEs", fun () -> Z.add twos ones)
    ; ("add of all ONEs to all ONEs", fun () -> Z.add ones ones)
    ; ("add of 1212... to 2121...", fun () -> Z.add alternate other)
    ; ("add of two random numerals", fun () -> Z.add r1 r2)
    ; ("add of one digit to all TWOs", fun () -> Z.add [ Z.Two ] twos)
    ; ("dec of all ONEs", fun () -> Z.dec ones)
    ; ("dec of all TWOs", fun () -> Z.dec twos)
    ; ("dec of a random numeral", fun () -> Z.dec r1)
    ]
  in
  let dearest = ref (0.0, "") in
  List.iter
    (fun (what, f) ->
      match cost f with
      | _, c -> if c > fst !dearest then dearest := c, what
      | exception e -> dearest := infinity, what ^ " raised " ^ Printexc.to_string e)
    calls;
  let c, what = !dearest in
  let fine = c <= digit_budget k in
  check
    (Printf.sprintf
       "Zeroless, %d digits: the dearest of dec and add is %s at %.0f words, budget %.0f"
       k
       what
       c
       (digit_budget k))
    fine;
  fine
;;

(* Short numerals first, for what they are and then for what they cost; only then the long
   ones, which an add that is not linear in the digits would never finish. *)
let test_zeroless () =
  section "Zeroless binary numbers (Exercise 9.4)";
  let before = !failures in
  test_zeroless_contract ();
  if !failures > before
  then
    Printf.printf
      "  SKIP  Zeroless: long numerals and costs -- the checks above do not hold\n"
  else if not (test_zeroless_short_costs ())
  then Printf.printf "  SKIP  Zeroless: long numerals -- over budget on short ones\n"
  else (
    test_zeroless_long ();
    if test_zeroless_long_costs 1_000
    then ignore (test_zeroless_long_costs 100_000)
    else Printf.printf "  SKIP  Zeroless: costs at 100000 digits -- over budget at 1000\n")
;;

(* ----------------------------- ZerolessBinaryRandomAccessList (Exercise 9.5) *)

(* Exercise 9.5 asks for the rest of the binary random-access list over zeroless numbers:
   digits ONE of a tree and TWO of two trees, the i-th holding trees of size 2^i, and no
   position ever empty. cons is inc with trees and tail is dec with trees, so what can go
   wrong is what went wrong with the numbers: a carry that stops short or runs on, a
   borrow taken where none is due or not passed up the list, an update that forgets a
   digit it walked past. The contract and the clock above see those, unchanged: a carry
   that stops short leaves the list linear in n, and update's walk to the last element
   pays for it.

   What the section is for is head. The first digit is never empty, so the head is always
   a leaf right at the front, and p.125 says head "clearly runs in O(1) worst-case time".
   That is a claim about head itself, as the book writes it, reading the front digit and
   nothing else. A head written the way Figure 9.6 writes it, through the unconsTree that
   tail uses, gives the right answer and rebuilds the list it throws away, and over
   zeroless digits that rebuilding borrows up the list whenever the front is a ONE, which
   is O(log n) on perfectly shaped lists. So head is on the clock at every size of a build
   by cons and of the drain by tail that follows, and its dearest must stay within one
   digit's budget, the same at a thousand elements and at a hundred thousand. A tail that
   leaves a bigger tree at the front is the contract's to catch: the next cons pairs trees
   of different sizes, and lookups go astray. O(log i) for lookup and update is Exercise
   9.6, and not asked of this one. *)

module Zeroless_list = Rlist_tests (ZerolessBinaryRandomAccessList)

let test_zeroless_head_at n =
  let module R = ZerolessBinaryRandomAccessList in
  let name =
    Printf.sprintf
      "ZerolessBinaryRandomAccessList: head, at every size of a build and of the drain \
       after it, n=%d"
      n
  in
  let dearest () =
    let dear = ref 0.0
    and sum = ref 0
    and r = ref R.empty in
    let see r =
      let x, c = cost (fun () -> R.head r) in
      sum := !sum + x;
      if c > !dear then dear := c
    in
    for i = 1 to n do
      r := R.cons i !r;
      see !r
    done;
    for _ = 2 to n do
      r := R.tail !r;
      see !r
    done;
    ignore (Sys.opaque_identity !sum);
    !dear
  in
  match dearest () with
  | c ->
    let fine = c <= per_digit in
    check
      (Printf.sprintf
         "%s, dearest at %.0f words, budget %.0f whatever n"
         name
         c
         per_digit)
      fine;
    fine
  | exception e ->
    check (Printf.sprintf "%s: raised %s" name (Printexc.to_string e)) false;
    false
;;

let test_zeroless_list () =
  section "ZerolessBinaryRandomAccessList (Exercise 9.5)";
  let before = !failures in
  Zeroless_list.run_contract "ZerolessBinaryRandomAccessList";
  if !failures > before
  then
    Printf.printf
      "  SKIP  ZerolessBinaryRandomAccessList: cost checks -- the contract above does \
       not hold\n"
  else (
    Zeroless_list.run_costs "ZerolessBinaryRandomAccessList";
    if test_zeroless_head_at 1_000
    then ignore (test_zeroless_head_at 100_000)
    else
      Printf.printf
        "  SKIP  ZerolessBinaryRandomAccessList: head at n=100000 -- over budget at n=1000\n")
;;

(* ------------------- ZerolessRedundantBinaryRandomAccessList (Exercise 9.9) *)

(* Exercise 9.9 asks for cons, head and tail on a random-access list over zeroless
   redundant binary numbers: digits ONE, TWO and THREE of trees, the i-th holding trees of
   size 2^i, in a stream, with all three in O(1) amortised time. Section 9.2.3 (p.126) has
   the numbers, and the trees are those of the lists above. The module offers the stack
   and nothing else (RANDOM_ACCESS_LIST_LITE), so the contract is about the order the
   elements come back in: every size from 0 to 70, both built by cons and left by tails
   from a longer list, read back, emptied, and moved back and forth by a cons and a tail
   in turn; a list of twenty thousand, whose digits run to thirteen positions, and a
   random walk from it; and random steps over a pool of versions, old ones used again,
   against a list model. The messages are the ones the other lists here use. What the
   stack cannot see is where the trees are: a carry or a borrow that left a tree at the
   wrong level, in the right order, reads back correctly, and at these sizes costs no
   more. A lookup would see it, and this module has none.

   Amortised costs change what goes on the clock. A single operation may be dear, since it
   can do work that earlier ones left for later, so no single operation is held to
   anything. The clock goes on whole sequences, from the empty list to the last operation,
   and what is held to a budget is the mean, words per cons or tail, a constant whatever
   the size: the same budget at 3 (2^10 - 1) elements and at 3 (2^17 - 1). Each cons and
   tail is followed by a head, which reads the front of the stream it returns. An
   amortised bound in this book is one that survives persistence (section 6.2; 5.6 shows
   what goes wrong otherwise), so two of the sequences use one old version over and over,
   each time where a carry or a borrow could run the whole length: the list of 3 (2^k - 1)
   elements built by cons, which the carry of the exercise leaves with a THREE at every
   position, given as many conses as it took to build; and the list that 2 (2^k - 1) tails
   then leave with a ONE at every position, given as many tails as it took to make. Two
   more go back and forth, a cons and a tail in turn, from each of those lists, and then
   drain what they end with. And the plainest: a build by cons and its drain by tail. *)

module Lite_tests (R : RANDOM_ACCESS_LIST_LITE) = struct
  let of_list xs = List.fold_right R.cons xs R.empty
  let to_list r = drain_with ~is_empty:R.is_empty ~head:R.head ~tail:R.tail r
  let rec tails k r = if k = 0 then r else tails (k - 1) (R.tail r)

  (* k, k + 1, ..., k + n - 1. *)
  let from k n = List.init n (fun i -> k + i)

  let show_list l =
    let n = List.length l in
    if n <= 12
    then string_of_int_list l
    else
      Printf.sprintf
        "%s... (%d elements)"
        (string_of_int_list (List.filteri (fun i _ -> i < 10) l))
        n
  ;;

  (* [r] read back, for [all_of]: a note unless it is [expect]. *)
  let reads note what expect r =
    match to_list (r ()) with
    | got when got = expect -> ()
    | got -> note (Printf.sprintf "%s reads back %s" what (show_list got))
    | exception e -> note (Printf.sprintf "%s: raised %s" what (Printexc.to_string e))
  ;;

  (* The n elements 0 to n - 1, reached two ways: built by cons, and left by 40 tails from
     a list 40 longer, whose digits the borrows have made. *)
  let versions n =
    [ ("built by cons", fun () -> of_list (from 0 n))
    ; ("left by tails", fun () -> tails 40 (of_list (from (-40) (n + 40))))
    ]
  ;;

  let run_contract name =
    let t label = Printf.sprintf "%s: %s" name label in
    check (t "empty is empty") (R.is_empty R.empty);
    check (t "a singleton is not empty") (not (R.is_empty (R.cons 1 R.empty)));
    check_raises (t "head on empty raises") "head: empty list" (fun () -> R.head R.empty);
    check_raises (t "tail on empty raises") "tail: empty list" (fun () ->
      ignore (R.is_empty (R.tail R.empty)));
    surviving
      (t "head is the element cons'ed last")
      (fun () -> R.head (R.cons 3 (R.cons 2 (R.cons 1 R.empty))))
      (fun h -> check_int (t "head is the element cons'ed last") ~expect:3 ~actual:h);
    all_of (t "tail removes it and nothing else") (fun note ->
      reads note "tail of [3;2;1]" [ 2; 1 ] (fun () -> R.tail (of_list [ 3; 2; 1 ])));
    all_of (t "equal elements are all kept, in order") (fun note ->
      reads note "[7;7;1;7]" [ 7; 7; 1; 7 ] (fun () -> of_list [ 7; 7; 1; 7 ]));
    all_of
      (t "every size from 0 to 70, built by cons or left by tails, reads back in order")
      (fun note ->
         for n = 0 to 70 do
           List.iter
             (fun (how, r) -> reads note (Printf.sprintf "n=%d %s" n how) (from 0 n) r)
             (versions n)
         done);
    all_of (t "a list emptied by tails is empty again, sizes 1 to 70") (fun note ->
      for n = 1 to 70 do
        try
          let r = tails n (of_list (from 0 n)) in
          if not (R.is_empty r) then note (Printf.sprintf "n=%d: not empty" n);
          (match R.head r with
           | _ -> note (Printf.sprintf "n=%d: head did not raise" n)
           | exception Failure m when m = "head: empty list" -> ()
           | exception e ->
             note (Printf.sprintf "n=%d: head raised %s" n (Printexc.to_string e)));
          (match R.tail r with
           | _ -> note (Printf.sprintf "n=%d: tail did not raise" n)
           | exception Failure m when m = "tail: empty list" -> ()
           | exception e ->
             note (Printf.sprintf "n=%d: tail raised %s" n (Printexc.to_string e)));
          reads note (Printf.sprintf "n=%d: a cons onto it" n) [ 7 ] (fun () ->
            R.cons 7 r)
        with
        | e -> note (Printf.sprintf "n=%d: raised %s" n (Printexc.to_string e))
      done);
    (* Forty steps, a cons and a tail in turn, starting with either, from every size and
       both ways of reaching it, the head read after every step: a carry and a borrow at
       the same positions, again and again. *)
    all_of
      (t
         "back and forth by cons and tail, 40 steps from every size from 0 to 70 either \
          way: the head after every step, and the list at the end")
      (fun note ->
         for n = 0 to 70 do
           List.iter
             (fun (how, r) ->
               List.iter
                 (fun cons_first ->
                   let what =
                     Printf.sprintf
                       "n=%d %s, %s first"
                       n
                       how
                       (if cons_first then "cons" else "tail")
                   in
                   try
                     let r = ref (r ())
                     and model = ref (from 0 n) in
                     for i = 1 to 40 do
                       if i mod 2 = 1 = cons_first
                       then (
                         r := R.cons (-i) !r;
                         model := -i :: !model)
                       else (
                         r := R.tail !r;
                         model := List.tl !model);
                       match !model with
                       | x :: _ when R.head !r <> x ->
                         note
                           (Printf.sprintf
                              "%s, step %d: head %d, want %d"
                              what
                              i
                              (R.head !r)
                              x)
                       | _ -> ()
                     done;
                     reads note what !model (fun () -> !r)
                   with
                   | e ->
                     note (Printf.sprintf "%s: raised %s" what (Printexc.to_string e)))
                 (if n = 0 then [ true ] else [ true; false ]))
             (versions n)
         done);
    (* Twenty thousand elements: the build read back, then a random walk of as many conses
       and tails from it, the head checked at every step, and where it ends read back. *)
    all_of
      (t
         "a list of 20000 reads back, and so does a random walk of 20000 steps from it, \
          the head checked at each")
      (fun note ->
         let n = 20_000 in
         reads note "the build of 20000" (from 0 n) (fun () -> of_list (from 0 n));
         Random.init 20260929;
         try
           let r = ref (of_list (from 0 n))
           and model = ref (from 0 n) in
           for i = 1 to 20_000 do
             if !model = [] || Random.bool ()
             then (
               r := R.cons (-i) !r;
               model := -i :: !model)
             else (
               r := R.tail !r;
               model := List.tl !model);
             match !model with
             | x :: _ when R.head !r <> x ->
               note (Printf.sprintf "walk step %d: head %d, want %d" i (R.head !r) x)
             | _ -> ()
           done;
           reads note "the end of the walk" !model (fun () -> !r)
         with
         | e -> note ("the walk raised " ^ Printexc.to_string e));
    (* Random steps over a pool of versions: each takes a version at random, old or new,
       conses onto it or takes its tail, checks the result against a list model, and puts
       it in the pool in place of one at random. Every version left in the pool is read
       back at the end. *)
    all_of
      (t
         "5000 random steps over a pool of versions, old ones used again: is_empty and \
          head after each, and every version read back at the end")
      (fun note ->
         Random.init 20260930;
         let size = 64 in
         let pool = Array.make size (R.empty, []) in
         for i = 1 to 5000 do
           let r, model = pool.(Random.int size) in
           try
             let r', model' =
               if model = [] || Random.int 3 > 0
               then R.cons i r, i :: model
               else R.tail r, List.tl model
             in
             if R.is_empty r' <> (model' = [])
             then note (Printf.sprintf "step %d: is_empty is wrong" i);
             (match model' with
              | x :: _ when R.head r' <> x ->
                note (Printf.sprintf "step %d: head %d, want %d" i (R.head r') x)
              | _ -> ());
             pool.(Random.int size) <- r', model'
           with
           | e -> note (Printf.sprintf "step %d: raised %s" i (Printexc.to_string e))
         done;
         Array.iteri
           (fun j (r, model) ->
             reads note (Printf.sprintf "pool version %d" j) model (fun () -> r))
           pool);
    (* Persistence, plainly: every version of a build of 40, and of the drain after it,
       reads as it did once all of them have been cons'ed onto and tailed. *)
    all_of
      (t "every version of a build of 40, and of its drain, still reads as it did")
      (fun note ->
         try
           let built = Array.make 41 R.empty in
           for i = 1 to 40 do
             built.(i) <- R.cons (40 - i) built.(i - 1)
           done;
           let drained = Array.make 41 built.(40) in
           for i = 1 to 40 do
             drained.(i) <- R.tail drained.(i - 1)
           done;
           let use v =
             ignore (Sys.opaque_identity (R.cons 99 v));
             if not (R.is_empty v) then ignore (Sys.opaque_identity (R.tail v))
           in
           Array.iter use built;
           Array.iter use drained;
           Array.iteri
             (fun i v ->
               reads
                 note
                 (Printf.sprintf "build version %d" i)
                 (from (40 - i) i)
                 (fun () -> v))
             built;
           Array.iteri
             (fun i v ->
               reads
                 note
                 (Printf.sprintf "drain version %d" i)
                 (from i (40 - i))
                 (fun () -> v))
             drained
         with
         | e -> note ("raised " ^ Printexc.to_string e))
  ;;

  (* ------------------------------------------------ whole sequences on the clock *)

  (* Two digits' worth, a cons or a tail. Measured, the dearest mean here is some 29
     words, the build and its drain; the sequences on one old version come to 24.
     Something that does O(log n) work where these sequences aim is out by a factor of two
     at 3 (2^10 - 1), and further at 3 (2^17 - 1). *)
  let amortised_budget = 2.0 *. per_digit
  let read r = ignore (Sys.opaque_identity (R.head r))

  let build n =
    let r = ref R.empty in
    for i = 1 to n do
      r := R.cons i !r;
      read !r
    done;
    !r
  ;;

  let rec tails_reading k r =
    if k = 0
    then r
    else (
      let r = R.tail r in
      if not (R.is_empty r) then read r;
      tails_reading (k - 1) r)
  ;;

  (* [steps] conses and tails in turn, starting with either. *)
  let back_and_forth ~cons_first steps r =
    let r = ref r in
    for i = 1 to steps do
      r := if i mod 2 = 1 = cons_first then R.cons (-i) !r else R.tail !r;
      if not (R.is_empty !r) then read !r
    done;
    !r
  ;;

  (* Words per cons or tail over a sequence: [f] runs it and says how many it made. *)
  let mean f =
    let before = words () in
    let ops = f () in
    float_of_int (words () - before) /. float_of_int ops
  ;;

  let sequences k =
    let m = (1 lsl k) - 1 in
    let n = 3 * m in
    [ ( Printf.sprintf "a build of %d by cons and its drain by tail" n
      , fun () ->
          ignore (Sys.opaque_identity (tails_reading n (build n)));
          2 * n )
    ; ( Printf.sprintf "a build of %d, then %d conses onto that one version" n n
      , fun () ->
          let v = build n in
          for i = 1 to n do
            read (R.cons (-i) v)
          done;
          2 * n )
    ; ( Printf.sprintf
          "a build of %d and %d tails, then %d tails of that one version"
          n
          (2 * m)
          (n + (2 * m))
      , fun () ->
          let v = tails_reading (2 * m) (build n) in
          for _ = 1 to n + (2 * m) do
            let r = R.tail v in
            if not (R.is_empty r) then read r
          done;
          2 * (n + (2 * m)) )
    ; ( Printf.sprintf
          "a build of %d, then %d conses and tails in turn, then the drain"
          n
          (2 * n)
      , fun () ->
          let r = back_and_forth ~cons_first:true (2 * n) (build n) in
          ignore (Sys.opaque_identity (tails_reading n r));
          4 * n )
    ; ( Printf.sprintf
          "a build of %d and %d tails, then %d tails and conses in turn, then the drain"
          n
          (2 * m)
          (2 * (n + (2 * m)))
      , fun () ->
          let v = tails_reading (2 * m) (build n) in
          let r = back_and_forth ~cons_first:false (2 * (n + (2 * m))) v in
          ignore (Sys.opaque_identity (tails_reading m r));
          ((n + (2 * m)) * 3) + m )
    ]
  ;;

  (* True if every sequence was within budget. *)
  let run_costs_at name k =
    List.fold_left
      (fun ok (what, f) ->
        let label = Printf.sprintf "%s: %s" name what in
        match mean f with
        | c ->
          let fine = c <= amortised_budget in
          check
            (Printf.sprintf
               "%s, %.1f words a cons or tail, budget %.0f"
               label
               c
               amortised_budget)
            fine;
          ok && fine
        | exception e ->
          check (Printf.sprintf "%s: raised %s" label (Printexc.to_string e)) false;
          false)
      true
      (sequences k)
  ;;

  (* The same budget at two sizes 128 times apart, the large one guarded on the small, as
     everywhere in these files. *)
  let run_costs name =
    if run_costs_at name 10
    then ignore (run_costs_at name 17)
    else
      Printf.printf
        "  SKIP  %s: costs at 3 (2^17 - 1) -- over budget at 3 (2^10 - 1)\n"
        name
  ;;

  (* ------------------------------------------ every operation on its own clock *)

  (* For a worst-case bound (Exercise 9.10): every cons, head, tail and is_empty on the
     clock by itself, and the dearest of a whole sequence held to a constant, the same at
     both sizes: four digits' worth. Measured, the dearest is some 55 words, a cons that
     starts a carry and runs its steps of the schedule. A schedule that falls behind, or a
     tail that leaves its borrow off it, comes to 120 words and more at 3 (2^10 - 1)
     already; a carry or a borrow run to its end on the spot, some 180; and no schedule at
     all, thousands. *)
  let worst_case_budget = 4.0 *. per_digit
  let dearest = ref 0.0
  let dearest_at = ref ("", 0)
  let steps = ref 0

  let clocked op f =
    incr steps;
    let r, c = cost f in
    if c > !dearest
    then (
      dearest := c;
      dearest_at := op, !steps);
    r
  ;;

  let c_cons i r = clocked "cons" (fun () -> R.cons i r)
  let c_tail r = clocked "tail" (fun () -> R.tail r)

  (* is_empty forces the front of the stream as much as head does, so it is on the clock
     as well. *)
  let c_head r =
    if not (clocked "is_empty" (fun () -> R.is_empty r))
    then ignore (Sys.opaque_identity (clocked "head" (fun () -> R.head r)))
  ;;

  let c_tails k r =
    let r = ref r in
    for _ = 1 to k do
      r := c_tail !r;
      c_head !r
    done;
    !r
  ;;

  let worst_sequences k =
    let m = (1 lsl k) - 1 in
    let n = 3 * m in
    let build () =
      let r = ref R.empty in
      for i = 1 to n do
        r := c_cons i !r;
        c_head !r
      done;
      !r
    in
    let back_and_forth ~cons_first steps r =
      let r = ref r in
      for i = 1 to steps do
        r := if i mod 2 = 1 = cons_first then c_cons (-i) !r else c_tail !r;
        c_head !r
      done;
      !r
    in
    [ ( Printf.sprintf "a build of %d by cons and its drain by tail" n
      , fun () -> ignore (c_tails n (build ())) )
    ; ( Printf.sprintf "a build of %d, then %d conses onto that one version" n n
      , fun () ->
          let v = build () in
          for i = 1 to n do
            c_head (c_cons (-i) v)
          done )
    ; ( Printf.sprintf
          "a build of %d and %d tails, then %d tails of that one version"
          n
          (2 * m)
          (n + (2 * m))
      , fun () ->
          let v = c_tails (2 * m) (build ()) in
          for _ = 1 to n + (2 * m) do
            c_head (c_tail v)
          done )
    ; ( Printf.sprintf
          "a build of %d, then %d conses and tails in turn, then the drain"
          n
          (2 * n)
      , fun () -> ignore (c_tails n (back_and_forth ~cons_first:true (2 * n) (build ())))
      )
    ; ( Printf.sprintf
          "a build of %d and %d tails, then %d tails and conses in turn, then the drain"
          n
          (2 * m)
          (2 * (n + (2 * m)))
      , fun () ->
          let v = c_tails (2 * m) (build ()) in
          ignore (c_tails m (back_and_forth ~cons_first:false (2 * (n + (2 * m))) v)) )
    ; ( Printf.sprintf "%d conses that nobody reads, then a head, then the drain" n
      , fun () ->
          let r = ref R.empty in
          for i = 1 to n do
            r := c_cons i !r
          done;
          c_head !r;
          ignore (c_tails n !r) )
    ]
  ;;

  (* True if every sequence's dearest operation was within budget. *)
  let run_worst_costs_at name k =
    List.fold_left
      (fun ok (what, f) ->
        dearest := 0.0;
        dearest_at := "", 0;
        steps := 0;
        match f () with
        | () ->
          let op, i = !dearest_at in
          let fine = !dearest <= worst_case_budget in
          check
            (Printf.sprintf
               "%s: %s, the dearest is the %s at step %d, %.0f words, budget %.0f"
               name
               what
               op
               i
               !dearest
               worst_case_budget)
            fine;
          ok && fine
        | exception e ->
          check
            (Printf.sprintf "%s: %s: raised %s" name what (Printexc.to_string e))
            false;
          false)
      true
      (worst_sequences k)
  ;;

  let run_worst_costs name =
    if run_worst_costs_at name 10
    then ignore (run_worst_costs_at name 17)
    else
      Printf.printf
        "  SKIP  %s: costs at 3 (2^17 - 1) -- over budget at 3 (2^10 - 1)\n"
        name
  ;;
end

module Redundant = Lite_tests (ZerolessRedundantBinaryRandomAccessList (Okasaki.Ch4.Stream))

let test_redundant () =
  let name = "ZerolessRedundantBinaryRandomAccessList" in
  section (name ^ " (Exercise 9.9)");
  let before = !failures in
  Redundant.run_contract name;
  if !failures > before
  then Printf.printf "  SKIP  %s: cost checks -- the contract above does not hold\n" name
  else Redundant.run_costs name
;;

(* ---------- ScheduledZerolessRedundantBinaryRandomAccessList (Exercise 9.10) *)

(* Exercise 9.10 asks for the same three operations in O(1) worst-case time, by
   scheduling, as the binomial heaps of section 7.3 do it: the list carries, beside its
   stream, the carries and borrows that have not yet run, and every cons and tail runs a
   few steps of them, so that no suspension is forced before the ones it depends on.
   Nothing the stack can see changes, so the contract is 9.9's, through the same functor,
   and so is what it cannot see.

   What changes is the clock. Every cons, head and tail goes on it by itself now, and the
   dearest single operation of each sequence is held to a constant, the same at 3
   (2^10 - 1) elements and at 3 (2^17 - 1). The sequences are 9.9's: a build and its
   drain, one old version cons'ed onto and tailed over and over where a carry or a borrow
   runs the whole length, and back and forth from both of those. And one more, which 9.9
   would fail: conses that nobody reads, then a head. In 9.9 that head runs every carry
   the conses left behind, some twelve words an element; here each cons has already done
   its share. *)

module Scheduled =
  Lite_tests (ScheduledZerolessRedundantBinaryRandomAccessList (Okasaki.Ch4.Stream))

let test_scheduled () =
  let name = "ScheduledZerolessRedundantBinaryRandomAccessList" in
  section (name ^ " (Exercise 9.10)");
  let before = !failures in
  Scheduled.run_contract name;
  if !failures > before
  then Printf.printf "  SKIP  %s: cost checks -- the contract above does not hold\n" name
  else Scheduled.run_worst_costs name
;;

(* ------------------------------------------- segmented binary numbers (9.2.4) *)

(* Section 9.2.4 groups runs of equal digits into blocks, so that a carry or a borrow
   through a whole run is one step. p.129: "segmented binary numbers support inc and dec
   in O(1) worst-case time", and of the redundant form that follows, "we can increment a
   number in O(1) worst-case time".

   SegmentedRepresentationOne is alternating blocks of zeros and ones. p.128: the helpers
   "merge adjacent blocks of the same digit and discard empty blocks", and zeros "discards
   any trailing zeros". So every n has exactly one list of blocks, and inc and dec are
   right exactly when they return it. The model run-length encodes the binary digits of n
   and knows nothing else of blocks: every n up to 4095, then numerals thousands of digits
   long in runs of up to 300, whose bits the model keeps as a list. The value alone would
   not do: a block of length zero adds nothing to it, so a dec that leaves one behind is
   right by the value and wrong by the shape.

   SegmentedRepresentationTwo has digits ZERO and TWO and blocks of ONEs, and more than
   one numeral per number. A result is right when it has the right value and keeps the
   book's invariant (0*1 | 0+1*2)*: the last digit below a TWO that is not a one is a
   ZERO, and nothing ends in a ZERO. Its blocks of ONEs are never empty and never side by
   side, which fixup's second clause needs to see a TWO behind the first block. inc is
   held to that on every regular numeral of up to ten digits, not only the ones counting
   reaches, on every number up to 2^16 counted from zero, and on long numerals.

   Then the clock, every call on it by itself, and the dearest held to one constant at a
   thousand and at a hundred thousand, in block lengths and in block counts: the numerals
   where a carry or borrow that went digit by digit, or a pass over every block, would
   cost the most. *)

module S1 = SegmentedRepresentationOne
module S2 = SegmentedRepresentationTwo

(* Binary digits, lowest first, never ending in a 0: the model for both. *)
let rec bits_of_int n = if n = 0 then [] else (n mod 2) :: bits_of_int (n / 2)

let rec inc_bits = function
  | [] -> [ 1 ]
  | 0 :: bs -> 1 :: bs
  | _ :: bs -> 0 :: inc_bits bs
;;

let rec dec_bits = function
  | [] -> invalid_arg "dec_bits: zero"
  | [ _ ] -> []
  | 1 :: bs -> 0 :: bs
  | _ :: bs -> 1 :: dec_bits bs
;;

(* The one list of blocks for these bits: their runs, lowest first. *)
let blocks_of_bits bs =
  let block b i = if b = 0 then S1.Zeros i else S1.Ones i in
  let rec go b i = function
    | b' :: bs when b' = b -> go b (i + 1) bs
    | b' :: bs -> block b i :: go b' 1 bs
    | [] -> [ block b i ]
  in
  match bs with
  | [] -> []
  | b :: bs -> go b 1 bs
;;

let s1_of_int n = blocks_of_bits (bits_of_int n)

(* Spelled out digit by digit: only ever applied to numerals the tests made. *)
let bits_of_blocks bks =
  List.concat_map
    (function
      | S1.Zeros i -> List.init i (fun _ -> 0)
      | S1.Ones i -> List.init i (fun _ -> 1))
    bks
;;

(* Lowest first, a run as its digit and its length. *)
let string_of_s1 = function
  | [] -> "[]"
  | bks ->
    String.concat
      " "
      (List.map
         (function
           | S1.Zeros i -> Printf.sprintf "0^%d" i
           | S1.Ones i -> Printf.sprintf "1^%d" i)
         bks)
;;

(* Alternating runs of length one, [count] blocks, the top one ONEs. *)
let s1_alternating count =
  List.init count (fun j -> if (count - 1 - j) mod 2 = 0 then S1.Ones 1 else S1.Zeros 1)
;;

(* [count] alternating runs of random lengths from 1 to [longest], the top one ONEs. *)
let s1_random count longest =
  List.init count (fun j ->
    let i = 1 + Random.int longest in
    if (count - 1 - j) mod 2 = 0 then S1.Ones i else S1.Zeros i)
;;

let test_seg1_contract () =
  let t label = "SegmentedRepresentationOne: " ^ label in
  let s = string_of_s1 in
  all_of (t "inc of every n up to 4095 is the blocks of n + 1") (fun note ->
    for n = 0 to 4095 do
      match S1.inc (s1_of_int n) with
      | r when r = s1_of_int (n + 1) -> ()
      | r ->
        note
          (Printf.sprintf
             "inc %s = %s, want %s"
             (s (s1_of_int n))
             (s r)
             (s (s1_of_int (n + 1))))
      | exception e ->
        note (Printf.sprintf "inc %s raised %s" (s (s1_of_int n)) (Printexc.to_string e))
    done);
  refuses ~prefix:"dec:" (t "dec of zero refuses") (fun () -> S1.dec []);
  all_of (t "dec of every n from 1 to 4095 is the blocks of n - 1") (fun note ->
    for n = 1 to 4095 do
      match S1.dec (s1_of_int n) with
      | r when r = s1_of_int (n - 1) -> ()
      | r ->
        note
          (Printf.sprintf
             "dec %s = %s, want %s"
             (s (s1_of_int n))
             (s r)
             (s (s1_of_int (n - 1))))
      | exception e ->
        note (Printf.sprintf "dec %s raised %s" (s (s1_of_int n)) (Printexc.to_string e))
    done)
;;

(* Numerals far past any int. Each takes a hundred incs and then two hundred decs, every
   step against the model, so that inc and dec also see what the other returned. A chain
   stops at its first wrong step: what follows a wrong numeral says nothing new. *)
let test_seg1_long () =
  let t label = "SegmentedRepresentationOne, long numerals: " ^ label in
  Random.init 20260929;
  let rec random () =
    let x = s1_random (2 + Random.int 40) 300 in
    if List.length (bits_of_blocks x) < 10 then random () else x
  in
  let samples =
    [ "1^1000", [ S1.Ones 1000 ]
    ; "0^1000 1", [ S1.Zeros 1000; S1.Ones 1 ]
    ; "1^300 0^300 1^300", [ S1.Ones 300; S1.Zeros 300; S1.Ones 300 ]
    ; "1010... in 999 blocks", s1_alternating 999
    ; "0101... in 1000 blocks", s1_alternating 1000
    ]
    @ List.init 40 (fun i -> Printf.sprintf "random sample %d" i, random ())
  in
  all_of
    (t "a hundred incs, then two hundred decs, each the blocks the model gives")
    (fun note ->
       List.iter
         (fun (what, x) ->
           let rec go step x bits =
             if step < 300
             then (
               let op, f, model =
                 if step < 100 then "inc", S1.inc, inc_bits else "dec", S1.dec, dec_bits
               in
               let want_bits = model bits in
               let want = blocks_of_bits want_bits in
               match f x with
               | r when r = want -> go (step + 1) r want_bits
               | _ -> note (Printf.sprintf "%s, step %d, %s: wrong blocks" what step op)
               | exception e ->
                 note
                   (Printf.sprintf
                      "%s, step %d, %s raised %s"
                      what
                      step
                      op
                      (Printexc.to_string e)))
           in
           go 0 x (bits_of_blocks x))
         samples)
;;

(* O(1) worst case: one budget whatever the size. An operation here rebuilds at most a few
   blocks at the front, each a box and a list cell, some 20 words at the dearest; twice
   what one digit gets elsewhere leaves room for that, and a carry that went digit by
   digit, or a pass over every block, is out by a factor of a hundred and more at the
   sizes below. *)
let flat_budget = 2.0 *. per_digit

(* Each call on the clock by itself, inputs made beforehand; the dearest, and what it was. *)
let dearest_call calls =
  let dearest = ref (0.0, "") in
  List.iter
    (fun (what, f) ->
      match cost f with
      | _, c -> if c > fst !dearest then dearest := c, what
      | exception e -> dearest := infinity, what ^ " raised " ^ Printexc.to_string e)
    calls;
  !dearest
;;

let within_flat_budget name (c, what) =
  let fine = c <= flat_budget in
  check
    (Printf.sprintf
       "%s: the dearest is %s at %.0f words, budget %.0f whatever the size"
       name
       what
       c
       flat_budget)
    fine;
  fine
;;

let test_seg1_costs k =
  Random.init k;
  let run = [ S1.Ones k ]
  and power = [ S1.Zeros k; S1.Ones 1 ]
  and three = [ S1.Ones k; S1.Zeros k; S1.Ones k ]
  and four = [ S1.Zeros k; S1.Ones k; S1.Zeros k; S1.Ones k ]
  and odd = s1_alternating ((2 * k) - 1)
  and even = s1_alternating (2 * k)
  and random = s1_random k 8 in
  let calls =
    [ ("inc of 1^k", fun () -> S1.inc run)
    ; ("dec of 0^k 1", fun () -> S1.dec power)
    ; ("inc of 1^k 0^k 1^k", fun () -> S1.inc three)
    ; ("dec of 1^k 0^k 1^k", fun () -> S1.dec three)
    ; ("inc of 0^k 1^k 0^k 1^k", fun () -> S1.inc four)
    ; ("dec of 0^k 1^k 0^k 1^k", fun () -> S1.dec four)
    ; ("inc of 1010... in 2k - 1 blocks", fun () -> S1.inc odd)
    ; ("dec of 1010... in 2k - 1 blocks", fun () -> S1.dec odd)
    ; ("inc of 0101... in 2k blocks", fun () -> S1.inc even)
    ; ("dec of 0101... in 2k blocks", fun () -> S1.dec even)
    ; ("inc of k random blocks", fun () -> S1.inc random)
    ; ("dec of k random blocks", fun () -> S1.dec random)
    ]
  in
  within_flat_budget
    (Printf.sprintf "SegmentedRepresentationOne, inc and dec, k=%d" k)
    (dearest_call calls)
;;

(* What is wrong with the shape of a numeral, if anything. Block by block: a length is
   never spelled out, so a numeral that came back wrong cannot run away with memory. *)
let s2_fault ds =
  let rec go below prev = function
    | [] -> if prev = Some S2.Zero then Some "it ends in a ZERO" else None
    | S2.Ones i :: _ when i <= 0 -> Some (Printf.sprintf "a block of %d ONEs" i)
    | S2.Ones _ :: _
      when match prev with
           | Some (S2.Ones _) -> true
           | _ -> false -> Some "two blocks of ONEs side by side"
    | (S2.Ones _ as d) :: ds -> go below (Some d) ds
    | S2.Two :: _ when below <> Some S2.Zero ->
      Some "a TWO whose last digit below that is not a one is not a ZERO"
    | d :: ds -> go (Some d) (Some d) ds
  in
  go None None ds
;;

let s2_length ds =
  List.fold_left
    (fun n d ->
      n
      +
      match d with
      | S2.Ones i -> i
      | _ -> 1)
    0
    ds
;;

(* The bits of the number a numeral stands for, carrying each TWO up. *)
let bits_of_s2 ds =
  let digits =
    List.concat_map
      (function
        | S2.Zero -> [ 0 ]
        | S2.Two -> [ 2 ]
        | S2.Ones i -> List.init i (fun _ -> 1))
      ds
  in
  let rec carry c = function
    | [] -> if c = 0 then [] else [ c ]
    | d :: ds -> ((d + c) mod 2) :: carry ((d + c) / 2) ds
  in
  carry 0 digits
;;

(* Merges runs of ones into blocks: a digit list as a numeral. *)
let s2_of_digits ds =
  List.fold_right
    (fun d acc ->
      match d, acc with
      | 0, _ -> S2.Zero :: acc
      | 2, _ -> S2.Two :: acc
      | _, S2.Ones i :: acc -> S2.Ones (i + 1) :: acc
      | _, _ -> S2.Ones 1 :: acc)
    ds
    []
;;

let string_of_s2 = function
  | [] -> "[]"
  | ds ->
    String.concat
      " "
      (List.map
         (function
           | S2.Zero -> "0"
           | S2.Two -> "2"
           | S2.Ones 1 -> "1"
           | S2.Ones i -> Printf.sprintf "1^%d" i)
         ds)
;;

(* Why [r] is not inc of [x], if it is not. A regular numeral of d digits stands for less
   than 2^(d+1) - 1 and one of d + 2 for at least 2^(d+1), so a longer result has the
   wrong value; that is checked first, and the digits spelled out only after. *)
let s2_inc_fault x r =
  match s2_fault r with
  | Some why -> Some why
  | None ->
    if s2_length r > s2_length x + 1
    then Some (Printf.sprintf "%d digits from %d" (s2_length r) (s2_length x))
    else if bits_of_s2 r <> inc_bits (bits_of_s2 x)
    then Some "the wrong number"
    else None
;;

(* Every regular numeral of exactly k digits. *)
let rec digit_strings k =
  if k = 0
  then [ [] ]
  else List.concat_map (fun ds -> [ 0 :: ds; 1 :: ds; 2 :: ds ]) (digit_strings (k - 1))
;;

let regular_numerals k =
  List.filter_map
    (fun ds ->
      let x = s2_of_digits ds in
      if s2_fault x = None then Some x else None)
    (digit_strings k)
;;

(* A numeral in a failure message, unless it is too long to read. *)
let show_s2 ds =
  if List.length ds <= 40
  then string_of_s2 ds
  else Printf.sprintf "%d blocks" (List.length ds)
;;

(* incs from [x], [steps] of them, stopping at the first wrong one. *)
let s2_chain note what steps x =
  let rec go step x =
    if step < steps
    then (
      match S2.inc x with
      | r ->
        (match s2_inc_fault x r with
         | None -> go (step + 1) r
         | Some why ->
           note
             (Printf.sprintf
                "%s, inc number %d gives %s: %s"
                what
                (step + 1)
                (show_s2 r)
                why))
      | exception e ->
        note
          (Printf.sprintf
             "%s, inc number %d raised %s"
             what
             (step + 1)
             (Printexc.to_string e)))
  in
  go 0 x
;;

let test_seg2_contract () =
  let t label = "SegmentedRepresentationTwo: " ^ label in
  all_of (t "inc of every regular numeral of up to 10 digits") (fun note ->
    for k = 0 to 10 do
      List.iter (fun x -> s2_chain note (string_of_s2 x) 1 x) (regular_numerals k)
    done);
  all_of (t "every number up to 2^16, counted up from zero") (fun note ->
    s2_chain note "from zero" (1 lsl 16) [])
;;

(* Groups of the invariant, 0*1 and 0+1*2, at random, with runs of up to [longest] ONEs. *)
let s2_random groups longest =
  s2_of_digits
    (List.concat
       (List.init groups (fun _ ->
          if Random.bool ()
          then List.init (Random.int 4) (fun _ -> 0) @ [ 1 ]
          else
            List.init (1 + Random.int 3) (fun _ -> 0)
            @ List.init (Random.int (longest + 1)) (fun _ -> 1)
            @ [ 2 ])))
;;

let test_seg2_long () =
  let t label = "SegmentedRepresentationTwo, long numerals: " ^ label in
  Random.init 20260929;
  let samples =
    [ "1^1000", [ S2.Ones 1000 ]
    ; "0 1^1000 2 1^1000", [ S2.Zero; S2.Ones 1000; S2.Two; S2.Ones 1000 ]
    ; "1^1000 0 2", [ S2.Ones 1000; S2.Zero; S2.Two ]
    ; "0202... in 1000 blocks", List.concat (List.init 500 (fun _ -> [ S2.Zero; S2.Two ]))
    ; ( "0101... in 1000 blocks"
      , List.concat (List.init 500 (fun _ -> [ S2.Zero; S2.Ones 1 ])) )
    ]
    @ List.init 30 (fun i ->
      Printf.sprintf "random sample %d" i, s2_random (5 + Random.int 35) 200)
  in
  all_of (t "a hundred incs from each") (fun note ->
    List.iter (fun (what, x) -> s2_chain note what 100 x) samples)
;;

let test_seg2_costs k =
  Random.init k;
  let run = [ S2.Ones k ]
  and behind = [ S2.Zero; S2.Ones k; S2.Two; S2.Ones k ]
  and below = [ S2.Ones k; S2.Zero; S2.Two ]
  and twos = List.concat (List.init k (fun _ -> [ S2.Zero; S2.Two ]))
  and ones = List.concat (List.init k (fun _ -> [ S2.Zero; S2.Ones 1 ]))
  and random = s2_random k 8 in
  let calls =
    [ ("inc of 1^k", fun () -> S2.inc run)
    ; ("inc of 0 1^k 2 1^k", fun () -> S2.inc behind)
    ; ("inc of 1^k 0 2", fun () -> S2.inc below)
    ; ("inc of (0 2)^k", fun () -> S2.inc twos)
    ; ("inc of (0 1)^k", fun () -> S2.inc ones)
    ; ("inc of k random groups", fun () -> S2.inc random)
    ]
  in
  within_flat_budget
    (Printf.sprintf "SegmentedRepresentationTwo, inc, k=%d" k)
    (dearest_call calls)
;;

(* Counting up from zero, every inc on the clock; stops at a result the shape check or its
   length gives away, which the contract has already failed. *)
let test_seg2_counting_cost () =
  let n = 1 lsl 17 in
  let dearest = ref (0.0, "") in
  let rec go i x =
    if i < n
    then (
      match cost (fun () -> S2.inc x) with
      | r, c ->
        if c > fst !dearest then dearest := c, Printf.sprintf "inc of %d" i;
        if s2_fault r = None && s2_length r <= s2_length x + 1
        then go (i + 1) r
        else dearest := infinity, Printf.sprintf "inc of %d, a malformed result" i
      | exception e ->
        dearest := infinity, Printf.sprintf "inc of %d raised %s" i (Printexc.to_string e))
  in
  go 0 [];
  within_flat_budget
    (Printf.sprintf "SegmentedRepresentationTwo, counting from 0 to %d" n)
    !dearest
;;

(* For each representation, what it returns first; only then what it costs. *)
let test_segmented () =
  section "Segmented binary numbers (section 9.2.4)";
  let before = !failures in
  test_seg1_contract ();
  test_seg1_long ();
  if !failures > before
  then
    Printf.printf
      "  SKIP  SegmentedRepresentationOne: costs -- the checks above do not hold\n"
  else if test_seg1_costs 1_000
  then ignore (test_seg1_costs 100_000)
  else
    Printf.printf
      "  SKIP  SegmentedRepresentationOne: costs at k=100000 -- over budget at k=1000\n";
  let before = !failures in
  test_seg2_contract ();
  test_seg2_long ();
  if !failures > before
  then
    Printf.printf
      "  SKIP  SegmentedRepresentationTwo: costs -- the checks above do not hold\n"
  else if test_seg2_counting_cost () && test_seg2_costs 1_000
  then ignore (test_seg2_costs 100_000)
  else
    Printf.printf
      "  SKIP  SegmentedRepresentationTwo: costs at k=100000 -- over budget before\n"
;;

(* ------------------------------------------------------------------- runner *)

(* A regression can make a function raise where the test did not expect it. Report that as
   a failure and carry on rather than hiding it. *)
let run name f =
  match f () with
  | () -> ()
  | exception e ->
    incr failures;
    Printf.printf "  FAIL  %s: unexpected exception %s\n" name (Printexc.to_string e)
;;

let () =
  run "BinaryRandomAccessList" test_binary;
  run "drop" test_drop;
  run "create" test_create;
  run "SparseBinaryRandomAccessList" test_sparse;
  run "sparse drop" test_sparse_drop;
  run "sparse create" test_sparse_create;
  run "Zeroless" test_zeroless;
  run "ZerolessBinaryRandomAccessList" test_zeroless_list;
  run "ZerolessRedundantBinaryRandomAccessList" test_redundant;
  run "ScheduledZerolessRedundantBinaryRandomAccessList" test_scheduled;
  run "Segmented binary numbers" test_segmented;
  Printf.printf "\n%d checks, %d failures\n\n" !checks !failures;
  if !failures > 0 then exit 1
;;
