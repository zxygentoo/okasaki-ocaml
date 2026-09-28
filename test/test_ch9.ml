(* Tests for Chapter 9: the binary random-access list of Figure 9.6 (section 9.2.1), the
   drop of Exercise 9.1, the create of Exercise 9.2, the sparse list of Exercise 9.3 with
   its own drop and create, and the zeroless numbers and list of Exercises 9.4 and 9.5,
   each with its own preamble further down. Plain OCaml, no test framework, matching the
   earlier chapters.

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
  Printf.printf "\n%d checks, %d failures\n\n" !checks !failures;
  if !failures > 0 then exit 1
;;
