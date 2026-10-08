(* Tests for Chapter 9: the binary random-access list of Figure 9.6 (section 9.2.1), the
   drop of Exercise 9.1, the create of Exercise 9.2, the sparse list of Exercise 9.3 with
   its own drop and create, the zeroless numbers and list of Exercises 9.4 and 9.5, and
   the zeroless redundant list of Exercise 9.9 and its scheduled form of Exercise 9.10,
   the segmented binary numbers of section 9.2.4, the segmented binomial heap of Exercise
   9.11, the segmented numbers with digits 0 to 4 of Exercise 9.12, the random-access
   list over them of Exercise 9.13, the skew binary random-access list of Figure 9.7, the
   Hood-Melville queue over it of Exercise 9.14, the skew binomial heap of Figure 9.8
   (section 9.3) and the heap with delete of Exercise 9.16 over it, each with its own
   preamble further down. Alcotest cases written in the checks of harness.ml, as in the
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
open Harness

(* [f], the operation [what], must refuse with Failure [msg]; [note] hears it if not. *)
let refused note what msg f =
  match f () with
  | _ -> note (what ^ " did not raise")
  | exception Failure m when m = msg -> ()
  | exception e -> note (what ^ " raised " ^ Printexc.to_string e)
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
      check_eq (t label) ~expect ~actual:(to_list (r ())) string_of_int_list
    in
    check (t "empty is empty") (R.is_empty R.empty);
    check (t "a singleton is not empty") (not (R.is_empty (R.cons 1 R.empty)));
    check_failure (t "head on empty raises") "head: empty list" (fun () -> R.head R.empty);
    check_failure (t "tail on empty raises") "tail: empty list" (fun () ->
      ignore (R.is_empty (R.tail R.empty)));
    check_failure (t "lookup on empty raises") "lookup: not found" (fun () ->
      R.lookup 0 R.empty);
    check_failure (t "update on empty raises") "update: not found" (fun () ->
      ignore (R.is_empty (R.update 0 1 R.empty)));
    (* A stack at the front. *)
    check_int
      (t "head is the element cons'ed last")
      ~expect:3
      ~actual:(R.head (R.cons 3 (R.cons 2 (R.cons 1 R.empty))));
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
        refused (note n) "lookup one past the end" "lookup: not found" (fun () ->
          R.lookup n r);
        refused (note n) "lookup at -1" "lookup: not found" (fun () -> R.lookup (-1) r)
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
          refused (note n) "head" "head: empty list" (fun () -> R.head r);
          refused (note n) "tail" "tail: empty list" (fun () -> R.tail r);
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
        refused (note n) "update at -1" "update: not found" (fun () -> R.update (-1) 0 r);
        refused (note n) "update one past the end" "update: not found" (fun () ->
          R.update n 0 r)
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
    let versions = List.init 40 (fun i -> of_list (upto i)) in
    List.iter
      (fun v ->
         ignore (R.cons 99 v);
         if not (R.is_empty v)
         then (
           ignore (R.tail v);
           ignore (R.update 0 99 v)))
      versions;
    let stale =
      List.mapi
        (fun i v -> if to_list v = upto i && lookups i v = upto i then 0 else 1)
        versions
      |> List.fold_left ( + ) 0
    in
    check_int (t "every earlier version stays correct") ~expect:0 ~actual:stale
  ;;

  (* ------------------------------------------ every operation on its own clock *)

  (* Every version of a build by cons, each cons on the clock; then head from every
     version, tail down the whole drain, and lookup and update at every index of the full
     list. The dearest of each is what the bound is about. [stack] is the budget for cons,
     head and tail: a constant per digit, unless a list promises better. *)
  let run_costs_at ?(stack = budget) name n =
    let t label = Printf.sprintf "%s: %s" name label in
    let within budget label (k, c) =
      check
        (t
           (Printf.sprintf
              "%s, dearest is #%d at %.0f words, n=%d, budget %.0f"
              label
              k
              c
              n
              (budget n)))
        (c <= budget n)
    in
    let v = Array.make (n + 1) R.empty
    and dear = ref (0, 0.0) in
    for i = 1 to n do
      let r, c = cost (fun () -> R.cons i v.(i - 1)) in
      v.(i) <- r;
      if c > snd !dear then dear := i, c
    done;
    within stack "cons, at every size of a build" !dear;
    let dear = ref (0, 0.0)
    and sum = ref 0 in
    for k = 1 to n do
      let x, c = cost (fun () -> R.head v.(k)) in
      sum := !sum + x;
      if c > snd !dear then dear := k, c
    done;
    within stack "head, at every size of a build" !dear;
    let r = ref v.(n)
    and dear = ref (0, 0.0) in
    for i = 1 to n do
      let r', c = cost (fun () -> R.tail !r) in
      r := r';
      if c > snd !dear then dear := i, c
    done;
    ignore (Sys.opaque_identity !r);
    within stack "tail, at every size of a drain" !dear;
    let full = v.(n) in
    let dear = ref (0, 0.0) in
    for i = 0 to n - 1 do
      let x, c = cost (fun () -> R.lookup i full) in
      sum := !sum + x;
      if c > snd !dear then dear := i, c
    done;
    ignore (Sys.opaque_identity !sum);
    within budget "lookup, at every index" !dear;
    let dear = ref (0, 0.0) in
    for i = 0 to n - 1 do
      let r', c = cost (fun () -> R.update i 0 full) in
      ignore (Sys.opaque_identity r');
      if c > snd !dear then dear := i, c
    done;
    within budget "update, at every index" !dear
  ;;

  (* O(log n) worst-case, at two sizes a hundred times apart. The small size comes first
     and guards the large one, as everywhere in these files: an operation that is secretly
     linear makes the large run quadratic, and that is not a failure but a hang. A check
     that fails at n=1000 ends the case instead. *)
  let run_costs ?stack name =
    run_costs_at ?stack name 1_000;
    run_costs_at ?stack name 100_000
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

(* What a list costs means nothing until it behaves like one: the contract comes first,
   here and in every case below, and the case ends there if it does not hold. *)
let test_binary () =
  Binary.run_contract "BinaryRandomAccessList";
  test_guard ();
  Binary.run_costs "BinaryRandomAccessList"
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
      check_eq (t label) ~expect ~actual:(to_list (r ())) string_of_int_list
    in
    eq "drop 0 of empty is empty" [] (fun () -> R.drop 0 R.empty);
    eq "drop 0 changes nothing" [ 1; 2; 3 ] (fun () -> R.drop 0 (of_list [ 1; 2; 3 ]));
    eq "drop 1 of two" [ 2 ] (fun () -> R.drop 1 (of_list [ 1; 2 ]));
    eq "drop 2 of two is empty" [] (fun () -> R.drop 2 (of_list [ 1; 2 ]));
    check
      (t "drop 2 of two is empty by is_empty too")
      (R.is_empty (R.drop 2 (of_list [ 1; 2 ])));
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
          let expect = List.drop k xs in
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
          let survivors = List.drop k xs in
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
                 if to_list (R.drop j r') <> List.drop (k + j) xs
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
             model := List.drop k !model);
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
      (List.drop 3 (upto 10))
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
      (99 :: List.drop 3 (upto 10))
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
    check
      (t
         (Printf.sprintf
            "drop, at every k of %d, dearest is k=%d at %.0f words, budget %.0f"
            n
            (fst !dear)
            (snd !dear)
            (budget n)))
      (snd !dear <= budget n)
  ;;

  let run_costs name =
    run_costs_at name 1_000;
    run_costs_at name 100_000
  ;;
end

module Binary_drop = Drop_tests (BinaryRandomAccessList)

let test_drop () =
  Binary_drop.run_contract "BinaryRandomAccessList.drop";
  Binary_drop.run_costs "BinaryRandomAccessList.drop"
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
      check_eq (t label) ~expect ~actual:(to_list (r ())) string_of_int_list
    in
    eq "create 0 is empty" [] (fun () -> R.create 0 7);
    check (t "create 0 is empty by is_empty too") (R.is_empty (R.create 0 7));
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
          refused (note n) "lookup one past the end" "lookup: not found" (fun () ->
            R.lookup n r)
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
           refused (note n) "update one past the end" "update: not found" (fun () ->
             R.update n 1 r)
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
             model := List.drop k !model);
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
    (* Persistence: a created list is a version like any other. Each check makes its own. *)
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
     about. *)
  let run_costs_at name n =
    let t label = Printf.sprintf "%s: %s" name label in
    let within label (k, c) =
      check
        (t
           (Printf.sprintf
              "%s, dearest is #%d at %.0f words, n=%d, budget %.0f"
              label
              k
              c
              n
              (budget n)))
        (c <= budget n)
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
    within "tail, at every size of a drain from a created list" !dear
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
              else if
                R.lookup (n - 1) r' <> 1
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
     that does not hold. *)
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
      (bad = None)
  ;;

  (* O(log n) worst-case: the sweep at n=1000, the ladder, and the sweep at n=100000, in
     that order, each reached only if the one before held. *)
  let run_costs name =
    run_costs_at name 1_000;
    run_ladder name;
    run_costs_at name 100_000
  ;;
end

module Binary_create = Create_tests (BinaryRandomAccessList)

let test_create () =
  Binary_create.run_contract "BinaryRandomAccessList.create";
  Binary_create.run_costs "BinaryRandomAccessList.create"
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
  Sparse.run_contract "SparseBinaryRandomAccessList";
  Sparse.run_costs "SparseBinaryRandomAccessList"
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
  Sparse_drop.run_contract "SparseBinaryRandomAccessList.drop";
  Sparse_drop.run_costs "SparseBinaryRandomAccessList.drop"
;;

let test_sparse_create () =
  Sparse_create.run_contract "SparseBinaryRandomAccessList.create";
  Sparse_create.run_costs "SparseBinaryRandomAccessList.create"
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
   is over budget. *)
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
                | _, c ->
                  see (Printf.sprintf "add %s %s" (string_of_z b) (string_of_z a)) c
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
    (over = None)
;;

(* Long families at k digits: each call on the clock by itself, inputs made beforehand. *)
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
  let c, what = dearest_call calls in
  check
    (Printf.sprintf
       "Zeroless, %d digits: the dearest of dec and add is %s at %.0f words, budget %.0f"
       k
       what
       c
       (digit_budget k))
    (c <= digit_budget k)
;;

(* Short numerals first, for what they are and then for what they cost; only then the long
   ones, which an add that is not linear in the digits would never finish. *)
let test_zeroless () =
  test_zeroless_contract ();
  test_zeroless_short_costs ();
  test_zeroless_long ();
  test_zeroless_long_costs 1_000;
  test_zeroless_long_costs 100_000
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
  let c = dearest () in
  check
    (Printf.sprintf "%s, dearest at %.0f words, budget %.0f whatever n" name c per_digit)
    (c <= per_digit)
;;

let test_zeroless_list () =
  Zeroless_list.run_contract "ZerolessBinaryRandomAccessList";
  Zeroless_list.run_costs "ZerolessBinaryRandomAccessList";
  test_zeroless_head_at 1_000;
  test_zeroless_head_at 100_000
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
    else Printf.sprintf "%s... (%d elements)" (string_of_int_list (List.take 10 l)) n
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
    check_failure (t "head on empty raises") "head: empty list" (fun () -> R.head R.empty);
    check_failure (t "tail on empty raises") "tail: empty list" (fun () ->
      ignore (R.is_empty (R.tail R.empty)));
    check_int
      (t "head is the element cons'ed last")
      ~expect:3
      ~actual:(R.head (R.cons 3 (R.cons 2 (R.cons 1 R.empty))));
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
          refused
            (fun why -> note (Printf.sprintf "n=%d: %s" n why))
            "head"
            "head: empty list"
            (fun () -> R.head r);
          refused
            (fun why -> note (Printf.sprintf "n=%d: %s" n why))
            "tail"
            "tail: empty list"
            (fun () -> R.tail r);
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

  let run_costs_at name k =
    List.iter
      (fun (what, f) ->
         let label = Printf.sprintf "%s: %s" name what in
         let c = mean f in
         check
           (Printf.sprintf
              "%s, %.1f words a cons or tail, budget %.0f"
              label
              c
              amortised_budget)
           (c <= amortised_budget))
      (sequences k)
  ;;

  (* The same budget at two sizes 128 times apart, the small one first, as everywhere in
     these files. *)
  let run_costs name =
    run_costs_at name 10;
    run_costs_at name 17
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

  let run_worst_costs_at name k =
    List.iter
      (fun (what, f) ->
         dearest := 0.0;
         dearest_at := "", 0;
         steps := 0;
         match f () with
         | () ->
           let op, i = !dearest_at in
           check
             (Printf.sprintf
                "%s: %s, the dearest is the %s at step %d, %.0f words, budget %.0f"
                name
                what
                op
                i
                !dearest
                worst_case_budget)
             (!dearest <= worst_case_budget)
         | exception e ->
           check
             (Printf.sprintf "%s: %s: raised %s" name what (Printexc.to_string e))
             false)
      (worst_sequences k)
  ;;

  let run_worst_costs name =
    run_worst_costs_at name 10;
    run_worst_costs_at name 17
  ;;
end

module Redundant = Lite_tests (ZerolessRedundantBinaryRandomAccessList (Okasaki.Ch4.Stream))

let test_redundant () =
  let name = "ZerolessRedundantBinaryRandomAccessList" in
  Redundant.run_contract name;
  Redundant.run_costs name
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
  Scheduled.run_contract name;
  Scheduled.run_worst_costs name
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

let within_flat_budget name (c, what) =
  check
    (Printf.sprintf
       "%s: the dearest is %s at %.0f words, budget %.0f whatever the size"
       name
       what
       c
       flat_budget)
    (c <= flat_budget)
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

(* A case for each representation: what it returns first, and only then what it costs, the
   large size last. *)
let test_seg1 () =
  test_seg1_contract ();
  test_seg1_long ();
  test_seg1_costs 1_000;
  test_seg1_costs 100_000
;;

let test_seg2 () =
  test_seg2_contract ();
  test_seg2_long ();
  test_seg2_counting_cost ();
  test_seg2_costs 1_000;
  test_seg2_costs 100_000
;;

(* ------------------------------------------ SegmentedBinomialHeap (Exercise 9.11) *)

(* Exercise 9.11 asks for binomial heaps extended with segmentation, "so that insert runs
   in O(1) worst-case time", over digits ZERO, ONES of a list of trees and TWO of two
   trees, and says: "Restore the invariant after a merge by eliminating all Twos."
   find_min, merge and delete_min keep the O(log n) worst case of the binomial heaps of
   section 3.2.

   The heap is abstract behind HEAP, so the contract is what a client sees: a drain by
   find_min and delete_min comes out sorted, with every element exactly once. It is
   checked on every size up to 64, on the merge of every pair of sizes up to 24, on the
   futures of one shared heap, and on a random trace of inserts, merges and delete_mins
   over earlier versions against a sorted list. Ties get their own check, with elements
   that the order calls equal but a tag tells apart: each has to come out exactly once,
   which holds only if delete_min takes out the very element find_min returned.

   A sorted drain cannot see a tree at the wrong rank: heap order survives any link, so a
   heap whose trees sit at the wrong positions still drains sorted. The shape is read
   through find_min instead, which compares every root but the first once. Two counts
   follow from the book. After n inserts into the empty heap, insert being the section's
   inc with trees, there is one tree per unit of the numeral inc reaches from zero, and
   SegmentedRepresentationTwo.inc says what that numeral is. After a merge of two
   non-empty heaps no TWO is left and the tree at rank r holds 2^r elements, so there is
   exactly one tree per 1 bit of n. A tree at the wrong rank shows up there as soon as it
   is deleted: the digits then stop adding up to n, and the next merge's count is off.

   Then the clocks, every operation on them by itself: comparisons, through a counting
   element type, which see every link, and words, which see everything else. fixup links
   at most once, so an insert is held to one comparison and to the flat budget in words,
   from every heap and at every size; the dearest case is the all-ones heap a merge
   leaves, one block of k trees, where the insert of section 3.2 carries k times.
   find_min, merge and delete_min are held to 6L + 6 comparisons and 160L + 160 words, L =
   log2 (n + 1), about twice what the dearest of them spends. That the probe can tell O(1)
   from O(log n) is checked on Figure 3.4's heap. *)

module SH = SegmentedBinomialHeap (Counting_int)

(* Trees in [h]: find_min compares every root but the first once. *)
let sh_trees h = if SH.is_empty h then 0 else count_only (fun () -> SH.find_min h) + 1

(* ----------------------------------------------------------------- contract *)

(* Order by key only: the tag tells equal elements apart. *)
module Keyed = struct
  type t = int * int

  let eq (a, _) (b, _) = a = b
  let lt (a, _) (b, _) = a < b
  let leq (a, _) (b, _) = a <= b
end

(* The contract, written for the segmented heap and run on the skew heap of Figure 9.8
   further down as well: [H] over ints, [K] over keyed pairs for the ties. *)
module Heap_contract
    (H : HEAP with type Element.t = int)
    (K : HEAP with type Element.t = int * int) =
struct
  let of_list xs = List.fold_left (fun h x -> H.insert x h) H.empty xs
  let drain h = drain_with ~is_empty:H.is_empty ~head:H.find_min ~tail:H.delete_min h

  let run name =
    let t label = name ^ ": " ^ label in
    check (t "empty is empty") (H.is_empty H.empty);
    check (t "a singleton is not empty") (not (H.is_empty (H.insert 1 H.empty)));
    check_failure (t "find_min of the empty heap") "find_min: empty heap" (fun () ->
      H.find_min H.empty);
    check_failure (t "delete_min of the empty heap") "delete_min: empty heap" (fun () ->
      H.delete_min H.empty);
    let drains_to note what want h =
      match drain h with
      | out when out = want -> ()
      | out -> note (Printf.sprintf "%s drains to %s" what (string_of_int_list out))
      | exception e -> note (Printf.sprintf "%s raised %s" what (Printexc.to_string e))
    in
    Random.init 20260930;
    all_of
      (t "every size up to 64, ascending, descending and random, drains sorted")
      (fun note ->
         for n = 0 to 64 do
           List.iter
             (fun (kind, xs) ->
                drains_to
                  note
                  (Printf.sprintf "%d %s inserts" n kind)
                  (List.sort compare xs)
                  (of_list xs))
             [ "ascending", upto n
             ; "descending", List.rev (upto n)
             ; "random", List.init n (fun _ -> Random.int 16)
             ]
         done);
    all_of
      (t "the merge of every pair of sizes up to 24 drains to the sorted union")
      (fun note ->
         for a = 0 to 24 do
           for b = 0 to 24 do
             let xs = List.init a (fun _ -> Random.int 16)
             and ys = List.init b (fun _ -> Random.int 16) in
             drains_to
               note
               (Printf.sprintf "the merge of %d and %d" a b)
               (List.sort compare (xs @ ys))
               (H.merge (of_list xs) (of_list ys))
           done
         done);
    all_of (t "four futures of one heap, and the heap itself, untouched") (fun note ->
      let h = of_list [ 5; 3; 8; 1 ] in
      let a = H.insert 0 h
      and b = H.insert 4 h
      and c = H.delete_min h
      and d = H.merge h h in
      drains_to note "insert 0" [ 0; 1; 3; 5; 8 ] a;
      drains_to note "insert 4" [ 1; 3; 4; 5; 8 ] b;
      drains_to note "delete_min" [ 3; 5; 8 ] c;
      drains_to note "merge with itself" [ 1; 1; 3; 3; 5; 5; 8; 8 ] d;
      drains_to note "the heap" [ 1; 3; 5; 8 ] h);
    all_of
      (t
         "a random trace of 6000 inserts, merges and delete_mins over earlier versions, \
          against a sorted list")
      (fun note ->
         let n = 6_000 in
         let v = Array.make (n + 1) H.empty
         and model = Array.make (n + 1) []
         and size = Array.make (n + 1) 0 in
         for i = 1 to n do
           let p = Random.int i
           and q = Random.int i in
           let what, h, m, s =
             match Random.int 4 with
             | 2 when size.(p) + size.(q) <= 600 ->
               ( "merge"
               , H.merge v.(p) v.(q)
               , List.merge compare model.(p) model.(q)
               , size.(p) + size.(q) )
             | 3 when size.(p) > 0 ->
               "delete_min", H.delete_min v.(p), List.tl model.(p), size.(p) - 1
             | _ ->
               let x = Random.int 1000 in
               ( "insert"
               , H.insert x v.(p)
               , List.merge compare [ x ] model.(p)
               , size.(p) + 1 )
           in
           v.(i) <- h;
           model.(i) <- m;
           size.(i) <- s;
           match m with
           | [] ->
             if not (H.is_empty h) then note (Printf.sprintf "%s %d is not empty" what i)
           | x :: _ ->
             if H.is_empty h
             then note (Printf.sprintf "%s %d is empty" what i)
             else if H.find_min h <> x
             then
               note (Printf.sprintf "%s %d: find_min %d, want %d" what i (H.find_min h) x)
         done;
         for i = 0 to n do
           if i mod 200 = 0
           then drains_to note (Printf.sprintf "version %d" i) model.(i) v.(i)
         done);
    all_of
      (t "equal keys, distinct tags: every element comes out exactly once, in order")
      (fun note ->
         let sk_of_list = List.fold_left (fun h x -> K.insert x h) K.empty in
         for n = 1 to 80 do
           let xs = List.init n (fun tag -> Random.int 4, tag) in
           let half = List.take (n / 2) xs
           and rest = List.drop (n / 2) xs in
           List.iter
             (fun (how, h) ->
                match
                  drain_with ~is_empty:K.is_empty ~head:K.find_min ~tail:K.delete_min h
                with
                | out ->
                  let keys = List.map fst out in
                  if List.sort compare out <> List.sort compare xs
                  then note (Printf.sprintf "%d %s: not every element once" n how)
                  else if keys <> List.sort compare keys
                  then note (Printf.sprintf "%d %s: out of order" n how)
                | exception e ->
                  note (Printf.sprintf "%d %s raised %s" n how (Printexc.to_string e)))
             [ "inserts", sk_of_list xs
             ; "merged halves", K.merge (sk_of_list half) (sk_of_list rest)
             ]
         done)
  ;;
end

module SK = SegmentedBinomialHeap (Keyed)
module SH_contract = Heap_contract (SH) (SK)

(* -------------------------------------------------------------------- shape *)

let test_sh_shape () =
  let t label = "SegmentedBinomialHeap, shape: " ^ label in
  let module N = SegmentedRepresentationTwo in
  let units =
    List.fold_left
      (fun s -> function
         | N.Zero -> s
         | N.Two -> s + 2
         | N.Ones i -> s + i)
      0
  in
  all_of
    (t
       "after n inserts from empty, one tree per unit of the numeral inc reaches, n up \
        to 2000")
    (fun note ->
       let h = ref SH.empty
       and num = ref [] in
       for n = 1 to 2000 do
         h := SH.insert n !h;
         num := N.inc !num;
         let got = sh_trees !h
         and want = units !num in
         if got <> want then note (Printf.sprintf "n=%d: %d trees, want %d" n got want)
       done);
  all_of
    (t
       "after every merge of two non-empty heaps in a random trace of 6000 operations, \
        one tree per 1 bit of n")
    (fun note ->
       Random.init 20260930;
       let n = 6_000 in
       let v = Array.make (n + 1) SH.empty
       and size = Array.make (n + 1) 0 in
       for i = 1 to n do
         let p = Random.int i
         and q = Random.int i in
         match Random.int 4 with
         | 2 when size.(p) > 0 && size.(q) > 0 && size.(p) + size.(q) <= 1 lsl 20 ->
           let s = size.(p) + size.(q) in
           v.(i) <- SH.merge v.(p) v.(q);
           size.(i) <- s;
           let got = sh_trees v.(i) in
           if got <> popcount s
           then
             note
               (Printf.sprintf
                  "merge %d, of %d and %d: %d trees, want %d"
                  i
                  size.(p)
                  size.(q)
                  got
                  (popcount s))
         | 3 when size.(p) > 0 ->
           v.(i) <- SH.delete_min v.(p);
           size.(i) <- size.(p) - 1
         | _ ->
           v.(i) <- SH.insert i v.(p);
           size.(i) <- size.(p) + 1
       done)
;;

(* ------------------------------------------- every operation on its own clock *)

(* The budgets a heap's operations are held to: for an insert two constants, for a query
   (find_min, merge, delete_min) two functions of L = log2 (n + 1). *)
module type HEAP_BUDGETS = sig
  val insert_comparisons : float
  val insert_words : float
  val query_comparisons : float -> float
  val query_words : float -> float
end

(* The clocks, written for the segmented heap and run on the skew heap further down as
   well: comparisons through a counting element type, which see every link, and words. *)
module Heap_clocks (H : HEAP with type Element.t = int) (B : HEAP_BUDGETS) = struct
  let of_list xs = List.fold_left (fun h x -> H.insert x h) H.empty xs

  (* The dearest operation of a run, as a fraction of its budget: within its bound when the
     fraction is at most one. *)
  let dearer (ratio, what) ~at ~op ~size (c, w) =
    let cb, wb =
      if op = "insert"
      then B.insert_comparisons, B.insert_words
      else (
        let l = log2 (size + 1) in
        B.query_comparisons l, B.query_words l)
    in
    let r = Float.max (c /. cb) (w /. wb) in
    if r > ratio
    then
      ( r
      , Printf.sprintf
          "%s #%d on %d elements, %.0f comparisons and %.0f words (budget %.0f, %.0f)"
          op
          at
          size
          c
          w
          cb
          wb )
    else ratio, what
  ;;

  let within name (ratio, what) =
    check (Printf.sprintf "%s: the dearest is %s" name what) (ratio <= 1.0)
  ;;

  type op =
    | Insert of int
    | Find_min
    | Delete_min

  (* Runs [ops] from the empty heap, every operation on the clocks by itself; the dearest
     insert and the dearest query. *)
  let run ops =
    let h = ref H.empty
    and size = ref 0
    and sum = ref 0
    and ins = ref (0.0, "nothing")
    and query = ref (0.0, "nothing") in
    Array.iteri
      (fun i op ->
         match op with
         | Insert x ->
           let h', cw = spent (fun () -> H.insert x !h) in
           ins := dearer !ins ~at:i ~op:"insert" ~size:!size cw;
           h := h';
           incr size
         | Find_min ->
           let x, cw = spent (fun () -> H.find_min !h) in
           query := dearer !query ~at:i ~op:"find_min" ~size:!size cw;
           sum := !sum + x
         | Delete_min ->
           let h', cw = spent (fun () -> H.delete_min !h) in
           query := dearer !query ~at:i ~op:"delete_min" ~size:!size cw;
           h := h';
           decr size)
      ops;
    ignore (Sys.opaque_identity !sum);
    !ins, !query
  ;;

  (* Each insert followed by a find_min, then a drain. *)
  let build_then_drain xs =
    let n = Array.length xs in
    Array.init (3 * n) (fun i ->
      if i < 2 * n
      then if i mod 2 = 0 then Insert xs.(i / 2) else Find_min
      else Delete_min)
  ;;

  let sequences n =
    Random.init n;
    [ ( "n ascending inserts, each then a find_min, then n delete_mins"
      , build_then_drain (Array.init n Fun.id) )
    ; ( "n random inserts, each then a find_min, then n delete_mins"
      , build_then_drain (Array.init n (fun _ -> Random.int 1_000_000)) )
    ; ( "n equal inserts, each then a find_min, then n delete_mins"
      , build_then_drain (Array.make n 7) )
    ; ( "insert then delete_min at a steady size of 1000, n times over"
      , Array.init
          (1000 + (2 * n))
          (fun i ->
             if i < 1000 then Insert i else if i mod 2 = 0 then Insert i else Delete_min)
      )
    ]
  ;;

  (* Every sequence against both budgets at n. *)
  let test_sequences name n =
    List.iter
      (fun (what, ops) ->
         let ins, query = run ops in
         let name = Printf.sprintf "%s, n=%d, %s" name n what in
         within (name ^ ", insert") ins;
         within (name ^ ", queries") query)
      (sequences n)
  ;;

  (* The all-ones heap of 2^k - 1 elements, as a merge leaves it, one block of k trees: the
     insert of section 3.2 would carry k times here. *)
  let test_all_ones name =
    let d = ref (0.0, "nothing") in
    for k = 1 to 17 do
      let h = H.merge (of_list (upto ((1 lsl k) - 2))) (H.insert (-1) H.empty) in
      let _, cw = spent (fun () -> H.insert (-2) h) in
      d := dearer !d ~at:k ~op:"insert" ~size:((1 lsl k) - 1) cw
    done;
    within
      (name ^ ": insert into the heap of 2^k - 1 elements a merge leaves, k = 1..17")
      !d
  ;;

  (* n singletons merged pairwise, every merge on the clocks against the heap it makes, and
     the result drained. *)
  let test_merges name n =
    let d = ref (0.0, "nothing")
    and at = ref 0 in
    let rec round = function
      | (a, sa) :: (b, sb) :: rest ->
        incr at;
        let m, cw = spent (fun () -> H.merge a b) in
        d := dearer !d ~at:!at ~op:"merge" ~size:(sa + sb) cw;
        (m, sa + sb) :: round rest
      | l -> l
    in
    let rec go = function
      | [ (h, _) ] -> h
      | [] -> H.empty
      | l -> go (round l)
    in
    let h = ref (go (List.init n (fun i -> H.insert i H.empty, 1))) in
    for i = 1 to n do
      let h', cw = spent (fun () -> H.delete_min !h) in
      d := dearer !d ~at:i ~op:"delete_min" ~size:(n - i + 1) cw;
      h := h'
    done;
    within (Printf.sprintf "%s: %d singletons merged pairwise, then drained" name n) !d
  ;;

  (* A random trace over earlier versions, each operation on the clocks against the heap it
     is applied to or makes. Sizes are tracked, since merging versions of versions makes
     heaps far larger than the trace is long. *)
  let test_versions name =
    let n = 20_000 in
    Random.init 20260930;
    let v = Array.make (n + 1) H.empty
    and size = Array.make (n + 1) 0
    and ins = ref (0.0, "nothing")
    and query = ref (0.0, "nothing") in
    for i = 1 to n do
      let p = Random.int i
      and q = Random.int i in
      match Random.int 4 with
      | 2 when size.(p) + size.(q) <= 1 lsl 40 ->
        let h, cw = spent (fun () -> H.merge v.(p) v.(q)) in
        v.(i) <- h;
        size.(i) <- size.(p) + size.(q);
        query := dearer !query ~at:i ~op:"merge" ~size:size.(i) cw
      | 3 when size.(p) > 0 ->
        let h, cw = spent (fun () -> H.delete_min v.(p)) in
        query := dearer !query ~at:i ~op:"delete_min" ~size:size.(p) cw;
        v.(i) <- h;
        size.(i) <- size.(p) - 1
      | _ ->
        let h, cw = spent (fun () -> H.insert i v.(p)) in
        ins := dearer !ins ~at:i ~op:"insert" ~size:size.(p) cw;
        v.(i) <- h;
        size.(i) <- size.(p) + 1
    done;
    ignore (Sys.opaque_identity v);
    let name = name ^ ": a random trace of 20000 operations over earlier versions" in
    within (name ^ ", insert") !ins;
    within (name ^ ", merge and delete_min") !query
  ;;
end

(* fixup links at most once, so an insert is one comparison; the queries get 6L + 6 and
   160L + 160, about twice what the dearest of them spends. *)
module SH_clocks =
  Heap_clocks
    (SH)
    (struct
      let insert_comparisons = 1.0
      let insert_words = flat_budget
      let query_comparisons l = (6. *. l) +. 6.
      let query_words l = (160. *. l) +. 160.
    end)

(* Whether the probe can tell O(1) from O(log n): Figure 3.4's insert into the all-ones
   heap of 2^16 - 1 links 16 times on the spot, and the same clock must see every link. *)
module Strict_heap = Okasaki.Ch3.BinomialHeap (Counting_int)

let test_sh_guard () =
  let k = 16 in
  let h =
    List.fold_left
      (fun h x -> Strict_heap.insert x h)
      Strict_heap.empty
      (upto ((1 lsl k) - 1))
  in
  let c = count_only (fun () -> Strict_heap.insert (-1) h) in
  check
    (Printf.sprintf
       "guard: the same probe sees Figure 3.4's insert into the all-ones heap of 2^%d - \
        1 link %d times"
       k
       c)
    (c >= k)
;;

(* What it returns, then its shape, then its costs, the large size only after the small. *)
let test_segmented_heap () =
  let name = "SegmentedBinomialHeap" in
  SH_contract.run name;
  test_sh_shape ();
  test_sh_guard ();
  SH_clocks.test_all_ones name;
  SH_clocks.test_sequences name 1_000;
  SH_clocks.test_sequences name 100_000;
  SH_clocks.test_merges name 1_000;
  SH_clocks.test_merges name 100_000;
  SH_clocks.test_versions name
;;

(* ------------------ segmented redundant numbers, digits 0 to 4 (Exercise 9.12) *)

(* Exercise 9.12 asks for segmented, redundant binary numbers with both inc and dec in
   O(1) worst-case time, "by allowing each digit to be 0, 1, 2, 3, or 4, where 0 and 4 are
   red, 1 and 3 are yellow, and 2 is green". p.130 gives the rest of the recipe: "The
   invariant is that the last non-yellow level before a red level is always green", a
   fixup "checking if the first non-yellow level is red", and "Consecutive yellow levels
   are grouped in a block to support efficient access to the first non-yellow level."

   DenseRepresentation keeps the digits in a plain list, and its fixup walks the yellow
   digits one at a time to reach the first that is not; SegmentedRepresentation groups
   them in blocks. Both go through one contract. A number has more than one
   numeral, so a result is right when it stands for the right number, keeps the invariant
   (which makes the first non-yellow digit never red, so the next inc or dec can change the
   first digit unchecked), and does not end in a 0. Blocks are never empty and never side
   by side: a second block straight after the first would hide the first non-yellow digit
   from a fixup that looks one block deep. That is held on inc and dec of every regular
   numeral of up to eight digits, not only the ones counting reaches, on counting to 2^16
   and back, on a random walk, and on numerals over a thousand digits long, far past any
   int, whose number the model keeps as bits.

   Then the clock, for the blocks only, every call on it by itself and the dearest held to
   one constant at a thousand and at a hundred thousand. The families are long blocks
   where rank 0 leaves one or joins one, a red digit behind a long block, long blocks where
   its carry or borrow lands, and long runs of red digits each with its 2 below, which a
   fixup that went on past the first red digit would walk. The dense module is the guard:
   the same clock has to see its fixup walk a run of yellows. At the larger size the
   calls go on a stopwatch as well, for a walk that allocates nothing. *)

module FD = DenseRepresentation
module FS = SegmentedRepresentation

(* What is wrong with a digit list, lowest first, if anything. *)
let five_fault ds =
  let rec go rank below = function
    | [] -> None
    | [ 0 ] -> Some (Printf.sprintf "it ends in a 0, at rank %d" rank)
    | ((0 | 4) as d) :: _ when below <> Some 2 ->
      Some
        (Printf.sprintf
           "the red %d at rank %d has %s"
           d
           rank
           (match below with
            | None -> "no non-yellow digit below it"
            | Some b -> Printf.sprintf "a %d as the last non-yellow digit below it" b))
    | (1 | 3) :: ds -> go (rank + 1) below ds
    | d :: ds -> go (rank + 1) (Some d) ds
  in
  go 0 None ds
;;

(* The bits of the number a digit list stands for, carrying up whatever is over 1. *)
let five_bits ds =
  let rec carry c = function
    | [] -> bits_of_int c
    | d :: ds -> ((d + c) mod 2) :: carry ((d + c) / 2) ds
  in
  carry 0 ds
;;

(* Every digit list of exactly k digits, and the regular ones of up to k. *)
let rec five_strings k =
  if k = 0
  then [ [] ]
  else
    List.concat_map
      (fun ds -> List.map (fun d -> d :: ds) [ 0; 1; 2; 3; 4 ])
      (five_strings (k - 1))
;;

let five_regular_up_to k =
  List.concat_map
    (fun k -> List.filter (fun ds -> five_fault ds = None) (five_strings k))
    (upto (k + 1))
;;

let five_short = lazy (five_regular_up_to 8)

(* [groups] at random, each a run of up to [longest] yellow digits and then a 2, or a red
   digit where the last non-yellow digit below is a 2; a 1 on top if it ends in a 0. *)
let five_random groups longest =
  let rec yellows n acc =
    if n = 0 then acc else yellows (n - 1) ((if Random.bool () then 1 else 3) :: acc)
  in
  let rec go n green acc =
    if n = 0
    then acc
    else (
      let acc = yellows (Random.int (longest + 1)) acc in
      let d = if green && Random.bool () then if Random.bool () then 0 else 4 else 2 in
      go (n - 1) (d = 2) (d :: acc))
  in
  List.rev
    (match go groups false [] with
     | 0 :: _ as acc -> 1 :: acc
     | acc -> acc)
;;

(* Numerals with runs k digits long, where a wrong inc or dec shows, and a slow one costs
   the most. Y1 and Y3 are runs of alternating yellows starting with a 1 and a 3. *)
let five_families k =
  let run d = List.init k (fun _ -> d) in
  let y1 = List.init k (fun i -> if i mod 2 = 0 then 1 else 3)
  and y3 = List.init k (fun i -> if i mod 2 = 0 then 3 else 1)
  and pairs a b = List.concat (List.init k (fun _ -> [ a; b ])) in
  [ "1^k", run 1
  ; "3^k", run 3
  ; "Y1", y1
  ; "Y3", y3
  ; "2 Y1", 2 :: y1
  ; "2 Y3", 2 :: y3
  ; "2^k", run 2
  ; "2 Y1 4 Y1", (2 :: y1) @ (4 :: y1)
  ; "2 Y1 4 Y3", (2 :: y1) @ (4 :: y3)
  ; "2 Y1 4 2 Y1", (2 :: y1) @ (4 :: 2 :: y1)
  ; "2 Y1 0 Y1", (2 :: y1) @ (0 :: y1)
  ; "2 Y1 0 Y3", (2 :: y1) @ (0 :: y3)
  ; "2 Y1 0 2 Y1", (2 :: y1) @ (0 :: 2 :: y1)
  ; "(2 4)^k", pairs 2 4
  ; "(2 0)^k 1", pairs 2 0 @ [ 1 ]
  ]
;;

(* What the tests need of each module: inc and dec, and a way in and out of its digits. *)
module type FIVE = sig
  type nat

  val name : string
  val inc : nat -> nat
  val dec : nat -> nat

  (* A regular digit list, lowest first, as the module writes it. *)
  val of_digits : int list -> nat

  (* Its digits, lowest first. *)
  val to_digits : nat -> int list

  (* What is wrong with its blocks, if anything. *)
  val block_fault : nat -> string option

  (* For a failure message. *)
  val show : nat -> string
end

module Five_dense : FIVE with type nat = FD.nat = struct
  type nat = FD.nat

  let name = "DenseRepresentation"
  let inc = FD.inc
  let dec = FD.dec

  let of_digits =
    List.map (function
      | 0 -> FD.Zero
      | 1 -> FD.One
      | 2 -> FD.Two
      | 3 -> FD.Three
      | _ -> FD.Four)
  ;;

  let to_digits =
    List.map (function
      | FD.Zero -> 0
      | FD.One -> 1
      | FD.Two -> 2
      | FD.Three -> 3
      | FD.Four -> 4)
  ;;

  let block_fault _ = None
  let show x = String.concat " " (List.map string_of_int (to_digits x))
end

module Five_segmented : FIVE with type nat = FS.nat = struct
  type nat = FS.nat

  let name = "SegmentedRepresentation"
  let inc = FS.inc
  let dec = FS.dec
  let yellow d = if d = 1 then FS.One else FS.Three

  let yellow_digit = function
    | FS.One -> 1
    | FS.Three -> 3
  ;;

  (* Every run of 1s and 3s as one block, as long as the run. *)
  let of_digits ds =
    List.fold_right
      (fun d acc ->
         match d, acc with
         | 0, _ -> FS.Zero :: acc
         | 2, _ -> FS.Two :: acc
         | 4, _ -> FS.Four :: acc
         | _, FS.Yellows ys :: acc -> FS.Yellows (yellow d :: ys) :: acc
         | _, _ -> FS.Yellows [ yellow d ] :: acc)
      ds
      []
  ;;

  let to_digits =
    List.concat_map (function
      | FS.Zero -> [ 0 ]
      | FS.Two -> [ 2 ]
      | FS.Four -> [ 4 ]
      | FS.Yellows ys -> List.map yellow_digit ys)
  ;;

  let rec block_fault = function
    | [] -> None
    | FS.Yellows [] :: _ -> Some "an empty block"
    | FS.Yellows _ :: FS.Yellows _ :: _ -> Some "two blocks side by side"
    | _ :: ds -> block_fault ds
  ;;

  (* A block in parentheses. *)
  let show x =
    String.concat
      " "
      (List.map
         (function
           | FS.Zero -> "0"
           | FS.Two -> "2"
           | FS.Four -> "4"
           | FS.Yellows ys ->
             "("
             ^ String.concat " " (List.map (fun y -> string_of_int (yellow_digit y)) ys)
             ^ ")")
         x)
  ;;
end

module Five_tests (N : FIVE) = struct
  let t label = N.name ^ ": " ^ label

  (* A numeral in a failure message, unless it is too long to read. *)
  let show x =
    let n = List.length (N.to_digits x) in
    if n <= 40 then "[" ^ N.show x ^ "]" else Printf.sprintf "a numeral of %d digits" n
  ;;

  (* A numeral with the number it stands for. *)
  let numbered x = x, five_bits (N.to_digits x)

  (* [r] with its number, if it is what [model] says of [bits], the number of the operand;
     why not, if it is not. *)
  let fault ~model bits r =
    match N.block_fault r with
    | Some why -> Error why
    | None ->
      let ds = N.to_digits r in
      (match five_fault ds with
       | Some why -> Error why
       | None ->
         let r_bits = five_bits ds in
         if r_bits <> model bits then Error "the wrong number" else Ok (r, r_bits))
  ;;

  (* inc or dec of a numbered [x], checked: the result, numbered, or None once [note] has
     heard what is wrong, from the step [where ()] names. *)
  let step note where op (x, bits) =
    let name, f, model =
      match op with
      | `Inc -> "inc", N.inc, inc_bits
      | `Dec -> "dec", N.dec, dec_bits
    in
    match f x with
    | r ->
      (match fault ~model bits r with
       | Ok r -> Some r
       | Error why ->
         note (Printf.sprintf "%s%s %s = %s: %s" (where ()) name (show x) (show r) why);
         None)
    | exception e ->
      note
        (Printf.sprintf
           "%s%s %s raised %s"
           (where ())
           name
           (show x)
           (Printexc.to_string e));
      None
  ;;

  (* [ops] steps from [x], each checked, stopping at the first wrong one. Each step's
     result is numbered once, and its number is the next step's model. *)
  let chain note what ops x =
    let rec go i x = function
      | [] -> ()
      | op :: ops ->
        (match step note (fun () -> Printf.sprintf "%s, step %d: " what i) op x with
         | Some r -> go (i + 1) r ops
         | None -> ())
    in
    go 1 (numbered x) ops
  ;;

  let test_contract () =
    refuses ~prefix:"dec:" (t "dec of zero refuses") (fun () -> N.dec (N.of_digits []));
    all_of (t "inc and dec of every regular numeral of up to 8 digits") (fun note ->
      List.iter
        (fun ds ->
           let x = numbered (N.of_digits ds) in
           ignore (step note (fun () -> "") `Inc x);
           if ds <> [] then ignore (step note (fun () -> "") `Dec x))
        (Lazy.force five_short));
    all_of (t "counting up to 2^16 from zero, then back down to zero") (fun note ->
      let n = 1 lsl 16 in
      chain
        note
        "counting"
        (List.init (2 * n) (fun i -> if i < n then `Inc else `Dec))
        (N.of_digits []));
    all_of (t "a random walk of 200000 incs and decs from zero") (fun note ->
      Random.init 20261001;
      let rec ops i v acc =
        if i = 200_000
        then List.rev acc
        else if v = 0 || Random.int 5 < 3
        then ops (i + 1) (v + 1) (`Inc :: acc)
        else ops (i + 1) (v - 1) (`Dec :: acc)
      in
      chain note "the walk" (ops 0 0 []) (N.of_digits []))
  ;;

  (* Numerals far past any int. Each takes a hundred incs and then two hundred decs, every
     step against the model, so that inc and dec also see what the other returned. *)
  let test_long () =
    Random.init 20261001;
    let samples =
      five_families 500
      @ List.init 20 (fun i -> Printf.sprintf "random sample %d" i, five_random 200 12)
    in
    let ops = List.init 300 (fun i -> if i < 100 then `Inc else `Dec) in
    all_of
      (t
         "a hundred incs, then two hundred decs, from numerals over a thousand digits \
          long")
      (fun note ->
         List.iter (fun (what, ds) -> chain note what ops (N.of_digits ds)) samples)
  ;;
end

module Five_dense_tests = Five_tests (Five_dense)
module Five_segmented_tests = Five_tests (Five_segmented)

(* Whether the clock can tell O(1) from O(log n): the dense fixup rebuilds every yellow
   digit in front of the red one, so dec of 2 1^k 4 costs at least k words. *)
let test_five_guard () =
  let k = 1000 in
  let x = Five_dense.of_digits ((2 :: List.init k (fun _ -> 1)) @ [ 4 ]) in
  let name = Printf.sprintf "guard: the same clock sees the dense dec of 2 1^%d 4" k in
  let _, c = cost (fun () -> FD.dec x) in
  check (Printf.sprintf "%s walk its yellows, %.0f words" name c) (c >= float k)
;;

(* inc and dec of every family at k, inputs made beforehand. *)
let five_calls k =
  Random.init k;
  List.concat_map
    (fun (what, ds) ->
       let x = Five_segmented.of_digits ds in
       [ ("inc of " ^ what, fun () -> FS.inc x); ("dec of " ^ what, fun () -> FS.dec x) ])
    (five_families k @ [ "k random groups", five_random k 8 ])
;;

let test_five_costs k calls =
  within_flat_budget
    (Printf.sprintf "SegmentedRepresentation, inc and dec, k=%d" k)
    (dearest_call calls)
;;

(* The clock cannot see a walk that allocates nothing, a List.length on a block say. So at
   the larger size every call goes on the stopwatch too, ten thousand times over. Ten
   thousand of any of them take under a millisecond of processor time; ten thousand of
   one that walks a block of a hundred thousand digits take over a second, even when
   nothing is allocated. *)
let five_reps = 10_000
let five_cpu_limit = 0.1

let test_five_stopwatch k calls =
  let slowest = ref (0.0, "") in
  (try
     List.iter
       (fun (what, f) ->
          let started = Sys.time () in
          for _ = 1 to five_reps do
            ignore (Sys.opaque_identity (f ()))
          done;
          let took = Sys.time () -. started in
          if took > fst !slowest then slowest := took, what;
          if took > five_cpu_limit then raise Exit)
       calls
   with
   | Exit -> ()
   | e -> slowest := infinity, "a call that raised " ^ Printexc.to_string e);
  let took, what = !slowest in
  check
    (Printf.sprintf
       "SegmentedRepresentation, inc and dec, k=%d: the slowest is %s, %d calls in %.3f \
        s of processor time, limit %.1f s"
       k
       what
       five_reps
       took
       five_cpu_limit)
    (took <= five_cpu_limit)
;;

(* Counting up to 2^17 from zero, a random walk as long, and back down to zero, every inc
   and dec on the clock; stops at a result the contract has already failed. *)
let test_five_counting_cost () =
  let n = 1 lsl 17 in
  Random.init n;
  let dearest = ref (0.0, "") in
  let rec go i v x =
    if i < 2 * n || v > 0
    then (
      let name, f, v' =
        if i < n || (i < 2 * n && (v = 0 || Random.bool ()))
        then "inc", FS.inc, v + 1
        else "dec", FS.dec, v - 1
      in
      match cost (fun () -> f x) with
      | r, c ->
        if c > fst !dearest then dearest := c, Printf.sprintf "%s of %d" name v;
        if
          Five_segmented.block_fault r = None
          && five_fault (Five_segmented.to_digits r) = None
        then go (i + 1) v' r
        else dearest := infinity, Printf.sprintf "%s of %d, a malformed result" name v
      | exception e ->
        dearest
        := infinity, Printf.sprintf "%s of %d raised %s" name v (Printexc.to_string e))
  in
  go 0 0 [];
  within_flat_budget
    (Printf.sprintf
       "SegmentedRepresentation, counting to %d, a random walk and back down to 0"
       n)
    !dearest
;;

(* Both modules through the contract, a case each; then the clock, for the blocks only,
   the large size and the stopwatch last. *)
let test_five_dense () =
  Five_dense_tests.test_contract ();
  Five_dense_tests.test_long ()
;;

let test_five_segmented () =
  Five_segmented_tests.test_contract ();
  Five_segmented_tests.test_long ();
  test_five_guard ();
  test_five_counting_cost ();
  test_five_costs 1_000 (five_calls 1_000);
  let calls = five_calls 100_000 in
  test_five_costs 100_000 calls;
  test_five_stopwatch 100_000 calls
;;

(* ---------------------------------- SegmentedRandomAccessList (Exercise 9.13) *)

(* Exercise 9.13 asks for cons, head, tail and lookup on a random-access list over the
   numbers of Exercise 9.12, with "cons, head, and tail in O(1) worst-case time, and lookup
   in O(log i) worst-case time". The digits hold trees: digit d at position r holds d
   complete binary leaf trees of 2^r elements each, in order, so cons is inc with a leaf,
   tail is dec, a carry links two trees and a borrow splits one.

   cons, head and tail go through the tests of Exercises 9.9 and 9.10: the order the
   elements come back in, and every operation on the clock by itself, the dearest held to
   one constant at two sizes. Those cannot see where the trees are; lookup can. It is held
   to every index of every size up to 300, built by cons and left by tails; to refusing
   one past either end; to a random walk of conses and tails with every index looked up
   along the way, which leaves lists with red digits further up; and to old versions,
   looked up after newer ones were made from them.

   O(log i) is a bound in the index, not in the length. Every index of lists of 2^10 and
   2^17 elements goes on the clock, each against its own budget of a constant per binary
   digit of i, and three more. The clock sees only what lookup allocates, and a lookup
   that walked the whole list first, to count it say, could allocate nothing. So a
   stopwatch holds lookup 0 in a list of a million to twice what it takes in a list of
   eight. Figure 9.6's lookup is the guard: it is O(log n), and the same stopwatch has to
   see its lookup 0 grow with the length. *)

module SL = SegmentedRandomAccessList
module Seg_list = Lite_tests (SL)

(* [r] holds 0 to n - 1: every index looked up. *)
let seg_looks note what n r =
  for i = 0 to n - 1 do
    match SL.lookup i r with
    | v when v = i -> ()
    | v -> note (Printf.sprintf "%s: lookup %d = %d" what i v)
    | exception e ->
      note (Printf.sprintf "%s: lookup %d raised %s" what i (Printexc.to_string e))
  done
;;

let test_seg_list_lookup name =
  let t label = Printf.sprintf "%s: %s" name label in
  all_of
    (t "lookup of every index, sizes 0 to 300, built by cons or left by tails")
    (fun note ->
       for n = 0 to 300 do
         List.iter
           (fun (how, r) -> seg_looks note (Printf.sprintf "n=%d %s" n how) n (r ()))
           (Seg_list.versions n)
       done);
  all_of (t "lookup one past either end refuses, sizes 0 to 300") (fun note ->
    for n = 0 to 300 do
      List.iter
        (fun (how, r) ->
           let r = r () in
           List.iter
             (fun i ->
                match SL.lookup i r with
                | _ -> note (Printf.sprintf "n=%d %s: lookup %d returned" n how i)
                | exception Failure m when m = "lookup: not found" -> ()
                | exception e ->
                  note
                    (Printf.sprintf
                       "n=%d %s: lookup %d raised %s"
                       n
                       how
                       i
                       (Printexc.to_string e)))
             [ -1; n ])
        (Seg_list.versions n)
    done);
  all_of
    (t "a random walk of 100000 conses and tails, every index looked up every 997 steps")
    (fun note ->
       Random.init 20261002;
       let r = ref SL.empty
       and model = ref []
       and next = ref 0 in
       for step = 1 to 100_000 do
         (match !model with
          | _ :: rest when Random.int 5 >= 3 ->
            r := SL.tail !r;
            model := rest
          | _ ->
            r := SL.cons !next !r;
            model := !next :: !model;
            incr next);
         if step mod 997 = 0
         then
           List.iteri
             (fun i v ->
                match SL.lookup i !r with
                | w when w = v -> ()
                | w -> note (Printf.sprintf "step %d: lookup %d = %d, want %d" step i w v)
                | exception e ->
                  note
                    (Printf.sprintf
                       "step %d: lookup %d raised %s"
                       step
                       i
                       (Printexc.to_string e)))
             !model
       done);
  all_of
    (t "old versions look up as they did, after newer ones were made from them")
    (fun note ->
       let n = 1000 in
       let base = Seg_list.of_list (Seg_list.from 0 n) in
       let newer =
         List.init 200 (fun j ->
           if j mod 2 = 0
           then `Consed (j, SL.cons (-j) base)
           else `Tailed (1 + (j mod 7), Seg_list.tails (1 + (j mod 7)) base))
       in
       seg_looks note "the shared version, after 200 newer ones" n base;
       List.iter
         (function
           | `Consed (j, r) ->
             (match SL.lookup 0 r with
              | v when v = -j -> ()
              | v -> note (Printf.sprintf "cons %d onto it: lookup 0 = %d" (-j) v));
             seg_looks
               note
               (Printf.sprintf "cons %d onto it, tail again" (-j))
               n
               (SL.tail r)
           | `Tailed (k, r) ->
             for i = 0 to n - k - 1 do
               match SL.lookup i r with
               | v when v = i + k -> ()
               | v -> note (Printf.sprintf "%d tails of it: lookup %d = %d" k i v)
             done)
         newer)
;;

(* A constant per binary digit of i, and three more. A lookup that takes each position's
   trees off as a list and folds over them allocates for every position it passes, and
   more for every tree: measured, some 13 words a digit with a running total, some 28 with
   a pair rebuilt for every tree. Twice what a digit gets elsewhere leaves room for both,
   and none for a lookup that walks every position, which at i = 0 is out by the length of
   the list. *)
let lookup_budget i = 2.0 *. per_digit *. float_of_int (digits i + 3)

(* Every index on the clock by itself, each against its own budget. *)
let test_seg_list_lookup_costs name n =
  let worst = ref (0.0, "", 0, 0.0) in
  List.iter
    (fun (how, r) ->
       let r = r () in
       for i = 0 to n - 1 do
         match cost (fun () -> SL.lookup i r) with
         | _, c ->
           let ratio, _, _, _ = !worst in
           if c /. lookup_budget i > ratio then worst := c /. lookup_budget i, how, i, c
         | exception e ->
           worst := infinity, how ^ " raised " ^ Printexc.to_string e, i, infinity
       done)
    (Seg_list.versions n);
  let ratio, how, i, c = !worst in
  check
    (Printf.sprintf
       "%s: lookup of every index at n=%d, the dearest against its budget is lookup %d \
        (%s), %.0f words, budget %.0f"
       name
       n
       i
       how
       c
       (lookup_budget i))
    (ratio <= 1.0)
;;

(* Processor time for a million calls, the best of three. *)
let lookup_stopwatch f =
  let once () =
    let started = Sys.time () in
    for _ = 1 to 1_000_000 do
      ignore (Sys.opaque_identity (f ()))
    done;
    Sys.time () -. started
  in
  min (once ()) (min (once ()) (once ()))
;;

(* lookup 0 in a list of 8 and in a list of 2^20 elements, or of [large], each built by
   cons: the time of the second over the first. *)
module Lookup_growth (R : sig
    type 'a rlist

    val empty : 'a rlist
    val cons : 'a -> 'a rlist -> 'a rlist
    val lookup : int -> 'a rlist -> 'a
  end) =
struct
  let ratio ?(large = 1 lsl 20) () =
    let build n = List.fold_left (fun r i -> R.cons i r) R.empty (List.rev (upto n)) in
    let small = build 8
    and large = build large in
    let s = lookup_stopwatch (fun () -> R.lookup 0 small)
    and l = lookup_stopwatch (fun () -> R.lookup 0 large) in
    l /. s
  ;;
end

module Seg_growth = Lookup_growth (SL)
module Binary_growth = Lookup_growth (BinaryRandomAccessList)

let lookup_growth_limit = 2.0

let test_seg_list_lookup_stopwatch name =
  let g = Binary_growth.ratio () in
  check
    (Printf.sprintf
       "guard: the same stopwatch sees Figure 9.6's lookup 0 grow with the length, %.1f \
        times as long at 2^20 as at 8"
       g)
    (g > lookup_growth_limit);
  let r = Seg_growth.ratio () in
  check
    (Printf.sprintf
       "%s: lookup 0 takes %.1f times as long at 2^20 elements as at 8, limit %.1f"
       name
       r
       lookup_growth_limit)
    (r <= lookup_growth_limit)
;;

(* The stack first, then lookup; each one's costs only once what it returns holds. *)
let test_seg_list () =
  let name = "SegmentedRandomAccessList" in
  Seg_list.run_contract name;
  test_seg_list_lookup name;
  Seg_list.run_worst_costs name;
  test_seg_list_lookup_costs name (1 lsl 10);
  test_seg_list_lookup_costs name (1 lsl 17);
  test_seg_list_lookup_stopwatch name
;;

(* ------------------------------ SkewBinaryRandomAccessList (Figure 9.7, 9.3.1) *)

(* Section 9.3.1 builds the list out of a skew binary number: digit i weighs 2^(i+1) - 1,
   the digits are 0, 1 and 2, and only the lowest non-zero digit may be a 2, which leaves
   every number one form (Theorem 9.1) and makes an increment a matter of the lowest
   digit alone. The list holds a complete binary tree of 2^(i+1) - 1 elements for each one
   in digit i and two of them for a two, smallest first, each with its weight beside it,
   so the lowest non-zero digit is right at the front. cons links the first two trees under
   the new element when their weights agree and puts down a leaf when they do not; tail
   hands the root's two children back to the front; head reads the root. p.133: "cons,
   head, and tail run in O(1) worst-case time", and lookup and update, which find the
   tree by the weights and the element by halving, "run in O(log n) worst-case time. In
   fact, every unsuccessful step of lookup or update discards at least one element, so
   this bound can be reduced slightly to O(min(i, log n))".

   Behaviour is the contract above, unchanged. It looks up every index of every size to
   70, which is where the halving goes wrong: in a tree of weight w the root is index 0 and
   the left child holds the next w div 2, so index w div 2 still belongs on the left; the
   figure as printed sends it right, where it is index -1, and lookup 1 of three elements
   is refused. The clock above holds every operation to a constant per digit, which is the
   O(log n) of lookup and update; cons, head and tail are held to one digit's budget
   instead, the same at a thousand elements and at a hundred thousand, which a cons or a
   tail that copies the spine is over by the time the spine has seven trees. update is
   held to its index too: a constant for each element of the index when that is less than
   the per-digit budget, so an update of index 0 that copies the spine is seen. The clock
   sees nothing of lookup, which allocates nothing, so the stopwatch of Exercise 9.13 is
   used again, with care over the size: a million is a poor choice here, as 2^20 is a one
   and a 2^20 - 1 in skew binary, two trees, and a lookup that walked the spine first would
   never show. 2^20 - 21 is nineteen ones, a tree for each, the most trees a million
   elements can have, and lookup 0 in that list may take no more than twice what it takes
   in a list of eight. *)

module Skew = Rlist_tests (SkewBinaryRandomAccessList)

(* update at every index of a list of n: each on the clock against the smaller of the
   per-digit budget and a constant per element of the index. The dearest against its own
   budget is what is reported. *)
let test_skew_update_by_index name n =
  let module R = SkewBinaryRandomAccessList in
  let index_budget i = Float.min (budget n) (per_digit *. float_of_int (i + 1)) in
  let full = Skew.of_list (upto n) in
  let worst = ref (0.0, 0, 0.0) in
  for i = 0 to n - 1 do
    let r', c = cost (fun () -> R.update i 0 full) in
    ignore (Sys.opaque_identity r');
    let ratio, _, _ = !worst in
    if c /. index_budget i > ratio then worst := c /. index_budget i, i, c
  done;
  let ratio, i, c = !worst in
  check
    (Printf.sprintf
       "%s: update at every index against its index, n=%d, the dearest against its \
        budget is update %d, %.0f words, budget %.0f"
       name
       n
       i
       c
       (index_budget i))
    (ratio <= 1.0)
;;

module Skew_growth = Lookup_growth (SkewBinaryRandomAccessList)

(* 2^20 - 21 = 1 + 3 + 7 + ... + (2^19 - 1): nineteen trees. *)
let skew_all_ones = (1 lsl 20) - 21

let test_skew_lookup_stopwatch name =
  let r = Skew_growth.ratio ~large:skew_all_ones () in
  check
    (Printf.sprintf
       "%s: lookup 0 takes %.1f times as long at %d elements, nineteen trees, as at 8, \
        limit %.1f"
       name
       r
       skew_all_ones
       lookup_growth_limit)
    (r <= lookup_growth_limit)
;;

let test_skew () =
  let name = "SkewBinaryRandomAccessList" in
  Skew.run_contract name;
  Skew.run_costs ~stack:(fun _ -> per_digit) name;
  test_skew_update_by_index name 1_000;
  test_skew_update_by_index name 100_000;
  test_skew_lookup_stopwatch name
;;

(* ---------------------------------- SkewHoodMelvilleQueue (Exercise 9.14) *)

(* Exercise 9.14 asks for the Hood-Melville queue of Figure 8.1 over skew binary
   random-access lists instead of lists, "and lookup and update functions on these
   queues". The queue is the figure's, lenf and lenr and all, with the list patterns of
   exec and invalidate turned into the skew list's head, tail and cons, so it keeps
   Chapter 8's O(1) worst case at a larger constant: a skew cons is 10 words where a list
   cell is 3, and a skew tail allocates 12 where a list pattern allocates nothing, so an
   operation that steps the rotation costs about twice what it did. The contract and the
   clocks for snoc, head and tail are Chapter 8's, from queues.ml, with the constant
   doubled.

   lookup and update are the exercise. Idle, the queue is f ++ reverse r and the split is
   at lenf, the rear read from its far end. During a rotation lenf counts the front under
   construction, f ++ reverse (old r), of which the physical f holds only the first part;
   the rest is in the state, split between the unreversed remainder of the old rear and
   the reversed part while reversing, or at the end of r' while appending. So the state
   carries the two lengths the figure did not need, and the old rear's size through the
   appending phase, and lookup is one skew lookup in whichever list holds the index:
   O(log n). update has one thing more to get right. An element of the old front is in the
   physical f, which head and lookup read now, and in the copy the state is building,
   which commit will install, and a change to one copy only is lost, or arrives after the
   rotation ends. So every update is read back two ways: by lookup at once, and by a drain
   through head and tail, which crosses the rotation's end.

   The contract: every index of every queue reachable by n snocs and t tails, n up to 80,
   which passes through every phase of many rotations, looked up, refused one past either
   end, updated and read back both ways; a random walk of all five operations against a
   list; old versions after newer ones. The clocks: Chapter 8's sequences and versions for
   snoc, head and tail; then lookup and update at every index of versions in every phase,
   each held to a constant per digit of n, at a thousand and a hundred thousand
   elements. *)

module SQ = SkewHoodMelvilleQueue
module Skew_queue = Queues.Contract (SQ)

(* Twice Chapter 8's 96: measured, the dearest snoc is 118 words and the dearest tail 98,
   the rotation step's two skew conses and two skew tails on top of the records. A tail
   that reversed the rear in one go is three cells of ten words each per element, out by
   a factor of a hundred at the smaller size. *)
let skew_queue_constant = 192.0

module Skew_queue_costs =
  Queues.Worst_case
    (SQ)
    (struct
      let constant = skew_queue_constant
      let mix_seed = 20261007
      let trace_seed = 20261008
    end)

let sq_of_list xs = List.fold_left SQ.snoc SQ.empty xs
let sq_drain q = drain_with ~is_empty:SQ.is_empty ~head:SQ.head ~tail:SQ.tail q

(* [f what q contents] on every queue of n snocs then t tails, n up to [n_max]. *)
let sq_reachable n_max f =
  for n = 0 to n_max do
    let q = ref (sq_of_list (upto n)) in
    for t = 0 to n do
      f (Printf.sprintf "n=%d t=%d" n t) !q (List.init (n - t) (fun i -> i + t));
      if t < n then q := SQ.tail !q
    done
  done
;;

(* [q] holds [m]: every index looked up. *)
let sq_looks note what q m =
  List.iteri
    (fun i x ->
       match SQ.lookup i q with
       | v when v = x -> ()
       | v -> note (Printf.sprintf "%s: lookup %d = %d, want %d" what i v x)
       | exception e ->
         note (Printf.sprintf "%s: lookup %d raised %s" what i (Printexc.to_string e)))
    m
;;

let sq_refused note what msg i f =
  match f () with
  | _ -> note (Printf.sprintf "%s: index %d was not refused" what i)
  | exception Failure m when m = msg -> ()
  | exception e ->
    note (Printf.sprintf "%s: index %d raised %s" what i (Printexc.to_string e))
;;

let test_skew_queue_lookup name =
  let t label = Printf.sprintf "%s: %s" name label in
  all_of
    (t "lookup of every index of every queue of n snocs and t tails, n up to 80")
    (fun note -> sq_reachable 80 (fun what q m -> sq_looks note what q m));
  all_of
    (t "lookup and update refuse -1 and one past the end, on the same queues")
    (fun note ->
       sq_reachable 80 (fun what q m ->
         List.iter
           (fun i ->
              sq_refused note what "lookup: not found" i (fun () -> SQ.lookup i q);
              sq_refused note what "update: not found" i (fun () ->
                SQ.is_empty (SQ.update i 0 q)))
           [ -1; List.length m ]))
;;

let test_skew_queue_update name =
  let t label = Printf.sprintf "%s: %s" name label in
  all_of
    (t
       "update at every index of the same queues reads back by lookup, and by a drain \
        through head and tail")
    (fun note ->
       sq_reachable 80 (fun what q m ->
         List.iteri
           (fun i _ ->
              let what = Printf.sprintf "%s update %d" what i in
              let want = List.mapi (fun j x -> if j = i then 1000 + i else x) m in
              match SQ.update i (1000 + i) q with
              | q' ->
                sq_looks note what q' want;
                (match sq_drain q' with
                 | got when got = want -> ()
                 | got ->
                   note (Printf.sprintf "%s: drains to %s" what (string_of_int_list got))
                 | exception e ->
                   note (Printf.sprintf "%s: drain raised %s" what (Printexc.to_string e)))
              | exception e ->
                note (Printf.sprintf "%s raised %s" what (Printexc.to_string e)))
           m))
;;

let test_skew_queue_walk name =
  let t label = Printf.sprintf "%s: %s" name label in
  all_of
    (t
       "a random walk of 100000 snocs, tails, updates and lookups against a list, head \
        and is_empty at every step, read back and drained every 997 steps")
    (fun note ->
       Random.init 20261007;
       (* The model: the elements ever snoc'ed, in an array, and the index of the front. *)
       let q = ref SQ.empty
       and all = Dynarray.create ()
       and front = ref 0
       and versions = ref [] in
       let n () = Dynarray.length all - !front in
       let at i = Dynarray.get all (!front + i) in
       let contents () = List.init (n ()) at in
       for step = 1 to 100_000 do
         (match Random.int 6 with
          | 0 | 1 ->
            q := SQ.snoc !q step;
            Dynarray.add_last all step
          | 2 when n () > 0 ->
            q := SQ.tail !q;
            incr front
          | 3 when n () > 0 ->
            let i = Random.int (n ()) in
            q := SQ.update i (-step) !q;
            Dynarray.set all (!front + i) (-step)
          | 4 when n () > 0 ->
            let i = Random.int (n ()) in
            (match SQ.lookup i !q with
             | v when v = at i -> ()
             | v -> note (Printf.sprintf "step %d: lookup %d = %d" step i v)
             | exception e ->
               note
                 (Printf.sprintf
                    "step %d: lookup %d raised %s"
                    step
                    i
                    (Printexc.to_string e)))
          | _ -> ());
         if SQ.is_empty !q <> (n () = 0)
         then note (Printf.sprintf "step %d: is_empty" step);
         if n () > 0 && SQ.head !q <> at 0 then note (Printf.sprintf "step %d: head" step);
         if step mod 997 = 0
         then (
           let m = contents () in
           sq_looks note (Printf.sprintf "step %d" step) !q m;
           if sq_drain !q <> m then note (Printf.sprintf "step %d: drain" step);
           versions := (step, !q, m) :: !versions)
       done;
       (* Every saved version still reads as it did, and an update of one makes a new
          version and leaves it alone. *)
       List.iter
         (fun (step, q, m) ->
            let what = Printf.sprintf "version of step %d, at the end" step in
            sq_looks note what q m;
            if sq_drain q <> m then note (what ^ ": drains differently");
            if m <> []
            then (
              let q' = SQ.update 0 (-1) q in
              if SQ.head q' <> -1 || SQ.lookup 0 q' <> -1
              then note (what ^ ": update 0 not visible in the new version");
              if SQ.head q <> List.hd m || sq_drain q <> m
              then note (what ^ ": update 0 changed the version it came from")))
         !versions)
;;

(* lookup and update at every index of [q], a queue of [size], each on its own clock. *)
let sq_sweep q size =
  let dl = ref (0, 0.0)
  and du = ref (0, 0.0)
  and sum = ref 0 in
  for i = 0 to size - 1 do
    let x, c = cost (fun () -> SQ.lookup i q) in
    sum := !sum + x;
    if c > snd !dl then dl := i, c;
    let q', c = cost (fun () -> SQ.update i 0 q) in
    ignore (Sys.opaque_identity q');
    if c > snd !du then du := i, c
  done;
  ignore (Sys.opaque_identity !sum);
  !dl, !du
;;

(* A constant per digit of n, twice what the lists get: an update during a rotation is
   two skew updates and the state's record on top of the queue's, some 15 words a digit
   measured; a lookup allocates nothing, and the budget is there for a lookup that walks
   the queue by tails, which costs the whole rotation step per element passed. *)
let sq_budget n = 2.0 *. budget n

(* A build of n by snocs ends inside a rotation, and so do the [versions] tails that
   follow it, which keep the rotation stepping: every index of each of those versions. *)
let test_skew_queue_access_costs name n versions =
  let t label = Printf.sprintf "%s: %s" name label in
  let q = ref (sq_of_list (upto n))
  and dl = ref (0, 0, 0.0)
  and du = ref (0, 0, 0.0) in
  for k = 0 to versions do
    let (il, cl), (iu, cu) = sq_sweep !q (n - k) in
    (let _, _, c = !dl in
     if cl > c then dl := k, il, cl);
    (let _, _, c = !du in
     if cu > c then du := k, iu, cu);
    if k < versions then q := SQ.tail !q
  done;
  let within op (k, i, c) =
    check
      (t
         (Printf.sprintf
            "%s at every index of a build of %d and of the %d versions a tail at a time \
             after it, dearest is index %d after %d tails at %.0f words, budget %.0f"
            op
            n
            versions
            i
            k
            c
            (sq_budget n)))
      (c <= sq_budget n)
  in
  within "lookup" !dl;
  within "update" !du
;;

(* The queue first, then lookup on the small queues, then lookup and update on the clock
   at a thousand: that one stands guard, as everywhere in these files, because a lookup
   that walks the queue by tails makes the update read-backs and the random walk after
   it quadratic, a hang rather than a failure, and at a thousand it is a failure. Then the
   rest, the large size after the small. *)
let test_skew_queue () =
  let name = "SkewHoodMelvilleQueue" in
  Skew_queue.run_contract name;
  test_skew_queue_lookup name;
  test_skew_queue_access_costs name 1_000 200;
  test_skew_queue_update name;
  test_skew_queue_walk name;
  Skew_queue_costs.run_sequences name;
  Skew_queue_costs.run_versions (name ^ ", persistently");
  test_skew_queue_access_costs name 100_000 20
;;

(* ------------------------------------------ SkewBinomialHeap (Figure 9.8, 9.3.2) *)

(* Section 9.3.2 is a hybrid: insert follows the skew binary increment, merge the ordinary
   binary addition. A skew binomial tree of rank r is a binomial tree whose every node
   carries up to r more elements beside it, so its size is no longer fixed by its rank
   (Lemma 9.2: 2^r to 2^(r+1) - 1), and the heap is a list of them in increasing rank,
   except that the first two may share a rank. insert looks at the first two trees only:
   equal ranks are skew linked under the new element, a link and then one more comparison
   to decide which of the two smallest goes on the list; otherwise a singleton goes in
   front. merge normalizes both heaps, so that the lists it adds are of strictly
   increasing rank, and delete_min, after the usual reversed children and merge, puts the
   discarded root's auxiliary elements back one insert each. p.136: "insert runs in O(1)
   worst-case time, while merge, findMin, and deleteMin run in ... O(log n) worst-case
   time each."

   The contract and the clocks are those of Exercise 9.11, through their functors. The
   budgets differ: an insert may take two comparisons, where the segmented heap's took
   one, and the queries are given 6L + 6 comparisons and 60L + 60 words, L = log2 (n + 1),
   twice and more what the dearest of them spends. The shape is read through find_min's
   comparisons again, one per tree but the first. There is no numeral for the sizes, as
   p.135 says, but there is one for the ranks: insert from the empty heap IS the skew
   binary increment on the ranks, so after n inserts the trees are the non-zero digits of
   n in skew binary, counted with a two as two. And a merge of two such heaps is binary
   addition on the ranks: a tree of rank r counts 2^r whatever its size, normalize keeps
   that sum while it takes the leading pair to one tree, and mergeTrees carries like the
   adder of section 3.2, so the merge of the heaps of a and b inserts has one tree per 1
   bit of the sum of their rank weights. After delete_mins the count is not fixed, but
   Lemma 9.2 bounds it: k trees weigh at least 1 + 1 + 2 + ... + 2^(k-2) elements, so k is
   at most floor (log2 n) + 1 at every version of a random trace, which is what keeps the
   queries logarithmic. *)

module SBH = SkewBinomialHeap (Counting_int)
module SBK = SkewBinomialHeap (Keyed)
module Skew_heap_contract = Heap_contract (SBH) (SBK)

module Skew_heap_clocks =
  Heap_clocks
    (SBH)
    (struct
      let insert_comparisons = 2.0
      let insert_words = flat_budget
      let query_comparisons l = (6. *. l) +. 6.
      let query_words l = (60. *. l) +. 60.
    end)

(* Trees in [h]: find_min compares every root but the first once. *)
let skew_trees h = if SBH.is_empty h then 0 else count_only (fun () -> SBH.find_min h) + 1

(* p.132's inc on the weights of a skew binary number, smallest first: the first two
   weights combine when they are equal, else a 1 goes in front. *)
let skew_inc = function
  | w1 :: w2 :: rest when w1 = w2 -> (1 + w1 + w2) :: rest
  | ws -> 1 :: ws
;;

(* The skew binary weights of n, and the rank weights they stand for: a weight 2^(r+1) - 1
   is a tree of rank r, which counts 2^r in a merge. *)
let skew_weights n = List.fold_left (fun ws _ -> skew_inc ws) [] (upto n)
let rank_weight ws = List.fold_left (fun s w -> s + ((w + 1) / 2)) 0 ws

let test_skew_heap_shape () =
  let t label = "SkewBinomialHeap, shape: " ^ label in
  all_of
    (t
       "after n inserts from empty, one tree per non-zero digit of n in skew binary, a \
        two counting twice, n up to 2000")
    (fun note ->
       let h = ref SBH.empty
       and ws = ref [] in
       for n = 1 to 2000 do
         h := SBH.insert n !h;
         ws := skew_inc !ws;
         let got = skew_trees !h
         and want = List.length !ws in
         if got <> want then note (Printf.sprintf "n=%d: %d trees, want %d" n got want)
       done);
  all_of
    (t
       "after the merge of the heaps of a and b inserts, a and b up to 40, one tree per \
        1 bit of the sum of their rank weights")
    (fun note ->
       let heaps = Array.init 41 (fun n -> Skew_heap_contract.of_list (upto n))
       and weights = Array.init 41 (fun n -> rank_weight (skew_weights n)) in
       for a = 0 to 40 do
         for b = 0 to 40 do
           let got = skew_trees (SBH.merge heaps.(a) heaps.(b))
           and want = popcount (weights.(a) + weights.(b)) in
           if got <> want
           then note (Printf.sprintf "merge of %d and %d: %d trees, want %d" a b got want)
         done
       done);
  all_of
    (t
       "at most floor (log2 n) + 1 trees at every version of a random trace of 6000 \
        inserts, merges and delete_mins")
    (fun note ->
       Random.init 20261006;
       let n = 6_000 in
       let v = Array.make (n + 1) SBH.empty
       and size = Array.make (n + 1) 0 in
       for i = 1 to n do
         let p = Random.int i
         and q = Random.int i in
         (match Random.int 4 with
          | 2 when size.(p) + size.(q) <= 1 lsl 20 ->
            v.(i) <- SBH.merge v.(p) v.(q);
            size.(i) <- size.(p) + size.(q)
          | 3 when size.(p) > 0 ->
            v.(i) <- SBH.delete_min v.(p);
            size.(i) <- size.(p) - 1
          | _ ->
            v.(i) <- SBH.insert i v.(p);
            size.(i) <- size.(p) + 1);
         let got = skew_trees v.(i) in
         if size.(i) > 0 && got > floor_log2 size.(i) + 1
         then
           note
             (Printf.sprintf
                "version %d of %d elements: %d trees, at most %d"
                i
                size.(i)
                got
                (floor_log2 size.(i) + 1))
       done)
;;

(* What it returns, then its shape, then its costs, the large size only after the small. *)
let test_skew_heap () =
  let name = "SkewBinomialHeap" in
  Skew_heap_contract.run name;
  test_skew_heap_shape ();
  Skew_heap_clocks.test_all_ones name;
  Skew_heap_clocks.test_sequences name 1_000;
  Skew_heap_clocks.test_sequences name 100_000;
  Skew_heap_clocks.test_merges name 1_000;
  Skew_heap_clocks.test_merges name 100_000;
  Skew_heap_clocks.test_versions name
;;

(* ---------------------------------------------- HeapWithDelete (Exercise 9.16) *)

(* Exercise 9.16 asks for a functor that gives any heap H a delete, over the type H.Heap x
   H.Heap: one heap of positive occurrences and one of negative, where "a negative
   occurrence of an element means that that element has been deleted, but not yet
   physically removed from the heap"; the two "cancel each other out and are physically
   removed when both become the minimum elements of their respective heaps", under the
   invariant that "the minimum element of the positive heap is strictly smaller than the
   minimum element of the negative heap". The invariant is what lets find_min answer from
   the positive heap alone: its minimum is below every negative, so it is live. It also
   settles what delete means for an element that is not there. A negative above the live
   minimum stays and cancels the next insert of its element, the book's "curious property
   that an element can be deleted before it has been inserted"; a negative below the live
   minimum has nothing left to cancel and no place the invariant lets it stay, so it is let
   go. The negatives of one operand of a merge cancel positives of the other.

   The wrapped heap is the skew binomial heap of Figure 9.8. With delete unused the functor
   is that heap and a pair, so the contract and the clocks of Exercise 9.11 run on it first,
   to the budgets of Figure 9.8. Then delete's own contract: one copy of a present element
   goes, whichever copy and wherever it sits; an element deleted first and inserted after is
   not there; a delete below the minimum is let go; cancellations cascade; a merge cancels
   across its operands; a version with a pending delete serves several futures; equal keys
   lose exactly one of their number. And a random trace of 6000 inserts, deletes, merges and
   delete_mins over earlier versions, against the book's description on sorted lists.

   Costs. find_min reads the positive heap and stays worst-case. insert can only lower the
   positive minimum, so the invariant survives it: it needs no check unless the positive
   heap was empty, and into a non-empty one it is held to Figure 9.8's insert budget, with
   negatives pending. Every pass of the check's loop ends with a delete_min on H and takes
   an element out of one heap or both for good, and an element enters the positive heap by
   one insert and the negative heap by one delete, so over a sequence of m operations the
   loop runs at most m times: O(m log m) in all, amortized O(log n) a piece for delete,
   delete_min and merge. One operation can cost Theta(n log n): insert 0 to n, delete 1 to
   n, each a negative above the live minimum 0, and the one delete_min cancels n pairs. The
   bound is amortized and ephemeral, since the loop's work is not memoized: a second
   delete_min on that version cancels the n pairs over again. So the amortized clocks run
   single-threaded sequences, the sum of a sequence against m times a budget in L = log2
   (m + 1), m being what the two heaps can hold between them; the clocks over versions
   above are the ones with delete unused. *)

module DH = HeapWithDelete (Counting_int) (SkewBinomialHeap (Counting_int))
module DK = HeapWithDelete (Keyed) (SkewBinomialHeap (Keyed))
module Delete_base_contract = Heap_contract (DH) (DK)

module Delete_base_clocks =
  Heap_clocks
    (DH)
    (struct
      let insert_comparisons = 2.0
      let insert_words = flat_budget
      let query_comparisons l = (6. *. l) +. 6.
      let query_words l = (60. *. l) +. 60.
    end)

(* ----------------------------------------------------------- delete's contract *)

(* The book's description on sorted lists: positives, negatives, and the invariant
   restored the only way the type allows. Live is the first list; a drain gives the
   multiset difference. *)
module Model = struct
  type t = int list * int list

  let rec settle = function
    | ([], _ | _, []) as m -> m
    | (p :: ps as pos), n :: ns ->
      if p < n then pos, n :: ns else if p = n then settle (ps, ns) else settle (pos, ns)
  ;;

  let empty = [], []
  let is_empty (pos, _) = pos = []
  let find_min (pos, _) = List.hd pos
  let insert x (pos, neg) = settle (List.merge compare [ x ] pos, neg)
  let delete x (pos, neg) = settle (pos, List.merge compare [ x ] neg)
  let delete_min (pos, neg) = settle (List.tl pos, neg)

  let merge (pos1, neg1) (pos2, neg2) =
    settle (List.merge compare pos1 pos2, List.merge compare neg1 neg2)
  ;;

  let rec drain = function
    | [], _ -> []
    | pos, [] -> pos
    | (p :: ps as pos), n :: ns ->
      if p < n
      then p :: drain (ps, n :: ns)
      else if p = n
      then drain (ps, ns)
      else drain (pos, ns)
  ;;

  let size (pos, neg) = List.length pos + List.length neg
end

module Delete_tests
    (D : HEAP_WITH_DELETE with type Element.t = int)
    (K : HEAP_WITH_DELETE with type Element.t = int * int) =
struct
  let of_list xs = List.fold_left (fun h x -> D.insert x h) D.empty xs
  let drain h = drain_with ~is_empty:D.is_empty ~head:D.find_min ~tail:D.delete_min h

  let run name =
    let t label = name ^ ": " ^ label in
    let drains_to note what want h =
      match drain h with
      | out when out = want -> ()
      | out -> note (Printf.sprintf "%s drains to %s" what (string_of_int_list out))
      | exception e -> note (Printf.sprintf "%s raised %s" what (Printexc.to_string e))
    in
    all_of (t "delete on the empty heap leaves it empty") (fun note ->
      let h = D.delete 3 D.empty in
      if not (D.is_empty h) then note "not empty";
      refused note "find_min" "find_min: empty heap" (fun () -> D.find_min h);
      refused note "delete_min" "delete_min: empty heap" (fun () -> D.delete_min h));
    all_of
      (t "delete takes out one copy of a present element, wherever it sits")
      (fun note ->
         let h = of_list [ 4; 2; 6; 1; 3; 5; 7 ] in
         drains_to note "delete 1, the minimum" [ 2; 3; 4; 5; 6; 7 ] (D.delete 1 h);
         drains_to note "delete 7, the maximum" [ 1; 2; 3; 4; 5; 6 ] (D.delete 7 h);
         drains_to note "delete 4, in the middle" [ 1; 2; 3; 5; 6; 7 ] (D.delete 4 h);
         drains_to
           note
           "delete 4 then 1 then 7"
           [ 2; 3; 5; 6 ]
           (h |> D.delete 4 |> D.delete 1 |> D.delete 7);
         let d = of_list [ 2; 2; 2 ] in
         drains_to note "one of three copies" [ 2; 2 ] (D.delete 2 d);
         drains_to note "two of three copies" [ 2 ] (d |> D.delete 2 |> D.delete 2);
         drains_to note "all three copies" [] (d |> D.delete 2 |> D.delete 2 |> D.delete 2);
         let r = h |> D.delete 1 |> D.delete 2 |> D.delete 3 |> D.delete 4 in
         if D.find_min r <> 5
         then note (Printf.sprintf "find_min after four deletes: %d" (D.find_min r)));
    all_of (t "an element can be deleted before it has been inserted") (fun note ->
      drains_to note "delete 3, insert 3" [] (D.empty |> D.delete 3 |> D.insert 3);
      drains_to
        note
        "delete 3 twice, insert 3 twice"
        []
        (D.empty |> D.delete 3 |> D.delete 3 |> D.insert 3 |> D.insert 3);
      drains_to
        note
        "delete 3 twice, insert 3 three times"
        [ 3 ]
        (D.empty |> D.delete 3 |> D.delete 3 |> D.insert 3 |> D.insert 3 |> D.insert 3);
      drains_to
        note
        "insert 1, delete 3, insert 3"
        [ 1 ]
        (D.empty |> D.insert 1 |> D.delete 3 |> D.insert 3);
      drains_to
        note
        "insert 1, delete 3, insert 3 twice"
        [ 1; 3 ]
        (D.empty |> D.insert 1 |> D.delete 3 |> D.insert 3 |> D.insert 3);
      drains_to
        note
        "insert 1, delete 3, insert 2, insert 3"
        [ 1; 2 ]
        (D.empty |> D.insert 1 |> D.delete 3 |> D.insert 2 |> D.insert 3);
      let h = D.empty |> D.delete 3 |> D.delete 5 in
      if not (D.is_empty h) then note "two pending deletes are not empty";
      drains_to
        note
        "pending 3 and 5, insert 3, 4, 5"
        [ 4 ]
        (h |> D.insert 3 |> D.insert 4 |> D.insert 5));
    (* The invariant leaves a negative below the live minimum no place to stay. *)
    all_of (t "a delete below the minimum is let go") (fun note ->
      drains_to
        note
        "insert 5, delete 3, insert 3"
        [ 3; 5 ]
        (D.empty |> D.insert 5 |> D.delete 3 |> D.insert 3);
      drains_to
        note
        "insert 5, delete 3, delete 5"
        []
        (D.empty |> D.insert 5 |> D.delete 3 |> D.delete 5);
      drains_to
        note
        "delete 3, insert 5, insert 3"
        [ 3; 5 ]
        (D.empty |> D.delete 3 |> D.insert 5 |> D.insert 3);
      drains_to
        note
        "insert 5, delete 1, delete 2, delete 5, insert 1"
        [ 1 ]
        (D.empty |> D.insert 5 |> D.delete 1 |> D.delete 2 |> D.delete 5 |> D.insert 1);
      (* Pending 3 and 5, and 5 comes first: the 3 is let go when 5 becomes the minimum. *)
      drains_to
        note
        "delete 3, delete 5, insert 5, 4, 3"
        [ 3; 4 ]
        (D.empty |> D.delete 3 |> D.delete 5 |> D.insert 5 |> D.insert 4 |> D.insert 3));
    all_of (t "cancellations cascade") (fun note ->
      let h =
        List.fold_left (fun h x -> D.delete x h) (of_list (upto 10)) (List.tl (upto 10))
      in
      if D.find_min h <> 0 then note (Printf.sprintf "find_min %d, want 0" (D.find_min h));
      if not (D.is_empty (D.delete_min h))
      then note "delete_min of the last live element is not empty";
      drains_to note "0 to 9, 1 to 9 deleted" [ 0 ] h;
      let d = of_list [ 1; 2; 2; 3; 3; 3 ] in
      drains_to
        note
        "1 2 2 3 3 3, one 2 and two 3s deleted"
        [ 1; 2; 3 ]
        (d |> D.delete 3 |> D.delete 2 |> D.delete 3);
      drains_to
        note
        "every other of 0 to 19 deleted"
        (List.filter (fun x -> x mod 2 = 0) (upto 20))
        (List.fold_left
           (fun h x -> D.delete x h)
           (of_list (upto 20))
           (List.filter (fun x -> x mod 2 = 1) (upto 20))));
    all_of (t "a merge cancels across its operands") (fun note ->
      let pending x = D.delete x D.empty in
      drains_to note "pending 5 with 5" [] (D.merge (pending 5) (of_list [ 5 ]));
      drains_to note "5 with pending 5" [] (D.merge (of_list [ 5 ]) (pending 5));
      drains_to note "1 5 with pending 5" [ 1 ] (D.merge (of_list [ 1; 5 ]) (pending 5));
      drains_to note "pending 5 with 1 5" [ 1 ] (D.merge (pending 5) (of_list [ 1; 5 ]));
      drains_to
        note
        "3 5 less 5, with 5"
        [ 3; 5 ]
        (D.merge (of_list [ 3; 5 ] |> D.delete 5) (of_list [ 5 ]));
      drains_to
        note
        "1 5 less 5, with pending 1"
        []
        (D.merge (of_list [ 1; 5 ] |> D.delete 5) (pending 1));
      drains_to
        note
        "1 5 less 5, with 2 less 1: the 1 was let go, the 5 still cancels"
        [ 1; 2 ]
        (D.merge (of_list [ 1; 5 ] |> D.delete 5) (of_list [ 2 ] |> D.delete 1));
      drains_to
        note
        "pending 5 with pending 5, then 5 5"
        []
        (D.merge (pending 5) (pending 5) |> D.insert 5 |> D.insert 5);
      if not (D.is_empty (D.merge (pending 5) (pending 3)))
      then note "two pendings merged are not empty");
    all_of
      (t "a version with a pending delete serves several futures, untouched")
      (fun note ->
         let h = D.empty |> D.insert 1 |> D.delete 3 in
         drains_to note "insert 3" [ 1 ] (D.insert 3 h);
         drains_to note "insert 2" [ 1; 2 ] (D.insert 2 h);
         drains_to note "delete_min" [] (D.delete_min h);
         drains_to note "delete_min, insert 3" [] (h |> D.delete_min |> D.insert 3);
         drains_to note "delete 1" [] (D.delete 1 h);
         drains_to note "delete 1, insert 3" [] (h |> D.delete 1 |> D.insert 3);
         drains_to note "merge with itself" [ 1; 1 ] (D.merge h h);
         drains_to
           note
           "merge with itself, insert 3 twice"
           [ 1; 1 ]
           (D.merge h h |> D.insert 3 |> D.insert 3);
         drains_to note "the version" [ 1 ] h);
    all_of
      (t "equal keys, distinct tags: a delete takes exactly one of them")
      (fun note ->
         let xs = [ 2, 0; 2, 1; 1, 2; 3, 3; 2, 4 ] in
         let h = List.fold_left (fun h x -> K.insert x h) K.empty xs in
         let drain h =
           drain_with ~is_empty:K.is_empty ~head:K.find_min ~tail:K.delete_min h
         in
         let keys_after ?(among = xs) what want h =
           let out = drain h in
           let keys = List.map fst out in
           if keys <> want
           then
             note
               (Printf.sprintf
                  "%s: keys %s, want %s"
                  what
                  (string_of_int_list keys)
                  (string_of_int_list want))
           else if List.exists (fun x -> not (List.mem x among)) out
           then note (what ^ ": an element that was never inserted")
           else if List.length (List.sort_uniq compare out) <> List.length out
           then note (what ^ ": an element twice")
         in
         keys_after "delete (2, 99)" [ 1; 2; 2; 3 ] (K.delete (2, 99) h);
         keys_after
           "delete (2, 99) twice"
           [ 1; 2; 3 ]
           (h |> K.delete (2, 99) |> K.delete (2, 99));
         keys_after
           "delete (2, 99) three times"
           [ 1; 3 ]
           (h |> K.delete (2, 99) |> K.delete (2, 99) |> K.delete (2, 99));
         keys_after "delete (1, 99)" [ 2; 2; 2; 3 ] (K.delete (1, 99) h);
         keys_after
           ~among:((3, 5) :: xs)
           "delete (3, 99), then insert (3, 5): one of the two 3s"
           [ 1; 2; 2; 2; 3 ]
           (h |> K.delete (3, 99) |> K.insert (3, 5));
         keys_after
           ~among:((3, 5) :: xs)
           "delete (3, 99) twice, then insert (3, 5)"
           [ 1; 2; 2; 2 ]
           (h |> K.delete (3, 99) |> K.delete (3, 99) |> K.insert (3, 5)));
    all_of
      (t
         "a random trace of 6000 inserts, deletes, merges and delete_mins over earlier \
          versions, against the book's description on sorted lists")
      (fun note ->
         Random.init 20261008;
         let n = 6_000 in
         let v = Array.make (n + 1) D.empty
         and model = Array.make (n + 1) Model.empty in
         for i = 1 to n do
           let p = Random.int i
           and q = Random.int i in
           let what, h, m =
             match Random.int 6 with
             | 0 when Model.size model.(p) + Model.size model.(q) <= 600 ->
               "merge", D.merge v.(p) v.(q), Model.merge model.(p) model.(q)
             | 1 when not (Model.is_empty model.(p)) ->
               "delete_min", D.delete_min v.(p), Model.delete_min model.(p)
             | 2 | 3 ->
               (* A present element half the time, any element the other half. *)
               let live = Model.drain model.(p) in
               let x =
                 if live <> [] && Random.bool ()
                 then List.nth live (Random.int (List.length live))
                 else Random.int 64
               in
               "delete", D.delete x v.(p), Model.delete x model.(p)
             | _ ->
               let x = Random.int 64 in
               "insert", D.insert x v.(p), Model.insert x model.(p)
           in
           v.(i) <- h;
           model.(i) <- m;
           if Model.is_empty m
           then (
             if not (D.is_empty h) then note (Printf.sprintf "%s %d is not empty" what i))
           else if D.is_empty h
           then note (Printf.sprintf "%s %d is empty" what i)
           else if D.find_min h <> Model.find_min m
           then
             note
               (Printf.sprintf
                  "%s %d: find_min %d, want %d"
                  what
                  i
                  (D.find_min h)
                  (Model.find_min m))
         done;
         for i = 0 to n do
           if i mod 200 = 0
           then
             drains_to note (Printf.sprintf "version %d" i) (Model.drain model.(i)) v.(i)
         done)
  ;;
end

module Delete_contract = Delete_tests (DH) (DK)

(* ------------------------------------------------------------ delete's clocks *)

(* The budgets of Figure 9.8 for one operation, and for a sequence of m operations m times
   the amortized budget at L = log2 (m + 1), half of Figure 9.8's query budget: the dearest
   sequence spends a quarter of that a piece, the cascade a little over. *)
let delete_insert_budget = 2.0, flat_budget
let delete_query_budget l = (6. *. l) +. 6., (60. *. l) +. 60.

let delete_amortized_budget m =
  let l = log2 (m + 1) in
  float_of_int m *. ((3. *. l) +. 3.), float_of_int m *. ((30. *. l) +. 30.)
;;

let delete_within name ~budget:(cb, wb) ~what (c, w) =
  check
    (Printf.sprintf
       "%s: %s spends %.0f comparisons and %.0f words, budget %.0f and %.0f"
       name
       what
       c
       w
       cb
       wb)
    (c <= cb && w <= wb)
;;

(* A heap of n random elements, every 97th of them in sorted order deleted, all of them
   above the minimum, so that negatives are pending and the check has something to look at. *)
let dh_pending n =
  Random.init n;
  let xs = List.init n (fun _ -> 1 + Random.int 1_000_000) in
  let h = Delete_contract.of_list xs in
  List.fold_left
    (fun h x -> DH.delete x h)
    h
    (List.filteri (fun i _ -> i > 0 && i mod 97 = 0) (List.sort compare xs))
;;

let test_delete_worst_case name n =
  let h = dh_pending n in
  let l = log2 (n + 1) in
  List.iter
    (fun (what, x) ->
       delete_within
         name
         ~budget:delete_insert_budget
         ~what:(Printf.sprintf "insert %s into %d elements with negatives pending" what n)
         (spent_only (fun () -> DH.insert x h)))
    [ "below the minimum", 0; "above the maximum", 2_000_000; "in the middle", 500_000 ];
  delete_within
    name
    ~budget:(delete_query_budget l)
    ~what:(Printf.sprintf "find_min on %d elements with negatives pending" n)
    (spent_only (fun () -> DH.find_min h))
;;

type dop =
  | DInsert of int
  | DDelete of int
  | DFind_min
  | DDelete_min

(* Runs [ops] from the empty heap, single-threaded, every operation on the clocks: the sum
   of the sequence, and the dearest find_min and delete_min on their own. *)
let run_delete_ops ops =
  let h = ref DH.empty
  and sum = ref 0
  and total_c = ref 0.0
  and total_w = ref 0.0
  and dearest_find = ref (0.0, 0.0)
  and dearest_delete_min = ref (0.0, 0.0) in
  let dearer (a, b) (c, d) = if c > a then c, d else a, b in
  Array.iter
    (fun op ->
       let c, w =
         match op with
         | DInsert x ->
           let h', cw = spent (fun () -> DH.insert x !h) in
           h := h';
           cw
         | DDelete x ->
           let h', cw = spent (fun () -> DH.delete x !h) in
           h := h';
           cw
         | DFind_min ->
           let x, cw = spent (fun () -> DH.find_min !h) in
           sum := !sum + x;
           dearest_find := dearer !dearest_find cw;
           cw
         | DDelete_min ->
           let h', cw = spent (fun () -> DH.delete_min !h) in
           h := h';
           dearest_delete_min := dearer !dearest_delete_min cw;
           cw
       in
       total_c := !total_c +. c;
       total_w := !total_w +. w)
    ops;
  ignore (Sys.opaque_identity !sum);
  (!total_c, !total_w), !dearest_find, !dearest_delete_min
;;

let delete_sequences n =
  Random.init n;
  let xs = Array.init n (fun _ -> Random.int 1_000_000) in
  [ ( "n random inserts, then a find_min and a delete of each in a random order, to \
       exhaustion"
    , Array.concat
        [ Array.map (fun x -> DInsert x) xs
        ; Array.concat
            (List.map
               (fun x -> [| DFind_min; DDelete x |])
               (shuffle n (Array.to_list xs)))
        ] )
  ; ( "insert x then delete x at a live size of 1000, n times over"
    , Array.init
        (1000 + (2 * n))
        (fun i ->
           if i < 1000
           then DInsert xs.(i mod n)
           else if i mod 2 = 0
           then DInsert xs.(i mod n)
           else DDelete xs.((i - 1) mod n)) )
  ; ( "n inserts, then delete_min and a delete of a random present element in turn, to \
       exhaustion"
    , let sorted = Array.of_list (List.sort compare (Array.to_list xs)) in
      Array.concat
        [ Array.map (fun x -> DInsert x) xs
        ; Array.init n (fun i ->
            if i mod 2 = 0 then DDelete_min else DDelete sorted.(n - 1 - (i / 2)))
        ] )
  ]
;;

let test_delete_amortized name n =
  List.iter
    (fun (what, ops) ->
       let m = Array.length ops in
       let total, find, _ = run_delete_ops ops in
       let name = Printf.sprintf "%s, n=%d, %s" name n what in
       delete_within
         name
         ~budget:(delete_amortized_budget m)
         ~what:(Printf.sprintf "the sequence of %d operations" m)
         total;
       if Array.mem DFind_min ops
       then
         delete_within
           name
           ~budget:(delete_query_budget (log2 (m + 1)))
           ~what:"the dearest find_min"
           find)
    (delete_sequences n)
;;

(* 0 to n inserted, 1 to n deleted, all above the live minimum, then the one delete_min
   that cancels the n pairs. *)
let test_delete_cascade name n =
  let ops =
    Array.concat
      [ Array.init (n + 1) (fun i -> DInsert i)
      ; Array.init n (fun i -> DDelete (i + 1))
      ; [| DDelete_min |]
      ]
  in
  let m = Array.length ops in
  let total, _, (c, w) = run_delete_ops ops in
  let name = Printf.sprintf "%s, cascade of %d" name n in
  delete_within
    name
    ~budget:(delete_amortized_budget m)
    ~what:(Printf.sprintf "the sequence of %d operations" m)
    total;
  (* That the clock sees the cascade: the one delete_min cancels n pairs and compares the
     two minimums at least once each, n comparisons and more. *)
  check
    (Printf.sprintf
       "%s: the one delete_min spends %.0f comparisons and %.0f words, at least %d \
        comparisons"
       name
       c
       w
       n)
    (c >= float_of_int n)
;;

let test_heap_with_delete () =
  let name = "HeapWithDelete" in
  Delete_base_contract.run (name ^ ", delete unused");
  Delete_base_clocks.test_all_ones (name ^ ", delete unused");
  Delete_base_clocks.test_sequences (name ^ ", delete unused") 1_000;
  Delete_base_clocks.test_sequences (name ^ ", delete unused") 100_000;
  Delete_base_clocks.test_merges (name ^ ", delete unused") 1_000;
  Delete_base_clocks.test_versions (name ^ ", delete unused");
  Delete_contract.run name;
  test_delete_worst_case name 1_000;
  test_delete_worst_case name 100_000;
  test_delete_amortized name 1_000;
  test_delete_amortized name 100_000;
  test_delete_cascade name 1_000;
  test_delete_cascade name 100_000
;;

(* -------------------------------------------------------------------- cases *)

let tests =
  [ case "[Figure 9.6] BinaryRandomAccessList" test_binary
  ; case "[Exercise 9.1] drop" test_drop
  ; case "[Exercise 9.2] create" test_create
  ; case "[Exercise 9.3] SparseBinaryRandomAccessList" test_sparse
  ; case "[Exercise 9.1, 9.3] SparseBinaryRandomAccessList.drop" test_sparse_drop
  ; case "[Exercise 9.2, 9.3] SparseBinaryRandomAccessList.create" test_sparse_create
  ; case "[Exercise 9.4] Zeroless: binary numbers without zeros" test_zeroless
  ; case "[Exercise 9.5] ZerolessBinaryRandomAccessList" test_zeroless_list
  ; case "[Exercise 9.9] ZerolessRedundantBinaryRandomAccessList" test_redundant
  ; case "[Exercise 9.10] ScheduledZerolessRedundantBinaryRandomAccessList" test_scheduled
  ; case "[Example 9.2.4] SegmentedRepresentationOne" test_seg1
  ; case "[Example 9.2.4] SegmentedRepresentationTwo" test_seg2
  ; case "[Exercise 9.11] SegmentedBinomialHeap" test_segmented_heap
  ; case "[Exercise 9.12] DenseRepresentation, digits 0 to 4" test_five_dense
  ; case "[Exercise 9.12] SegmentedRepresentation, digits 0 to 4" test_five_segmented
  ; case "[Exercise 9.13] SegmentedRandomAccessList" test_seg_list
  ; case "[Figure 9.7] SkewBinaryRandomAccessList" test_skew
  ; case "[Exercise 9.14] SkewHoodMelvilleQueue" test_skew_queue
  ; case "[Figure 9.8] SkewBinomialHeap" test_skew_heap
  ; case "[Exercise 9.16] HeapWithDelete" test_heap_with_delete
  ]
;;
