(* The checks Chapters 9 and 10 hold their random-access lists to, written once. Every
   chapter declares RANDOM_ACCESS_LIST over again, but as the same signature, so the functor
   here takes the lists of both.

   The contract is aimed where the digits go wrong. A digit list may not end in a ZERO,
   which is what unconsTree's clause for the last ONE is for in Figure 9.6: emptying a list
   by tails has to give back the empty list, or isEmpty lies and every later head walks the
   zeros. The sizes 0 to 70 cross six powers of two, so every carry cascade and every
   borrow split of that length is exercised, and every index of every size is looked up.
   And update has to copy the whole path it walks, the ZEROs it passes in the list and the
   NODEs it passes in the tree, where lookup may skip both: a list read back after an
   update, and after an update and a cons, has to be the list that was meant, and the
   version that was updated has to read as it did, which is the whole of persistence here.

   The clock is allocation, as in the earlier chapters. It sees cons, head, tail and
   update, which allocate along the path they walk, and it cannot see a lookup that
   allocates nothing, so a lookup that scanned every leaf would read as free. lookup is
   held to the same budget all the same, which catches a lookup that copies, and its
   O(log n) rests on walking the path that update is measured on. The guard that the clock
   sees a linear operation at all is the update of a plain list. *)

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

module Contract (R : Okasaki.Ch9.RANDOM_ACCESS_LIST) = struct
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
module Plain : Okasaki.Ch9.RANDOM_ACCESS_LIST = struct
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

module Plain_tests = Contract (Plain)

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
