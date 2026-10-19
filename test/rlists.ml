(* The checks Chapters 9 and 10 hold their random-access lists to, written once. Every
   chapter declares RANDOM_ACCESS_LIST and RANDOM_ACCESS_LIST_LITE over again, but as the
   same signatures, so the functors here take the lists of both: Contract for a list whose
   every operation is worst-case, Lite for one whose stack is amortised.

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

(* A random run of a list, against a list: 60 operations, less what the model cannot
   take. On the empty list that is all but a cons; an index is drawn at large and taken
   modulo the length it meets, and a drop modulo one more than that. Drops are drawn only
   for a list that has one, Exercise 9.1's and 9.2's, and conses then come twice as
   often. *)
module Run = struct
  type op =
    | Cons of int
    | Tail
    | Update of int * int
    | Lookup of int
    | Drop of int

  let describe = function
    | Cons x -> Printf.sprintf "cons %d" x
    | Tail -> "tail"
    | Update (k, x) -> Printf.sprintf "update %d %d" k x
    | Lookup k -> Printf.sprintf "lookup %d" k
    | Drop k -> Printf.sprintf "drop %d" k
  ;;

  (* The run a draw makes from a list of [n] elements. *)
  let plan n draw =
    let rec go n = function
      | [] -> []
      | Cons x :: ops -> Cons x :: go (n + 1) ops
      | _ :: ops when n = 0 -> go n ops
      | Tail :: ops -> Tail :: go (n - 1) ops
      | Update (k, x) :: ops -> Update (k mod n, x) :: go n ops
      | Lookup k :: ops -> Lookup (k mod n) :: go n ops
      | Drop k :: ops ->
        let k = k mod (n + 1) in
        Drop k :: go (n - k) ops
    in
    go n draw
  ;;

  let length = 60

  let ops ~drops =
    QCheck.Gen.(
      [ (if drops then 2 else 1), map (fun x -> Cons x) (int_bound 99)
      ; 1, return Tail
      ; 1, map2 (fun k x -> Update (k, 1000 + x)) (int_bound 9999) (int_bound 99)
      ; 1, map (fun k -> Lookup k) (int_bound 9999)
      ]
      @ if drops then [ 1, map (fun k -> Drop k) (int_bound 9999) ] else [])
  ;;

  let draws ~drops = QCheck.Gen.(list_size (return length) (oneof_weighted (ops ~drops)))
  let runs ~drops = run_of ~length ~plan:(plan 0) ~show:describe (ops ~drops)
end

module Contract (R : Okasaki.Ch09.RANDOM_ACCESS_LIST) = struct
  (* The list whose index i holds List.nth xs i. *)
  let of_list xs = List.fold_right R.cons xs R.empty
  let to_list r = drain_with ~is_empty:R.is_empty ~head:R.head ~tail:R.tail r
  let lookups n r = List.init n (fun i -> R.lookup i r)
  let rec tails k r = if k = 0 then r else tails (k - 1) (R.tail r)

  (* A run from [r], which [model] describes: [after] sees the list and the model after
     every operation, [at_end] after the last, and [looked] every lookup with the model's
     answer; the run stops at the first that does not hold. [drop] makes the drops of a
     run that has them. *)
  let replay
        ?drop
        ?(after = fun _ _ -> true)
        ?(at_end = fun _ _ -> true)
        ?(looked = fun _ _ _ -> true)
        r
        model
        ops
    =
    let rec go r model = function
      | [] -> at_end r model
      | Run.Cons x :: ops -> step (R.cons x r) (x :: model) ops
      | Run.Tail :: ops -> step (R.tail r) (List.tl model) ops
      | Run.Update (k, x) :: ops ->
        step (R.update k x r) (List.mapi (fun j y -> if j = k then x else y) model) ops
      | Run.Lookup k :: ops -> looked k r (List.nth model k) && step r model ops
      | Run.Drop k :: ops ->
        (match drop with
         | Some drop -> step (drop k r) (List.drop k model) ops
         | None -> invalid_arg "replay: a drop in the run of a list without one")
    and step r model ops = after r model && go r model ops in
    go r model ops
  ;;

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
    (* Randomised, against the obvious model: a list. Checked after every operation. *)
    let replay ?after ?at_end ?looked draw =
      replay ?after ?at_end ?looked R.empty [] (Run.plan 0 draw)
    in
    let prop label =
      check_prop ~count:300 ~seed:20260926 (t label) (Run.runs ~drops:false)
    in
    prop
      "no operation raises on a valid index of a non-empty list, 300 random runs"
      (replay
         ~after:(fun r model ->
           ignore (R.is_empty r);
           if model <> [] then ignore (R.head r);
           true)
         ~looked:(fun k r _ ->
           ignore (R.lookup k r);
           true)
         ~at_end:(fun r model ->
           ignore (to_list r);
           ignore (lookups (List.length model) r);
           true));
    prop
      "is_empty agrees with a list model"
      (replay ~after:(fun r model ->
         agrees "is_empty" ~expect:(model = []) ~actual:(R.is_empty r) string_of_bool));
    prop
      "head agrees with a list model"
      (replay ~after:(fun r -> function
         | [] -> true
         | x :: _ -> agrees "head" ~expect:x ~actual:(R.head r) string_of_int));
    prop
      "lookup agrees with a list model"
      (replay ~looked:(fun k r x ->
         agrees "lookup %d" k ~expect:x ~actual:(R.lookup k r) string_of_int));
    prop
      "the whole list agrees with the model at the end of each run"
      (replay ~at_end:(fun r model ->
         agrees "read back" ~expect:model ~actual:(to_list r) string_of_int_list
         && agrees
              "looked up"
              ~expect:model
              ~actual:(lookups (List.length model) r)
              string_of_int_list));
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
module Plain : Okasaki.Ch09.RANDOM_ACCESS_LIST = struct
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

(* -------------------------------------------- the amortised list contract *)

(* For a list that offers the stack and nothing else (RANDOM_ACCESS_LIST_LITE), with cons,
   head and tail in O(1) amortised time: Exercises 9.9, 9.10 and 9.13, and Exercise 10.2,
   which has lookup and update as well but holds them to a clock of their own. The
   contract is about the order the elements come back in: every size from 0 to 70, both
   built by cons and left by tails from a longer list, read back, emptied, and moved back
   and forth by a cons and a tail in turn; a list of twenty thousand, whose digits run to
   thirteen positions, and a random walk from it; and random steps over a pool of
   versions, old ones used again, against a list model. The messages are the ones the
   other lists use.

   Amortised costs change what goes on the clock. A single operation may be dear, since it
   can do work that earlier ones left for later, so no single operation is held to
   anything. The clock goes on whole sequences, from the empty list to the last operation,
   and what is held to a budget is the mean, words per cons or tail, a constant whatever
   the size: the same budget at 3 (2^10 - 1) elements and at 3 (2^17 - 1). Each cons and
   tail is followed by a head, which reads the front of what it returns. An amortised
   bound in this book is one that survives persistence (section 6.2; 5.6 shows what goes
   wrong otherwise), so two of the sequences use one old version over and over, each time
   where a carry or a borrow could run the whole length: the list of 3 (2^k - 1) elements
   built by cons, which a zeroless redundant carry leaves with a THREE at every position,
   given as many conses as it took to build; and the list that 2 (2^k - 1) tails then
   leave with a ONE at every position, given as many tails as it took to make. Two more go
   back and forth, a cons and a tail in turn, from each of those lists, and then drain
   what they end with. And the plainest: a build by cons and its drain by tail.

   For a worst-case bound (Exercise 9.10) the same sequences run with every operation on
   its own clock, run_worst_costs, and the dearest single one is held to a constant. *)

module Lite (R : Okasaki.Ch09.RANDOM_ACCESS_LIST_LITE) = struct
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
       back at the end. A step names the places in the pool it reads and writes, so a step
       dropped in shrinking moves no other; a tail of an empty version is dropped. *)
    let size = 64 in
    let module Op = struct
      type t =
        | Cons of int * int * int
        | Tail of int * int

      let describe = function
        | Cons (x, from, into) -> Printf.sprintf "p%d <- cons %d p%d" into x from
        | Tail (from, into) -> Printf.sprintf "p%d <- tail p%d" into from
      ;;
    end
    in
    let plan draw =
      let len = Array.make size 0 in
      List.filter
        (function
          | Op.Cons (_, from, into) ->
            len.(into) <- len.(from) + 1;
            true
          | Op.Tail (from, into) when len.(from) > 0 ->
            len.(into) <- len.(from) - 1;
            true
          | Op.Tail _ -> false)
        draw
    in
    check_prop
      ~count:1
      ~seed:20260930
      (t
         "5000 random steps over a pool of versions, old ones used again: is_empty and \
          head after each, and every version read back at the end")
      (run_of
         ~length:5000
         ~plan
         ~show:Op.describe
         QCheck.Gen.
           [ ( 2
             , map3
                 (fun x from into -> Op.Cons (x, from, into))
                 (int_bound 999)
                 (int_bound (size - 1))
                 (int_bound (size - 1)) )
           ; ( 1
             , map2
                 (fun from into -> Op.Tail (from, into))
                 (int_bound (size - 1))
                 (int_bound (size - 1)) )
           ])
      (fun draw ->
         let pool = Array.make size (R.empty, []) in
         List.for_all
           (fun op ->
              let into, (r', model') =
                match op with
                | Op.Cons (x, from, into) ->
                  let r, model = pool.(from) in
                  into, (R.cons x r, x :: model)
                | Op.Tail (from, into) ->
                  let r, model = pool.(from) in
                  into, (R.tail r, List.tl model)
              in
              pool.(into) <- r', model';
              agrees
                "is_empty p%d"
                into
                ~expect:(model' = [])
                ~actual:(R.is_empty r')
                string_of_bool
              &&
              match model' with
              | [] -> true
              | x :: _ ->
                agrees "head p%d" into ~expect:x ~actual:(R.head r') string_of_int)
           (plan draw)
         && List.for_all
              (fun j ->
                 let r, model = pool.(j) in
                 agrees "p%d read back" j ~expect:model ~actual:(to_list r) show_list)
              (upto size));
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
