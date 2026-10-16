(* The checks Chapters 10 and 11 hold their catenable lists to, written once. Both
   chapters declare CATENABLE_LIST, Figure 10.3's signature, as the same signature, so the
   functor here takes the lists of both, and a catenable deque as well: the contract, the
   sequences from empty, and the clocks over versions, under one constant. Each list
   words its own refusal of an empty list, so the message is a parameter. *)

open Harness

module Contract
    (C : Okasaki.Ch10.CATENABLE_LIST)
    (P : sig
       (* The most any clock may read, in words an operation. *)
       val constant : float

       (* What [op] on an empty list fails with. *)
       val refusal : string -> string
     end) =
struct
  let ( ++ ) = C.( ++ )
  let to_list xs = drain_with ~is_empty:C.is_empty ~head:C.head ~tail:C.tail xs
  let by_cons l = List.fold_right C.cons l C.empty
  let by_snoc l = List.fold_left C.snoc C.empty l
  let singleton x = C.cons x C.empty

  (* ((s0 ++ s1) ++ s2) ++ ...: one root with every other element a child of it. *)
  let fat_of l = List.fold_left (fun acc x -> acc ++ singleton x) C.empty l

  (* s0 ++ (s1 ++ (s2 ++ ...)): a chain, every node with one child. *)
  let chain_of l = List.fold_right (fun x acc -> singleton x ++ acc) l C.empty
  let fat n = fat_of (upto n)
  let chain n = chain_of (upto n)
  let shifted n = List.init n (fun i -> 100 + i)

  (* xs ++ xs, k times over: 2^k copies of one shared tree. *)
  let rec squared k xs = if k = 0 then xs else squared (k - 1) (xs ++ xs)
  let rec copies k l = if k = 0 then [] else l @ copies (k - 1) l

  let builders =
    [ "cons", by_cons; "snoc", by_snoc; "a fat tree", fat_of; "a chain", chain_of ]
  ;;

  let run_contract name =
    let t label = Printf.sprintf "%s: %s" name label in
    check (t "empty is empty") (C.is_empty C.empty);
    check (t "cons makes it non-empty") (not (C.is_empty (C.cons 1 C.empty)));
    check (t "snoc makes it non-empty") (not (C.is_empty (C.snoc C.empty 1)));
    check (t "empty ++ empty is empty") (C.is_empty (C.empty ++ C.empty));
    check_failure (t "head of empty refuses") (P.refusal "head") (fun () ->
      C.head C.empty);
    check_failure (t "tail of empty refuses") (P.refusal "tail") (fun () ->
      C.tail C.empty);
    let sizes = [ 0; 1; 2; 3; 7; 100; 1000 ] in
    all_of (t "built every way, drained in order, at every size") (fun note ->
      List.iter
        (fun n ->
           List.iter
             (fun (how, build) ->
                if to_list (build (upto n)) <> upto n
                then note (Printf.sprintf "%d by %s" n how))
             builders)
        sizes);
    all_of
      (t "xs ++ ys is xs then ys, at every pair of sizes up to 6, built every way")
      (fun note ->
         for a = 0 to 6 do
           for b = 0 to 6 do
             let l1 = upto a
             and l2 = shifted b in
             List.iter
               (fun (h1, b1) ->
                  List.iter
                    (fun (h2, b2) ->
                       if to_list (b1 l1 ++ b2 l2) <> l1 @ l2
                       then note (Printf.sprintf "%d by %s ++ %d by %s" a h1 b h2))
                    builders)
               builders
           done
         done);
    all_of (t "++ is associative: both bracketings drain the same") (fun note ->
      List.iter
        (fun (a, b, c) ->
           let l1 = upto a
           and l2 = shifted b
           and l3 = List.init c (fun i -> 200 + i) in
           let xs = by_cons l1
           and ys = fat_of l2
           and zs = chain_of l3 in
           if
             to_list (xs ++ ys ++ zs) <> l1 @ l2 @ l3
             || to_list (xs ++ (ys ++ zs)) <> l1 @ l2 @ l3
           then note (Printf.sprintf "%d, %d, %d" a b c))
        [ 0, 0, 1; 1, 0, 0; 1, 1, 1; 3, 0, 3; 5, 4, 3; 100, 1, 100 ]);
    (* a version is what it was, whatever is done to it afterwards *)
    let xs = fat 10
    and ys = chain_of (shifted 5) in
    let zs = xs ++ ys in
    ignore
      (Sys.opaque_identity
         (to_list (C.tail zs), to_list (C.tail xs), C.cons 7 ys, C.snoc zs 8));
    check
      (t "xs, ys and xs ++ ys are what they were after a tail, a cons and a snoc on them")
      (to_list xs = upto 10 && to_list ys = shifted 5 && to_list zs = upto 10 @ shifted 5);
    check
      (t "xs ++ xs squared ten times is 1024 copies of xs, one tree shared throughout")
      (to_list (squared 10 (by_cons (upto 10))) = copies 1024 (upto 10));
    (* a random trace over earlier versions, every version against a list model *)
    let steps = 600
    and cap = 2_000 in
    let v = Array.make (steps + 1) (C.empty, []) in
    Random.init 20261013;
    all_of
      (t
         (Printf.sprintf
            "a random trace of %d cons, snoc, ++, tail and head on random earlier \
             versions, every version against a list model"
            steps))
      (fun note ->
         for i = 1 to steps do
           let a, la = v.(Random.int i) in
           v.(i)
           <- (match Random.int 5 with
               | 0 -> C.cons i a, i :: la
               | 1 -> C.snoc a i, la @ [ i ]
               | 2 ->
                 let b, lb = v.(Random.int i) in
                 if List.length la + List.length lb > cap then a, la else a ++ b, la @ lb
               | 3 -> if la = [] then a, la else C.tail a, List.tl la
               | _ ->
                 if la <> [] && C.head a <> List.hd la
                 then note (Printf.sprintf "head at step %d" i);
                 a, la)
         done;
         Array.iteri
           (fun i (c, l) -> if to_list c <> l then note (Printf.sprintf "version #%d" i))
           v)
  ;;

  (* ------------------------------------------- sequences: one thread, from empty *)

  (* Each driver returns the number of operations it did. *)
  let drain n xs =
    for _ = 1 to n do
      xs := C.tail !xs
    done
  ;;

  let sequences n =
    [ ( "cons n then n tails"
      , fun () ->
          let xs = ref C.empty in
          for i = 1 to n do
            xs := C.cons i !xs
          done;
          drain n xs;
          ignore (Sys.opaque_identity !xs);
          2 * n )
    ; ( "snoc n then n tails"
      , fun () ->
          let xs = ref C.empty in
          for i = 1 to n do
            xs := C.snoc !xs i
          done;
          drain n xs;
          ignore (Sys.opaque_identity !xs);
          2 * n )
    ; ( "n singletons ++ left to right, the fat tree, then n tails"
      , fun () ->
          let xs = ref C.empty in
          for i = 1 to n do
            xs := !xs ++ singleton i
          done;
          drain n xs;
          ignore (Sys.opaque_identity !xs);
          3 * n )
    ; ( "n singletons ++ right to left, the chain, then n tails"
      , fun () ->
          let xs = ref C.empty in
          for i = n downto 1 do
            xs := singleton i ++ !xs
          done;
          drain n xs;
          ignore (Sys.opaque_identity !xs);
          3 * n )
    ; ( "a random mix of cons, snoc, ++ with a list of three, tail and head"
      , fun () ->
          Random.init 20261014;
          let xs = ref C.empty
          and ops = ref 0
          and sum = ref 0 in
          for i = 1 to n do
            match Random.int 5 with
            | 0 ->
              xs := C.cons i !xs;
              incr ops
            | 1 ->
              xs := C.snoc !xs i;
              incr ops
            | 2 ->
              xs := !xs ++ by_cons [ i; i + 1; i + 2 ];
              ops := !ops + 4
            | 3 ->
              if not (C.is_empty !xs) then xs := C.tail !xs;
              incr ops
            | _ ->
              if not (C.is_empty !xs) then sum := !sum + C.head !xs;
              incr ops
          done;
          ignore (Sys.opaque_identity !xs);
          ignore (Sys.opaque_identity !sum);
          !ops )
    ]
  ;;

  let mean f =
    let ops, c = cost f in
    c /. float_of_int ops
  ;;

  let run_sequences name =
    let t label = Printf.sprintf "%s: %s" name label in
    List.iter
      (fun (label, n, longer) ->
         List.iter
           (fun (sequence, f) ->
              let c = mean f in
              check
                (t
                   (Printf.sprintf
                      "%s, amortised O(1)%s: %.2f words per operation at n=%d"
                      sequence
                      longer
                      c
                      n))
                (c <= P.constant))
           (sequences n))
      [ "", 1_000, ""; "", 100_000, ", a hundred times longer" ]
  ;;

  (* ---------------------------------------------------- persistence: versions *)

  (* Every version of a drain of the fat tree of n, which is where tail has the most
     children to link. *)
  let fat_versions n =
    let v = Array.make n C.empty in
    v.(0) <- fat n;
    for i = 1 to n - 1 do
      v.(i) <- C.tail v.(i - 1)
    done;
    v
  ;;

  (* An operation whose result is kept from the optimiser and then dropped. *)
  let op f xs = ignore (Sys.opaque_identity (f xs))
  let tail_op = op C.tail

  (* [op] k times over from each version, the dearest version's mean. *)
  let dearest_repeated v k op =
    let dear = ref (0, 0.0) in
    Array.iteri
      (fun i x ->
         let _, c =
           cost (fun () ->
             for _ = 1 to k do
               op x
             done)
         in
         let c = c /. float_of_int k in
         if c > snd !dear then dear := i, c)
      v;
    !dear
  ;;

  let run_versions name =
    let t label = Printf.sprintf "%s, persistently: %s" name label in
    let n = 1_000
    and k = 20 in
    let v = fat_versions n in
    List.iter
      (fun (label, op) ->
         let i, c = dearest_repeated v k op in
         check
           (t
              (Printf.sprintf
                 "%s, %d times over from each version of a drain of the fat tree of %d, \
                  dearest from #%d: %.2f words per operation"
                 label
                 k
                 n
                 i
                 c))
           (c <= P.constant))
      [ "tail", tail_op
      ; ( "tail then head"
        , op (fun xs ->
            let ys = C.tail xs in
            if C.is_empty ys then 0 else C.head ys) )
      ; "++ a singleton", op (fun xs -> xs ++ singleton 0)
      ; "cons then tail", op (fun xs -> C.tail (C.cons 0 xs))
      ];
    let i, c = dearest_repeated v 1 (op C.head) in
    check
      (t
         (Printf.sprintf
            "head allocates nothing at any version of the drain, dearest #%d at %.0f \
             words"
            i
            c))
      (c = 0.0);
    let xs = squared 10 (by_cons (upto 10)) in
    let c =
      mean (fun () ->
        let xs = ref xs in
        drain 10_240 xs;
        ignore (Sys.opaque_identity !xs);
        10_240)
    in
    check
      (t
         (Printf.sprintf
            "a list squared ten times, 1024 copies of one tree, drained: %.2f words per \
             tail"
            c))
      (c <= P.constant);
    let steps = 100_000 in
    let v = Array.make (steps + 1) C.empty in
    Random.init 20261015;
    let c =
      mean (fun () ->
        let sum = ref 0 in
        for i = 1 to steps do
          let a = v.(Random.int i) in
          v.(i)
          <- (match Random.int 5 with
              | 0 -> C.cons i a
              | 1 -> C.snoc a i
              | 2 -> a ++ v.(Random.int i)
              | 3 -> if C.is_empty a then a else C.tail a
              | _ ->
                if not (C.is_empty a) then sum := !sum + C.head a;
                a)
        done;
        ignore (Sys.opaque_identity !sum);
        steps)
    in
    check
      (t
         (Printf.sprintf
            "a random trace of %d operations, each on a random earlier version: %.2f \
             words per operation"
            steps
            c))
      (c <= P.constant)
  ;;

  let run name =
    run_contract name;
    run_sequences name;
    run_versions name
  ;;
end
