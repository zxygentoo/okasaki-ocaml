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

let string_of_int_list l = "[" ^ String.concat ";" (List.map string_of_int l) ^ "]"

(* One Alcotest case. *)
let case name f = Alcotest.test_case name `Quick f
