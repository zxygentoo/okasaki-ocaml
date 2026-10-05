(* The one test runner: every chapter's cases, in order.

   All of them, one chapter, or one case of it by the number in its line:

   {v
   dune exec test/main.exe
   dune exec test/main.exe -- test ch9
   dune exec test/main.exe -- test ch9 3
   v}

   Run this way each case is printed as it starts and again as it ends. [dune test] runs
   them all too, but dune holds a command's output back until the command is over, so
   nothing shows for some twenty seconds; [dune test --no-buffer] lets it through.

   Every check that holds logs a line, so a failing case prints only the tail of its log
   and not the hundreds of lines before it. Alcotest names the file that has the whole of
   it, but [dune test] runs in a sandbox that is gone by the time the name is read: under
   [dune exec] the file stays. Only the first failing case is printed in full; [-e] prints
   them all. *)

let chapters =
  [ "ch2", Test_ch2.tests
  ; "ch3", Test_ch3.tests
  ; "ch4", Test_ch4.tests
  ; "ch5", Test_ch5.tests
  ; "ch6", Test_ch6.tests
  ; "ch7", Test_ch7.tests
  ; "ch8", Test_ch8.tests
  ; "ch9", Test_ch9.tests
  ]
;;

(* Alcotest prints a [SKIP] line for every case it leaves out, which buries one chapter's
   results under sixty lines of the others. So a chapter named on the command line is also
   the only one Alcotest is given. The command line itself is still Alcotest's to read. *)
let named = List.filter (fun (chapter, _) -> Array.mem chapter Sys.argv) chapters

let () =
  Alcotest.run ~tail_errors:(`Limit 20) "okasaki" (if named = [] then chapters else named)
;;
