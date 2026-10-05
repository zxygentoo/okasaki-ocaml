# make test          every chapter's tests
# make test-ch9      one chapter's

.PHONY: test test-ch2 test-ch3 test-ch4 test-ch5 test-ch6 test-ch7 test-ch8 test-ch9

test:
	dune exec test/main.exe

test-ch2:
	dune exec test/main.exe -- test ch2

test-ch3:
	dune exec test/main.exe -- test ch3

test-ch4:
	dune exec test/main.exe -- test ch4

test-ch5:
	dune exec test/main.exe -- test ch5

test-ch6:
	dune exec test/main.exe -- test ch6

test-ch7:
	dune exec test/main.exe -- test ch7

test-ch8:
	dune exec test/main.exe -- test ch8

test-ch9:
	dune exec test/main.exe -- test ch9
