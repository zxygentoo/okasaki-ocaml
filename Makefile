.PHONY: test test-ch02 test-ch03 test-ch04 test-ch05 test-ch06 test-ch07 test-ch08 test-ch09 test-ch10 test-ch11

test:
	dune exec test/main.exe

test-ch02:
	dune exec test/main.exe -- test ch02

test-ch03:
	dune exec test/main.exe -- test ch03

test-ch04:
	dune exec test/main.exe -- test ch04

test-ch05:
	dune exec test/main.exe -- test ch05

test-ch06:
	dune exec test/main.exe -- test ch06

test-ch07:
	dune exec test/main.exe -- test ch07

test-ch08:
	dune exec test/main.exe -- test ch08

test-ch09:
	dune exec test/main.exe -- test ch09

test-ch10:
	dune exec test/main.exe -- test ch10

test-ch11:
	dune exec test/main.exe -- test ch11
