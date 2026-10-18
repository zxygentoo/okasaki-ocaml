# okasaki-ocaml

Working through Chris Okasaki's [Purely Functional Data Structures](https://www.cambridge.org/core/books/purely-functional-data-structures/0409255DA1B48FA731859AC72E34D494) in OCaml.

## Requirements

OCaml 5.3 or later, dune, and Alcotest for the tests. With opam:

```sh
git clone https://github.com/zxygentoo/okasaki-ocaml
cd okasaki-ocaml
opam install . --deps-only --with-test
```

## Layout

- `lib/chXX.ml`: the figures and exercises of chapter XX
- `test/test_chXX.ml`: their tests (written by a coding agent); the other files in `test/` are the shared harness and contracts

## Running the tests

```sh
make test           # all chapters
make test-ch09      # Chapter 9 only
```

## Coverage

- All the important code from the figures, and every implementation exercise except 10.7 (it only works around SML's lack of recursive modules, which OCaml's `module rec` makes unnecessary: Figure 10.7 compiles as written).
- Most proof exercises are left out (doing them in Lean or Rocq might be a fun future project).
- Everything is tested for correctness, and its performance bounds are checked empirically (proving them in Lean or Rocq too would be a *VERY* fun future project).
