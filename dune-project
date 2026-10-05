(lang dune 3.22)

(name okasaki-ocaml)

(generate_opam_files true)

(source
 (github zxygentoo/okasaki-ocaml))

(package
 (name okasaki-ocaml)
 (synopsis
  "Working through Chris Okasaki's Purely Functional Data Structures in OCaml")
 (allow_empty)
 (depends
  (ocaml
   (>= 5.3))
  (alcotest
   (and
    :with-test
    (>= 1.9)))
  (ocamlformat :with-dev-setup)
  (ocaml-lsp-server :with-dev-setup)))
