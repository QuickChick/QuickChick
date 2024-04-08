(lang dune 3.12)
(using coq 0.7)
(using menhir 2.0)
(name coq-quickchick)
(version dev)

(generate_opam_files true)

(source (github QuickChick/QuickChick))
(license MIT)
(authors
  "Leonidas Lampropoulos"
  "Zoe Paraskevopoulou"
  "Maxime Denes"
  "Catalin Hritcu"
  "Benjamin Pierce"
  "Li-yao Xia"
  "Arthur Azevedo de Amorim"
  "Yishuai Li"
  "Antal Spector-Zabusky")
(maintainers "leonidas@umd.edu")

(package
 (name coq-quickchick)
 (synopsis "Randomized Property-Based Testing for Coq")
 (description
  "A library for property-based testing in Coq.

  - Combinators for testable properties and random generators.
  - QuickChick plugin for running tests in a Coq session.
  - Includes a mutation testing tool.")
 (depends
  (ocaml (>= 4.07))
  (menhir :build)
  (cppo (and :build (>= 1.6.8)))
  (coq (>= 8.15~))
  coq-ext-lib
  coq-mathcomp-ssreflect
  (coq-simple-io (>= 1.6.0))
  ocamlfind
  ocamlbuild)
)
