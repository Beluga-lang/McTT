(lang dune 3.13)
(using menhir 2.1)
(name mctt)

(generate_opam_files)

(license MIT)
(authors "Antoine Gaulin"
         "Jason Hu"
         "Junyoung Jang")
(maintainers "the CompLogic group, McGill University")
(homepage "https://beluga-lang.github.io/McTT/")
(documentation "https://beluga-lang.github.io/McTT/")
(source (github Beluga-lang/McTT))

(package
 (name mctt)
 (synopsis "A Correct-By-Construction Proof Checkers For Type Theories")
 (description "McTT is a verified, runnable typechecker for Martin-Löf type 
theory. This project provides an executable, to which we can feed a program 
in Martin-Löf type theory to check whether this program has the specified type. 
McTT is novel in that it is implemented and verified in Coq. More specifically, 
we proved that the typechecking algorithm extracted from Coq is sound and 
complete: a program passes typechecker if and only if it is a well-typed 
program in MLTT. This is the first verified proof assistant (despite being 
elementary) and serves as a basis for future extensions.")
 (depends
  (ocaml (>= "4.14.2"))
  (rocq-prover (= "9.0.0"))
  (rocq-equations (= "1.3.1+9.0"))
  (menhir (= "20250903"))
  (coq-menhirlib (= "20250903"))
  (ppx_inline_test (>= "0.16.1"))
  (ppx_expect (>= "0.16.1"))
  (sherlodoc :with-doc)))
