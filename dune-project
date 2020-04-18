(lang dune 2.5)
(name maniunfold)
(version 0.0.0)

(generate_opam_files true)
(license GPL-3.0-or-later)
(authors "Sampsa Kiiskinen")
(maintainers "Sampsa Kiiskinen")
(source (github Tuplanolla/maniunfold))
; (bug-reports <url>)
(homepage http://users.jyu.fi/~sapekiis/maniunfold/)
; (documentation <url>)

(using coq 0.2) ; 8.11.1

(package
  (name maniunfold)
  (synopsis "Formalization of Discrete Exterior Calculus")
  (description "This is a repository for a research project that aims to
develop a type-theoretical model of discrete exterior calculus,
formalize the model with the Coq proof assistant,
extract OCaml code from the proof-relevant parts of the formalization,
link the extracted code with existing numerical solvers,
implement a user interface for the resulting system and
define a protocol for distributing and extending it further.")
  ; (depends <dep-specification>)
  ; (conflicts <dep-specification)
  ; (depopts <dep-specification)
  ; (tags <tags>)
  ; (deprecated_package_names <name list>)
  )
