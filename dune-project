(lang dune 2.7)
; (for dune version 2.7.1)
(using coq 0.2)
; (for coq version 8.12.0)
(name maniunfold)
(version 0.0.0)
; (implicit_transitive_deps <bool>)
; (wrapped_executables <bool>)
; (explicit_js_mode)
; (dialect
;   (name <name>)
;   (implementation
;     (extension <string>)
;     <optional fields>)
;   (interface
;     (extension <string>)
;     <optional fields>))
(formatting disabled)
(generate_opam_files true)

(license GPL-3.0-or-later)
(authors "Sampsa Kiiskinen")
(maintainers "Sampsa Kiiskinen")
(source (github Tuplanolla/maniunfold))
; (bug-reports <url>)
(homepage http://users.jyu.fi/~sapekiis/maniunfold/)
; (documentation <url>)

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
  (depends
    (coq-stdpp (>= 1.4.0))
    (logs (>= 0.7.0))
    (num (>= 1.3))
    (thrift (>= 0.10.0)))
  ; (conflicts <dep-specification)
  ; (depopts <dep-specification)
  ; (tags <tags>)
  ; (deprecated_package_names <name list>)
  )
