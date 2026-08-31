(lang dune 3.11)

(name zutils)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Author Name")

(maintainers "Maintainer Name")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name zutils)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends
  ocaml
  dune
  core
  z3
  yojson
  ppxlib
  ppx_assert
  ppx_deriving
  ppx_deriving_yojson
  ppx_here
  ppx_optcomp
  ppx_compare
  ppx_inline_test
  ppx_sexp_conv
  (spectrum (>= 0.6.0)))
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
