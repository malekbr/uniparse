(lang dune 3.18)

(using cinaps 1.3)

(name uniparse)

(generate_opam_files true)

(source
 (github malekbr/uniparse))

(authors "Author Name <author@example.com>")

(maintainers "Maintainer Name <maintainer@example.com>")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name uniparse)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends ocaml core uucp)
 (tags
  ("add topics" "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
