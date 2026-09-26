(lang dune 3.0)
(name ocaml-pq)
(version 0.2.0)
(generate_opam_files true)
(source (github thevilledev/ocaml-pq))
(license ISC)
(authors "Ville Vesilehto <ville@vesilehto.fi>")
(maintainers "Ville Vesilehto <ville@vesilehto.fi>")
(package
 (name mlkem)
 (synopsis "Pure OCaml implementation of FIPS 203 ML-KEM")
 (description
  "Portable, typed implementations of ML-KEM-512, ML-KEM-768, and ML-KEM-1024 with no C stubs or runtime package dependencies."))
(package
 (name mldsa)
 (synopsis "Pure OCaml implementation of FIPS 204 ML-DSA")
 (description
  "Portable, typed implementations of ML-DSA-44, ML-DSA-65, and ML-DSA-87 with no C stubs or runtime package dependencies."))
(package
 (name slhdsa)
 (synopsis "Pure OCaml implementation of FIPS 205 SLH-DSA")
 (description
  "Portable, typed implementations of all twelve SHA2 and SHAKE SLH-DSA parameter sets with no C stubs or runtime package dependencies."))
