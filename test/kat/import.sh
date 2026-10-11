#!/bin/sh
# Copy the known-answer subset in test/kat out of the full corpora. Release
# archives leave the corpora out (see .gitattributes), so the package tests
# run against this subset. Records are copied verbatim; README.md lists them.
set -eu

cd "$(dirname "$0")/../.."
export LC_ALL=C

# Copy the given blank-line-separated records (1-based) of a vector file.
records() {
  source=$1
  target=$2
  shift 2
  awk -v want=" $* " '
    BEGIN { RS = "" }
    index(want, " " NR " ") { if (copied++) print ""; print }
  ' "$source" > "$target"
}

# Copy the given lines (1-based) of a line-oriented vector file.
lines() {
  source=$1
  target=$2
  shift 2
  sed -n "$(printf '%sp;' "$@")" "$source" > "$target"
}

kat=test/kat
mkdir -p "$kat/mlkem" "$kat/mldsa" "$kat/slhdsa"

cp test/vectors/LICENSE "$kat/mlkem/LICENSE"
cp test/wycheproof/LICENSE "$kat/mlkem/LICENSE.wycheproof"
records test/vectors/mlkem512-seed-decap.txt "$kat/mlkem/mlkem512-seed-decap.txt" 1
records test/vectors/mlkem512-encap.txt "$kat/mlkem/mlkem512-encap.txt" 9
records test/vectors/mlkem512-decap.txt "$kat/mlkem/mlkem512-decap.txt" 1
for parameter in 768 1024; do
  records "test/vectors/mlkem$parameter-keygen.txt" \
    "$kat/mlkem/mlkem$parameter-keygen.txt" 1
  records "test/vectors/mlkem$parameter-encap.txt" \
    "$kat/mlkem/mlkem$parameter-encap.txt" 1
  records "test/vectors/mlkem$parameter-decap.txt" \
    "$kat/mlkem/mlkem$parameter-decap.txt" 1 254
done

cp test/mldsa_vectors/LICENSE "$kat/mldsa/LICENSE"
for parameter in 44 65 87; do
  records "test/mldsa_vectors/mldsa_nist_keygen_${parameter}_tests.txt" \
    "$kat/mldsa/mldsa_nist_keygen_${parameter}_tests.txt" 1 2
done
records test/mldsa_vectors/mldsa_nist_siggen_44_tests.txt \
  "$kat/mldsa/mldsa_nist_siggen_44_tests.txt" 1 4
records test/mldsa_vectors/mldsa_nist_siggen_65_tests.txt \
  "$kat/mldsa/mldsa_nist_siggen_65_tests.txt" 1 4
records test/mldsa_vectors/mldsa_nist_siggen_87_tests.txt \
  "$kat/mldsa/mldsa_nist_siggen_87_tests.txt" 6
records test/mldsa_vectors/mldsa_eta_restart_keygen_65_tests.txt \
  "$kat/mldsa/mldsa_eta_restart_keygen_65_tests.txt" 1 2

cp test/slhdsa_vectors/LICENSE "$kat/slhdsa/LICENSE"
cp test/slhdsa_vectors/keygen.txt "$kat/slhdsa/keygen.txt"
lines test/slhdsa_vectors/siggen.txt "$kat/slhdsa/siggen.txt" 1 3 4
lines test/slhdsa_vectors/sigver.txt "$kat/slhdsa/sigver.txt" 98 133

if command -v sha256sum > /dev/null; then
  checksum="sha256sum"
else
  checksum="shasum -a 256"
fi
(cd "$kat" && $checksum mlkem/*.txt mldsa/*.txt slhdsa/*.txt) > "$kat/SHA256SUMS"
