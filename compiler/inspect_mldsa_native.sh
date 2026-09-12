#!/bin/sh
set -eu

archive=${1:-_build/default/mldsa/mldsa.a}

if [ ! -f "$archive" ]; then
  echo "native archive not found: $archive" >&2
  exit 2
fi

if command -v llvm-objdump >/dev/null 2>&1; then
  disassembly=$(llvm-objdump --disassemble --reloc --no-show-raw-insn "$archive")
elif command -v objdump >/dev/null 2>&1; then
  disassembly=$(objdump --disassemble --reloc "$archive")
else
  echo "llvm-objdump or objdump is required" >&2
  exit 2
fi

extract_symbol () {
  symbol=$1
  printf '%s\n' "$disassembly" | awk -v symbol="$symbol" '
    $0 ~ ("<[^>]*" symbol "_[0-9]+>:") {
      found = 1
      active = 1
      print
      next
    }
    active && $0 ~ /^[[:xdigit:]]+[[:space:]]+<[^>]+>:/ { active = 0 }
    active { print }
    END { if (!found) exit 2 }
  '
}

attempt_body=$(extract_symbol attempt)
check_calls=$(printf '%s\n' "$attempt_body" |
  awk '/vector_norm_violation_flag_[0-9]+/ { count++ } END { print count + 0 }')
first_check_line=$(printf '%s\n' "$attempt_body" |
  awk '/vector_norm_violation_flag_[0-9]+/ && !found { print NR; found = 1 }')
last_check_line=$(printf '%s\n' "$attempt_body" |
  awk '/vector_norm_violation_flag_[0-9]+/ { line = NR } END { print line + 0 }')

if [ "$check_calls" -ne 3 ]; then
  echo "ML-DSA signing attempt calls $check_calls vector norm checks; expected 3" >&2
  printf '%s\n' "$attempt_body" >&2
  exit 1
fi

# Retry is a backward unconditional branch into the small prologue of
# [attempt]. No such edge may appear between the first and third norm check;
# after the third check one must remain. This survives signature-encoder
# inlining differences between OCaml 4.13 and 5.4.
between_checks=$(printf '%s\n' "$attempt_body" |
  sed -n "${first_check_line},${last_check_line}p")
after_checks=$(printf '%s\n' "$attempt_body" |
  sed -n "${last_check_line},\$p")
retry_pattern='[[:space:]](b|jmp)[[:space:]].*<[^>]*attempt_[0-9]+\+0x([0-9a-f]|[123][0-9a-f])>'

if printf '%s\n' "$between_checks" | grep -E "$retry_pattern" >/dev/null; then
  echo "ML-DSA signing can retry before all three rejection checks" >&2
  printf '%s\n' "$attempt_body" >&2
  exit 1
fi

if ! printf '%s\n' "$after_checks" | grep -E "$retry_pattern" >/dev/null; then
  echo "ML-DSA signing retry back-edge was not found after the rejection checks" >&2
  printf '%s\n' "$attempt_body" >&2
  exit 1
fi

echo "ML-DSA native-code inspection passed ($(uname -m)):"
echo "  signing attempt retains 3 complete vector norm checks before retry"
echo "  variable attempt-count rejection remains part of the documented boundary"
