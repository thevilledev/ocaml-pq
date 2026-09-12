#!/bin/sh
set -eu

archive=${1:-_build/default/lib/mlkem.a}

if [ ! -f "$archive" ]; then
  echo "native archive not found: $archive" >&2
  exit 2
fi

if command -v llvm-objdump >/dev/null 2>&1; then
  disassembly=$(llvm-objdump --disassemble --no-show-raw-insn "$archive")
elif command -v objdump >/dev/null 2>&1; then
  disassembly=$(objdump --disassemble "$archive")
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

conditional_branch_count () {
  architecture=$1
  case "$architecture" in
    arm64|aarch64)
      awk '
        $0 ~ /[[:space:]](b\.[[:alpha:]]+|cbz|cbnz|tbz|tbnz)[[:space:]]/ {
          count++
        }
        END { print count + 0 }
      '
      ;;
    x86_64|amd64)
      awk '
        $0 ~ /[[:space:]]j[[:alpha:]]+[[:space:]]/ &&
        $0 !~ /[[:space:]]jmp[[:space:]]/ { count++ }
        END { print count + 0 }
      '
      ;;
    *)
      echo "unsupported architecture for reviewed branch baseline: $architecture" >&2
      exit 2
      ;;
  esac
}

architecture=$(uname -m)
ct_equal_body=$(extract_symbol ct_equal)
select_body=$(extract_symbol select_secret)
ct_equal_branches=$(printf '%s\n' "$ct_equal_body" |
  conditional_branch_count "$architecture")
select_branches=$(printf '%s\n' "$select_body" |
  conditional_branch_count "$architecture")

arithmetic_functions="field_reduce_once field_reduce field_add field_sub field_mul field_mul_sub field_add_mul decompress inc"
for function_name in $arithmetic_functions; do
  function_body=$(extract_symbol "$function_name")
  function_branches=$(printf '%s\n' "$function_body" |
    conditional_branch_count "$architecture")
  if [ "$function_branches" -ne 0 ]; then
    echo "$function_name has $function_branches conditional branches; expected 0" >&2
    printf '%s\n' "$function_body" >&2
    exit 1
  fi
done

# The reviewed control-flow shape has exactly three conditional branches in
# each routine: fixed loop entry/exit and the OCaml runtime poll. A generated
# branch on compared bytes or the secret-selection mask increases this count
# and requires a fresh native-code review.
if [ "$ct_equal_branches" -ne 3 ]; then
  echo "ct_equal has $ct_equal_branches conditional branches; expected 3" >&2
  printf '%s\n' "$ct_equal_body" >&2
  exit 1
fi

if [ "$select_branches" -ne 3 ]; then
  echo "select_secret has $select_branches conditional branches; expected 3" >&2
  printf '%s\n' "$select_body" >&2
  exit 1
fi

case "$architecture" in
  arm64|aarch64)
    printf '%s\n' "$select_body" | grep -E '[[:space:]]and[[:space:]]' >/dev/null
    printf '%s\n' "$select_body" | grep -E '[[:space:]]orr[[:space:]]' >/dev/null
    ;;
  x86_64|amd64)
    printf '%s\n' "$select_body" | grep -E '[[:space:]]and[a-z]*[[:space:]]' >/dev/null
    printf '%s\n' "$select_body" | grep -E '[[:space:]]or[a-z]*[[:space:]]' >/dev/null
    ;;
esac

echo "ML-KEM native-code inspection passed ($architecture):"
echo "  field arithmetic: 9 scalar routines have no conditional branches"
echo "  ct_equal: $ct_equal_branches fixed-control branches"
echo "  select_secret: $select_branches fixed-control branches, arithmetic mask present"
