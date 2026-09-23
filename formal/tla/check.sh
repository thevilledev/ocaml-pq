#!/bin/sh
# Parse every TLA+ module in this directory with SANY and model-check every
# configuration with TLC.  Exits non-zero if any parse or check fails.
#
#   TLA2TOOLS  path to tla2tools.jar (default: tla2tools.jar next to this script)
#   JAVA       java executable (default: java from PATH)
#   TLC_WORKERS  TLC worker threads (default: auto)
#
# Usage: ./check.sh [Model ...]     (default: all models)
#
# A configuration Foo.cfg checks Foo.tla; Foo__variant.cfg would also check
# Foo.tla.  TLC metadata goes to a temporary directory that is removed on
# exit, and no trace-exploration specs are written.
set -u

DIR=$(cd "$(dirname "$0")" && pwd)
JAR=${TLA2TOOLS:-$DIR/tla2tools.jar}
JAVA=${JAVA:-java}
WORKERS=${TLC_WORKERS:-auto}

if [ ! -f "$JAR" ]; then
  echo "check.sh: tla2tools.jar not found at $JAR (set TLA2TOOLS)" >&2
  exit 2
fi
if ! command -v "$JAVA" >/dev/null 2>&1; then
  echo "check.sh: java not found (set JAVA)" >&2
  exit 2
fi

WORK=$(mktemp -d "${TMPDIR:-/tmp}/tla-check.XXXXXX") || exit 2
trap 'rm -rf "$WORK"' EXIT INT TERM

status=0

SELECTION="$*"
selected() {
  [ -z "$SELECTION" ] && return 0
  for want in $SELECTION; do
    [ "$want" = "$1" ] && return 0
  done
  return 1
}

# 1. SANY on every module (including helper modules without a cfg).
for tla in "$DIR"/*.tla; do
  name=$(basename "$tla" .tla)
  case $name in *_TTrace_*) continue ;; esac
  if [ -f "$DIR/$name.cfg" ]; then selected "$name" || continue; fi
  out=$(cd "$DIR" && "$JAVA" -cp "$JAR" tla2sany.SANY "$name.tla" 2>&1)
  rc=$?
  # SANY exits 0 on semantic errors, so also inspect its output.
  if [ $rc -ne 0 ] || printf '%s\n' "$out" |
       grep -q -E 'Semantic errors|\*\*\* Errors|Parse Error|Could not parse|Fatal errors'; then
    echo "SANY  FAIL  $name"
    printf '%s\n' "$out" | tail -25
    status=1
  else
    echo "SANY  ok    $name"
  fi
done

# 2. TLC on every configuration.
for cfg in "$DIR"/*.cfg; do
  name=$(basename "$cfg" .cfg)
  spec=${name%%__*}
  selected "$spec" || continue
  start=$(date +%s)
  out=$(cd "$DIR" && "$JAVA" -XX:+UseParallelGC -cp "$JAR" tlc2.TLC \
          -workers "$WORKERS" -noGenerateSpecTE -cleanup \
          -metadir "$WORK/$name" -config "$name.cfg" "$spec.tla" 2>&1)
  rc=$?
  secs=$(( $(date +%s) - start ))
  states=$(printf '%s\n' "$out" | sed -n 's/.* \([0-9][0-9 ,]*\) distinct states found.*/\1/p' | tail -1 | tr -d ' ,')
  if [ $rc -eq 0 ] && printf '%s\n' "$out" | grep -q 'Model checking completed. No error has been found.'; then
    echo "TLC   ok    $name  (${states:-?} distinct states, ${secs}s)"
  else
    echo "TLC   FAIL  $name  (exit $rc, ${secs}s)"
    printf '%s\n' "$out" | grep -v '^Progress' | tail -60
    status=1
  fi
done

exit $status
