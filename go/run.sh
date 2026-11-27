#!/usr/bin/env bash
# Usage: go/run.sh affected|corrected|upstream-tests|pr-test [SEEDS]
#   affected         apply 0002 only, run the harness, write traces/affected/*.jsonl
#   corrected        apply the fix (0001, or 0003 with APF_FIX=0003) + 0002, run the harness, write traces/corrected/*.jsonl
#   pr-test          the PR's own regression test, unmodified, on unpatched, 0002 and 0001+0002 trees
#   upstream-tests   apply 0002 (and then 0001+0002), run upstream's own flowcontrol tests
# SEEDS is the number of random seeds (default 300). The script is idempotent: it
# restores the upstream tree on exit and first deletes old output for the chosen mode.
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(dirname "$HERE")"
MODE="${1:?usage: run.sh affected|corrected|upstream-tests|pr-test [SEEDS]}"
SEEDS="${2:-300}"
UP="$HERE/upstream"
MOD="$UP/staging/src/k8s.io/apiserver"
PKG=./pkg/util/flowcontrol/fairqueuing/queueset
PKGDIR="$MOD/pkg/util/flowcontrol/fairqueuing/queueset"
# APF_FIX=0003 uses the fix that go/gen-fix.sh generates from the Lean spec in place of PR #144078's (0001).
FIX="${APF_FIX:-0001}"
LOGS="$HERE/logs/$MODE"
[ "$FIX" = 0001 ] || LOGS="$HERE/logs/$MODE-fix$FIX"

"$HERE/fetch.sh" >/dev/null
restore() { git -C "$UP" reset -q; git -C "$UP" checkout -q .; git -C "$UP" clean -fdq; }
restore
trap restore EXIT

apply() { for p in "$@"; do git -C "$UP" apply "$HERE/patches/$p" || { echo "patch $p failed"; exit 1; }; done; }

rm -rf "$LOGS"; mkdir -p "$LOGS"

if [ "$MODE" = upstream-tests ]; then
  for variant in "0002" "$FIX 0002"; do
    restore
    for n in $variant; do apply "$(cd "$HERE/patches" && ls | grep "^$n-")"; done
    echo "== upstream tests with patches: $variant"
    ( cd "$MOD" && go test -count=1 ./pkg/util/flowcontrol/... ) 2>&1 | tee "$LOGS/upstream-tests-${variant// /+}.log"
    echo "exit code: ${PIPESTATUS[0]}"
  done
  exit 0
fi

if [ "$MODE" = pr-test ]; then
  # Run the PR author's own regression test, unmodified, on three trees.
  for variant in "none" "0002" "$FIX 0002"; do
    restore
    [ "$variant" = none ] || for n in $variant; do apply "$(cd "$HERE/patches" && ls | grep "^$n-")"; done
    git -C "$UP" apply "$HERE/harness/pr144078-test.patch" || exit 1
    echo "== PR test with patches: $variant"
    ( cd "$MOD" && go test -count=1 -v -run '^TestRemoveQueueOnlyWhenNoSeatsInUse$' "$PKG" ) 2>&1 | tee "$LOGS/pr-test-${variant// /+}.log"
    echo "exit code: ${PIPESTATUS[0]}"
  done
  exit 0
fi

case "$MODE" in
  affected)  apply 0002-instrumentation.patch ;;
  corrected) apply "$(cd "$HERE/patches" && ls | grep "^$FIX-")" 0002-instrumentation.patch ;;
  *) echo "unknown mode $MODE"; exit 2 ;;
esac

OUT="$ROOT/traces/$MODE"
rm -rf "$OUT"; mkdir -p "$OUT"
cp "$HERE"/harness/apf_trace_test.go "$PKGDIR/"
BIN="$HERE/logs/queueset-$MODE.test"
( cd "$MOD" && go test -c -o "$BIN" "$PKG" ) || exit 1

export APF_TRACE_DIR="$OUT"
: > "$LOGS/exit-codes.tsv"
runone() { # name, env assignment
  local name="$1"; shift
  env "$@" "$BIN" -test.v -test.count=1 -test.run 'TestAPFScenario|TestAPFRandom' > "$LOGS/$name.log" 2>&1
  printf '%s\t%s\n' "$name" "$?" >> "$LOGS/exit-codes.tsv"
}
runone pr-panic APF_SCENARIO=pr-panic
for sc in pr-wrongqueue-executing pr-wrongqueue-waiting-crash pr-wrongqueue-waiting-lost; do runone "$sc" APF_SCENARIO="$sc"; done
for ((s = 1; s <= SEEDS; s++)); do
  runone "$(printf 'seed-%04d' "$s")" APF_SEED="$s"
done
grep -h '^SUMMARY' "$LOGS"/*.log | sed 's/^SUMMARY //' > "$LOGS/summary.txt"
echo "traces: $(ls "$OUT" | wc -l) in $OUT; summary: $LOGS/summary.txt"
