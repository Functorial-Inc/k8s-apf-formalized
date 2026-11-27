#!/usr/bin/env bash
# Runs tracecheck over traces/**/*.jsonl with the expected verdict per directory:
#   traces/corrected/*            must conform
#   traces/handmade/ok*           must conform
#   traces/handmade/* (others)    must be rejected
#   traces/mutated/*              must be rejected
#   traces/affected/*             per file: must be rejected exactly when the
#                                 seed is in go/RESULTS.md's bug-hitting list
#                                 (the four pr-* scenarios all hit the bug)
# The script reports any other directory under traces/ without an expectation.
set -u
cd "$(dirname "$0")/.."
TC=.lake/build/bin/tracecheck
OUT=${OUT:-counterexamples/tracecheck-all.txt}
fail=0
: > "$OUT"

verdicts() { # dir -> lines "OK|FAIL path ..."
  "$TC" "$@" | grep -v '^summary:'
}

expect_all() { # label expected(OK|FAIL) files...
  local label=$1 want=$2; shift 2
  [ $# -eq 0 ] && { echo "$label: no files"; return; }
  local res; res=$(verdicts "$@")
  echo "$res" >> "$OUT"
  local n; n=$(echo "$res" | wc -l | tr -d ' ')
  local good; good=$(echo "$res" | grep -c "^$want ")
  if [ "$good" -eq "$n" ]; then
    echo "$label: $good/$n $want as expected"
  else
    echo "$label: MISMATCH, $good/$n $want; unexpected:"
    echo "$res" | grep -v "^$want " | cut -c1-200
    fail=1
  fi
}

shopt -s nullglob
expect_all "traces/corrected" OK traces/corrected/*.jsonl
expect_all "traces/handmade (ok*)" OK traces/handmade/ok*.jsonl
other=(); for f in traces/handmade/*.jsonl; do case $(basename "$f") in ok*) ;; *) other+=("$f");; esac; done
expect_all "traces/handmade (others)" FAIL "${other[@]}"
expect_all "traces/mutated" FAIL traces/mutated/*.jsonl

# affected: compare with the bug-hitting seed list
aff=(traces/affected/*.jsonl)
if [ ${#aff[@]} -gt 0 ]; then
  res=$(verdicts "${aff[@]}"); echo "$res" >> "$OUT"
  hit=$(grep -A1 'Seeds that hit the bug on affected code:' go/RESULTS.md | tail -1 | tr -d '`')
  agree=0; disagree=0
  while read -r verdict path rest; do
    path=${path%:}; base=$(basename "$path" .jsonl)
    case $base in
      seed-*) n=$((10#${base#seed-})); want=OK
              for h in $hit; do [ "$h" -eq "$n" ] && want=FAIL; done ;;
      pr-*)   want=FAIL ;;
      *)      want=? ;;
    esac
    if [ "$verdict" = "$want" ]; then agree=$((agree+1)); else disagree=$((disagree+1)); echo "  disagree: $base want $want got $verdict"; fi
  done <<< "$res"
  nfail=$(echo "$res" | grep -c '^FAIL '); nok=$(echo "$res" | grep -c '^OK ')
  echo "traces/affected: $nok conform, $nfail rejected; agreement with go/RESULTS.md bug list: $agree agree, $disagree disagree"
  [ "$disagree" -eq 0 ] || fail=1
fi

for d in traces/*/; do
  case $d in traces/corrected/|traces/handmade/|traces/mutated/|traces/affected/) ;;
    *) fs=("$d"*.jsonl); [ ${#fs[@]} -gt 0 ] && { echo "$d (no expectation):"; verdicts "${fs[@]}" | cut -c1-200; };;
  esac
done
exit $fail
