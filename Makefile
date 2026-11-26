# Lean/Veil side of k8s-apf-formalized. See proof-status.md.
.PHONY: verify build check-parallel axioms counterexamples check-traces tracecheck

# lake build elaborates every module, which runs:
#   Affected.lean    : the model only (source of the three generated files)
#   AffectedMC.lean  : #model_check, finds the safe_retirement counterexample
#                      (reported as info, not an error)
#   Corrected.lean   : #check_invariants (SMT with proof reconstruction + 3
#                      hand proofs), with the trusted `assume` in `release`
#   CorrectedMC.lean : three exhaustive #model_check runs, no `assume`
#   Mirror.lean      : the kernel-checked proofs
# A failed VC, or a violation in CorrectedMC.lean, is a build error.
verify: check-parallel build axioms

build:
	lake build

# Corrected.lean is generated from Affected.lean; they must differ only in the guard.
check-parallel:
	uv run scripts/gen_corrected.py --check

axioms: build
	lake build ApfQueueSet.Axioms 2>&1 | grep 'depends on axioms' | sed 's/^info: [^ ]* //' > axioms.txt
	@cat axioms.txt
	@! grep -q sorryAx axioms.txt

counterexamples: build
	lake env lean --run scripts/IssueReplay.lean > counterexamples/issue-144077-mirror-replay.txt
	{ echo "# Veil #model_check on ApfQueueSet/AffectedMC.lean (no assume; interpreted, breadth-first, so a shortest trace)"; \
	  echo "# Instantiation: { queue := Fin 2, req := Fin 2, num := Fin 3, val := Fin.val, qnum := Fin.val, maxIds := 2 }"; \
	  echo "# 'choices:' lines show the values picked by 'let x :| ...' (n, q0 in init; v in removeAt)."; echo; \
	  lake build ApfQueueSet.AffectedMC 2>&1 | sed -n '/Violation/,/^[^ ]/p' | grep -v '^[✔ℹ⚠]\|Build completed\|^info: .*LocalRProp' | sed 's/^info: [^ ]* //'; \
	} > counterexamples/affected-safe_retirement.veil-mc.txt

tracecheck:
	lake build tracecheck

check-traces: tracecheck
	scripts/check_traces.sh
