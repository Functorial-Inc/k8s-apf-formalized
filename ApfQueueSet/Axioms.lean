import ApfQueueSet.Corrected
import ApfQueueSet.Mirror
import ApfQueueSet.Synth

/-! `#print axioms` for every final theorem. `make axioms` saves the output to
`proof-status.md`'s appendix source, `axioms.txt`. -/

-- Plain-Lean mirror (kernel-checked, no SMT)
#print axioms ApfQueueSet.Mirror.corrected_safe
#print axioms ApfQueueSet.Mirror.release_once_step
#print axioms ApfQueueSet.Mirror.conservation_reachable
#print axioms ApfQueueSet.Mirror.conservation_fo_reachable
#print axioms ApfQueueSet.Mirror.issue_144077_affected
#print axioms ApfQueueSet.Mirror.issue_144077_corrected
#print axioms ApfQueueSet.Mirror.issue_144077_panics
-- naive versus strict reading of "empty"
#print axioms ApfQueueSet.Mirror.naive_imp_discarded
#print axioms ApfQueueSet.Mirror.clean_until_strict_discard
#print axioms ApfQueueSet.Mirror.corrected_naive_safe
#print axioms ApfQueueSet.Mirror.issue_144077_first_bad_step_is_naive_ok
#print axioms ApfQueueSet.Mirror.wrong_queue_premature_removal
#print axioms ApfQueueSet.Mirror.wrong_queue_naive_violated

-- Lemmas behind the hand-written Veil proofs
#print axioms ApfQueueSet.onto_remove
#print axioms ApfQueueSet.onto_grow

-- Hand-written Veil VC proofs. `prove_veil_invariant_goal` registers each one
-- with `@[veil]`, and `#check_invariants` uses them for these three VCs.
#print axioms ApfCorrected.timerFire_index_integrity_onto
#print axioms ApfCorrected.finish_index_integrity_onto
#print axioms ApfCorrected.reconfigure_index_integrity_onto

-- From the specification of "empty" to the Go guard (Synth.lean)
#print axioms ApfQueueSet.Synth.eval_derive_strict
#print axioms ApfQueueSet.Synth.eval_derive_naive
#print axioms ApfQueueSet.Synth.derived_strict_iff_spec
#print axioms ApfQueueSet.Synth.naive_guard_unsound
#print axioms ApfQueueSet.Synth.strict_guard_holds_back
