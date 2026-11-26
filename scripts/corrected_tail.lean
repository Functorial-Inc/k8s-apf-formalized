-- ## Hand-written Lean proofs (kernel-checked)
-- SMT (cvc5) times out on `index_integrity_onto` (a ∀∃ formula over Nat) for
-- the three actions that change the slice. These proofs discharge those VCs;
-- `#check_invariants` then uses them instead of SMT.

prove_veil_invariant_goal timerFire index_integrity_onto using wp by
  obtain ⟨_, _, _, _, _, honto, _⟩ := hinv
  intro _ _
  split
  · split
    · exact honto
    · intro v _ hvi
      exact ApfQueueSet.onto_remove _ _ _ _ v honto hvi (by intro q h1 h2; simp [h1, h2])
  · exact honto

prove_veil_invariant_goal finish index_integrity_onto using wp by
  obtain ⟨_, _, _, _, _, honto, _⟩ := hinv
  intro _
  split
  · exact honto
  · intro _
    split
    · split
      · exact honto
      · intro v _ hvi
        exact ApfQueueSet.onto_remove _ _ _ _ v honto hvi (by intro q h1 h2; simp [h1, h2])
    · exact honto

prove_veil_invariant_goal reconfigure index_integrity_onto using wp by
  obtain ⟨_, _, _, _, _, honto, _, _, hcr, _⟩ := hinv
  obtain ⟨_, _, hqonto⟩ := has
  intro _
  split
  · intro hcap
    exact ApfQueueSet.onto_grow _ _ _ _ _ _ _ honto hcr hqonto hcap
  · exact honto

-- ## Unbounded verification: SMT for everything else
#check_invariants

-- Model checking of this model is in CorrectedMC.lean, which has no `assume`.

end ApfCorrected
