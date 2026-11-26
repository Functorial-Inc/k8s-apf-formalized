module

/-! Plain Lean lemmas used by the hand-written proofs in `Corrected.lean`.

They state, over arbitrary functions, the two facts behind
`index_integrity_onto` ("every slice position below `len` is taken"):

* `onto_remove`: removing the queue at position `k` and decrementing every
  larger index keeps positions `0 .. len-2` taken.
* `onto_grow`: appending fresh queues numbered `created ..` at positions
  `len .. n-1` keeps positions `0 .. n-1` taken.

The statements are shaped exactly like the goals Veil's `unveil` produces, so
the proofs in `Corrected.lean` just apply them. -/

public section

namespace ApfQueueSet

-- The `if` condition `C` and its `Decidable` instance are implicit, so that the
-- lemma applies whatever form Veil's simplifier left the condition in; the
-- caller proves that `C q` means `k < idx q` for the surviving queues.
theorem onto_remove {Q : Type} (inS : Q → Bool) (idx : Q → Nat) (len k : Nat) (v : Q)
    {C : Q → Prop} {d : ∀ q, Decidable (C q)}
    (honto : ∀ i, i < len → ∃ q, inS q = true ∧ idx q = i) (hv : idx v = k)
    (hC : ∀ q, ¬ v = q → inS q = true → (C q ↔ k < idx q)) :
    ∀ i, i < len - 1 → ∃ q, (¬ v = q ∧ inS q = true) ∧
      (@ite Nat (C q) (d q) (idx q - 1) (idx q)) = i := by
  intro i hi
  by_cases hik : i < k
  · obtain ⟨q, hq, hqi⟩ := honto i (by omega)
    have hvq : ¬ v = q := by intro h; subst h; omega
    refine ⟨q, ⟨hvq, hq⟩, ?_⟩
    have := hC q hvq hq
    split
    · rename_i h; have := this.mp h; omega
    · omega
  · obtain ⟨q, hq, hqi⟩ := honto (i + 1) (by omega)
    have hvq : ¬ v = q := by intro h; subst h; omega
    refine ⟨q, ⟨hvq, hq⟩, ?_⟩
    have := hC q hvq hq
    split
    · omega
    · rename_i h; exact absurd (this.mpr (by omega)) h

theorem onto_grow {Q : Type} (inS : Q → Bool) (idx qnum : Q → Nat)
    (len created n maxIds : Nat)
    {d : ∀ q, Decidable (created ≤ qnum q ∧ qnum q < created + (n - len))}
    (honto : ∀ i, i < len → ∃ q, inS q = true ∧ idx q = i)
    (hcr : ∀ q, inS q = true → qnum q < created)
    (hqonto : ∀ i, i < maxIds → ∃ q, qnum q = i)
    (hcap : created + (n - len) ≤ maxIds) :
    ∀ i, i < n → ∃ q,
      (inS q = true ∨ created ≤ qnum q ∧ qnum q < created + (n - len)) ∧
      (@ite Nat (created ≤ qnum q ∧ qnum q < created + (n - len)) (d q)
        (len + (qnum q - created)) (idx q)) = i := by
  intro i hi
  by_cases hil : i < len
  · obtain ⟨q, hq, hqi⟩ := honto i hil
    have hc := hcr q hq
    refine ⟨q, .inl hq, ?_⟩
    split
    · omega
    · exact hqi
  · obtain ⟨q, hq⟩ := hqonto (created + (i - len)) (by omega)
    refine ⟨q, .inr (by omega), ?_⟩
    split
    · omega
    · omega

end ApfQueueSet

end
