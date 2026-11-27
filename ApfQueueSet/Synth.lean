import ApfQueueSet.Mirror

/-! # From the specification of "empty" to the Go guard

`interface.go` says a queue is discarded only when it is "undesired and
empty". This file

1. states that sentence as a Lean predicate, parameterised by a *reading* of
   "empty": the list of request phases that make a queue non-empty;
2. derives a guard from a reading, as a list of observations the Go `queue`
   struct can actually make (`derive`);
3. proves that the guard derived from the strict reading is exactly the guard
   of the corrected model (`eval_derive_strict`), so `Mirror.corrected_safe`
   is a theorem about it, and that in every reachable state of that model it
   is true exactly when the queue is undesired and empty
   (`derived_strict_iff_spec`);
4. proves that the guard derived from the naive reading is the affected guard
   (`eval_derive_naive`) and does not imply the strict specification
   (`naive_guard_unsound`);
5. prints a guard as Go (`goFunction`). `GoFixMain.lean` wraps that in an
   executable, and `go/gen-fix.sh` splices its output into `queueset.go`.

What is trusted here, and not proved: the table `Obs.go` (that each Go
expression reads the quantity `Obs.eval` says it reads), the Go text around
the condition in `goFunction` (copied from upstream), and everything already
listed as trusted for the mirror. See `docs/spec-to-go.md`. -/

set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ApfQueueSet.Synth
open ApfQueueSet.Mirror

/-- A reading of "empty": the phases of a request that make its queue
non-empty. -/
abbrev Reading := List Phase

/-- The reading the affected code implements: waiting or executing. -/
def naiveReading : Reading := [.waiting, .executing]

/-- Our reading of the contract: waiting, executing, or lingering. -/
def strictReading : Reading := [.waiting, .executing, .lingering]

section Spec
variable {Q R : Type} [DecidableEq Q] [DecidableEq R]

/-- **The specification of "empty".** No request assigned to `q` is in one of
the phases of the reading. -/
def EmptyOf (ps : Reading) (rs : List R) (s : St Q R) (q : Q) : Prop :=
  ∀ r ∈ rs, s.rq r = q → s.phase r ∉ ps

/-- "undesired": there are more queues than the configuration asks for. -/
def Undesired (s : St Q R) : Prop := s.desired < s.slice.length

/-- "undesired and empty", `interface.go` lines 66 to 67. -/
def MayDiscard (ps : Reading) (rs : List R) (s : St Q R) (q : Q) : Prop :=
  Undesired s ∧ EmptyOf ps rs s q

/-- The strict reading says: no live request. -/
theorem emptyOf_strict_iff (rs : List R) (s : St Q R) (q : Q) :
    EmptyOf strictReading rs s q ↔ ∀ r ∈ rs, s.rq r = q → (s.phase r).live = false := by
  constructor
  · intro h r hr hq
    have := h r hr hq
    cases hp : s.phase r <;> simp_all [strictReading]
  · intro h r hr hq
    have := h r hr hq
    cases hp : s.phase r <;> simp_all [strictReading]

end Spec

/-! ## Observations: what the Go code can test -/

/-- The tests available on `qs` and `r.queue`. There is no "lingering" set in
the Go `queue` struct; a lingering request is visible only through the seats
it still holds. -/
inductive Obs where
  | excess | noWaiting | noExecuting | noSeatsInUse
  deriving DecidableEq, Repr

/-- The Go expression for an observation. TRUSTED: this table is the link
between the model's fields and the Go fields. -/
def Obs.go : Obs → String
  | .excess => "len(qs.queues) > qs.qCfg.DesiredNumQueues"
  | .noWaiting => "r.queue.requestsWaiting.Length() == 0"
  | .noExecuting => "r.queue.requestsExecuting.Len() == 0"
  | .noSeatsInUse => "r.queue.seatsInUse == 0"

abbrev Guard := List Obs

/-- Which observation rules out a request in a given phase. `fresh` and
`released` requests are not in any queue, so nothing needs testing. -/
def detector : Phase → Option Obs
  | .waiting => some .noWaiting
  | .executing => some .noExecuting
  | .lingering => some .noSeatsInUse
  | .fresh | .released => none

/-- **The derivation.** "undesired" first, then one test per phase of the
reading. -/
def derive (ps : Reading) : Guard := .excess :: ps.filterMap detector

section Semantics
variable {Q R : Type} [DecidableEq Q] [DecidableEq R]

/-- What an observation means in the model. -/
def Obs.eval (rs : List R) (s : St Q R) (q : Q) : Obs → Bool
  | .excess => decide (s.desired < s.slice.length)
  | .noWaiting => rs.all (fun x => !(s.rq x == q && s.phase x == .waiting))
  | .noExecuting => rs.all (fun x => !(s.rq x == q && s.phase x == .executing))
  | .noSeatsInUse => s.seats q == 0

def Guard.eval (rs : List R) (s : St Q R) (q : Q) (g : Guard) : Bool :=
  g.all (Obs.eval rs s q)

/-- The guard derived from the strict reading IS the corrected model's guard. -/
theorem eval_derive_strict (rs : List R) (s : St Q R) (q : Q) :
    Guard.eval rs s q (derive strictReading) = removeGuard rs true s q := by
  simp [Guard.eval, derive, strictReading, detector, Obs.eval, removeGuard, Bool.and_assoc]

/-- The guard derived from the naive reading IS the affected model's guard. -/
theorem eval_derive_naive (rs : List R) (s : St Q R) (q : Q) :
    Guard.eval rs s q (derive naiveReading) = removeGuard rs false s q := by
  simp [Guard.eval, derive, naiveReading, detector, Obs.eval, removeGuard, Bool.and_assoc]

theorem sum_map_eq_zero {β : Type} (l : List β) (f : β → Int) (h : ∀ r ∈ l, f r = 0) :
    (l.map f).sum = 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h a (by simp), ih (fun r hr => h r (by simp [hr]))]; rfl

variable (rs : List R) (hall : ∀ r, r ∈ rs) (hnd : rs.Nodup)

include hall hnd in
/-- **Derived guard = specification.** In any state satisfying the invariant
of the corrected model, the guard derived from the strict reading is true
exactly when the queue is undesired and empty. Left to right is safety (the
guard never discards a non-empty queue). Right to left says the guard is not
stronger than the sentence asks for. -/
theorem derived_strict_iff_inv {s : St Q R} (hinv : Inv rs s) (q : Q) :
    Guard.eval rs s q (derive strictReading) = true ↔ MayDiscard strictReading rs s q := by
  rw [eval_derive_strict, MayDiscard, emptyOf_strict_iff]
  constructor
  · intro hg
    refine ⟨?_, fun r _ hq => guard_empty rs hall hnd hinv hg r hq⟩
    simp only [removeGuard, Bool.and_eq_true, decide_eq_true_eq] at hg
    exact hg.1.1.1
  · rintro ⟨hd, he⟩
    have hz : s.seats q = 0 := by
      rw [hinv.cons.1 q]
      unfold heldQ
      apply sum_map_eq_zero
      intro r hr
      by_cases hc : (s.phase r).holds = true ∧ s.rq r = q
      · have := he r hr hc.2
        have hh := hc.1
        cases hp : s.phase r <;> simp_all
      · rw [if_neg hc]
    simp only [removeGuard, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      Bool.not_eq_true', Bool.or_eq_true, beq_iff_eq, Bool.not_true, Bool.false_or]
    refine ⟨⟨⟨hd, fun x hx => ?_⟩, fun x hx => ?_⟩, hz⟩
    · by_cases hq : s.rq x = q
      · have := he x hx hq
        cases hp : s.phase x <;> simp_all
      · simp [hq]
    · by_cases hq : s.rq x = q
      · have := he x hx hq
        cases hp : s.phase x <;> simp_all
      · simp [hq]

include hall hnd in
/-- The same, for every reachable state of the corrected model. -/
theorem derived_strict_iff_spec {s : St Q R} (h : Reachable rs true s) (q : Q) :
    Guard.eval rs s q (derive strictReading) = true ↔ MayDiscard strictReading rs s q :=
  derived_strict_iff_inv rs hall hnd (inv_reachable rs hall hnd h) q

end Semantics

/-! ## The naive reading does not meet the strict specification -/

/-- The issue's execution after six actions, plus the seat release of the
seventh (`finish 1`), with that action's queue removal still pending: request
0 lingers in queue 2, request 1 has released its seat. -/
def beforeBadRemoval : St Nat Nat :=
  releaseSeats ((run [0, 1] false (issueActions.take 6) issueInit).getD issueInit) 1

/-- In the affected model, at the moment `removeQueueIfEmptyLocked` runs in
the issue's execution, the guard derived from the naive reading is true for
queue 2 and queue 2 is not empty. -/
theorem naive_guard_unsound :
    Guard.eval [0, 1] beforeBadRemoval 2 (derive naiveReading) = true ∧
    ¬ EmptyOf strictReading [0, 1] beforeBadRemoval 2 := by
  refine ⟨by decide, fun h => ?_⟩
  have := h 0 (by decide) (by decide)
  exact this (by decide)

/-- At the same moment the guard derived from the strict reading is false. -/
theorem strict_guard_holds_back :
    Guard.eval [0, 1] beforeBadRemoval 2 (derive strictReading) = false := by
  decide

/-! ## Printing Go -/

def Guard.go (g : Guard) : String := " &&\n\t\t".intercalate (g.map Obs.go)

/-- `removeQueueIfEmptyLocked` with the given guard. Everything except the
condition is the upstream text at the pinned commit, unchanged. -/
def goFunction (g : Guard) : String :=
  "func (qs *queueSet) removeQueueIfEmptyLocked(r *request) {\n" ++
  "\tif r.queue == nil {\n" ++
  "\t\treturn\n" ++
  "\t}\n" ++
  "\n" ++
  "\t// If there are more queues than desired and this one has no\n" ++
  "\t// requests then remove it\n" ++
  "\tif " ++ g.go ++ " {\n" ++
  "\t\tqs.queues = removeQueueAndUpdateIndexes(qs.queues, r.queue.index)\n" ++
  "\n" ++
  "\t\t// decrement here to maintain the invariant that (qs.robinIndex+1) % numQueues\n" ++
  "\t\t// is the index of the next queue after the one last dispatched from\n" ++
  "\t\tif qs.robinIndex >= r.queue.index {\n" ++
  "\t\t\tqs.robinIndex--\n" ++
  "\t\t}\n" ++
  "\t}\n" ++
  "}\n"

end ApfQueueSet.Synth
