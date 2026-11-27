/-! # Plain-Lean mirror of the APF `queueSet` model

This file restates the model of `Affected.lean` / `Corrected.lean` as ordinary
Lean definitions, with one Boolean `corrected` selecting the guard
`seatsInUse q = 0` of `removeQueueIfEmpty`, and proves the four properties of
`docs/model-contract.md` for the corrected model by induction over executions,
in Lean's kernel, with no SMT and no Mathlib.

**We checked the correspondence with the Veil models by inspection, not by proof.** The
differences in representation are:

* The slice `qs.queues` is a `List Q` (`slice`). Veil's `inSlice q` is
  `q ∈ slice` and Veil's `len` is `slice.length`. The stored `queue.index` is
  `idx`, which keeps its value for queues that left the slice, as in Veil.
* `reconfigure` takes the new queue identities as an explicit list `fresh` of
  never-used queues (any order). Veil allocates them by the numbering `qnum`;
  that is one instance of this.
* `removeAt i` removes `slice[i]`. Veil picks the in-slice `v` with
  `idx v = i`. The two agree whenever `index_integrity` holds, and the
  structural part of `index_integrity` (not `¬ panicked`) holds in every
  reachable state of BOTH models (the bug does not affect it).
* The universe of requests is a list `rs`. The theorems assume it lists every
  request exactly once (a finite request type). Quantifiers over requests in
  guards are `rs.all` / `rs.any`.
* `release` has no `assume`. Veil's `release` assumes `conservation_fo`;
  `conservation_fo_of_cons` below proves that it holds in every reachable
  state of either model, so the `assume` never cuts off an execution.
-/

set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ApfQueueSet.Mirror

inductive Phase where
  | fresh | waiting | executing | lingering | released
  deriving DecidableEq, Repr, Inhabited

def Phase.holds : Phase → Bool
  | .executing | .lingering => true
  | _ => false

def Phase.live : Phase → Bool
  | .waiting | .executing | .lingering => true
  | _ => false

@[simp] theorem Phase.holds_fresh : Phase.fresh.holds = false := rfl
@[simp] theorem Phase.holds_waiting : Phase.waiting.holds = false := rfl
@[simp] theorem Phase.holds_executing : Phase.executing.holds = true := rfl
@[simp] theorem Phase.holds_lingering : Phase.lingering.holds = true := rfl
@[simp] theorem Phase.holds_released : Phase.released.holds = false := rfl
@[simp] theorem Phase.live_fresh : Phase.fresh.live = false := rfl
@[simp] theorem Phase.live_waiting : Phase.waiting.live = true := rfl
@[simp] theorem Phase.live_executing : Phase.executing.live = true := rfl
@[simp] theorem Phase.live_lingering : Phase.lingering.live = true := rfl
@[simp] theorem Phase.live_released : Phase.released.live = false := rfl

structure St (Q R : Type) where
  slice : List Q
  idx : Q → Nat
  desired : Nat
  used : Q → Bool
  phase : R → Phase
  rq : R → Q
  width : R → Nat
  lingers : R → Bool
  seats : Q → Int
  tot : Int
  panicked : Bool
  /-- ghost `discardedNonEmpty`: a queue left the slice while some request in
  it was waiting, executing or lingering (the strict reading of "empty") -/
  discarded : Bool
  /-- ghost: a queue left the slice while some request in it was waiting or
  executing (the naive reading of "empty", the one the affected guard tests) -/
  discardedNaive : Bool
  releases : R → Nat

def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

@[simp] theorem upd_same {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) :
    upd f a b a = b := by simp [upd]

theorem upd_ne {α β : Type} [DecidableEq α] (f : α → β) {a x : α} (b : β) (h : x ≠ a) :
    upd f a b x = f x := by simp [upd, h]

section Model
variable {Q R : Type} [DecidableEq Q] [DecidableEq R]

/-- `removeQueueAndUpdateIndexes(qs.queues, i)` -/
def removeAt (rs : List R) (s : St Q R) (i : Nat) : St Q R :=
  if h : i < s.slice.length then
    let v := s.slice[i]
    let sl := s.slice.eraseIdx i
    { s with
      slice := sl
      idx := fun q => if q ∈ sl ∧ i < s.idx q then s.idx q - 1 else s.idx q
      discarded := s.discarded || rs.any (fun x => s.rq x == v && (s.phase x).live)
      discardedNaive := s.discardedNaive ||
        rs.any (fun x => s.rq x == v && (s.phase x == .waiting || s.phase x == .executing)) }
  else { s with panicked := true }

/-- the guard of `removeQueueIfEmptyLocked` -/
def removeGuard (rs : List R) (corrected : Bool) (s : St Q R) (q : Q) : Bool :=
  decide (s.desired < s.slice.length) &&
  rs.all (fun x => !(s.rq x == q && s.phase x == .waiting)) &&
  rs.all (fun x => !(s.rq x == q && s.phase x == .executing)) &&
  (!corrected || s.seats q == 0)

/-- `removeQueueIfEmptyLocked(r)` -/
def removeQueueIfEmpty (rs : List R) (corrected : Bool) (s : St Q R) (r : R) : St Q R :=
  if removeGuard rs corrected s (s.rq r) then removeAt rs s (s.idx (s.rq r)) else s

/-- the seat bookkeeping of `releaseSeatsLocked` -/
def releaseSeats (s : St Q R) (r : R) : St Q R :=
  { s with
    releases := upd s.releases r (s.releases r + 1)
    tot := s.tot - s.width r
    seats := upd s.seats (s.rq r) (s.seats (s.rq r) - s.width r)
    phase := upd s.phase r .released }

/-- `releaseSeatsLocked` (with its deferred `removeQueueIfEmptyLocked`) -/
def release (rs : List R) (corrected : Bool) (s : St Q R) (r : R) : St Q R :=
  removeQueueIfEmpty rs corrected (releaseSeats s r) r

inductive Action (Q R : Type) where
  | reconfigure (n : Nat) (fresh : List Q)
  | arrive (r : R) (q : Q) (w : Nat) (l : Bool)
  | dispatch (r : R)
  | finish (r : R)
  | timerFire (r : R)

def apply (rs : List R) (corrected : Bool) : Action Q R → St Q R → Option (St Q R)
  | .reconfigure n fresh, s =>
    if 0 < n then
      if s.slice.length < n then
        if fresh.length = n - s.slice.length ∧ fresh.Nodup ∧ fresh.all (fun q => !s.used q) then
          some { s with
            slice := s.slice ++ fresh
            idx := fun q => if q ∈ fresh then s.slice.length + fresh.idxOf q else s.idx q
            used := fun q => s.used q || decide (q ∈ fresh)
            desired := n }
        else none
      else if fresh = [] then some { s with desired := n } else none
    else none
  | .arrive r q w l, s =>
    if s.phase r = .fresh ∧ q ∈ s.slice ∧ 0 < w then
      some { s with
        rq := upd s.rq r q
        width := upd s.width r w
        lingers := upd s.lingers r l
        phase := upd s.phase r .waiting }
    else none
  | .dispatch r, s =>
    if s.phase r = .waiting then
      some { s with
        phase := upd s.phase r .executing
        seats := upd s.seats (s.rq r) (s.seats (s.rq r) + s.width r)
        tot := s.tot + s.width r }
    else none
  | .finish r, s =>
    if s.phase r = .executing then
      if s.lingers r then some { s with phase := upd s.phase r .lingering }
      else some (release rs corrected s r)
    else none
  | .timerFire r, s =>
    if s.phase r = .lingering then some (release rs corrected s r) else none

/-- Stored indexes match slice positions, and the slice has no duplicates. -/
def IdxOk (s : St Q R) : Prop :=
  s.slice.Nodup ∧ ∀ i (h : i < s.slice.length), s.idx s.slice[i] = i

/-- Initial states: a constructed `queueSet` with some queues and no requests. -/
structure Init (s : St Q R) : Prop where
  idxOk : IdxOk s
  desired_pos : 0 < s.desired
  used : ∀ q ∈ s.slice, s.used q = true
  fresh : ∀ r, s.phase r = .fresh
  releases : ∀ r, s.releases r = 0
  seats : ∀ q, s.seats q = 0
  tot : s.tot = 0
  panicked : s.panicked = false
  discarded : s.discarded = false
  discardedNaive : s.discardedNaive = false

inductive Reachable (rs : List R) (corrected : Bool) : St Q R → Prop
  | init {s} : Init s → Reachable rs corrected s
  | step {s s'} (a : Action Q R) :
      Reachable rs corrected s → apply rs corrected a s = some s' → Reachable rs corrected s'

/-! ## The four properties (docs/model-contract.md) -/

def heldQ (rs : List R) (s : St Q R) (q : Q) : Int :=
  (rs.map fun r => if (s.phase r).holds ∧ s.rq r = q then (s.width r : Int) else 0).sum

def heldAll (rs : List R) (s : St Q R) : Int :=
  (rs.map fun r => if (s.phase r).holds then (s.width r : Int) else 0).sum

/-- `conservation` -/
def Conservation (rs : List R) (s : St Q R) : Prop :=
  (∀ q, s.seats q = heldQ rs s q) ∧ s.tot = heldAll rs s ∧
  (∀ q, 0 ≤ s.seats q) ∧ 0 ≤ s.tot

/-- `release_once` (state form: the ghost counter of `release` runs) -/
def ReleaseOnce (s : St Q R) : Prop := ∀ r, s.releases r ≤ 1

/-- `safe_retirement` -/
def SafeRetirement (s : St Q R) : Prop :=
  s.discarded = false ∧ ∀ r, (s.phase r).live → s.rq r ∈ s.slice

/-- `index_integrity`, in the contract's words -/
def IndexIntegrity (s : St Q R) : Prop :=
  s.panicked = false ∧
  (∀ q1 q2, q1 ∈ s.slice → q2 ∈ s.slice → s.idx q1 = s.idx q2 → q1 = q2) ∧
  (∀ q, q ∈ s.slice → s.idx q < s.slice.length) ∧
  (∀ i, i < s.slice.length → ∃ q, q ∈ s.slice ∧ s.idx q = i)

end Model

/-! ## Lemmas about lists -/

section ListLemmas
variable {α : Type} [DecidableEq α]

theorem nodup_getElem_inj {l : List α} (hnd : l.Nodup) {i j : Nat}
    (hi : i < l.length) (hj : j < l.length) (h : l[i] = l[j]) : i = j := by
  have h1 := List.Nodup.idxOf_getElem hnd i hi
  have h2 := List.Nodup.idxOf_getElem hnd j hj
  rw [h] at h1; omega

theorem mem_eraseIdx_nodup {l : List α} (hnd : l.Nodup) {k : Nat} (hk : k < l.length)
    {x : α} : x ∈ l.eraseIdx k ↔ x ∈ l ∧ x ≠ l[k] := by
  rw [List.mem_eraseIdx_iff_getElem]
  constructor
  · rintro ⟨i, hi, hik, rfl⟩
    exact ⟨List.getElem_mem hi, fun h => hik (nodup_getElem_inj hnd hi hk h)⟩
  · rintro ⟨hx, hne⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    exact ⟨i, hi, fun h => hne (by subst h; rfl), rfl⟩

/-- Updating a function at one point changes the sum only by the change in that term. -/
theorem sum_map_update {β : Type} (rs : List β) [DecidableEq β] (hnd : rs.Nodup) (f g : β → Int)
    (r0 : β) (hfg : ∀ r, r ≠ r0 → g r = f r) :
    (rs.map g).sum = (rs.map f).sum + (if r0 ∈ rs then g r0 - f r0 else 0) := by
  induction rs with
  | nil => simp
  | cons a t ih =>
    have hnd' := (List.nodup_cons.mp hnd)
    simp only [List.map_cons, List.sum_cons, List.mem_cons]
    by_cases ha : a = r0
    · subst ha
      have hrest : (t.map g).sum = (t.map f).sum := by
        have := ih hnd'.2; rw [this, if_neg hnd'.1]; simp
      rw [hrest]; simp; omega
    · rw [hfg a ha, ih hnd'.2]
      have : (r0 = a ∨ r0 ∈ t) ↔ r0 ∈ t := by
        constructor
        · rintro (h | h); exact absurd h.symm ha; exact h
        · exact .inr
      by_cases hr : r0 ∈ t
      · rw [if_pos hr, if_pos (.inr hr)]; omega
      · rw [if_neg hr, if_neg (by rintro (h | h); exact ha h.symm; exact hr h)]; omega

theorem sum_map_zero {β : Type} (rs : List β) : (rs.map fun _ => (0 : Int)).sum = 0 := by
  induction rs with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; rfl

theorem sum_nonneg {β : Type} (rs : List β) (f : β → Int) (hf : ∀ r, 0 ≤ f r) :
    0 ≤ (rs.map f).sum := by
  induction rs with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons]; have := hf a; omega

theorem term_le_sum {β : Type} (rs : List β) (f : β → Int) (hf : ∀ r, 0 ≤ f r)
    {a : β} (ha : a ∈ rs) : f a ≤ (rs.map f).sum := by
  induction rs with
  | nil => simp at ha
  | cons b t ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp ha with h | h
    · subst h; have := sum_nonneg t f hf; omega
    · have := ih h; have := hf b; omega

theorem two_terms_le_sum {β : Type} (rs : List β) (hnd : rs.Nodup) (f : β → Int)
    (hf : ∀ r, 0 ≤ f r) {a b : β} (ha : a ∈ rs) (hb : b ∈ rs) (hab : a ≠ b) :
    f a + f b ≤ (rs.map f).sum := by
  induction rs with
  | nil => simp at ha
  | cons c t ih =>
    have hnd' := List.nodup_cons.mp hnd
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp ha with h1 | h1 <;> rcases List.mem_cons.mp hb with h2 | h2
    · exact absurd (h1.trans h2.symm) hab
    · subst h1; have := term_le_sum t f hf h2; omega
    · subst h2; have := term_le_sum t f hf h1; omega
    · have := ih hnd'.2 h1 h2; have := hf c; omega

end ListLemmas

/-! ## Conservation: preserved by every action of BOTH models -/

section Conservation
variable {Q R : Type} [DecidableEq Q] [DecidableEq R]
variable (rs : List R) (hall : ∀ r, r ∈ rs) (hnd : rs.Nodup)

/-- the two sum equalities; nonnegativity follows from them -/
def ConsEq (s : St Q R) : Prop := (∀ q, s.seats q = heldQ rs s q) ∧ s.tot = heldAll rs s

theorem heldQ_nonneg (s : St Q R) (q : Q) : 0 ≤ heldQ rs s q :=
  sum_nonneg _ _ (fun r => by split <;> omega)

theorem heldAll_nonneg (s : St Q R) : 0 ≤ heldAll rs s :=
  sum_nonneg _ _ (fun r => by split <;> omega)

theorem conservation_of_consEq {s : St Q R} (h : ConsEq rs s) : Conservation rs s := by
  refine ⟨h.1, h.2, fun q => ?_, ?_⟩
  · rw [h.1 q]; exact heldQ_nonneg rs s q
  · rw [h.2]; exact heldAll_nonneg rs s

theorem consEq_removeAt {s : St Q R} (i : Nat) (h : ConsEq rs s) :
    ConsEq rs (removeAt rs s i) := by
  unfold removeAt; split <;> exact h

theorem consEq_removeQueueIfEmpty (c : Bool) {s : St Q R} (r : R) (h : ConsEq rs s) :
    ConsEq rs (removeQueueIfEmpty rs c s r) := by
  unfold removeQueueIfEmpty; split
  · exact consEq_removeAt rs _ h
  · exact h

/-- request `r`'s contribution to `heldQ s q` -/
def termQ (s : St Q R) (q : Q) (r : R) : Int :=
  if (s.phase r).holds ∧ s.rq r = q then (s.width r : Int) else 0

/-- request `r`'s contribution to `heldAll s` -/
def termAll (s : St Q R) (r : R) : Int :=
  if (s.phase r).holds then (s.width r : Int) else 0

include hall hnd in
theorem held_update {s s' : St Q R} (r : R)
    (hag : ∀ x, x ≠ r → s'.phase x = s.phase x ∧ s'.rq x = s.rq x ∧ s'.width x = s.width x) :
    (∀ q, heldQ rs s' q = heldQ rs s q + (termQ s' q r - termQ s q r)) ∧
    heldAll rs s' = heldAll rs s + (termAll s' r - termAll s r) := by
  constructor
  · intro q
    have := sum_map_update rs hnd (termQ s q) (termQ s' q) r
      (fun x hx => by obtain ⟨h1, h2, h3⟩ := hag x hx; simp [termQ, h1, h2, h3])
    rw [if_pos (hall r)] at this
    exact this
  · have := sum_map_update rs hnd (termAll s) (termAll s') r
      (fun x hx => by obtain ⟨h1, h2, h3⟩ := hag x hx; simp [termAll, h1, h3])
    rw [if_pos (hall r)] at this
    exact this

include hall hnd in
/-- One-request updates: an update keeps conservation when the seat counters
move by exactly the change of `r`'s contribution. -/
theorem consEq_of_update {s s' : St Q R} (r : R) (h : ConsEq rs s)
    (hag : ∀ x, x ≠ r → s'.phase x = s.phase x ∧ s'.rq x = s.rq x ∧ s'.width x = s.width x)
    (hseats : ∀ q, s'.seats q = s.seats q + (termQ s' q r - termQ s q r))
    (htot : s'.tot = s.tot + (termAll s' r - termAll s r)) : ConsEq rs s' := by
  obtain ⟨hq, ht⟩ := held_update rs hall hnd r hag
  exact ⟨fun q => by rw [hseats, hq, h.1], by rw [htot, ht, h.2]⟩

theorem agree_upd_phase {s : St Q R} (r : R) (p : Phase) (x : R) (hx : x ≠ r) :
    upd s.phase r p x = s.phase x ∧ s.rq x = s.rq x ∧ s.width x = s.width x :=
  ⟨upd_ne _ _ hx, rfl, rfl⟩

include hall hnd in
theorem consEq_releaseSeats {s : St Q R} (r : R) (hr : (s.phase r).holds) (h : ConsEq rs s) :
    ConsEq rs (releaseSeats s r) := by
  apply consEq_of_update rs hall hnd r h (fun x hx => agree_upd_phase r _ x hx)
  · intro q
    simp only [releaseSeats, termQ, upd_same, hr, true_and]
    by_cases hq' : q = s.rq r
    · subst hq'; simp; omega
    · rw [upd_ne _ _ hq']; simp [Ne.symm hq']
  · simp [releaseSeats, termAll, hr]; omega

include hall hnd in
theorem consEq_release (c : Bool) {s : St Q R} (r : R) (hr : (s.phase r).holds)
    (h : ConsEq rs s) : ConsEq rs (release rs c s r) :=
  consEq_removeQueueIfEmpty rs c r (consEq_releaseSeats rs hall hnd r hr h)

include hall hnd in
theorem consEq_step (c : Bool) {s s' : St Q R} (a : Action Q R)
    (h : ConsEq rs s) (hs : apply rs c a s = some s') : ConsEq rs s' := by
  cases a with
  | reconfigure n fresh =>
    simp only [apply] at hs
    split at hs
    · split at hs
      · split at hs
        · cases hs; exact h
        · cases hs
      · split at hs
        · cases hs; exact h
        · cases hs
    · cases hs
  | arrive r q w l =>
    simp only [apply] at hs
    split at hs
    · rename_i hc
      cases hs
      apply consEq_of_update rs hall hnd r h
        (fun x hx => ⟨upd_ne _ _ hx, upd_ne _ _ hx, upd_ne _ _ hx⟩)
      · intro q'; simp [termQ, hc.1]
      · simp [termAll, hc.1]
    · cases hs
  | dispatch r =>
    simp only [apply] at hs
    split at hs
    · rename_i hw
      cases hs
      apply consEq_of_update rs hall hnd r h (fun x hx => agree_upd_phase r _ x hx)
      · intro q
        simp only [termQ, upd_same, hw]
        by_cases hq' : q = s.rq r
        · subst hq'; simp
        · rw [upd_ne _ _ hq']; simp [Ne.symm hq']
      · simp [termAll, hw]
    · cases hs
  | finish r =>
    simp only [apply] at hs
    split at hs
    · rename_i he
      split at hs
      · cases hs
        apply consEq_of_update rs hall hnd r h (fun x hx => agree_upd_phase r _ x hx)
        · intro q; simp [termQ, he]
        · simp [termAll, he]
      · cases hs
        exact consEq_release rs hall hnd c r (by simp [he]) h
    · cases hs
  | timerFire r =>
    simp only [apply] at hs
    split at hs
    · rename_i hl
      cases hs
      exact consEq_release rs hall hnd c r (by simp [hl]) h
    · cases hs

include hall hnd in
theorem consEq_init {s : St Q R} (h : Init s) : ConsEq rs s := by
  constructor
  · intro q; simp [heldQ, h.seats, h.fresh, sum_map_zero]
  · simp [heldAll, h.tot, h.fresh, sum_map_zero]

include hall hnd in
theorem consEq_reachable (c : Bool) {s : St Q R} (h : Reachable rs c s) : ConsEq rs s := by
  induction h with
  | init hi => exact consEq_init rs hall hnd hi
  | step a _ hs ih => exact consEq_step rs hall hnd c a ih hs

include hall hnd in
/-- **`conservation` holds in every reachable state of both models.** -/
theorem conservation_reachable (c : Bool) {s : St Q R} (h : Reachable rs c s) :
    Conservation rs s :=
  conservation_of_consEq rs (consEq_reachable rs hall hnd c h)

include hall hnd in
/-- The first-order consequence that Veil's `release` assumes
(`conservation_fo`): two distinct holders in one queue fit in its seats. -/
theorem conservation_fo_of_cons {s : St Q R} (h : ConsEq rs s) (r x : R) (hxr : x ≠ r)
    (hr : (s.phase r).holds) (hx : (s.phase x).holds) (hq : s.rq x = s.rq r) :
    (s.width r : Int) + (s.width x : Int) ≤ s.seats (s.rq r) := by
  rw [h.1, heldQ]
  have := two_terms_le_sum rs hnd
    (fun y => if (s.phase y).holds ∧ s.rq y = s.rq r then (s.width y : Int) else 0)
    (fun y => by split <;> omega) (hall r) (hall x) (Ne.symm hxr)
  simp only [hr, hx, hq, and_self, if_true] at this
  exact this

include hall hnd in
/-- `conservation_fo` in every reachable state of either model: Veil's
`assume` in `release` never discards an execution. -/
theorem conservation_fo_reachable (c : Bool) {s : St Q R} (h : Reachable rs c s)
    (r x : R) (hxr : x ≠ r) (hr : (s.phase r).holds) (hx : (s.phase x).holds)
    (hq : s.rq x = s.rq r) :
    (s.width r : Int) + (s.width x : Int) ≤ s.seats (s.rq r) :=
  conservation_fo_of_cons rs hall hnd (consEq_reachable rs hall hnd c h) r x hxr hr hx hq

end Conservation

/-! ## The `release` counter never decreases (both models) -/

section Mono
variable {Q R : Type} [DecidableEq Q] [DecidableEq R]

theorem releases_removeAt (rs : List R) (s : St Q R) (i : Nat) :
    (removeAt rs s i).releases = s.releases := by
  unfold removeAt; split <;> rfl

theorem releases_release (rs : List R) (c : Bool) (s : St Q R) (r x : R) :
    s.releases x ≤ (release rs c s r).releases x := by
  unfold release removeQueueIfEmpty
  have : s.releases x ≤ (releaseSeats s r).releases x := by
    by_cases hx : x = r
    · subst hx; simp [releaseSeats]
    · simp [releaseSeats, upd_ne _ _ hx]
  split
  · rw [releases_removeAt]; exact this
  · exact this

theorem releases_mono (rs : List R) (c : Bool) {s s' : St Q R} (a : Action Q R)
    (hs : apply rs c a s = some s') (x : R) : s.releases x ≤ s'.releases x := by
  cases a with
  | reconfigure n fresh =>
    simp only [apply] at hs
    split at hs
    · split at hs
      · split at hs
        · cases hs; exact Nat.le_refl _
        · cases hs
      · split at hs
        · cases hs; exact Nat.le_refl _
        · cases hs
    · cases hs
  | arrive r q w l =>
    simp only [apply] at hs; split at hs
    · cases hs; exact Nat.le_refl _
    · cases hs
  | dispatch r =>
    simp only [apply] at hs; split at hs
    · cases hs; exact Nat.le_refl _
    · cases hs
  | finish r =>
    simp only [apply] at hs; split at hs
    · split at hs
      · cases hs; exact Nat.le_refl _
      · cases hs; exact releases_release rs c s r x
    · cases hs
  | timerFire r =>
    simp only [apply] at hs; split at hs
    · cases hs; exact releases_release rs c s r x
    · cases hs

end Mono

/-! ## The corrected model: an inductive invariant -/

section Corrected
variable {Q R : Type} [DecidableEq Q] [DecidableEq R]
variable (rs : List R) (hall : ∀ r, r ∈ rs) (hnd : rs.Nodup)

structure Inv (s : St Q R) : Prop where
  idxOk : IdxOk s
  cons : ConsEq rs s
  panicked : s.panicked = false
  discarded : s.discarded = false
  liveIn : ∀ r, (s.phase r).live → s.rq r ∈ s.slice
  widthPos : ∀ r, s.phase r ≠ .fresh → 0 < s.width r
  releases : ∀ r, s.releases r = if s.phase r = .released then 1 else 0
  usedSlice : ∀ q ∈ s.slice, s.used q = true

theorem idx_of_mem {s : St Q R} (h : IdxOk s) {q : Q} (hq : q ∈ s.slice) :
    ∃ (hl : s.idx q < s.slice.length), s.slice[s.idx q] = q := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hq
  rw [h.2 i hi]; exact ⟨hi, rfl⟩

include hall hnd in
theorem inv_init {s : St Q R} (h : Init s) : Inv rs s where
  idxOk := h.idxOk
  cons := consEq_init rs hall hnd h
  panicked := h.panicked
  discarded := h.discarded
  liveIn := fun r hr => by rw [h.fresh r] at hr; simp at hr
  widthPos := fun r hr => absurd (h.fresh r) hr
  releases := fun r => by rw [h.releases r, h.fresh r]; simp
  usedSlice := h.used

include hall hnd in
theorem inv_releaseSeats {s : St Q R} (hinv : Inv rs s) (r : R) (hr : (s.phase r).holds) :
    Inv rs (releaseSeats s r) where
  idxOk := hinv.idxOk
  cons := consEq_releaseSeats rs hall hnd r hr hinv.cons
  panicked := hinv.panicked
  discarded := hinv.discarded
  liveIn := fun x hx => by
    by_cases hxr : x = r
    · subst hxr; simp [releaseSeats] at hx
    · simp only [releaseSeats, upd_ne _ _ hxr] at hx ⊢; exact hinv.liveIn x hx
  widthPos := fun x hx => by
    by_cases hxr : x = r
    · subst hxr
      exact hinv.widthPos x (by intro h; rw [h] at hr; simp at hr)
    · simp only [releaseSeats, upd_ne _ _ hxr] at hx ⊢; exact hinv.widthPos x hx
  releases := fun x => by
    by_cases hxr : x = r
    · subst hxr
      have h0 := hinv.releases x
      have hnr : s.phase x ≠ .released := by intro h; rw [h] at hr; simp at hr
      rw [if_neg hnr] at h0
      simp [releaseSeats, h0]
    · simp only [releaseSeats, upd_ne _ _ hxr]; exact hinv.releases x
  usedSlice := hinv.usedSlice

include hall hnd in
/-- The corrected guard leaves no live request behind in the queue it removes. -/
theorem guard_empty {s : St Q R} (hinv : Inv rs s) {q : Q}
    (hg : removeGuard rs true s q = true) :
    ∀ x, s.rq x = q → (s.phase x).live = false := by
  intro x hxq
  simp only [removeGuard, Bool.and_eq_true, List.all_eq_true, Bool.not_or, decide_eq_true_eq,
    beq_iff_eq, Bool.not_true, Bool.false_or] at hg
  obtain ⟨⟨⟨_, hw⟩, he⟩, hz⟩ := hg
  have hw := hw x (hall x); have he := he x (hall x)
  simp only [Bool.not_and, Bool.not_eq_true', beq_eq_false_iff_ne, Bool.or_eq_true] at hw he
  cases hp : s.phase x
  · rfl
  · simp_all
  · simp_all
  · exfalso
    have hpos := hinv.widthPos x (by rw [hp]; simp)
    have hle := term_le_sum rs (termQ s q) (fun y => by unfold termQ; split <;> omega) (hall x)
    have hseq := hinv.cons.1 q
    simp only [termQ, hp, Phase.holds_lingering, hxq, and_self, if_true] at hle
    have : s.seats q = 0 := by simpa using hz
    unfold heldQ at hseq
    have heq : (rs.map (termQ s q)).sum = (rs.map fun r =>
        if (s.phase r).holds ∧ s.rq r = q then (s.width r : Int) else 0).sum := rfl
    omega
  · rfl

include hall hnd in
theorem inv_removeQueueIfEmpty {s : St Q R} (hinv : Inv rs s) (r : R)
    (hrq : s.rq r ∈ s.slice) : Inv rs (removeQueueIfEmpty rs true s r) := by
  unfold removeQueueIfEmpty
  split
  · rename_i hg
    have hempty := guard_empty rs hall hnd hinv hg
    obtain ⟨hj, hjq⟩ := idx_of_mem hinv.idxOk hrq
    have hnd' := hinv.idxOk.1
    have hmem : ∀ y, y ∈ s.slice.eraseIdx (s.idx (s.rq r)) ↔ y ∈ s.slice ∧ y ≠ s.rq r := by
      intro y; rw [mem_eraseIdx_nodup hnd' hj, hjq]
    unfold removeAt
    rw [dif_pos hj]
    refine ⟨⟨hnd'.eraseIdx _, ?_⟩, hinv.cons, hinv.panicked, ?_, ?_,
      hinv.widthPos, hinv.releases, ?_⟩
    · intro i hi
      have hlen : i < s.slice.length - 1 := by
        rw [List.length_eraseIdx, if_pos hj] at hi; exact hi
      simp only
      rw [List.getElem_eraseIdx]
      have hin : ∀ (h' : i < s.slice.length - 1),
          (if h'' : i < s.idx (s.rq r) then s.slice[i] else s.slice[i + 1]) ∈
            s.slice.eraseIdx (s.idx (s.rq r)) := by
        intro _
        have := List.getElem_mem hi
        rw [List.getElem_eraseIdx] at this; exact this
      have hin' := hin hlen
      split
      · rename_i hij
        rw [dif_pos hij] at hin'
        rw [hinv.idxOk.2 i (by omega)]
        simp [hin', Nat.not_lt.mpr (Nat.le_of_lt hij)]
      · rename_i hij
        rw [dif_neg hij] at hin'
        rw [hinv.idxOk.2 (i + 1) (by omega)]
        simp [hin']; omega
    · simp only [hinv.discarded, Bool.false_or, List.any_eq_false, Bool.and_eq_true, beq_iff_eq,
        not_and, Bool.not_eq_true]
      intro x _ hx
      rw [hjq] at hx
      exact hempty x hx
    · intro x hx
      rw [hmem]
      refine ⟨hinv.liveIn x hx, fun h => ?_⟩
      rw [hempty x h] at hx; simp at hx
    · intro y hy
      exact hinv.usedSlice y ((hmem y).mp hy).1
  · exact hinv

include hall hnd in
theorem inv_release {s : St Q R} (hinv : Inv rs s) (r : R) (hr : (s.phase r).holds) :
    Inv rs (release rs true s r) := by
  unfold release
  apply inv_removeQueueIfEmpty rs hall hnd (inv_releaseSeats rs hall hnd hinv r hr) r
  have hl : (s.phase r).live := by
    cases hp : s.phase r <;> simp_all
  exact hinv.liveIn r hl

include hall hnd in
theorem inv_step {s s' : St Q R} (a : Action Q R) (hinv : Inv rs s)
    (hs : apply rs true a s = some s') : Inv rs s' := by
  cases a with
  | reconfigure n fresh =>
    simp only [apply] at hs
    split at hs
    · split at hs
      · split at hs
        · rename_i _ hlt hc
          cases hs
          obtain ⟨hlen, hfnd, hfu⟩ := hc
          simp only [List.all_eq_true, Bool.not_eq_true'] at hfu
          have hdisj : ∀ a ∈ s.slice, ∀ b ∈ fresh, a ≠ b := by
            intro a ha b hb hab; subst hab
            have := hinv.usedSlice a ha; rw [hfu a hb] at this; cases this
          refine ⟨⟨List.nodup_append.mpr ⟨hinv.idxOk.1, hfnd, hdisj⟩, ?_⟩, hinv.cons,
            hinv.panicked, hinv.discarded, fun x hx => List.mem_append_left _ (hinv.liveIn x hx),
            hinv.widthPos, hinv.releases, ?_⟩
          · intro i hi
            simp only [List.length_append] at hi
            by_cases hil : i < s.slice.length
            · simp only
              rw [List.getElem_append_left hil]
              have hnf : s.slice[i] ∉ fresh := fun h => hdisj _ (List.getElem_mem hil) _ h rfl
              simp [hnf, hinv.idxOk.2 i hil]
            · simp only
              rw [List.getElem_append_right (by omega)]
              have hk : i - s.slice.length < fresh.length := by omega
              simp [List.getElem_mem hk, List.Nodup.idxOf_getElem hfnd _ hk]
              omega
          · intro q hq
            rcases List.mem_append.mp hq with h | h
            · simp [hinv.usedSlice q h]
            · simp [h]
        · cases hs
      · split at hs
        · cases hs; exact { hinv with }
        · cases hs
    · cases hs
  | arrive r q w l =>
    simp only [apply] at hs
    split at hs
    · rename_i hc
      obtain ⟨hfr, hq, hw⟩ := hc
      cases hs
      refine ⟨hinv.idxOk, consEq_step rs hall hnd true (.arrive r q w l) hinv.cons
        (by simp only [apply]; rw [if_pos ⟨hfr, hq, hw⟩]), hinv.panicked, hinv.discarded,
        ?_, ?_, ?_, hinv.usedSlice⟩
      · intro x hx
        by_cases hxr : x = r
        · subst hxr; simp [hq]
        · simp only [upd_ne _ _ hxr] at hx ⊢; exact hinv.liveIn x hx
      · intro x hx
        by_cases hxr : x = r
        · subst hxr; simp [hw]
        · simp only [upd_ne _ _ hxr] at hx ⊢; exact hinv.widthPos x hx
      · intro x
        by_cases hxr : x = r
        · subst hxr; have := hinv.releases x; rw [hfr] at this; simp [this]
        · simp only [upd_ne _ _ hxr]; exact hinv.releases x
    · cases hs
  | dispatch r =>
    simp only [apply] at hs
    split at hs
    · rename_i hwt
      cases hs
      refine ⟨hinv.idxOk, consEq_step rs hall hnd true (.dispatch r) hinv.cons
        (by simp only [apply]; rw [if_pos hwt]), hinv.panicked, hinv.discarded, ?_, ?_, ?_,
        hinv.usedSlice⟩
      · intro x hx
        by_cases hxr : x = r
        · subst hxr; exact hinv.liveIn x (by rw [hwt]; rfl)
        · simp only [upd_ne _ _ hxr] at hx; exact hinv.liveIn x hx
      · intro x hx
        by_cases hxr : x = r
        · subst hxr; exact hinv.widthPos x (by rw [hwt]; simp)
        · simp only [upd_ne _ _ hxr] at hx; exact hinv.widthPos x hx
      · intro x
        by_cases hxr : x = r
        · subst hxr; have := hinv.releases x; rw [hwt] at this; simp [this]
        · simp only [upd_ne _ _ hxr]; exact hinv.releases x
    · cases hs
  | finish r =>
    simp only [apply] at hs
    split at hs
    · rename_i he
      split at hs
      · rename_i hlg
        cases hs
        refine ⟨hinv.idxOk, consEq_step rs hall hnd true (.finish r) hinv.cons
          (by simp only [apply]; rw [if_pos he, if_pos hlg]), hinv.panicked, hinv.discarded,
          ?_, ?_, ?_, hinv.usedSlice⟩
        · intro x hx
          by_cases hxr : x = r
          · subst hxr; exact hinv.liveIn x (by rw [he]; rfl)
          · simp only [upd_ne _ _ hxr] at hx; exact hinv.liveIn x hx
        · intro x hx
          by_cases hxr : x = r
          · subst hxr; exact hinv.widthPos x (by rw [he]; simp)
          · simp only [upd_ne _ _ hxr] at hx; exact hinv.widthPos x hx
        · intro x
          by_cases hxr : x = r
          · subst hxr; have := hinv.releases x; rw [he] at this; simp [this]
          · simp only [upd_ne _ _ hxr]; exact hinv.releases x
      · cases hs
        exact inv_release rs hall hnd hinv r (by rw [he]; rfl)
    · cases hs
  | timerFire r =>
    simp only [apply] at hs
    split at hs
    · rename_i hl
      cases hs
      exact inv_release rs hall hnd hinv r (by rw [hl]; rfl)
    · cases hs

include hall hnd in
theorem inv_reachable {s : St Q R} (h : Reachable rs true s) : Inv rs s := by
  induction h with
  | init hi => exact inv_init rs hall hnd hi
  | step a _ hs ih => exact inv_step rs hall hnd a ih hs

theorem indexIntegrity_of_inv {s : St Q R} (hinv : Inv rs s) : IndexIntegrity s := by
  obtain ⟨hnd', hpos⟩ := hinv.idxOk
  refine ⟨hinv.panicked, ?_, ?_, ?_⟩
  · intro q1 q2 h1 h2 he
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp h1
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp h2
    rw [hpos i hi, hpos j hj] at he; subst he; rfl
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hq
    rw [hpos i hi]; exact hi
  · intro i hi
    exact ⟨s.slice[i], List.getElem_mem hi, hpos i hi⟩

include hall hnd in
/-- **Main theorem.** In every reachable state of the CORRECTED model, for a
finite request universe `rs` (every request listed exactly once), all four
properties of `docs/model-contract.md` hold. -/
theorem corrected_safe {s : St Q R} (h : Reachable rs true s) :
    Conservation rs s ∧ ReleaseOnce s ∧ SafeRetirement s ∧ IndexIntegrity s := by
  have hinv := inv_reachable rs hall hnd h
  refine ⟨conservation_of_consEq rs hinv.cons, fun r => ?_, ⟨hinv.discarded, hinv.liveIn⟩,
    indexIntegrity_of_inv rs hinv⟩
  rw [hinv.releases r]; split <;> omega

include hall hnd in
/-- `release_once` in its transition form: no step of the corrected model
runs `release` on a request whose phase is already `released` (the counter of
`release` runs for that request does not move). -/
theorem release_once_step {s s' : St Q R} (h : Reachable rs true s) (a : Action Q R)
    (hs : apply rs true a s = some s') (r : R) (hrel : s.phase r = .released) :
    s'.releases r = s.releases r := by
  have h1 := (inv_reachable rs hall hnd h).releases r
  have h2 := (inv_reachable rs hall hnd (.step a h hs)).releases r
  rw [if_pos hrel] at h1
  have h3 : s'.releases r ≤ 1 := by rw [h2]; split <;> omega
  -- the counter never decreases
  have hmono : s.releases r ≤ s'.releases r := releases_mono rs true a hs r
  omega

end Corrected

/-! ## The affected model: the issue #144077 execution (kernel-checked) -/

section Issue
open Action

/-- A constructed `queueSet` with `DesiredNumQueues = 3`: queue ids 0, 1, 2
at indexes 0, 1, 2. Requests 0 and 1. -/
def issueInit : St Nat Nat where
  slice := [0, 1, 2]
  idx := fun q => q
  desired := 3
  used := fun q => decide (q < 3)
  phase := fun _ => .fresh
  rq := fun _ => 0
  width := fun _ => 0
  lingers := fun _ => false
  seats := fun _ => 0
  tot := 0
  panicked := false
  discarded := false
  discardedNaive := false
  releases := fun _ => 0

theorem issueInit_init : Init issueInit where
  idxOk := ⟨by decide, by
    intro i hi
    have h3 : i < 3 := hi
    match i, h3 with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl⟩
  desired_pos := by decide
  used := by intro q hq; simp [issueInit] at hq ⊢; omega
  fresh := fun _ => rfl
  releases := fun _ => rfl
  seats := fun _ => rfl
  tot := rfl
  panicked := rfl
  discarded := rfl
  discardedNaive := rfl

/-- Issue #144077: two requests share the last queue (id 2), request 0
lingers, the desired count drops to 1, request 0 finishes (lingering),
request 1 finishes (`removeQueueIfEmpty` removes queue 2 while request 0 still
holds its seat), the timer fires and removes index 2 of a 2-element slice. -/
def issueActions : List (Action Nat Nat) :=
  [arrive 0 2 1 true, dispatch 0, arrive 1 2 1 false, dispatch 1,
   reconfigure 1 [], finish 0, finish 1, timerFire 0]

def run (rs : List Nat) (c : Bool) : List (Action Nat Nat) → St Nat Nat → Option (St Nat Nat)
  | [], s => some s
  | a :: as, s => (apply rs c a s).bind (run rs c as)

theorem run_reachable {rs : List Nat} {c : Bool} :
    ∀ (as : List (Action Nat Nat)) {s s' : St Nat Nat},
      Reachable rs c s → run rs c as s = some s' → Reachable rs c s'
  | [], _, _, h, hr => by simp [run] at hr; subst hr; exact h
  | a :: as, s, s', h, hr => by
    simp only [run] at hr
    cases ha : apply rs c a s with
    | none => rw [ha] at hr; cases hr
    | some t => rw [ha] at hr; exact run_reachable as (.step a h ha) hr

/-- In the AFFECTED model the issue's execution is enabled step by step and
ends with `panicked`, after the execution has already violated
`safe_retirement`. -/
theorem issue_144077_affected :
    (run [0, 1] false issueActions issueInit).map (fun s => (s.panicked, s.discarded))
      = some (true, true) := by
  decide

/-- The same eight actions in the CORRECTED model: every step is enabled,
nothing panics, no step discards a non-empty queue, and `removeQueueIfEmpty`
removes the queue once, when the timer fires (two queues remain, as in PR
#144078's test). -/
theorem issue_144077_corrected :
    (run [0, 1] true issueActions issueInit).map
      (fun s => (s.panicked, s.discarded, s.slice)) = some (false, false, [0, 1]) := by
  decide

/-- The panicking state is reachable in the affected model. -/
theorem issue_144077_panics : ∃ s : St Nat Nat,
    Reachable [0, 1] false s ∧ s.panicked = true ∧ s.discarded = true := by
  cases h : run [0, 1] false issueActions issueInit with
  | none => have := issue_144077_affected; rw [h] at this; cases this
  | some s =>
    have := issue_144077_affected
    rw [h] at this
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
    exact ⟨s, run_reachable issueActions (.init issueInit_init) h, this.1, this.2⟩

end Issue

/-! ## The naive and the strict reading of "empty" (both models)

The doc comment on `QueueSet.BeginConfigChange` says that reconfiguration
"does not discard any queue unless and until it is undesired and empty".
`discardedNaive` records a discard that breaks the naive reading (the removed
queue had a waiting or executing request).
`discarded` records one that breaks the strict reading (waiting, executing or
lingering). -/

section Naive
variable {Q R : Type} [DecidableEq Q] [DecidableEq R]
variable (rs : List R) (hall : ∀ r, r ∈ rs)

/-- An invariant of BOTH models (any guard): the slice is consistent, and
until some step discards a queue holding a live request (strict reading),
nothing else has gone wrong either: no naive discard, no panic, and every
live request's queue is in the slice. -/
structure InvS (s : St Q R) : Prop where
  idxOk : IdxOk s
  usedSlice : ∀ q ∈ s.slice, s.used q = true
  naiveImp : s.discardedNaive = true → s.discarded = true
  clean : s.discarded = false → s.panicked = false ∧ ∀ r, (s.phase r).live → s.rq r ∈ s.slice

theorem idxOk_eraseIdx {s : St Q R} (hok : IdxOk s) {i : Nat} (hi : i < s.slice.length) :
    (s.slice.eraseIdx i).Nodup ∧ ∀ j (hj : j < (s.slice.eraseIdx i).length),
      (if (s.slice.eraseIdx i)[j] ∈ s.slice.eraseIdx i ∧ i < s.idx (s.slice.eraseIdx i)[j]
        then s.idx (s.slice.eraseIdx i)[j] - 1 else s.idx (s.slice.eraseIdx i)[j]) = j := by
  refine ⟨hok.1.eraseIdx _, fun j hj => ?_⟩
  have hlen : j < s.slice.length - 1 := by
    rw [List.length_eraseIdx, if_pos hi] at hj; exact hj
  have hin := List.getElem_mem hj
  rw [List.getElem_eraseIdx] at hin ⊢
  split
  · rename_i hji
    rw [dif_pos hji] at hin
    rw [hok.2 j (by omega)]
    simp [hin, Nat.not_lt.mpr (Nat.le_of_lt hji)]
  · rename_i hji
    rw [dif_neg hji] at hin
    rw [hok.2 (j + 1) (by omega)]
    simp [hin]; omega

include hall in
theorem invS_removeAt {s : St Q R} (hS : InvS s) (i : Nat)
    (hcl : s.discarded = false → i < s.slice.length) : InvS (removeAt rs s i) := by
  unfold removeAt
  split
  · rename_i hi
    have hnd := hS.idxOk.1
    refine ⟨idxOk_eraseIdx hS.idxOk hi, ?_, ?_, ?_⟩
    · intro q hq
      exact hS.usedSlice q ((mem_eraseIdx_nodup hnd hi).mp hq).1
    · simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
      rintro (h | ⟨x, hx, hxq, hp⟩)
      · exact .inl (hS.naiveImp h)
      · refine .inr ⟨x, hx, hxq, ?_⟩
        rcases hp with hp | hp <;> simp [hp]
    · simp only [Bool.or_eq_false_iff, List.any_eq_false, Bool.and_eq_true, beq_iff_eq, not_and,
        Bool.not_eq_true]
      rintro ⟨hd, hnone⟩
      obtain ⟨hp, hlive⟩ := hS.clean hd
      refine ⟨hp, fun x hx => ?_⟩
      rw [mem_eraseIdx_nodup hnd hi]
      refine ⟨hlive x hx, fun h => ?_⟩
      rw [hnone x (hall x) h] at hx; cases hx
  · rename_i hi
    refine ⟨hS.idxOk, hS.usedSlice, hS.naiveImp, fun hd => absurd (hcl hd) hi⟩

include hall in
theorem invS_release (c : Bool) {s : St Q R} (hS : InvS s) (r : R) (hr : (s.phase r).holds) :
    InvS (release rs c s r) := by
  have hrl : (s.phase r).live := by cases hp : s.phase r <;> simp_all
  have hS1 : InvS (releaseSeats s r) := by
    refine ⟨hS.idxOk, hS.usedSlice, hS.naiveImp, fun hd => ?_⟩
    obtain ⟨hp, hlive⟩ := hS.clean hd
    refine ⟨hp, fun x hx => ?_⟩
    by_cases hxr : x = r
    · subst hxr; simp [releaseSeats] at hx
    · simp only [releaseSeats, upd_ne _ _ hxr] at hx ⊢; exact hlive x hx
  unfold release removeQueueIfEmpty
  split
  · apply invS_removeAt rs hall hS1
    intro hd
    have hin : s.rq r ∈ s.slice := (hS.clean hd).2 r hrl
    exact (idx_of_mem hS.idxOk hin).1
  · exact hS1

include hall in
theorem invS_step (c : Bool) {s s' : St Q R} (a : Action Q R) (hS : InvS s)
    (hs : apply rs c a s = some s') : InvS s' := by
  cases a with
  | reconfigure n fresh =>
    simp only [apply] at hs
    split at hs
    · split at hs
      · split at hs
        · rename_i _ hlt hc
          cases hs
          obtain ⟨hlen, hfnd, hfu⟩ := hc
          simp only [List.all_eq_true, Bool.not_eq_true'] at hfu
          have hdisj : ∀ a ∈ s.slice, ∀ b ∈ fresh, a ≠ b := by
            intro a ha b hb hab; subst hab
            have := hS.usedSlice a ha; rw [hfu a hb] at this; cases this
          refine ⟨⟨List.nodup_append.mpr ⟨hS.idxOk.1, hfnd, hdisj⟩, ?_⟩, ?_, hS.naiveImp,
            fun hd => ⟨(hS.clean hd).1, fun x hx => List.mem_append_left _ ((hS.clean hd).2 x hx)⟩⟩
          · intro i hi
            simp only [List.length_append] at hi
            by_cases hil : i < s.slice.length
            · simp only
              rw [List.getElem_append_left hil]
              have hnf : s.slice[i] ∉ fresh := fun h => hdisj _ (List.getElem_mem hil) _ h rfl
              simp [hnf, hS.idxOk.2 i hil]
            · simp only
              rw [List.getElem_append_right (by omega)]
              have hk : i - s.slice.length < fresh.length := by omega
              simp [List.getElem_mem hk, List.Nodup.idxOf_getElem hfnd _ hk]
              omega
          · intro q hq
            rcases List.mem_append.mp hq with h | h
            · simp [hS.usedSlice q h]
            · simp [h]
        · cases hs
      · split at hs
        · cases hs; exact ⟨hS.idxOk, hS.usedSlice, hS.naiveImp, hS.clean⟩
        · cases hs
    · cases hs
  | arrive r q w l =>
    simp only [apply] at hs
    split at hs
    · rename_i hc
      cases hs
      refine ⟨hS.idxOk, hS.usedSlice, hS.naiveImp, fun hd => ⟨(hS.clean hd).1, fun x hx => ?_⟩⟩
      by_cases hxr : x = r
      · subst hxr; simp [hc.2.1]
      · simp only [upd_ne _ _ hxr] at hx ⊢; exact (hS.clean hd).2 x hx
    · cases hs
  | dispatch r =>
    simp only [apply] at hs
    split at hs
    · rename_i hwt
      cases hs
      refine ⟨hS.idxOk, hS.usedSlice, hS.naiveImp, fun hd => ⟨(hS.clean hd).1, fun x hx => ?_⟩⟩
      by_cases hxr : x = r
      · subst hxr; exact (hS.clean hd).2 x (by rw [hwt]; rfl)
      · simp only [upd_ne _ _ hxr] at hx; exact (hS.clean hd).2 x hx
    · cases hs
  | finish r =>
    simp only [apply] at hs
    split at hs
    · rename_i he
      split at hs
      · cases hs
        refine ⟨hS.idxOk, hS.usedSlice, hS.naiveImp, fun hd => ⟨(hS.clean hd).1, fun x hx => ?_⟩⟩
        by_cases hxr : x = r
        · subst hxr; exact (hS.clean hd).2 x (by rw [he]; rfl)
        · simp only [upd_ne _ _ hxr] at hx; exact (hS.clean hd).2 x hx
      · cases hs
        exact invS_release rs hall c hS r (by rw [he]; rfl)
    · cases hs
  | timerFire r =>
    simp only [apply] at hs
    split at hs
    · rename_i hl
      cases hs
      exact invS_release rs hall c hS r (by rw [hl]; rfl)
    · cases hs

theorem invS_init {s : St Q R} (h : Init s) : InvS s where
  idxOk := h.idxOk
  usedSlice := h.used
  naiveImp := fun hn => by rw [h.discardedNaive] at hn; cases hn
  clean := fun _ => ⟨h.panicked, fun r hr => by rw [h.fresh r] at hr; simp at hr⟩

include hall in
theorem invS_reachable (c : Bool) {s : St Q R} (h : Reachable rs c s) : InvS s := by
  induction h with
  | init hi => exact invS_init hi
  | step a _ hs ih => exact invS_step rs hall c a ih hs

include hall in
/-- In BOTH models, a naive discard is always also a strict discard. -/
theorem naive_imp_discarded (c : Bool) {s : St Q R} (h : Reachable rs c s) :
    s.discardedNaive = true → s.discarded = true :=
  (invS_reachable rs hall c h).naiveImp

include hall in
/-- **No step sets the naive flag before the strict one.** In BOTH models (in
particular the affected one, `c = false`), as long as no step has discarded a
queue holding a waiting, executing or lingering request, no step has discarded
a queue holding a waiting or executing request either, nothing has panicked,
every live request's queue is in the slice (`SafeRetirement`), and the stored
indexes match slice positions. -/
theorem clean_until_strict_discard (c : Bool) {s : St Q R} (h : Reachable rs c s)
    (hd : s.discarded = false) :
    s.discardedNaive = false ∧ s.panicked = false ∧ SafeRetirement s ∧ IdxOk s := by
  have hS := invS_reachable rs hall c h
  obtain ⟨hp, hlive⟩ := hS.clean hd
  refine ⟨?_, hp, ⟨hd, hlive⟩, hS.idxOk⟩
  cases hn : s.discardedNaive
  · rfl
  · rw [hS.naiveImp hn] at hd; cases hd

include hall in
/-- Corrected model: the naive reading is never violated either. -/
theorem corrected_naive_safe (hnd : rs.Nodup) {s : St Q R} (h : Reachable rs true s) :
    s.discardedNaive = false :=
  (clean_until_strict_discard rs hall true h
    (corrected_safe rs hall hnd h).2.2.1.1).1

end Naive

section NaiveIssue
open Action

/-- The issue's sequence up to and including the premature removal (the
second `finish`): the strict reading is already broken, the naive one is not,
and nothing has panicked yet. -/
theorem issue_144077_first_bad_step_is_naive_ok :
    (run [0, 1] false (issueActions.take 7) issueInit).map
      (fun s => (s.discarded, s.discardedNaive, s.panicked)) = some (true, false, false) := by
  decide

/-- A wrong-queue sequence in the shape of go's `pr-wrongqueue-waiting-crash`:
queue 0 holds request 0 (lingering) and request 1; queue 1 holds request 2
(executing) and request 3 (waiting). Desired drops to 1. Request 1's finish
removes queue 0 early; request 0's timer then removes index 0 again, which is
now queue 1. -/
def wrongQueueActions : List (Action Nat Nat) :=
  [arrive 0 0 1 true, dispatch 0, arrive 1 0 1 false, dispatch 1,
   arrive 2 1 1 false, dispatch 2, arrive 3 1 1 false,
   reconfigure 1 [], finish 0, finish 1, timerFire 0]

/-- After the premature removal (10 actions), the naive reading is intact. -/
theorem wrong_queue_premature_removal :
    (run [0, 1, 2, 3] false (wrongQueueActions.take 10) issueInit).map
      (fun s => (s.discarded, s.discardedNaive, s.panicked, s.slice))
      = some (true, false, false, [1, 2]) := by
  decide

/-- After the timer (11 actions): the naive reading is violated too, at a
different queue (queue 1, holding an executing and a waiting request), and the
slice is down to queue 2. No panic: the stale index 0 is in range. -/
theorem wrong_queue_naive_violated :
    (run [0, 1, 2, 3] false wrongQueueActions issueInit).map
      (fun s => (s.discarded, s.discardedNaive, s.panicked, s.slice))
      = some (true, true, false, [2]) := by
  decide

end NaiveIssue

end ApfQueueSet.Mirror
