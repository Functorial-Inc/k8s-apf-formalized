module

public import Veil
public import ApfQueueSet.Lemmas

/-! # APF `queueSet` queue lifecycle: CORRECTED model, model checking

Model of one Kubernetes API Priority and Fairness `queueSet`, following
`docs/model-contract.md`. This file is the CORRECTED model (with the
`seatsInUse = 0` conjunct, PR #144078) for explicit-state model checking:
no `assume` in `release`, and extra checked clauses including the sum form
of `conservation`.

GENERATED from `Affected.lean` by `scripts/gen_corrected.py`. Do not edit.
-/

veil module ApfCorrectedMC

-- We do not trust SMT results: lean-smt reconstructs a Lean proof for every
-- VC that cvc5 discharges. `#check_invariants` in Corrected.lean relies on this.
set_option veil.smt.trust false

-- Stable queue identity (the Go `*queue` pointer), never an index.
type queue
-- Stable request identity (the Go `*request` pointer).
type req
-- A finite carrier for the natural-number arguments of actions (a desired
-- queue count, a request width). `val` maps it into `Nat`. For verification it
-- is uninterpreted, so `val n` ranges over every natural number. For model
-- checking it is `Fin k` with `val := Fin.val`.
type num
param val : num → Nat

-- The instrumentation hands out queue ids `0, 1, 2, ...` in creation order.
-- `qnum` is that numbering, `maxIds` how many identities exist.
param qnum : queue → Nat
param maxIds : Nat

enum phase_t = { fresh, waiting, executing, lingering, released }

relation inSlice : queue → Bool
function idx : queue → Nat
individual len : Nat
individual desired : Nat
-- number of queue identities handed out so far
individual created : Nat

function phase : req → phase_t
function rq : req → queue
function width : req → Nat
relation lingers : req → Bool

function seatsInUse : queue → Int
individual totSeats : Int

individual panicked : Bool
individual discardedNonEmpty : Bool
-- ghost: how many times `release` ran for a request
function releases : req → Nat

-- Model checking only: a complete list of requests, so that `conservation`
-- can be stated as a sum. For `req := Fin n` Veil resolves it to
-- `List.finRange n` (each request exactly once).
instantiate reqEnum : Veil.Enumeration req
-- Veil generates no verification conditions in the model-checking variants.
set_option veil.deferVCGeneration true

#gen_state

assumption [qnum_inj] qnum Q1 = qnum Q2 → Q1 = Q2
assumption [qnum_lt] qnum Q < maxIds
assumption [qnum_onto] ∀ i, i < maxIds → ∃ q, qnum q = i

ghost relation holds (r : req) := phase r = executing ∨ phase r = lingering
ghost relation live (r : req) := phase r = waiting ∨ phase r = executing ∨ phase r = lingering
ghost relation nonEmpty (q : queue) := ∃ r, rq r = q ∧ live r

/- Construction: `setConfiguration` with some positive `DesiredNumQueues`
on an empty `queueSet`. -/
after_init {
  let n :| 0 < val n ∧ val n ≤ maxIds
  desired := val n
  len := val n
  created := val n
  inSlice Q := decide (qnum Q < val n)
  idx Q := qnum Q
  -- Nothing depends on `rq` of a fresh request, so pin it to queue id 0.
  let q0 :| qnum q0 = 0
  rq R := q0
  phase R := fresh
  width R := 0
  lingers R := false
  releases R := 0
  seatsInUse Q := 0
  totSeats := 0
  panicked := false
  discardedNonEmpty := false
}

-- `setConfiguration` with `DesiredNumQueues = val n > 0`.
action reconfigure (n : num) {
  require 0 < val n
  if len < val n then
    let k := val n - len
    require created + k ≤ maxIds
    idx Q := if created ≤ qnum Q ∧ qnum Q < created + k then len + (qnum Q - created) else idx Q
    inSlice Q := inSlice Q || decide (created ≤ qnum Q ∧ qnum Q < created + k)
    created := created + k
    len := val n
  desired := val n
}

-- `shuffleShardAndRejectOrEnqueueLocked`: the request joins in-slice queue `q`.
action arrive (r : req) (q : queue) (w : num) (l : Bool) {
  require phase r = fresh
  require inSlice q
  require 0 < val w
  rq r := q
  width r := val w
  lingers r := l
  phase r := waiting
}

-- `dispatchLocked`
action dispatch (r : req) {
  require phase r = waiting
  phase r := executing
  seatsInUse (rq r) := seatsInUse (rq r) + (width r : Int)
  totSeats := totSeats + (width r : Int)
}

-- `removeQueueAndUpdateIndexes(qs.queues, i)`
procedure removeAt (i : Nat) {
  if len ≤ i then
    panicked := true
  else
    let v :| inSlice v ∧ idx v = i
    if nonEmpty v then
      discardedNonEmpty := true
    inSlice v := false
    idx Q := if inSlice Q ∧ i < idx Q then idx Q - 1 else idx Q
    len := len - 1
}

-- `removeQueueIfEmptyLocked(r)`
procedure removeQueueIfEmpty (r : req) {
  let q := rq r
  if desired < len ∧
     (∀ x, ¬ (rq x = q ∧ phase x = waiting)) ∧
     (∀ x, ¬ (rq x = q ∧ phase x = executing)) ∧
     seatsInUse q = 0 then
    removeAt (idx q)
}

-- `releaseSeatsLocked`
procedure release (r : req) {
  releases r := releases r + 1
  totSeats := totSeats - (width r : Int)
  seatsInUse (rq r) := seatsInUse (rq r) - (width r : Int)
  phase r := released
  removeQueueIfEmpty r
}

-- `finishRequestLocked`
action finish (r : req) {
  require phase r = executing
  if lingers r then
    phase r := lingering
  else
    release r
}

-- The `EventAfterDuration` callback of a lingering request.
action timerFire (r : req) {
  require phase r = lingering
  release r
}

-- ## Properties (names from docs/model-contract.md)

-- `release_once`: `releases r` counts the runs of `release r`.
safety [release_once] releases R ≤ 1

safety [safe_retirement]
  ¬ discardedNonEmpty ∧
  (phase R = waiting ∨ phase R = executing ∨ phase R = lingering → inSlice (rq R))

-- `index_integrity` is the conjunction of the four clauses below. They are
-- separate clauses so that each is a separate verification condition.
safety [index_integrity_nopanic] ¬ panicked
safety [index_integrity_inj] inSlice Q1 ∧ inSlice Q2 ∧ idx Q1 = idx Q2 → Q1 = Q2
safety [index_integrity_bound] inSlice Q → idx Q < len
safety [index_integrity_onto] ∀ i, i < len → ∃ q, inSlice q ∧ idx q = i

-- `conservation` (a sum over requests) is not first-order, so this file does
-- not state it. `ApfQueueSet/Mirror.lean` proves it. (Veil 4.35's pipeline
-- cannot translate a bare nonnegativity clause `0 ≤ seatsInUse Q` to SMT-LIB
-- for this model, so we leave nonnegativity to the mirror as well.)

-- ## Auxiliary invariants (true in both models; the corrected model needs
-- them to make the safety clauses inductive)
invariant [desired_bounds] 0 < desired ∧ desired ≤ len
invariant [created_bounds] len ≤ created ∧ created ≤ maxIds
invariant [in_slice_created] inSlice Q → qnum Q < created
invariant [width_pos] phase R ≠ fresh → 0 < width R
invariant [releases_count]
  (phase R = released → releases R = 1) ∧ (phase R ≠ released → releases R = 0)

-- ## Model checking only: checked in every reachable state
-- `conservation_fo` is the formula that the unbounded proof (Corrected.lean)
-- assumes in `release`; here the model checker checks it instead.
safety [conservation_fo]
  (phase R1 = executing ∨ phase R1 = lingering) ∧
  (phase R2 = executing ∨ phase R2 = lingering) ∧
  R1 ≠ R2 ∧ rq R1 = rq R2 →
    (width R1 : Int) + (width R2 : Int) ≤ seatsInUse (rq R1)
-- `conservation` (docs/model-contract.md), sum form and nonnegativity.
safety [conservation]
  seatsInUse Q = ((Veil.Enumeration.allValues : List req).map (fun r =>
    if (phase r = executing ∨ phase r = lingering) ∧ rq r = Q then (width r : Int) else 0)).sum ∧
  totSeats = ((Veil.Enumeration.allValues : List req).map (fun r =>
    if phase r = executing ∨ phase r = lingering then (width r : Int) else 0)).sum ∧
  (0 : Int) ≤ seatsInUse Q ∧ (0 : Int) ≤ totSeats

#gen_spec

-- ## Exhaustive model checking (no maxDepth). Bounds and state counts are in
-- proof-status.md. `num := Fin k` gives widths and desired counts 1 .. k-1.
#model_check interpreted { queue := Fin 2, req := Fin 2, num := Fin 3, val := fun n => n.val, qnum := fun q => q.val, maxIds := 2 }
#model_check compiled { queue := Fin 3, req := Fin 3, num := Fin 4, val := fun n => n.val, qnum := fun q => q.val, maxIds := 3 }
#model_check compiled { queue := Fin 4, req := Fin 4, num := Fin 3, val := fun n => n.val, qnum := fun q => q.val, maxIds := 4 }

end ApfCorrectedMC
