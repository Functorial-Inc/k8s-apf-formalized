# Proof status: what is proved, what is checked, what is trusted

Toolchain: Lean `leanprover/lean4:v4.35.0`, Veil `v4.35.0` (git tag, pinned in `lake-manifest.json`), cvc5 through lean-cvc5 (`d19a134c`, in-process FFI). No Mathlib. Every claim below was reproduced with `make verify` and `make check-traces` on 2026-11-25 (macOS, Apple silicon).

There are three artifacts:

* **Veil models.** `ApfQueueSet/Affected.lean` is the single source of the model. `scripts/gen_corrected.py` derives three files from it, and `make check-parallel` checks they are up to date:
  * `Corrected.lean`: adds the conjunct `seatsInUse q = 0` in `removeQueueIfEmpty`. Unbounded verification only (`#check_invariants`). Keeps the trusted `assume` in `release`. **No model checking.**
  * `CorrectedMC.lean`: adds the conjunct, **removes the `assume`**, adds the checked clauses `conservation_fo` and `conservation` (sum form and nonnegativity). The exhaustive model-checking runs live here.
  * `AffectedMC.lean`: no conjunct, **no `assume`**, the same extra clauses. The counterexample run lives here.

  Apart from those edits, the module name and the header prose, every derived file is `Affected.lean` verbatim.
* **Plain-Lean mirror** `ApfQueueSet/Mirror.lean`: the same model as ordinary Lean definitions, with one Boolean selecting the guard, and kernel-checked proofs. **The mirror corresponds to the Veil models by inspection, not by proof.** The representation differences are listed in its header and in NOTES-veil.md items 3 and 8.
* **Trace checker** `tracecheck` (`ApfQueueSet/TraceCheck.lean`), which replays Go traces with the mirror's step function.

## 1. Unbounded results for the corrected model

### 1a. Kernel-checked, no SMT: the mirror (all four properties)

```lean
theorem ApfQueueSet.Mirror.corrected_safe :
  ∀ {Q R : Type} [DecidableEq Q] [DecidableEq R] (rs : List R),
    (∀ (r : R), r ∈ rs) → rs.Nodup →
    ∀ {s : St Q R}, Reachable rs true s →
      Conservation rs s ∧ ReleaseOnce s ∧ SafeRetirement s ∧ IndexIntegrity s
```

with, from `Mirror.lean`,

```lean
def Conservation (rs : List R) (s : St Q R) : Prop :=
  (∀ q, s.seats q = heldQ rs s q) ∧ s.tot = heldAll rs s ∧
  (∀ q, 0 ≤ s.seats q) ∧ 0 ≤ s.tot
-- heldQ rs s q = Σ over r ∈ rs of (if r is executing or lingering and rq r = q then width r else 0)
-- heldAll rs s = Σ over r ∈ rs of (if r is executing or lingering then width r else 0)

def ReleaseOnce (s : St Q R) : Prop := ∀ r, s.releases r ≤ 1

def SafeRetirement (s : St Q R) : Prop :=
  s.discarded = false ∧ ∀ r, (s.phase r).live → s.rq r ∈ s.slice

def IndexIntegrity (s : St Q R) : Prop :=
  s.panicked = false ∧
  (∀ q1 q2, q1 ∈ s.slice → q2 ∈ s.slice → s.idx q1 = s.idx q2 → q1 = q2) ∧
  (∀ q, q ∈ s.slice → s.idx q < s.slice.length) ∧
  (∀ i, i < s.slice.length → ∃ q, q ∈ s.slice ∧ s.idx q = i)
```

`Reachable rs true` is the closure of `Init` under `apply rs true`, the corrected model. The request universe `rs` must list every request exactly once, i.e. the request type is finite. Queue types are arbitrary. Widths and the desired count are unbounded naturals; seat counters are `Int`.

Also kernel-checked:

```lean
theorem ApfQueueSet.Mirror.release_once_step :   -- transition form of release_once
  ∀ ... (rs : List R), (∀ r, r ∈ rs) → rs.Nodup →
    ∀ {s s' : St Q R}, Reachable rs true s → ∀ (a : Action Q R),
      apply rs true a s = some s' → ∀ (r : R), s.phase r = Phase.released →
        s'.releases r = s.releases r

theorem ApfQueueSet.Mirror.conservation_reachable :   -- BOTH models (any c)
  ∀ ... (rs : List R), (∀ r, r ∈ rs) → rs.Nodup →
    ∀ (c : Bool) {s : St Q R}, Reachable rs c s → Conservation rs s

theorem ApfQueueSet.Mirror.conservation_fo_reachable :   -- BOTH models; justifies Veil's `assume`
  ∀ ... (rs : List R), (∀ r, r ∈ rs) → rs.Nodup →
    ∀ (c : Bool) {s : St Q R}, Reachable rs c s →
      ∀ (r x : R), x ≠ r → (s.phase r).holds = true → (s.phase x).holds = true →
        s.rq x = s.rq r → ↑(s.width r) + ↑(s.width x) ≤ s.seats (s.rq r)
```

### 1b. Veil `#check_invariants` on `Corrected.lean`: SMT with proof reconstruction, plus three hand proofs

Clauses (all universally quantified over capitalised variables). `index_integrity` is the conjunction of the four `index_integrity_*` clauses.

```
safety    [release_once]            releases R ≤ 1
safety    [safe_retirement]         ¬ discardedNonEmpty ∧
                                    (phase R = waiting ∨ phase R = executing ∨ phase R = lingering → inSlice (rq R))
safety    [index_integrity_nopanic] ¬ panicked
safety    [index_integrity_inj]     inSlice Q1 ∧ inSlice Q2 ∧ idx Q1 = idx Q2 → Q1 = Q2
safety    [index_integrity_bound]   inSlice Q → idx Q < len
safety    [index_integrity_onto]    ∀ i, i < len → ∃ q, inSlice q ∧ idx q = i
invariant [desired_bounds]          0 < desired ∧ desired ≤ len
invariant [created_bounds]          len ≤ created ∧ created ≤ maxIds
invariant [in_slice_created]        inSlice Q → qnum Q < created
invariant [width_pos]               phase R ≠ fresh → 0 < width R
invariant [releases_count]          (phase R = released → releases R = 1) ∧ (phase R ≠ released → releases R = 0)
```

Theory assumptions: `qnum Q1 = qnum Q2 → Q1 = Q2`, `qnum Q < maxIds`, `∀ i, i < maxIds → ∃ q, qnum q = i`.

**Trusted assumption, used by the SMT proof:** `release` starts with

```
assume ∀ x, x ≠ r ∧ (phase x = executing ∨ phase x = lingering) ∧ rq x = rq r →
  (width r : Int) + (width x : Int) ≤ seatsInUse (rq r)
```

This is a first-order consequence of `conservation`. In both models, `safe_retirement` for `finish` and `timerFire` depends on it: it is what turns `seatsInUse q = 0` into "no other holder in `q`". The Veil result is therefore "the clauses are inductive in every execution where this `assume` holds". The `assume` exists only in `Affected.lean` and `Corrected.lean`, and neither runs a model check. The model-checking variants drop it and check the same formula as a clause (section 3). `Mirror.conservation_fo_reachable` (1a) proves that the `assume` holds in every reachable state of the mirror of either model, so it removes no executions, up to the by-inspection correspondence. It is an `assume` and not a `trusted invariant` because of a Veil bug (NOTES-veil.md item 10).

Results: 72 checks, 12 for the initializer and 12 for each of the 5 actions. All 72 pass.

| How discharged | VCs | Trust |
| -- | -- | -- |
| cvc5 through lean-smt, `set_option veil.smt.trust false` | 69 | Veil reconstructs a Lean proof from cvc5's answer. The "Trusting SMT solver for N goals" warning that Veil prints under `trust true` (63 goals) does not appear. These proofs are not exported as named declarations, so `#print axioms` cannot be run on them. I have not audited lean-smt's reconstruction for its own trusted steps. |
| hand-written Lean proofs (`prove_veil_invariant_goal`, `@[veil]`) | 3: `index_integrity_onto` for `reconfigure`, `finish`, `timerFire` | Kernel-checked. cvc5 times out on these. Proofs at the end of `Corrected.lean`, lemmas `ApfQueueSet.onto_remove` and `ApfQueueSet.onto_grow` in `Lemmas.lean`. |

The three hand proofs have the statement Veil generates, of the form

```lean
ApfCorrected.timerFire_index_integrity_onto : ∀ ... (r : req),
  (ApfCorrected.timerFire.ext r).meetsSpecificationIfSuccessfulAssuming
    (ApfCorrected.Assumptions ...) (ApfCorrected.Invariants ...) (ApfCorrected.index_integrity_onto ...)
```

(the same for `finish` and `reconfigure`).

### 1c. What `conservation` gets from each side

| Property | Mirror (kernel, no SMT) | Veil (SMT, reconstructed) |
| -- | -- | -- |
| `conservation` (sum form, nonnegativity) | proved, both models | not stated in `Corrected.lean` (not first-order; NOTES-veil.md item 11); checked by bounded model checking in `CorrectedMC.lean` |
| `release_once` | proved | proved |
| `safe_retirement` | proved | proved, given the `assume` above |
| `index_integrity` | proved | proved (`_onto`: 3 VCs by hand) |

## 2. The affected model

* **Veil explicit-state counterexample** to `safe_retirement`, found on `AffectedMC.lean` (no `assume`): `counterexamples/affected-safe_retirement.veil-mc.txt`. Instance `queue := Fin 2, req := Fin 2, num := Fin 3, maxIds := 2`, interpreted mode, 7 actions: arrive, dispatch, arrive, finish (lingers), dispatch, reconfigure(1), finish. The last `finish` removes a queue in which a request still lingers.
* **Kernel-checked panic witness** for the issue's exact sequence (3 queues, desired 3 → 1, two requests on the last queue, the lingerer finishes first):

  ```lean
  theorem ApfQueueSet.Mirror.issue_144077_affected :
    (run [0, 1] false issueActions issueInit).map (fun s => (s.panicked, s.discarded)) = some (true, true)
  theorem ApfQueueSet.Mirror.issue_144077_corrected :
    (run [0, 1] true issueActions issueInit).map (fun s => (s.panicked, s.discarded, s.slice)) = some (false, false, [0, 1])
  theorem ApfQueueSet.Mirror.issue_144077_panics :
    ∃ s : St Nat Nat, Reachable [0, 1] false s ∧ s.panicked = true ∧ s.discarded = true
  ```

  Proved by `decide`, which the kernel evaluates. A step-by-step printout is in `counterexamples/issue-144077-mirror-replay.txt`. Veil itself does not produce a panic trace (NOTES-veil.md item 12).

## 3. Bounded model checking of the corrected model (`CorrectedMC.lean`, exhaustive)

**No `assume` anywhere in this model.** `release` is exactly the Go logic, and the formula the unbounded proof assumes is a checked clause. No `maxDepth`, so every reachable state of each instance is explored. Each state is checked against all 11 clauses of section 1b plus:

```
safety [conservation_fo]
  (phase R1 = executing ∨ phase R1 = lingering) ∧ (phase R2 = executing ∨ phase R2 = lingering) ∧
  R1 ≠ R2 ∧ rq R1 = rq R2 → (width R1 : Int) + (width R2 : Int) ≤ seatsInUse (rq R1)
safety [conservation]
  seatsInUse Q = ((Veil.Enumeration.allValues : List req).map (fun r =>
    if (phase r = executing ∨ phase r = lingering) ∧ rq r = Q then (width r : Int) else 0)).sum ∧
  totSeats = ((Veil.Enumeration.allValues : List req).map (fun r =>
    if phase r = executing ∨ phase r = lingering then (width r : Int) else 0)).sum ∧
  (0 : Int) ≤ seatsInUse Q ∧ (0 : Int) ≤ totSeats
```

The sum ranges over `Veil.Enumeration.allValues`, which comes from `instantiate reqEnum : Veil.Enumeration req`. For `req := Fin n` it is `List.finRange n`, each request once. The variant sets `veil.deferVCGeneration true` and runs no verification command, so no VC is generated for it. A sanity check (a copy with `+ (if totSeats = 2 then 1 else 0)` on the left of the sum) fails at the first state with `totSeats = 2`, so the clause really is evaluated. `num := Fin k` gives widths and desired counts `1 .. k-1`.

| queue | req | num (widths, desired) | maxIds | mode | states | result |
| -- | -- | -- | -- | -- | -- | -- |
| `Fin 2` | `Fin 2` | `Fin 3` (1..2) | 2 | interpreted | 2,179 | no violation |
| `Fin 3` | `Fin 3` | `Fin 4` (1..3) | 3 | compiled | 1,243,842 | no violation |
| `Fin 4` | `Fin 4` | `Fin 3` (1..2) | 4 | compiled | 5,753,283 | no violation |

The state counts are identical to the earlier runs with the `assume`, which is consistent with the `assume` never having dropped a transition at these bounds.

Also run during the first round (with the `assume`, same counts expected but not re-run): `(3,2,4)` 20,814 states, `(3,3,3)` 112,609, `(4,3,3)` 141,025, `(3,4,3)` 3,818,435, all with no violation. `(4,4,4)` did not finish in 10 minutes and was stopped.

Timing (clean-copy build, Apple silicon): `ApfQueueSet.CorrectedMC` 51 s (three model checks, including compiling the checker binary); `ApfQueueSet.Corrected` 19 s (`#check_invariants` with proof reconstruction); `ApfQueueSet.AffectedMC` 9.4 s; `ApfQueueSet.Affected` 11 s; `ApfQueueSet.Mirror` 2.2 s. These are the per-module times lake reported in the clean-copy build (3 min 16 s in total, including all dependencies). Veil does not report per-run times.

## 3b. The naive and the strict reading of "empty" (mirror, kernel-checked)

The interface says a queue is not discarded "unless and until it is undesired and empty". The mirror now has two ghost flags, both set only by `removeAt`:

* `discarded` (the strict reading, unchanged): the removed queue had a request that was waiting, executing **or lingering**;
* `discardedNaive` (the naive reading, the one the affected guard tests): the removed queue had a request that was waiting or executing.

```lean
-- (a)+(d) both models (any guard c), every reachable state
theorem ApfQueueSet.Mirror.naive_imp_discarded :
  ∀ ... (rs : List R), (∀ r, r ∈ rs) → ∀ (c : Bool) {s : St Q R},
    Reachable rs c s → s.discardedNaive = true → s.discarded = true

theorem ApfQueueSet.Mirror.clean_until_strict_discard :
  ∀ ... (rs : List R), (∀ r, r ∈ rs) → ∀ (c : Bool) {s : St Q R},
    Reachable rs c s → s.discarded = false →
      s.discardedNaive = false ∧ s.panicked = false ∧ SafeRetirement s ∧ IdxOk s

-- (e) corrected model
theorem ApfQueueSet.Mirror.corrected_naive_safe :
  ∀ ... (rs : List R), (∀ r, r ∈ rs) → rs.Nodup → ∀ {s : St Q R},
    Reachable rs true s → s.discardedNaive = false

-- (b) the issue's sequence, stopped right after the premature removal (7 of 8 actions)
theorem ApfQueueSet.Mirror.issue_144077_first_bad_step_is_naive_ok :
  Option.map (fun s => (s.discarded, s.discardedNaive, s.panicked))
    (run [0, 1] false (List.take 7 issueActions) issueInit) = some (true, false, false)

-- (c) a wrong-queue sequence shaped like go's pr-wrongqueue-waiting-crash
theorem ApfQueueSet.Mirror.wrong_queue_premature_removal :
  Option.map (fun s => (s.discarded, s.discardedNaive, s.panicked, s.slice))
    (run [0, 1, 2, 3] false (List.take 10 wrongQueueActions) issueInit) = some (true, false, false, [1, 2])
theorem ApfQueueSet.Mirror.wrong_queue_naive_violated :
  Option.map (fun s => (s.discarded, s.discardedNaive, s.panicked, s.slice))
    (run [0, 1, 2, 3] false wrongQueueActions issueInit) = some (true, true, false, [2])
```

What these say, exactly:

* `clean_until_strict_discard` is the "naive flag is never first" fact, for **both** models (it holds for any guard, so in particular the affected one, `c = false`). In any reachable state where no queue with a waiting, executing or lingering request has been discarded yet, none with a waiting or executing request has been discarded either; nothing has panicked; every waiting, executing or lingering request's queue is in the slice; and stored indexes match slice positions. It is a state invariant, not a statement about traces. Because the flags never reset, it implies that in every execution the strict flag is set no later than the naive flag, and no panic happens while the strict flag is clear. I did not state that trace-level corollary as a separate theorem.
* `naive_imp_discarded` is the trivial half: a naive discard is a strict discard.
* (b) On the issue's sequence, the first bad step (request 1's `finish` removes queue 2 while request 0 lingers in it) breaks the strict reading and satisfies the naive one. No panic yet.
* (c) `wrongQueueActions` = `[arrive 0 0 1 true, dispatch 0, arrive 1 0 1 false, dispatch 1, arrive 2 1 1 false, dispatch 2, arrive 3 1 1 false, reconfigure 1 [], finish 0, finish 1, timerFire 0]` from `issueInit` (3 queues, desired 3). After 10 actions, request 1's `finish` has removed queue 0 early; the naive flag is still false. The 11th action, request 0's timer, removes the stale index 0, which is now queue 1 holding request 2 (executing) and request 3 (waiting): the naive reading is violated too, later and at a different queue. No panic, because index 0 is in range.
* `corrected_naive_safe` follows from `corrected_safe` and `clean_until_strict_discard`.

Proofs: `InvS` (in `Mirror.lean`) is an inductive invariant for any guard. It holds structural facts (`IdxOk`, used queues), `discardedNaive → discarded`, and "`discarded = false` → no panic ∧ live requests' queues in the slice". (b) and (c) are `decide`, evaluated by the kernel. The step-by-step states are in `counterexamples/issue-144077-mirror-replay.txt`. Adding the field changed no existing theorem statement; all earlier theorems still check.

## 4. `#print axioms` (from `ApfQueueSet/Axioms.lean`, saved in `axioms.txt`)

```
'ApfQueueSet.Mirror.corrected_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
'ApfQueueSet.Mirror.release_once_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'ApfQueueSet.Mirror.conservation_reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
'ApfQueueSet.Mirror.conservation_fo_reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
'ApfQueueSet.Mirror.issue_144077_affected' depends on axioms: [propext, Classical.choice, Quot.sound]
'ApfQueueSet.Mirror.issue_144077_corrected' depends on axioms: [propext, Classical.choice, Quot.sound]
'ApfQueueSet.Mirror.issue_144077_panics' depends on axioms: [propext, Classical.choice, Quot.sound]
'ApfQueueSet.Mirror.naive_imp_discarded' depends on axioms: [propext, Classical.choice, Quot.sound]
'ApfQueueSet.Mirror.clean_until_strict_discard' depends on axioms: [propext, Classical.choice, Quot.sound]
'ApfQueueSet.Mirror.corrected_naive_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
'ApfQueueSet.Mirror.issue_144077_first_bad_step_is_naive_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'ApfQueueSet.Mirror.wrong_queue_premature_removal' depends on axioms: [propext, Classical.choice, Quot.sound]
'ApfQueueSet.Mirror.wrong_queue_naive_violated' depends on axioms: [propext, Classical.choice, Quot.sound]
'ApfQueueSet.onto_remove' depends on axioms: [propext, Quot.sound]
'ApfQueueSet.onto_grow' depends on axioms: [propext, Classical.choice, Quot.sound]
'ApfCorrected.timerFire_index_integrity_onto' depends on axioms: [propext, Classical.choice, Quot.sound]
'ApfCorrected.finish_index_integrity_onto' depends on axioms: [propext, Classical.choice, Quot.sound]
'ApfCorrected.reconfigure_index_integrity_onto' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no `Lean.ofReduceBool` (no `native_decide`), no project axioms.

## 5. Trace conformance (`make check-traces`)

| Directory | Files | Verdict | Expected |
| -- | -- | -- | -- |
| `traces/corrected/` | 304 | 304 conform | all conform |
| `traces/mutated/` | 30 | 30 rejected | all rejected |
| `traces/handmade/ok*` | 1 | conforms | conform |
| `traces/handmade/` others | 2 | rejected (early retirement: `safe_retirement`; malformed JSON at line 5) | rejected |
| `traces/affected/` | 304 | 224 conform, 80 rejected | rejected exactly for the 76 bug-hitting seeds in go/RESULTS.md and the 4 `pr-*` scenarios: **304 of 304 agree** |

Every rejected affected trace fails first on `safe_retirement`: at a release, the `post` has removed a queue in which some request is still waiting, executing or lingering. The first failure is at a `finish` record in 58 traces and at a `timer_fire` record in 22. That includes the 18 traces that later panic, so the checker never reaches their `panic` record. Mutated traces are rejected for the reason their kind predicts: `change-seatsInUse` for `conservation`, `duplicate-timer-fire` for `release_once` (the event is not enabled), `early-queue-removal` for `safe_retirement` (and `index_integrity`, since the indexes are no longer contiguous). `swap-index` violates none of the four properties in the snapshot and is rejected only because the model predicts different indexes. `drop-timer-fire` is rejected as a model mismatch, with `conservation` or `safe_retirement` violated in the snapshot. All verdicts are in `counterexamples/tracecheck-all.txt`.

## 6. Everything that is trusted

1. Lean's kernel and the three standard axioms.
2. **The correspondence between the mirror and the Veil models, by inspection.** The mirror carries the unbounded `conservation` result and the trace checker's step function.
3. **The `assume` in Veil's `release`, for the unbounded SMT result only** (section 1b). It is discharged by `Mirror.conservation_fo_reachable`, through item 2. No model-checking result depends on it: `CorrectedMC.lean` and `AffectedMC.lean` do not contain it.
4. Veil's VC generation (the `meetsSpecificationIfSuccessfulAssuming` statements and their connection to the action semantics), and lean-smt's proof reconstruction for the 69 SMT-discharged VCs.
5. The model checker's implementation, and `Veil.Enumeration` for `Fin n` listing each request once, for section 3, which is bounded in any case.
6. That the model abstracts the Go code faithfully (`docs/model-contract.md` scope; NOTES-veil.md).
