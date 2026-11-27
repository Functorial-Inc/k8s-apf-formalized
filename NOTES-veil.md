# Notes: where the Lean/Veil side departs from the contract, and why

Each item says what `docs/model-contract.md` says, what I did, and why. Items 1 to 3 are places where the contract is ambiguous or not directly implementable. The rest are encoding choices and tool limits.

## Contract points

1. **`discardedNonEmpty` has two definitions**: The state table says "set when a queue leaves the slice while it is desired or not empty". `removeAt` says "set if `v` was not empty". "Desired" is not a property a single queue has, so I used the `removeAt` definition: `removeAt` sets the flag when the queue it removes has a request that is `waiting`, `executing` or `lingering`.

2. **`dispatch` does not require the request's queue to be in the slice**: The contract's `dispatch(r)` only requires `phase r = waiting`. Go only dispatches from queues in `qs.queues`, so Go never dispatches a waiting request whose queue `removeQueueIfEmptyLocked` has removed (go/RESULTS.md: the request is lost, and a later dispatch dereferences nil). I kept the contract's guard. It over-approximates the affected model only after `safe_retirement` has already failed. In the corrected model the guard makes no difference, because `safe_retirement` (proved) keeps every waiting request's queue in the slice.

3. **New queues need identities**: `reconfigure(n)` "appends `n - len` new queues". A finite model needs a supply of identities:
   * Veil: `param qnum : queue → Nat` numbers the identities (the model assumes it is injective and onto `0 .. maxIds-1`), `created` counts the identities that `reconfigure` has handed out, and `reconfigure` takes the queues numbered `created .. created + k - 1` as the new queues, at indexes `len .. len + k - 1`. The guard `created + k ≤ maxIds` disables `reconfigure` when fewer than `k` identities are left. That matches the Go instrumentation, which numbers queues from 0 in creation order (go/NOTES.md item 7).
   * Mirror (`Mirror.lean`): `reconfigure n fresh` takes the new identities as a list of never-used queues, in any order. Veil's numbering is one instance of it. The trace checker reads `fresh` off the `post` snapshot.

## Encoding choices

4. **Natural-number action arguments**: Veil's model checker enumerates action arguments, and it has no `Enumeration Nat`. `reconfigure(n)` and the width in `arrive` therefore take an argument of an uninterpreted type `num` with `param val : num → Nat`. For SMT, `num` and `val` are uninterpreted, so `val n` ranges over all of `Nat`. For model checking, `num := Fin k`, `val := Fin.val`.

5. **`arrive` sets `width` and `lingers`**: `arrive` takes them as arguments (`w : num`, `l : Bool`) instead of reading fixed theory functions, so the model checker explores every width and lingering choice per request.

6. **`release_once` is a ghost counter**: `releases r` counts the runs of `release r`, and the property is `releases R ≤ 1`. The mirror also proves the transition form ("no step changes the counter of a request that is already `released`", `Mirror.release_once_step`).

7. **`index_integrity` is four clauses in Veil**: The clauses `index_integrity_nopanic`, `_inj`, `_bound` and `_onto` are separate so that each is its own verification condition. The contract's property is their conjunction. The mirror states it in one piece (`Mirror.IndexIntegrity`).

8. **`removeAt` picks the removed queue differently in the two encodings**: Veil picks the in-slice `v` with `idx v = i` (the contract's words). The mirror picks `slice[i]` (Go's `append(queues[:i], queues[i+1:]...)`). They agree whenever the structural part of `index_integrity` holds, which is true in every reachable state of both models, because the bug never breaks it and affects only `panicked`.

9. **`after_init` pins `rq` of a fresh request** to the queue numbered 0: When I left it at Veil's default value, SMT translation failed ("cannot translate Type"). The model never reads it before `arrive` sets it.

## Tool limits that changed the encoding

10. **`trusted invariant` breaks SMT translation in Veil v4.35.0**: Any `trusted invariant` clause, even `releases R ≤ 5`, makes every action VC fail with "cannot translate Type". (I reproduced this with that one-line clause and `#check_action dispatch`.) The corrected model needs one non-inductive consequence of `conservation` to prove `safe_retirement`: when `release` runs on a request, that request and any other holder in the same queue fit inside that queue's `seatsInUse`. I stated it as an **`assume` at the top of `release`** in both models (`conservation_fo` in the comments). That is a trusted assumption for the SMT proof. The mirror discharges it outside Veil: `Mirror.conservation_fo_reachable` proves it holds in every reachable state of the mirror of either model, so the `assume` never cuts off an execution (the correspondence between the mirror and the Veil models is by inspection). Under `#model_check`, an `assume` silently drops a transition that violates it, so no model check runs on a file with the `assume`. `scripts/gen_corrected.py` generates `AffectedMC.lean` and `CorrectedMC.lean` without it, and those files check the same formula as `safety [conservation_fo]`.

11. **The SMT-verified file does not state `conservation`**: `conservation` is a sum over requests. Veil cannot translate a clause with a sum to SMT-LIB, and in Veil every clause is a hypothesis of every VC, so one such clause makes every VC fail. Veil cannot restrict a clause to model checking only within one module. A bare `0 ≤ seatsInUse Q` clause also failed to translate ("SMT-LIB does not support lambdas", from a `toNat` that Veil's preprocessing introduces). So `Corrected.lean` states neither, and the unbounded proof of `conservation` is the mirror's (`Mirror.conservation_reachable`, both models). **The model-checking variants do state both.** `AffectedMC.lean` and `CorrectedMC.lean` add `instantiate reqEnum : Veil.Enumeration req` and a `safety [conservation]` clause, a sum over `Veil.Enumeration.allValues` plus nonnegativity, and set `veil.deferVCGeneration true`. They never run `#check_invariants`, so Veil translates nothing to SMT-LIB. The model checker reports a deliberately wrong copy of the clause as violated, which shows that it evaluates the clause.

12. **No Veil-native panic counterexample**: `#model_check` stops at the first violated clause and cannot check a subset of clauses. In the affected model the premature removal (which breaks `safe_retirement`) always comes before any stale-index panic, so the checker never reaches `panicked`. Veil's symbolic `sat trace` would find it but cannot translate this model ("SMT-LIB does not support lambdas"). The panic witness is `Mirror.issue_144077_panics` (kernel-checked, the issue's exact sequence) and `counterexamples/issue-144077-mirror-replay.txt`.

13. **SMT time-outs on `index_integrity_onto`**: cvc5 times out (and `grind` fails) on "every position below `len` is taken" (a ∀∃ formula over `Nat`) for `reconfigure`, `finish` and `timerFire`. I proved those three VCs by hand in Lean, inside Veil (`prove_veil_invariant_goal`, end of `Corrected.lean`), from two plain lemmas in `Lemmas.lean`.

14. **`set_option veil.smt.trust false` only works module-wide**: The form `set_option ... in #check_invariants` had no effect (Veil still printed "Trusting SMT solver for 63 goals"). With the option at the top of the module, before `#gen_spec`, Veil no longer prints the warning and all VCs still pass.

15. **Downstream compiled model checking needs Veil's lakefile script**: `#model_check` (default and `compiled` modes) runs `lake script run veilModelCheckBuild` in the root workspace. The script lives in Veil's own lakefile, so `lakefile.lean` here carries a verbatim copy.

## Trace checking

16. **Schema extensions** (go/NOTES.md): The trace checker handles them as follows. It reads `desired` on every record and compares it through `post.desired`. A `panic` record is terminal and never conforms, because the corrected model never panics. A `panic` that replaces a `timer_fire` ends the request's lingering in the checker's own request view. `init` must have no requests, and every trace has an empty `init`.

17. **The checker does not compare waiting order**: `post.waiting` is FIFO. The model has no queue order, since fairness and dispatch choice are out of scope, so the checker compares waiting and executing as sets.

18. **The checker's step function is the mirror's**: It uses `Mirror.apply rs true`, the definition the theorems are about, not Veil's generated executable. The correspondence to the Veil model is by inspection.

## The naive reading of "empty"

19. **Second ghost flag `discardedNaive`, mirror only**: `removeAt` sets it when the queue it removes has a request that is waiting or executing (not lingering), which is exactly what the affected guard tests. The Veil models do not have it, and the facts about it are kernel theorems on the mirror (proof-status.md section 3b). The wrong-queue sequence for item (c) of the follow-up has an executing and a waiting request on the queue the stale index lands on, like go's `pr-wrongqueue-waiting-crash`. The mirror has no dispatch after the timer, so it does not model the later nil dereference.
