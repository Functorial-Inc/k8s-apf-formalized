# Notes: where the Lean/Veil side departs from the contract, and why

Each item says what `docs/model-contract.md` says, what I did, and why. Items 1 to 3 are places where the contract is ambiguous or not directly implementable. The rest are encoding choices and tool limits.

## Contract points

1. **`discardedNonEmpty` has two definitions.** The state table says "set when a queue leaves the slice while it is desired or not empty". `removeAt` says "set if `v` was not empty". "Desired" is not a property a single queue has, so I used the `removeAt` definition: set when the removed queue has a request that is `waiting`, `executing` or `lingering`.

2. **`dispatch` does not require the request's queue to be in the slice.** The contract's `dispatch(r)` only requires `phase r = waiting`. Go only dispatches from queues in `qs.queues`, so a waiting request in a queue that was removed is never dispatched (go/RESULTS.md: it is lost, and a later dispatch dereferences nil). I kept the contract's guard. It over-approximates the affected model only after `safe_retirement` has already failed. In the corrected model the guard makes no difference, because `safe_retirement` (proved) keeps every waiting request's queue in the slice.

3. **New queues need identities.** `reconfigure(n)` "appends `n - len` new queues". A finite model needs a supply of identities:
   * Veil: `param qnum : queue → Nat` numbers the identities (injective, onto `0 .. maxIds-1`, as assumptions), `created` counts those handed out, and the new queues are those numbered `created .. created + k - 1`, at indexes `len .. len + k - 1`. `reconfigure` is disabled when fewer than `k` identities are left (`created + k ≤ maxIds`). That matches the Go instrumentation, which numbers queues from 0 in creation order (go/NOTES.md item 7).
   * Mirror (`Mirror.lean`): `reconfigure n fresh` takes the new identities as a list of never-used queues, in any order. Veil's numbering is one instance of it. The trace checker reads `fresh` off the `post` snapshot.

## Encoding choices

4. **Natural-number action arguments.** Veil's model checker enumerates action arguments, and it has no `Enumeration Nat`. `reconfigure(n)` and the width in `arrive` therefore take an argument of an uninterpreted type `num` with `param val : num → Nat`. For SMT, `num` and `val` are uninterpreted, so `val n` ranges over all of `Nat`. For model checking, `num := Fin k`, `val := Fin.val`.

5. **`width` and `lingers` are set at `arrive`** (arguments `w : num`, `l : Bool`), not fixed theory functions, so the model checker explores every width and lingering choice per request.

6. **`release_once` is a ghost counter.** `releases r` counts the runs of `release r`; the property is `releases R ≤ 1`. The mirror also proves the transition form ("no step changes the counter of a request that is already `released`", `Mirror.release_once_step`).

7. **`index_integrity` is four clauses** in Veil (`index_integrity_nopanic`, `_inj`, `_bound`, `_onto`), so that each is its own verification condition. The contract's property is their conjunction. The mirror states it in one piece (`Mirror.IndexIntegrity`).

8. **`removeAt` picks the removed queue differently** in the two encodings. Veil: the in-slice `v` with `idx v = i` (the contract's words). Mirror: `slice[i]` (Go's `append(queues[:i], queues[i+1:]...)`). They agree whenever the structural part of `index_integrity` holds, which is true in every reachable state of both models (the bug never breaks it; only `panicked` is affected).

9. **`rq` of a fresh request** is pinned in `after_init` to the queue numbered 0. Leaving it at Veil's default value made SMT translation fail ("cannot translate Type"). It is never read before `arrive` sets it.

## Tool limits that changed the encoding

10. **`trusted invariant` breaks SMT translation in Veil v4.35.0.** Any `trusted invariant` clause, even `releases R ≤ 5`, makes every action VC fail with "cannot translate Type". (Reproduced with that one-line clause and `#check_action dispatch`.) The corrected model needs one non-inductive consequence of `conservation` to prove `safe_retirement`: when a request is released, it and any other holder in the same queue fit inside that queue's `seatsInUse`. I stated it as an **`assume` at the top of `release`** in both models (`conservation_fo` in the comments). That is a trusted assumption for the SMT proof. It is discharged outside Veil: `Mirror.conservation_fo_reachable` proves it holds in every reachable state of the mirror of either model, so the `assume` never cuts off an execution (correspondence by inspection). Under `#model_check`, an `assume` silently drops a transition that violates it. So no model check runs on a file with the `assume`: `AffectedMC.lean` and `CorrectedMC.lean` are generated without it, and check the same formula as `safety [conservation_fo]`.

11. **`conservation` is not stated in the SMT-verified file.** It is a sum over requests. A clause with a sum cannot be translated to SMT-LIB, and in Veil every clause is a hypothesis of every VC, so one such clause makes every VC fail. Veil cannot restrict a clause to model checking only within one module. A bare `0 ≤ seatsInUse Q` clause also failed to translate ("SMT-LIB does not support lambdas", from a `toNat` that Veil's preprocessing introduces). So in `Corrected.lean` neither is stated, and the unbounded proof of `conservation` is the mirror's (`Mirror.conservation_reachable`, both models). **The model-checking variants do state both.** `AffectedMC.lean` and `CorrectedMC.lean` add `instantiate reqEnum : Veil.Enumeration req` and a `safety [conservation]` clause, a sum over `Veil.Enumeration.allValues` plus nonnegativity, and set `veil.deferVCGeneration true`. They never run `#check_invariants`, so nothing has to be translated. A deliberately wrong copy of the clause is reported as violated, so it is evaluated.

12. **No Veil-native panic counterexample.** `#model_check` stops at the first violated clause and cannot check a subset of clauses. In the affected model the premature removal (which breaks `safe_retirement`) always comes before any stale-index panic, so the checker never reaches `panicked`. Veil's symbolic `sat trace` would find it but cannot translate this model ("SMT-LIB does not support lambdas"). The panic witness is `Mirror.issue_144077_panics` (kernel-checked, the issue's exact sequence) and `counterexamples/issue-144077-mirror-replay.txt`.

13. **SMT time-outs on `index_integrity_onto`.** cvc5 times out (and `grind` fails) on "every position below `len` is taken" (a ∀∃ formula over `Nat`) for `reconfigure`, `finish` and `timerFire`. Those three VCs are proved by hand in Lean, inside Veil (`prove_veil_invariant_goal`, end of `Corrected.lean`), from two plain lemmas in `Lemmas.lean`.

14. **`set_option veil.smt.trust false` only works module-wide.** Written as `set_option ... in #check_invariants` it had no effect (Veil still printed "Trusting SMT solver for 63 goals"). Set at the top of the module, before `#gen_spec`, the warning goes away and all VCs still pass.

15. **Downstream compiled model checking needs Veil's lakefile script.** `#model_check` (default and `compiled` modes) runs `lake script run veilModelCheckBuild` in the root workspace. The script lives in Veil's own lakefile, so `lakefile.lean` here carries a verbatim copy.

## Trace checking

16. **Schema extensions** (go/NOTES.md) are handled as follows. `desired` on every record: read, and compared through `post.desired`. A `panic` record is terminal and never conforms, because the corrected model never panics. A `panic` that replaces a `timer_fire` ends the request's lingering in the checker's own request view. `init` must have no requests; every trace has an empty `init`.

17. **Waiting order is not compared.** `post.waiting` is FIFO. The model has no queue order, since fairness and dispatch choice are out of scope, so waiting and executing are compared as sets.

18. **The checker's step function is the mirror's**, `Mirror.apply rs true`: the definition the theorems are about, not Veil's generated executable. The correspondence to the Veil model is by inspection.

## The naive reading of "empty"

19. **Second ghost flag `discardedNaive`, mirror only.** `removeAt` sets it when the removed queue has a request that is waiting or executing (not lingering), which is exactly what the affected guard tests. The Veil models do not have it; the facts about it are kernel theorems on the mirror (proof-status.md section 3b). The wrong-queue sequence for item (c) of the follow-up has an executing and a waiting request on the queue the stale index lands on, like go's `pr-wrongqueue-waiting-crash`. The mirror has no dispatch after the timer, so it does not model the later nil dereference.
