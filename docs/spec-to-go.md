# From the Lean specification to the Go fix

This is the path from one sentence of the contract to the two lines of Go that fix
[kubernetes/kubernetes#144077](https://github.com/kubernetes/kubernetes/issues/144077).
The code is in `ApfQueueSet/Synth.lean`, `ApfQueueSet/GoFixMain.lean` and `go/gen-fix.sh`.

```
make gen-fix     # derive the guard, print it as Go, write go/patches/0003-fix-from-spec.patch
make check-fix   # regenerate, then run the Go code with the generated fix and replay its traces
```

## The steps

1. **The specification.** A *reading* of "empty" is the list of request phases that make a queue
   non-empty. `EmptyOf ps rs s q` says no request assigned to `q` is in one of those phases.
   `MayDiscard` adds "undesired". Our reading is `strictReading = [waiting, executing, lingering]`.
   The reading the affected code implements is `naiveReading = [waiting, executing]`.
2. **The observations.** `Obs` lists what the Go `queue` struct lets the code test. There is no set
   of lingering requests in Go. A lingering request is visible only through `seatsInUse`.
3. **The derivation.** `derive ps` is "undesired", then one observation per phase of the reading,
   chosen by the table `detector`.
4. **The proofs**, all checked by Lean's kernel:
   - `eval_derive_strict`: the derived guard is the corrected model's guard, so `corrected_safe`
     (the four properties, every reachable state) is a theorem about it.
   - `derived_strict_iff_spec`: in every reachable state of that model, the derived guard is true
     exactly when the queue is undesired and empty. It never discards a non-empty queue, and it
     never holds back an empty one.
   - `eval_derive_naive` and `naive_guard_unsound`: the naive reading derives the affected guard,
     and at the bad step of the issue's execution that guard is true for a queue that is not empty.
5. **The printer.** `gofix strict` prints `removeQueueIfEmptyLocked` with the derived condition.
   `go/gen-fix.sh` splices it into `queueset.go` at the pinned commit and writes the diff.

## The checks `go/gen-fix.sh` makes

- `gofix naive` must reproduce the upstream function **byte for byte**. This tests the template
  and the observation table against the code that is really there. If upstream's function
  changes, this fails before anything is generated.
- The generated file must be `gofmt`-clean.
- The generated `queueset.go` is compared with the one PR #144078 produces. At the pinned commit
  they are **byte-identical**.

## What is proved and what is trusted

| Claim | Status |
|---|---|
| The derived guard equals the corrected model's guard | Proved (`eval_derive_strict`) |
| The corrected model satisfies the four properties | Proved (`Mirror.corrected_safe`) |
| Derived guard ⇔ undesired and empty, in reachable states | Proved (`derived_strict_iff_spec`) |
| The naive guard discards a non-empty queue | Proved, one execution (`naive_guard_unsound`) |
| The printed Go for the naive reading is the upstream text | Checked, by `go/gen-fix.sh` |
| The Go code with the generated fix behaves like the model | Observed: PR regression test, 304 traces replayed in Lean, upstream's flow-control tests |
| Each Go expression in `Obs.go` reads what `Obs.eval` says | **Trusted** (four lines, by inspection) |
| The Go text around the condition (nil check, `robinIndex`) | **Trusted**, copied from upstream, not modelled |
| The Go code refines the model | **Not established.** No refinement proof. |

## Scope

This is a derivation for one guard in one function, not a Lean-to-Go compiler. The generator
knows four observations and one function template. What it does give is a fix whose *content*
(which conjuncts, and why those) comes from the specification by a function that Lean can reason
about, so that changing the reading changes the code, and the proof obligations move with it.
