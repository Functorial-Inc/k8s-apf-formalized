# Results: running issue #144077 on real Kubernetes code

Pinned commit `dbe731cf4b0286d68d743068f251263c70719f3e` (master, 2026-11-09 per `git log`). Go 1.27.3 darwin/arm64 is installed. Upstream's `go.mod` says `go 1.27.0` and `godebug default=go1.27`, and its `.go-version` says `1.27.3`. Fix: [PR #144078](https://github.com/kubernetes/kubernetes/pull/144078), head `e2f47fe77d83`, one added conjunct `&& r.queue.seatsInUse == 0`.

## Verdict

| Claim in the issue | Reproduced? | Evidence |
| -- | -- | -- |
| Early removal: an excess queue is removed while a lingering request still holds seats in it | **Yes** | The PR author's own test, unmodified, fails on the unpatched tree: `got 2 queues while the lingering request still holds seats, want 3`. 76 of 300 random seeds hit it. |
| Panic: stale index at or past the end gives `slice bounds out of range` | **Yes** | `pr-panic` scenario: `panic: runtime error: slice bounds out of range [3:2]`, process exit 2. 5 of 300 random seeds end this way. |
| Panic crashes the process, because the timer goroutine has no `recover` | **Yes, in the fake-clock harness** | The panic is raised in a goroutine that `eventclock.Fake` starts, which kills the test binary. I did not run a real apiserver. |
| Different live queue removed when the stale index is in range | **Yes** | Three scenarios below. 28 of 300 seeds remove a queue that was not the finishing request's own; 13 of those removed a queue that still had waiting or executing requests. |
| "silently corrupting the round-robin index bookkeeping and seat accounting" | **Partly. It is not silent when a waiting request is lost.** | If the wrongly removed queue held only an *executing* request, nothing crashed (`pr-wrongqueue-executing`, exit 1 from failed assertions only). If it held a *waiting* request, the next dispatch dereferences a nil queue and the process dies with `invalid memory address or nil pointer dereference`. All 13 random seeds with a wrongly removed busy queue ended in a panic. |
| Corrected code (PR) fixes it | **Yes** | 304 of 304 corrected runs exit 0 and no seed hits the bug. The PR's test passes. |

The nil dereference is not in the issue. It is a second crash with the same root cause, and it is the common one: 13 of the 18 seeds that panic. The contract's `panicked` flag only covers slice bounds; see `NOTES.md` item 1.

## Commands

All from `go/`. Exit codes are those of the test binary for one scenario or seed.

```
./fetch.sh                      # blobless, sparse (staging/src/k8s.io) checkout at the pinned SHA into go/upstream
./run.sh pr-test                # the PR's regression test, unmodified: no patch, 0002, 0001+0002
./run.sh upstream-tests         # upstream's flowcontrol tests with 0002, then with 0001+0002
./run.sh affected 300           # 0002 only: 4 scenarios + 300 seeds -> traces/affected/*.jsonl
./run.sh corrected 300          # 0001+0002: same scenarios and seeds -> traces/corrected/*.jsonl
uv run mutate.py                # -> traces/mutated/ (30 files and MANIFEST.tsv)
```

`fetch.sh` takes about 14 s. Tests build with `cd go/upstream/staging/src/k8s.io/apiserver && go test ...`; the staging modules resolve each other through their `replace` directives, so no `vendor/` and no top-level `go.mod` is needed. `run.sh` restores the tree on exit (`git reset; git checkout .; git clean -fd`). Running `affected` and `corrected` twice produced byte-identical trace files (compared by `shasum`).

Each scenario and each seed runs in its own process: on affected code the timer goroutine panics and takes the process down, so one process per seed is the only way to keep going. Logs are in `go/logs/<mode>/`: one `.log` per run, `exit-codes.tsv`, `summary.txt`.

## 1. The PR's own test, unmodified (`./run.sh pr-test`)

```
== PR test with patches: none            (exit code: 1)
    queueset_test.go:1678: got 2 queues while the lingering request still holds seats, want 3
--- FAIL: TestRemoveQueueOnlyWhenNoSeatsInUse (0.00s)
== PR test with patches: 0002            (exit code: 1)
    queueset_test.go:1678: got 2 queues while the lingering request still holds seats, want 3
--- FAIL: TestRemoveQueueOnlyWhenNoSeatsInUse (0.00s)
== PR test with patches: 0001 0002       (exit code: 0)
--- PASS: TestRemoveQueueOnlyWhenNoSeatsInUse (0.00s)
```

This is exactly the failure message the issue quotes. The PR's test stops at that assertion (`t.Fatalf`), so it never reaches the panic. My harness uses `Errorf` and carries on.

## 2. Scenarios (`traces/*/pr-*.jsonl`)

Same results from `go/logs/affected/*.log` and `go/logs/corrected/*.log`.

| Scenario | What it is | Affected | Corrected |
| -- | -- | -- | -- |
| `pr-panic` | The PR's scenario. 3 queues, 1 desired, lingering `r` and ordinary `s` share queue index 2. | exit 2, 9 events, panic `slice bounds out of range [3:2]` | exit 0, 9 events |
| `pr-wrongqueue-executing` | Queue 0 holds `r` (lingering) and `s`. Queue 1 holds an executing `t`. | exit 1, 12 events, no panic. Queue 0 removed early at `s.Finish`. At `r`'s timer the stale index 0 removes queue 1 while `t` executes. `t` then finishes normally on a queue that is no longer in the slice. Final slice: `[q2]`. | exit 0, 12 events |
| `pr-wrongqueue-waiting-crash` | As above, plus a waiting request `u` (width 3) in queue 1. | exit 2, 13 events. The timer's removal takes out queue 1 with `t` executing and `u` waiting. The dispatch that follows in the same callback panics: nil dereference. `u` is never dispatched. | exit 0, 15 events |
| `pr-wrongqueue-waiting-lost` | As above, plus a waiting `v` (width 3) in queue 2, so the dispatch loop has something to find. | exit 2, 17 events. `u` is lost; `t` and `v` finish; then `totRequestsWaiting=1` with no waiting request in any queue, and the next dispatch panics (nil dereference). | exit 0, 18 events |

### `pr-panic`, affected

```
OBS after both Finish calls: 2 queues; queue ids in slice and their index: [q0(index=0,seats=0,waiting=0,exec=0) q1(index=1,seats=0,waiting=0,exec=0)]
    apf_trace_test.go:288: got 2 queues while the lingering request still holds seats, want 3
OBS advancing the clock by 2s, past the lingering request's 1s
panic: runtime error: slice bounds out of range [3:2] [recovered, repanicked]

goroutine 83 [running]:
...queueset.(*queueSet).traceRecoverLocked(...)          queueset/trace.go:125     <- my re-panic
panic(...)
...queueset.removeQueueAndUpdateIndexes(...)             queueset/queueset.go:1017
...queueset.(*queueSet).removeQueueIfEmptyLocked(...)    queueset/queueset.go:1004
...queueset.(*queueSet).finishRequestLocked.func1()      queueset/queueset.go:906   <- releaseSeatsLocked's deferred call
...queueset.(*queueSet).finishRequestLocked.func2.1(...) queueset/queueset.go:943   <- the timer callback
...eventclock.(*Fake).SetTime.func1.1(...)               fake.go:211
created by ...eventclock.(*Fake).SetTime.func1
```

(Line numbers are for the tree with patch 0002 applied. The stack top is `removeQueueAndUpdateIndexes` exactly as the issue says. The `[3:2]` is `queues[index+1:]` with `index=2` on a slice of length 2.)

The trace's last line is the `panic` record, `msg: "runtime error: slice bounds out of range [3:2]"`, `post.panicked: true`.

### `pr-wrongqueue-waiting-crash`, affected

```
OBS after r.Finish, s.Finish: [q1(index=0,seats=1,waiting=1,exec=1) q2(index=1,seats=0,waiting=0,exec=0)]
OBS advancing the clock by 2s; r's stale index is 0
panic: runtime error: invalid memory address or nil pointer dereference [recovered, repanicked]
[signal SIGSEGV: segmentation violation code=0x2 addr=0x8 ...]
...queueset.(*queueSet).findDispatchQueueToBoundLocked(...)   queueset.go:826   <- minQueue.requestsWaiting.Peek(), minQueue == nil
...queueset.(*queueSet).dispatchLocked(...)                   queueset.go:716
...queueset.(*queueSet).dispatchAsMuchAsPossibleLocked(...)   queueset.go:675
...queueset.(*queueSet).finishRequestLocked.func2.1(...)      queueset.go:954   <- the timer callback, after the wrong removal
```

### `pr-wrongqueue-executing`, affected (no crash)

```
OBS before reconfigure: [q0(index=0,seats=2,waiting=0,exec=2) q1(index=1,seats=1,waiting=0,exec=1) q2(index=2,seats=0,waiting=0,exec=0)]
OBS after r.Finish, s.Finish: [q1(index=0,seats=1,waiting=0,exec=1) q2(index=1,seats=0,waiting=0,exec=0)]
OBS advancing the clock by 2s; r's stale index is 0
OBS after r's timer: [q2(index=0,seats=0,waiting=0,exec=0)]; t executing=true
OBS after t.Finish: [q2(index=0,seats=0,waiting=0,exec=0)]; totSeatsInUse=0 totRequestsWaiting=0
```

Queue 1 was removed while `t` executed in it. `t` still held its seat (the set's `totSeatsInUse` counted it), then finished against a queue that no longer exists. Nothing failed except the harness's expectations (`got 1 queues after r released its seats, want 2`).

## 3. Random seeds (`traces/*/seed-NNNN.jsonl`)

Generator: `go/harness/apf_trace_test.go`, `TestAPFRandom`. Per seed: 1 to 4 desired queues, concurrency limit 3 to 6, 2 to 5 flows, hand size 1 or 2, 40 to 79 steps. A step is an arrival (38%, width 1 to 3, 45% lingering for 0.1 to 3 s), a finish of a random executing request (38%), a reconfiguration to 1 to 5 queues (12%) or a clock advance of 0 to 3 s (12%). Then a drain: finish everything, fire every timer. Queue length limit 1000, so nothing is rejected; no cancellation; desired is always positive; every started request is finished exactly once.

| | Affected (0002) | Corrected (0001 + 0002) |
| -- | -- | -- |
| Trace files | 304 (300 seeds + 4 scenarios) | 304 |
| Events in all traces | 25,806 | 26,073 |
| Events per seed trace: min / median / mean / max | 29 / 85 / 85.8 / 142 | 31 / 86 / 86.7 / 142 |
| Event kinds | init 304, arrive 6834, dispatch 6788, reconfigure 2138, finish 6769, timer_fire 2952, panic 21 | init 304, arrive 6867, dispatch 6867, reconfigure 2146, finish 6867, timer_fire 3022 |
| Exit codes | 282 × 0, 1 × 1, 21 × 2 | 304 × 0 |
| **Seeds that hit the bug** | **76 of 300** | **0 of 300** |
| of which end in a panic | 18 (13 nil dereference, 5 slice bounds) | 0 |
| of which no panic, early removal only | 58 | 0 |
| Seeds with a wrong-queue removal | 28 (13 of them removed a queue with waiting or executing requests, all 13 ended in a panic) | 0 |

"Hit" means the harness saw a queue leave the slice while it still had waiting, executing or lingering requests, or a removal of a queue that was not the finishing request's own, or a panic. In every exit-2 trace the last line is a `panic` record, and in no other trace is there one (checked over all 304 files).

Seeds that hit the bug on affected code:
`2 13 26 27 41 46 53 59 62 67 69 74 76 82 84 87 88 99 101 102 104 108 112 113 119 124 131 132 148 150 151 169 172 175 179 180 183 185 187 195 203 204 208 210 213 217 218 221 224 226 227 231 236 238 242 248 251 258 260 264 266 267 268 269 274 275 277 280 281 283 284 285 286 288 289 292`


## 4. Upstream's own tests with 0002 applied (`./run.sh upstream-tests`)

`go test -count=1 ./pkg/util/flowcontrol/...` in `staging/src/k8s.io/apiserver`, exit code 0 for both variants:

```
patches: 0002          ok  .../flowcontrol 51.176s, .../fairqueuing 0.295s, .../fairqueuing/queueset 0.574s, (all packages ok)
patches: 0001 0002     ok  .../flowcontrol 51.160s, .../fairqueuing 0.204s, .../fairqueuing/queueset 0.448s, (all packages ok)
```

The queueset package alone, `-v`: 29 top-level and 40 sub-tests pass with no patch, with 0002, and with 0001+0002 (0 failures). `go test -race` on the queueset package passes for all three.

## 5. Mutated traces (`uv run mutate.py`)

30 files in `traces/mutated/`, six per kind, made from conforming corrected traces. `MANIFEST.tsv` gives the source, the mutated `seq` and why each must be rejected. Kinds: `drop-timer-fire`, `duplicate-timer-fire`, `early-queue-removal` (a busy queue deleted from one `post`), `change-seatsInUse` (+1 in one `post`), `swap-index` (two queues exchange `index` in one `post`; this one keeps the indexes a permutation, so only the comparison with the model's expected state can reject it). `seq` is renumbered after dropping or duplicating a line, so a gap in `seq` is not what gives the mutation away. I have not run these through the Lean checker.

## Not done, or limits

- No real apiserver, no real clock. Everything uses the package's fake event clock, as the PR's test does.
- No rejection, cancellation or exempt mode (out of scope). `QueueLengthLimit` is 1000.
- The harness never fires two timers at the same instant (`NOTES.md` item 11).
- Hand sizes above 2 and more than 5 queues are not generated.
