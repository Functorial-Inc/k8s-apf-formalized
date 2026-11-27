# Model contract

This file fixes the vocabulary shared by the Lean/Veil model, the Go instrumentation, and the trace checker. If one of them changes, this file changes first.

Pinned source: `kubernetes/kubernetes` at `dbe731cf4b0286d68d743068f251263c70719f3e`, file `staging/src/k8s.io/apiserver/pkg/util/flowcontrol/fairqueuing/queueset/queueset.go`.

## Scope

One non-exempt `queueSet` in one API server process, with `DesiredNumQueues > 0` at all times. Every request goes through a queue. Request contexts never cancel. The client calls `Finish` exactly once on each non-nil `StartRequest` result. The event clock fires each registered callback at most once. Every action below is one critical section under `qs.lock`.

Out of scope: fairness and virtual time (`nextDispatchR`, `robinIndex`, `currentR`), the concurrency-limit guard on dispatch, rejection, cancellation and timeouts, exempt and queueless modes, metrics.

## State

| Model | Go | Notes |
| -- | -- | -- |
| `inSlice : Queue → Bool` | membership in `qs.queues` | `Queue` is a stable identity (the pointer), never an index |
| `idx : Queue → Nat` | `queue.index` | keeps its old value after `removeQueueAndUpdateIndexes` drops the queue from the slice |
| `len : Nat` | `len(qs.queues)` | |
| `desired : Nat` | `qs.qCfg.DesiredNumQueues` | always positive |
| `phase : Req → {fresh, waiting, executing, lingering, released}` | position of the request | `lingering` is: `Finish` has returned, the release callback has not run |
| `rq : Req → Queue` | `request.queue` | `arrive` sets it, and no action changes it |
| `width : Req → Nat` | `request.MaxSeats()` | positive, and `arrive` fixes it |
| `lingers : Req → Bool` | `workEstimate.AdditionalLatency > 0` | `arrive` fixes it |
| `seatsInUse : Queue → Int` | `queue.seatsInUse` | `Int`, so that an underflow is visible instead of truncated |
| `totSeats : Int` | `qs.totSeatsInUse` | |
| `panicked : Bool` | `slice bounds out of range` in `removeQueueAndUpdateIndexes` | |
| `discardedNonEmpty : Bool` | ghost | set when a queue leaves the slice while it is desired or not empty |

A request **holds a reservation** when its phase is `executing` or `lingering`. A queue is **empty** when no request with `rq r = q` is `waiting`, `executing` or `lingering`.

## Actions

| Action | Go | Effect |
| -- | -- | -- |
| `reconfigure(n)` | `setConfiguration` | `n > 0`. `desired := n`. If `n > len`, append `n - len` new queues with `idx = len, len+1, ...`. This action removes no queue. |
| `arrive(r, q)` | `shuffleShardAndRejectOrEnqueueLocked` | `phase r = fresh`, `inSlice q`. `rq r := q`, `phase r := waiting`. The shuffle-shard choice is nondeterministic. |
| `dispatch(r)` | `dispatchLocked` | `phase r = waiting`. `phase r := executing`, `seatsInUse (rq r) += width r`, `totSeats += width r`. Which request is chosen, and whether there is room, is nondeterministic. |
| `finish(r)` | `finishRequestLocked` | `phase r = executing`. If `lingers r`: `phase r := lingering`, nothing else. Otherwise `release(r)`. |
| `timerFire(r)` | the `EventAfterDuration` callback | `phase r = lingering`. `release(r)`. |

`release(r)`: `totSeats -= width r`, `seatsInUse (rq r) -= width r`, `phase r := released`, then `removeQueueIfEmpty(r)`.

`removeQueueIfEmpty(r)`, with `q = rq r`: if `len > desired`, and no request is `waiting` in `q`, and no request is `executing` in `q`, **and (corrected model only) `seatsInUse q = 0`**, then `removeAt(idx q)`.

`removeAt(i)`: if `i ≥ len` then `panicked := true`. Otherwise the queue `v` with `inSlice v ∧ idx v = i` leaves the slice and keeps its `idx`, `removeAt` decrements `idx` of every in-slice queue with `idx > i`, `len -= 1`, and `removeAt` sets `discardedNonEmpty` if `v` was not empty.

The affected model and the corrected model differ only in the bold conjunct, exactly as [PR #144078](https://github.com/kubernetes/kubernetes/pull/144078) differs from its base.

## Properties

| Name | Statement |
| -- | -- |
| `conservation` | for every queue, `seatsInUse q` is the sum of `width r` over requests holding a reservation with `rq r = q`. `totSeats` is the sum over all requests holding a reservation. Both are nonnegative. |
| `release_once` | a request is released at most once: no action can release a request whose phase is `released`. |
| `safe_retirement` | `¬ discardedNonEmpty`, and every request that is `waiting`, `executing` or `lingering` has `inSlice (rq r)`. |
| `index_integrity` | `¬ panicked`. In-slice queues have pairwise distinct `idx`, all below `len`, and every position below `len` is taken. |

## Trace schema

The Go instrumentation writes one JSON object per line, one line per model action, inside the action's critical section under `qs.lock`, after the action's effects are complete.

```json
{"seq": 7, "ev": "finish", "req": 2, "queue": 5, "width": 1, "lingers": true, "desired": 1,
 "post": {"desired": 1, "totSeatsInUse": 2, "panicked": false,
          "queues": [{"id": 3, "index": 0, "seatsInUse": 0, "waiting": [], "executing": []},
                     {"id": 5, "index": 2, "seatsInUse": 2, "waiting": [], "executing": [4]}],
          "lingering": [{"req": 2, "queue": 5, "width": 1}]}}
```

- `ev` is one of `init`, `reconfigure`, `arrive`, `dispatch`, `finish`, `timer_fire`, `panic`.
- `req` and `queue` are stable ids that the instrumentation assigns at creation. They are never slice indexes.
- `post.queues` lists `qs.queues` in slice order. `index` is the stored `queue.index` field.
- `post.lingering` lists requests whose `Finish` has run and whose release callback has not. Each entry names the queue by stable id, whether or not that queue is still in the slice.
- `init` carries the first `post` and no request. `reconfigure` carries `desired`. `arrive` carries `req`, `queue`, `width`, `lingers`. `panic` carries the recovered message in `msg`, and is the last line of its trace.
