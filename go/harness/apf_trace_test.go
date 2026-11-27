/*
Copyright The Kubernetes Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

// This is the harness for the k8s-apf-formalized project. It drives one
// queueSet through scenarios inside the scope of docs/model-contract.md and
// writes the trace that trace.go emits. go/run.sh copies it into this package,
// and it is not part of any Kubernetes patch.
//
// An environment variable selects each test, and the test skips otherwise:
//   APF_SCENARIO=pr-panic|pr-wrongqueue-executing|pr-wrongqueue-waiting-crash|pr-wrongqueue-waiting-lost
//   APF_SEED=<n>   APF_TRACE_DIR=<dir>
// Each process runs one scenario, because on affected code the timer goroutine
// panics and takes the process down (exit status 2).

package queueset

import (
	"context"
	"encoding/json"
	"fmt"
	"math/rand"
	"os"
	"path/filepath"
	"strconv"
	"testing"
	"time"

	fq "k8s.io/apiserver/pkg/util/flowcontrol/fairqueuing"
	testeventclock "k8s.io/apiserver/pkg/util/flowcontrol/fairqueuing/testing/eventclock"
	"k8s.io/apiserver/pkg/util/flowcontrol/metrics"
	fcrequest "k8s.io/apiserver/pkg/util/flowcontrol/request"
)

// apfEnv is one queueSet under test plus the bookkeeping that watches its trace.
type apfEnv struct {
	t       *testing.T
	name    string
	clk     *testeventclock.Fake
	qs      fq.QueueSet
	impl    *queueSet
	cfg     fq.QueuingConfig
	limit   int
	out     *os.File
	reqs    map[int]*request // by trace id
	ready   []int            // dispatched, not yet finished, in dispatch order
	events  int
	arrived int
	done    int

	// what the watcher saw
	prev      *tracePost
	panicked  bool
	panicMsg  string
	early     int // queue left the slice while it still had waiting, executing or lingering requests
	wrong     int // the removed queue was not the queue of the request whose action caused the removal
	wrongBusy int // wrong removals of a queue that still had waiting or executing requests
	summaryOK bool
}

func apfNew(t *testing.T, name string, qCfg fq.QueuingConfig, limit int) *apfEnv {
	dir := os.Getenv("APF_TRACE_DIR")
	if dir == "" {
		dir = t.TempDir()
	}
	f, err := os.Create(filepath.Join(dir, name+".jsonl"))
	if err != nil {
		t.Fatal(err)
	}
	e := &apfEnv{t: t, name: name, cfg: qCfg, limit: limit, out: f, reqs: map[int]*request{}}
	traceSink = e.sink
	t.Cleanup(func() { traceSink = nil; f.Close() })

	metrics.Register()
	metrics.Reset()
	clk, counter := testeventclock.NewFake(time.Unix(1_000_000, 0), 0, nil)
	e.clk = clk
	qsf := newTestableQueueSetFactory(clk, countingPromiseFactoryFactory(counter))
	qsc, err := qsf.BeginConstruction(qCfg, newGaugePair(clk), newExecSeatsGauge(clk), fq.NewNamedIntegrator(clk, qCfg.Name))
	if err != nil {
		t.Fatal(err)
	}
	e.qs = qsComplete(qsc, limit)
	e.impl = e.qs.(*queueSet)
	return e
}

// apfNew installs sink as traceSink. traceLocked calls it with qs.lock held,
// so it must not call back into the queueSet.
func (e *apfEnv) sink(line []byte) {
	if _, err := e.out.Write(append(line, '\n')); err != nil {
		panic(err)
	}
	var rec traceRecord
	if err := json.Unmarshal(line, &rec); err != nil {
		panic(err)
	}
	e.events++
	switch rec.Ev {
	case "arrive":
		e.arrived++
	case "dispatch":
		e.ready = append(e.ready, *rec.Req)
	case "panic":
		e.panicked, e.panicMsg = true, rec.Msg
	}
	if e.prev != nil && rec.Ev != "panic" {
		e.watchRemovals(&rec)
	}
	post := rec.Post
	e.prev = &post
	if rec.Ev == "panic" {
		e.printSummary() // the process is about to die
	}
}

// watchRemovals compares consecutive snapshots. It is a quick, independent
// check for classifying runs. The Lean trace checker decides whether a trace
// conforms.
func (e *apfEnv) watchRemovals(rec *traceRecord) {
	now := map[int]bool{}
	for _, q := range rec.Post.Queues {
		now[q.ID] = true
	}
	for _, q := range e.prev.Queues {
		if now[q.ID] {
			continue
		}
		busy := len(q.Waiting) > 0
		for _, x := range q.Executing {
			if rec.Req == nil || x != *rec.Req {
				busy = true
			}
		}
		lingering := false
		for _, l := range rec.Post.Lingering {
			if l.Queue == q.ID {
				lingering = true
			}
		}
		if busy || lingering {
			e.early++
		}
		if rec.Queue != nil && q.ID != *rec.Queue {
			e.wrong++
			if busy {
				e.wrongBusy++
			}
		}
	}
}

// Every test defers guard. If the instrumentation did not already record a
// panic on the test goroutine (for example a nil dereference in dispatch after
// the queueSet lost a waiting request), guard writes a panic record for it.
// guard then panics again with the same value.
func (e *apfEnv) guard() {
	if p := recover(); p != nil {
		if !e.panicked {
			e.impl.lock.Lock()
			e.impl.traceLocked("panic", nil, p)
			e.impl.lock.Unlock()
		}
		e.printSummary()
		panic(p)
	}
}

func (e *apfEnv) printSummary() {
	if e.summaryOK {
		return
	}
	e.summaryOK = true
	hit := e.panicked || e.early > 0 || e.wrong > 0
	fmt.Printf("SUMMARY name=%s events=%d arrived=%d finished=%d panic=%v early_removals=%d wrong_removals=%d wrong_busy=%d hit=%v\n",
		e.name, e.events, e.arrived, e.done, e.panicked, e.early, e.wrong, e.wrongBusy, hit)
}

func (e *apfEnv) start(hash uint64, width int, linger time.Duration, descr string) *request {
	we := &fcrequest.WorkEstimate{InitialSeats: uint64(width), FinalSeats: uint64(width), AdditionalLatency: linger}
	r, _ := e.qs.StartRequest(context.Background(), we, hash, "", "fs", "test", descr, nil)
	if r == nil {
		e.t.Fatalf("request %s was rejected, which is outside the model's scope", descr)
	}
	req := r.(*request)
	e.reqs[req.id] = req
	return req
}

func (e *apfEnv) reconfigure(desired, handSize int) {
	e.cfg.DesiredNumQueues, e.cfg.HandSize = desired, handSize
	c, err := e.qs.BeginConfigChange(e.cfg)
	if err != nil {
		e.t.Fatal(err)
	}
	e.qs = qsComplete(c, e.limit)
}

func (e *apfEnv) finish(r *request) {
	r.Finish(func() {})
	e.done++
	for i, id := range e.ready {
		if id == r.id {
			e.ready = append(e.ready[:i:i], e.ready[i+1:]...)
			return
		}
	}
	e.t.Fatalf("finished request %d that was not dispatched", r.id)
}

// advance moves the fake clock forward by d, firing timers one at a time in
// time order (they run in separate goroutines, so firing two in one SetTime
// would make the trace nondeterministic).
func (e *apfEnv) advance(d time.Duration) {
	target := e.clk.Now().Add(d)
	for {
		next, ok := e.clk.GetNextTime()
		if !ok || next.After(target) {
			break
		}
		e.clk.SetTime(next)
	}
	e.clk.SetTime(target)
}

func (e *apfEnv) hashFor(queueIndex int) uint64 {
	for i := uint64(1); i < 100000; i++ {
		if e.impl.shuffleShardLocked(i, nil, nil) == queueIndex {
			return i
		}
	}
	e.t.Fatalf("no hash maps to queue index %d", queueIndex)
	return 0
}

func (e *apfEnv) nQueues() int { return len(e.impl.queues) }

func apfCfg(name string, desired, hand int) fq.QueuingConfig {
	return fq.QueuingConfig{Name: name, DesiredNumQueues: desired, QueueLengthLimit: 1000, HandSize: hand}
}

// TestAPFScenario runs the PR #144078 regression scenario in two variants.
func TestAPFScenario(t *testing.T) {
	name := os.Getenv("APF_SCENARIO")
	switch name {
	case "pr-panic":
		apfPRPanic(t)
	case "pr-wrongqueue-executing":
		apfWrongQueue(t, name, false, false)
	case "pr-wrongqueue-waiting-crash":
		apfWrongQueue(t, name, true, false)
	case "pr-wrongqueue-waiting-lost":
		apfWrongQueue(t, name, true, true)
	default:
		t.Skip("APF_SCENARIO not set")
	}
}

// apfPRPanic is the PR's test, except that it calls Errorf where the PR calls
// Fatalf, so that the clock still advances on affected code. The shared queue is the last one,
// so the stale index (2) is past the end of the shortened slice (2 queues).
func apfPRPanic(t *testing.T) {
	e := apfNew(t, "pr-panic", apfCfg("pr-panic", 3, 1), 10)
	defer e.printSummary()
	defer e.guard()
	hash := e.hashFor(2)
	r := e.start(hash, 1, time.Second, "lingering")
	s := e.start(hash, 1, 0, "ordinary")
	if e.nQueues() != 3 {
		t.Fatalf("precondition: got %d queues, want 3", e.nQueues())
	}
	e.reconfigure(1, 1)
	e.finish(r) // lingers on its seat
	e.finish(s)
	fmt.Printf("OBS after both Finish calls: %d queues; queue ids in slice and their index: %s\n", e.nQueues(), e.sliceDesc())
	if e.nQueues() != 3 {
		t.Errorf("got %d queues while the lingering request still holds seats, want 3", e.nQueues())
	}
	fmt.Printf("OBS advancing the clock by 2s, past the lingering request's 1s\n")
	e.advance(2 * time.Second)
	fmt.Printf("OBS after the timer: %d queues; %s; totSeatsInUse=%d\n", e.nQueues(), e.sliceDesc(), e.impl.totSeatsInUse)
	if e.nQueues() != 2 {
		t.Errorf("got %d queues after the lingering request released its seats, want 2", e.nQueues())
	}
	if !e.qs.IsIdle() {
		t.Error("QueueSet is not idle at the end")
	}
	if n := e.impl.totSeatsInUse; n != 0 {
		t.Errorf("totSeatsInUse=%d, want 0", n)
	}
}

// apfWrongQueue makes the stale index land in range. The queueSet starts with
// three queues, and the reconfiguration sets the desired count to one. Queue 0
// holds a lingering request r and an ordinary one s. Queue 1 holds an executing
// request t. When s finishes, removeQueueIfEmptyLocked removes queue 0 early.
// When r's timer fires, its stale index 0 now names queue 1, and
// removeQueueIfEmptyLocked removes queue 1 although t executes in it. With waiter, queue 1 also holds a waiting request
// u that is too wide to run until t finishes. With other, queue 2 holds a
// waiting request v as well, so that totRequestsWaiting stays consistent with
// some queue in the slice.
func apfWrongQueue(t *testing.T, name string, waiter, other bool) {
	e := apfNew(t, name, apfCfg(name, 3, 1), 3)
	defer e.printSummary()
	defer e.guard()
	h0, h1, h2 := e.hashFor(0), e.hashFor(1), e.hashFor(2)
	r := e.start(h0, 1, time.Second, "r-lingering")
	s := e.start(h0, 1, 0, "s-ordinary")
	tt := e.start(h1, 1, 0, "t-executing")
	var u, v *request
	if waiter {
		u = e.start(h1, 3, 0, "u-waiting-wide")
	}
	if other {
		v = e.start(h2, 3, 0, "v-waiting-wide-other-queue")
	}
	fmt.Printf("OBS before reconfigure: %s\n", e.sliceDesc())
	e.reconfigure(1, 1)
	e.finish(r)
	e.finish(s)
	fmt.Printf("OBS after r.Finish, s.Finish: %s\n", e.sliceDesc())
	if e.nQueues() != 3 {
		t.Errorf("got %d queues while the lingering request still holds seats, want 3", e.nQueues())
	}
	fmt.Printf("OBS advancing the clock by 2s; r's stale index is %d\n", e.reqs[r.id].queue.index)
	e.advance(2 * time.Second)
	fmt.Printf("OBS after r's timer: %s; t executing=%v\n", e.sliceDesc(), e.isReady(tt))
	if e.nQueues() != 2 {
		t.Errorf("got %d queues after r released its seats, want 2", e.nQueues())
	}
	e.finish(tt)
	fmt.Printf("OBS after t.Finish: %s; totSeatsInUse=%d totRequestsWaiting=%d\n", e.sliceDesc(), e.impl.totSeatsInUse, e.impl.totRequestsWaiting)
	if other {
		if !e.isReady(v) {
			t.Fatalf("v was not dispatched")
		}
		e.finish(v)
	}
	if waiter && !e.isReady(u) {
		fmt.Printf("OBS request u is never dispatched: it waits in queue q%d, which is not in the slice; totRequestsWaiting=%d, IsIdle=%v\n", u.queue.id, e.impl.totRequestsWaiting, e.qs.IsIdle())
		t.Errorf("request u was never dispatched")
		return // u.Finish would block forever
	}
	if waiter {
		e.finish(u)
	}
	if !e.qs.IsIdle() {
		t.Error("QueueSet is not idle at the end")
	}
	if e.nQueues() != 1 {
		t.Errorf("got %d queues at the end, want 1", e.nQueues())
	}
}

func (e *apfEnv) isReady(r *request) bool {
	for _, id := range e.ready {
		if id == r.id {
			return true
		}
	}
	return false
}

func (e *apfEnv) sliceDesc() string {
	s := "["
	for i, q := range e.impl.queues {
		if i > 0 {
			s += " "
		}
		s += fmt.Sprintf("q%d(index=%d,seats=%d,waiting=%d,exec=%d)", q.id, q.index, q.seatsInUse, q.requestsWaiting.Length(), q.requestsExecuting.Len())
	}
	return s + "]"
}

// TestAPFRandom runs one seeded random scenario inside the contract's scope.
func TestAPFRandom(t *testing.T) {
	seedStr := os.Getenv("APF_SEED")
	if seedStr == "" {
		t.Skip("APF_SEED not set")
	}
	seed, err := strconv.ParseInt(seedStr, 10, 64)
	if err != nil {
		t.Fatal(err)
	}
	rng := rand.New(rand.NewSource(seed))
	desired := 1 + rng.Intn(4)
	limit := 3 + rng.Intn(4)
	flows := make([]uint64, 2+rng.Intn(4))
	for i := range flows {
		flows[i] = rng.Uint64()
	}
	steps := 40 + rng.Intn(40)
	handFor := func(n int) int { return 1 + rng.Intn(min(n, 2)) }

	name := fmt.Sprintf("seed-%04d", seed)
	e := apfNew(t, name, apfCfg(name, desired, handFor(desired)), limit)
	defer e.printSummary()
	defer e.guard()

	for step := 0; step < steps; step++ {
		switch x := rng.Intn(100); {
		case x < 38: // arrival
			var linger time.Duration
			if rng.Intn(100) < 45 {
				// Distinct nanosecond offsets keep timers from tying.
				linger = time.Duration(100+rng.Intn(2900))*time.Millisecond + time.Duration(e.impl.nextRequestID+1)
			}
			e.start(flows[rng.Intn(len(flows))], 1+rng.Intn(3), linger, fmt.Sprintf("r%d", e.impl.nextRequestID))
		case x < 76: // finish some request that is executing
			if len(e.ready) > 0 {
				e.finish(e.reqs[e.ready[rng.Intn(len(e.ready))]])
			}
		case x < 88: // reconfigure up or down
			n := 1 + rng.Intn(5)
			e.reconfigure(n, handFor(n))
		default: // time passes
			e.advance(time.Duration(rng.Intn(3000)) * time.Millisecond)
		}
	}
	// Drain: finish every started request exactly once, and let every timer fire.
	for {
		for len(e.ready) > 0 {
			e.finish(e.reqs[e.ready[rng.Intn(len(e.ready))]])
		}
		if _, ok := e.clk.GetNextTime(); !ok {
			break
		}
		e.advance(5 * time.Second)
	}
	if e.done != e.arrived {
		fmt.Printf("OBS stuck requests: arrived=%d finished=%d totRequestsWaiting=%d\n", e.arrived, e.done, e.impl.totRequestsWaiting)
	}
}
