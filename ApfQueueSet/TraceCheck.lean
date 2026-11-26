import Lean.Data.Json
import ApfQueueSet.Mirror

/-! # Trace checker

**It replays traces with `ApfQueueSet.Mirror.apply rs true`**: the corrected
model of the plain-Lean mirror (`Mirror.lean`), where `rs` is every request id
that occurs in the trace. Not Veil's generated executable.

Replays a JSONL trace (schema: `docs/model-contract.md`, extended as listed in
`go/NOTES.md`) against the CORRECTED model.

The step function is `ApfQueueSet.Mirror.apply rs true`, i.e. the very
definition that `Mirror.corrected_safe` is proved about. It mirrors the Veil
model `ApfCorrected` by inspection (see the header of `Mirror.lean`); Veil's
own executable semantics are not driven from here.

For every record after `init`:

1. The event must be an enabled action of the model (`apply` returns `some`).
2. The model's post-state must agree with the record's `post`: slice
   membership and order, stored indexes, per-queue `seatsInUse`,
   `totSeatsInUse`, `desired`, `panicked`, the waiting and executing sets of
   each queue (compared as sets: the model does not order them), and the
   lingering set with each entry's queue and width.
3. The four properties are evaluated on the record's `post` together with
   what the trace itself said about each request (`arrive` gives its queue
   and width; `finish`/`timer_fire`/`panic` end it). This view does not use the
   model, so it names the property the Go code broke even when the model
   disagrees with the trace.

A `panic` record is terminal (`go/NOTES.md` items 1 to 3). The corrected
model never panics, so a `panic` record never conforms.
-/

namespace ApfQueueSet.TraceCheck

open Lean (Json)
open ApfQueueSet.Mirror

structure QSnap where
  id : Nat
  index : Nat
  seats : Int
  waiting : List Nat
  executing : List Nat
  deriving Repr

structure LSnap where
  req : Nat
  queue : Nat
  width : Nat
  deriving Repr

structure Snap where
  desired : Nat
  tot : Int
  panicked : Bool
  queues : List QSnap
  lingering : List LSnap
  deriving Repr

structure Rec where
  seq : Nat
  ev : String
  req : Option Nat
  queue : Option Nat
  width : Option Nat
  lingers : Option Bool
  desired : Option Nat
  msg : Option String
  post : Snap
  deriving Repr

/-! ## Parsing -/

def natArr (j : Json) : Except String (List Nat) := do
  let a ← j.getArr?
  a.toList.mapM (·.getNat?)

def parseQ (j : Json) : Except String QSnap := do
  return { id := ← j.getObjValAs? Nat "id", index := ← j.getObjValAs? Nat "index",
           seats := ← j.getObjValAs? Int "seatsInUse",
           waiting := ← natArr (← j.getObjVal? "waiting"),
           executing := ← natArr (← j.getObjVal? "executing") }

def parseL (j : Json) : Except String LSnap := do
  return { req := ← j.getObjValAs? Nat "req", queue := ← j.getObjValAs? Nat "queue",
           width := ← j.getObjValAs? Nat "width" }

def parseSnap (j : Json) : Except String Snap := do
  let qs ← (← j.getObjVal? "queues").getArr?
  let ls ← (← j.getObjVal? "lingering").getArr?
  return { desired := ← j.getObjValAs? Nat "desired", tot := ← j.getObjValAs? Int "totSeatsInUse",
           panicked := ← j.getObjValAs? Bool "panicked",
           queues := ← qs.toList.mapM parseQ, lingering := ← ls.toList.mapM parseL }

def optField (α : Type) [Lean.FromJson α] (j : Json) (k : String) : Except String (Option α) :=
  match j.getObjVal? k with
  | .ok v => if v.isNull then pure none else some <$> Lean.fromJson? v
  | .error _ => pure none

def parseRec (line : String) : Except String Rec := do
  let j ← Json.parse line
  return { seq := ← j.getObjValAs? Nat "seq", ev := ← j.getObjValAs? String "ev",
           req := ← optField Nat j "req", queue := ← optField Nat j "queue",
           width := ← optField Nat j "width", lingers := ← optField Bool j "lingers",
           desired := ← optField Nat j "desired", msg := ← optField String j "msg",
           post := ← parseSnap (← j.getObjVal? "post") }

/-! ## Model state from the `init` record -/

abbrev S := St Nat Nat

def initState (p : Snap) : S where
  slice := p.queues.map (·.id)
  idx := fun q => match p.queues.find? (·.id == q) with
    | some qs => qs.index
    | none => 0
  desired := p.desired
  used := fun q => p.queues.any (·.id == q)
  phase := fun _ => .fresh
  rq := fun _ => 0
  width := fun _ => 0
  lingers := fun _ => false
  seats := fun q => match p.queues.find? (·.id == q) with
    | some qs => qs.seats
    | none => 0
  tot := p.tot
  panicked := p.panicked
  discarded := false
  discardedNaive := false
  releases := fun _ => 0

/-! ## Comparing the model with a snapshot -/

def sortNat (l : List Nat) : List Nat := l.mergeSort (· ≤ ·)

def showL (l : List Nat) : String := toString l

/-- The first disagreement between the model state and the snapshot. -/
def compare (rs : List Nat) (s : S) (p : Snap) : Option String := Id.run do
  let ids := p.queues.map (·.id)
  if s.slice != ids then
    return some s!"queues in slice {showL ids}, model predicts {showL s.slice}"
  for q in p.queues do
    if s.idx q.id != q.index then
      return some s!"queue {q.id} has index {q.index}, model predicts {s.idx q.id}"
    if s.seats q.id != q.seats then
      return some s!"queue {q.id} has seatsInUse {q.seats}, model predicts {s.seats q.id}"
    let mw := sortNat (rs.filter fun r => s.phase r == .waiting && s.rq r == q.id)
    if mw != sortNat q.waiting then
      return some s!"queue {q.id} waiting {showL (sortNat q.waiting)}, model predicts {showL mw}"
    let me := sortNat (rs.filter fun r => s.phase r == .executing && s.rq r == q.id)
    if me != sortNat q.executing then
      return some s!"queue {q.id} executing {showL (sortNat q.executing)}, model predicts {showL me}"
  -- waiting/executing requests whose queue is not in the snapshot's slice
  for r in rs do
    if (s.phase r == .waiting || s.phase r == .executing) && !(ids.contains (s.rq r)) then
      return some s!"request {r} is {repr (s.phase r)} in queue {s.rq r} per the model, which the snapshot's slice does not contain"
  if s.tot != p.tot then
    return some s!"totSeatsInUse {p.tot}, model predicts {s.tot}"
  if s.desired != p.desired then
    return some s!"desired {p.desired}, model predicts {s.desired}"
  if s.panicked != p.panicked then
    return some s!"panicked {p.panicked}, model predicts {s.panicked}"
  let ml := sortNat (rs.filter fun r => s.phase r == .lingering)
  let pl := sortNat (p.lingering.map (·.req))
  if ml != pl then
    return some s!"lingering {showL pl}, model predicts {showL ml}"
  for l in p.lingering do
    if s.rq l.req != l.queue || s.width l.req != l.width then
      return some s!"lingering request {l.req} listed with queue {l.queue} width {l.width}, model has queue {s.rq l.req} width {s.width l.req}"
  return none

/-! ## The four properties on a snapshot, with the trace's own request view -/

/-- What the trace itself says about requests: queue and width from
`arrive`, live until a releasing `finish`, a `timer_fire` or a `panic`
naming it; how many times each was released. -/
structure View where
  info : List (Nat × Nat × Nat) := []   -- (req, queue, width)
  live : List Nat := []
  dispatched : List Nat := []
  released : List (Nat × Nat) := []     -- (req, count)

def View.queueOf (v : View) (r : Nat) : Option Nat := (v.info.find? (·.1 == r)).map (·.2.1)
def View.widthOf (v : View) (r : Nat) : Nat := ((v.info.find? (·.1 == r)).map (·.2.2)).getD 0
def View.relCount (v : View) (r : Nat) : Nat := ((v.released.find? (·.1 == r)).map (·.2)).getD 0
def View.release (v : View) (r : Nat) : View :=
  { v with live := v.live.erase r,
           released := (r, v.relCount r + 1) :: v.released.filter (·.1 != r) }

/-- Violated properties of the snapshot, with reasons. -/
def snapProps (v : View) (p : Snap) : List (String × String) := Id.run do
  let mut out : List (String × String) := []
  let ids := p.queues.map (·.id)
  let n := p.queues.length
  -- index_integrity
  if p.panicked then
    out := out ++ [("index_integrity", "post.panicked is true")]
  let idxs := p.queues.map (·.index)
  if !(idxs.all (· < n)) || (List.range n).any (fun i => !(idxs.contains i)) then
    out := out ++ [("index_integrity", s!"stored indexes {showL idxs} are not a permutation of 0..{n}-1")]
  -- safe_retirement
  for r in v.live do
    match v.queueOf r with
    | some q => if !(ids.contains q) then
        out := out ++ [("safe_retirement", s!"request {r} is still waiting, executing or lingering in queue {q}, which is not in the slice")]
    | none => pure ()
  for l in p.lingering do
    if !(ids.contains l.queue) then
      out := out ++ [("safe_retirement", s!"lingering request {l.req} holds seats in queue {l.queue}, which is not in the slice")]
  -- release_once
  for (r, c) in v.released do
    if c > 1 then
      out := out ++ [("release_once", s!"request {r} released {c} times")]
  -- conservation
  for q in p.queues do
    let sum : Int := (q.executing.map fun r => (v.widthOf r : Int)).sum +
      ((p.lingering.filter (·.queue == q.id)).map fun l => (l.width : Int)).sum
    if q.seats != sum then
      out := out ++ [("conservation", s!"queue {q.id} has seatsInUse {q.seats} but its reservations sum to {sum}")]
    if q.seats < 0 then
      out := out ++ [("conservation", s!"queue {q.id} has negative seatsInUse {q.seats}")]
  -- totals: every holder the trace knows of, in or out of the slice
  let holders := v.live.filter fun r => v.dispatched.contains r
  let tsum : Int := (holders.map fun r => (v.widthOf r : Int)).sum
  if p.tot != tsum then
    out := out ++ [("conservation", s!"totSeatsInUse {p.tot} but the reservations sum to {tsum}")]
  if p.tot < 0 then
    out := out ++ [("conservation", s!"negative totSeatsInUse {p.tot}")]
  return out

/-! ## Replay -/

structure Failure where
  line : Nat
  seq : Nat
  ev : String
  reason : String
  violated : List String

def Failure.render (f : Failure) : String :=
  let v := if f.violated.isEmpty then "none of the four in the snapshot (model mismatch)"
    else ", ".intercalate f.violated.eraseDups
  s!"line {f.line} (seq {f.seq}, ev {f.ev}): {f.reason} [violates: {v}]"

def reqIds (recs : List Rec) : List Nat :=
  (recs.foldl (fun acc r =>
    let fromPost := r.post.queues.foldl (fun a q => a ++ q.waiting ++ q.executing) [] ++
      r.post.lingering.map (·.req)
    acc ++ r.req.toList ++ fromPost) []).eraseDups

def needReq (r : Rec) : Except String Nat :=
  match r.req with
  | some x => pure x
  | none => throw s!"record seq {r.seq} ({r.ev}) has no req"

/-- Update the trace's own request view for one record. -/
def viewStep (v : View) (r : Rec) : View :=
  match r.ev, r.req with
  | "arrive", some x =>
    { v with info := (x, r.queue.getD 0, r.width.getD 0) :: v.info, live := x :: v.live }
  | "dispatch", some x => { v with dispatched := x :: v.dispatched }
  | "finish", some x => if r.lingers == some true then v else v.release x
  | "timer_fire", some x => v.release x
  | "panic", some x =>
    -- a panic that replaced a timer_fire (`go/NOTES.md` item 3): the
    -- request is no longer lingering in `post`, its release already ran
    if (r.post.lingering.any (·.req == x)) then v
    else if v.live.contains x then v.release x else v
  | _, _ => v

/-- The model action for a record, given the state before it. -/
def actionOf (s : S) (r : Rec) : Except String (Action Nat Nat) := do
  match r.ev with
  | "reconfigure" =>
    let n := r.desired.getD r.post.desired
    let fresh := (r.post.queues.map (·.id)).filter (fun q => !(s.slice.contains q))
    return .reconfigure n fresh
  | "arrive" =>
    return .arrive (← needReq r) (r.queue.getD 0) (r.width.getD 0) (r.lingers.getD false)
  | "dispatch" => return .dispatch (← needReq r)
  | "finish" => return .finish (← needReq r)
  | "timer_fire" => return .timerFire (← needReq r)
  | ev => throw s!"unknown event {ev}"

def check (recs : List Rec) : Except Failure Nat := do
  let rs := reqIds recs
  match recs with
  | [] => throw { line := 0, seq := 0, ev := "", reason := "empty trace", violated := [] }
  | r0 :: rest =>
    if r0.ev != "init" then
      throw { line := 1, seq := r0.seq, ev := r0.ev, reason := "first record is not init", violated := [] }
    if !r0.post.lingering.isEmpty || r0.post.queues.any (fun q => !q.waiting.isEmpty || !q.executing.isEmpty) then
      throw { line := 1, seq := r0.seq, ev := r0.ev,
              reason := "init snapshot has requests; the checker starts from an empty queueSet", violated := [] }
    let v0 : View := {}
    let bad0 := snapProps v0 r0.post
    if !bad0.isEmpty then
      throw { line := 1, seq := r0.seq, ev := r0.ev, reason := (bad0.map (·.2)).head!,
              violated := bad0.map (·.1) }
    if r0.post.desired == 0 then
      throw { line := 1, seq := r0.seq, ev := r0.ev, reason := "desired is 0 (out of scope)", violated := [] }
    let mut s := initState r0.post
    let mut v := v0
    let mut line := 1
    for r in rest do
      line := line + 1
      let v' := viewStep v r
      -- the release_once violation is visible before the step
      let dup : Bool := match r.ev, r.req with
        | "timer_fire", some x => decide (v.relCount x ≥ 1)
        | "finish", some x => decide (v.relCount x ≥ 1)
        | _, _ => false
      let bad := snapProps v' r.post
      let viol := (if dup then ["release_once"] else []) ++ bad.map (·.1)
      if r.ev == "panic" then
        throw { line, seq := r.seq, ev := r.ev,
                reason := s!"panic record ({r.msg.getD "no message"}); the corrected model never panics",
                violated := viol ++ ["index_integrity"] }
      let a ← match actionOf s r with
        | .ok a => pure a
        | .error e => throw { line, seq := r.seq, ev := r.ev, reason := e, violated := viol }
      match apply rs true a s with
      | none =>
        let why := if dup then "the request was already released" else "precondition fails in the model"
        throw { line, seq := r.seq, ev := r.ev, reason := s!"event is not an enabled action: {why}",
                violated := viol }
      | some s' =>
        if let some e := compare rs s' r.post then
          let why := if bad.isEmpty then e else s!"{e}; {(bad.map (·.2)).head!}"
          throw { line, seq := r.seq, ev := r.ev, reason := why, violated := viol }
        if !bad.isEmpty then
          throw { line, seq := r.seq, ev := r.ev, reason := (bad.map (·.2)).head!, violated := viol }
        s := s'
        v := v'
    return line

def parseAll (text : String) : Except String (List Rec) := do
  let lines := (text.splitOn "\n").zipIdx.filter (fun (l, _) => !l.trimAscii.isEmpty)
  lines.mapM fun (l, i) =>
    match parseRec l with
    | .ok r => pure r
    | .error e => throw s!"line {i + 1}: {e}"

end ApfQueueSet.TraceCheck
