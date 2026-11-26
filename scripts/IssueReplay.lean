import ApfQueueSet.Mirror
/-! Prints the issue #144077 execution (`Mirror.issueActions`) and the
wrong-queue execution (`Mirror.wrongQueueActions`), both from
`Mirror.issueInit`, step by step in both mirror models. The final states are
the ones `Mirror.issue_144077_affected` / `issue_144077_corrected` pin down
in the kernel; this file only prints them.
Run: `lake env lean --run scripts/IssueReplay.lean` -/
open ApfQueueSet.Mirror

def showPhase : Phase → String
  | .fresh => "fresh" | .waiting => "waiting" | .executing => "executing"
  | .lingering => "lingering" | .released => "released"

def showAction : Action Nat Nat → String
  | .reconfigure n f => s!"reconfigure(n={n}, fresh={f})"
  | .arrive r q w l => s!"arrive(r={r}, q={q}, width={w}, lingers={l})"
  | .dispatch r => s!"dispatch(r={r})"
  | .finish r => s!"finish(r={r})"
  | .timerFire r => s!"timerFire(r={r})"

def showState (s : St Nat Nat) : String :=
  let qs := s.slice.map fun q => s!"q{q}(idx={s.idx q}, seats={s.seats q})"
  let rs := [0, 1, 2, 3].map fun r => s!"r{r}:{showPhase (s.phase r)}@q{s.rq r}"
  s!"slice={qs} desired={s.desired} totSeats={s.tot} reqs={rs} panicked={s.panicked} discarded(strict)={s.discarded} discarded(naive)={s.discardedNaive}"

def replay (title : String) (rs : List Nat) (c : Bool) (as : List (Action Nat Nat)) : IO Unit := do
  IO.println s!"== {title}, {if c then "CORRECTED" else "AFFECTED"} model"
  let mut s := issueInit
  IO.println s!"  init: {showState s}"
  for a in as do
    match apply rs c a s with
    | none => IO.println s!"  {showAction a}: NOT ENABLED"; return
    | some s' =>
      IO.println s!"  {showAction a}: {showState s'}"
      s := s'

def main : IO Unit := do
  replay "issue #144077 sequence (Mirror.issueActions)" [0, 1] false issueActions
  replay "issue #144077 sequence (Mirror.issueActions)" [0, 1] true issueActions
  replay "wrong-queue sequence (Mirror.wrongQueueActions)" [0, 1, 2, 3] false wrongQueueActions
  replay "wrong-queue sequence (Mirror.wrongQueueActions)" [0, 1, 2, 3] true wrongQueueActions
