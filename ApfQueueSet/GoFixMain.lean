import ApfQueueSet.Synth

open ApfQueueSet.Synth

/-- `gofix strict|naive`: print `removeQueueIfEmptyLocked` with the guard
that `derive` computes from that reading of "empty". `strict` is the fix; `naive` must
reproduce the upstream function byte for byte (go/gen-fix.sh checks this). -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["strict"] => IO.print (goFunction (derive strictReading)); return 0
  | ["naive"] => IO.print (goFunction (derive naiveReading)); return 0
  | _ => IO.eprintln "usage: gofix strict|naive"; return 2
