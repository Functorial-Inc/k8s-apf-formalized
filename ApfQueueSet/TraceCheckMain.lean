import ApfQueueSet.TraceCheck

open ApfQueueSet.TraceCheck

/-- `tracecheck FILE...`: replay each JSONL trace against the corrected model.
Prints one line per file, `OK <file> (<n> records)` or
`FAIL <file>: line <n> (seq <s>, ev <e>): <reason> [violates: <properties>]`.
Exits 0 if every file conforms, 1 otherwise, 2 on usage or I/O errors. -/
def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: tracecheck FILE.jsonl..."
    return 2
  let mut allOk := true
  let mut nOk := 0
  let mut nFail := 0
  for path in args do
    let text ← try IO.FS.readFile path catch e => do
      IO.eprintln s!"tracecheck: cannot read {path}: {e}"; return 2
    match parseAll text with
    | .error e =>
      IO.println s!"FAIL {path}: malformed trace: {e} [violates: none (malformed)]"
      allOk := false; nFail := nFail + 1
    | .ok recs =>
      match check recs with
      | .ok n => IO.println s!"OK {path} ({n} records)"; nOk := nOk + 1
      | .error f =>
        IO.println s!"FAIL {path}: {f.render}"
        allOk := false; nFail := nFail + 1
  if args.length > 1 then
    IO.println s!"summary: {nOk} conform, {nFail} do not, of {args.length}"
  return if allOk then 0 else 1
