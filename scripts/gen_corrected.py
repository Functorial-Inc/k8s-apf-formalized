"""Generate the derived Veil files from ApfQueueSet/Affected.lean.

Affected.lean is the single source of the model. This script derives:

* Corrected.lean   : + the `seatsInUse q = 0` guard; tail = scripts/corrected_tail.lean
                     (hand proofs + #check_invariants; no model checking).
* CorrectedMC.lean : + the guard; the `assume` in `release` removed; extra
                     checked clauses (scripts/mc_clauses.lean); tail =
                     scripts/corrected_mc_tail.lean (exhaustive #model_check runs).
* AffectedMC.lean  : the `assume` removed; the same extra clauses; tail =
                     scripts/affected_mc_tail.lean (the counterexample run).

Every derived file is Affected.lean with exactly these textual edits, plus the
module name and header prose. `uv run scripts/gen_corrected.py` regenerates;
`--check` verifies the files on disk are up to date (`make check-parallel`).
"""
import pathlib
import sys

root = pathlib.Path(__file__).resolve().parent.parent
src = (root / "ApfQueueSet/Affected.lean").read_text()
scripts = root / "scripts"

OLD_GUARD = "     (∀ x, ¬ (rq x = q ∧ phase x = executing)) then"
NEW_GUARD = "     (∀ x, ¬ (rq x = q ∧ phase x = executing)) ∧\n     seatsInUse q = 0 then"
ASSUME_START = "  -- TRUSTED ASSUMPTION (`conservation_fo`)"
ASSUME_END = "    (width r : Int) + (width x : Int) ≤ seatsInUse (rq r)\n"
TAIL_START = "-- ## Verification commands"
HEADER_OLD = ("This file is the model WITHOUT the\n`seatsInUse = 0` conjunct in `removeQueueIfEmpty`, "
              "i.e. the base of\nkubernetes/kubernetes PR #144078.")
GENERATED = ("`Corrected.lean`, `CorrectedMC.lean` and `AffectedMC.lean` are generated from\n"
             "this file by `scripts/gen_corrected.py` (see that script and `proof-status.md`\n"
             "for exactly what each changes).")


def edit(s, *, name, corrected, mc, title, header, tail_file):
    for needle in (OLD_GUARD, ASSUME_START, ASSUME_END, TAIL_START, HEADER_OLD, GENERATED,
                   "veil module ApfAffected", "#gen_spec\n"):
        assert needle in s, needle
    s = s.replace("veil module ApfAffected", f"veil module {name}")
    s = s.replace("# APF `queueSet` queue lifecycle: AFFECTED model",
                  f"# APF `queueSet` queue lifecycle: {title}")
    s = s.replace(HEADER_OLD, header)
    s = s.replace(GENERATED, "GENERATED from `Affected.lean` by `scripts/gen_corrected.py`. Do not edit.")
    if corrected:
        s = s.replace(OLD_GUARD, NEW_GUARD)
    if mc:
        i = s.index(ASSUME_START)
        j = s.index(ASSUME_END) + len(ASSUME_END)
        s = s[:i] + s[j:]
        clauses = (scripts / "mc_clauses.lean").read_text()
        s = s.replace("#gen_spec\n", clauses + "\n#gen_spec\n", 1)
        decl = (scripts / "mc_decls.lean").read_text()
        s = s.replace("#gen_state\n", decl + "\n#gen_state\n", 1)
    s = s[: s.index(TAIL_START)] + (scripts / tail_file).read_text()
    return s


outputs = {
    "ApfQueueSet/Corrected.lean": edit(
        src, name="ApfCorrected", corrected=True, mc=False, title="CORRECTED model",
        header=("This file is the model WITH the\n`seatsInUse = 0` conjunct in `removeQueueIfEmpty`, "
                "i.e. kubernetes/kubernetes\nPR #144078. Unbounded verification (`#check_invariants`)."),
        tail_file="corrected_tail.lean"),
    "ApfQueueSet/CorrectedMC.lean": edit(
        src, name="ApfCorrectedMC", corrected=True, mc=True, title="CORRECTED model, model checking",
        header=("This file is the CORRECTED model (with the\n`seatsInUse = 0` conjunct, PR #144078) "
                "for explicit-state model checking:\nno `assume` in `release`, and extra checked clauses "
                "including the sum form\nof `conservation`."),
        tail_file="corrected_mc_tail.lean"),
    "ApfQueueSet/AffectedMC.lean": edit(
        src, name="ApfAffectedMC", corrected=False, mc=True, title="AFFECTED model, model checking",
        header=("This file is the AFFECTED model (without the\n`seatsInUse = 0` conjunct) for "
                "explicit-state model checking: no `assume`\nin `release`, and extra checked clauses "
                "including the sum form of\n`conservation`."),
        tail_file="affected_mc_tail.lean"),
}

if "--check" in sys.argv:
    stale = [p for p, s in outputs.items() if (root / p).read_text() != s]
    if stale:
        sys.exit("out of date (run `uv run scripts/gen_corrected.py`): " + ", ".join(stale))
    print("Corrected.lean, CorrectedMC.lean, AffectedMC.lean == gen_corrected(Affected.lean)")
else:
    for p, s in outputs.items():
        (root / p).write_text(s)
