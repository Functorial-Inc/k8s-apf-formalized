# /// script
# requires-python = ">=3.10"
# ///
"""Write mutated copies of conforming traces to traces/mutated/.

Every mutation breaks a trace in a way a correct checker must reject. Usage:

    uv run go/mutate.py [--src traces/corrected] [--out traces/mutated] [--per-kind 6]

The script names each output file <kind>--<source>.jsonl. MANIFEST.tsv lists,
for each, the mutated line (seq) and what the checker should object to. The
script picks sources deterministically: the scenario traces first, then seeds
in a fixed shuffle.
"""
import argparse
import copy
import json
import random
from pathlib import Path


def load(path):
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def dump(path, events):
    for i, e in enumerate(events):
        e["seq"] = i  # keep seq contiguous so that only the content is wrong
    path.write_text("".join(json.dumps(e, separators=(",", ":")) + "\n" for e in events))


def busy(q, post):
    """True if the queue has waiting, executing or lingering requests, or seats in use."""
    return bool(q["waiting"] or q["executing"] or q["seatsInUse"] or any(l["queue"] == q["id"] for l in post["lingering"]))


def drop_timer_fire(ev):
    # The dropped timer_fire needs a later event, so that the later snapshots
    # disagree with the model.
    for i, e in enumerate(ev[:-1]):
        if e["ev"] == "timer_fire":
            out = ev[:i] + ev[i + 1:]
            return out, e["seq"], "a lingering request is never released: later snapshots show its seats gone, or it stays lingering forever"
    return None


def duplicate_timer_fire(ev):
    for i, e in enumerate(ev):
        if e["ev"] == "timer_fire":
            out = ev[: i + 1] + [copy.deepcopy(e)] + ev[i + 1:]
            return out, e["seq"], "release_once: the second timer_fire has no lingering request to release"
    return None


def early_queue_removal(ev):
    for i, e in enumerate(ev):
        post = e["post"]
        if e["ev"] in ("init", "panic") or len(post["queues"]) < 2:
            continue
        for k, q in enumerate(post["queues"]):
            if busy(q, post):
                out = copy.deepcopy(ev)
                del out[i]["post"]["queues"][k]
                return out, e["seq"], f"queue {q['id']} leaves the slice while it still has requests: safe_retirement, and the model keeps it in the slice"
    return None


def change_seats_in_use(ev):
    for i, e in enumerate(ev):
        post = e["post"]
        if e["ev"] in ("init", "panic"):
            continue
        for k, q in enumerate(post["queues"]):
            if q["seatsInUse"] > 0:
                out = copy.deepcopy(ev)
                out[i]["post"]["queues"][k]["seatsInUse"] += 1
                return out, e["seq"], f"conservation: queue {q['id']} claims {q['seatsInUse'] + 1} seats but its reservations sum to {q['seatsInUse']}"
    return None


def swap_index(ev):
    for i, e in enumerate(ev):
        post = e["post"]
        if e["ev"] in ("init", "panic") or len(post["queues"]) < 2:
            continue
        out = copy.deepcopy(ev)
        a, b = out[i]["post"]["queues"][0], out[i]["post"]["queues"][1]
        a["index"], b["index"] = b["index"], a["index"]
        return out, e["seq"], f"index of queues {a['id']} and {b['id']} swapped: the indexes are still a permutation, so only the comparison with the model's predicted idx catches it"
    return None


MUTATIONS = {
    "drop-timer-fire": drop_timer_fire,
    "duplicate-timer-fire": duplicate_timer_fire,
    "early-queue-removal": early_queue_removal,
    "change-seatsInUse": change_seats_in_use,
    "swap-index": swap_index,
}


def main():
    here = Path(__file__).resolve().parent
    ap = argparse.ArgumentParser()
    ap.add_argument("--src", default=str(here.parent / "traces" / "corrected"))
    ap.add_argument("--out", default=str(here.parent / "traces" / "mutated"))
    ap.add_argument("--per-kind", type=int, default=6)
    args = ap.parse_args()
    src, out = Path(args.src), Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    for old in out.glob("*.jsonl"):
        old.unlink()
    scenarios = sorted(p for p in src.glob("*.jsonl") if not p.name.startswith("seed-"))
    seeds = sorted(src.glob("seed-*.jsonl"))
    random.Random(0).shuffle(seeds)
    sources = scenarios + seeds
    rows = []
    for kind, fn in MUTATIONS.items():
        n = 0
        for p in sources:
            if n >= args.per_kind:
                break
            ev = load(p)
            if ev and ev[-1]["ev"] == "panic":
                continue  # the source must be a conforming trace
            res = fn(ev)
            if res is None:
                continue
            mutated, seq, why = res
            name = f"{kind}--{p.stem}.jsonl"
            dump(out / name, mutated)
            rows.append((name, kind, p.name, seq, why))
            n += 1
    with open(out / "MANIFEST.tsv", "w") as f:
        f.write("file\tkind\tsource\tmutated_seq\twhy_it_must_be_rejected\n")
        for r in rows:
            f.write("\t".join(map(str, r)) + "\n")
    print(f"wrote {len(rows)} mutated traces to {out}")


if __name__ == "__main__":
    main()
