"""Compare the simulator's answers with Batfish's, question by question.

For each exported snapshot (see `export.py`), runs `lean-batfish-sim answer` on the
snapshot's `viModel.json` and compares each answer with the one Batfish gave. Rows are
compared as multisets, since neither side promises an order.

Usage:
    lake build && .venv/bin/python tools/difftest.py [--verbose] [SNAPSHOT_SUBSTRING ...]

Writes `data/difftest.json` and prints one line per snapshot.
"""

import argparse
import json
import subprocess
from collections import Counter
from pathlib import Path

from common import ROOT, export_id, exports
from scan import side_inputs

SIM = ROOT / ".lake" / "build" / "bin" / "lean-batfish-sim"

QUESTIONS = ["routes", "fibs", "bgpRib", "ipsecSessionStatus", "ipsecEdges"]


def rows(answer: dict) -> Counter:
    table = answer["answerElements"][0]
    return Counter(json.dumps(r, sort_keys=True) for r in table.get("rows", []))


def compare(expected: Counter, actual: Counter) -> dict:
    missing, extra = expected - actual, actual - expected
    return {
        "match": not missing and not extra,
        "rows": sum(expected.values()),
        "missing": sorted(missing.elements()),
        "extra": sorted(extra.elements()),
    }


def check(snapshot: Path, dynamics: bool = False) -> dict:
    sid = export_id(snapshot)
    meta = json.loads((snapshot / "meta.json").read_text())
    result = {"snapshot": sid, "questions": {}}
    if meta["errors"]:
        result["status"] = "batfish errors: " + ", ".join(meta["errors"])
        return result
    extras = side_inputs(ROOT / meta["source"])
    if extras:
        result["status"] = "side inputs: " + ", ".join(extras)
        return result
    qs = [q for q in QUESTIONS if (snapshot / f"{q}.json").exists()]
    engine = ["--dynamics"] if dynamics else []
    out = subprocess.run([SIM, "answer", *engine, str(snapshot), *qs], capture_output=True, text=True)
    try:
        answers = json.loads(out.stdout)
    except json.JSONDecodeError:
        result["status"] = "crashed: " + (out.stderr or out.stdout)[:200]
        return result
    if "rejected" in answers:
        result["status"] = "rejected: " + answers["rejected"]
        return result
    if "failed" in answers:
        result["status"] = "failed: " + answers["failed"]
        return result
    for q in qs:
        expected = rows(json.loads((snapshot / f"{q}.json").read_text()))
        result["questions"][q] = compare(expected, rows(answers[q]))
    ok = all(c["match"] for c in result["questions"].values())
    result["status"] = "match" if ok else "differs"
    return result


def check_stable(snapshot: Path) -> dict:
    """Whether the simulator's converged state is a stable state of the declarative dynamics."""
    sid = export_id(snapshot)
    meta = json.loads((snapshot / "meta.json").read_text())
    if meta["errors"]:
        return {"snapshot": sid, "status": "batfish errors"}
    if side_inputs(ROOT / meta["source"]):
        return {"snapshot": sid, "status": "side inputs"}
    out = subprocess.run([SIM, "check-stable", str(snapshot)], capture_output=True, text=True)
    try:
        answer = json.loads(out.stdout)
    except json.JSONDecodeError:
        return {"snapshot": sid, "status": "crashed: " + (out.stderr or out.stdout)[:200]}
    for key in ("rejected", "failed"):
        if key in answer:
            return {"snapshot": sid, "status": f"{key}: {answer[key]}"}
    if answer["stable"]:
        return {"snapshot": sid, "status": "stable"}
    where = "; ".join(f"{u['node']}/{u['vrf']}: {','.join(u['tables'])}" for u in answer["unstable"])
    return {"snapshot": sid, "status": "unstable: " + where}


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("filters", nargs="*", help="only snapshots whose id contains one of these")
    ap.add_argument("--verbose", action="store_true", help="print differing rows")
    ap.add_argument("--stable", action="store_true",
                    help="instead of comparing answers, check that the simulator's converged state "
                         "is a stable state of the declarative dynamics")
    ap.add_argument("--dynamics", action="store_true",
                    help="answer from the declarative dynamics (LeanBatfish.Model) run to a fixed "
                         "point, instead of the simulator's engine")
    args = ap.parse_args()

    snapshots = exports()
    if args.filters:
        snapshots = [s for s in snapshots if any(f in str(s) for f in args.filters)]
    if args.stable:
        results = [check_stable(s) for s in snapshots]
        for r in results:
            print(f"{r['status'][:100]:12.100}  {r['snapshot']}")
        counts = Counter(r["status"].split(":")[0] for r in results)
        print("\n" + ", ".join(f"{n} {s}" for s, n in counts.most_common()))
        return
    results = [check(s, args.dynamics) for s in snapshots]
    out = "difftest-dynamics.json" if args.dynamics else "difftest.json"
    (ROOT / "data" / out).write_text(json.dumps(results, indent=1))

    for r in results:
        detail = ""
        if r["questions"]:
            detail = "  " + "  ".join(
                f"{q}: {'ok' if c['match'] else f'-{len(c['missing'])} +{len(c['extra'])}'}"
                f" ({c['rows']} rows)" for q, c in r["questions"].items())
        status = r["status"] if r["status"] in ("match", "differs") else r["status"][:100]
        print(f"{status:8.100}  {r['snapshot']}{detail}")
        if args.verbose and r["status"] == "differs":
            for q, c in r["questions"].items():
                for row in c["missing"][:5]:
                    print(f"    {q} missing: {row}")
                for row in c["extra"][:5]:
                    print(f"    {q} extra:   {row}")

    counts = Counter(r["status"].split(":")[0] for r in results)
    print("\n" + ", ".join(f"{n} {s}" for s, n in counts.most_common()))


if __name__ == "__main__":
    main()
