"""Check which exported snapshots fall inside the modeled subset.

Runs the strict decoder (`lean-batfish-sim decode`) on every exported `viModel.json` and
also rejects snapshots with side inputs that neither the simulator nor the `viModel` and
adjacency answers account for.

Usage:
    lake build && .venv/bin/python tools/scan.py [--verbose]

Writes `data/scan.json` and prints a summary.
"""

import argparse
import json
import re
import subprocess
from collections import Counter
from pathlib import Path

from common import EXPORT, ROOT, export_id, exports
SIM = ROOT / ".lake" / "build" / "bin" / "lean-batfish-sim"

# Snapshot entries that only carry device configurations, or are not read by Batfish.
CONFIG_DIRS = {"configs", "hosts", "iptables"}
# Inputs the simulator reads (external announcements), or that reach Batfish's data plane
# only through what we already read: the vendor-independent model (interface blacklists
# and runtime data deactivate interfaces; ISP models and cloud configurations become
# nodes) and the adjacencies (layer-1 topology).
MODELED_INPUTS = {"external_bgp_announcements.json", "interface_blacklist", "runtime_data.json",
                  "layer1_topology.json", "isp_config.json", "aws_configs", "azure_configs"}
NOT_INPUTS = {"README.md", "BUILD.bazel", "BUILD", ".gitignore", EXPORT}
# Lean modules about a network (`Model.lean`, `Properties.lean`) live next to its snapshot.
NOT_INPUT_SUFFIXES = (".png", ".jpg", ".svg", ".lean")


def side_inputs(source: Path):
    """Snapshot inputs besides device configurations (`batfish/` holds more of them)."""
    found = []
    for p in source.iterdir():
        if (p.name in CONFIG_DIRS or p.name in NOT_INPUTS or p.name in MODELED_INPUTS
                or p.name.startswith(".") or p.name.endswith(NOT_INPUT_SUFFIXES)):
            continue
        if p.name == "batfish" and p.is_dir():
            found += ["batfish/" + q.name for q in p.iterdir()
                      if q.name not in NOT_INPUTS and q.name not in MODELED_INPUTS]
        else:
            found.append(p.name)
    return sorted(found)


def family(formats):
    cisco = any(f.startswith("CISCO") for f in formats)
    juniper = any("JUNIPER" in f for f in formats)
    if cisco and juniper:
        return "cisco+juniper"
    return "cisco" if cisco else "juniper" if juniper else "other"


def reason_key(reason: str) -> str:
    """Collapse a rejection message to the feature it names."""
    m = re.search(r": (.*?) (?:is|are) not modeled", reason)
    if m:
        return m.group(1)
    if "field is not modeled" in reason:
        return "unknown field " + reason.split(":")[0].split(".")[-1]
    return reason[:80]


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args()

    files = [e / "viModel.json" for e in exports()]
    out = subprocess.run([SIM, "decode", *map(str, files)], capture_output=True, text=True).stdout
    decoded = dict(line.split("\t", 1) for line in out.splitlines())

    results = []
    for f in files:
        sid = export_id(f.parent)
        meta = json.loads((f.parent / "meta.json").read_text())
        nodes = json.loads(f.read_text())["answerElements"][0]["nodes"]
        formats = sorted({n["configurationFormat"] for n in nodes.values()})
        bgp = any(v.get("bgpProcess") for n in nodes.values() for v in n.get("vrfs", {}).values())
        ospf = any(v.get("ospfProcesses") for n in nodes.values() for v in n.get("vrfs", {}).values())
        verdict = decoded.get(str(f), "missing")
        extras = side_inputs(ROOT / meta["source"])
        if verdict.startswith("ok") and extras:
            verdict = "unsupported: side inputs are not modeled (" + ", ".join(extras) + ")"
        if verdict.startswith("ok") and meta["errors"]:
            verdict = "batfish: " + ", ".join(meta["errors"])
        results.append({
            "snapshot": sid, "formats": formats, "family": family(formats),
            "bgp": bgp, "ospf": ospf, "accepted": verdict.startswith("ok"), "verdict": verdict,
        })

    (ROOT / "data" / "scan.json").write_text(json.dumps(results, indent=1))

    total = Counter((r["family"], r["bgp"]) for r in results)
    ok = Counter((r["family"], r["bgp"]) for r in results if r["accepted"])
    print(f"{sum(ok.values())} of {len(results)} snapshots are inside the modeled subset\n")
    print(f"{'vendors':16} {'BGP':5} {'accepted':>9}")
    for key in sorted(total):
        print(f"{key[0]:16} {'yes' if key[1] else 'no':5} {ok[key]:>4} / {total[key]}")
    reasons = Counter(reason_key(r["verdict"]) for r in results if not r["accepted"])
    print("\nRejections by feature:")
    for reason, n in reasons.most_common():
        print(f"  {n:3}  {reason}")
    if args.verbose:
        print()
        for r in results:
            print(("OK  " if r["accepted"] else "NO  ") + r["snapshot"] + "  " +
                  ("" if r["accepted"] else r["verdict"][:140]))


if __name__ == "__main__":
    main()
