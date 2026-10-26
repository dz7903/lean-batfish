"""Summarize which parts of Batfish's IR appear in the exported corpus.

Walks every `data/batfish/**/viModel.json` and reports, for each kind of IR object,
the fields it has and how many snapshots use each field, with a few example values.
An object's kind is its `class` tag if it has one, otherwise the field path leading to
it (with name-keyed maps collapsed to `*`).

Usage:
    .venv/bin/python tools/survey.py [--json OUT] [KIND_SUBSTRING ...]
"""

import argparse
import json
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / "data" / "batfish"

# Fields whose JSON value is an object keyed by names (hostnames, VRFs, policies, IPs, ...).
MAP_FIELDS = {
    "nodes", "vrfs", "interfaces", "routingPolicies", "ipAccessLists", "ip6AccessLists",
    "routeFilterLists", "route6FilterLists", "asPathAccessLists", "asPathExprs",
    "asPathMatchExprs", "communityMatchExprs", "communitySetExprs", "communitySetMatchExprs",
    "communitySets", "ipSpaces", "ipSpaceMetadata", "neighbors", "dynamicNeighbors",
    "interfaceNeighbors", "ospfProcesses", "eigrpProcesses", "areas", "aggregates",
    "addressMetadata", "zones", "trackingGroups", "packetPolicies", "mlags",
    "generatedReferenceBooks", "ikePhase1Keys", "ikePhase1Policies", "ikePhase1Proposals",
    "ipsecPeerConfigs", "ipsecPhase2Policies", "ipsecPhase2Proposals", "layer2Vnis",
    "layer3Vnis", "hsrpGroups", "vrrpGroups", "isisProcesses", "tracks", "ospfNeighborConfigs",
    "ospfNeighbors", "dhcpRelayAddresses", "eigrpNeighbors", "routeFilterListsByName",
    "vrfLeakConfigs", "bgpVrfLeakConfigs", "ospfInterfaceSettings", "ospfAreaSummaries",
    "summaries", "interfacesByName", "ipsecStaticPeerConfigs", "localInterfaces",
}


def kind_of(obj, path):
    cls = obj.get("class")
    if isinstance(cls, str):
        return cls.replace("org.batfish.datamodel.", "")
    return ".".join(path) or "<root>"


def walk(value, path, stats, snapshot):
    if isinstance(value, dict):
        kind = kind_of(value, path)
        entry = stats[kind]
        entry["snapshots"].add(snapshot)
        entry["count"] += 1
        base = [kind] if "class" in value else path
        for key, sub in value.items():
            f = entry["fields"][key]
            f["snapshots"].add(snapshot)
            f["count"] += 1
            if len(f["examples"]) < 4 and not isinstance(sub, (dict, list)):
                if sub not in f["examples"]:
                    f["examples"].append(sub)
            if key in MAP_FIELDS and isinstance(sub, dict):
                for name, item in sub.items():
                    walk(item, base + [key, "*"], stats, snapshot)
            else:
                walk(sub, base + [key], stats, snapshot)
    elif isinstance(value, list):
        for item in value:
            walk(item, path + ["[]"], stats, snapshot)


def new_entry():
    field = lambda: {"snapshots": set(), "count": 0, "examples": []}
    return {"snapshots": set(), "count": 0, "fields": defaultdict(field)}


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("kinds", nargs="*", help="only show kinds containing one of these")
    ap.add_argument("--json", type=Path, help="also write the full survey as JSON")
    args = ap.parse_args()

    stats = defaultdict(new_entry)
    files = sorted(DATA.rglob("viModel.json"))
    for f in files:
        snapshot = str(f.parent.relative_to(DATA))
        answer = json.loads(f.read_text())
        for elem in answer.get("answerElements", []):
            for host, config in elem.get("nodes", {}).items():
                walk(config, ["Configuration"], stats, snapshot)

    print(f"{len(files)} snapshots, {len(stats)} kinds of objects\n")
    out = {}
    for kind in sorted(stats, key=lambda k: -len(stats[k]["snapshots"])):
        if args.kinds and not any(s in kind for s in args.kinds):
            continue
        e = stats[kind]
        print(f"{kind}  [{len(e['snapshots'])} snapshots, {e['count']} objects]")
        out[kind] = {"snapshots": len(e["snapshots"]), "fields": {}}
        for name in sorted(e["fields"], key=lambda n: -len(e["fields"][n]["snapshots"])):
            f = e["fields"][name]
            ex = ", ".join(json.dumps(x) for x in f["examples"])
            print(f"    {name:40} {len(f['snapshots']):4}  {ex[:90]}")
            out[kind]["fields"][name] = {"snapshots": len(f["snapshots"]), "examples": f["examples"]}
    if args.json:
        args.json.write_text(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
