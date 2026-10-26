"""Export Batfish's view of network snapshots for differential testing.

For each snapshot this asks a running Batfish service for the vendor-independent
model (`viModel`) and for the results of its own simulation (RIBs, sessions,
edges), and writes the raw answers as JSON under `data/batfish/<snapshot-id>/`.

Usage:
    .venv/bin/python tools/export.py SNAPSHOT_DIR [SNAPSHOT_DIR ...]
    .venv/bin/python tools/export.py --discover external/batfish

With `--discover`, every directory below the given roots that contains a
`configs/` folder is treated as a snapshot. The snapshot id is its path relative
to the Batfish checkout, or `lean-batfish/networks/<name>` for this repository's
networks.
"""

import argparse
import json
import logging
import shutil
import subprocess
import sys
import tempfile
import time
import traceback
from pathlib import Path

from pybatfish.client.session import Session

ROOT = Path(__file__).resolve().parent.parent
BATFISH_SRC = ROOT / "external" / "batfish"
OUT = ROOT / "data" / "batfish"
NETWORK = "lean-batfish-corpus"

# Questions whose answers we keep, by output file name.
QUESTIONS = {
    "initIssues": lambda q: q.initIssues(),
    "viModel": lambda q: q.viModel(),
    "layer3Edges": lambda q: q.layer3Edges(),
    "ospfEdges": lambda q: q.ospfEdges(),
    "bgpEdges": lambda q: q.bgpEdges(),
    "bgpSessionStatus": lambda q: q.bgpSessionStatus(),
    "routes": lambda q: q.routes(),
    "bgpRib": lambda q: q.bgpRib(),
    "fibs": lambda q: q.fibs(),
}


def batfish_version(bf: Session) -> dict:
    commit = subprocess.run(["git", "-C", str(BATFISH_SRC), "rev-parse", "HEAD"],
                            capture_output=True, text=True).stdout.strip()
    return {**bf.get_component_versions(), "source_commit": commit}


def snapshot_id(path: Path) -> str:
    """Snapshots from the Batfish checkout keep their path there; this repository's own
    networks are under `lean-batfish/`; anything else is named by its directory."""
    path = path.resolve()
    for base, prefix in ((BATFISH_SRC, ""), (ROOT, "lean-batfish/")):
        try:
            return prefix + str(path.relative_to(base.resolve()))
        except ValueError:
            pass
    return path.name


def discover(roots):
    found = []
    for root in roots:
        for configs in sorted(Path(root).rglob("configs")):
            if configs.is_dir() and "configs" not in configs.parent.parts:
                found.append(configs.parent)
    return found


def export(bf: Session, path: Path, force: bool) -> dict:
    sid = snapshot_id(path)
    out = OUT / sid
    if (out / "meta.json").exists() and not force:
        return json.loads((out / "meta.json").read_text())
    out.mkdir(parents=True, exist_ok=True)
    meta = {"snapshot": sid, "source": str(path), "answers": {}, "errors": {}}
    start = time.time()
    name = "s"
    try:
        # Upload the snapshot without the Lean modules that live next to it.
        with tempfile.TemporaryDirectory() as tmp:
            copy = Path(tmp) / path.name
            shutil.copytree(path, copy, ignore=shutil.ignore_patterns("*.lean"))
            bf.init_snapshot(str(copy), name=name, overwrite=True)
    except Exception as e:  # parse failures are data too
        meta["errors"]["init"] = "".join(traceback.format_exception_only(e)).strip()
    else:
        for qname, make in QUESTIONS.items():
            try:
                answer = dict(make(bf.q).answer(snapshot=name))
                (out / f"{qname}.json").write_text(json.dumps(answer, indent=1))
                meta["answers"][qname] = answer.get("status", "?")
            except Exception as e:
                meta["errors"][qname] = "".join(traceback.format_exception_only(e)).strip()
        try:
            bf.delete_snapshot(name)
        except Exception:
            pass
    # Side inputs the simulator reads, next to the answers.
    for side in ("external_bgp_announcements.json",):
        for candidate in (path / side, path / "batfish" / side):
            if candidate.exists():
                shutil.copy(candidate, out / side)
    meta["seconds"] = round(time.time() - start, 1)
    (out / "meta.json").write_text(json.dumps(meta, indent=1))
    return meta


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("paths", nargs="*", type=Path)
    ap.add_argument("--discover", nargs="*", type=Path, default=[])
    ap.add_argument("--host", default="localhost")
    ap.add_argument("--force", action="store_true", help="re-export existing snapshots")
    args = ap.parse_args()

    logging.disable(logging.WARNING)
    snapshots = list(args.paths) + discover(args.discover)
    if not snapshots:
        ap.error("no snapshots given")

    bf = Session(host=args.host)
    bf.set_network(NETWORK)
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "batfish-version.json").write_text(json.dumps(batfish_version(bf), indent=1))

    for i, path in enumerate(snapshots, 1):
        meta = export(bf, path, args.force)
        status = "ok" if not meta["errors"] else "errors: " + ", ".join(meta["errors"])
        print(f"[{i}/{len(snapshots)}] {meta['snapshot']} ({meta.get('seconds')}s) {status}",
              flush=True)


if __name__ == "__main__":
    sys.exit(main())
