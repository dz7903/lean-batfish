"""Where Batfish's exports live.

This repository's networks keep their export next to the snapshot, in
`networks/<name>/export/`, tracked in git, so that their Lean models (`Model.lean`) read it
locally. Other snapshots (Batfish's own tests and examples) are exported to
`data/batfish/<snapshot-id>/`, which is not tracked.
"""

from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BATFISH_SRC = ROOT / "external" / "batfish"
NETWORKS = ROOT / "networks"
DATA = ROOT / "data" / "batfish"
# The folder of a network that holds its export. Not `batfish/`, which Batfish reads as part
# of the snapshot.
EXPORT = "export"


def is_network(source: Path) -> bool:
    """Whether a snapshot directory is one of this repository's networks."""
    return source.resolve().parent == NETWORKS.resolve()


def snapshot_id(source: Path) -> str:
    """`networks/<name>` for this repository's networks; for the Batfish checkout, the path
    in it; otherwise the directory's name."""
    source = source.resolve()
    for base in (ROOT, BATFISH_SRC):
        try:
            rel = source.relative_to(base.resolve())
        except ValueError:
            continue
        if base == ROOT and rel.parts[:1] != ("networks",):
            continue
        return str(rel)
    return source.name


def export_dir(source: Path) -> Path:
    """Where the export of a snapshot goes."""
    if is_network(source):
        return source / EXPORT
    return DATA / snapshot_id(source)


def exports() -> list[Path]:
    """Every exported snapshot: this repository's networks first, then the rest."""
    local = sorted(p.parent for p in NETWORKS.glob(f"*/{EXPORT}/viModel.json"))
    other = sorted(p.parent for p in DATA.rglob("viModel.json")) if DATA.exists() else []
    return local + other


def export_id(export: Path) -> str:
    """The snapshot id of an export directory."""
    export = export.resolve()
    if export.name == EXPORT and export.parent.parent == NETWORKS.resolve():
        return str(export.parent.relative_to(ROOT))
    return str(export.relative_to(DATA.resolve()))
