# LeanBatfish

LeanBatfish gives a formal semantics, in Lean 4, to the vendor-independent model that
[Batfish](https://github.com/batfish/batfish) builds from router configurations. Batfish
parses Cisco and Juniper configurations and exports its model as JSON; LeanBatfish reads
that JSON and gives it meaning, so that properties of a real network can be computed and
proved in Lean.

The semantics follows Batfish's own behavior. To check that it does, the simulator in this
repository runs a network to its converged data plane and answers the same questions
Batfish answers: the main routing tables (`routes`), the forwarding tables (`fibs`) and the
BGP tables (`bgpRib`). The answers are compared with Batfish's for the same network
(differential testing). On every network inside the modeled subset (connected, static and
aggregate routes, OSPF, and BGP with route reflection, communities, AS-path policies,
multipath, add-path and aggregation, on Cisco, Juniper and Arista), the answers match.

The library also gives the network a *dynamic* semantics, after Daggitt and Griffin. Each
router (a VRF of a device) holds routing tables and updates them from its neighbors'
current tables and its configuration (static routes, OSPF, BGP import and export
policies, ...). Routers update in any order, on information of any age, and peers outside
the network may announce anything. The forwarding tables computed from the routers'
states then change over time. Properties can be stated *at any time* (for every schedule
and every announcement from outside) or about the converged state. The state Batfish
converges to is a stable state of these dynamics on every network but one in the modeled
subset, and synchronous iteration of the dynamics reaches exactly Batfish's answers on
almost all of them.

For example, `networks/example/Properties.lean` proves about Batfish's example
network:

* in the converged state, `host1` reaches `host2`, and AS3 reaches `host1`, but `host1` cannot
  reach AS3's loopbacks;
* whatever the BGP peers outside the network announce, at any time, no router of AS2 ever
  holds a route more specific than `/24` for `host2`'s address (AS1's and AS3's export
  filters protect AS2);
* if AS1 itself misbehaves, a single announcement makes `as2border1` send `host2`'s traffic
  to AS1 (AS2 defines an inbound filter but never applies it).

The "at any time" result follows from a general theorem, proved once: a part of the network
whose originations, adjacencies and incoming policies pass a computable check only ever
holds routes for a given set of prefixes. The incoming policies are checked by an analysis
of routing policies that is proved sound against the policy interpreter.

## How it is organized

- `LeanBatfish` is the library: the IR types, the strict JSON decoder, and the semantics
  (routing policies, routing tables, OSPF, BGP, forwarding). `Theory/` formalizes routing
  dynamics in general (schedules, routing systems, stable states, invariants, data planes);
  `Model/` makes a snapshot such a system; `Reasoning/` holds what is proved about the
  semantics and the model.
- `LeanBatfishSim` is the simulator, an executable of the semantics, with the
  `lean-batfish-sim` command.
- `tests/` holds the unit tests (`lake test`).
- `networks/` holds test networks taken from Batfish's examples, tutorials and tests. Each
  network's directory also holds its Lean model (`Model.lean`, generated) and properties
  proved about it (`Properties.lean`).
- `tools/` has the Python scripts that drive Batfish and compare answers.
- `external/batfish` is a Git submodule: Batfish on our `lean-batfish` branch, which adds
  two things to upstream: static-route flags that the JSON export used to drop, and a
  `fibs` question that lists forwarding-table entries.

The decoder is strict. It understands a chosen subset of Batfish's model, and it rejects
any input that uses something outside that subset, naming the feature. A network is
therefore either simulated with the modeled semantics or refused; it is never simulated
as if an unmodeled feature were absent.

## Setup

You need Lean (via `elan`), Docker, Bazel (via `bazelisk`) and `uv`.

```sh
git submodule update --init
lake build                                   # library and simulator
lake test                                    # unit tests

uv venv .venv --python 3.12
uv pip install --python .venv/bin/python -r tools/requirements.txt

tools/batfish/build.sh                       # build Batfish into a Docker image
tools/batfish/run.sh                         # start it on ports 9996/9997
```

## Usage

Export Batfish's view of snapshots (its model, and its answers to the questions we
compare) to `data/batfish/`:

```sh
.venv/bin/python tools/export.py networks/example
.venv/bin/python tools/export.py --discover networks external/batfish/networks external/batfish/projects
```

Ask the simulator questions about an exported snapshot:

```sh
.lake/build/bin/lean-batfish-sim answer data/batfish/<snapshot> routes fibs bgpRib
```

Compare the simulator's answers with Batfish's on every exported snapshot:

```sh
.venv/bin/python tools/difftest.py [--verbose] [snapshot-substring ...]
```

Run the dynamic semantics instead of the simulator's engine (synchronous iteration to a fixed
point), or check that the state Batfish converges to is a stable state of the dynamics:

```sh
.venv/bin/python tools/difftest.py --dynamics
.venv/bin/python tools/difftest.py --stable
```

Generate the Lean models of the exported networks, then check their properties:

```sh
.venv/bin/python tools/model.py              # writes networks/<name>/Model.lean
lake build networks
```

A generated `Model.lean` is one command, `batfish_snapshot Networks.Example from
"data/batfish/..."`, which reads the export when the file is built and defines the snapshot,
its network (`network.system`, `network.dataPlane`) and its converged state. Proofs about a
concrete network evaluate the semantics with `native_decide`.

See which exported snapshots are inside the modeled subset, and why the others are not:

```sh
.venv/bin/python tools/scan.py --verbose
```
