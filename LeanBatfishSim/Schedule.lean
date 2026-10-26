import LeanBatfish.Semantics.Bgp.JavaHash

/-!
# The node schedule

Within a round of the main loop, Batfish does not update all nodes at once. It colors the
graph of nodes (an edge for each BGP session and OSPF adjacency) so that no two adjacent
nodes share a color, and updates the nodes color by color; nodes later in a round see what
earlier ones did in the same round (`NodeColoredSchedule` with JGraphT's
`SaturationDegreeColoring`, the DSatur heuristic).

The order matters for BGP: with the `ARRIVAL_ORDER` tie breaker the oldest of two equally
good eBGP routes wins. So the simulator reproduces the coloring exactly, including how
JGraphT breaks ties: its heap is filled from a Java `HashMap`, so the order of equal
vertices depends on Java's string hashing and `HashMap` iteration order.
-/

namespace LeanBatfishSim.Schedule

/-- Java's `String.hashCode`. -/
def javaStringHash (s : String) : UInt32 := LeanBatfish.JavaHash.string s

/-- The bucket of a key in a Java `HashMap` of the given capacity (`HashMap.hash`). -/
def javaBucket (hash : UInt32) (capacity : Nat) : Nat :=
  ((hash ^^^ (hash >>> 16)).toNat) % capacity

/-- The capacity of a default `HashMap` after `n` insertions: it doubles from 16 whenever
it holds more than three quarters of its capacity. -/
def javaHashMapCapacity (n : Nat) : Nat := Id.run do
  let mut cap := 16
  for _ in [0:64] do
    if n * 4 > cap * 3 then cap := cap * 2
  return cap

/-- The iteration order of a default Java `HashMap` whose string keys were inserted in the
given order: by bucket, and within a bucket by insertion order. (Buckets of eight or more
keys become trees in Java; with configuration names that is not expected to happen.) -/
def javaHashMapOrder (keys : Array String) : Array String :=
  let cap := javaHashMapCapacity keys.size
  let indexed := keys.mapIdx fun i k => (javaBucket (javaStringHash k) cap, i, k)
  (indexed.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)).map (·.2.2)

/-! ## DSatur, as JGraphT implements it -/

private structure St where
  /-- The heap, 1-indexed: `heap[0]` is unused. Entries are vertex indices. -/
  heap : Array Nat
  /-- The position of each vertex in the heap (0 when not in it). -/
  pos : Array Nat
  size : Nat
  saturation : Array Nat
  degree : Array Nat

/-- `DSaturComparator`: negative when `a` should come out of the heap first (higher
saturation, then higher remaining degree). -/
private def cmp (s : St) (a b : Nat) : Int :=
  if s.saturation[a]! > s.saturation[b]! then -1
  else if s.saturation[a]! < s.saturation[b]! then 1
  else if s.degree[a]! > s.degree[b]! then -1
  else if s.degree[a]! < s.degree[b]! then 1
  else 0

private def place (s : St) (k v : Nat) : St :=
  { s with heap := s.heap.set! k v, pos := s.pos.set! v k }

private def fixdown (s : St) (k0 : Nat) : St := Id.run do
  let h := s.heap[k0]!
  let mut s := s
  let mut k := k0
  for _ in [0:s.size + 1] do
    if 2 * k > s.size then break
    let mut j := 2 * k
    if j < s.size && cmp s s.heap[j]! s.heap[j + 1]! > 0 then j := j + 1
    if cmp s h s.heap[j]! ≤ 0 then break
    s := place s k s.heap[j]!
    k := j
  return place s k h

private def fixup (s : St) (k0 : Nat) : St := Id.run do
  let h := s.heap[k0]!
  let mut s := s
  let mut k := k0
  for _ in [0:s.size + 1] do
    if !(k > 1 && cmp s s.heap[k / 2]! h > 0) then break
    s := place s k s.heap[k / 2]!
    k := k / 2
  return place s k h

private def forceFixup (s : St) (k0 : Nat) : St := Id.run do
  let h := s.heap[k0]!
  let mut s := s
  let mut k := k0
  for _ in [0:s.size + 1] do
    if k ≤ 1 then break
    s := place s k s.heap[k / 2]!
    k := k / 2
  return place s k h

private def deleteMin (s : St) : St × Nat :=
  let result := s.heap[1]!
  let s := { s with pos := s.pos.set! result 0 }
  if s.size == 1 then ({ s with size := 0 }, result)
  else
    let s := place s 1 s.heap[s.size]!
    let s := { s with size := s.size - 1 }
    (fixdown s 1, result)

private def delete (s : St) (v : Nat) : St := (deleteMin (forceFixup s s.pos[v]!)).1

private def insert (s : St) (v : Nat) : St :=
  let s := { s with size := s.size + 1 }
  fixup (place s s.size v) s.size

/-- Color the graph with vertices `vertices` (in insertion order) and undirected edges
`edges` (pairs of vertex indices, in insertion order), and return the color classes in color
order, each as vertex names. -/
def colorClasses (vertices : Array String) (edges : Array (Nat × Nat)) : Array (Array String) :=
  Id.run do
  let n := vertices.size
  if n == 0 then return #[]
  -- Adjacency, in edge insertion order (`graph.edgesOf`).
  let mut adj : Array (Array Nat) := Array.replicate n #[]
  for (a, b) in edges do
    adj := adj.modify a (·.push b)
    adj := adj.modify b (·.push a)
  -- The heap is bulk-loaded in the iteration order of a `HashMap` keyed by vertex.
  let index (name : String) : Nat := (vertices.findIdx? (· == name)).getD 0
  let order := (javaHashMapOrder vertices).map index
  let mut s : St := {
    heap := #[0] ++ order, pos := Array.replicate n 0, size := n
    saturation := Array.replicate n 0, degree := adj.map (·.size) }
  for i in [0:n] do
    s := { s with pos := s.pos.set! order[i]! (i + 1) }
  for i' in [0:n / 2] do
    s := fixdown s (n / 2 - i')
  let mut colors : Array (Option Nat) := Array.replicate n none
  let mut adjColors : Array (Array Nat) := Array.replicate n #[]
  let mut maxColor := 0
  for _ in [0:n] do
    if s.size == 0 then break
    let (s', v) := deleteMin s
    s := s'
    let used := adjColors[v]!
    let c := (List.range (used.size + 1)).find? (!used.contains ·) |>.getD 0
    maxColor := max maxColor c
    colors := colors.set! v (some c)
    for u in adj[v]! do
      if colors[u]!.isSome then continue
      if adjColors[u]!.contains c then
        s := delete s u
        s := { s with degree := s.degree.modify u (· - 1) }
        s := insert s u
      else
        adjColors := adjColors.modify u (·.push c)
        s := { s with saturation := s.saturation.modify u (· + 1),
                      degree := s.degree.modify u (· - 1) }
        s := fixup s s.pos[u]!
  let mut classes : Array (Array String) := Array.replicate (maxColor + 1) #[]
  for v in [0:n] do
    if let some c := colors[v]! then classes := classes.modify c (·.push vertices[v]!)
  return classes.filter (!·.isEmpty)

/-- The schedule of a network: its nodes (sorted by name) colored over the edges between
distinct nodes (each pair once, sorted). -/
def nodeSchedule (nodes : Array String) (links : Array (String × String)) :
    Array (Array String) :=
  let vertices := nodes.qsort (· < ·)
  let pairs := links.filterMap fun (a, b) =>
    if a == b then none else some (if a < b then (a, b) else (b, a))
  let pairs := (pairs.qsort fun p q => p.1 < q.1 || (p.1 == q.1 && p.2 < q.2)).toList.eraseDups
  let index (name : String) : Option Nat := vertices.findIdx? (· == name)
  let edges := pairs.toArray.filterMap fun (a, b) => do pure (← index a, ← index b)
  colorClasses vertices edges

end LeanBatfishSim.Schedule
