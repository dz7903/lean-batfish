import LeanBatfish.Semantics.Routing.Static

/-!
# Forwarding tables

The FIB turns each forwarding route of the main RIB into forwarding actions, by resolving
its next hop through the RIB until it reaches a route out of an interface (Batfish's
`FibImpl`). A next-hop IP resolves through the longest matching route, and through each
of them if there are several (ECMP). When a route is reached through a next-hop IP and
leaves by an interface without a next-hop IP of its own, the packet is sent to the most
recent next-hop IP on the way (the *ARP IP*).

A next hop that does not resolve, or resolves through a route already on the path (a
loop), becomes a discard entry.
-/

namespace LeanBatfish

/-- What the FIB does with a packet (`FibAction`). -/
inductive FibAction
  /-- Send out of `iface`, to `arpIp` if given and otherwise to the destination itself. -/
  | forward (iface : String) (arpIp : Option Ip)
  | discard
  deriving DecidableEq, Hashable, Inhabited, Repr

/-- A FIB entry: a main-RIB route and one forwarding action it resolves to (`FibEntry`). -/
structure FibEntry where
  route : Route
  action : FibAction
  deriving DecidableEq, Inhabited, Repr

/-- `FibImpl.MAX_DEPTH`. -/
def fibMaxDepth : Nat := 10

/-- Whether `r` may resolve the next-hop IP of `route`: static routes may always resolve
through connected routes, non-recursive ones only through those; everything else must
pass the resolution policy. -/
def fibResolutionAllowed (c : Configuration) (v : Vrf) (route r : Route) : EvalM Bool :=
  if route.protocol == .static then
    if r.protocol == .connected then pure true
    else if !route.recursive then pure false
    else resolutionAllowed c v r
  else resolutionAllowed c v r

/-- The actions reached from `route` (`FibImpl.buildResolutionTree` and `collectEntries`).
`arpIp` is the last next-hop IP on the way, `seen` the networks on the path. -/
def resolveActions (c : Configuration) (v : Vrf) (rib : Rib) (route : Route)
    (arpIp : Option Ip) (seen : List Prefix) (depth : Nat) : EvalM (Array FibAction) :=
  if depth > fibMaxDepth then
    -- Batfish stops building the tree here and keeps the node as a leaf.
    match route.nextHop with
    | .iface name _ => pure #[.forward name none]
    | .discard => pure #[.discard]
    | .ip _ => throw "FIB resolution exceeded the maximum depth"
  else
    let seen := route.network :: seen
    match route.nextHop with
    | .iface name ip => pure #[.forward name (ip <|> arpIp)]
    | .discard => pure #[.discard]
    | .ip ip => do
      let lpm ← rib.longestPrefixMatch ip (fibResolutionAllowed c v route)
      match lpm[0]? with
      | none => pure #[.discard]
      | some first =>
        if seen.contains first.network then pure #[.discard]
        else
          let mut out := #[]
          for r in lpm do
            for a in ← resolveActions c v rib r (some ip) seen (depth + 1) do
              if !out.contains a then out := out.push a
          pure out
termination_by fibMaxDepth + 1 - depth

/-- The FIB of a VRF: an entry for each action of each forwarding route in the RIB. -/
def computeFib (c : Configuration) (v : Vrf) (rib : Rib) : EvalM (Array FibEntry) := do
  let mut out := #[]
  for r in rib.routes do
    if r.nonForwarding then continue
    for a in ← resolveActions c v rib r none [] 0 do
      out := out.push { route := r, action := a }
  return out

end LeanBatfish
