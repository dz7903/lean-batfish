import LeanBatfish.Model.Router
import LeanBatfish.Semantics.Forwarding.Acl
import LeanBatfish.Semantics.Forwarding.Fib
import LeanBatfish.Semantics.Ipsec

/-!
# Forwarding packets

How a router forwards a packet, from its main RIB and the IPsec sessions it has up.

**Packets.** Only addresses are modeled: forwarding is by destination, and IPsec reads the
source and destination. A packet is a plain IP header, or a packet wrapped by a tunnel in
an outer header: by GRE, which anyone on the way can read, or by IPsec, which protects it
with the negotiated proposal.

**A router** accepts a packet addressed to it; if the packet is wrapped and the router is
the far end of its tunnel, it unwraps it and forwards what was inside instead. Otherwise
it looks up the outer destination in its FIB, computed from its main RIB as Batfish does,
and for each action:

* out of a tunnel interface: wrap the packet and forward the result — by GRE for a GRE
  tunnel, by IPsec for the tunnel's peer if the interface is an IPsec tunnel (a GRE tunnel
  with IPsec protection does both, IPsec outside). If the IPsec session is down, or did not
  negotiate, drop it: a packet never leaves by a tunnel interface unwrapped;
* out of an interface with a crypto map: if the first crypto-map entry whose ACL permits
  the packet has its session up, wrap the packet for that peer and forward the result;
  drop it if the session is down; send it unchanged if no entry permits it;
* out of any other interface: send it to the router on the link that owns the address it
  is sent to, or out of the network if no modeled router owns it.

Wrapping and unwrapping happen inside one router, before the packet leaves it, so a hop
always carries the packet as it is on the wire.
-/

namespace LeanBatfish.Model

/-- A packet, as forwarding and IPsec see it. -/
inductive Packet
  /-- A plain IP packet from `src` to `dst`. -/
  | ip (src dst : Ip)
  /-- `inner`, wrapped by GRE in an outer header from `src` to `dst`. -/
  | gre (src dst : Ip) (inner : Packet)
  /-- `inner`, protected by IPsec with `proposal`, in an outer header from `src` to `dst`. -/
  | ipsec (src dst : Ip) (proposal : IpsecPhase2Proposal) (inner : Packet)
  deriving DecidableEq, Hashable, Inhabited, Repr

namespace Packet

/-- The source of the outer header. -/
def src : Packet → Ip
  | .ip s _ | .gre s _ _ | .ipsec s _ _ _ => s

/-- The destination of the outer header: where the packet is routed to. -/
def dst : Packet → Ip
  | .ip _ d | .gre _ d _ | .ipsec _ d _ _ => d

end Packet

/-- What a router does with a packet, naming routers by index. -/
inductive Out
  /-- Send packet `p` to router `router`. -/
  | send (router : Nat) (p : Packet)
  | accept
  | drop
  | exit
  deriving DecidableEq, Repr

/-- How deeply a router may wrap or unwrap one packet. -/
def wrapFuel : Nat := 8

namespace Router

/-- Whether `ip` is an address of an active interface of the router. -/
def owns (r : Router) (ip : Ip) : Bool :=
  r.config.interfaces.any fun (_, i) =>
    i.active && i.vrf == r.vrf.name && i.allAddresses.any (·.ip == ip)

/-- The addresses of the router's active interfaces: those it accepts packets for. -/
def addresses (r : Router) : Array Ip :=
  r.config.interfaces.flatMap fun (_, i) =>
    if i.active && i.vrf == r.vrf.name then i.allAddresses.map (·.ip) else #[]

/-- The FIB actions for destination `dst` in a main RIB: those of the longest-matching
forwarding routes. -/
def fibActions (r : Router) (main : Array Route) (dst : Ip) : EvalM (Array FibAction) := do
  let rib := Rib.ofRoutes main
  let mut out := #[]
  for route in Bgp.lpm rib dst do
    for a in ← resolveActions r.config r.vrf rib route none [] 0 do
      if !out.contains a then out := out.push a
  return out

/-- The IPsec links whose sessions are up in state `x`. -/
def live (r : Router) (x : RouterState) : Array IpsecLink :=
  r.ipsecLinks.filter fun l => x.ipsec.contains l.key

/-- The GRE endpoints of an interface of the router. -/
def greTunnel? (r : Router) (iface : String) : Option TunnelConfiguration :=
  (r.config.interfaces.find? iface).bind (·.tunnelConfig)

/-- Whether the router has a GRE tunnel from `src` to `dst`. -/
def hasGre (r : Router) (src dst : Ip) : Bool :=
  r.config.interfaces.any fun (_, i) =>
    i.vrf == r.vrf.name && i.tunnelConfig == some ⟨src, dst⟩

/-- Whether `iface` is configured as an IPsec tunnel interface, whether or not its session
negotiates. -/
def isIpsecTunnel (r : Router) (iface : String) : Bool :=
  r.config.ipsecPeerConfigs.any (·.2.tunnelInterface == some iface)

/-- Whether `iface` is a tunnel interface: packets leave by it only wrapped. -/
def isTunnel (r : Router) (iface : String) : Bool :=
  r.isIpsecTunnel iface || (r.greTunnel? iface).isSome ||
    (r.config.interfaces.find? iface).any (·.type == "TUNNEL")

/-- The crypto-map entry that protects packet `p` leaving by `iface`: `none` if no entry
permits it, `some l` for the first that does. An ACL that cannot be decided on addresses
counts as permitting. -/
def cryptoEntry? (r : Router) (iface : String) (p : Packet) : Option IpsecLink :=
  r.ipsecLinks.find? fun l =>
    l.tunnelInterface.isNone && l.sourceInterface == iface &&
      match l.acl with
      | some acl => (acl.permitsAddresses r.config.ipSpaces ⟨p.src, p.dst⟩).getD true
      | none => false

/-- Where the router sends packet `p` out of `iface` toward `arpIp`, unchanged. -/
def sendOut (r : Router) (iface : String) (arpIp : Option Ip) (p : Packet) : Out :=
  let target := arpIp.getD p.dst
  match r.links.find? fun (name, ip, _) => name == iface && ip == target with
  | some (_, _, j) => .send j p
  | none => .exit

/-- What the router does with packet `p`, with main RIB `main` and the IPsec links `live`
up. `fuel` bounds how often it wraps or unwraps. -/
def forwardOn (r : Router) (main : Array Route) (live : Array IpsecLink) :
    Nat → Packet → List Out
  | 0, _ => [.drop]
  | fuel + 1, p =>
    if r.owns p.dst then
      match p with
      | .ip .. => [.accept]
      | .gre src dst inner => if r.hasGre dst src then r.forwardOn main live fuel inner else [.drop]
      | .ipsec src dst _ inner =>
        if live.any fun l => l.localAddress == dst && l.remoteAddress == src
        then r.forwardOn main live fuel inner else [.drop]
    else
    match r.fibActions main p.dst with
    | .error _ => [.drop]
    | .ok actions =>
      if actions.isEmpty then [.drop] else
      actions.toList.flatMap fun
        | .discard => [.drop]
        | .forward iface arpIp =>
          if r.isTunnel iface then
            -- GRE wraps first; IPsec protection, if any, wraps the result.
            let inner := match r.greTunnel? iface with
              | some t => Packet.gre t.sourceAddress t.destinationAddress p
              | none => p
            if r.isIpsecTunnel iface then
              match live.find? (·.tunnelInterface == some iface) with
              | some l => r.forwardOn main live fuel (.ipsec l.localAddress l.remoteAddress l.proposal inner)
              | none => [.drop]
            else if (r.greTunnel? iface).isSome then r.forwardOn main live fuel inner
            else [.drop]
          else
            match p with
            | .ipsec .. => [r.sendOut iface arpIp p]
            | _ => match r.cryptoEntry? iface p with
              | none => [r.sendOut iface arpIp p]
              | some l =>
                if live.any (·.key == l.key) then
                  r.forwardOn main live fuel (.ipsec l.localAddress l.remoteAddress l.proposal p)
                else [.drop]

/-- What the router, in state `x`, does with packet `p`. -/
def forward (r : Router) (x : RouterState) (p : Packet) : List Out :=
  r.forwardOn x.main (r.live x) wrapFuel p

end Router

/-! ## Probing the data plane

A router brings an IPsec session up when IKE gets through: the two peers' packets reach
each other, both ways (Batfish's `retainReachableIpsecEdges`). -/

/-- What router `k` of `net`, in the states `X`, does with packet `p`. -/
def forwardIn (net : Array Router) (X : Nat → RouterState) (k : Nat) (p : Packet) : List Out :=
  match net[k]? with
  | some r => r.forward (X k) p
  | none => []

/-- Whether packet `p`, sent from router `i`, can be accepted by router `j` in the states `X`,
within `bound` hops. -/
def deliversIn (net : Array Router) (X : Nat → RouterState) (i : Nat) (p : Packet) (j : Nat)
    (bound : Nat) : Bool :=
  go bound [] [(i, p)]
where
  go : Nat → List (Nat × Packet) → List (Nat × Packet) → Bool
    | 0, _, _ => false
    | fuel + 1, seen, frontier =>
      if frontier.any fun (k, q) => k == j && (forwardIn net X k q).contains .accept then true
      else
        let seen := seen ++ frontier
        let next := frontier.flatMap fun (k, q) => (forwardIn net X k q).filterMap fun
          | .send k' q' => some (k', q')
          | _ => none
        let fresh := next.foldl (fun acc x => if seen.contains x || acc.contains x then acc else acc ++ [x]) []
        if fresh.isEmpty then false else go fuel seen fresh

namespace Router

/-- The IPsec links that are up after the router updates: those whose peers' probes get
through both ways in the current states. -/
def ikeStep (net : Array Router) (r : Router) (X : Nat → RouterState) : Array (String × Ip) :=
  let bound := 2 * net.size + 2
  (r.ipsecLinks.filter fun l =>
    deliversIn net X r.index (.ip l.localAddress l.remoteAddress) l.peer bound &&
    deliversIn net X l.peer (.ip l.remoteAddress l.localAddress) r.index bound).map (·.key)

/-- The router's state after it updates: its routing tables (`updateRoutes`) and its IPsec
sessions. -/
def update (net : Array Router) (r : Router) (X : Nat → RouterState) (input : Input) :
    RouterState :=
  { r.updateRoutes net X input with ipsec := r.ikeStep net X }

end Router

end LeanBatfish.Model
