import LeanBatfish.IR.Ospf

/-!
# Interfaces

The parts of Batfish's `Interface` that the routing and forwarding semantics read.
Batfish has already decided whether each interface is `active` (admin state, line state,
blacklists, autostate); we take that decision from the IR.
-/

namespace LeanBatfish

/-- An interface address: an IP together with its subnet length, e.g. `10.0.0.1/24`
(`ConcreteInterfaceAddress`). Unlike a `Prefix`, the host bits are kept. -/
structure InterfaceAddress where
  ip : Ip
  len : Fin 33
  deriving DecidableEq, Hashable, Inhabited, Repr, Ord

namespace InterfaceAddress

def parse? (s : String) : Option InterfaceAddress := do
  let [ip, len] := s.splitOn "/" | none
  let ip ← Ip.parse? ip
  let len ← len.toNat?
  if h : len < 33 then pure ⟨ip, ⟨len, h⟩⟩ else none

/-- The subnet of the address. -/
def «prefix» (a : InterfaceAddress) : Prefix := Prefix.make a.ip a.len

instance : ToString InterfaceAddress := ⟨fun a => s!"{a.ip}/{a.len}"⟩

end InterfaceAddress

/-- Per-address overrides for the connected and local routes Batfish generates
(`ConnectedRouteMetadata`). Absent values mean "use Batfish's default". -/
structure ConnectedRouteMetadata where
  admin : Option Nat := none
  tag : Option Int := none
  generateConnectedRoute : Option Bool := none
  generateLocalRoutes : Option Bool := none
  generateLocalNullRouteIfDown : Option Bool := none
  deriving Inhabited, Repr

structure Interface where
  name : String
  vrf : String
  active : Bool
  /-- Interface type as Batfish names it, e.g. `PHYSICAL`, `LOOPBACK`. -/
  type : String
  /-- The primary address (`prefix` in the JSON). -/
  address : Option InterfaceAddress
  /-- All addresses, including the primary one (`allPrefixes`). -/
  allAddresses : Array InterfaceAddress
  addressMetadata : Array (InterfaceAddress × ConnectedRouteMetadata)
  incomingFilter : Option String
  outgoingFilter : Option String
  proxyArp : Bool
  ospf : Option OspfInterfaceSettings
  deriving Inhabited, Repr

end LeanBatfish
