import LeanBatfish.IR.Basic
import LeanBatfish.Net.Community
import LeanBatfish.Net.Prefix

namespace LeanBatfish

/-- A generated route (`GeneratedRoute`), such as a Junos aggregate route: active while some
main-RIB route passes its generation policy (or always, without one). Batfish never
deactivates a generated route once active. -/
structure GeneratedRoute where
  network : Prefix
  administrativeCost : Nat
  metric : Nat
  tag : Int
  /-- Discard traffic; otherwise forward to the next hop of the route that activated it. -/
  discard : Bool
  generationPolicy : Option String
  /-- Sets BGP attributes when the route is exported into BGP. -/
  attributePolicy : Option String
  communities : Array Community
  localPreference : Nat
  originType : OriginType
  weight : Nat
  deriving Inhabited, Repr

end LeanBatfish
