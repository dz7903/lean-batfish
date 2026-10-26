/-!
# Common IR enumerations

Small enumerations shared across the IR. Each one lists the JSON spelling Batfish uses.
-/

namespace LeanBatfish

/-- Permit or deny, used by ACL lines, route-filter lines and similar. -/
inductive LineAction
  | permit
  | deny
  deriving DecidableEq, Hashable, Inhabited, Repr

def LineAction.names : List (String × LineAction) := [("PERMIT", .permit), ("DENY", .deny)]

/-- The protocol that produced a route. The table is generated from Batfish's
`RoutingProtocol.java`. -/
inductive RoutingProtocol
  | aggregate
  | bgp
  | connected
  | egp
  | eigrp
  | eigrpEx
  | evpn
  | ibgp
  | igp
  | isisAny
  | isisEl1
  | isisEl2
  | isisL1
  | isisL2
  | kernel
  | ldp
  | lisp
  | local
  | hmm
  | msdp
  | ospf
  | ospfE1
  | ospfE2
  | ospfIa
  | ospfIs
  | ospf3
  | rip
  | rsvp
  | static
  deriving DecidableEq, Hashable, Inhabited, Repr, Ord

def RoutingProtocol.names : List (String × RoutingProtocol) := [
  ("aggregate", .aggregate),
  ("bgp", .bgp),
  ("connected", .connected),
  ("egp", .egp),
  ("eigrp", .eigrp),
  ("eigrpEX", .eigrpEx),
  ("evpn", .evpn),
  ("ibgp", .ibgp),
  ("igp", .igp),
  ("isis", .isisAny),
  ("isisEL1", .isisEl1),
  ("isisEL2", .isisEl2),
  ("isisL1", .isisL1),
  ("isisL2", .isisL2),
  ("kernel", .kernel),
  ("ldp", .ldp),
  ("lisp", .lisp),
  ("local", .local),
  ("hmm", .hmm),
  ("msdp", .msdp),
  ("ospf", .ospf),
  ("ospfE1", .ospfE1),
  ("ospfE2", .ospfE2),
  ("ospfIA", .ospfIa),
  ("ospfIS", .ospfIs),
  ("ospf3", .ospf3),
  ("rip", .rip),
  ("rsvp", .rsvp),
  ("static", .static)
]

/-- The BGP ORIGIN attribute. -/
inductive OriginType
  | egp
  | igp
  | incomplete
  deriving DecidableEq, Hashable, Inhabited, Repr

def OriginType.names : List (String × OriginType) :=
  [("egp", .egp), ("igp", .igp), ("incomplete", .incomplete)]

/-- Preference of an origin type in BGP best-path selection: higher is better
(IGP 2, EGP 1, INCOMPLETE 0), as in `OriginType.getPreference`. -/
def OriginType.preference : OriginType → Nat
  | .igp => 2
  | .egp => 1
  | .incomplete => 0

inductive IntComparator
  | eq | ge | gt | le | lt
  deriving DecidableEq, Hashable, Inhabited, Repr

def IntComparator.names : List (String × IntComparator) :=
  [("EQ", .eq), ("GE", .ge), ("GT", .gt), ("LE", .le), ("LT", .lt)]

def IntComparator.apply : IntComparator → Int → Int → Bool
  | .eq, a, b => a == b
  | .ge, a, b => a ≥ b
  | .gt, a, b => a > b
  | .le, a, b => a ≤ b
  | .lt, a, b => a < b

/-- OSPF external route metric type. -/
inductive OspfMetricType
  | e1
  | e2
  deriving DecidableEq, Hashable, Inhabited, Repr

def OspfMetricType.names : List (String × OspfMetricType) := [("E1", .e1), ("E2", .e2)]

/-- The type of a BGP session (`BgpSessionProperties.SessionType`). -/
inductive BgpSessionType
  | ibgp
  | ebgpSinglehop
  | ebgpMultihop
  | ebgpUnnumbered
  | ibgpUnnumbered
  | unset
  deriving DecidableEq, Hashable, Inhabited, Repr

def BgpSessionType.names : List (String × BgpSessionType) :=
  [("IBGP", .ibgp), ("EBGP_SINGLEHOP", .ebgpSinglehop), ("EBGP_MULTIHOP", .ebgpMultihop),
   ("EBGP_UNNUMBERED", .ebgpUnnumbered), ("IBGP_UNNUMBERED", .ibgpUnnumbered),
   ("UNSET", .unset)]

end LeanBatfish
