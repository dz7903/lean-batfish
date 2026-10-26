import LeanBatfishSim.Engine

/-!
# Answers

The simulator answers the same questions as Batfish, in the same table format, so the
two answers can be compared row by row. Each question is a function from the converged
data plane (and the configurations) to rows; a row is a JSON object whose keys are
Batfish's column names and whose values are rendered as Batfish renders them.
-/

namespace LeanBatfishSim

open Lean LeanBatfish

/-- A table answer: column names and rows, shaped like Batfish's `TableAnswerElement`
inside an answer. -/
def table (columns : Array String) (rows : Array Json) : Json :=
  Json.mkObj [("answerElements", Json.arr #[Json.mkObj [
    ("metadata", Json.mkObj [("columnMetadata", Json.arr (columns.map fun c =>
      Json.mkObj [("name", toJson c)]))]),
    ("rows", Json.arr rows)]])]

/-! ## Rendering values as Batfish does -/

def renderNode (name : String) : Json :=
  Json.mkObj [("id", s!"node-{name}"), ("name", name)]

def renderProtocol (p : RoutingProtocol) : String :=
  match RoutingProtocol.names.find? (·.2 == p) with
  | some (name, _) => name
  | none => "?"

/-- A next hop (`NextHop`, tagged by `type`). -/
def renderNextHop : NextHop → Json
  | .discard => Json.mkObj [("type", "discard")]
  | .ip ip => Json.mkObj [("type", "ip"), ("ip", toString ip)]
  | .iface name none => Json.mkObj [("type", "interface"), ("interface", name)]
  | .iface name (some ip) =>
    Json.mkObj [("type", "interface"), ("interface", name), ("ip", toString ip)]

def renderTag (tag : Int) : Json := if tag == unsetRouteTag then .null else toJson tag

/-! ## Questions -/

/-- `routes`: every route of every main RIB. -/
def answerRoutes (dp : DataPlane) : Json :=
  table #["Node", "VRF", "Network", "Next_Hop", "Protocol", "Metric", "Admin_Distance", "Tag"]
    (dp.vrfs.flatMap fun v => v.rib.routes.map fun r => Json.mkObj [
      ("Node", renderNode v.node), ("VRF", v.vrf), ("Network", toString r.network),
      ("Next_Hop", renderNextHop r.nextHop), ("Protocol", renderProtocol r.protocol),
      ("Metric", r.metric), ("Admin_Distance", r.admin), ("Tag", renderTag r.tag)])

/-- `fibs`: every FIB entry (a question our Batfish branch adds). -/
def answerFibs (dp : DataPlane) : Json :=
  table #["Node", "VRF", "Network", "Protocol", "Next_Hop", "Action", "Interface", "Arp_IP",
      "Next_VRF"]
    (dp.vrfs.flatMap fun v => v.fib.map fun e =>
      let (action, iface, arpIp) : String × Json × Json := match e.action with
        | .forward name ip => ("forward", toJson name, (ip.map (toJson ∘ toString)).getD .null)
        | .discard => ("discard", .null, .null)
      Json.mkObj [
        ("Node", renderNode v.node), ("VRF", v.vrf), ("Network", toString e.route.network),
        ("Protocol", renderProtocol e.route.protocol),
        ("Next_Hop", renderNextHop e.route.nextHop), ("Action", action),
        ("Interface", iface), ("Arp_IP", arpIp), ("Next_VRF", Json.null)])

def renderOriginType (o : OriginType) : String :=
  match OriginType.names.find? (·.2 == o) with
  | some (name, _) => name
  | none => "?"

/-- `bgpRib`: the routes of every BGP RIB (best paths, or the best route per next hop in a
multipath RIB), with their BGP attributes. -/
def answerBgpRib (dp : DataPlane) : Json :=
  table #["Node", "VRF", "Network", "Status", "Next_Hop", "Protocol", "AS_Path", "Metric",
      "Local_Pref", "Communities", "Origin_Protocol", "Origin_Type", "Originator_Id",
      "Received_From_IP", "Received_Path_Id", "Cluster_List", "Tunnel_Encapsulation_Attribute",
      "Weight", "Tag"]
    (dp.bgp.flatMap fun (node, vrf, routes) => routes.map fun r =>
      let a := r.bgp.getD {}
      Json.mkObj [
        ("Node", renderNode node), ("VRF", vrf), ("Network", toString r.network),
        ("Status", Json.arr #["BEST"]), ("Next_Hop", renderNextHop r.nextHop),
        ("Protocol", renderProtocol r.protocol), ("AS_Path", a.asPath.render),
        ("Metric", r.metric), ("Local_Pref", a.localPreference),
        ("Communities", Json.arr (a.communities.toArray.map (toJson ∘ toString))),
        ("Origin_Protocol", match a.srcProtocol with
          | some p => toJson (renderProtocol p) | none => Json.null),
        ("Origin_Type", renderOriginType a.originType),
        ("Originator_Id", toString a.originatorIp),
        ("Received_From_IP", toString (Bgp.receivedFromIp a.receivedFrom)),
        ("Received_Path_Id", match a.pathId with | some n => toJson n | none => Json.null),
        ("Cluster_List", if a.clusterList.isEmpty then Json.null
          else Json.arr (a.clusterList.map toJson)),
        ("Tunnel_Encapsulation_Attribute", Json.null), ("Weight", a.weight),
        ("Tag", renderTag r.tag)])

/-- The questions the simulator answers, by Batfish's name. -/
def questions : List (String × (DataPlane → Json)) :=
  [("routes", answerRoutes), ("fibs", answerFibs), ("bgpRib", answerBgpRib)]

end LeanBatfishSim
