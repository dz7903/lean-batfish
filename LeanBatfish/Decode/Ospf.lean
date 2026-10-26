import LeanBatfish.Decode.GeneratedRoute
import LeanBatfish.IR.Ospf

/-!
# Decoding OSPF configuration

The modeled subset: normal areas (no stub or NSSA), broadcast and point-to-point
networks, no area summaries, no distribute lists, no max-metric and no OSPF-generated
routes (default-originate).
-/

namespace LeanBatfish.Decode

open Lean ObjM

def ospfInterfaceSettings : Decoder OspfInterfaceSettings := object do
  ignore "helloMultiplier"
  gateEmpty "inboundDistributeListPolicy" "OSPF distribute lists"
  gateEmpty "nbmaNeighbors" "OSPF NBMA neighbors"
  gateEmpty "ospfAddresses" "OSPF address overrides"
  gateEmpty "type5FilterPolicy" "OSPF type-5 filters"
  pure {
    enabled := ← dflt "enabled" false bool
    passive := ← dflt "passive" false bool
    process := ← opt "process" str
    area := ← opt "area" nat
    cost := ← opt "cost" nat
    networkType := ← opt "networkType" (enum "OSPF network type" OspfNetworkType.names)
    helloInterval := ← dflt "helloInterval" 10 nat
    deadInterval := ← dflt "deadInterval" 40 nat }

def ospfArea : Decoder OspfArea := object do
  gateEmpty "nssa" "OSPF NSSA areas"
  gateEmpty "stub" "OSPF stub areas"
  gate "stubType" "OSPF stub/NSSA areas" (· == .str "NONE")
  gateEmpty "summaries" "OSPF area summaries"
  gateEmpty "summaryFilter" "OSPF summary filters"
  pure {
    name := ← req "name" nat
    interfaces := ← dflt "interfaces" #[] (array str)
    injectDefaultRoute := ← dflt "injectDefaultRoute" true bool
    metricOfDefaultRoute := ← dflt "metricOfDefaultRoute" 0 nat }

def ospfProcess : Decoder OspfProcess := object do
  -- Batfish's JSON reader ignores `summaryDiscardMetric`.
  ignoreAll ["exportPolicySources", "summaryDiscardMetric"]
  gateEmpty "maxMetricExternalNetworks" "OSPF max-metric"
  gateEmpty "maxMetricStubNetworks" "OSPF max-metric"
  gateEmpty "maxMetricSummaryNetworks" "OSPF max-metric"
  gateEmpty "maxMetricTransitLinks" "OSPF max-metric"
  gateEmpty "rfc1583Compatible" "OSPF RFC 1583 compatibility setting"
  let adminCosts ← dflt "adminCosts" #[] (map nat)
  let adminCosts ← adminCosts.mapM fun (k, v) => do
    match RoutingProtocol.names.lookup k with
    | some p => pure (p, v)
    | none => DecodeM.malformed s!"unknown protocol {k.quote} in adminCosts"
  pure {
    processId := ← req "processId" str
    routerId := ← req "routerId" ip
    referenceBandwidth := ← req "referenceBandwidth" fun j => match j with
      | .num n => pure n
      | _ => DecodeM.malformed "expected a number"
    adminCosts
    areas := (← dflt "areas" #[] (map ospfArea)).map (·.2)
    exportPolicy := ← opt "exportPolicy" str
    summaryAdminCost := ← dflt "summaryAdminCost" 254 nat
    generatedRoutes := ← dflt "generatedRoutes" #[] (array generatedRoute) }

end LeanBatfish.Decode
