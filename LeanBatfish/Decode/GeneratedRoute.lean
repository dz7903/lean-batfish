import LeanBatfish.Decode.Net
import LeanBatfish.IR.GeneratedRoute

/-!
# Decoding generated routes

Generated routes appear in VRFs (Junos aggregate routes), on BGP neighbors and in OSPF
processes (default-originate).
-/

namespace LeanBatfish.Decode

open Lean ObjM

def generatedRoute : Decoder GeneratedRoute := byClass "generated route" [
  ("GeneratedRoute", do
    ignoreAll ["attributePolicySources", "generationPolicySources"]
    gateEmpty "asPath" "generated routes with an AS path"
    let discard ← dflt "discard" false bool
    -- The next hop is the activating route's, or discard; Batfish ignores these fields.
    ignoreAll ["nextHopInterface", "nextHopIp"]
    pure {
      network := ← req "network" «prefix», discard
      administrativeCost := ← req "administrativeCost" nat
      metric := ← dflt "metric" 0 nat
      tag := ← dflt "tag" (-1) int
      generationPolicy := ← opt "generationPolicy" str
      attributePolicy := ← opt "attributePolicy" str
      communities := ← dflt "communities" #[] (array community)
      localPreference := ← dflt "localPreference" 100 nat
      originType := ← dflt "originType" .igp (enum "origin type" OriginType.names)
      weight := ← dflt "weight" 0 nat })]

end LeanBatfish.Decode
