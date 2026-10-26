import LeanBatfish.Decode.Net
import LeanBatfish.IR.Announcement

/-!
# Decoding external BGP announcements

Decodes `external_bgp_announcements.json`. Its AS paths are lists of AS sets, each a list
of AS numbers.
-/

namespace LeanBatfish.Decode

open Lean ObjM

def announcementType : Decoder AnnouncementType := fun j => do
  let s ← str j
  match s.toLower.splitOn "_" with
  | [proto, how] =>
    let ebgp ← match proto with
      | "ebgp" => pure true
      | "ibgp" => pure false
      | _ => DecodeM.malformed s!"unknown announcement type {s}"
    let received ← match how with
      | "received" => pure true
      | "sent" => pure false
      | _ => DecodeM.unsupported s!"announcement type {s} is not modeled"
    pure { ebgp, received }
  | _ => DecodeM.malformed s!"unknown announcement type {s}"

def asPathSets : Decoder AsPath := array fun j => do
  let asns ← array nat j
  pure { asns := asns.qsort (· < ·) }

def announcement : Decoder Announcement := object do
  pure {
    type := ← req "type" announcementType
    network := ← req "network" «prefix»
    nextHopIp := ← req "nextHopIp" ip
    srcIp := ← req "srcIp" ip
    dstNode := ← req "dstNode" str
    dstIp := ← req "dstIp" ip
    dstVrf := ← dflt "dstVrf" "default" str
    -- Announcements spell protocols in upper case; Batfish reads enums case-insensitively.
    srcProtocol := ← req "srcProtocol" fun j => do
      let name ← str j
      match RoutingProtocol.names.find? (·.1.toLower == name.toLower) with
      | some (_, p) => pure p
      | none => DecodeM.malformed s!"unknown routing protocol {name}"
    originType := ← req "originType" (enum "origin type" OriginType.names)
    localPreference := ← dflt "localPreference" 0 nat
    med := ← dflt "med" 0 nat
    originatorIp := ← opt "originatorIp" ip
    asPath := ← dflt "asPath" #[] asPathSets
    -- Communities may also be written as the 32-bit value of a standard community.
    communities := ← dflt "communities" #[] (array fun j => match j with
      | .num _ => do
        let v ← nat j
        if v < 2 ^ 32 then pure (.standard (UInt32.ofNat v))
        else DecodeM.malformed s!"community value {v} out of range"
      | _ => community j)
    clusterList := ← dflt "clusterList" #[] (array nat)
    weight := ← dflt "weight" 0 nat }

/-- Decode an `external_bgp_announcements.json` file. -/
def announcements (j : Json) : Except Rejection (Array Announcement) :=
  (object (do req "Announcements" (array announcement)) j).run
