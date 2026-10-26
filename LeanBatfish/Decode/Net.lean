import LeanBatfish.Decode.Core
import LeanBatfish.Data.IntervalSet
import LeanBatfish.Net.IpWildcard
import LeanBatfish.Net.IpProtocol
import LeanBatfish.Net.Community
import LeanBatfish.IR.Basic
import LeanBatfish.IR.Interface

/-!
# Decoders for network values

Decoders for the scalar values that appear throughout the IR: addresses, prefixes,
ranges, protocols, communities and the common enumerations.
-/

namespace LeanBatfish.Decode

open Lean

def ip : Decoder Ip := parsed "an IP address" Ip.parse?
def «prefix» : Decoder Prefix := parsed "a prefix" Prefix.parse?
def ipWildcard : Decoder IpWildcard := parsed "an IP wildcard" IpWildcard.parse?
def interfaceAddress : Decoder InterfaceAddress := fun j => do
  if let .str s := j then
    if s.startsWith "link-local:" then
      DecodeM.unsupported "link-local interface addresses are not modeled"
  parsed "an interface address" InterfaceAddress.parse? j
def intervalSet : Decoder IntervalSet := parsed "a number space" IntervalSet.parse?
def community : Decoder Community := parsed "a BGP community" Community.parse?
def ipProtocol : Decoder IpProtocol := parsed "an IP protocol" IpProtocol.parse?

/-- A `SubRange`: a string `"a-b"` or a single number. -/
def subRange : Decoder SubRange := fun j =>
  match j with
  | .str s => match SubRange.parse? s with
    | some r => pure r
    | none => DecodeM.malformed s!"expected a range, got {s.quote}"
  | _ => do let n ← nat j; pure (.singleton n)

def lineAction : Decoder LineAction := enum "line action" LineAction.names
def routingProtocol : Decoder RoutingProtocol := enum "routing protocol" RoutingProtocol.names
def originType : Decoder OriginType := enum "origin type" OriginType.names
def intComparator : Decoder IntComparator := enum "comparator" IntComparator.names
def ospfMetricType : Decoder OspfMetricType := enum "OSPF metric type" OspfMetricType.names
def bgpSessionType : Decoder BgpSessionType := enum "BGP session type" BgpSessionType.names

end LeanBatfish.Decode
