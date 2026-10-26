import LeanBatfish.IR.Basic
import LeanBatfish.Net.AsPath
import LeanBatfish.Net.Community
import LeanBatfish.Net.Prefix

/-!
# External BGP announcements

A snapshot may include BGP announcements from outside the network
(`external_bgp_announcements.json`, Batfish's `BgpAdvertisement`): routes that a peer
outside the snapshot sends to a router in it.
-/

namespace LeanBatfish

/-- How an announcement reached the router (`BgpAdvertisementType`): over eBGP or iBGP, and
either as sent by the peer (so the router's import policy still applies) or as already
received. -/
structure AnnouncementType where
  ebgp : Bool
  received : Bool
  deriving DecidableEq, Inhabited, Repr

structure Announcement where
  type : AnnouncementType
  network : Prefix
  nextHopIp : Ip
  srcIp : Ip
  dstNode : String
  dstIp : Ip
  dstVrf : String
  srcProtocol : RoutingProtocol
  originType : OriginType
  localPreference : Nat
  med : Nat
  /-- Absent means the source IP. -/
  originatorIp : Option Ip
  asPath : AsPath
  communities : Array Community
  clusterList : Array Nat
  weight : Nat
  deriving Inhabited, Repr

end LeanBatfish
