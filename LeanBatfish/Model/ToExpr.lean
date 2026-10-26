import Lean.Elab.Deriving.ToExpr
import LeanBatfish.IR.Snapshot

/-!
# Snapshots as Lean terms

`ToExpr` instances for the IR, so that a snapshot read at elaboration time becomes an
ordinary Lean definition (see `LeanBatfish.Model.Command`): its configurations are then
terms that evaluation and proofs can unfold.
-/

namespace LeanBatfish

open Lean

instance : ToExpr JsonNumber where
  toExpr n := mkApp2 (mkConst ``JsonNumber.mk) (toExpr n.mantissa) (toExpr n.exponent)
  toTypeExpr := mkConst ``JsonNumber

deriving instance ToExpr for Ip
deriving instance ToExpr for Prefix
deriving instance ToExpr for IpWildcard
deriving instance ToExpr for AsSet
deriving instance ToExpr for Community
deriving instance ToExpr for SubRange
deriving instance ToExpr for IntervalSet
deriving instance ToExpr for LineAction
deriving instance ToExpr for RoutingProtocol
deriving instance ToExpr for OriginType
deriving instance ToExpr for IntComparator
deriving instance ToExpr for OspfMetricType
deriving instance ToExpr for BgpSessionType
deriving instance ToExpr for IpSpace
deriving instance ToExpr for TcpFlags
deriving instance ToExpr for TcpFlagsMatchConditions
deriving instance ToExpr for HeaderSpace
deriving instance ToExpr for AclLineMatchExpr
deriving instance ToExpr for AclLine
deriving instance ToExpr for IpAccessList
deriving instance ToExpr for NextHop
deriving instance ToExpr for PrefixRange
deriving instance ToExpr for RouteFilterLine
deriving instance ToExpr for RouteFilterList
deriving instance ToExpr for IntMatchExpr
deriving instance ToExpr for AsExpr
deriving instance ToExpr for LongExpr
deriving instance ToExpr for LongMatchExpr
deriving instance ToExpr for AsPathListExpr
deriving instance ToExpr for NextHopExpr
deriving instance ToExpr for PrefixSetExpr
deriving instance ToExpr for CommunityRendering
deriving instance ToExpr for CommunitySetRendering
deriving instance ToExpr for CommunityExpr
deriving instance ToExpr for CommunityMatchExpr, CommunitySetExpr
deriving instance ToExpr for CommunitySetMatchExpr
deriving instance ToExpr for AsPathExpr
deriving instance ToExpr for AsPathMatchExpr
deriving instance ToExpr for AsPathAccessListLine
deriving instance ToExpr for AsPathAccessList
deriving instance ToExpr for StaticStatementType
deriving instance ToExpr for StaticBooleanType
deriving instance ToExpr for AdminCostExpr
deriving instance ToExpr for BooleanExpr, Statement
deriving instance ToExpr for RoutingPolicy
deriving instance ToExpr for GeneratedRoute
deriving instance ToExpr for OspfNetworkType
deriving instance ToExpr for OspfInterfaceSettings
deriving instance ToExpr for OspfArea
deriving instance ToExpr for OspfProcess
deriving instance ToExpr for InterfaceAddress
deriving instance ToExpr for ConnectedRouteMetadata
deriving instance ToExpr for Interface
deriving instance ToExpr for AllowRemoteAsOut
deriving instance ToExpr for AddressFamilyCapabilities
deriving instance ToExpr for Ipv4UnicastAddressFamily
deriving instance ToExpr for BgpPeerRemote
deriving instance ToExpr for BgpPeer
deriving instance ToExpr for NextHopIpTieBreaker
deriving instance ToExpr for BgpTieBreaker
deriving instance ToExpr for MultipathEquivalentAsPathMatchMode
deriving instance ToExpr for LocalOriginationTypeTieBreaker
deriving instance ToExpr for AggregateAsPathMode
deriving instance ToExpr for BgpAggregate
deriving instance ToExpr for BgpProcess
deriving instance ToExpr for StaticRoute
deriving instance ToExpr for Vrf
deriving instance ToExpr for Configuration
deriving instance ToExpr for AnnouncementType
deriving instance ToExpr for Announcement
deriving instance ToExpr for NodeInterface
deriving instance ToExpr for OspfEdge
deriving instance ToExpr for BgpEdge
deriving instance ToExpr for Layer3Edge
deriving instance ToExpr for Topology
deriving instance ToExpr for Snapshot

end LeanBatfish
