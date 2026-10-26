import LeanBatfish.IR.IpSpace
import LeanBatfish.Data.IntervalSet
import LeanBatfish.Net.IpProtocol

/-!
# Access control lists

An `IpAccessList` is an ordered list of lines; a packet takes the action of the first
line that matches it, and is denied if no line matches. A line either tests a match
expression (`ExprAclLine`) or defers to another ACL (`AclAclLine`).
-/

namespace LeanBatfish

/-- TCP flag values. -/
structure TcpFlags where
  ack : Bool := false
  cwr : Bool := false
  ece : Bool := false
  fin : Bool := false
  psh : Bool := false
  rst : Bool := false
  syn : Bool := false
  urg : Bool := false
  deriving DecidableEq, Hashable, Inhabited, Repr

/-- A condition on TCP flags: each flag whose `use` bit is set must equal the value in
`tcpFlags`. -/
structure TcpFlagsMatchConditions where
  tcpFlags : TcpFlags := {}
  useAck : Bool := false
  useCwr : Bool := false
  useEce : Bool := false
  useFin : Bool := false
  usePsh : Bool := false
  useRst : Bool := false
  useSyn : Bool := false
  useUrg : Bool := false
  deriving DecidableEq, Hashable, Inhabited, Repr

/-- A set of packet headers, described field by field. An absent IP space or an empty
range list places no constraint. -/
structure HeaderSpace where
  srcIps : Option IpSpace := none
  dstIps : Option IpSpace := none
  srcOrDstIps : Option IpSpace := none
  notSrcIps : Option IpSpace := none
  notDstIps : Option IpSpace := none
  srcPorts : Array SubRange := #[]
  dstPorts : Array SubRange := #[]
  srcOrDstPorts : Array SubRange := #[]
  notSrcPorts : Array SubRange := #[]
  notDstPorts : Array SubRange := #[]
  ipProtocols : Array IpProtocol := #[]
  notIpProtocols : Array IpProtocol := #[]
  icmpTypes : Array SubRange := #[]
  notIcmpTypes : Array SubRange := #[]
  icmpCodes : Array SubRange := #[]
  notIcmpCodes : Array SubRange := #[]
  dscps : Array Nat := #[]
  notDscps : Array Nat := #[]
  ecns : Array Nat := #[]
  notEcns : Array Nat := #[]
  fragmentOffsets : Array SubRange := #[]
  notFragmentOffsets : Array SubRange := #[]
  packetLengths : Array SubRange := #[]
  notPacketLengths : Array SubRange := #[]
  tcpFlagsMatchConditions : Array TcpFlagsMatchConditions := #[]
  deriving Inhabited, Repr

inductive AclLineMatchExpr
  | trueExpr
  | falseExpr
  | matchHeaderSpace (headerSpace : HeaderSpace)
  | and (conjuncts : Array AclLineMatchExpr)
  | or (disjuncts : Array AclLineMatchExpr)
  | not (operand : AclLineMatchExpr)
  | matchSourceIp (ips : IpSpace)
  | matchDestinationIp (ips : IpSpace)
  | matchSourcePort (ports : IntervalSet)
  | matchDestinationPort (ports : IntervalSet)
  | matchIpProtocol (protocol : IpProtocol)
  /-- The packet entered the device on one of these interfaces. -/
  | matchSrcInterface (interfaces : Array String)
  /-- The packet was originated by the device itself. -/
  | originatingFromDevice
  | permittedByAcl (aclName : String)
  | deniedByAcl (aclName : String)
  deriving Inhabited, Repr

inductive AclLine
  | expr (action : LineAction) (matchCondition : AclLineMatchExpr)
  /-- Evaluate the named ACL; if one of its lines matches, take that line's action,
  otherwise fall through to the next line. -/
  | acl (aclName : String)
  deriving Inhabited, Repr

structure IpAccessList where
  name : String
  lines : Array AclLine
  deriving Inhabited, Repr

end LeanBatfish
