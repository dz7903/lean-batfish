import LeanBatfish.Decode.Net
import LeanBatfish.IR.Acl

/-!
# Decoding IP spaces and ACLs
-/

namespace LeanBatfish.Decode

open Lean ObjM

/-- Trace elements and vendor structure ids only serve Batfish's presentation of
results. -/
def ignorePresentation : ObjM Unit :=
  ignoreAll ["traceElement", "vendorStructureId", "name"]

partial def ipSpace : Decoder IpSpace :=
  byClass "IP space" [
    ("EmptyIpSpace", pure .empty),
    ("UniverseIpSpace", pure .universe),
    ("IpIpSpace", .ip <$> req "ip" ip),
    ("PrefixIpSpace", .prefix <$> req "prefix" «prefix»),
    ("IpWildcardIpSpace", .wildcard <$> req "ipWildcard" ipWildcard),
    ("IpWildcardSetIpSpace", do
      let w ← dflt "whitelist" #[] (array ipWildcard)
      let b ← dflt "blacklist" #[] (array ipWildcard)
      pure (.wildcardSet w b)),
    ("IpSpaceReference", do ignore "description"; .reference <$> req "name" str),
    ("AclIpSpace", .acl <$> dflt "lines" #[] (array (object do
      ignore "srcText"
      let action ← req "action" lineAction
      let space ← req "ipSpace" ipSpace
      pure (action, space))))]

def tcpFlags : Decoder TcpFlags := object do
  pure {
    ack := ← dflt "ack" false bool, cwr := ← dflt "cwr" false bool
    ece := ← dflt "ece" false bool, fin := ← dflt "fin" false bool
    psh := ← dflt "psh" false bool, rst := ← dflt "rst" false bool
    syn := ← dflt "syn" false bool, urg := ← dflt "urg" false bool }

def tcpFlagsMatchConditions : Decoder TcpFlagsMatchConditions := object do
  pure {
    tcpFlags := ← dflt "tcpFlags" {} tcpFlags
    useAck := ← dflt "useAck" false bool, useCwr := ← dflt "useCwr" false bool
    useEce := ← dflt "useEce" false bool, useFin := ← dflt "useFin" false bool
    usePsh := ← dflt "usePsh" false bool, useRst := ← dflt "useRst" false bool
    useSyn := ← dflt "useSyn" false bool, useUrg := ← dflt "useUrg" false bool }

def headerSpace : Decoder HeaderSpace := object do
  -- Batfish's concrete evaluator ignores `negate`, so only its neutral value is accepted.
  gate "negate" "negated header space" (· == .bool false)
  let ranges (k : String) := dflt k #[] (array subRange)
  pure {
    srcIps := ← opt "srcIps" ipSpace
    dstIps := ← opt "dstIps" ipSpace
    srcOrDstIps := ← opt "srcOrDstIps" ipSpace
    notSrcIps := ← opt "notSrcIps" ipSpace
    notDstIps := ← opt "notDstIps" ipSpace
    srcPorts := ← ranges "srcPorts"
    dstPorts := ← ranges "dstPorts"
    srcOrDstPorts := ← ranges "srcOrDstPorts"
    notSrcPorts := ← ranges "notSrcPorts"
    notDstPorts := ← ranges "notDstPorts"
    ipProtocols := ← dflt "ipProtocols" #[] (array ipProtocol)
    notIpProtocols := ← dflt "notIpProtocols" #[] (array ipProtocol)
    icmpTypes := ← ranges "icmpTypes"
    notIcmpTypes := ← ranges "notIcmpTypes"
    icmpCodes := ← ranges "icmpCodes"
    notIcmpCodes := ← ranges "notIcmpCodes"
    dscps := ← dflt "dscps" #[] (array nat)
    notDscps := ← dflt "notDscps" #[] (array nat)
    ecns := ← dflt "ecns" #[] (array nat)
    notEcns := ← dflt "notEcns" #[] (array nat)
    fragmentOffsets := ← ranges "fragmentOffsets"
    notFragmentOffsets := ← ranges "notFragmentOffsets"
    packetLengths := ← ranges "packetLengths"
    notPacketLengths := ← ranges "notPacketLengths"
    tcpFlagsMatchConditions := ← dflt "tcpFlagsMatchConditions" #[]
      (array tcpFlagsMatchConditions) }

partial def aclLineMatchExpr : Decoder AclLineMatchExpr :=
  let c (name : String) (d : ObjM AclLineMatchExpr) := ("acl." ++ name, do ignorePresentation; d)
  byClass "ACL match expression" [
    c "TrueExpr" (pure .trueExpr),
    c "FalseExpr" (pure .falseExpr),
    c "MatchHeaderSpace" (.matchHeaderSpace <$> req "headerSpace" headerSpace),
    c "AndMatchExpr" (.and <$> dflt "conjuncts" #[] (array aclLineMatchExpr)),
    c "OrMatchExpr" (.or <$> dflt "disjuncts" #[] (array aclLineMatchExpr)),
    c "NotMatchExpr" (.not <$> req "operand" aclLineMatchExpr),
    c "MatchSourceIp" (.matchSourceIp <$> req "ips" ipSpace),
    c "MatchDestinationIp" (.matchDestinationIp <$> req "ips" ipSpace),
    c "MatchSourcePort" (.matchSourcePort <$> req "ports" intervalSet),
    c "MatchDestinationPort" (.matchDestinationPort <$> req "ports" intervalSet),
    c "MatchIpProtocol" (.matchIpProtocol <$> req "protocol" ipProtocol),
    c "MatchSrcInterface" (.matchSrcInterface <$> dflt "srcInterfaces" #[] (array str)),
    c "OriginatingFromDevice" (pure .originatingFromDevice),
    c "PermittedByAcl" (.permittedByAcl <$> req "aclName" str),
    c "DeniedByAcl" (.deniedByAcl <$> req "aclName" str)]

def aclLine : Decoder AclLine :=
  byClass "ACL line" [
    ("ExprAclLine", do
      ignorePresentation
      let action ← req "action" lineAction
      let m ← req "matchCondition" aclLineMatchExpr
      pure (.expr action m)),
    ("AclAclLine", do ignorePresentation; .acl <$> req "aclName" str)]

def ipAccessList : Decoder IpAccessList := object do
  ignoreAll ["sourceName", "sourceType"]
  pure { name := ← req "name" str, lines := ← dflt "lines" #[] (array aclLine) }

end LeanBatfish.Decode
