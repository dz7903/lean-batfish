import LeanBatfish.IR.Configuration

/-!
# IP spaces and ACLs on addresses

Membership of an address in an `IpSpace`, and the decision of an ACL on a packet of which
only the source and destination addresses are known. LeanBatfish does not model packet
filters yet; these are what IPsec reads: the identities of dynamic peers, and the crypto
maps that select the packets to protect. An ACL line that looks at anything other than
addresses (ports, protocols, interfaces, ...) cannot be decided on addresses alone; the
decision is then `none`.
-/

namespace LeanBatfish

namespace IpSpace

/-- Whether `ip` is in the space. `named` holds the named spaces that references point to;
`fuel` bounds how many references are followed. -/
def containsIp (named : NameMap IpSpace) (ip : Ip) (fuel : Nat) : IpSpace → Bool
  | .empty => false
  | .universe => true
  | .ip a => a == ip
  | .prefix p => p.containsIp ip
  | .wildcard w => w.containsIp ip
  | .wildcardSet white black => white.any (·.containsIp ip) && !black.any (·.containsIp ip)
  | .reference name => match fuel, named.find? name with
    | fuel + 1, some s => containsIp named ip fuel s
    | _, _ => false
  -- The action of the first line whose space contains `ip`.
  | .acl lines =>
    match lines.attach.find? (fun ⟨(_, s), _⟩ => containsIp named ip fuel s) with
    | some ⟨(action, _), _⟩ => action == .permit
    | none => false
termination_by s => (fuel, s)
decreasing_by
  · exact Prod.Lex.left _ _ (by omega)
  · rename_i h
    apply Prod.Lex.right
    have := Array.sizeOf_lt_of_mem h
    simp_all; omega

end IpSpace

/-- How many named references an address test follows. -/
def ipSpaceFuel : Nat := 16

/-- A packet as an ACL of a crypto map sees it: its two addresses. -/
structure AddressPair where
  src : Ip
  dst : Ip
  deriving DecidableEq, Hashable, Inhabited, Repr

namespace HeaderSpace

/-- Whether the header space constrains only addresses. -/
def onlyAddresses (h : HeaderSpace) : Bool :=
  h.srcPorts.isEmpty && h.dstPorts.isEmpty && h.srcOrDstPorts.isEmpty &&
  h.notSrcPorts.isEmpty && h.notDstPorts.isEmpty && h.ipProtocols.isEmpty &&
  h.notIpProtocols.isEmpty && h.icmpTypes.isEmpty && h.notIcmpTypes.isEmpty &&
  h.icmpCodes.isEmpty && h.notIcmpCodes.isEmpty && h.dscps.isEmpty && h.notDscps.isEmpty &&
  h.ecns.isEmpty && h.notEcns.isEmpty && h.fragmentOffsets.isEmpty &&
  h.notFragmentOffsets.isEmpty && h.packetLengths.isEmpty && h.notPacketLengths.isEmpty &&
  h.tcpFlagsMatchConditions.isEmpty

/-- Whether a packet with addresses `a` is in the header space, if that depends only on
addresses. -/
def matchAddresses (named : NameMap IpSpace) (a : AddressPair) (h : HeaderSpace) :
    Option Bool :=
  if !h.onlyAddresses then none else
  let inSpace (s : IpSpace) (ip : Ip) := s.containsIp named ip ipSpaceFuel
  -- An absent space places no constraint.
  let holds (s : Option IpSpace) (test : IpSpace → Bool) := (s.map test).getD true
  some <| holds h.srcIps (inSpace · a.src) && holds h.dstIps (inSpace · a.dst) &&
    holds h.srcOrDstIps (fun s => inSpace s a.src || inSpace s a.dst) &&
    holds h.notSrcIps (!inSpace · a.src) && holds h.notDstIps (!inSpace · a.dst)

end HeaderSpace

/-- The conjunction of decisions that may be unknown: false if one is false. -/
def Option.allTrue : List (Option Bool) → Option Bool
  | [] => some true
  | some false :: _ => some false
  | x :: rest => match x, Option.allTrue rest with
    | _, some false => some false
    | some true, some true => some true
    | _, _ => none

/-- The disjunction of decisions that may be unknown: true if one is true. -/
def Option.anyTrue (xs : List (Option Bool)) : Option Bool :=
  (Option.allTrue (xs.map (·.map (!·)))).map (!·)

namespace AclLineMatchExpr

/-- Whether a packet with addresses `a` matches, if that depends only on addresses. -/
def matchAddresses (named : NameMap IpSpace) (a : AddressPair) : AclLineMatchExpr → Option Bool
  | .trueExpr => some true
  | .falseExpr => some false
  | .matchHeaderSpace h => h.matchAddresses named a
  | .and xs => Option.allTrue (xs.attach.toList.map fun ⟨x, _⟩ => matchAddresses named a x)
  | .or xs => Option.anyTrue (xs.attach.toList.map fun ⟨x, _⟩ => matchAddresses named a x)
  | .not x => (matchAddresses named a x).map (!·)
  | .matchSourceIp s => some (s.containsIp named a.src ipSpaceFuel)
  | .matchDestinationIp s => some (s.containsIp named a.dst ipSpaceFuel)
  | _ => none

end AclLineMatchExpr

/-- Whether the ACL permits a packet with addresses `a`, if that depends only on addresses:
the action of the first matching line, and deny if none matches. Lines referring to other
ACLs are not followed. -/
def IpAccessList.permitsAddresses (acl : IpAccessList) (named : NameMap IpSpace)
    (a : AddressPair) : Option Bool :=
  go acl.lines.toList
where
  go : List AclLine → Option Bool
    | [] => some false
    | .expr action m :: rest => match m.matchAddresses named a with
      | some true => some (action == .permit)
      | some false => go rest
      | none => none
    | .acl _ :: _ => none

end LeanBatfish
