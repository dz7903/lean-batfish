import LeanBatfish.Semantics.Forwarding.Acl

/-!
# IPsec sessions

Which IPsec peers can form a session, and what they agree on, as Batfish decides it from
the configurations (`IpsecUtil.initIpsecTopology` and the negotiation it calls):

* A *static* peer configuration with a destination address is paired with every peer
  configuration whose local address is that destination, except that a crypto-map peer
  never pairs with a tunnel peer. The static one is the *initiator*.
* IKE phase 1: the initiator's policy and the responder's (for a dynamic responder, the
  first of its policies whose remote identity contains the initiator's address) must have
  compatible proposals — the first pair, in the initiator's order, with equal
  authentication method, Diffie–Hellman group, cipher and hash — and keys that match.
* IPsec phase 2: the two phase-2 policies must share a PFS group and have equal
  proposals; the first, in the initiator's order, is the negotiated one.

Nothing here depends on reachability: whether the peers' packets get through is decided
by the data plane (`LeanBatfish.Model`).
-/

namespace LeanBatfish

/-- Whether a phase-2 proposal hides what it protects: ESP with a cipher. AH, and ESP with
the `NULL` cipher, only authenticate. -/
def IpsecPhase2Proposal.encrypts (p : IpsecPhase2Proposal) : Bool :=
  p.protocols.contains "ESP" &&
    match p.encryptionAlgorithm with
    | some c => c != "NULL"
    | none => false

end LeanBatfish

namespace LeanBatfish.Ipsec

/-- A peer configuration: the device and the configuration's name. -/
structure PeerId where
  host : String
  name : String
  deriving DecidableEq, Hashable, Inhabited, Repr

/-- What a pair of peers negotiates (`IpsecSession`); an absent value means that step
failed. -/
structure Session where
  ikeProposal : Option IkePhase1Proposal := none
  /-- Whether the phase-1 keys match (Batfish's negotiated key). -/
  keyMatches : Bool := false
  ipsecProposal : Option IpsecPhase2Proposal := none
  deriving Inhabited, Repr

/-- The negotiated phase-2 proposal if the session is established. -/
def Session.established (s : Session) : Option IpsecPhase2Proposal :=
  if s.ikeProposal.isSome && s.keyMatches then s.ipsecProposal else none

/-- `IkePhase1Proposal.isCompatibleWith`. -/
def ikeCompatible (a b : IkePhase1Proposal) : Bool :=
  a.authenticationMethod == b.authenticationMethod &&
  a.diffieHellmanGroup == b.diffieHellmanGroup &&
  a.encryptionAlgorithm == b.encryptionAlgorithm && a.hashingAlgorithm == b.hashingAlgorithm

/-- The first pair of compatible proposals, in the initiator's order; the initiator's
proposal is the negotiated one (`getMatchingIkeP1Proposal`). -/
def matchingIkeProposal (ic rc : Configuration) (mine theirs : Array String) :
    Option IkePhase1Proposal :=
  let mine := mine.filterMap ic.ikePhase1Proposals.find?
  let theirs := theirs.filterMap rc.ikePhase1Proposals.find?
  mine.find? fun a => theirs.any (ikeCompatible a)

def isPreSharedKey (t : String) : Bool :=
  t == "PRE_SHARED_KEY_ENCRYPTED" || t == "PRE_SHARED_KEY_UNENCRYPTED"

/-- Whether two phase-1 keys match (`negotiateIkePhase1Key`): two keys in plain text must
be equal; pre-shared keys that are stored encrypted cannot be compared and are taken to
match, as are two RSA keys. -/
def keysMatch (a b : IkePhase1Key) : Bool :=
  match a.keyHash, b.keyHash with
  | some ha, some hb =>
    if a.keyType == "PRE_SHARED_KEY_UNENCRYPTED" && b.keyType == "PRE_SHARED_KEY_UNENCRYPTED"
    then ha == hb
    else (isPreSharedKey a.keyType && isPreSharedKey b.keyType) ||
      (a.keyType == "RSA_PUB_KEY" && b.keyType == "RSA_PUB_KEY")
  | _, _ => false

/-- The first pair of equal phase-2 proposals, in the initiator's order
(`getMatchingIpsecP2Proposal`). -/
def matchingIpsecProposal (ic rc : Configuration) (mine theirs : Array String) :
    Option IpsecPhase2Proposal :=
  let mine := mine.filterMap ic.ipsecPhase2Proposals.find?
  let theirs := theirs.filterMap rc.ipsecPhase2Proposals.find?
  mine.find? (theirs.contains ·)

/-- The responder's phase-1 policy toward an initiator at `initiatorIp`. -/
def responderPolicy (rc : Configuration) (r : IpsecPeerConfig) (initiatorIp : Ip) :
    Option IkePhase1Policy :=
  match r.kind with
  | .static _ policy => policy.bind rc.ikePhase1Policies.find?
  | .dynamic policies =>
    (policies.filterMap rc.ikePhase1Policies.find?).find? fun p =>
      match p.remoteIdentity with
      | some s => s.containsIp #[] initiatorIp ipSpaceFuel
      | none => false

/-- The session the static peer `i` of `ic` negotiates with peer `r` of `rc`
(`getIpsecSession`). -/
def session (ic rc : Configuration) (i r : IpsecPeerConfig) : Session := Id.run do
  let .static _ iPolicyName := i.kind | return {}
  let (some iPolicy, some rPolicy) :=
      (iPolicyName.bind ic.ikePhase1Policies.find?, responderPolicy rc r i.localAddress)
    | return {}
  let ikeProposal := matchingIkeProposal ic rc iPolicy.ikePhase1Proposals rPolicy.ikePhase1Proposals
  let keyMatches := ikeProposal.isSome &&
    match iPolicy.ikePhase1Key, rPolicy.ikePhase1Key with
    | some a, some b => keysMatch a b
    | _, _ => false
  if !keyMatches then return { ikeProposal }
  let (some iP2, some rP2) :=
      (i.ipsecPolicy.bind ic.ipsecPhase2Policies.find?, r.ipsecPolicy.bind rc.ipsecPhase2Policies.find?)
    | return { ikeProposal, keyMatches }
  if !iP2.pfsKeyGroups.any (rP2.pfsKeyGroups.contains ·) then return { ikeProposal, keyMatches }
  return { ikeProposal, keyMatches,
           ipsecProposal := matchingIpsecProposal ic rc iP2.proposals rP2.proposals }

/-- An edge of the IPsec topology: an initiator, a responder, and their session. -/
structure Edge where
  initiator : PeerId
  responder : PeerId
  session : Session
  deriving Inhabited

/-- All peer configurations of the network. -/
def peers (configs : Array Configuration) : Array (PeerId × Configuration × IpsecPeerConfig) :=
  configs.flatMap fun c => c.ipsecPeerConfigs.map fun (name, p) => ({ host := c.hostname, name }, c, p)

/-- The IPsec topology Batfish computes from the configurations
(`IpsecUtil.initIpsecTopology`). Peers behind NAT are not paired: LeanBatfish does not
read NAT. -/
def topology (configs : Array Configuration) : Array Edge :=
  let all := peers configs
  all.flatMap fun (iId, ic, i) =>
    match i.kind with
    | .static (some dst) _ =>
      (all.filter fun (rId, _, r) =>
          r.localAddress == dst && rId != iId && i.tunnelInterface.isSome == r.tunnelInterface.isSome)
        |>.map fun (rId, rc, r) => { initiator := iId, responder := rId, session := session ic rc i r }
    | _ => #[]

end LeanBatfish.Ipsec
