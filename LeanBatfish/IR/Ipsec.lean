import LeanBatfish.IR.Acl

/-!
# IPsec

The IPsec parts of Batfish's IR. Two gateways (the *peers*) protect traffic between them in
two phases: IKE phase 1 authenticates them to each other (with a key and a proposal of
algorithms) and IPsec phase 2 agrees on how packets are protected (a proposal of
protocols and algorithms). Each `IpsecPeerConfig` is one end of a would-be session: its
local address, and either a tunnel interface (route-based VPN: whatever is routed into the
interface is protected) or an ACL (a crypto map, policy-based VPN: the packets it permits
on the source interface are protected).

Algorithms and groups are kept as Batfish's enum names (`AES_256_CBC`, `GROUP14`, ...):
Batfish only compares them for equality, and `Confidential` (in `Semantics/Ipsec`) reads
the cipher's name.
-/

namespace LeanBatfish

/-- A key for IKE phase 1 (`IkePhase1Key`). Batfish keeps a hash of the key, not the key. -/
structure IkePhase1Key where
  /-- `PRE_SHARED_KEY_UNENCRYPTED`, `PRE_SHARED_KEY_ENCRYPTED` (stored encrypted, so it
  cannot be compared) or `RSA_PUB_KEY`. -/
  keyType : String
  keyHash : Option String
  remoteIdentity : Option IpSpace
  localInterface : String
  deriving Inhabited, Repr

/-- A proposal of algorithms for IKE phase 1 (`IkePhase1Proposal`). -/
structure IkePhase1Proposal where
  name : String
  authenticationMethod : Option String
  diffieHellmanGroup : Option String
  encryptionAlgorithm : Option String
  hashingAlgorithm : Option String
  lifetimeSeconds : Option Nat
  deriving DecidableEq, Inhabited, Repr

/-- The IKE phase-1 settings toward a peer (`IkePhase1Policy`): proposals by name, in order
of preference, and the key. -/
structure IkePhase1Policy where
  name : String
  ikePhase1Key : Option IkePhase1Key
  ikePhase1Proposals : Array String
  /-- The peers this policy is for; read for dynamic peers. -/
  remoteIdentity : Option IpSpace
  localInterface : String
  deriving Inhabited, Repr

/-- A proposal for IPsec phase 2 (`IpsecPhase2Proposal`): how packets are protected. -/
structure IpsecPhase2Proposal where
  /-- The integrity algorithm, e.g. `HMAC_SHA1_96`. -/
  authenticationAlgorithm : Option String
  /-- The cipher, e.g. `AES_256_CBC`; `NULL` or absent means no encryption. -/
  encryptionAlgorithm : Option String
  /-- `TUNNEL` (the whole packet is wrapped) or `TRANSPORT`. -/
  ipsecEncapsulationMode : String
  /-- `ESP` (encrypts and authenticates) and/or `AH` (authenticates only). -/
  protocols : Array String
  deriving DecidableEq, Hashable, Inhabited, Repr

/-- The IPsec phase-2 settings (`IpsecPhase2Policy`): proposals by name, in order of
preference, and the Diffie–Hellman groups for perfect forward secrecy. -/
structure IpsecPhase2Policy where
  pfsKeyGroups : Array String
  proposals : Array String
  deriving Inhabited, Repr

/-- Whether a peer configuration starts sessions toward a known address, or only answers
initiators that one of its IKE policies accepts (`IpsecStaticPeerConfig`,
`IpsecDynamicPeerConfig`). -/
inductive IpsecPeerKind
  | static (destinationAddress : Option Ip) (ikePhase1Policy : Option String)
  | dynamic (ikePhase1Policies : Array String)
  deriving Inhabited, Repr

/-- One end of an IPsec session (`IpsecPeerConfig`). -/
structure IpsecPeerConfig where
  kind : IpsecPeerKind
  /-- The address the session runs from: the source of the outer header. -/
  localAddress : Ip
  /-- The interface owning `localAddress`. -/
  sourceInterface : String
  /-- The tunnel interface, for a route-based VPN. -/
  tunnelInterface : Option String
  /-- The phase-2 policy, by name. -/
  ipsecPolicy : Option String
  /-- The crypto-map ACL selecting the packets to protect, for a policy-based VPN. -/
  policyAccessList : Option IpAccessList
  deriving Inhabited, Repr

end LeanBatfish
