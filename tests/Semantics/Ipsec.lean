import LeanBatfish.Semantics.Ipsec

namespace Tests.Semantics.Ipsec
open LeanBatfish Ipsec

private def ip (s : String) : Ip := (Ip.parse? s).get!
private def pfx (s : String) : Prefix := (Prefix.parse? s).get!

/-! ## IP spaces and ACLs on addresses -/

private def named : NameMap IpSpace := #[("inside", .prefix (pfx "10.1.0.0/16"))]

#guard (IpSpace.reference "inside").containsIp named (ip "10.1.2.3") ipSpaceFuel
#guard !(IpSpace.reference "inside").containsIp named (ip "10.2.0.1") ipSpaceFuel
#guard !(IpSpace.reference "missing").containsIp named (ip "10.1.2.3") ipSpaceFuel
-- First match: 10.1.5.0/24 is denied before the rest of 10.1.0.0/16 is permitted.
#guard !(IpSpace.acl #[(.deny, .prefix (pfx "10.1.5.0/24")), (.permit, .reference "inside")]).containsIp
  named (ip "10.1.5.9") ipSpaceFuel
#guard (IpSpace.acl #[(.deny, .prefix (pfx "10.1.5.0/24")), (.permit, .reference "inside")]).containsIp
  named (ip "10.1.6.9") ipSpaceFuel

/-- `permit ip 10.1.0.0 0.0.255.255 10.3.0.0 0.0.255.255`, as a crypto-map ACL. -/
private def siteToSite : IpAccessList := {
  name := "SITES"
  lines := #[.expr .permit (.matchHeaderSpace {
    srcIps := some (.prefix (pfx "10.1.0.0/16")), dstIps := some (.prefix (pfx "10.3.0.0/16")) })] }

#guard siteToSite.permitsAddresses #[] ⟨ip "10.1.1.1", ip "10.3.1.1"⟩ == some true
#guard siteToSite.permitsAddresses #[] ⟨ip "10.1.1.1", ip "8.8.8.8"⟩ == some false

/-- A line on ports cannot be decided on addresses alone. -/
private def ssh : IpAccessList := {
  name := "SSH"
  lines := #[.expr .permit (.matchHeaderSpace { dstPorts := #[⟨22, 22⟩] })] }

#guard ssh.permitsAddresses #[] ⟨ip "10.1.1.1", ip "10.3.1.1"⟩ == none

/-! ## Negotiation -/

private def ike : IkePhase1Proposal := {
  name := "10", authenticationMethod := some "PRE_SHARED_KEYS", diffieHellmanGroup := some "GROUP14"
  encryptionAlgorithm := some "AES_256_CBC", hashingAlgorithm := some "SHA1", lifetimeSeconds := some 28800 }

private def key (hash : String) (type := "PRE_SHARED_KEY_UNENCRYPTED") : IkePhase1Key :=
  { keyType := type, keyHash := some hash, remoteIdentity := none, localInterface := "" }

private def esp (cipher : String) : IpsecPhase2Proposal := {
  authenticationAlgorithm := some "HMAC_SHA_256_128", encryptionAlgorithm := some cipher
  ipsecEncapsulationMode := "TUNNEL", protocols := #["ESP"] }

#guard keysMatch (key "a") (key "a")
#guard !keysMatch (key "a") (key "b")
-- A key stored encrypted cannot be compared, and is taken to match.
#guard keysMatch (key "a" "PRE_SHARED_KEY_ENCRYPTED") (key "b")
#guard (esp "AES_256_CBC").encrypts
#guard !(esp "NULL").encrypts
#guard !{ esp "AES_256_CBC" with protocols := #["AH"] }.encrypts

/-- A gateway at `local_` with a tunnel toward `remote`, its key and its phase-2 cipher. -/
private def gateway (host : String) (local_ remote : String) (k : String) (cipher : String) :
    Configuration :=
  let p1 : IkePhase1Policy :=
    { name := "P1", ikePhase1Key := some (key k), ikePhase1Proposals := #["10"]
      remoteIdentity := none, localInterface := "" }
  let peer : IpsecPeerConfig :=
    { kind := .static (some (ip remote)) (some "P1"), localAddress := ip local_
      sourceInterface := "Gi0", tunnelInterface := some "Tunnel0", ipsecPolicy := some "P2"
      policyAccessList := none }
  { (default : Configuration) with
    hostname := host
    ikePhase1Proposals := #[("10", ike)]
    ikePhase1Policies := #[("P1", p1)]
    ipsecPhase2Proposals := #[("T", esp cipher)]
    ipsecPhase2Policies := #[("P2", { pfsKeyGroups := #["GROUP14"], proposals := #["T"] })]
    ipsecPeerConfigs := #[("Tunnel0", peer)] }

private def status (configs : Array Configuration) : List (String × Bool × Bool × Bool) :=
  (topology configs).toList.map fun e =>
    (e.initiator.host, e.session.ikeProposal.isSome, e.session.keyMatches, e.session.ipsecProposal.isSome)

#guard status #[gateway "a" "1.0.0.1" "2.0.0.1" "k" "AES_256_CBC",
                gateway "c" "2.0.0.1" "1.0.0.1" "k" "AES_256_CBC"] ==
  [("a", true, true, true), ("c", true, true, true)]
#guard status #[gateway "a" "1.0.0.1" "2.0.0.1" "k" "AES_256_CBC",
                gateway "c" "2.0.0.1" "1.0.0.1" "other" "AES_256_CBC"] ==
  [("a", true, false, false), ("c", true, false, false)]
#guard status #[gateway "a" "1.0.0.1" "2.0.0.1" "k" "AES_256_CBC",
                gateway "c" "2.0.0.1" "1.0.0.1" "k" "AES_128_CBC"] ==
  [("a", true, true, false), ("c", true, true, false)]
-- No peer at the destination: no session.
#guard status #[gateway "a" "1.0.0.1" "2.0.0.1" "k" "AES_256_CBC"] == []

end Tests.Semantics.Ipsec
