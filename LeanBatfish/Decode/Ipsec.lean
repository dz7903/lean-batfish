import LeanBatfish.Decode.Acl
import LeanBatfish.IR.Ipsec

/-!
# Decoding IPsec
-/

namespace LeanBatfish.Decode

open Lean ObjM

def ikePhase1Key : Decoder IkePhase1Key := object do
  pure {
    keyType := ← req "keyType" str
    keyHash := ← opt "keyHash" str
    remoteIdentity := ← opt "remoteIdentity" ipSpace
    localInterface := ← dflt "localInterface" "" str }

def ikePhase1Proposal : Decoder IkePhase1Proposal := object do
  pure {
    name := ← req "name" str
    authenticationMethod := ← opt "authenticationMethod" str
    diffieHellmanGroup := ← opt "diffieHellmanGroup" str
    encryptionAlgorithm := ← opt "encryptionAlgorithm" str
    hashingAlgorithm := ← opt "hashingAlgorithm" str
    lifetimeSeconds := ← opt "lifetimeSeconds" nat }

def ikePhase1Policy : Decoder IkePhase1Policy := object do
  -- Batfish's negotiation never reads the local identity.
  ignore "selfIdentity"
  pure {
    name := ← req "name" str
    ikePhase1Key := ← opt "ikePhase1Key" ikePhase1Key
    ikePhase1Proposals := ← dflt "ikePhase1Proposals" #[] (array str)
    remoteIdentity := ← opt "remoteIdentity" ipSpace
    localInterface := ← dflt "localInterface" "" str }

def ipsecPhase2Proposal : Decoder IpsecPhase2Proposal := object do
  pure {
    authenticationAlgorithm := ← opt "authenticationAlgorithm" str
    encryptionAlgorithm := ← opt "encryptionAlgorithm" str
    ipsecEncapsulationMode := ← req "ipsecEncapsulationMode" str
    protocols := ← dflt "protocols" #[] (array str) }

def ipsecPhase2Policy : Decoder IpsecPhase2Policy := object do
  pure {
    pfsKeyGroups := ← dflt "pfsKeyGroup" #[] (array str)
    proposals := ← dflt "proposals" #[] (array str) }

def ipsecPeerConfig : Decoder IpsecPeerConfig :=
  let common (kind : IpsecPeerKind) : ObjM IpsecPeerConfig := do
    pure {
      kind
      localAddress := ← req "localAddress" ip
      sourceInterface := ← req "sourceInterface" str
      tunnelInterface := ← opt "tunnelInterface" str
      ipsecPolicy := ← opt "ipsecPolicy" str
      policyAccessList := ← opt "policyAccessList" ipAccessList }
  byClass "IPsec peer configuration" [
    ("IpsecStaticPeerConfig", do
      let dst ← opt "destinationAddress" ip
      let policy ← opt "ikePhase1Policy" str
      common (.static dst policy)),
    ("IpsecDynamicPeerConfig", do
      common (.dynamic (← dflt "ikePhase1Policies" #[] (array str))))]

def tunnelConfiguration : Decoder TunnelConfiguration := object do
  pure {
    sourceAddress := ← req "sourceAddress" ip
    destinationAddress := ← req "destinationAddress" ip }

end LeanBatfish.Decode
