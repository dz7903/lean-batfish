import networks.«ipsec-negotiation».Model

/-!
# Properties of the `ipsec-negotiation` network

A Cisco hub with seven spokes, each on its own link `172.20.N.0/30` (hub `.1`, spoke `.2`),
with loopbacks `10.0.0.1` (hub) and `10.0.N.1` (spoke `N`). Each spoke tries IPsec with the
hub in its own way:

| spoke | how | outcome (Batfish's `ipsecSessionStatus`) |
|---|---|---|
| `spoke1` | route-based (`Tunnel1` on the hub) | established |
| `spoke2` | route-based, another pre-shared key | IKE phase-1 key mismatch |
| `spoke3` | route-based, AES-128 instead of AES-256 | IPsec phase 2 fails |
| `spoke4` | route-based, DH group 2 instead of 14 | IKE phase 1 fails |
| `spoke5` | crypto map on both ends | established |
| `spoke6` | Junos, route-based (`st0.0`) | established |
| `spoke7` | crypto map toward the hub's dynamic crypto map | established |

The hub also has `Tunnel9` toward `192.0.2.99`, which no device has (missing end point).

Proved at convergence, by evaluation: which sessions are up, and what happens to the hub's
packets toward each spoke's loopback — through an established session they arrive, wrapped
on the link and unwrapped by the spoke; through a failed one they are dropped at the hub,
never sent in the clear.
-/

namespace Networks.IpsecNegotiation

open LeanBatfish Model

def host (i : Fin network.size) : String := network.routers[i].config.hostname

/-- The sessions up at convergence, by router: the hub has four, one per established spoke. -/
theorem sessions_up :
    (List.finRange network.size).filterMap (fun i =>
        if (converged i).ipsec.isEmpty then none else some (host i, (converged i).ipsec.size)) =
      [("hub", 4), ("spoke1", 1), ("spoke5", 1), ("spoke6", 1), ("spoke7", 1)] := by
  native_decide

/-- A packet from the hub's loopback to spoke `n`'s. -/
def toSpoke (n : Nat) : Packet := .ip (.ofOctets 10 0 0 1) (.ofOctets 10 0 n.toUInt8 1)

/-- The packet wrapped by the session between the hub and spoke `n`, on their link
`172.20.n.0/30`, with a cipher. -/
def wrappedOnLink (n : Nat) : Packet → Bool
  | .ipsec src dst proposal inner =>
    src == .ofOctets 172 20 n.toUInt8 1 && dst == .ofOctets 172 20 n.toUInt8 2 &&
      proposal.encrypts && inner == toSpoke n
  | _ => false

/-- Whether everything the hub's packet toward spoke `n` can become, at convergence, satisfies
`Q`. -/
def everywhere (n : Nat) (Q : Fin network.size → Packet → Bool) : Bool :=
  match network.find? "hub" with
  | some i => (network.dataPlane converged).checkAlong Q (fun _ _ _ _ => true) i (toSpoke n)
      network.size
  | none => false

theorem of_everywhere {n : Nat} {Q : Fin network.size → Packet → Bool} (h : everywhere n Q = true)
    {i j : Fin network.size} {q : Packet} (hi : network.find? "hub" = some i)
    (hp : (network.dataPlane converged).Path i (toSpoke n) j q) : Q j q = true := by
  rw [everywhere, hi] at h
  exact ((network.dataPlane converged).along_of_checkAlong h hp).1

/-- Through the established sessions (route-based to `spoke1`, crypto maps to `spoke5` and
`spoke7`, Junos to `spoke6`) the hub's packets arrive... -/
theorem established_deliver :
    [1, 5, 6, 7].all (fun n => network.checkDelivers converged (toSpoke n) "hub" s!"spoke{n}") := by
  native_decide

/-- ...and outside the hub they are only on the link, wrapped with a cipher. -/
theorem established_wrapped : [1, 5, 6, 7].all (fun n => everywhere n fun j q =>
    (host j == "hub" && q == toSpoke n) || (host j == s!"spoke{n}" && wrappedOnLink n q)) := by
  native_decide

/-- Toward the spokes whose sessions fail, and toward the missing end point, the hub's packets
never leave the hub: the tunnel interfaces drop them. -/
theorem failed_stay_at_hub :
    [2, 3, 4, 9].all (fun n => everywhere n fun j _ => host j == "hub") := by
  native_decide

end Networks.IpsecNegotiation
