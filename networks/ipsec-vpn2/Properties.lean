import networks.«ipsec-vpn2».Model
import LeanBatfish.Reasoning.Forwarding

/-!
# Properties of the `ipsec-vpn2` network

Five networks of Cisco routers, in a chain of trust: two sites, A (`a1`, `a2` and the gateway
`gwa`) and E (`e1`, `e2` and the gateway `gwe`); two regional networks, B (`b1`, `b2` and the
gateway `gwb`) and D (`d1` and the gateway `gwd`); and a core C (`c1`, `c2`, `c3`, a triangle
running OSPF) that joins the regions and carries their address spaces, 100.64.1.0/24 and
100.64.2.0/24 (`c1` and `c3` announce them from static routes).

```
  a1 ─┐       ┌─ b1 ─┐              ┌─ c2 ─┐                          ┌─ e1
  │   gwa ────┤      ├─ gwb ── c1 ──┤      ├── c3 ── gwd ── d1 ── gwe ┤
  a2 ─┘       └─ b2 ─┘              └──────┘                          └─ e2
```

`gwa` is dual-homed to B, and B's two routers both reach `gwb`; the core is a triangle. There
are two route-based IPsec tunnels (Cisco IOS VTIs, ESP):

* the site tunnel, from `gwa` (its loopback 100.64.1.1, in B's space) to `gwe` (100.64.2.1, in
  D's space), with AES-256: each gateway sends the other site's space into it;
* the region tunnel, from `gwb` (203.0.113.1) to `gwd` (198.51.100.1), across the core, with
  AES-128: each gateway sends the other region's space into it, rather than to the core.

The site tunnel's ends are in the regions' spaces, so the region tunnel carries it: a packet
from A to E is encrypted by `gwa`, encrypted again by `gwb`, decrypted once by `gwd` and once
more by `gwe`. Site A is 10.1.0.0/16 and site E 10.5.0.0/16. The sites and the four gateways
route statically.

What is proved, for every packet sent by a router of A to an address in E of a router of E:

* At any time, for any schedule of updates and anything peers outside announce: whenever the
  packet is at a router of C, it is encrypted twice — by the site tunnel inside and by the
  region tunnel outside (`doubly_encrypted_in_C`); in B and D it is encrypted at least by the
  site tunnel (`encrypted_in_B_and_D`); it is in the clear only in the sites and never leaves
  the network in the clear (`clear_only_in_sites`, `not_out_in_clear`). Only the gateways add
  or remove a layer: `gwa` the first and `gwb` the second, `gwd` takes the second off and `gwe`
  the first (`only_gateways_rewrap`). Nothing is assumed of the routers inside B, C and D
  (`b1`, `b2`, `c1`, `c2`, `c3`, `d1`): they may forward the packet anywhere.
* At convergence, both tunnels are up and the packet arrives (`tunnels_up`, `flows_arrive`).

Double encryption depends on `gwb`'s configuration: if it did not route D's space into the
region tunnel, packets from A to E would still get through, since the core routes D's space,
but they would cross it encrypted only once (`leaky_singly_in_C`).
-/

namespace Networks.IpsecVpn2

open LeanBatfish Model

/-! ## The networks and the packets -/

def host (i : Fin network.size) : String := network.routers[i].config.hostname

def siteA : List String := ["a1", "a2", "gwa"]
def regionB : List String := ["b1", "b2", "gwb"]
def core : List String := ["c1", "c2", "c3"]
def regionD : List String := ["d1", "gwd"]
def siteE : List String := ["e1", "e2", "gwe"]

/-- The address space of site E. -/
def spaceE : Prefix := Prefix.make (.ofOctets 10 5 0 0) ⟨16, by decide⟩

/-- The ends of the site tunnel. -/
def gwaAddress : Ip := .ofOctets 100 64 1 1
def gweAddress : Ip := .ofOctets 100 64 2 1

/-- The ends of the region tunnel. -/
def gwbAddress : Ip := .ofOctets 203 0 113 1
def gwdAddress : Ip := .ofOctets 198 51 100 1

/-- Packet `p`, sent by router `i` of site A, to an address in E's space of router `e` of site
E. -/
def Flow (i e : Fin network.size) (p : Packet) : Prop :=
  host i ∈ siteA ∧ host e ∈ siteE ∧
    ∃ src ∈ network.routers[i].addresses, ∃ dst ∈ network.routers[e].addresses,
      spaceE.containsIp dst = true ∧ p = .ip src dst

/-- All of them. -/
def flows : List (Fin network.size × Fin network.size × Packet) :=
  (List.finRange network.size).flatMap fun i => (List.finRange network.size).flatMap fun e =>
    if host i ∈ siteA ∧ host e ∈ siteE then
      network.routers[i].addresses.toList.flatMap fun src =>
        (network.routers[e].addresses.toList.filter spaceE.containsIp).map fun dst =>
          (i, e, .ip src dst)
    else []

theorem mem_flows {i e : Fin network.size} {p : Packet} (h : Flow i e p) : (i, e, p) ∈ flows := by
  obtain ⟨ha, he, src, hsrc, dst, hdst, hin, rfl⟩ := h
  simp only [flows, List.mem_flatMap, List.mem_finRange, true_and]
  refine ⟨i, e, ?_⟩
  simp only [ha, he, and_self, ↓reduceIte, List.mem_flatMap, List.mem_map, List.mem_filter,
    Array.mem_toList_iff]
  exact ⟨src, hsrc, dst, ⟨hdst, hin⟩, rfl⟩

/-- `q` is `p` encrypted by a tunnel from `src` to `dst`: protected by IPsec with a cipher, in
an outer header from `src` to `dst`. -/
def Encrypted (src dst : Ip) (p q : Packet) : Prop :=
  ∃ proposal : IpsecPhase2Proposal, proposal.encrypts = true ∧ q = .ipsec src dst proposal p

/-- `q` is `p` encrypted by the site tunnel. -/
def Hidden (p q : Packet) : Prop := Encrypted gwaAddress gweAddress p q

/-- `q` is `p` encrypted twice: by the site tunnel, and the result by the region tunnel. -/
def DoublyHidden (p q : Packet) : Prop :=
  ∃ q', Hidden p q' ∧ Encrypted gwbAddress gwdAddress q' q

def encrypted (src dst : Ip) (p : Packet) : Packet → Bool
  | .ipsec s d proposal inner => s == src && d == dst && proposal.encrypts && inner == p
  | _ => false

def hidden (p : Packet) : Packet → Bool := encrypted gwaAddress gweAddress p

def doublyHidden (p : Packet) : Packet → Bool
  | .ipsec s d proposal inner =>
    s == gwbAddress && d == gwdAddress && proposal.encrypts && hidden p inner
  | _ => false

theorem encrypted_spec {src dst : Ip} {p q : Packet} (h : encrypted src dst p q = true) :
    Encrypted src dst p q := by
  cases q with
  | ipsec s d proposal inner =>
    simp only [encrypted, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, he⟩, rfl⟩ := h
    exact ⟨proposal, he, rfl⟩
  | _ => simp [encrypted] at h

theorem doublyHidden_spec {p q : Packet} (h : doublyHidden p q = true) : DoublyHidden p q := by
  cases q with
  | ipsec s d proposal inner =>
    simp only [doublyHidden, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, he⟩, hi⟩ := h
    exact ⟨inner, encrypted_spec hi, proposal, he, rfl⟩
  | _ => simp [doublyHidden] at h

/-- How many tunnels a packet is wrapped in. -/
def layers : Packet → Nat
  | .ip .. => 0
  | .gre _ _ inner | .ipsec _ _ _ inner => layers inner + 1

/-- The gateways own the ends of the tunnels. -/
theorem tunnel_ends : ∀ i : Fin network.size,
    (network.routers[i].owns gwaAddress = true ↔ host i = "gwa") ∧
    (network.routers[i].owns gweAddress = true ↔ host i = "gwe") ∧
    (network.routers[i].owns gwbAddress = true ↔ host i = "gwb") ∧
    (network.routers[i].owns gwdAddress = true ↔ host i = "gwd") := by
  native_decide

/-! ## At any time

The routers of the sites and the four gateways route statically, so each stays among a few
main RIBs (`Network.anyTime`); the routers inside B, C and D may do anything that does not
change a packet. The properties are checked on every way the routers may forward, for every
flow. -/

/-- The routers that are trusted: those of the sites, and the gateways of the regions. -/
def trusted (i : Nat) : Bool :=
  match network.routers[i]? with
  | some r => r.config.hostname ∈ siteA ++ siteE ++ ["gwb", "gwd"]
  | none => true

/-- What the property says of a router and a packet: in C the packet is encrypted twice, in B
and D at least by the site tunnel, and in the clear it is only in the sites and does not leave
the network. -/
def safe (p : Packet) (j : Fin network.size) (q : Packet) : Bool :=
  (host j ∉ core || doublyHidden p q) &&
  (host j ∉ regionB ++ regionD || hidden p q || doublyHidden p q) &&
  (q != p || host j ∈ siteA ++ siteE) &&
  (q != p || !(network.anyTime trusted j q).contains .exit)

/-- Where a packet gains or loses a layer: `gwa` wraps the plain packet and `gwb` wraps it
again; `gwd` unwraps the outer layer and `gwe` the inner one. -/
def rewraps : List (String × Nat × Nat) :=
  [("gwa", 0, 1), ("gwb", 1, 2), ("gwd", 2, 1), ("gwe", 1, 0)]

/-- What the property says of a hop: the packet keeps its layers, or the hop is one of
`rewraps`. -/
def gatewayHop (j : Fin network.size) (q : Packet) (_ : Fin network.size) (r : Packet) : Bool :=
  layers q == layers r || rewraps.contains (host j, layers q, layers r)

theorem anyTime_check : network.anyTimeCheck trusted = true := by native_decide

theorem flows_checked :
    flows.all (fun (i, _, p) => (network.anyTime trusted).checkAlong (safe p) gatewayHop i p 32) =
      true := by
  native_decide

theorem along {i e : Fin network.size} {p : Packet} (hf : Flow i e p) (ψ : Theory.Schedule network.size)
    (env : network.system.Env) (t : Nat) {j : Fin network.size} {q : Packet}
    (h : (network.dataPlane (network.system.run ψ env network.init t)).Path i p j q) :
    safe p j q = true ∧ ∀ k r, .forward k r ∈ network.dataPlane (network.system.run ψ env network.init t) j q →
      gatewayHop j q k r = true :=
  Network.along_always anyTime_check (List.all_eq_true.mp flows_checked _ (mem_flows hf)) ψ env t h

/-- Whenever a packet from A to E is at a router of C, it is encrypted twice: by the site
tunnel, from `gwa` to `gwe`, and the result by the region tunnel, from `gwb` to `gwd`. -/
theorem doubly_encrypted_in_C {i e : Fin network.size} {p : Packet} (hf : Flow i e p)
    (ψ : Theory.Schedule network.size) (env : network.system.Env) (t : Nat) {j : Fin network.size}
    {q : Packet} (h : (network.dataPlane (network.system.run ψ env network.init t)).Path i p j q)
    (hj : host j ∈ core) : DoublyHidden p q := by
  have h1 := (along hf ψ env t h).1
  have hC : decide (host j ∉ core) = false := by simp [hj]
  simp only [safe, hC, Bool.false_or, Bool.and_eq_true] at h1
  exact doublyHidden_spec h1.1.1.1

/-- Whenever a packet from A to E is at a router of B or D, it is encrypted by the site tunnel,
and maybe again by the region tunnel (at `gwb` and `gwd`). -/
theorem encrypted_in_B_and_D {i e : Fin network.size} {p : Packet} (hf : Flow i e p)
    (ψ : Theory.Schedule network.size) (env : network.system.Env) (t : Nat) {j : Fin network.size}
    {q : Packet} (h : (network.dataPlane (network.system.run ψ env network.init t)).Path i p j q)
    (hj : host j ∈ regionB ∨ host j ∈ regionD) : Hidden p q ∨ DoublyHidden p q := by
  have h1 := (along hf ψ env t h).1
  have hBD : decide (host j ∉ regionB ++ regionD) = false := by simp [hj]
  simp only [safe, hBD, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true] at h1
  rcases h1.1.1.2 with h2 | h2
  · exact .inl (encrypted_spec h2)
  · exact .inr (doublyHidden_spec h2)

/-- A packet from A to E is in the clear only at routers of the sites. -/
theorem clear_only_in_sites {i e : Fin network.size} {p : Packet} (hf : Flow i e p)
    (ψ : Theory.Schedule network.size) (env : network.system.Env) (t : Nat) {j : Fin network.size}
    (h : (network.dataPlane (network.system.run ψ env network.init t)).Path i p j p) :
    host j ∈ siteA ∨ host j ∈ siteE := by
  have := (along hf ψ env t h).1
  simp only [safe, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
    List.mem_append] at this
  exact this.1.2

/-- In the clear, a packet from A to E never leaves the network. -/
theorem not_out_in_clear {i e : Fin network.size} {p : Packet} (hf : Flow i e p)
    (ψ : Theory.Schedule network.size) (env : network.system.Env) (t : Nat) {j : Fin network.size}
    (h : (network.dataPlane (network.system.run ψ env network.init t)).Path i p j p) :
    .exit ∉ network.dataPlane (network.system.run ψ env network.init t) j p := by
  intro hexit
  have hmem := Network.hop_anyTime anyTime_check (Network.inOrbit_run anyTime_check ψ env t) j p hexit
  have := (along hf ψ env t h).1
  simp [safe] at this
  exact this.2 hmem

/-- Only the gateways add or remove a layer of a packet from A to E: `gwa` wraps it, `gwb`
wraps it again, `gwd` takes the outer layer off and `gwe` the inner one. -/
theorem only_gateways_rewrap {i e : Fin network.size} {p : Packet} (hf : Flow i e p)
    (ψ : Theory.Schedule network.size) (env : network.system.Env) (t : Nat) {j k : Fin network.size}
    {q r : Packet} (h : (network.dataPlane (network.system.run ψ env network.init t)).Path i p j q)
    (hk : .forward k r ∈ network.dataPlane (network.system.run ψ env network.init t) j q)
    (hne : layers r ≠ layers q) : (host j, layers q, layers r) ∈ rewraps := by
  have := (along hf ψ env t h).2 k r hk
  simp only [gatewayHop, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at this
  exact this.resolve_left (Ne.symm hne)

/-! ## At convergence -/

/-- The synchronous iteration from empty tables reaches `converged`... -/
theorem converged_reached :
    ∃ t, converged = network.system.iterate network.quiet network.init t :=
  network.converge_eq_iterate network.quiet 1000

/-- ...and it is a stable state. -/
theorem converged_stable : network.system.Stable network.quiet converged := by
  native_decide

/-- Both tunnels are up, on all four gateways. -/
theorem tunnels_up : ∀ i : Fin network.size,
    (host i = "gwa" → (converged i).ipsec = #[("Tunnel0", gweAddress)]) ∧
    (host i = "gwe" → (converged i).ipsec = #[("Tunnel0", gwaAddress)]) ∧
    (host i = "gwb" → (converged i).ipsec = #[("Tunnel0", gwdAddress)]) ∧
    (host i = "gwd" → (converged i).ipsec = #[("Tunnel0", gwbAddress)]) := by
  native_decide

/-- Every packet from A to E arrives. -/
theorem flows_arrive {i e : Fin network.size} {p : Packet} (hf : Flow i e p) :
    (network.dataPlane converged).Delivers p i e := by
  have h : flows.all (fun (i, e, p) => (network.dataPlane converged).canDeliver p i e) = true := by
    native_decide
  exact Theory.DataPlane.delivers_of_canDeliver _ (List.all_eq_true.mp h _ (mem_flows hf))

/-! ## Without the route into the region tunnel -/

/-- D's address space, which `gwb` sends into the region tunnel. -/
def spaceD : Prefix := Prefix.make (.ofOctets 100 64 2 0) ⟨24, by decide⟩

/-- The snapshot with `gwb`'s static routes for D's space removed: the one into the tunnel and
its `Null0` backup. -/
def leakySnapshot : Snapshot :=
  { snapshot with configs := snapshot.configs.map fun c =>
      if c.hostname != "gwb" then c else
      { c with vrfs := c.vrfs.map fun (name, v) =>
          (name, { v with staticRoutes := v.staticRoutes.filter (·.network != spaceD) }) } }

def leaky : Network := Network.ofSnapshot leakySnapshot

/-- The state the leaky network converges to. -/
def leakyConverged : Fin leaky.size → RouterState := leaky.ofArray (leaky.converge leaky.quiet)

/-- There, the site tunnel still comes up, but `a1`'s packets to `e1` reach `c1` encrypted
only once: by the site tunnel, in an outer header that `gwb` sends to the core as it is. -/
theorem leaky_singly_in_C :
    ∃ i j, leaky.find? "a1" = some i ∧ leaky.find? "c1" = some j ∧ ∃ q,
      (leaky.dataPlane leakyConverged).Path i (.ip (.ofOctets 10 1 1 1) (.ofOctets 10 5 1 1)) j q ∧
        Hidden (.ip (.ofOctets 10 1 1 1) (.ofOctets 10 5 1 1)) q := by
  let p : Packet := .ip (.ofOctets 10 1 1 1) (.ofOctets 10 5 1 1)
  have h : (match leaky.find? "a1", leaky.find? "c1" with
      | some i, some j => ((leaky.dataPlane leakyConverged).reachWithin i p leaky.size).any
          fun x => x.1 == j && hidden p x.2
      | _, _ => false) = true := by native_decide
  split at h
  · rename_i i j hi hj
    obtain ⟨x, hx, hq⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, beq_iff_eq] at hq
    obtain ⟨rfl, hq⟩ := hq
    exact ⟨i, x.1, hi, hj, x.2, (leaky.dataPlane leakyConverged).path_of_mem_reachWithin hx,
      encrypted_spec hq⟩
  · cases h

end Networks.IpsecVpn2
