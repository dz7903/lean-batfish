import networks.«ipsec-vpn».Model
import LeanBatfish.Reasoning.Forwarding

/-!
# Properties of the `ipsec-vpn` network

Three networks of Cisco routers: site A (`a1`, `a2` and the gateway `gwa`), site C (`c1` and
the gateway `gwc`), and between them a provider B (`b1`, `b2`, running OSPF) that the sites do
not trust. The gateways join the sites with a route-based IPsec tunnel: `Tunnel0` on each,
from `gwa` at 203.0.113.1 to `gwc` at 198.51.100.1, protected with ESP and AES-256. Site A is
10.1.0.0/16 and site C 10.3.0.0/16; the sites and gateways route statically, and each gateway
sends the other site's space into the tunnel.

What is proved, for every packet sent by a router of A to an address in C of a router of C:

* At any time, for any schedule of updates and anything peers outside announce: whenever
  the packet is at a router of B, it is encrypted — wrapped by IPsec with a cipher, from
  `gwa` to `gwc` — and it never leaves the network in the clear (`encrypted_in_B`,
  `not_out_in_clear`). Only `gwa` wraps it and only `gwc` unwraps it (`only_gateways_wrap`).
  Nothing is assumed of B's routers: they may forward it anywhere.
* At convergence, the tunnel is up and the packet arrives (`tunnel_up`, `flows_arrive`).

The properties depend on the configuration: if `gwa` did not route C's space into the tunnel,
its default route would take the packets to B in the clear (`leaky_in_clear`).
-/

namespace Networks.IpsecVpn

open LeanBatfish Model

/-! ## The sites and the packets -/

def host (i : Fin network.size) : String := network.routers[i].config.hostname

def siteA : List String := ["a1", "a2", "gwa"]
def siteB : List String := ["b1", "b2"]
def siteC : List String := ["c1", "gwc"]

/-- The address space of site C. -/
def spaceC : Prefix := Prefix.make (.ofOctets 10 3 0 0) ⟨16, by decide⟩

/-- The gateways' addresses toward B: the ends of the tunnel. -/
def gwaAddress : Ip := .ofOctets 203 0 113 1
def gwcAddress : Ip := .ofOctets 198 51 100 1

/-- Packet `p`, sent by router `i` of site A, to an address in C's space of router `c` of site
C. -/
def Flow (i c : Fin network.size) (p : Packet) : Prop :=
  host i ∈ siteA ∧ host c ∈ siteC ∧
    ∃ src ∈ network.routers[i].addresses, ∃ dst ∈ network.routers[c].addresses,
      spaceC.containsIp dst = true ∧ p = .ip src dst

/-- All of them. -/
def flows : List (Fin network.size × Fin network.size × Packet) :=
  (List.finRange network.size).flatMap fun i => (List.finRange network.size).flatMap fun c =>
    if host i ∈ siteA ∧ host c ∈ siteC then
      network.routers[i].addresses.toList.flatMap fun src =>
        (network.routers[c].addresses.toList.filter spaceC.containsIp).map fun dst =>
          (i, c, .ip src dst)
    else []

theorem mem_flows {i c : Fin network.size} {p : Packet} (h : Flow i c p) : (i, c, p) ∈ flows := by
  obtain ⟨ha, hc, src, hsrc, dst, hdst, hin, rfl⟩ := h
  simp only [flows, List.mem_flatMap, List.mem_finRange, true_and]
  refine ⟨i, c, ?_⟩
  simp only [ha, hc, and_self, ↓reduceIte, List.mem_flatMap, List.mem_map, List.mem_filter,
    Array.mem_toList_iff]
  exact ⟨src, hsrc, dst, ⟨hdst, hin⟩, rfl⟩

/-- `q` is `p` hidden by the tunnel: protected by IPsec with a cipher, in an outer header from
`gwa` to `gwc`. -/
def Hidden (p q : Packet) : Prop :=
  ∃ proposal : IpsecPhase2Proposal, proposal.encrypts = true ∧ q = .ipsec gwaAddress gwcAddress proposal p

def hidden (p : Packet) : Packet → Bool
  | .ipsec src dst proposal inner =>
    src == gwaAddress && dst == gwcAddress && proposal.encrypts && inner == p
  | _ => false

theorem hidden_spec {p q : Packet} (h : hidden p q = true) : Hidden p q := by
  cases q with
  | ipsec src dst proposal inner =>
    simp only [hidden, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, he⟩, rfl⟩ := h
    exact ⟨proposal, he, rfl⟩
  | _ => simp [hidden] at h

/-- The gateways own the ends of the tunnel. -/
theorem tunnel_ends : ∀ i : Fin network.size,
    (network.routers[i].owns gwaAddress = true ↔ host i = "gwa") ∧
    (network.routers[i].owns gwcAddress = true ↔ host i = "gwc") := by
  native_decide

/-! ## At any time

The routers of A and C, gateways included, route statically, so each stays among a few main
RIBs (`Network.anyTime`); B's routers may do anything that does not change a packet. The
properties are checked on every way the routers may forward, for every flow. -/

/-- The routers that are not B's. -/
def trusted (i : Nat) : Bool :=
  match network.routers[i]? with
  | some r => r.config.hostname ∉ siteB
  | none => true

/-- What the property says of a router and a packet: at B the packet is hidden, and in the
clear it does not leave the network. -/
def safe (p : Packet) (j : Fin network.size) (q : Packet) : Bool :=
  (host j ∉ siteB || hidden p q) && (q != p || !(network.anyTime trusted j q).contains .exit)

/-- What the property says of a hop: only `gwa` wraps the packet, only `gwc` unwraps it. -/
def gatewayHop (p : Packet) (j : Fin network.size) (q : Packet) (_ : Fin network.size)
    (r : Packet) : Bool :=
  (!(q == p && r != p) || host j == "gwa") && (!(q != p && r == p) || host j == "gwc")

theorem anyTime_check : network.anyTimeCheck trusted = true := by native_decide

theorem flows_checked :
    flows.all (fun (i, _, p) => (network.anyTime trusted).checkAlong (safe p) (gatewayHop p) i p 16) =
      true := by
  native_decide

theorem along {i c : Fin network.size} {p : Packet} (hf : Flow i c p) (ψ : Theory.Schedule network.size)
    (env : network.system.Env) (t : Nat) {j : Fin network.size} {q : Packet}
    (h : (network.dataPlane (network.system.run ψ env network.init t)).Path i p j q) :
    safe p j q = true ∧ ∀ k r, .forward k r ∈ network.dataPlane (network.system.run ψ env network.init t) j q →
      gatewayHop p j q k r = true :=
  Network.along_always anyTime_check (List.all_eq_true.mp flows_checked _ (mem_flows hf)) ψ env t h

/-- Whenever a packet from A to C is at a router of B, it is encrypted: wrapped by IPsec with
a cipher, from `gwa` to `gwc`. -/
theorem encrypted_in_B {i c : Fin network.size} {p : Packet} (hf : Flow i c p)
    (ψ : Theory.Schedule network.size) (env : network.system.Env) (t : Nat) {j : Fin network.size}
    {q : Packet} (h : (network.dataPlane (network.system.run ψ env network.init t)).Path i p j q)
    (hj : host j ∈ siteB) : Hidden p q := by
  have h1 := (along hf ψ env t h).1
  have hB : decide (host j ∉ siteB) = false := by simp [hj]
  simp only [safe, hB, Bool.false_or, Bool.and_eq_true] at h1
  exact hidden_spec h1.1

/-- In the clear, a packet from A to C never leaves the network. -/
theorem not_out_in_clear {i c : Fin network.size} {p : Packet} (hf : Flow i c p)
    (ψ : Theory.Schedule network.size) (env : network.system.Env) (t : Nat) {j : Fin network.size}
    (h : (network.dataPlane (network.system.run ψ env network.init t)).Path i p j p) :
    .exit ∉ network.dataPlane (network.system.run ψ env network.init t) j p := by
  intro hexit
  have hmem := Network.hop_anyTime anyTime_check (Network.inOrbit_run anyTime_check ψ env t) j p hexit
  have := (along hf ψ env t h).1
  simp [safe] at this
  exact this.2 hmem

/-- Only `gwa` wraps a packet from A to C, and only `gwc` unwraps it. -/
theorem only_gateways_wrap {i c : Fin network.size} {p : Packet} (hf : Flow i c p)
    (ψ : Theory.Schedule network.size) (env : network.system.Env) (t : Nat) {j k : Fin network.size}
    {q r : Packet} (h : (network.dataPlane (network.system.run ψ env network.init t)).Path i p j q)
    (hk : .forward k r ∈ network.dataPlane (network.system.run ψ env network.init t) j q) :
    (q = p → r ≠ p → host j = "gwa") ∧ (q ≠ p → r = p → host j = "gwc") := by
  have := (along hf ψ env t h).2 k r hk
  simp only [gatewayHop, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq,
    Bool.and_eq_false_iff] at this
  constructor
  · intro hq hr
    rcases this.1 with h1 | h1
    · rcases h1 with h1 | h1
      · exact absurd hq (by simpa using h1)
      · exact absurd (by simpa using h1) hr
    · exact h1
  · intro hq hr
    rcases this.2 with h2 | h2
    · rcases h2 with h2 | h2
      · exact absurd (by simpa using h2) hq
      · exact absurd hr (by simpa using h2)
    · exact h2

/-! ## At convergence -/

/-- The synchronous iteration from empty tables reaches `converged`... -/
theorem converged_reached :
    ∃ t, converged = network.system.iterate network.quiet network.init t :=
  network.converge_eq_iterate network.quiet 1000

/-- ...and it is a stable state. -/
theorem converged_stable : network.system.Stable network.quiet converged := by
  native_decide

/-- The tunnel is up on both gateways. -/
theorem tunnel_up : ∀ i : Fin network.size,
    (host i = "gwa" → (converged i).ipsec = #[("Tunnel0", gwcAddress)]) ∧
    (host i = "gwc" → (converged i).ipsec = #[("Tunnel0", gwaAddress)]) := by
  native_decide

/-- Every packet from A to C arrives. -/
theorem flows_arrive {i c : Fin network.size} {p : Packet} (hf : Flow i c p) :
    (network.dataPlane converged).Delivers p i c := by
  have h : flows.all (fun (i, c, p) => (network.dataPlane converged).canDeliver p i c) = true := by
    native_decide
  exact Theory.DataPlane.delivers_of_canDeliver _ (List.all_eq_true.mp h _ (mem_flows hf))

/-! ## Without the route into the tunnel -/

/-- The snapshot with `gwa`'s static routes for C's space removed: the one into the tunnel and
its `Null0` backup. -/
def leakySnapshot : Snapshot :=
  { snapshot with configs := snapshot.configs.map fun c =>
      if c.hostname != "gwa" then c else
      { c with vrfs := c.vrfs.map fun (name, v) =>
          (name, { v with staticRoutes := v.staticRoutes.filter (·.network != spaceC) }) } }

def leaky : Network := Network.ofSnapshot leakySnapshot

/-- The state the leaky network converges to. -/
def leakyConverged : Fin leaky.size → RouterState := leaky.ofArray (leaky.converge leaky.quiet)

/-- There, `a1`'s packets to `c1` reach B in the clear. -/
theorem leaky_in_clear :
    ∃ i j, leaky.find? "a1" = some i ∧ leaky.find? "b1" = some j ∧
      (leaky.dataPlane leakyConverged).Path i (.ip (.ofOctets 10 1 1 1) (.ofOctets 10 3 1 1)) j
        (.ip (.ofOctets 10 1 1 1) (.ofOctets 10 3 1 1)) := by
  let p : Packet := .ip (.ofOctets 10 1 1 1) (.ofOctets 10 3 1 1)
  have h : (match leaky.find? "a1", leaky.find? "b1" with
      | some i, some j => decide ((j, p) ∈ (leaky.dataPlane leakyConverged).reachWithin i p leaky.size)
      | _, _ => false) = true := by native_decide
  split at h
  · rename_i i j hi hj
    exact ⟨i, j, hi, hj, (leaky.dataPlane leakyConverged).path_of_mem_reachWithin
      (k := leaky.size) (of_decide_eq_true h)⟩
  · cases h

end Networks.IpsecVpn
