import networks.«example».Model
import LeanBatfish.Reasoning.Confinement

/-!
# Properties of the `example` network

Batfish's example network: three ASes of Cisco routers. AS2 has border, core and
distribution routers and a department router `as2dept1` (in its own AS 65001) with two hosts,
`host1` (2.128.0.101) and `host2` (2.128.1.101).

## The converged state

With nothing announced from outside, the network converges from empty tables to the state
`converged`, which is stable. Its data plane is the one Batfish computes (the differential
tests compare them). Facts about it are proved by evaluation (`native_decide`, which trusts
Lean's compiler in addition to its kernel).
-/

namespace Networks.Example

open LeanBatfish Model

/-- The synchronous iteration from empty tables reaches `converged`... -/
theorem converged_reached :
    ∃ t, converged = network.system.iterate network.quiet network.init t :=
  network.converge_eq_iterate network.quiet 1000

/-- ...and it is a stable state: no router changes when it updates. -/
theorem converged_stable : network.system.Stable network.quiet converged := by
  native_decide

/-- Once there, the network stays there whatever the schedule of updates. -/
theorem converged_forever (ψ : Theory.Schedule network.size) (t : Nat) :
    network.system.run ψ (fun _ => network.quiet) converged t = converged :=
  network.system.run_stable _ _ converged_stable ψ t

/-- `host1` reaches `host2`, through `as2dept1`. -/
theorem host1_reaches_host2 :
    network.Delivers converged (.ip (.ofOctets 2 128 0 101) (.ofOctets 2 128 1 101)) "host1" "host2" :=
  Network.delivers_of_check (by native_decide)

/-- `as3core1`, in AS3, reaches `host1`: its traffic crosses AS3 and AS2. -/
theorem as3core1_reaches_host1 :
    network.Delivers converged (.ip (.ofOctets 3 10 1 1) (.ofOctets 2 128 0 101)) "as3core1" "host1" :=
  Network.delivers_of_check (by native_decide)

/-- But `host1` does not reach `as3core1`'s loopback (3.10.1.1): AS3 announces only some of its
prefixes to its neighbors (its export policies `as3_to_as1` and `as3_to_as2`), not its
loopbacks, so no router outside AS3 has a route to it, and `as2dept1` drops the packets. -/
theorem host1_isolated_from_as3core1 :
    network.Isolated converged (.ip (.ofOctets 2 128 0 101) (.ofOctets 3 10 1 1)) "host1" "as3core1" :=
  Network.isolated_of_check (by native_decide)

/-! ## At any time: what announcements from outside can do to AS2

The snapshot configures BGP neighbors that are not in it: `xanadu` (5.6.7.8, AS 555) and
`bad-ebgp` (3.2.2.2, AS 666) on `as1border1`, and 10.14.22.4 on `as1border2`. In the model
they are peers outside the network, which may announce anything at any time. AS1 accepts
whatever they send. But AS1 and AS3 export to AS2 only a few prefixes (route maps
`as1_to_as2` and `as3_to_as2`), so AS2 never learns more than those, whatever the outside
announces and whatever the timing. (AS2 does not protect itself: its prefix list
`inbound_route_filter`, which would reject AS2's own space, is defined but never applied.)
-/

/-- The routers of AS2, including the department router `as2dept1`. -/
def as2 (k : Nat) : Bool := (network.routers[k]?).any (·.config.hostname.startsWith "as2")

/-- The networks AS2's routers hold in the converged state, and the default route. -/
def as2Known : List NetRange :=
  NetRange.ofPrefix ⟨⟨0⟩, 0⟩ ::
    ((List.finRange network.size).filter (as2 ·.val)).flatMap fun i =>
      (converged i).routes.toList.map (NetRange.ofPrefix ·.network)

/-- **AS2 is confined.** Whatever the peers outside the network announce, and whatever the
schedule, every route an AS2 router holds, at any time, is for a network AS2 holds at
convergence, or the default route. -/
theorem as2_confined (ψ : Theory.Schedule network.size) (env : network.system.Env) (t : Nat)
    (i : Fin network.size) (hi : as2 i = true) :
    Confined as2Known (network.system.run ψ env network.init t i) :=
  confined_always network as2 as2Known (by native_decide) ψ env t i hi

/-- `host2`'s address. -/
def host2Ip : Ip := .ofOctets 2 128 1 101

/-- A prefix that covers `host2` and is longer than `/24` is determined by its length. -/
theorem covers_host2 {n : Prefix} (h : n.containsIp host2Ip = true) :
    n = Prefix.make host2Ip n.len := by
  obtain ⟨⟨bits⟩, len⟩ := n
  simp only [Prefix.containsIp, beq_iff_eq] at h
  simp only [Prefix.make, h]

/-- **No hijack of `host2`.** At any time, whatever the outside announces, no AS2 router holds a
route that covers `host2` and is more specific than its `/24` subnet: such a route would
divert `host2`'s traffic. -/
theorem as2_no_more_specific (ψ : Theory.Schedule network.size) (env : network.system.Env)
    (t : Nat) (i : Fin network.size) (hi : as2 i = true)
    (r : Route) (hr : r ∈ (network.system.run ψ env network.init t i).routes)
    (hcover : r.network.containsIp host2Ip = true) : r.network.len.val ≤ 24 := by
  have hk := as2_confined ψ env t i hi r hr
  rw [covers_host2 hcover] at hk
  have hlens : ∀ len : Fin 33, 24 < len.val →
      knownB as2Known (Prefix.make host2Ip len) = false := by native_decide
  by_cases hlong : r.network.len.val ≤ 24
  · exact hlong
  · have := hlens r.network.len (by omega)
    rw [← Bool.not_eq_true, knownB_iff] at this
    exact absurd hk this

/-! ## A counterexample: AS2 trusts its neighbors

If AS1 itself misbehaves, nothing in AS2 stops it. Leave AS1 out of the model, so that its
sessions to AS2 become peers outside the network, and let it announce `2.128.1.0/25` (half of
`host2`'s subnet) with an AS1 community. `as2border1` takes the route (its import policy
`as1_to_as2` only checks the community), and sends `host2`'s traffic to AS1. -/

/-- The network without AS1: its sessions with AS2 come from outside. -/
def withoutAS1 : Network := Network.ofSnapshot snapshot (fun h => !h.startsWith "as1")

/-- The announcement: `2.128.1.0/25` from AS1, with community `1:1`. -/
def hijackRoute : Route := {
  network := Prefix.make (.ofOctets 2 128 1 0) ⟨25, by decide⟩
  nextHop := .ip (.ofOctets 10 12 11 1), protocol := .bgp, admin := 20
  bgp := some { asPath := #[AsSet.single 1], communities := .ofArray #[.standard (65536 + 1)],
                localPreference := 100 } }

/-- AS1 (at 10.12.11.1) announces the route to `as2border1`, all the time. -/
def hijackInput : Fin withoutAS1.size → Input := fun i =>
  if withoutAS1.routers[i].config.hostname == "as2border1" then
    #[(.ofOctets 10 12 11 1, hijackRoute)] else #[]

/-- The state the network reaches under the announcement, by synchronous iteration. -/
def hijacked : Fin withoutAS1.size → RouterState :=
  withoutAS1.ofArray (withoutAS1.converge hijackInput)

/-- Under the announcement, packets for `host2` sent to `as2border1` leave the network toward
AS1. -/
theorem hijack_diverts :
    (∃ t, hijacked = withoutAS1.system.iterate hijackInput withoutAS1.init t) ∧
    withoutAS1.Exits hijacked (.ip (.ofOctets 2 128 0 101) host2Ip) "as2border1" :=
  ⟨withoutAS1.converge_eq_iterate hijackInput 1000, Network.exits_of_check (by native_decide)⟩

end Networks.Example
