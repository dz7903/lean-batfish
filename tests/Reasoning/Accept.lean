import LeanBatfish.Reasoning.Accept

namespace Tests.Reasoning
open LeanBatfish Policy

private def pfx (s : String) : Prefix := (Prefix.parse? s).get!

/-- A Cisco-style route map: permit the prefix list `pl`, after a community match; the
peer export policy calls a common policy that returns true, then the route map. -/
private def routeMap : RoutingPolicy := {
  name := "rm"
  statements := #[.ifThen (.conjunction #[.matchPrefixSet (.named "pl"),
      .matchCommunities .input (.hasCommunity .allStandard)])
    #[.traceable #[.setMetric (.literal 50), .static .returnTrue]]
    #[.static .returnLocalDefaultAction]] }

private def common : RoutingPolicy := { name := "common", statements := #[.static .returnTrue] }

private def peerExport : RoutingPolicy := {
  name := "peer"
  statements := #[.ifThen (.conjunction #[.call "common", .call "rm"])
    #[.static .exitAccept] #[.static .exitReject]] }

private def config : Configuration := { (default : Configuration) with
  routingPolicies := #[("common", common), ("peer", peerExport), ("rm", routeMap)]
  routeFilterLists := #[("pl", { name := "pl", lines := #[
    { action := .deny, ipWildcard := IpWildcard.ofPrefix (pfx "10.1.0.0/16"), lengthRange := ⟨16, 32⟩ },
    { action := .permit, ipWildcard := IpWildcard.ofPrefix (pfx "10.0.0.0/8"), lengthRange := ⟨8, 24⟩ }] })] }

-- The analysis bounds the peer policy to the permit line of `pl`: the community match and the
-- calls do not lose the bound, and the deny line is over-approximated away.
#guard (accCall config policyFuel peerExport).safe
#guard (accCall config policyFuel peerExport).accepted.within
  [NetRange.under (pfx "10.0.0.0/8") 8 24]
#guard !(accCall config policyFuel peerExport).accepted.within [NetRange.ofPrefix (pfx "10.0.0.0/8")]

-- A policy that sets its default action to accept is not analyzed.
private def acceptAll : RoutingPolicy := { name := "all", statements := #[.static .setDefaultActionAccept] }
#guard !(accCall config policyFuel acceptAll).safe

end Tests.Reasoning
