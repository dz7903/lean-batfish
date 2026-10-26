import LeanBatfish.Semantics.Policy.Eval

namespace Tests.Semantics
open LeanBatfish

private def pfx (s : String) : Prefix := (Prefix.parse? s).get!

/-- Cisco's resolution policy: reject the default route, accept everything else. -/
private def resolutionPolicy : RoutingPolicy := {
  name := "~RESOLUTION_POLICY~"
  statements := #[.ifThen (.matchPrefixSet (.explicit #[⟨pfx "0.0.0.0/0", ⟨0, 0⟩⟩]))
    #[.static .returnFalse] #[.static .returnTrue]] }

private def config : Configuration :=
  { (default : Configuration) with routingPolicies := #[(resolutionPolicy.name, resolutionPolicy)] }

private def staticRoute (p : String) : Route :=
  { network := pfx p, nextHop := .discard, protocol := .static, admin := 1 }

private def accepts (p : RoutingPolicy) (r : Route) : String :=
  match Policy.accepts config p r with
  | .ok b => toString b
  | .error e => e

#guard accepts resolutionPolicy (staticRoute "0.0.0.0/0") == "false"
#guard accepts resolutionPolicy (staticRoute "10.0.0.0/8") == "true"

/-- A route map that sets local preference 200 on routes tagged 7 and rejects the rest. -/
private def setLp : RoutingPolicy := {
  name := "set-lp"
  statements := #[
    .ifThen (.matchTag .eq (.literal 7))
      #[.setLocalPreference (.literal 200), .static .exitAccept]
      #[.static .exitReject]] }

private def run (p : RoutingPolicy) (r : Route) : Option Nat :=
  let ctx : Policy.Context :=
    { config, original := r, useOutputAttributes := false, outputKind := .bgp }
  match Policy.process ctx p { r with bgp := some {} } with
  | .ok o => if o.accepted then some o.output.localPreference else none
  | .error _ => none

#guard run setLp { staticRoute "10.0.0.0/8" with tag := 7 } == some 200
#guard run setLp (staticRoute "10.0.0.0/8") == none

end Tests.Semantics
