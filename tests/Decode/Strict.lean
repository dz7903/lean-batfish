import LeanBatfish.Decode.Configuration

/-! Strictness of the decoder: unknown fields and classes are rejected, gated fields are
accepted only at their neutral values. -/

namespace Tests.Decode
open Lean LeanBatfish Decode

/-- `"ok"`, `"unsupported"` or `"malformed"`. -/
def decodes (d : Decoder α) (s : String) : String :=
  match Json.parse s with
  | .error _ => "bad test JSON"
  | .ok j => match (d j).run with
    | .ok _ => "ok"
    | .error { kind := .unsupported, .. } => "unsupported"
    | .error { kind := .malformed, .. } => "malformed"

#guard decodes ipSpace r#"{"class": "org.batfish.datamodel.EmptyIpSpace"}"# == "ok"
#guard decodes ipSpace r#"{"class": "org.batfish.datamodel.FancyIpSpace"}"#
  == "unsupported"
#guard decodes ipSpace r#"{"class": "org.batfish.datamodel.IpIpSpace", "ip": "1.2.3.4",
  "extra": 1}"# == "unsupported"
#guard decodes ipSpace r#"{"class": "org.batfish.datamodel.IpIpSpace", "ip": "1.2.3"}"#
  == "malformed"

-- A gated field at its neutral value is fine; otherwise the input is rejected.
#guard decodes staticRoute r#"{"class": "org.batfish.datamodel.StaticRoute",
  "network": "0.0.0.0/0", "nextHopIp": "1.1.1.1", "administrativeCost": 1,
  "recursive": true, "nonForwarding": false, "track": null}"# == "ok"
#guard decodes staticRoute r#"{"class": "org.batfish.datamodel.StaticRoute",
  "network": "0.0.0.0/0", "nextHopIp": "1.1.1.1", "administrativeCost": 1,
  "recursive": true, "nonForwarding": false, "track": "10"}"# == "unsupported"
-- Upstream Batfish omits the static-route flags; only exports from our build decode.
#guard decodes staticRoute r#"{"class": "org.batfish.datamodel.StaticRoute",
  "network": "0.0.0.0/0", "nextHopIp": "1.1.1.1", "administrativeCost": 1}"# == "malformed"

-- Amount expressions carry their amount.
#guard decodes statement r#"{"class":
  "org.batfish.datamodel.routing_policy.statement.SetLocalPreference",
  "localPreference": {"class":
  "org.batfish.datamodel.routing_policy.expr.DecrementLocalPreference", "subtrahend": 5}}"#
  == "ok"

end Tests.Decode
