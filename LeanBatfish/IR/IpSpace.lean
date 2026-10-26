import LeanBatfish.IR.Basic
import LeanBatfish.Net.IpWildcard

/-!
# IP spaces

An `IpSpace` is Batfish's description of a set of IPv4 addresses. ACLs use IP spaces to
match source and destination addresses. Named IP spaces live in
`Configuration.ipSpaces` and are referred to by `IpSpaceReference`.
-/

namespace LeanBatfish

inductive IpSpace
  | empty
  | universe
  | ip (ip : Ip)
  | «prefix» (p : Prefix)
  | wildcard (wildcard : IpWildcard)
  /-- Addresses matching some whitelisted wildcard and no blacklisted one. -/
  | wildcardSet (whitelist blacklist : Array IpWildcard)
  /-- A named IP space of the same configuration. -/
  | reference (name : String)
  /-- First-match lines: the space contains an address if the first line whose space
  contains it is a permit line. -/
  | acl (lines : Array (LineAction × IpSpace))
  deriving Inhabited, Repr

end LeanBatfish
