import LeanBatfish.IR.Basic
import LeanBatfish.Net.IpWildcard
import LeanBatfish.Data.IntervalSet

/-!
# Prefix sets and route-filter lists

Routing policies match route prefixes against prefix sets. A `PrefixSpace` is a set of
`PrefixRange`s; a `RouteFilterList` (Cisco prefix lists, Juniper route filters) is an
ordered list of permit/deny lines over wildcards and length ranges.
-/

namespace LeanBatfish

/-- The prefixes contained in `prefix` whose length lies in `lengthRange`. Batfish writes
these as `"10.0.0.0/8"` (exact) or `"10.0.0.0/8:16-24"`. -/
structure PrefixRange where
  «prefix» : Prefix
  lengthRange : SubRange
  deriving DecidableEq, Hashable, Inhabited, Repr

abbrev PrefixSpace := Array PrefixRange

structure RouteFilterLine where
  action : LineAction
  ipWildcard : IpWildcard
  lengthRange : SubRange
  deriving Inhabited, Repr

structure RouteFilterList where
  name : String
  lines : Array RouteFilterLine
  deriving Inhabited, Repr

end LeanBatfish
