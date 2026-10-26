import LeanBatfish.Net.Prefix

/-!
# IP wildcards

An IP wildcard is an address with a mask of "don't care" bits, as in Cisco ACLs. Unlike a
prefix, the don't-care bits need not be contiguous. Batfish writes wildcards as
`ip`, `ip/len`, or `ip:mask`, and clears the don't-care bits of the address.
-/

namespace LeanBatfish

structure IpWildcard where
  ip : Ip
  /-- Bits set here are ignored when matching. -/
  wildcardMask : UInt32
  deriving DecidableEq, Hashable, Inhabited, Repr, Ord

namespace IpWildcard

def make (ip : Ip) (mask : UInt32) : IpWildcard := ⟨⟨ip.bits &&& ~~~mask⟩, mask⟩

def ofPrefix (p : Prefix) : IpWildcard := make p.addr (~~~(netmask p.len))

def containsIp (w : IpWildcard) (ip : Ip) : Bool :=
  (ip.bits ||| w.wildcardMask) == (w.ip.bits ||| w.wildcardMask)

/-- Parse Batfish's `IpWildcard` string forms (`IpWildcard.parse`). -/
def parse? (s : String) : Option IpWildcard :=
  match s.splitOn ":" with
  | [ip, mask] => do pure (make (← Ip.parse? ip) (← Ip.parse? mask).bits)
  | [_] =>
    match s.splitOn "/" with
    | [_, _] => ofPrefix <$> Prefix.parse? s
    | [ip] => (make · 0) <$> Ip.parse? ip
    | _ => none
  | _ => none

end IpWildcard

end LeanBatfish
