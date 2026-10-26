/-!
# IPv4 addresses

Batfish's `Ip` is a 32-bit IPv4 address, written in JSON as a dotted quad such as
`"10.0.0.1"`.
-/

namespace LeanBatfish

/-- An IPv4 address, stored as its 32-bit big-endian value. -/
structure Ip where
  bits : UInt32
  deriving DecidableEq, Hashable, Inhabited, Repr, Ord

namespace Ip

instance : LT Ip := ⟨fun a b => a.bits < b.bits⟩
instance : LE Ip := ⟨fun a b => a.bits ≤ b.bits⟩
instance (a b : Ip) : Decidable (a < b) := inferInstanceAs (Decidable (a.bits < b.bits))
instance (a b : Ip) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.bits ≤ b.bits))

def ofOctets (a b c d : UInt8) : Ip :=
  ⟨(a.toUInt32 <<< 24) ||| (b.toUInt32 <<< 16) ||| (c.toUInt32 <<< 8) ||| d.toUInt32⟩

/-- The four octets, most significant first. -/
def octets (ip : Ip) : UInt8 × UInt8 × UInt8 × UInt8 :=
  ((ip.bits >>> 24).toUInt8, (ip.bits >>> 16).toUInt8, (ip.bits >>> 8).toUInt8, ip.bits.toUInt8)

/-- Parse a dotted quad. Each octet is a decimal number below 256. -/
def parse? (s : String) : Option Ip := do
  let parts := s.splitOn "."
  guard (parts.length == 4)
  let octets ← parts.mapM fun p => do
    guard (!p.isEmpty)
    let n ← p.toNat?
    guard (n < 256)
    pure n
  pure ⟨UInt32.ofNat (octets.foldl (fun acc n => acc * 256 + n) 0)⟩

protected def toString (ip : Ip) : String :=
  let (a, b, c, d) := ip.octets
  s!"{a}.{b}.{c}.{d}"

instance : ToString Ip := ⟨Ip.toString⟩

def zero : Ip := ⟨0⟩

end Ip

end LeanBatfish
