import LeanBatfish.Net.Ip

/-!
# IPv4 prefixes

A prefix is an address together with a length between 0 and 32. As in Batfish
(`Prefix.create`), the host bits are always cleared, so `10.0.0.1/8` and `10.0.0.0/8`
denote the same prefix.
-/

namespace LeanBatfish

/-- The netmask with the top `len` bits set. -/
def netmask (len : Nat) : UInt32 :=
  if len = 0 then 0 else (0xFFFFFFFF : UInt32) <<< (32 - min len 32).toUInt32

/-- An IPv4 prefix. Build values with `Prefix.make`, which clears the host bits. -/
structure Prefix where
  addr : Ip
  len : Fin 33
  deriving DecidableEq, Hashable, Inhabited, Repr, Ord

namespace Prefix

def make (ip : Ip) (len : Fin 33) : Prefix :=
  ⟨⟨ip.bits &&& netmask len⟩, len⟩

def containsIp (p : Prefix) (ip : Ip) : Bool :=
  (ip.bits &&& netmask p.len) == p.addr.bits

/-- Whether `q` is contained in `p`, i.e. `p` is at most as long and covers `q`'s address. -/
def containsPrefix (p q : Prefix) : Bool :=
  p.len ≤ q.len && p.containsIp q.addr

/-- Parse `a.b.c.d/n`. -/
def parse? (s : String) : Option Prefix := do
  let [ip, len] := s.splitOn "/" | none
  let ip ← Ip.parse? ip
  let len ← len.toNat?
  if h : len < 33 then pure (make ip ⟨len, h⟩) else none

protected def toString (p : Prefix) : String := s!"{p.addr}/{p.len}"

instance : ToString Prefix := ⟨Prefix.toString⟩

end Prefix

end LeanBatfish
