import Std.Data.HashMap
import LeanBatfish.Semantics.Route

/-!
# Routing tables

A `Rib` holds the routes offered to a routing table, indexed by prefix. For each prefix
the *active* routes are the offered routes of the best preference, all of them if
several tie (ECMP). Batfish keeps the active routes and, separately, the losing ones as
backups (`AbstractRib` with backup routes); offering and withdrawing routes in any order
leaves the same active routes as computing the best of what is currently offered, which
is what this module does.

The main RIB prefers lower administrative distance, then lower metric (`Rib`).
-/

namespace LeanBatfish

structure Rib where
  /-- The offered routes of each prefix, without duplicates. -/
  offered : Std.HashMap Prefix (Array Route) := {}
  deriving Inhabited

namespace Rib

/-- The main RIB's preference: lower administrative distance, then lower metric. -/
def mainPreference (r : Route) : Nat × Nat := (r.admin, r.metric)

/-- `a` is strictly preferred to `b`. -/
def morePreferred (a b : Nat × Nat) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

/-- The best routes among `routes` by the main RIB's preference. -/
def best (routes : Array Route) : Array Route :=
  match routes[0]? with
  | none => #[]
  | some first =>
    let key := routes.foldl (init := mainPreference first) fun k r =>
      if morePreferred (mainPreference r) k then mainPreference r else k
    routes.filter (mainPreference · == key)

/-- Offer a route. Non-routing routes never enter the main RIB. -/
def offer (rib : Rib) (r : Route) : Rib :=
  if r.nonRouting then rib
  else
    let cur := rib.offered.getD r.network #[]
    if cur.contains r then rib else { offered := rib.offered.insert r.network (cur.push r) }

def withdraw (rib : Rib) (r : Route) : Rib :=
  match rib.offered[r.network]? with
  | none => rib
  | some cur =>
    let rest := cur.filter (· != r)
    { offered := if rest.isEmpty then rib.offered.erase r.network
        else rib.offered.insert r.network rest }

def ofRoutes (routes : Array Route) : Rib := routes.foldl offer {}

/-- The active routes for one prefix. -/
def routesAt (rib : Rib) (p : Prefix) : Array Route := best (rib.offered.getD p #[])

/-- Whether `r` is an active route. -/
def isActive (rib : Rib) (r : Route) : Bool := (rib.routesAt r.network).contains r

/-- All active routes. -/
def routes (rib : Rib) : Array Route :=
  rib.offered.fold (fun acc _ rs => acc ++ best rs) #[]

/-- Longest-prefix match among active routes (`RibTree.getLongestPrefixMatch`): the
active routes of the longest prefix containing `ip` that has an active forwarding route
satisfying `allowed`; of those, the ones that are forwarding and allowed. -/
def longestPrefixMatch [Monad m] (rib : Rib) (ip : Ip) (allowed : Route → m Bool) :
    m (Array Route) := do
  for i in [0:33] do
    let len := 32 - i
    if h : len < 33 then
      let routes := rib.routesAt (Prefix.make ip ⟨len, h⟩)
      let usable ← routes.filterM fun r => do
        if r.nonForwarding then return false else allowed r
      if !usable.isEmpty then return usable
  return #[]

end Rib

end LeanBatfish
