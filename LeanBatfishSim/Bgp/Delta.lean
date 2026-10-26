import Std.Data.HashMap
import LeanBatfish

/-!
# Route deltas

Batfish's engine passes changes rather than states: a *delta* is an ordered list of route
advertisements and withdrawals (`RibDelta`). Deltas are built with Batfish's rules
(`RibDelta.Builder`): each route appears at most once, at the position it was first
mentioned; withdrawing a route that the delta adds cancels both, and so does adding a route
it withdraws.
-/

namespace LeanBatfishSim

open LeanBatfish Std

inductive Reason
  | add
  | withdraw
  /-- Withdrawn because a better route replaced it. -/
  | replace
  deriving DecidableEq, Inhabited, Repr

structure Advert where
  route : Route
  reason : Reason := .add
  deriving DecidableEq, Inhabited

def Advert.withdrawn (a : Advert) : Bool := a.reason != .add

/-- A delta under construction. -/
structure Delta where
  slots : Array (Option Advert) := #[]
  index : HashMap Route Nat := {}
  deriving Inhabited

namespace Delta

def add (d : Delta) (r : Route) : Delta :=
  match d.index[r]? with
  | some i =>
    match d.slots[i]! with
    | some a => if a.withdrawn then { slots := d.slots.set! i none, index := d.index.erase r }
      else { d with slots := d.slots.set! i (some { route := r }) }
    | none => { slots := d.slots.set! i (some { route := r }), index := d.index }
  | none => { slots := d.slots.push (some { route := r }), index := d.index.insert r d.slots.size }

def remove (d : Delta) (r : Route) (reason : Reason := .withdraw) : Delta :=
  match d.index[r]? with
  | some i =>
    match d.slots[i]! with
    | some a => if a.reason == .add then { slots := d.slots.set! i none, index := d.index.erase r }
      else { d with slots := d.slots.set! i (some { route := r, reason }) }
    | none => { d with slots := d.slots.set! i (some { route := r, reason }) }
  | none =>
    { slots := d.slots.push (some { route := r, reason }), index := d.index.insert r d.slots.size }

def push (d : Delta) (a : Advert) : Delta :=
  if a.withdrawn then d.remove a.route a.reason else d.add a.route

def append (d : Delta) (as : Array Advert) : Delta := as.foldl push d

def toArray (d : Delta) : Array Advert := d.slots.filterMap id

def isEmpty (d : Delta) : Bool := d.index.isEmpty

def ofArray (as : Array Advert) : Array Advert := ({} : Delta).append as |>.toArray

end Delta

end LeanBatfishSim
