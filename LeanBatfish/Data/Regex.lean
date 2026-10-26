/-!
# Java regular expressions

Batfish matches AS paths and communities with `java.util.regex.Pattern`, using
`Matcher.find()`: a regex matches a string if it matches some substring of it. This file
implements that for the part of Java's syntax that router configurations produce:
literals and escapes, `.`, character classes (`[...]`, `\d`, `\w`, `\s` and their
negations), groups `(...)` and `(?:...)`, alternation, the anchors `^` and `$`, and the
greedy or lazy quantifiers `*`, `+`, `?`, `{n}`, `{n,}` and `{n,m}`.

Anything else (backreferences, lookaround, flags, possessive quantifiers, word
boundaries, class intersections) is rejected when parsing, so a regex is either matched
exactly as Java would match it or refused.

Matching computes, for a regex and a start position, the set of positions where a match
can end. This is exact for deciding whether a match exists, which is all Batfish asks.
Lazy and greedy quantifiers only differ in which match Java reports, not in whether one
exists, so they are treated alike.
-/

namespace LeanBatfish

/-- A character class: a union of inclusive ranges, possibly negated. -/
structure CharClass where
  ranges : Array (Char × Char)
  negated : Bool := false
  deriving DecidableEq, Repr, Inhabited

namespace CharClass

def contains (c : CharClass) (ch : Char) : Bool :=
  c.ranges.any (fun (lo, hi) => lo ≤ ch && ch ≤ hi) != c.negated

def single (ch : Char) : CharClass := ⟨#[(ch, ch)], false⟩

def digit : CharClass := ⟨#[('0', '9')], false⟩
def word : CharClass := ⟨#[('a', 'z'), ('A', 'Z'), ('_', '_'), ('0', '9')], false⟩
def space : CharClass :=
  ⟨#[(' ', ' '), ('\t', '\t'), ('\n', '\n'), ('\x0B', '\x0B'), ('\x0C', '\x0C'),
     ('\r', '\r')], false⟩

/-- `.`: any character except Java's line terminators. -/
def dot : CharClass :=
  ⟨#[('\n', '\n'), ('\r', '\r'), ('\u0085', '\u0085'), (' ', ' ')], true⟩

def negate (c : CharClass) : CharClass := { c with negated := !c.negated }

end CharClass

inductive Regex
  /-- Matches the empty string. -/
  | empty
  | chars (c : CharClass)
  | seq (a b : Regex)
  | alt (a b : Regex)
  /-- `a` repeated between `min` and `max` times (`none`: unbounded). -/
  | rep (a : Regex) (min : Nat) (max : Option Nat)
  /-- `^`: the start of the input. -/
  | start
  /-- `$`: the end of the input (or just before a final line terminator). -/
  | finish
  deriving Repr, Inhabited

namespace Regex

/-! ## Parsing -/

private abbrev ParseM := StateT (List Char) (Except String)

private def peek? : ParseM (Option Char) := do
  return (← get).head?

private def next : ParseM Char := do
  match ← get with
  | c :: rest => set rest; pure c
  | [] => throw "unexpected end of regex"

private def expect (c : Char) : ParseM Unit := do
  let d ← next
  unless d == c do throw s!"expected '{c}'"

private def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

private partial def number : ParseM (Option Nat) := do
  let rec go (acc : Option Nat) : ParseM (Option Nat) := do
    match ← peek? with
    | some c =>
      if isDigit c then
        let _ ← next
        go (some ((acc.getD 0) * 10 + (c.toNat - '0'.toNat)))
      else pure acc
    | none => pure acc
  go none

/-- An escape after `\`, outside or inside a character class. -/
private def escape : ParseM CharClass := do
  let c ← next
  match c with
  | 'd' => pure .digit
  | 'D' => pure CharClass.digit.negate
  | 'w' => pure .word
  | 'W' => pure CharClass.word.negate
  | 's' => pure .space
  | 'S' => pure CharClass.space.negate
  | 't' => pure (.single '\t')
  | 'n' => pure (.single '\n')
  | 'r' => pure (.single '\r')
  | 'f' => pure (.single '\x0C')
  | 'e' => pure (.single '\x1B')
  | 'a' => pure (.single '\x07')
  | _ =>
    -- Java treats a backslash before any non-alphabetic character as a literal.
    if c.isAlphanum then throw s!"unsupported escape \\{c}" else pure (.single c)

/-- A character class body, after the opening `[`. -/
private partial def classBody : ParseM CharClass := do
  let negated ← do
    if (← peek?) == some '^' then let _ ← next; pure true else pure false
  let rec items (acc : Array (Char × Char)) (first : Bool) : ParseM (Array (Char × Char)) := do
    let c ← next
    if c == ']' && !first then return acc
    if c == '[' then throw "nested character classes are not supported"
    if c == '&' && (← peek?) == some '&' then
      throw "character class intersection is not supported"
    let lo ← if c == '\\' then do
        let e ← escape
        if e.negated || e.ranges.size != 1 || e.ranges[0]!.1 != e.ranges[0]!.2 then
          -- A class escape such as \d: add its ranges (negated ones are not supported).
          if e.negated then throw "negated class escape inside a class is not supported"
          return ← items (acc ++ e.ranges) false
        pure e.ranges[0]!.1
      else pure c
    -- A range `lo-hi`, unless `-` is the last character before `]`.
    match ← get with
    | '-' :: ']' :: _ => items (acc.push (lo, lo)) false
    | '-' :: _ =>
      let _ ← next
      let hc ← next
      let hi ← if hc == '\\' then do
          let e ← escape
          if e.negated || e.ranges.size != 1 then throw "bad range in character class"
          pure e.ranges[0]!.1
        else pure hc
      if hi < lo then throw "illegal character range"
      items (acc.push (lo, hi)) false
    | _ => items (acc.push (lo, lo)) false
  let ranges ← items #[] true
  pure ⟨ranges, negated⟩

mutual

private partial def alternation : ParseM Regex := do
  let first ← sequence
  if (← peek?) == some '|' then
    let _ ← next
    pure (.alt first (← alternation))
  else pure first

private partial def sequence : ParseM Regex := do
  let rec go (acc : Regex) : ParseM Regex := do
    match ← peek? with
    | none | some '|' | some ')' => pure acc
    | some _ => go (.seq acc (← quantified))
  go .empty

private partial def quantified : ParseM Regex := do
  let a ← atom
  let go (a : Regex) : ParseM Regex := do
    let q ← match ← peek? with
      | some '*' => do let _ ← next; pure (some (0, none))
      | some '+' => do let _ ← next; pure (some (1, none))
      | some '?' => do let _ ← next; pure (some (0, some 1))
      | some '{' => do
        let _ ← next
        let some lo ← number | throw "illegal repetition"
        let hi ← match ← next with
          | '}' => pure (some lo)
          | ',' => do
            let hi ← number
            expect '}'
            pure hi
          | _ => throw "illegal repetition"
        if let some h := hi then if h < lo then throw "illegal repetition range"
        pure (some (lo, hi))
      | _ => pure none
    match q with
    | none => pure a
    | some (lo, hi) =>
      match ← peek? with
      | some '?' => let _ ← next  -- lazy: same set of matches
      | some '+' => throw "possessive quantifiers are not supported"
      | _ => pure ()
      -- Java rejects a quantifier applied to a quantified atom, as in `a**`.
      match ← peek? with
      | some '*' | some '+' | some '?' => throw "dangling quantifier"
      | _ => pure (.rep a lo hi)
  go a

private partial def atom : ParseM Regex := do
  match ← next with
  | '(' =>
    if (← peek?) == some '?' then
      let _ ← next
      unless (← next) == ':' do throw "only (?:...) groups are supported"
    let r ← alternation
    expect ')'
    pure r
  | '[' => pure (.chars (← classBody))
  | '.' => pure (.chars .dot)
  | '^' => pure .start
  | '$' => pure .finish
  | '\\' =>
    match ← peek? with
    | some c =>
      if isDigit c && c != '0' then throw "backreferences are not supported"
      if c == 'b' || c == 'B' || c == 'A' || c == 'z' || c == 'Z' || c == 'G' then
        throw s!"\\{c} is not supported"
      if c == 'Q' || c == 'E' || c == 'p' || c == 'P' || c == 'x' || c == 'u' || c == '0' then
        throw s!"\\{c} is not supported"
      pure (.chars (← escape))
    | none => throw "trailing backslash"
  | '*' | '+' | '?' => throw "dangling quantifier"
  | '{' => throw "illegal repetition"
  | c => pure (.chars (.single c))

end

/-- Parse a Java regex, or explain why it is outside the supported syntax. -/
def parse (s : String) : Except String Regex := do
  let (r, rest) ← alternation.run s.toList
  unless rest.isEmpty do throw "unbalanced ')'"
  pure r

/-! ## Matching -/

/-- Java's line terminators, which `$` may precede at the end of the input. -/
private def isLineTerminator (c : Char) : Bool :=
  c == '\n' || c == '\r' || c == '\u0085' || c == ' ' || c == ' '

private def insertSorted (xs : List Nat) (x : Nat) : List Nat :=
  match xs with
  | [] => [x]
  | y :: ys => if x < y then x :: xs else if x == y then xs else y :: insertSorted ys x

private def union (xs ys : List Nat) : List Nat := ys.foldl insertSorted xs

/-- The positions after `k` more iterations of `step`, from `frontier`, collecting every
position reached once at least `min` iterations have been done. -/
private def iterate (step : Nat → List Nat) (frontier : List Nat) (min : Nat)
    (max : Option Nat) (fuel : Nat) (acc : List Nat) : List Nat :=
  match fuel with
  | 0 => acc
  | fuel + 1 =>
    if frontier.isEmpty || max == some 0 then acc
    else
      let next := frontier.foldl (fun s p => union s (step p)) []
      let min' := min - 1
      let max' := max.map (· - 1)
      let acc' := if min' == 0 then union acc next else acc
      -- Once past the minimum, positions seen before add nothing new.
      let frontier' := if min' == 0 then next.filter (fun p => !acc.contains p) else next
      iterate step frontier' min' max' fuel acc'

/-- The end positions of matches of `r` in `s` that start at `i`. -/
def ends (s : Array Char) : Regex → Nat → List Nat
  | .empty, i => [i]
  | .chars c, i => if h : i < s.size then (if c.contains s[i] then [i + 1] else []) else []
  | .seq a b, i => (ends s a i).foldl (fun acc j => union acc (ends s b j)) []
  | .alt a b, i => union (ends s a i) (ends s b i)
  | .rep a min max, i =>
    let start := if min == 0 then [i] else []
    -- Each productive iteration moves forward, so `s.size + min + 1` rounds reach every
    -- position that can be reached.
    iterate (ends s a) [i] min max (s.size + min + 1) start
  | .start, i => if i == 0 then [i] else []
  | .finish, i =>
    -- The end of the input, or just before a final line terminator, where `\r\n` counts
    -- as one terminator and is not split.
    if i == s.size then [i]
    else if h : i + 1 = s.size then
      if isLineTerminator s[i] && !(s[i] == '\n' && i > 0 && s[i - 1]! == '\r') then [i]
      else []
    else if h : i + 2 = s.size then
      if s[i] == '\r' && s[i + 1] == '\n' then [i] else []
    else []

/-- `Matcher.find()`: whether `r` matches some substring of `s`. -/
def find (r : Regex) (s : String) : Bool :=
  let cs := s.toList.toArray
  (List.range (cs.size + 1)).any fun i => !(ends cs r i).isEmpty

end Regex

end LeanBatfish
