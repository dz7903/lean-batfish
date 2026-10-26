import LeanBatfish.Data.Regex

namespace Tests.Data
open LeanBatfish

private def finds (re s : String) : String :=
  match Regex.parse re with
  | .ok r => if r.find s then "match" else "no match"
  | .error _ => "rejected"

-- `find()` looks for a match anywhere unless anchored.
#guard finds "65001" "100 65001 200" == "match"
#guard finds "^65001" "100 65001" == "no match"
#guard finds "^65001$" "65001" == "match"
#guard finds "^$" "" == "match"
#guard finds "_" "65001" == "no match"
-- Batfish's translation of Cisco's `_`.
#guard finds "(,|\\{|\\}|^|$| )2:" "1:1 2:5" == "match"
#guard finds "(,|\\{|\\}|^|$| )2:" "12:5" == "no match"
#guard finds "^(100 )+200$" "100 100 200" == "match"
#guard finds "^(100 )+200$" "200" == "no match"
#guard finds "^[0-9]{3,5}$" "1234" == "match"
#guard finds "^[0-9]{3,5}$" "123456" == "no match"
#guard finds "^\\d+ [^ ]*$" "1 abc" == "match"
#guard finds "a.c" "a\nc" == "no match"
#guard finds "^(a|ab)c$" "abc" == "match"
#guard finds "^(a*)*$" "aaaa" == "match"
#guard finds "^(a?){3}b$" "ab" == "match"
#guard finds "x*?" "" == "match"
#guard finds "a$" "a\r\n" == "match"
#guard finds "a$" "a\n" == "match"
#guard finds "a$" "a\n\n" == "no match"
-- Java rejects these, or we do not model them.
#guard finds "a**" "a" == "rejected"
#guard finds "a{" "a" == "rejected"
#guard finds "(a)\\1" "aa" == "rejected"
#guard finds "a*+" "a" == "rejected"
#guard finds "(?i)a" "A" == "rejected"
#guard finds "\\bfoo" "foo" == "rejected"

end Tests.Data
