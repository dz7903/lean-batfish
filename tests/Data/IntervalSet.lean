import LeanBatfish.Data.IntervalSet

namespace Tests.Data
open LeanBatfish

#guard (IntervalSet.parse? "1").map (·.contains 1) == some true
#guard (IntervalSet.parse? "1-5,10").map (·.contains 4) == some true
#guard (IntervalSet.parse? "1-5,10").map (·.contains 7) == some false
#guard (IntervalSet.parse? "1-10,!5").map (·.contains 5) == some false
#guard (IntervalSet.parse? "").map (·.contains 0) == some false
#guard IntervalSet.parse? "5-1" == none
#guard (SubRange.parse? "24-24") == some ⟨24, 24⟩

end Tests.Data
