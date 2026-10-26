import LeanBatfish.Net.Community
import LeanBatfish.Net.IpWildcard
import LeanBatfish.Net.AsPath

namespace Tests.Net
open LeanBatfish

-- Communities round-trip through Batfish's printed forms.
#guard (Community.parse? "65000:100").map toString == some "65000:100"
#guard (Community.parse? "large:1:2:3").map toString == some "large:1:2:3"
#guard (Community.parse? "514:65000L:1").map toString == some "514:65000L:1"
#guard (Community.parse? "2:100:7").map toString == some "2:100:7"
#guard Community.parse? "65536:1" == none
#guard (Community.parse? "1:2").map (·.isStandard) == some true

-- Wildcards: don't-care bits need not be contiguous.
#guard ((IpWildcard.parse? "10.0.0.0:0.255.0.255").get!).containsIp (Ip.parse? "10.7.0.9").get!
#guard !((IpWildcard.parse? "10.0.0.0:0.255.0.255").get!).containsIp (Ip.parse? "10.7.1.9").get!
#guard ((IpWildcard.parse? "10.0.0.0/8").get!).containsIp (Ip.parse? "10.200.0.1").get!
#guard ((IpWildcard.parse? "1.2.3.4").get!).containsIp (Ip.parse? "1.2.3.4").get!

-- AS-path rendering used as regex input.
#guard AsPath.render #[.single 1, ⟨#[2, 3], false⟩, ⟨#[65000], true⟩] == "1 {2,3} (65000)"

end Tests.Net
