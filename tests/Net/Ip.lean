import LeanBatfish.Net.Prefix

namespace Tests.Net
open LeanBatfish

#guard (Ip.parse? "10.1.2.3").map toString == some "10.1.2.3"
#guard (Ip.parse? "255.255.255.255").map (·.bits) == some 0xFFFFFFFF
#guard Ip.parse? "256.0.0.1" == none
#guard Ip.parse? "1.2.3" == none
#guard Ip.parse? "1..2.3" == none

#guard (Prefix.parse? "10.0.0.1/8").map toString == some "10.0.0.0/8"
#guard (Prefix.parse? "0.0.0.0/0").map toString == some "0.0.0.0/0"
#guard (Prefix.parse? "1.2.3.4/32").map toString == some "1.2.3.4/32"
#guard Prefix.parse? "1.2.3.4/33" == none

#guard ((Prefix.parse? "10.0.0.0/8").get!).containsIp (Ip.parse? "10.255.0.1").get!
#guard !((Prefix.parse? "10.0.0.0/8").get!).containsIp (Ip.parse? "11.0.0.1").get!
#guard ((Prefix.parse? "0.0.0.0/0").get!).containsIp (Ip.parse? "11.0.0.1").get!
#guard ((Prefix.parse? "10.0.0.0/8").get!).containsPrefix (Prefix.parse? "10.1.0.0/16").get!
#guard !((Prefix.parse? "10.1.0.0/16").get!).containsPrefix (Prefix.parse? "10.0.0.0/8").get!

end Tests.Net
