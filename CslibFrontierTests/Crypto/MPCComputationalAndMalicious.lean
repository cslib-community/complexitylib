import CslibFrontier.Crypto.Protocols.MPC.ComputationalComposition
import CslibFrontier.Crypto.Protocols.MPC.Malicious

namespace CslibFrontierTests.Crypto.MPCComputationalAndMalicious

open Cslib.Crypto.Protocols.MPC

/-- info: 'Cslib.Crypto.Protocols.MPC.semiHonestAdvantage_compose_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms semiHonestAdvantage_compose_le

/-- info: 'Cslib.Crypto.Protocols.MPC.adversaryAborts_characterization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms adversaryAborts_characterization

/-- info: 'Cslib.Crypto.Protocols.MPC.naive_without_abort_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms naive_without_abort_failure

#check semiHonestAdvantage_compose_le (m := 2)
#check adversaryAborts_characterization (m := 2)
#check naive_without_abort_failure

end CslibFrontierTests.Crypto.MPCComputationalAndMalicious
