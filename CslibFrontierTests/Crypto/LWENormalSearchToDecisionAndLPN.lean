import CslibFrontier.Crypto.Computational.LWE.NormalForm
import CslibFrontier.Crypto.Computational.LPN
import CslibFrontier.Crypto.Computational.LWE.SearchToDecision

namespace CslibFrontierTests.Crypto.LWENormalSearchToDecisionAndLPN

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.PrimeLWE

/--
info: 'Cslib.Crypto.PrimeLWE.decisionNormalForm' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs in
#print axioms decisionNormalForm

/--
info: 'Cslib.Crypto.PrimeLWE.searchNormalForm' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs in
#print axioms searchNormalForm





/--
info: 'Cslib.Crypto.SearchLPN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.SearchLPN

end CslibFrontierTests.Crypto.LWENormalSearchToDecisionAndLPN
