import CslibFrontier.Crypto.Protocols.MPC.ComputationalComposition
import CslibFrontier.Crypto.Protocols.MPC.Malicious

namespace CslibFrontierTests.Crypto.MPCComputationalAndMalicious

open Cslib.Crypto.Protocols.MPC Cslib

/--
info: 'Cslib.Crypto.Protocols.MPC.semiHonestAdvantage_compose_le' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms semiHonestAdvantage_compose_le

/--
info: 'Cslib.Crypto.Protocols.MPC.adversaryAborts_characterization' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms adversaryAborts_characterization

/--
info: 'Cslib.Crypto.Protocols.MPC.naive_without_abort_failure' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms naive_without_abort_failure

noncomputable def myCoinS (_x : (i : (I0 : Finset (Fin 2))) → Unit) :
    ProbComp (((i : (I0 : Finset (Fin 2))) → Unit) ×
      (((i : (I0 : Finset (Fin 2))) → (if (i:Fin 2) = 0 then Unit else Bool)) → Bool × Unit)) :=
  return (fun _ => (), fun _ => (true, ()))

#check adversaryAborts_characterization coinTossPrivateFunc I0 (by decide) (fun _ => ())
  myCoinS

#check semiHonestAdvantage_compose_le (m := 2)

end CslibFrontierTests.Crypto.MPCComputationalAndMalicious
