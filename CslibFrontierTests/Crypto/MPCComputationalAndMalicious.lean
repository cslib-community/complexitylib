/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Crypto.Protocols.MPC.ComputationalComposition
import CslibFrontier.Crypto.Protocols.MPC.Malicious

/-!
# MPC Computational and Malicious Tests

Tests and examples exercising `semiHonestAdvantage_compose_le`, `adversaryAborts_characterization`,
and `naive_without_abort_failure`.
-/

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

example :
    ProbComp.eval (maliciousIdealWithAbort coinTossPrivateFunc I0 (fun _ => ()) myCoinS) =
      ProbComp.eval (maliciousIdeal (adversaryAborts coinTossPrivateFunc I0) I0 (fun i => ((), fun _ _ => true))
        (fun x_I => do
          let (x_I_prime, S_out) ← myCoinS x_I
          return (x_I_prime, fun y_I => S_out y_I))) :=
  adversaryAborts_characterization coinTossPrivateFunc I0 (by decide) (fun _ => ()) myCoinS

example :
  ¬ (∃ (S : ((i : I0) → Unit) → ProbComp (((i : I0) → Unit) × (((i : I0) →
      (if (↑i : Fin 2) = 0 then Unit else Bool)) → Unit))),
        ProbComp.eval (do
            let (_, y) ← maliciousIdeal coinTossPrivateFunc I0 (fun _ => ()) S
            return extractBoolFromMalicious y) = 
        ProbComp.eval (do
            let (_, y) ← coinTossBiasedDist
            return extractBoolFromBiased y)) :=
  naive_without_abort_failure

example {m : ℕ} {In Out : Fin m → Type}
    {D : ((i : Fin m) → Out i) → ProbComp Bool}
    {P_sub : Functionality m In Out}
    {π : Protocol m In Out}
    {x : (i : Fin m) → In i}
    {c : Fin m → Type}
    {C : Protocol m (fun i => c i × In i) Out}
    {h_len : (C.subcalls x).length > 0}
    {ε_out ε_sub : ℝ}
    (h_out : C.outerDistinguisherAdvantage P_sub x D ≤ ε_out)
    (h_sub : C.subcallDistinguisherAdvantage π P_sub x D ≤ ε_sub) :
    |ProbComp.eval (C.realExecution π x) true -
     ProbComp.eval (C.idealExecution P_sub x) true| ≤
    ε_out + (C.subcalls x).length * ε_sub :=
  semiHonestAdvantage_compose_le h_out h_sub

end CslibFrontierTests.Crypto.MPCComputationalAndMalicious
