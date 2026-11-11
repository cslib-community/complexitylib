/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Crypto.Protocols.MPC.ComputationalComposition
import CslibFrontier.Crypto.Protocols.MPC.Malicious

set_option linter.privateModule false

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

noncomputable def myCoinS (_x : (i : ({0} : Finset (Fin 2))) → Unit) :
    ProbComp (((i : ({0} : Finset (Fin 2))) → Unit) ×
      (((i : ({0} : Finset (Fin 2))) →
        (if (i:Fin 2) = 0 then Unit else Bool)) → Bool × Unit)) :=
  return (fun _ => (), fun _ => (true, ()))

example :
    ProbComp.eval (maliciousIdealWithAbort coinTossPrivateFunc {0} (fun _ => ()) myCoinS) =
      ProbComp.eval (maliciousIdeal (adversaryAborts coinTossPrivateFunc {0}) {0}
        (fun _ => ((), fun _ _ => true))
        (fun x_I => do
          let (x_I_prime, S_out) ← myCoinS (fun i => (x_I i).1)
          return (fun i => (x_I_prime i, fun _ y_I => (S_out y_I).1), fun y_I =>
            if h : ∀ i, (y_I i).isSome then
              (S_out (fun i => Option.get _ (h i))).2
            else ()))) :=
  adversaryAborts_characterization coinTossPrivateFunc {0}
    (Finset.singleton_nonempty 0) (fun _ => ()) myCoinS

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

open scoped NNReal

example {m : ℕ} {spec₁ spec₂ : MultiOracleSpec}
    {sc₁ : Schedule m spec₁} {In Coins₁ Out : Fin m → Type}
    (P : Protocol m spec₁ sc₁ In Coins₁ Out)
    (W₁ : MultiOracleWorld spec₁) (W₂ : MultiOracleWorld spec₂)
    (f : Functionality m In Out)
    (S₁ : (I : Finset (Fin m)) → CoalitionSimulator sc₁ In Coins₁ Out I)
    {sc₂ : (op : spec₁.Op) → Schedule (spec₁.arity op) spec₂}
    {Coins₂ : (op : spec₁.Op) → Fin (spec₁.arity op) → Type}
    (Sub : (op : spec₁.Op) →
      Protocol (spec₁.arity op) spec₂ (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op))
    (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J)
    (I : Finset (Fin m)) (x : (i : Fin m) → In i)
    (D : ((i : I) → PartyView In (Schedule.ComposedCoins Coins₂ Coins₁ sc₁)
        (Schedule.compose sc₂ sc₁) i) × ((i : Fin m) → Out i) → ProbComp Bool)
    (ε_out ε_sub : ℝ≥0)
    (hout : semiHonestAdvantage P W₁ f I (S₁ I) x (composeDistinguisher P S₂ I x D) ≤ ε_out)
    (hsub : ∀ op J q D_sub, semiHonestAdvantage (Sub op) W₂ (W₁ op) J (S₂ op J) q D_sub ≤ ε_sub) :=
  semiHonestAdvantage_compose_le P W₁ W₂ f S₁ Sub S₂ I x D ε_out ε_sub hout hsub

end CslibFrontierTests.Crypto.MPCComputationalAndMalicious
