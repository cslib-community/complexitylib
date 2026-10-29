/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.HardCore
import Complexity.Tactic.PPT

/-! Finite/list security agreement, honest sampling programs, and hard-core prediction tests. -/

namespace ComplexityTests.HardCore

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

-- The finite-test restriction is inhabited for every declared output length.
example (length : ℕ → ℕ) :
    IsPPTBitStringTest (fun n (_ : BitString (length n)) => PMF.pure true) :=
  ⟨fun _ _ => pure true, by ppt, fun _ _ => rfl⟩

-- Security without stretching is inhabited, and the bridge includes the empty seed.
example : (PRG.wordFamily id id).Secure IsPPTBitStringTest := by
  apply (PRG.wordFamily_secure_iff (fun _ => rfl)).mpr
  rw [show generatorEnsemble id = BitString.uniformList from funext fun _ => PMF.map_id _]
  exact ComputationallyIndistinguishable.refl BitString.uniformList

-- No security hypothesis is needed to compute the declared output length of a concrete generator.
example : ComputableInPolyTime (fun n => n + 1) encUnary encUnary :=
  PRG.polyTime_length (generator := fun word : List Bool => word ++ [false]) (by fun_prop) (by simp)

example (adversary : Distinguisher) (ha : IsPPT encBool adversary) :
    IsPPT encBool (fun n _ => prgIdealGame (fun k => k * k + 1) adversary n) := by ppt

section

attribute [local irreducible] hardCorePredictor prgRealGame prgIdealGame

-- Folded reduction programs compose with new parameters and auxiliary inputs.
example (adversary : Distinguisher) (ha : IsPPT encBool adversary) :
    IsPPT encBool (fun n word => hardCorePredictor adversary true (n + 1) (word ++ word)) := by
  ppt

end

-- A fresh fair trial predicts a perfectly distinguishing label exactly.
example (truth : Bool) :
    ProbComp.eval ((fun guess => guess == truth) <$>
      bitPredictor (fun trial => pure (trial == truth))) = PMF.pure true := by
  have h (trial : Bool) : ((if trial = truth then trial else !trial) == truth) = true := by
    cases trial <;> cases truth <;> decide
  simp [bitPredictor, trialPredictor, PMF.map, Function.comp_def, h]

-- A constant image hides the uniform seed's first bit perfectly for every nonempty length.
private theorem hidden_head (adversary : Distinguisher) (n : ℕ) :
    ProbComp.eval (predictionGame (fun _ => []) (fun word => word.headD false) adversary (n + 1)) =
      PMF.uniformOfFintype Bool := by
  simp only [predictionGame, ProbComp.eval_bind, BitString.eval_sampleList,
    BitString.uniformList_succ, PMF.bind_bind, PMF.bind_map, Function.comp_def, List.headD_cons,
    ProbComp.eval_pure, PMF.bind_const]
  rw [PMF.bind_comm]
  convert PMF.bind_const (ProbComp.eval (adversary (n + 1) [])) (PMF.uniformOfFintype Bool) using 1
  congr 1
  funext guess
  ext bit
  cases guess <;> cases bit <;> simp [PMF.bind_apply]

-- The hard-core definition has a concrete instance; it does not assume one-wayness of f.
example : Cslib.Crypto.HardCore (fun _ => []) (fun word => word.headD false) := by
  refine ⟨by fun_prop, fun adversary _ => ?_⟩
  apply negligible_zero.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : n ≠ 0)
  simp only [hidden_head, Game.advantage_self]

-- A primitive's plain certificate composes directly in an ordinary client proof.
example {f : List Bool → List Bool} {predicate : List Bool → Bool}
    (h : Cslib.Crypto.HardCore f predicate) :
    ComputableInPolyTime (fun word => !(predicate word)) encBits encBool := by
  have hp := h.polyTime
  fun_prop

end ComplexityTests.HardCore
