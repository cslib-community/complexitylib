/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.PMF.Bind
import Complexity.Crypto.Protocols.SigmaProtocol.SchnorrIdentification
import Complexity.Probability.PMF
import Complexity.Probability.Rewinding
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for rewinding and identification from Sigma protocols

The rewinding lemma's bound is attained by a second stage that succeeds exactly at one fixed
challenge. For Schnorr's protocol in `ZMod 11`, where discrete logarithms are easy, an
impersonator that computes the witness succeeds with probability one, so the extraction theorem
gives the rewinding extractor success probability at least `10 / 11`.
-/

namespace ComplexityTests.Crypto.SigmaIdentification

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Protocols SigmaProtocol

/-! ### Sharpness of the rewinding lemma

A second stage that passes only at the challenge `0 : Fin 4` succeeds once with probability
`1 / 4` and never twice at distinct challenges, so `ε ^ 2 - ε / N = 0` is attained. -/

example : (Rewinding.once (PMF.pure ()) (fun _ => PMF.uniformOfFintype (Fin 4))
    (fun _ _ => PMF.pure ()) fun _ (t : Fin 4) _ =>
    decide (t = 0)) true = 1 / 4 := by
  simp [Rewinding.once, PMF.bind_apply, tsum_fintype]

example : (Rewinding.twice (PMF.pure ()) (fun _ => PMF.uniformOfFintype (Fin 4))
    (fun _ _ => PMF.pure ()) fun _ (t : Fin 4) _ =>
    decide (t = 0)) true = 0 := by
  simp [Rewinding.twice, PMF.bind_apply, tsum_fintype, Fin.sum_univ_four]

/-! ### Schnorr identification in `ZMod 11` -/

instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- Challenges are all of `ZMod 11`. -/
abbrev ι : ZMod 11 ↪ ZMod 11 := Function.Embedding.refl _

/-- An impersonator that knows discrete logarithms to the base `2` in `ZMod 11`: the witness of
`u` is `6 • u`, and it runs the honest prover with it. -/
noncomputable def knower : Impersonator (ZMod 11) (ZMod 11) (ZMod 11) (ZMod 11) where
  State := ZMod 11 × ZMod 11
  commit u := (PMF.uniformOfFintype (ZMod 11)).map fun r => (r • (2 : ZMod 11), (r, u))
  respond s c := PMF.pure (s.1 + c • (6 • s.2))

/-- The impersonator that knows the witness always succeeds. -/
theorem succProbability_knower :
    Game.succProbability ((schnorr ι (2 : ZMod 11)).directAttack (schnorrKeyGen 2) knower) = 1 := by
  rw [Game.succProbability, ENNReal.toNNReal_eq_one_iff]
  refine le_antisymm (PMF.coe_le_one _ _) ?_
  simp only [directAttack, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  refine PMF.le_bind_apply_on_support _ fun key _ => ?_
  refine PMF.le_bind_apply_on_support _ fun ts hts => ?_
  obtain ⟨r, -, rfl⟩ := (_root_.PMF.mem_support_map_iff _ _ _).mp hts
  refine PMF.le_bind_apply_on_support _ fun c _ => ?_
  refine PMF.le_bind_apply_on_support _ fun z hz => ?_
  simp only [knower, _root_.PMF.mem_support_pure_iff] at hz
  subst hz
  have h11 : (11 : ZMod 11) = 0 := by decide
  have haccept : (schnorr ι (2 : ZMod 11)).Accepts key.2 (r • 2) c (r + c • (6 • key.2)) := by
    rw [schnorr_accepts_iff]
    simp only [smul_eq_mul, Function.Embedding.refl_apply]
    linear_combination (c * key.2) * h11
  have hverify : (schnorr ι (2 : ZMod 11)).verify key.2 (r • 2) c (r + c • (6 • key.2)) = true :=
    haccept
  simp only [hverify, _root_.PMF.pure_apply, ite_true, le_refl]

/-- Rewinding the impersonator that always succeeds computes a discrete logarithm with
probability at least `1 - 1 / 11`. -/
example : (10 / 11 : ℝ) ≤ Game.succProbability (oneWayGame (schnorrKeyGen (2 : ZMod 11))
    (fun α u => α • (2 : ZMod 11) = u) (knower.rewind (linearExtract ι))) := by
  have h := sq_sub_le_oneWayGame_rewind
    ((schnorr_specialSoundness (ι := ι) (g := (2 : ZMod 11))).specialSoundOn (schnorrKeyGen 2))
    knower
  rw [succProbability_knower, ZMod.card] at h
  norm_num at h ⊢
  exact h

/-- An eavesdropper on Schnorr identification in `ZMod 11` that ignores the eavesdropped views
and runs `knower` has the same attack distribution as the direct simulated-view impersonator. -/
example :
    let A : Impersonator (ZMod 11 × (Fin 2 → ZMod 11 × ZMod 11 × ZMod 11)) (ZMod 11) (ZMod 11)
      (ZMod 11) :=
      { State := ZMod 11 × ZMod 11
        commit := fun u => knower.commit u.1
        respond := knower.respond }
    (schnorr ι (2 : ZMod 11)).eavesdropAttack (schnorrKeyGen 2) 2 A =
      (schnorr ι (2 : ZMod 11)).directAttack (schnorrKeyGen 2) (A.withSimulatedViews
        (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod 11) (ZMod 11) 2) id ι)) :=
  schnorr_eavesdropAttack_eq_directAttack _

end ComplexityTests.Crypto.SigmaIdentification
