/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Protocols.VOLE.Basic

/-!
# Tests for VOLE correlations, IT-MACs, and VOLE-in-the-head

Concrete examples over `ZMod 5` and `ZMod 7` exercising `VOLECorrelation`, `voleSample`,
`voleIdealDist`, linear homomorphism (`add`, `smul`, `addConst`, `Valid.linearComb`), witness
commitment (`voleCommitWitness`, `voleAdjustReceiver`), IT-MAC unforgeability
(`voleOpen_unique_delta_of_ne`, `card_filter_voleVerifyOpening_le_one`,
`toOuterMeasure_voleVerifyOpening_le`), the Quicksilver / VOLE degree-2 multiplication check
(`voleMulCheck`), and `voleInTheHeadSigma`.
-/

namespace CslibFrontierTests.Crypto.VOLE

open Cslib.Crypto.Protocols Cslib.Crypto.Protocols.VOLE

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- A concrete length-2 VOLE correlation over `ZMod 5` with `u = ![2, 4]`, `v = ![1, 3]`, and
global key `Δ = 3`. -/
def sample5 : VOLECorrelation (ZMod 5) 2 :=
  voleSample ![2, 4] ![1, 3] 3

example : sample5.Valid := by decide
example : sample5.w 0 = 2 := by decide
example : sample5.w 1 = 0 := by decide

-- Ideal VOLE distribution support characterization and delta marginal over ZMod 5.
example : sample5 ∈ (voleIdealDist (ZMod 5) 2).support := by
  rw [mem_support_voleIdealDist_iff]
  decide

example :
    (voleIdealDist (ZMod 5) 2).map VOLECorrelation.delta =
      Cslib.Probability.PMF.uniformOfFintype (ZMod 5) :=
  voleIdealDist_map_delta 2

-- Linear homomorphism on concrete correlations over ZMod 5.
example : (sample5.add sample5).Valid :=
  (valid_voleSample _ _ _).add (valid_voleSample _ _ _) rfl

example : (sample5.smul 4).Valid :=
  (valid_voleSample _ _ _).smul 4

example : (sample5.addConst ![3, 1]).Valid :=
  (valid_voleSample _ _ _).addConst ![3, 1]

example (coeff : Fin 2 → ZMod 5) :
    ∑ i, coeff i * sample5.w i =
      (∑ i, coeff i * sample5.u i) * sample5.delta + ∑ i, coeff i * sample5.v i :=
  (valid_voleSample _ _ _).linearComb coeff

/-- Witness commitment to `x = ![1, 2]` over `ZMod 5` using `sample5`. -/
def witness5 : Fin 2 → ZMod 5 := ![1, 2]

example : voleCommitWitness witness5 sample5.u 0 = 4 := by decide
example : voleCommitWitness witness5 sample5.u 1 = 3 := by decide
example : (sample5.commitWitness witness5).Valid :=
  (valid_voleSample _ _ _).commitWitness witness5
example :
    voleVerifyOpening (sample5.commitWitness witness5).w sample5.delta witness5 sample5.v := by
  decide

-- Perfect hiding of witness commitment over ZMod 5.
example :
    (Cslib.Probability.PMF.uniformOfFintype (Fin 2 → ZMod 5)).map (voleCommitWitness witness5) =
      Cslib.Probability.PMF.uniformOfFintype (Fin 2 → ZMod 5) :=
  voleCommitWitness_uniform witness5

example (x₂ : Fin 2 → ZMod 5) :
    (Cslib.Probability.PMF.uniformOfFintype (Fin 2 → ZMod 5)).map (voleCommitWitness witness5) =
      (Cslib.Probability.PMF.uniformOfFintype (Fin 2 → ZMod 5)).map (voleCommitWitness x₂) :=
  voleCommitWitness_indep witness5 x₂

/-- A forged opening `x' = ![0, 2] ≠ witness5` with `v' = ![4, 3]` over `ZMod 5` is accepted at
the unique global key `Δ = (4 - 1) / (1 - 0) = 3` and rejected at every other key in `ZMod 5`. -/
def forgedX5 : Fin 2 → ZMod 5 := ![0, 2]
def forgedV5 : Fin 2 → ZMod 5 := ![4, 3]

theorem forgedX5_ne_witness5 : forgedX5 ≠ witness5 := by
  intro h
  have h0 : forgedX5 0 = witness5 0 := congrFun h 0
  revert h0
  decide

example :
    (Finset.univ.filter fun delta : ZMod 5 =>
      ∀ i, witness5 i * delta + sample5.v i = forgedX5 i * delta + forgedV5 i) = {3} := by
  decide

example :
    (Finset.univ.filter fun delta : ZMod 5 =>
      ∀ i, witness5 i * delta + sample5.v i = forgedX5 i * delta + forgedV5 i).card ≤ 1 :=
  card_filter_voleVerifyOpening_le_one (v := sample5.v) (v' := forgedV5) forgedX5_ne_witness5

example :
    (Cslib.Probability.PMF.uniformOfFintype (ZMod 5)).toOuterMeasure
      {delta : ZMod 5 |
        ∀ i, witness5 i * delta + sample5.v i = forgedX5 i * delta + forgedV5 i} ≤
      (Fintype.card (ZMod 5) : ENNReal)⁻¹ :=
  toOuterMeasure_voleVerifyOpening_le (v := sample5.v) (v' := forgedV5) forgedX5_ne_witness5

/-- Concrete Quicksilver / VOLE degree-2 multiplication check over `ZMod 7`:
`x = 3`, `y = 4`, `z = 3 * 4 = 5 (mod 7)` with MAC masks `v_x = 2`, `v_y = 6`, `v_z = 1`
and global key `Δ = 5`. -/
example :
    let x : ZMod 7 := 3
    let y : ZMod 7 := 4
    let z : ZMod 7 := 5
    let vx : ZMod 7 := 2
    let vy : ZMod 7 := 6
    let vz : ZMod 7 := 1
    let delta : ZMod 7 := 5
    let wx := x * delta + vx
    let wy := y * delta + vy
    let wz := z * delta + vz
    wx * wy - wz * delta =
      voleMulCrossTerm x vx y vy vz * delta + voleMulConstTerm vx vy :=
  voleMulCheck rfl rfl rfl (by decide)

-- Concrete VOLE-in-the-head Sigma protocol instance over ZMod 5.
section SigmaTest

noncomputable abbrev linearMap5 : Unit → (Fin 2 → ZMod 5) →ₗ[ZMod 5] ZMod 5 :=
  fun _ => Fintype.linearCombination (ZMod 5) ![1, 2]

abbrev target5 : Unit → ZMod 5 := fun _ => 0

noncomputable abbrev sigma5 :
    SigmaProtocol (Fin 2 → ZMod 5) Unit (ZMod 5) (ZMod 5) (Fin 2 → ZMod 5) :=
  voleInTheHeadSigma linearMap5 target5 (Function.Embedding.refl (ZMod 5))

example : sigma5.Complete fun x y => linearMap5 y x = target5 y :=
  voleInTheHeadSigma_complete linearMap5 target5 (Function.Embedding.refl (ZMod 5))

example :
    sigma5.SpecialSoundness (fun x y => linearMap5 y x = target5 y)
      (voleInTheHeadExtract (Function.Embedding.refl (ZMod 5))) :=
  voleInTheHeadSigma_specialSoundness linearMap5 target5 (Function.Embedding.refl (ZMod 5))

example :
    sigma5.SpecialHVZK (fun x y => linearMap5 y x = target5 y)
      (voleInTheHeadSimulate linearMap5 target5 (Function.Embedding.refl (ZMod 5))) :=
  voleInTheHeadSigma_specialHVZK linearMap5 target5 (Function.Embedding.refl (ZMod 5))

end SigmaTest

end CslibFrontierTests.Crypto.VOLE
