/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Communication.FoolingSet
import CslibFrontier.Computability.Communication.Rank
import CslibFrontier.Computability.Communication.Discrepancy
import CslibFrontier.Probability.PMF

/-! Concrete arbitrary tilings, minimum-size bounds, uniform discrepancy and empty domains. -/

namespace CslibFrontierTests.CommunicationTilings

open Cslib Cslib.Communication Cslib.Probability Finset

private def eqBool (x y : Bool) : Bool := decide (x = y)

private theorem equality_fooling :
    IsFoolingSet eqBool true {(false, false), (true, true)} := by
  simp [IsFoolingSet, eqBool]

-- These rectangles are built from inputs, without choosing a communication protocol.
example : (RectanglePartition.singletons eqBool).size = 4 := by simp [RectanglePartition.singletons]

private theorem tiling_le_four : tilingNumber eqBool ≤ 4 := by
  simpa [RectanglePartition.singletons] using
    (RectanglePartition.singletons eqBool).tilingNumber_le
      (RectanglePartition.run_singletons eqBool)

example : 2 ≤ tilingNumber eqBool := by
  simpa using equality_fooling.card_le_tilingNumber

-- The rank bound uses the zero/one matrix, which here is the two-by-two identity.
example : 2 ≤ tilingNumber eqBool := by
  have hM : communicationMatrix ℝ eqBool = 1 := by
    ext x y
    simp [communicationMatrix, eqBool, Matrix.one_apply]
  have h := rank_communicationMatrix_le_tilingNumber ℝ eqBool
  simpa [hM] using h

-- The minimum-number discrepancy theorem yields a concrete uniform lower bound.
example : (1 : ℝ) / 4 ≤
    discrepancy (PMF.uniformOfFintype (Bool × Bool)) eqBool := by
  have h := one_le_tilingNumber_mul_discrepancy (PMF.uniformOfFintype (Bool × Bool)) eqBool
  have hn : (tilingNumber eqBool).toNat ≤ 4 :=
    ENat.toNat_le_toNat tiling_le_four (by decide)
  have hn' : ((tilingNumber eqBool).toNat : ℝ) ≤ 4 := by exact_mod_cast hn
  nlinarith [discrepancy_nonneg (ν := PMF.uniformOfFintype (Bool × Bool)) (f := eqBool)]

private theorem constant_tilingNumber : tilingNumber (fun (_ _ : Unit) => true) = 1 := by
  apply le_antisymm
  · exact (RectanglePartition.constant Unit Unit true).tilingNumber_le
      (RectanglePartition.run_constant Unit Unit true)
  · have hS : IsFoolingSet (fun (_ _ : Unit) => true) true {((), ())} := by
      unfold IsFoolingSet
      simp
    simpa using hS.card_le_tilingNumber

-- An extra empty piece is charged, but does not lower the minimum.
private def padded : RectanglePartition Unit Unit Bool where
  size := 2
  alice i := if i = 0 then Set.univ else ∅
  bob _ := Set.univ
  output _ := true
  partition _ _ := by
    refine ⟨0, by simp, ?_⟩
    intro i hi
    by_contra h
    simpa [h] using hi.1

example : padded.size = 2 ∧ tilingNumber padded.run = 1 := by
  have hr : padded.run = fun _ _ => true := by
    funext x y
    exact RectanglePartition.run_eq_output (i := ⟨0, by decide⟩) (by simp [padded]) trivial
  exact ⟨rfl, hr ▸ constant_tilingNumber⟩

-- A point mass on the four-point domain tests nonuniform inputs.
example : (1 : ℝ) ≤ discrepancy (PMF.pure (false, false)) (fun (_ _ : Bool) => true) := by
  have h := (RectanglePartition.constant Bool Bool true).one_le_size_mul_discrepancy
    (RectanglePartition.run_constant Bool Bool true) (PMF.pure (false, false))
  simpa only [RectanglePartition.constant, Nat.cast_one, one_mul] using h

private def emptyPartition : RectanglePartition Empty Bool Bool where
  size := 0
  alice := Fin.elim0
  bob := Fin.elim0
  output := Fin.elim0
  partition x := nomatch x

example (f : Empty → Bool → Bool) : tilingNumber f = 0 := by
  refine le_antisymm (emptyPartition.tilingNumber_le ?_) bot_le
  funext x
  exact nomatch x

-- A zero-piece family cannot cover even the smallest inhabited product.
example (p : RectanglePartition Unit Unit Bool) : 0 < p.size := by
  have h := (p.part () ()).isLt
  omega

end CslibFrontierTests.CommunicationTilings
