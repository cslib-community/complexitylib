/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module

import Complexity.Computability.LogSpaceDerandomization.HierarchyRankEnvironment

/-! Arbitrary-prime clients exercise full spectator coordinates and nonconstant dense rows. -/

set_option linter.privateModule false

namespace ComplexityTests.HierarchyRankEnvironment

open Finset Matrix Matrix.HierarchyParams Cslib Cslib.Probability RotationMap
open H4RankEnvironment
open scoped BigOperators

variable {P : ℕ} [Fact P.Prime]

-- Every supplied prime admits a horizon, and a supplied larger horizon has the actual grid.
example (K : ℕ) (hK : 2 ^ K ≤ P) : ∃ H : Horizon P, H.maxExponent = K := by
  exact ⟨⟨K, P - 1, hK, Nat.sub_lt (Fact.out : P.Prime).pos (by decide)⟩, rfl⟩

-- The spectator is retained as a full slice, at its public identifier, rather than frozen.
example (Ls Lt : ℕ) (a b : ZMod P) :
    pairSide (P := P) (0 : Fin 3) 2 Ls Lt 1 = P ∧
      pairId (0 : Fin 3) 2 a b 1 = 0 := by
  simp [pairSide, pairId]

-- Inverse transport really preserves the spectator frame on every retained draw.
example (Ls Lt : ℕ) (a b : Fin 2 → ZMod P) (x y : Fin 2)
    (σ : RetainedPairSlice (X (0 : Fin 3) Ls a) (Y 2 Lt b) x y) :
    (((pairEquiv 0 2 (by decide) Ls Lt a b x y).symm
      (pairEquiv 0 2 (by decide) Ls Lt a b x y σ)).val 1) = σ.val 1 := by
  rw [Equiv.symm_apply_apply]

-- An actual nonconstant identity row gives mean one on the diagonal and zero off it.
-- This uses primitive frame laws for every prime, not a supplied mean certificate.
example (D : ZMod P) (hD : D ≠ 0) (suffix : List (ZMod P)) (H : Horizon P)
    (x y : ZMod P) (hxy : x ≠ y) :
    let A := explicitDense (J := 3) D hD 2 suffix H 0 (Nat.zero_le _)
      P P (Fact.out : P.Prime).pos le_rfl le_rfl
    (𝔼 σ ∈ ({σ : Environment P 3 | frameRetains P 4 P (σ 2)
      (CopyPadding.identifier D suffix x)} : Finset _), A.direct 1 σ x x) = 1 ∧
    (𝔼 σ ∈ ({σ : Environment P 3 | frameRetains P 4 P (σ 2)
      (CopyPadding.identifier D suffix y)} : Finset _), A.direct 1 σ x y) = 0 := by
  constructor
  · exact explicitDense_nonzero D hD 2 suffix H x
  · have h := explicitDense_mean (J := 3) D hD 2 suffix H 0 (Nat.zero_le _)
      P P (Fact.out : P.Prime).pos le_rfl le_rfl (1 : Matrix (ZMod P) (ZMod P) ℝ)
      (fun a b => by
        change 0 ≤ if a = b then (1 : ℝ) else 0
        split_ifs <;> norm_num)
      (fun a => by
        change (∑ b : ZMod P, if a = b then (1 : ℝ) else 0) ≤ 1
        simp) x y
    simpa only [Matrix.one_apply_ne hxy, zero_div, H4RankEnvironment.cutoff,
      polynomialSwitch4_of_le (by norm_num : (1 : ℝ) / 2 < 1) (by norm_num : (0 : ℝ) ≤ 1 / 2),
      mul_zero] using h

-- Actual residual requests preserve the rank/usage grid with a narrowed negative usage.
example :
    let r := (HierarchyTask.rawRequests (k := 1) 2 3 .residual
      (gridChannel (P := P) (0 : Fin 3) 0 [1])
      (gridChannel 1 1 [2]) (gridChannel 2 2 [3]) (rate 3)).negative
    r = some ⟨.row 2 (.normalized 0), gridChannel 0 0 [1],
      gridChannel 2 1 [3], gridChannel 2 2 [3]⟩ := by
  dsimp only [HierarchyTask.rawRequests, gridChannel, HierarchyTask.correctionAtomTask]
  norm_num [rate]
  rfl

end ComplexityTests.HierarchyRankEnvironment
