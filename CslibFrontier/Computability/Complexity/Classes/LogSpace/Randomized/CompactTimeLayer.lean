/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized.CompactMatrix
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.TimeLayer.Fin
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.CounterBounds

/-!
# The clocked BPL matrix on consecutive compact identifiers

The entire compact configuration box is clocked and indexed by the explicit integer
`clock * vertexBound + baseID`. Its real-valued matrix is nonnegative, substochastic and strictly
forward in that numeric order. Terminal rewards and the remaining-time potential satisfy the
linear and inverse equations, with potential in `[0,1]` at every ID, and retain the actual BPL
acceptance gap at the encoded initial configuration.

The endpoint preserves the original logarithmic-space constant and derives the fitting radix
from it. It does not choose an arbitrary ordering of reachable views. The ordinary entries are
the counts written by the native initialized table, via `compactCoinMatrix_eq_coinTable`.
The initialized clocked payload is supplied by `Randomized.ClockedTable`. Complete instance
packaging, paired ports and the native recursive estimator remain open.

## Main results

* `Turing.MultiTapePTM.ConfigurationGraph.finTimeLayer_compactCoinMatrix_acceptance`: clock-zero
  acceptance for the explicit finite indexing and any horizon.
* `Turing.MultiTapePTM.ConfigurationGraph.compactTimeLayer_polyClock`: the gap-independent
  matrix, reward and potential facts at the polynomial clock, shared by the `RL` and `BPL` layers.
* `Cslib.Complexity.exists_compactTimeLayer_of_mem_BPL`: the canonical polynomial-size
  strict-forward real matrix with the actual `2/3` versus `1/3` BPL gap.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 2, Lemma 2.1, `model.tex`, terminal-time construction
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Turing.MultiTapePTM.ConfigurationGraph

open MultiTapeNTM.ConfigurationGraph Matrix

variable {k : ℕ} {State : Type} [Fintype State] {machine : MultiTapePTM k Bool State}
  {R : Type*} [Field R]

/-- Clocking the ambient compact matrix preserves the machine's actual finite-time acceptance
probability at the explicit clock-zero start ID. -/
theorem finTimeLayer_compactCoinMatrix_acceptance (c : ℕ) {w : List Bool}
    (hs : machine.toNTM.RunsInSpace w (c * (Nat.log2 w.length + 1))) (T : ℕ) :
    let B := radix (radixExponent State c) w.length
    let N := vertexBound (k := k) B
    finTimeLayerPotential T (compactCoinMatrix machine R B w)
      (compactAcceptVec (k := k) (State := State) R B w.length)
      ((timeLayerEquiv T N).symm (toLex (0, compactStart machine c hs))) =
        (machine.acceptCoins w T : R) / 2 ^ T := by
  dsimp only
  rw [finTimeLayerPotential_zero, compactCoinMatrix_pow_accept]

/-- **The clocked compact layer at the polynomial clock.** On a word `w`, the compact matrix
clocked at `T = Turing.polyClock d w.length` has polynomial dimension, is strictly forward,
nonnegative and substochastic, has a `0`/`1` terminal reward, and its potential solves the linear
and inverse equations with values in `[0,1]`. These facts need no space bound; the `RL` and `BPL`
compact layers add the acceptance gap through
`Turing.MultiTapePTM.ConfigurationGraph.finTimeLayer_compactCoinMatrix_acceptance`. -/
theorem compactTimeLayer_polyClock (machine : MultiTapePTM k Bool State) (c d : ℕ)
    (w : List Bool) :
    let D := radixExponent State c
    let B := radix D w.length
    let N := vertexBound (k := k) B
    let T := polyClock d w.length
    let P := compactCoinMatrix machine ℝ B w
    let e₀ := compactAcceptVec (k := k) (State := State) ℝ B w.length
    let S := finTimeLayer T P
    let e := finTimeLayerReward T e₀
    let p := finTimeLayerPotential T P e₀
    Fintype.card (Fin ((T + 1) * N)) ≤
      (2 * (w.length + 1)) ^ (D * Fintype.card (Register k) + d + 2) ∧
    S.IsStrictUpperTriangular ∧ (∀ x y, 0 ≤ S x y) ∧ S *ᵥ 1 ≤ 1 ∧
    (∀ x, e x = 0 ∨ e x = 1) ∧ (1 - S) *ᵥ p = e ∧ (1 - S)⁻¹ *ᵥ e = p ∧
    p ∈ Set.Icc 0 1 := by
  intro D B N T P e₀ S e p
  have hP0 := compactCoinMatrix_nonneg (machine := machine) (R := ℝ) B w
  have hP1 := compactCoinMatrix_mulVec_one_le (machine := machine) (R := ℝ) B w
  refine ⟨?_, finTimeLayer_isStrictUpperTriangular _ _, finTimeLayer_nonneg hP0 _,
    finTimeLayer_mulVec_one_le hP1 _, fun x => ?_, one_sub_finTimeLayer_mulVec _ _ _,
    inv_one_sub_finTimeLayer_mulVec _ _ _,
    finTimeLayerPotential_mem_Icc hP0 hP1 (compactAcceptVec_mem_Icc _ _) _⟩
  · rw [Fintype.card_fin]
    exact (Nat.le_succ _).trans (clockedVertexBound_add_one_le_pow (k := k) D d w.length)
  · unfold e finTimeLayerReward timeLayerReward e₀ compactAcceptVec
    dsimp only [Function.comp_apply]
    split_ifs <;> simp

end Turing.MultiTapePTM.ConfigurationGraph

namespace Cslib.Complexity

open _root_.Turing MultiTapeNTM.ConfigurationGraph MultiTapePTM.ConfigurationGraph Matrix

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- **The enumerated clocked BPL matrix.** An actual BPL witness supplies one fixed machine,
space constant and polynomial horizon. On every encoded word the full compact box, with numeric
clock/base IDs, gives a real strict-forward substochastic matrix and a terminal reward whose
bounded inverse potential has the original acceptance gap. The dimension is explicitly polynomial.

The space witness is produced by this theorem, and all radix, start and representation bounds
are derived from it. `Randomized.ClockedTable` supplies the initialized native matrix payload;
complete instance packaging and incoming paired-port computation remain separate. -/
theorem exists_compactTimeLayer_of_mem_BPL (h : A ∈ BPL enc) :
    ∃ (k : ℕ) (State : Type) (_ : Fintype State) (M : MultiTapePTM k Bool State) (c d : ℕ),
      ∀ a, ∃ hs : M.toNTM.RunsInSpace (enc a) (c * (Nat.log2 (enc a).length + 1)),
        let w := enc a
        let D := radixExponent State c
        let B := radix D w.length
        let N := vertexBound (k := k) B
        let T := polyClock d w.length
        let P := compactCoinMatrix M ℝ B w
        let e₀ := compactAcceptVec (k := k) (State := State) ℝ B w.length
        let S := finTimeLayer T P
        let e := finTimeLayerReward T e₀
        let p := finTimeLayerPotential T P e₀
        let x₀ := (timeLayerEquiv T N).symm (toLex (0, compactStart M c hs))
        M.toNTM.RunsInTime w T ∧
        Fintype.card (Fin ((T + 1) * N)) ≤
          (2 * (w.length + 1)) ^ (D * Fintype.card (Register k) + d + 2) ∧
        S.IsStrictUpperTriangular ∧ (∀ x y, 0 ≤ S x y) ∧ S *ᵥ 1 ≤ 1 ∧
        (∀ x, e x = 0 ∨ e x = 1) ∧ (1 - S) *ᵥ p = e ∧ (1 - S)⁻¹ *ᵥ e = p ∧
        p ∈ Set.Icc 0 1 ∧
        (a ∈ A → 2 / 3 ≤ p x₀) ∧ (a ∉ A → p x₀ ≤ 1 / 3) := by
  classical
  obtain ⟨k, State, _, M, c, d, hM, herr⟩ := exists_polyClock_of_mem_BPL h
  let : Fintype State := Fintype.ofFinite State
  refine ⟨k, State, inferInstance, M, c, d, fun a => ⟨hM.runsInSpace a, ?_⟩⟩
  obtain ⟨hmem, hnot⟩ := herr a
  obtain ⟨hcard, hS, hS0, hS1, he, hp, hinv, hIcc⟩ := compactTimeLayer_polyClock M c d (enc a)
  refine ⟨hM.runsInTime a, hcard, hS, hS0, hS1, he, hp, hinv, hIcc, fun ha => ?_, fun ha => ?_⟩
  · rw [finTimeLayer_compactCoinMatrix_acceptance, le_div_iff₀ (by positivity)]
    have hc := (Nat.cast_le (α := ℝ)).mpr (hmem ha)
    push_cast at hc
    linarith
  · rw [finTimeLayer_compactCoinMatrix_acceptance, div_le_iff₀ (by positivity)]
    have hc := (Nat.cast_le (α := ℝ)).mpr (hnot ha)
    push_cast at hc
    linarith

end Cslib.Complexity
