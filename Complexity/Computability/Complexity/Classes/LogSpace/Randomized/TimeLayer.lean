/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.LogSpace.Randomized.ConfigurationReader
public import Complexity.Foundations.LinearAlgebra.Matrix.TimeLayer
import Mathlib.Tactic.Positivity

/-!
# Clocked fair-coin configuration matrices

The ordinary configuration matrix keeps halted views absorbing and counts both coins, including
coincident successors. Halving it gives a nonnegative matrix with row mass exactly one on any
closed finite set of views. Clocking this actual matrix and paying the accepting-view indicator
only at the final time gives the strictly forward system of [OpenAI2026LogSpace, Lemma 2.1].
Its explicitly constructed potential lies in `[0,1]` at every clocked view. At clock zero it is
the actual finite-time acceptance probability, and also the existing finite sum of live-matrix
acceptance terms. No halting-time hypothesis is needed for these finite-horizon identities.

The clocked matrix entry is also identified with the native compact-ID coin count, supplied
with its one scanned input symbol. This preserves the distinction between an absorbing halted
view before the horizon and a terminal clock layer with zero outgoing weight.

This file proves mathematical structure and acceptance semantics. It does not implement bounded
vertex enumeration, compose the symbol query with the original input, or construct incoming
paired ports or the recursive estimator. In particular it is not a proof of `BPL ⊆ L`.

## Main results

* `Turing.MultiTapePTM.half_configMatrix_mulVec_one`: actual fair-coin row mass.
* `Turing.MultiTapePTM.timeLayer_configMatrix_potential_mem_Icc`: bounded potential at every view.
* `Turing.MultiTapePTM.timeLayer_configMatrix_acceptance`: the clock-zero acceptance identity.
* `Turing.MultiTapePTM.ConfigurationGraph.timeLayer_configMatrix_eq_coinCountWithSymbol`:
  the actual local reader gives each nonzero clocked entry.
* `Cslib.Complexity.exists_timeLayer_configMatrix_of_mem_BPL`: polynomial-size strict-forward
  systems with the actual `2/3` versus `1/3` acceptance gap.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 2, Lemma 2.1, `model.tex`, terminal-time configuration reduction
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

/-- The accepting halted-view indicator lies in `[0,1]` at every view. -/
theorem Turing.FiniteCfg.acceptVec_mem_Icc {k : ℕ} {State : Type} {R : Type*}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {V : Finset (Turing.FiniteCfg k Bool State)} :
    Turing.FiniteCfg.acceptVec R V ∈ Set.Icc 0 1 := by
  classical
  constructor <;> intro x <;> unfold Turing.FiniteCfg.acceptVec <;> split_ifs <;> simp

namespace Turing.MultiTapePTM

open Matrix

variable {k : ℕ} {State : Type} (machine : MultiTapePTM k Bool State)
  {R : Type*} [Field R] {V : Finset (FiniteCfg k Bool State)}

section Ordered

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- The normalized ordinary coin matrix is entrywise nonnegative, including absorbing rows. -/
theorem half_configMatrix_nonneg :
    ∀ x y : V, 0 ≤ ((2 : R)⁻¹ • machine.configMatrix R V) x y := by
  classical
  intro x y
  change 0 ≤ (2 : R)⁻¹ * ∑ b : Bool, if machine.viewCoinStep x b = y then 1 else 0
  positivity

/-- Closedness of the actual view set makes every normalized ordinary coin row sum to one. -/
theorem half_configMatrix_mulVec_one
    (hV : ∀ finite ∈ V, ∀ bit, machine.viewCoinStep finite bit ∈ V) :
    ((2 : R)⁻¹ • machine.configMatrix R V) *ᵥ 1 = 1 := by
  classical
  ext x
  rw [Matrix.smul_mulVec, Pi.smul_apply, configMatrix, Matrix.coinStepMatrix_mulVec hV]
  simp [smul_eq_mul]

open scoped Classical in
/-- The actual clocked configuration potential is bounded on every state, including views
unreachable from the designated start. Closedness is the only graph hypothesis. -/
theorem timeLayer_configMatrix_potential_mem_Icc
    (hV : ∀ finite ∈ V, ∀ bit, machine.viewCoinStep finite bit ∈ V) (T : ℕ) :
    Matrix.timeLayerPotential T ((2 : R)⁻¹ • machine.configMatrix R V)
      (FiniteCfg.acceptVec R V) ∈ Set.Icc 0 1 := by
  classical
  exact Matrix.timeLayerPotential_mem_Icc (half_configMatrix_nonneg machine)
    (half_configMatrix_mulVec_one machine hV).le (FiniteCfg.acceptVec_mem_Icc (R := R)) T

end Ordered

open scoped Classical in
/-- At the initial clocked view, the explicit potential is the machine's finite-time
acceptance probability. The horizon may be zero and the machine need not yet have halted. -/
theorem timeLayer_configMatrix_acceptance {input : List Bool}
    (hV : ∀ finite ∈ V, ∀ bit, machine.viewCoinStep finite bit ∈ V)
    (hinit : machine.toNTM.initView input ∈ V) (T : ℕ) :
    Matrix.timeLayerPotential T ((2 : R)⁻¹ • machine.configMatrix R V)
      (FiniteCfg.acceptVec R V) (toLex (0, ⟨_, hinit⟩)) =
        (machine.acceptCoins input T : R) / 2 ^ T := by
  classical
  rw [Matrix.timeLayerPotential_zero]
  exact (acceptCoins_div_eq_configMatrix_pow_mulVec R hV hinit T).symm

open scoped Classical in
/-- The terminal-reward convention agrees exactly with the existing first-stop sum of live
acceptance terms; these are two proved expressions for the same actual probability. -/
theorem timeLayer_configMatrix_eq_sum_live [CharZero R] {input : List Bool}
    (hV : ∀ finite ∈ V, ∀ bit, machine.viewCoinStep finite bit ∈ V)
    (hinit : machine.toNTM.initView input ∈ V) (T : ℕ) :
    Matrix.timeLayerPotential T ((2 : R)⁻¹ • machine.configMatrix R V)
      (FiniteCfg.acceptVec R V) (toLex (0, ⟨_, hinit⟩)) =
        ∑ t ∈ Finset.range (T + 1),
          (((2 : R)⁻¹ • machine.liveConfigMatrix R V) ^ t *ᵥ FiniteCfg.acceptVec R V)
            ⟨_, hinit⟩ := by
  classical
  rw [timeLayer_configMatrix_acceptance machine hV hinit]
  exact acceptCoins_div_eq_sum_liveConfigMatrix R hV hinit T

namespace ConfigurationGraph

open MultiTapeNTM.ConfigurationGraph

variable [Fintype State]

/-- A clocked ordinary entry is half the certified local coin count exactly when the target
clock is the next one, and zero otherwise. Representation hypotheses concern only the two
actual views, and the original input is used at its explicit `queryIndex`. -/
theorem timeLayer_configMatrix_eq_coinCountWithSymbol {B T : ℕ} (i j : Fin (T + 1))
    (x y : V) (hinput : x.val.input = y.val.input)
    (hx : MultiTapeNTM.outputClass x.val.output = x.val.output)
    (hy : MultiTapeNTM.outputClass y.val.output = y.val.output)
    (hfitX : Fits B (registers x.val)) (hfitY : Fits B (registers y.val)) :
    Matrix.timeLayer T ((2 : R)⁻¹ • machine.configMatrix R V)
      (toLex (i, x)) (toLex (j, y)) =
        if i.val + 1 = j.val then
          (coinCountWithSymbol machine B x.val.input.length (vertexID B x.val) (vertexID B y.val)
            x.val.input[queryIndex (k := k) B (vertexID B x.val)]? : R) / 2 else 0 := by
  change (if i.val + 1 = j.val then (2 : R)⁻¹ * machine.configMatrix R V x y else 0) = _
  rw [← coinCountWithSymbol_eq_configMatrix machine x y hinput hx hy hfitX hfitY]
  simp only [div_eq_inv_mul]

/-- Actual reachability and logarithmic space discharge the representation conditions for
the clocked entry reader at the standard polynomial radix. -/
theorem timeLayer_configMatrix_eq_coinCountWithSymbol_of_reachable (c : ℕ) {input : List Bool}
    (hs : machine.toNTM.RunsInSpace input (c * (Nat.log2 input.length + 1)))
    (hV : ∀ v ∈ V, Relation.ReflTransGen machine.toNTM.ViewStep (machine.toNTM.initView input) v)
    {T : ℕ} (i j : Fin (T + 1)) (x y : V) :
    let B := radix (radixExponent State c) input.length
    Matrix.timeLayer T ((2 : R)⁻¹ • machine.configMatrix R V)
      (toLex (i, x)) (toLex (j, y)) =
        if i.val + 1 = j.val then
          (coinCountWithSymbol machine B input.length (vertexID B x.val) (vertexID B y.val)
            input[queryIndex (k := k) B (vertexID B x.val)]? : R) / 2 else 0 := by
  change (if i.val + 1 = j.val then (2 : R)⁻¹ * machine.configMatrix R V x y else 0) = _
  rw [← coinCountWithSymbol_eq_configMatrix_of_reachable (R := R) machine c hs hV x y]
  simp only [div_eq_inv_mul]

end ConfigurationGraph

end Turing.MultiTapePTM

namespace Cslib.Complexity

open _root_.Turing Matrix

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- **A concrete strict-forward matrix system for `BPL`.** Clock the actual ordinary
configuration matrix up to the existing polynomial halting bound `T`. There are at most
`(T + 1) * T` clocked views, the terminal reward is zero or one, and the explicitly defined
potential solves the system, lies in `[0,1]`, and retains the `2/3` versus `1/3` gap.

The order within a layer is chosen by a finite equivalence; it makes no algorithmic enumeration
claim. The clocked entries separately have the compact-reader interpretation above. Bounded-ID
enumeration, whole-input access, paired ports, and a native estimator remain separate. -/
theorem exists_timeLayer_configMatrix_of_mem_BPL (h : A ∈ BPL enc) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : MultiTapePTM k Bool State) (d : ℕ),
      ∀ a,
        let T := 2 * (2 * ((enc a).length + 1)) ^ d
        ∃ (V : Finset (FiniteCfg k Bool State)) (hinit : M.toNTM.initView (enc a) ∈ V)
          (order : LinearOrder V),
          letI := order
          let P := (2 : ℚ)⁻¹ • M.configMatrix ℚ V
          let C := timeLayer T P
          let e := timeLayerReward T (FiniteCfg.acceptVec ℚ V)
          let p := timeLayerPotential T P (FiniteCfg.acceptVec ℚ V)
          Fintype.card (Lex (Fin (T + 1) × V)) ≤ (T + 1) * T ∧
          C.IsStrictUpperTriangular ∧ (∀ x y, 0 ≤ C x y) ∧ C *ᵥ 1 ≤ 1 ∧
          (∀ x, e x = 0 ∨ e x = 1) ∧ (1 - C) *ᵥ p = e ∧ (1 - C)⁻¹ *ᵥ e = p ∧
          p ∈ Set.Icc 0 1 ∧
          (a ∈ A → 2 / 3 ≤ p (toLex (0, ⟨_, hinit⟩))) ∧
          (a ∉ A → p (toLex (0, ⟨_, hinit⟩)) ≤ 1 / 3) := by
  classical
  obtain ⟨k, State, hfin, M, d, hM⟩ := exists_configMatrix_of_mem_BPL h
  refine ⟨k, State, hfin, M, d, fun a => ?_⟩
  obtain ⟨V, hinit, hcard, hclosed, hreach, htime, _, hmem, hnot⟩ := hM a
  -- Keep the existing equality decision so the chosen order uses the same matrix powers.
  let decV : DecidableEq V := inferInstance
  let baseOrder : LinearOrder V := LinearOrder.lift' V.equivFin V.equivFin.injective
  let order : LinearOrder V :=
    { baseOrder with
      toDecidableEq := decV
      compare := fun a b =>
        @compareOfLessAndEq V a b baseOrder.toLT (baseOrder.toDecidableLT a b) decV
      compare_eq_compareOfLessAndEq := fun _ _ => rfl }
  refine ⟨V, hinit, order, ?_⟩
  have hP0 := M.half_configMatrix_nonneg (R := ℚ) (V := V)
  have hP1 := (M.half_configMatrix_mulVec_one (R := ℚ) hclosed).le
  refine ⟨?_, timeLayer_isStrictUpperTriangular _ _, timeLayer_nonneg hP0 _,
    timeLayer_mulVec_one_le hP1 _, ?_, one_sub_timeLayer_mulVec _ _ _,
    inv_one_sub_timeLayer_mulVec _ _ _, M.timeLayer_configMatrix_potential_mem_Icc hclosed _,
    ?_, ?_⟩
  · rw [card_timeLayer, Fintype.card_coe]
    exact Nat.mul_le_mul_left _ hcard
  · intro x
    unfold timeLayerReward FiniteCfg.acceptVec
    split_ifs <;> simp
  · intro ha
    rw [M.timeLayer_configMatrix_acceptance hclosed hinit,
      M.acceptCoins_div_eq_inv_mulVec ℚ htime hclosed hreach hinit]
    exact hmem ha
  · intro ha
    rw [M.timeLayer_configMatrix_acceptance hclosed hinit,
      M.acceptCoins_div_eq_inv_mulVec ℚ htime hclosed hreach hinit]
    exact hnot ha

end Cslib.Complexity
