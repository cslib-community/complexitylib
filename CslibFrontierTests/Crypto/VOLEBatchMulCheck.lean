/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Protocols.VOLE.BatchMulCheck

/-!
# Batched VOLE multiplication examples

Two false gates with residuals `1, -1` cancel under deterministic equal weights. Uniform weights
with the adaptive reply `(r 0 - r 1, 0)` attain the mixture bound `13 / 25` over `ZMod 5`.
The same reply always passes over `ZMod 2`. The empty-batch bad event has probability zero.
-/

namespace CslibFrontierTests.Crypto.VOLEBatchMulCheck

open Cslib.Probability Cslib.Crypto.Protocols.VOLE
open scoped BigOperators ENNReal

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- Both constraints are false, despite their residuals adding to zero.
example : ∀ i : Fin 2, (0 : ZMod 5) * 0 ≠ (![-1, 1] : Fin 2 → ZMod 5) i := by decide

example (delta : ZMod 5) :
    ∑ i : Fin 2, (1 : ZMod 5) *
      ((0 * delta + 0) * (0 * delta + 0) - ((![-1, 1] : Fin 2 → ZMod 5) i * delta + 0) *
        delta) = 0 * delta + 0 := by
  simp [Fin.sum_univ_two]

/-- The sender sees the public weights before choosing its affine slope. -/
noncomputable def adaptiveBatch5 : PMF Bool := do
  let r ← PMF.uniformOfFintype (Fin 2 → ZMod 5)
  let ab ← PMF.pure (r 0 - r 1, (0 : ZMod 5))
  let delta ← PMF.uniformOfFintype (ZMod 5)
  return decide (∑ i : Fin 2, r i *
    ((0 * delta + 0) * (0 * delta + 0) - ((![-1, 1] : Fin 2 → ZMod 5) i * delta + 0) *
      delta) = ab.1 * delta + ab.2)

private theorem adaptiveBatch5_eq : adaptiveBatch5 =
    (PMF.uniformOfFintype ((Fin 2 → ZMod 5) × ZMod 5)).map
      (fun p => decide (∑ i : Fin 2, p.1 i *
        ((0 * p.2 + 0) * (0 * p.2 + 0) - ((![-1, 1] : Fin 2 → ZMod 5) i * p.2 + 0) *
          p.2) = (p.1 0 - p.1 1) * p.2 + 0)) := by
  rw [← PMF.uniformOfFintype_prod, PMF.map_bind]
  simp only [adaptiveBatch5, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.pure_bind, PMF.map_comp, Function.comp_def]
  rfl

-- Exact sharpness for the actual public-weights / adaptive-reply / independent-key sampler.
example : adaptiveBatch5.toOuterMeasure {true} = 13 / (25 : ℝ≥0∞) := by
  classical
  rw [adaptiveBatch5_eq, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_uniformOfFintype]
  simp only [Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq]
  have hcard : (Finset.univ.filter fun p : (Fin 2 → ZMod 5) × ZMod 5 =>
      ∑ i : Fin 2, p.1 i *
        ((0 * p.2 + 0) * (0 * p.2 + 0) - ((![-1, 1] : Fin 2 → ZMod 5) i * p.2 + 0) *
          p.2) = (p.1 0 - p.1 1) * p.2 + 0).card = 65 := by decide
  rw [hcard]
  norm_num only [Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
  rw [← div_eq_mul_inv, ENNReal.div_eq_div_iff (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)]
  norm_num

example : adaptiveBatch5.toOuterMeasure {true} ≤
    (5 : ℝ≥0∞)⁻¹ + (1 - (5 : ℝ≥0∞)⁻¹) * (2 / (5 : ℝ≥0∞)) := by
  simpa only [adaptiveBatch5, ZMod.card, Nat.cast_ofNat] using
    toOuterMeasure_voleMulCheck_batch_le (fun _ : Fin 2 => (0 : ZMod 5)) (fun _ => 0)
      ![-1, 1] (fun _ => 0) (fun _ => 0) (fun _ => 0)
      (fun r => PMF.pure (r 0 - r 1, 0)) ⟨0, by decide⟩

-- The sharp mixture is one over F2, where this false batch can always pass.
example (r : Fin 2 → ZMod 2) (delta : ZMod 2) :
    ∑ i : Fin 2, r i *
      ((0 * delta + 0) * (0 * delta + 0) - ((![-1, 1] : Fin 2 → ZMod 2) i * delta + 0) *
        delta) = (r 0 - r 1) * delta + 0 := by
  revert r delta
  decide

example : (2 : ℝ≥0∞)⁻¹ + (1 - (2 : ℝ≥0∞)⁻¹) * (2 / (2 : ℝ≥0∞)) = 1 := by
  rw [ENNReal.div_self (by norm_num) (by norm_num)]
  simp only [mul_one]
  simpa using ENNReal.inv_two_add_inv_two

-- Honest nonzero wires and masks accept every public weight vector and key.
example (r : Fin 2 → ZMod 5) (delta : ZMod 5) :
    ∑ i, r i * ((2 * delta + 1) * (3 * delta + 2) - (1 * delta + 4) * delta) =
      (∑ i, r i * voleMulCrossTerm 2 1 3 2 4) * delta +
        ∑ i, r i * voleMulConstTerm 1 2 := by
  exact voleMulCheck_sum r (fun _ => 2) (fun _ => 3) (fun _ => 1)
    (fun _ => 1) (fun _ => 2) (fun _ => 4) delta (fun _ => by decide)

-- A nontrivial randomized sender fixes wires and masks before seeing the public weights;
-- fresh reply randomness may depend on both that state and those weights.
example : (do
    let s ← PMF.uniformOfFintype (ZMod 5)
    let r ← PMF.uniformOfFintype (Fin 2 → ZMod 5)
    let ab ← (PMF.uniformOfFintype (ZMod 5 × ZMod 5)).map
      (fun seed : ZMod 5 × ZMod 5 => (seed.1 + s + r 0, seed.2))
    let delta ← PMF.uniformOfFintype (ZMod 5)
    return decide ((∃ i : Fin 2, s * s ≠ s * s + (![-1, 1] : Fin 2 → ZMod 5) i) ∧
      ∑ i, r i * ((s * delta + s) * (s * delta + s) -
        ((s * s + (![-1, 1] : Fin 2 → ZMod 5) i) * delta + s) * delta) =
          ab.1 * delta + ab.2)).toOuterMeasure {true} ≤ 3 / (5 : ℝ≥0∞) := by
  have hfalse (s : ZMod 5) : ∃ i : Fin 2, s * s ≠ s * s + (![-1, 1] : Fin 2 → ZMod 5) i := by
    refine ⟨0, ?_⟩
    simp
  simpa only [ZMod.card, Nat.cast_ofNat, hfalse, true_and] using
    toOuterMeasure_voleMulCheck_batch_bind_le_three_div (ι := Fin 2)
      (PMF.uniformOfFintype (ZMod 5))
      (fun s _ => s) (fun s _ => s) (fun s i => s * s + (![-1, 1] : Fin 2 → ZMod 5) i)
      (fun s _ => s) (fun s _ => s) (fun s _ => s)
      (fun s r => (PMF.uniformOfFintype (ZMod 5 × ZMod 5)).map
        (fun seed : ZMod 5 × ZMod 5 => (seed.1 + s + r 0, seed.2)))

-- An empty batch cannot contain a false multiplication, for any reply distribution.
example (reply : (Fin 0 → ZMod 5) → PMF (ZMod 5 × ZMod 5)) :
    (do
      let r ← PMF.uniformOfFintype (Fin 0 → ZMod 5)
      let ab ← reply r
      let delta ← PMF.uniformOfFintype (ZMod 5)
      return decide ((∃ _ : Fin 0, (0 : ZMod 5) * 0 ≠ 0) ∧
        ∑ i, r i * ((0 * delta + 0) * (0 * delta + 0) - (0 * delta + 0) * delta) =
          ab.1 * delta + ab.2)).toOuterMeasure {true} = 0 := by
  simp

end CslibFrontierTests.Crypto.VOLEBatchMulCheck
