/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/
module
-- upstream: candidate
public import CslibFrontier.Foundations.Data.BitString.Basic
public import CslibFrontier.Probability.Uniform
import CslibFrontier.Probability.PMF.Uniform
/-!
# Uniform random-function evaluations and shifted collisions on bit strings

Two elementary sampling facts about `BitString n` with its coordinatewise XOR group structure.
Evaluating a uniform random function `BitString n → BitString n` at a fixed injective family of
points gives independent uniform values, also after XOR with any fixed vector. A uniform block
shifted by a fixed offset lands in a fixed finite set `S` with probability exactly
`S.card / 2 ^ n`, and in a fixed list `ks` with probability at most `ks.length / 2 ^ n`.

These are the per-step ingredients of lazy-sampling arguments for block-cipher modes and
message authentication codes.

## Main results

* `Cslib.BitString.map_evalPoints_uniformOfFintype`,
  `Cslib.BitString.map_xorEvalPoints_uniformOfFintype`: a uniform random function evaluated at an
  injective point family, optionally masked by a fixed vector, is uniform.
* `Cslib.BitString.toOuterMeasure_addRight_mem_finset_eq`,
  `Cslib.BitString.toOuterMeasure_addRight_mem_list_le`: exact finite-set and list-cache collision
  probabilities for a shifted uniform block.
-/
public section
namespace Cslib.BitString
open Probability
open scoped ENNReal
variable {n : ℕ}
/-- **Fixed-schedule distinct-point evaluation uniformity**: for any fixed (non-adaptive) injective
  point family `pts : ι → BitString n`, evaluating a uniform random function
  `g ← PMF.uniformOfFintype (BitString n → BitString n)` at `pts` produces a uniform random vector
  in `ι → BitString n`. -/
theorem map_evalPoints_uniformOfFintype {ι : Type*} [Fintype ι] [DecidableEq ι]
    {pts : ι → BitString n} (hpts : Function.Injective pts) :
    (PMF.uniformOfFintype (BitString n → BitString n)).map (fun g i => g (pts i)) =
      PMF.uniformOfFintype (ι → BitString n) := by
  classical
  let φ : (BitString n → BitString n) →+ (ι → BitString n) :=
    { toFun := fun g i => g (pts i)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  apply PMF.uniformOfFintype_map_addHom φ
  intro y
  refine ⟨fun x => if h : ∃ i, pts i = x then y (Classical.choose h) else 0, ?_⟩
  funext i
  have hex : ∃ j, pts j = pts i := ⟨i, rfl⟩
  simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hex, ↓reduceDIte]
  rw [hpts (Classical.choose_spec hex)]
/-- **Distinct-point masked uniformity**: when the evaluation points `pts : ι → BitString n` are
  pairwise distinct, XORing `g (pts i)` with any fixed vector `m : ι → BitString n` under a uniform
  random function `g` produces the uniform distribution on `ι → BitString n`, independent of `m`. -/
theorem map_xorEvalPoints_uniformOfFintype {ι : Type*} [Fintype ι] [DecidableEq ι]
    {pts : ι → BitString n} (hpts : Function.Injective pts) (m : ι → BitString n) :
    (PMF.uniformOfFintype (BitString n → BitString n)).map (fun g i => g (pts i) + m i) =
      PMF.uniformOfFintype (ι → BitString n) := by
  rw [show (fun g : BitString n → BitString n => fun i => g (pts i) + m i) =
      (Equiv.addRight m) ∘ (fun g i => g (pts i)) from rfl,
    ← PMF.map_comp, map_evalPoints_uniformOfFintype hpts, PMF.uniformOfFintype_map_equiv]
/-- **Single-step shifted-block collision probability**: for any finite set
  `S : Finset (BitString n)` and offset `b : BitString n`, a uniform block
  `u ← PMF.uniformOfFintype (BitString n)` satisfies `u + b ∈ S` with exact outer measure
  `S.card * (2 ^ n : ℝ≥0∞)⁻¹`. -/
theorem toOuterMeasure_addRight_mem_finset_eq (S : Finset (BitString n)) (b : BitString n) :
    (PMF.uniformOfFintype (BitString n)).toOuterMeasure {u | u + b ∈ S} =
      (S.card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  classical
  have hmap :
      (PMF.uniformOfFintype (BitString n)).toOuterMeasure {u | u + b ∈ S} =
        ((PMF.uniformOfFintype (BitString n)).map (Equiv.addRight b)).toOuterMeasure (S : Set _) :=
    (PMF.toOuterMeasure_map_apply (Equiv.addRight b) (PMF.uniformOfFintype (BitString n))
      (S : Set (BitString n))).symm
  rw [hmap, PMF.uniformOfFintype_map_equiv, PMF.toOuterMeasure_uniformOfFintype]
  simp
/-- List-cache version of `toOuterMeasure_addRight_mem_finset_eq`: for any list
  `ks : List (BitString n)` and offset `b : BitString n`, a uniform block `u` satisfies
  `u + b ∈ ks` with outer measure at most `ks.length * (2 ^ n : ℝ≥0∞)⁻¹`. -/
theorem toOuterMeasure_addRight_mem_list_le (ks : List (BitString n)) (b : BitString n) :
    (PMF.uniformOfFintype (BitString n)).toOuterMeasure {u | u + b ∈ ks} ≤
      (ks.length : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  classical
  have hsub : {u : BitString n | u + b ∈ ks} ⊆ {u | u + b ∈ ks.toFinset} := by
    intro u hu
    simpa using hu
  calc (PMF.uniformOfFintype (BitString n)).toOuterMeasure {u | u + b ∈ ks}
      ≤ (PMF.uniformOfFintype (BitString n)).toOuterMeasure {u | u + b ∈ ks.toFinset} :=
        MeasureTheory.measure_mono hsub
    _ = (ks.toFinset.card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹ :=
        toOuterMeasure_addRight_mem_finset_eq ks.toFinset b
    _ ≤ (ks.length : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹ := by
        gcongr
        exact_mod_cast List.toFinset_card_le ks
end Cslib.BitString
