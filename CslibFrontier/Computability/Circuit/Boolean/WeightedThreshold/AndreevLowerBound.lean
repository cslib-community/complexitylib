/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.Andreev
public import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.ThresholdCounting
public import CslibFrontier.Foundations.Combinatorics.Hoeffding
public import CslibFrontier.Foundations.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Field.GeomSum
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds

/-!
# Depth-two threshold gate and wire lower bounds for Andreev's function

For `m > 0`, a depth-two arbitrary-real-weight circuit on `n = 2 ^ b + b * m` bits has
agreement at most the fixed-weight counting/Hoeffding bound proved below. Under each block
restriction the bottom weight vectors are fixed; only their thresholds depend on the assigned
inputs. Counting these shifts saves one logarithmic factor compared with counting arbitrary LTFs.
A simultaneous bound at all survivor counts and Cauchy–Schwarz averaging give quadratic dependence
on the agreement advantage `ε`.

For `m ≤ 2 ^ b` and `3 (b + 2) / √(2 ^ b) ≤ ε ≤ 1`, the explicit inequalities are
`m · 2^b · ε² ≤ 144 (b + 2) · c.size · √n` and
`m · √m · 2^b · ε² ≤ 144 (b + 2) · c.wireCount`. In the balanced regime these express
`Ω(ε² n^(3/2) / log² n)` gates and `Ω(ε² n^(5/2) / log^(5/2) n)` active wires.
The exact case follows at `ε = 1/2`.

These are original improvements. The restriction estimates are the repaired Kane–Williams
lemmas ([KaneWilliams2016], `arXiv:1511.07860v1`, Lemmas 1.1 and 3.1); the stronger counting and
averaging arguments are not claims attributed to that paper. All endpoints below are explicit
finite inequalities, rather than formal asymptotic-limit statements.
-/
@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold
open BitString Finset Cslib.Combinatorics.LittlewoodOfford

/-! ### Live block variables and subcube evaluation of Andreev's function -/

/-- `andreevBlockVar b m` is jointly injective across blocks `j : Fin b` and slots `t : Fin m`. -/
theorem andreevBlockVar_joint_injective (b m : ℕ) (j₁ : Fin b) (t₁ : Fin m)
    (j₂ : Fin b) (t₂ : Fin m) (h : andreevBlockVar b m j₁ t₁ = andreevBlockVar b m j₂ t₂) :
    j₁ = j₂ ∧ t₁ = t₂ :=
  Prod.ext_iff.mp (finProdFinEquiv.injective (Fin.natAdd_injective (b * m) (2 ^ b) h))

/-- The live coordinate `andreevBlockVar b m j (σ j)` in block `j` chosen by `σ : Fin b → Fin m`. -/
def andreevLiveVar (b m : ℕ) (σ : Fin b → Fin m) (j : Fin b) : Fin (2 ^ b + b * m) :=
  andreevBlockVar b m j (σ j)

/-- For any block selection `σ : Fin b → Fin m`, `andreevLiveVar b m σ` is injective. -/
theorem andreevLiveVar_injective (b m : ℕ) (σ : Fin b → Fin m) :
    Function.Injective (andreevLiveVar b m σ) :=
  fun j₁ j₂ h => (andreevBlockVar_joint_injective b m j₁ (σ j₁) j₂ (σ j₂) h).1

/-- The image of `andreevLiveVar b m σ` is `blockLiveSet (andreevBlockVar b m) σ`. -/
theorem univ_image_andreevLiveVar_eq_blockLiveSet (b m : ℕ) (σ : Fin b → Fin m) :
    univ.image (andreevLiveVar b m σ) = blockLiveSet (andreevBlockVar b m) σ := rfl

/-- Every truth-table coordinate is distinct from every block coordinate. -/
theorem andreevTableIndex_ne_andreevBlockVar (b m : ℕ) (idx : Fin (2 ^ b))
    (j : Fin b) (t : Fin m) : andreevTableIndex b m idx ≠ andreevBlockVar b m j t := fun h => by
  have hval := congrArg Fin.val h
  simp only [andreevTableIndex, andreevBlockVar, Fin.val_castAdd, Fin.val_natAdd] at hval; omega

/-- No truth-table coordinate belongs to `univ.image (andreevLiveVar b m σ)`. -/
theorem andreevTableIndex_notMem_image_andreevLiveVar (b m : ℕ) (σ : Fin b → Fin m)
    (idx : Fin (2 ^ b)) : andreevTableIndex b m idx ∉ univ.image (andreevLiveVar b m σ) := by
  simp only [mem_image, mem_univ, true_and, not_exists]
  exact fun j hj => andreevTableIndex_ne_andreevBlockVar b m idx j (σ j) hj.symm

/-- The `b`-bit vector of residual block parities of `w` outside the live slots `σ j`. -/
def andreevResidualParities (b m : ℕ) (σ : Fin b → Fin m)
    (w : BitString (2 ^ b + b * m)) : BitString b :=
  fun j => parityOn (univ.erase (σ j)) fun t => w (andreevBlockVar b m j t)

/-- Updating `andreevLiveVar b m σ` of `w` with `u` shifts the block parities by `u`. -/
theorem andreevParities_embedUpdate_andreevLiveVar (b m : ℕ) (σ : Fin b → Fin m)
    (w : BitString (2 ^ b + b * m)) (u : BitString b) :
    andreevParities b m (embedUpdate (andreevLiveVar b m σ) w u) =
      u + andreevResidualParities b m σ w := by
  funext j
  change parityOn univ (fun t => embedUpdate (andreevLiveVar b m σ) w u (andreevBlockVar b m j t)) =
    (u j ^^ andreevResidualParities b m σ w j)
  rw [parityOn_eq_xor_erase (mem_univ (σ j))]
  congr 1
  · exact embedUpdate_emb (andreevLiveVar_injective b m σ) w u j
  · refine parityOn_congr fun t ht => embedUpdate_of_notMem w u ?_
    simp only [mem_image, mem_univ, true_and, not_exists]; intro j' hj'
    obtain ⟨rfl, h2⟩ := andreevBlockVar_joint_injective b m j' (σ j') j t hj'
    exact (mem_erase.mp ht).1 h2.symm

/-- Along `u ↦ embedUpdate (andreevLiveVar b m σ) w u`, `andreev b m` reads the shifted table. -/
theorem andreev_embedUpdate_andreevLiveVar (b m : ℕ) (σ : Fin b → Fin m)
    (w : BitString (2 ^ b + b * m)) (u : BitString b) :
    andreev b m (embedUpdate (andreevLiveVar b m σ) w u) =
      andreevTable b m w (u + andreevResidualParities b m σ w) := by
  rw [andreev_eq_table_parities, andreevParities_embedUpdate_andreevLiveVar]
  exact embedUpdate_of_notMem w u (andreevTableIndex_notMem_image_andreevLiveVar b m σ _)

/-! ### Measure-preserving truth-table involutions and Hoeffding tail bound -/

/-- The `2 ^ b` truth-table coordinates in `Fin (2 ^ b + b * m)`. -/
def andreevTableCoords (b m : ℕ) : Finset (Fin (2 ^ b + b * m)) :=
  univ.image (andreevTableIndex b m)

/-- `andreevTableCoords b m` has cardinality `2 ^ b`. -/
@[simp] theorem card_andreevTableCoords (b m : ℕ) : #(andreevTableCoords b m) = 2 ^ b := by
  rw [andreevTableCoords, card_image_of_injective _ (andreevTableIndex_injective b m), card_univ,
    Fintype.card_fin]

/-- Involution translating the truth-table coordinates by `andreevResidualParities b m σ w`. -/
def andreevShiftResidual (b m : ℕ) (σ : Fin b → Fin m)
    (w : BitString (2 ^ b + b * m)) : BitString (2 ^ b + b * m) :=
  andreevTranslateTableFun b m (andreevResidualParities b m σ w) false w

@[simp] theorem andreevResidualParities_andreevShiftResidual (b m : ℕ) (σ : Fin b → Fin m)
    (w : BitString (2 ^ b + b * m)) :
    andreevResidualParities b m σ (andreevShiftResidual b m σ w) =
      andreevResidualParities b m σ w := by
  funext j; simp [andreevResidualParities, andreevShiftResidual, andreevBlockVar]

/-- `andreevShiftResidual b m σ` is an involution. -/
theorem andreevShiftResidual_involutive (b m : ℕ) (σ : Fin b → Fin m) :
    Function.Involutive (andreevShiftResidual b m σ) := fun w => by
  funext i; refine Fin.addCases (fun idx => ?_) (fun v => by simp [andreevShiftResidual]) i
  exact show andreevShiftResidual b m σ (andreevShiftResidual b m σ w) (andreevTableIndex b m idx) =
    w (andreevTableIndex b m idx) by
      have h := andreevResidualParities_andreevShiftResidual b m σ w
      rw [andreevShiftResidual] at h
      simp [andreevShiftResidual, andreevTableIndex, h, add_assoc]

/-- Involution XNORing each table coordinate `idx` with `h ((BitString.equivFin b).symm idx)`. -/
def andreevAlignTable (b m : ℕ) (h : BitString b → Bool)
    (w : BitString (2 ^ b + b * m)) : BitString (2 ^ b + b * m) :=
  Fin.addCases (fun idx => !(w (andreevTableIndex b m idx) ^^ h ((BitString.equivFin b).symm idx)))
    (fun v => w (Fin.natAdd (2 ^ b) v))

/-- `andreevAlignTable b m h` is an involution. -/
theorem andreevAlignTable_involutive (b m : ℕ) (h : BitString b → Bool) :
    Function.Involutive (andreevAlignTable b m h) := fun w => by
  funext i; refine Fin.addCases (fun idx => ?_) (fun v => by simp [andreevAlignTable]) i
  change andreevAlignTable b m h (andreevAlignTable b m h w) (andreevTableIndex b m idx) = _
  simp only [andreevAlignTable, andreevTableIndex, Fin.addCases_left]
  cases w (Fin.castAdd (b * m) idx) <;> cases h ((BitString.equivFin b).symm idx) <;> rfl

/-- Composite permutation on `BitString (2 ^ b + b * m)`. -/
def andreevSubcubePerm (b m : ℕ) (σ : Fin b → Fin m) (h : BitString b → Bool) :
    Equiv.Perm (BitString (2 ^ b + b * m)) :=
  (andreevShiftResidual_involutive b m σ).toPerm.trans (andreevAlignTable_involutive b m h).toPerm

/-- Subcube agreement with `h` equals the number of `true` table coordinates under
`andreevSubcubePerm b m σ h`. -/
theorem card_subcube_agree_andreev_eq_card_tableCoords_true (b m : ℕ) (σ : Fin b → Fin m)
    (h : BitString b → Bool) (w : BitString (2 ^ b + b * m)) :
    #{u : BitString b | h u = andreev b m (embedUpdate (andreevLiveVar b m σ) w u)} =
      #{i ∈ andreevTableCoords b m | andreevSubcubePerm b m σ h w i = true} := by
  rw [andreevTableCoords, filter_image, card_image_of_injective _ (andreevTableIndex_injective b m),
    ← Fintype.card_subtype, ← Fintype.card_subtype]
  refine Fintype.card_congr ((BitString.equivFin b).subtypeEquiv fun u => ?_)
  simp only [andreevSubcubePerm, Equiv.trans_apply, Function.Involutive.coe_toPerm,
    andreevAlignTable, andreevShiftResidual, andreevTranslateTableFun_castAdd, Bool.xor_false,
    andreevTableIndex, Fin.addCases_left, Equiv.symm_apply_apply,
    andreev_embedUpdate_andreevLiveVar, andreevTable]
  cases h u <;>
    cases w (Fin.castAdd (b * m) (BitString.equivFin b (u + andreevResidualParities b m σ w))) <;>
      decide

/-- **Subcube Hoeffding Tail Bound** for a fixed function `h : BitString b → Bool`. -/
theorem card_subcube_agree_andreev_le (b m : ℕ) (σ : Fin b → Fin m) (h : BitString b → Bool)
    {t : ℝ} (ht : 0 ≤ t) :
    (#{w : BitString (2 ^ b + b * m) |
      t ≤ (#{u : BitString b | h u = andreev b m (embedUpdate (andreevLiveVar b m σ) w u)} : ℝ) -
        (2 : ℝ) ^ b / 2} : ℝ) ≤
      (2 : ℝ) ^ (2 ^ b + b * m) * Real.exp (-(2 * t ^ 2 / (2 : ℝ) ^ b)) := by
  refine (le_of_eq ?_).trans (by simpa [Fintype.card_fin] using
    Cslib.BitString.card_filter_le_card_filter_sub_half_le (andreevTableCoords b m) true ht)
  simp_rw [card_subcube_agree_andreev_eq_card_tableCoords_true, ← Fintype.card_subtype]
  exact congrArg Nat.cast (Fintype.card_congr
    ((andreevSubcubePerm b m σ h).subtypeEquiv fun _ => Iff.rfl))

/-- **Union Bound over a Finite Family of Subcube Functions**. -/
theorem card_exists_mem_agree_andreev_le (b m : ℕ) (σ : Fin b → Fin m)
    (H : Finset (BitString b → Bool)) {t : ℝ} (ht : 0 ≤ t) :
    (#{w : BitString (2 ^ b + b * m) | ∃ h ∈ H,
      t ≤ (#{u : BitString b | h u = andreev b m (embedUpdate (andreevLiveVar b m σ) w u)} : ℝ) -
        (2 : ℝ) ^ b / 2} : ℝ) ≤
      (2 : ℝ) ^ (2 ^ b + b * m) * (#H : ℝ) * Real.exp (-(2 * t ^ 2 / (2 : ℝ) ^ b)) := by
  classical
  refine ((Nat.cast_le (α := ℝ)).mpr ((card_le_card (t := H.biUnion fun h => univ.filter fun w =>
      t ≤ (#{u : BitString b | h u = andreev b m (embedUpdate (andreevLiveVar b m σ) w u)} : ℝ) -
        (2 : ℝ) ^ b / 2) fun w hw => by
    simp only [mem_filter, mem_univ, true_and, mem_biUnion] at hw ⊢; exact hw).trans
    card_biUnion_le)).trans ?_
  rw [Nat.cast_sum]
  refine (sum_le_sum fun h _ => card_subcube_agree_andreev_le b m σ h ht).trans_eq ?_
  rw [sum_const, nsmul_eq_mul]; ring

/-! ### Simultaneous union bound over all surviving gate counts `q < 2 ^ b` -/

/-- Bound `((2 ^ b + 1) * M) ^ q * (2 ^ b + 1) ^ (q + b + 1)` on the number of subcube functions in
`IsDepthTwoOverWeights W q` whenever `min (#W + 1) ((2 ^ b + 1) ^ b) ≤ M`
(`card_isDepthTwoOverWeights_le`). -/
def andreevWeightCount (b M q : ℕ) : ℕ := ((2 ^ b + 1) * M) ^ q * (2 ^ b + 1) ^ (q + b + 1)

/-- Simultaneous union-bound tail over all surviving gate counts `q < 2 ^ b` at deviation
`t_q = α * √q + β`, for subcube functions with `q` bottom gates over at most `M - 1` fixed
weight vectors. -/
noncomputable def andreevWeightTail (b M : ℕ) (α β : ℝ) : ℝ :=
  ∑ q ∈ range (2 ^ b), (andreevWeightCount b M q : ℝ) *
    Real.exp (-(2 * (α * Real.sqrt q + β) ^ 2 / (2 : ℝ) ^ b))

theorem andreevWeightTail_nonneg (b M : ℕ) (α β : ℝ) : 0 ≤ andreevWeightTail b M α β :=
  sum_nonneg fun _ _ => by positivity

/-- **Simultaneous Union Bound over all `q < 2 ^ b`** for subcube functions with bottom weight
vectors drawn from `W`. -/
theorem card_exists_lt_two_pow_isDepthTwoOverWeights_agree_andreev_le (b m : ℕ)
    (σ : Fin b → Fin m) (W : Finset (Fin b → ℝ)) {M : ℕ}
    (hM : min (#W + 1) ((2 ^ b + 1) ^ b) ≤ M) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    (#{w : BitString (2 ^ b + b * m) | ∃ q < 2 ^ b, ∃ h : BitString b → Bool,
      IsDepthTwoOverWeights W q h ∧ α * Real.sqrt q + β ≤
        (#{u : BitString b | h u = andreev b m (embedUpdate (andreevLiveVar b m σ) w u)} : ℝ) -
          (2 : ℝ) ^ b / 2} : ℝ) ≤
      (2 : ℝ) ^ (2 ^ b + b * m) * andreevWeightTail b M α β := by
  classical
  refine ((Nat.cast_le (α := ℝ)).mpr ((card_le_card (t := (range (2 ^ b)).biUnion fun q =>
      univ.filter fun w => ∃ h : BitString b → Bool, IsDepthTwoOverWeights W q h ∧
        α * Real.sqrt q + β ≤
          (#{u : BitString b | h u = andreev b m (embedUpdate (andreevLiveVar b m σ) w u)} : ℝ) -
            (2 : ℝ) ^ b / 2) fun w hw => by
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_range] at hw ⊢; exact hw).trans
    card_biUnion_le)).trans ?_
  rw [Nat.cast_sum]; unfold andreevWeightTail; rw [mul_sum]
  refine sum_le_sum fun q _ => ?_
  have hfamily := card_exists_mem_agree_andreev_le b m σ
    (univ.filter (IsDepthTwoOverWeights W q))
    (add_nonneg (mul_nonneg hα (Real.sqrt_nonneg (q : ℝ))) hβ)
  have hfamily' : (#{w : BitString (2 ^ b + b * m) | ∃ h : BitString b → Bool,
      IsDepthTwoOverWeights W q h ∧ α * Real.sqrt q + β ≤
        (#{u : BitString b | h u = andreev b m (embedUpdate (andreevLiveVar b m σ) w u)} : ℝ) -
          (2 : ℝ) ^ b / 2} : ℝ) ≤ (2 : ℝ) ^ (2 ^ b + b * m) *
      (#(univ.filter (IsDepthTwoOverWeights W q)) : ℝ) *
        Real.exp (-(2 * (α * Real.sqrt q + β) ^ 2 / (2 : ℝ) ^ b)) := by
    simpa only [mem_filter, mem_univ, true_and] using hfamily
  refine hfamily'.trans ?_
  have hH : (#(univ.filter (IsDepthTwoOverWeights W q)) : ℝ) ≤
      (andreevWeightCount b M q : ℝ) := by
    have hcount := card_isDepthTwoOverWeights_le (κ := Fin b) W q
    rw [Fintype.card_fin] at hcount
    have hle : ((2 ^ b + 1) * min (#W + 1) ((2 ^ b + 1) ^ b)) ^ q *
        (2 ^ b + 1) ^ (q + b + 1) ≤ andreevWeightCount b M q := by
      unfold andreevWeightCount
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hM) q)
    exact (Nat.cast_le (α := ℝ)).mpr (hcount.trans hle)
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hH (by positivity)) (by positivity)

/-! ### Simultaneous subcube averaging via Cauchy–Schwarz -/

/-- Simultaneous-in-`q` correlation bound for `f` against `andreev b m`, given for every block
selection `σ` a finite set `W σ` of bottom weight vectors and an unforced-gate count `U σ w` with
average at most `B ≥ 0`. -/
theorem card_eval_eq_andreev_le_of_unforced_mean_le {b m : ℕ} (hm : 0 < m)
    {α β B : ℝ} (hα : Real.sqrt ((2 : ℝ) ^ b) / 2 ≤ α) (hβ : 0 ≤ β) (hB0 : 0 ≤ B)
    (f : BitString (2 ^ b + b * m) → Bool) (W : (Fin b → Fin m) → Finset (Fin b → ℝ)) {M : ℕ}
    (hM : ∀ σ, min (#(W σ) + 1) ((2 ^ b + 1) ^ b) ≤ M)
    (U : (Fin b → Fin m) → BitString (2 ^ b + b * m) → ℕ)
    (hU : ∀ (σ : Fin b → Fin m) (w : BitString (2 ^ b + b * m)),
      IsDepthTwoOverWeights (W σ) (U σ w) (fun u => f (embedUpdate (andreevLiveVar b m σ) w u)))
    (hmean : (∑ σ : Fin b → Fin m, ∑ w : BitString (2 ^ b + b * m), (U σ w : ℝ)) ≤
      (Fintype.card (Fin b → Fin m) : ℝ) * (2 : ℝ) ^ (2 ^ b + b * m) * B) :
    (#{w : BitString (2 ^ b + b * m) | f w = andreev b m w} : ℝ) ≤ (2 : ℝ) ^ (2 ^ b + b * m) *
      (1 / 2 + (α * Real.sqrt B + β) / (2 : ℝ) ^ b + andreevWeightTail b M α β) := by
  classical
  have hα0 : 0 ≤ α := (by positivity : (0 : ℝ) ≤ Real.sqrt ((2 : ℝ) ^ b) / 2).trans hα
  have h2b_pos : (0 : ℝ) < (2 : ℝ) ^ b := by positivity
  set T := andreevWeightTail b M α β with hT
  set N : ℝ := (2 : ℝ) ^ (2 ^ b + b * m) with hN
  set A : ℝ := (#{w : BitString (2 ^ b + b * m) | f w = andreev b m w} : ℝ) with hA
  have hcardW : (Fintype.card (BitString (2 ^ b + b * m)) : ℝ) = N := by
    rw [hN, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]; push_cast; rfl
  let agree (σ : Fin b → Fin m) (w : BitString (2 ^ b + b * m)) : ℝ :=
    (#{u : BitString b | f (embedUpdate (andreevLiveVar b m σ) w u) =
      andreev b m (embedUpdate (andreevLiveVar b m σ) w u)} : ℝ)
  have hσ_step (σ : Fin b → Fin m) : (2 : ℝ) ^ b * A ≤ N * ((2 : ℝ) ^ b / 2 + β) +
      α * (∑ w : BitString (2 ^ b + b * m), Real.sqrt (U σ w : ℝ)) + N * T * (2 : ℝ) ^ b := by
    let Bad : Finset (BitString (2 ^ b + b * m)) :=
      univ.filter fun w => ∃ q < 2 ^ b, ∃ h : BitString b → Bool,
        IsDepthTwoOverWeights (W σ) q h ∧ α * Real.sqrt q + β ≤
          (#{u : BitString b | h u = andreev b m (embedUpdate (andreevLiveVar b m σ) w u)} : ℝ) -
            (2 : ℝ) ^ b / 2
    have hpt (w : BitString (2 ^ b + b * m)) : agree σ w ≤ ((2 : ℝ) ^ b / 2 + β) +
        α * Real.sqrt (U σ w : ℝ) + if w ∈ Bad then (2 : ℝ) ^ b else 0 := by
      have hle_2b : agree σ w ≤ (2 : ℝ) ^ b := by
        dsimp [agree]; exact_mod_cast (card_le_univ _).trans_eq (by simp)
      have hrest : 0 ≤ α * Real.sqrt (U σ w : ℝ) := mul_nonneg hα0 (Real.sqrt_nonneg _)
      by_cases hbad : w ∈ Bad
      · simp only [hbad, ↓reduceIte]; linarith
      · simp only [hbad, ↓reduceIte, add_zero]
        by_cases hlt : U σ w < 2 ^ b
        · have hng : ¬ (α * Real.sqrt (U σ w : ℝ) + β ≤ agree σ w - (2 : ℝ) ^ b / 2) := fun hge =>
            hbad (mem_filter.mpr ⟨mem_univ w, U σ w, hlt, _, hU σ w, hge⟩)
          linarith [lt_of_not_ge hng]
        · have h2b_le : (2 : ℝ) ^ b ≤ (U σ w : ℝ) := by exact_mod_cast not_lt.mp hlt
          have hhalf : (2 : ℝ) ^ b / 2 ≤ α * Real.sqrt (U σ w : ℝ) := by
            rw [show (2 : ℝ) ^ b / 2 = (Real.sqrt ((2 : ℝ) ^ b) / 2) * Real.sqrt ((2 : ℝ) ^ b) by
              rw [div_mul_eq_mul_div, Real.mul_self_sqrt h2b_pos.le]]
            exact mul_le_mul hα (Real.sqrt_le_sqrt h2b_le) (by positivity) hα0
          linarith
    have hsum_eq : (∑ w, agree σ w) = (2 : ℝ) ^ b * A := by
      have hnat := sum_card_filter_embedUpdate (andreevLiveVar_injective b m σ)
        (fun w' => f w' = andreev b m w')
      rw [Fintype.card_fin] at hnat; dsimp [agree]; rw [hA]; exact_mod_cast hnat
    have hBad_le : (#Bad : ℝ) ≤ N * T :=
      card_exists_lt_two_pow_isDepthTwoOverWeights_agree_andreev_le b m σ (W σ) (hM σ) hα0 hβ
    have hsum_le := sum_le_sum fun w (_ : w ∈ univ) => hpt w
    rw [hsum_eq, sum_add_distrib, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, hcardW,
      ← mul_sum, sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul] at hsum_le
    nlinarith [mul_le_mul_of_nonneg_right hBad_le h2b_pos.le]
  set C : ℝ := (Fintype.card (Fin b → Fin m) : ℝ) with hC
  have hC_pos : 0 < C := by
    rw [hC, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]; positivity
  have hsum_σ := sum_le_sum fun σ (_ : σ ∈ univ) => hσ_step σ
  rw [sum_const, card_univ, nsmul_eq_mul, sum_add_distrib, sum_add_distrib, sum_const, sum_const,
    card_univ, nsmul_eq_mul, nsmul_eq_mul, ← mul_sum, ← hC] at hsum_σ
  have hcs : (∑ σ : Fin b → Fin m, ∑ w : BitString (2 ^ b + b * m), Real.sqrt (U σ w : ℝ)) ≤
      C * N * Real.sqrt B := by
    have hcard : (#(univ : Finset ((Fin b → Fin m) × BitString (2 ^ b + b * m))) : ℝ) = C * N := by
      rw [card_univ, Fintype.card_prod, Nat.cast_mul, hcardW]
    have h := sum_sqrt_le_card_mul_sqrt
      (univ : Finset ((Fin b → Fin m) × BitString (2 ^ b + b * m)))
      (F := fun p => (U p.1 p.2 : ℝ)) (fun _ _ => by positivity) hB0
      (by rw [hcard, Fintype.sum_prod_type]; exact hmean)
    rwa [hcard, Fintype.sum_prod_type] at h
  have hfinal : C * ((2 : ℝ) ^ b * A) ≤
      C * ((2 : ℝ) ^ b * (N * (1 / 2 + (α * Real.sqrt B + β) / (2 : ℝ) ^ b + T))) := by
    have hexp : C * ((2 : ℝ) ^ b * (N * (1 / 2 + (α * Real.sqrt B + β) / (2 : ℝ) ^ b + T))) =
        C * (N * ((2 : ℝ) ^ b / 2 + β)) + α * (C * N * Real.sqrt B) + C * (N * T * (2 : ℝ) ^ b)
          := by
      field_simp; ring
    rw [hexp]; nlinarith [mul_le_mul_of_nonneg_left hcs hα0]
  exact le_of_mul_le_mul_left (le_of_mul_le_mul_left hfinal hC_pos) h2b_pos

/-- Squaring step: a correlation bound with excess `2 ^ b * (ε - T) - β ≥ 0` over the deviation
offset gives `(2 ^ b * (ε - T) - β) ^ 2 ≤ α ^ 2 * B`. -/
theorem sq_le_of_corr_le {b n : ℕ} {α β ε T B : ℝ} (hB0 : 0 ≤ B)
    (hpos : 0 ≤ (2 : ℝ) ^ b * (ε - T) - β)
    (hbound : (2 : ℝ) ^ n * (1 / 2 + ε) ≤
      (2 : ℝ) ^ n * (1 / 2 + (α * Real.sqrt B + β) / (2 : ℝ) ^ b + T)) :
    ((2 : ℝ) ^ b * (ε - T) - β) ^ 2 ≤ α ^ 2 * B := by
  have h1 := le_of_mul_le_mul_left hbound (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)
  have h2b_pos : (0 : ℝ) < (2 : ℝ) ^ b := by positivity
  have h2 : (2 : ℝ) ^ b * (ε - T) - β ≤ α * Real.sqrt B := by
    have hmul : (2 : ℝ) ^ b * ((α * Real.sqrt B + β) / (2 : ℝ) ^ b) = α * Real.sqrt B + β := by
      field_simp
    nlinarith [mul_le_mul_of_nonneg_left
      (by linarith : ε - T ≤ (α * Real.sqrt B + β) / (2 : ℝ) ^ b) h2b_pos.le]
  calc ((2 : ℝ) ^ b * (ε - T) - β) ^ 2 ≤ (α * Real.sqrt B) ^ 2 := pow_le_pow_left₀ hpos h2 2
    _ = α ^ 2 * B := by rw [mul_pow, Real.sq_sqrt hB0]

/-! ### Explicit deviation scales -/

/-- Canonical slope `α = √(2 ^ b * (b + 2 + log M))` of the deviation `t_q = α * √q + β`. -/
noncomputable def andreevWeightScale (b M : ℕ) : ℝ :=
  Real.sqrt ((2 : ℝ) ^ b * ((b : ℝ) + 2 + Real.log M))

theorem andreevWeightScale_sq (b : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    andreevWeightScale b M ^ 2 = (2 : ℝ) ^ b * ((b : ℝ) + 2 + Real.log M) :=
  Real.sq_sqrt (by have := Real.log_nonneg (by exact_mod_cast hM : (1 : ℝ) ≤ M); positivity)

theorem sqrt_two_pow_div_two_le_andreevWeightScale (b : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    Real.sqrt ((2 : ℝ) ^ b) / 2 ≤ andreevWeightScale b M := by
  have hlog := Real.log_nonneg (by exact_mod_cast hM : (1 : ℝ) ≤ M)
  rw [show Real.sqrt ((2 : ℝ) ^ b) / 2 = Real.sqrt ((2 : ℝ) ^ b / 4) by
    rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4),
      show Real.sqrt 4 = 2 from (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
        (by norm_num)]]
  exact Real.sqrt_le_sqrt (by nlinarith [(by positivity : (0 : ℝ) < (2 : ℝ) ^ b),
    (by positivity : (0 : ℝ) ≤ (b : ℝ))])

/-- At slope `α = andreevWeightScale b M` and offset `β = (b + 2) * √(2 ^ b)`, the simultaneous
tail is at most `(1 / 2) ^ (b + 6)`. -/
theorem andreevWeightTail_scale_le (b : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    andreevWeightTail b M (andreevWeightScale b M) (((b : ℝ) + 2) * Real.sqrt ((2 : ℝ) ^ b)) ≤
      (1 / 2 : ℝ) ^ (b + 6) := by
  set x : ℝ := (2 : ℝ) ^ b with hx
  have hx_pos : 0 < x := by positivity
  have hx1 : 1 ≤ x := one_le_pow₀ (by norm_num)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
  set A : ℝ := (b : ℝ) + 2 + Real.log M with hA
  set α := andreevWeightScale b M
  have hα_sq : α ^ 2 = x * A := andreevWeightScale_sq b hM
  have hα0 : 0 ≤ α := Real.sqrt_nonneg _
  set β := ((b : ℝ) + 2) * Real.sqrt x with hβ
  have hβ_sq : β ^ 2 = ((b : ℝ) + 2) ^ 2 * x := by rw [hβ, mul_pow, Real.sq_sqrt hx_pos.le]
  have hβ0 : 0 ≤ β := by positivity
  set K : ℝ := Real.exp (-(2 * ((b : ℝ) + 2) ^ 2)) with hK
  set r : ℝ := (x + 1) ^ 2 * M * Real.exp (-(2 * A)) with hr
  have hterm (q : ℕ) : (andreevWeightCount b M q : ℝ) *
      Real.exp (-(2 * (α * Real.sqrt q + β) ^ 2 / x)) ≤ (x + 1) ^ (b + 1) * K * r ^ q := by
    have hsq : α ^ 2 * q + β ^ 2 ≤ (α * Real.sqrt q + β) ^ 2 := by
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg q : (0 : ℝ) ≤ q),
        mul_nonneg (mul_nonneg hα0 (Real.sqrt_nonneg (q : ℝ))) hβ0]
    have hexp : Real.exp (-(2 * (α * Real.sqrt q + β) ^ 2 / x)) ≤
        Real.exp (-(2 * A)) ^ q * K := by
      rw [hK, ← Real.exp_nat_mul, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hval : 2 * (α ^ 2 * q + β ^ 2) / x = 2 * A * q + 2 * ((b : ℝ) + 2) ^ 2 := by
        rw [hα_sq, hβ_sq]; field_simp
      have hdiv : 2 * (α ^ 2 * q + β ^ 2) / x ≤ 2 * (α * Real.sqrt q + β) ^ 2 / x :=
        div_le_div_of_nonneg_right (by linarith) hx_pos.le
      nlinarith
    have hcount : (andreevWeightCount b M q : ℝ) = ((x + 1) ^ 2 * M) ^ q * (x + 1) ^ (b + 1) := by
      unfold andreevWeightCount
      push_cast
      rw [← hx]
      simp only [pow_add, mul_pow]
      rw [pow_two, mul_pow]
      ring
    rw [hcount]
    calc ((x + 1) ^ 2 * M) ^ q * (x + 1) ^ (b + 1) *
          Real.exp (-(2 * (α * Real.sqrt q + β) ^ 2 / x))
        ≤ ((x + 1) ^ 2 * M) ^ q * (x + 1) ^ (b + 1) * (Real.exp (-(2 * A)) ^ q * K) := by gcongr
      _ = (x + 1) ^ (b + 1) * K * r ^ q := by simp only [hr, mul_pow]; ring
  have hr0 : 0 ≤ r := by positivity
  have hr_le : r ≤ 1 / 4 := by
    have hexpA : Real.exp (-(2 * A)) * (M : ℝ) ^ 2 = Real.exp (-(2 * ((b : ℝ) + 2))) := by
      have hlog2 : Real.exp (2 * Real.log M) = (M : ℝ) ^ 2 := by
        rw [show (2 : ℝ) * Real.log M = ((2 : ℕ) : ℝ) * Real.log M by norm_num, Real.exp_nat_mul,
          Real.exp_log (by linarith)]
      rw [← hlog2, ← Real.exp_add, hA]; congr 1; ring
    have hx1' : x + 1 ≤ 2 * x := by linarith
    have he2 : (4 : ℝ) ^ (b + 2) ≤ Real.exp (2 * ((b : ℝ) + 2)) := by
      have h4 : (4 : ℝ) ≤ Real.exp 2 := by
        have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith
      calc (4 : ℝ) ^ (b + 2) ≤ Real.exp 2 ^ (b + 2) := pow_le_pow_left₀ (by norm_num) h4 _
        _ = Real.exp (2 * ((b : ℝ) + 2)) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hx4 : 4 * (x + 1) ^ 2 ≤ (4 : ℝ) ^ (b + 2) := by
      have : (4 : ℝ) ^ (b + 2) = 16 * x ^ 2 := by
        rw [hx, ← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring
      rw [this]; nlinarith
    have hE := Real.exp_pos (-(2 * A))
    have hrM : r * M = (x + 1) ^ 2 * Real.exp (-(2 * ((b : ℝ) + 2))) := by
      rw [hr, ← hexpA]; ring
    have hmain : 4 * ((x + 1) ^ 2 * Real.exp (-(2 * ((b : ℝ) + 2)))) ≤ 1 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, mul_div_assoc', div_le_one (Real.exp_pos _)]
      linarith
    nlinarith
  have hgeom : (∑ q ∈ range (2 ^ b), r ^ q) ≤ 4 / 3 := by
    rw [range_eq_Ico]
    refine (geom_sum_Ico_le_of_lt_one hr0 (by linarith)).trans ?_
    rw [pow_zero, div_le_iff₀ (by linarith)]; linarith
  have hT : andreevWeightTail b M α β ≤ (x + 1) ^ (b + 1) * K * (4 / 3) := by
    unfold andreevWeightTail
    refine (sum_le_sum fun q _ => hterm q).trans ?_
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left hgeom (by positivity)
  refine hT.trans ?_
  have hpow : (x + 1) ^ (b + 1) ≤ (2 : ℝ) ^ ((b + 1) * (b + 1)) := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) (by rw [pow_succ, ← hx]; linarith) _
  have hexpK : (2 : ℝ) ^ ((b + 1) * (b + 1) + 1 + (b + 6)) ≤ Real.exp (2 * ((b : ℝ) + 2) ^ 2) :=
    (pow_le_pow_right₀ (by norm_num) (by nlinarith)).trans
      ((Real.two_pow_le_exp (2 * (b + 2) ^ 2)).trans_eq (by push_cast; ring_nf))
  have hKpos : 0 < K := Real.exp_pos _
  have hK_eq : K * Real.exp (2 * ((b : ℝ) + 2) ^ 2) = 1 := by
    rw [hK, ← Real.exp_add]; simp
  rw [one_div, inv_pow]
  rw [← one_div]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (b + 6))).mpr
  have hp : (x + 1) ^ (b + 1) * (4 / 3 : ℝ) * (2 : ℝ) ^ (b + 6) ≤
      Real.exp (2 * ((b : ℝ) + 2) ^ 2) := by
    calc _ ≤ (2 : ℝ) ^ ((b + 1) * (b + 1)) * 2 * (2 : ℝ) ^ (b + 6) := by gcongr; norm_num
         _ = (2 : ℝ) ^ ((b + 1) * (b + 1) + 1 + (b + 6)) := by simp only [pow_add, pow_one]
         _ ≤ _ := hexpK
  nlinarith [mul_le_mul_of_nonneg_left hp hKpos.le]

/-- With `ε ≥ 3 (b + 2) / √(2 ^ b)`, the canonical offset and tail consume at most
`2 ε / 3`, leaving a nonnegative excess of at least `2 ^ b * ε / 3`. -/
theorem excess_ge_of_three_mul_div_sqrt_le {b M : ℕ} (hM : 1 ≤ M) {ε : ℝ}
    (hε : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ ε) :
    (2 : ℝ) ^ b * ε / 3 ≤ (2 : ℝ) ^ b * (ε -
      andreevWeightTail b M (andreevWeightScale b M)
        (((b : ℝ) + 2) * Real.sqrt ((2 : ℝ) ^ b))) -
      ((b : ℝ) + 2) * Real.sqrt ((2 : ℝ) ^ b) := by
  have hx : (0 : ℝ) < (2 : ℝ) ^ b := by positivity
  have hs : 0 < Real.sqrt ((2 : ℝ) ^ b) := by positivity
  have hsq := Real.sq_sqrt hx.le
  have hs_le : Real.sqrt ((2 : ℝ) ^ b) ≤ (2 : ℝ) ^ b := by
    have h1 : 1 ≤ Real.sqrt ((2 : ℝ) ^ b) := by
      simpa using Real.sqrt_le_sqrt (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := b))
    nlinarith
  have ht : andreevWeightTail b M (andreevWeightScale b M)
      (((b : ℝ) + 2) * Real.sqrt ((2 : ℝ) ^ b)) ≤
      ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) := by
    refine (andreevWeightTail_scale_le b hM).trans ?_
    have hp : (1 / 2 : ℝ) ^ (b + 6) ≤ (1 / 2 : ℝ) ^ b :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    simp only [one_div, inv_pow] at hp ⊢
    refine hp.trans ((inv_anti₀ hs hs_le).trans ?_)
    rw [← one_div]
    exact div_le_div_of_nonneg_right (by linarith [(by positivity : (0 : ℝ) ≤ (b : ℝ))]) hs.le
  have hε' := (div_le_iff₀ hs).mp hε
  have hβ : 3 * (((b : ℝ) + 2) * Real.sqrt ((2 : ℝ) ^ b)) ≤ (2 : ℝ) ^ b * ε := by
    nlinarith [mul_le_mul_of_nonneg_right hε' hs.le]
  have ht' : 3 * andreevWeightTail b M (andreevWeightScale b M)
      (((b : ℝ) + 2) * Real.sqrt ((2 : ℝ) ^ b)) ≤ ε := by
    linarith [show 3 * (((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b)) ≤ ε by simpa [mul_div_assoc]
      using hε]
  nlinarith [mul_le_mul_of_nonneg_left ht' hx.le]

/-! ### Depth-two gate and wire correlation and lower bounds -/

/-- Gate correlation bound counting only threshold shifts of the circuit's fixed bottom weights. -/
theorem card_eval_eq_andreev_le_of_depth_le_two_size {b m : ℕ} (hm : 0 < m)
    {α β : ℝ} (hα : Real.sqrt ((2 : ℝ) ^ b) / 2 ≤ α) (hβ : 0 ≤ β)
    (c : Circuit signature (2 ^ b + b * m) 1) (hd : c.depth ≤ 2) (o : Fin 1) :
    (#{w : BitString (2 ^ b + b * m) | c.eval interpretation w o = andreev b m w} : ℝ) ≤
      (2 : ℝ) ^ (2 ^ b + b * m) * (1 / 2 +
        (α * Real.sqrt (4 * (1 / (m : ℝ)) * (c.size : ℝ) * Real.sqrt ((2 ^ b + b * m : ℕ) : ℝ))
          + β) / (2 : ℝ) ^ b + andreevWeightTail b (c.size + 1) α β) := by
  classical
  refine card_eval_eq_andreev_le_of_unforced_mean_le hm hα hβ (by positivity)
    (fun w => c.eval interpretation w o)
    (fun σ => circuitLiveWeights c o (andreevLiveVar b m σ))
    (M := c.size + 1)
    (fun σ => (min_le_left _ _).trans (Nat.add_le_add_right
      (card_circuitLiveWeights_le_size c o _) 1))
    (fun σ w => circuitUnforcedConstCount c o (blockLiveSet (andreevBlockVar b m) σ) w)
    (fun σ w => by rw [← univ_image_andreevLiveVar_eq_blockLiveSet]; exact
      isDepthTwoOverWeights_eval_embedUpdate_const c hd o (andreevLiveVar_injective b m σ) w) ?_
  simpa [Fintype.card_fin] using sum_circuitUnforcedConstCount_blockLiveSet_le c o
    (andreevBlockVar b m) (andreevBlockVar_joint_injective b m)

/-- Explicit gate lower bound with separate slope and offset. -/
theorem size_ge_of_card_eval_eq_andreev_ge {b m : ℕ} (hm : 0 < m)
    {α β ε : ℝ} (hα : Real.sqrt ((2 : ℝ) ^ b) / 2 ≤ α) (hβ : 0 ≤ β)
    (c : Circuit signature (2 ^ b + b * m) 1) (hd : c.depth ≤ 2) (o : Fin 1)
    (hpos : 0 ≤ (2 : ℝ) ^ b * (ε - andreevWeightTail b (c.size + 1) α β) - β)
    (hcorr : (2 : ℝ) ^ (2 ^ b + b * m) * (1 / 2 + ε) ≤
      (#{w : BitString (2 ^ b + b * m) | c.eval interpretation w o = andreev b m w} : ℝ)) :
    ((2 : ℝ) ^ b * (ε - andreevWeightTail b (c.size + 1) α β) - β) ^ 2 ≤
      α ^ 2 * (4 * (1 / (m : ℝ)) * (c.size : ℝ) * Real.sqrt ((2 ^ b + b * m : ℕ) : ℝ)) :=
  sq_le_of_corr_le (by positivity) hpos (hcorr.trans
    (card_eval_eq_andreev_le_of_depth_le_two_size hm hα hβ c hd o))

/-- Canonical gate bound: the counting loss is `b + 2 + log (c.size + 1)`.
For polynomial resources this is linear in `b`, saving one logarithm over unrestricted LTF
  counting. -/
theorem size_ge_of_card_eval_eq_andreev_ge_of_le_eps {b m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ ε)
    (c : Circuit signature (2 ^ b + b * m) 1) (hd : c.depth ≤ 2) (o : Fin 1)
    (hcorr : (2 : ℝ) ^ (2 ^ b + b * m) * (1 / 2 + ε) ≤
      (#{w : BitString (2 ^ b + b * m) | c.eval interpretation w o = andreev b m w} : ℝ)) :
    (m : ℝ) * (2 : ℝ) ^ b * ε ^ 2 ≤
      36 * ((b : ℝ) + 2 + Real.log (c.size + 1)) * (c.size : ℝ) * Real.sqrt ((2 ^ b + b * m :
        ℕ) : ℝ) := by
  have hε0 : 0 ≤ ε := (by positivity : 0 ≤ 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b)).trans hε
  have hex := excess_ge_of_three_mul_div_sqrt_le (b := b) (M := c.size + 1) (by omega) hε
  have hp : 0 ≤ (2 : ℝ) ^ b * (ε - andreevWeightTail b (c.size + 1)
      (andreevWeightScale b (c.size + 1)) (((b : ℝ) + 2) * Real.sqrt ((2 : ℝ) ^ b))) -
      ((b : ℝ) + 2) * Real.sqrt ((2 : ℝ) ^ b) := (by positivity : 0 ≤ (2 : ℝ) ^ b * ε / 3).trans hex
  have h := (pow_le_pow_left₀ (by positivity) hex 2).trans
    (size_ge_of_card_eval_eq_andreev_ge hm
      (sqrt_two_pow_div_two_le_andreevWeightScale b (by omega)) (by positivity) c hd o hp hcorr)
  rw [andreevWeightScale_sq b (by omega)] at h
  simp only [Nat.cast_add, Nat.cast_one] at h ⊢
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hmne : (m : ℝ) ≠ 0 := hmpos.ne'
  have hmul := mul_le_mul_of_nonneg_left h hmpos.le
  have heq : (m : ℝ) * ((2 : ℝ) ^ b * ((b : ℝ) + 2 + Real.log (c.size + 1)) *
      (4 * (1 / (m : ℝ)) * (c.size : ℝ) * Real.sqrt ((2 ^ b + b * m : ℕ) : ℝ))) =
      (2 : ℝ) ^ b * (4 * ((b : ℝ) + 2 + Real.log (c.size + 1)) *
        (c.size : ℝ) * Real.sqrt ((2 ^ b + b * m : ℕ) : ℝ)) := by field_simp
  simp only [Nat.cast_add] at heq
  rw [heq] at hmul
  apply le_of_mul_le_mul_left (a := (2 : ℝ) ^ b) _ (by positivity)
  nlinarith

/-- Wire correlation bound counting only threshold shifts of the circuit's fixed bottom weights. -/
theorem card_eval_eq_andreev_le_of_depth_le_two_wireCount {b m : ℕ} (hm : 0 < m)
    {α β : ℝ} (hα : Real.sqrt ((2 : ℝ) ^ b) / 2 ≤ α) (hβ : 0 ≤ β)
    (c : Circuit signature (2 ^ b + b * m) 1) (hd : c.depth ≤ 2) (o : Fin 1) :
    (#{w : BitString (2 ^ b + b * m) | c.eval interpretation w o = andreev b m w} : ℝ) ≤
      (2 : ℝ) ^ (2 ^ b + b * m) * (1 / 2 +
        (α * Real.sqrt (4 * (c.wireCount : ℝ) * (1 / (m : ℝ)) * Real.sqrt (1 / (m : ℝ))) + β) /
          (2 : ℝ) ^ b + andreevWeightTail b (c.wireCount + 1) α β) := by
  classical
  refine card_eval_eq_andreev_le_of_unforced_mean_le hm hα hβ (by positivity)
    (fun w => c.eval interpretation w o)
    (fun σ => circuitLiveWeights c o (andreevLiveVar b m σ))
    (M := c.wireCount + 1)
    (fun σ => (min_le_left _ _).trans (Nat.add_le_add_right
      (card_circuitLiveWeights_le_wireCount c o _) 1))
    (fun σ w => circuitUnforcedAtMostOneCount c o (blockLiveSet (andreevBlockVar b m) σ) w)
    (fun σ w => by rw [← univ_image_andreevLiveVar_eq_blockLiveSet]; exact
      isDepthTwoOverWeights_eval_embedUpdate c hd o (andreevLiveVar_injective b m σ) w) ?_
  simpa [Fintype.card_fin] using sum_circuitUnforcedAtMostOneCount_blockLiveSet_le c o
    (andreevBlockVar b m) (andreevBlockVar_joint_injective b m)

/-- Explicit wire lower bound with separate slope and offset. -/
theorem wireCount_ge_of_card_eval_eq_andreev_ge {b m : ℕ} (hm : 0 < m)
    {α β ε : ℝ} (hα : Real.sqrt ((2 : ℝ) ^ b) / 2 ≤ α) (hβ : 0 ≤ β)
    (c : Circuit signature (2 ^ b + b * m) 1) (hd : c.depth ≤ 2) (o : Fin 1)
    (hpos : 0 ≤ (2 : ℝ) ^ b * (ε - andreevWeightTail b (c.wireCount + 1) α β) - β)
    (hcorr : (2 : ℝ) ^ (2 ^ b + b * m) * (1 / 2 + ε) ≤
      (#{w : BitString (2 ^ b + b * m) | c.eval interpretation w o = andreev b m w} : ℝ)) :
    ((2 : ℝ) ^ b * (ε - andreevWeightTail b (c.wireCount + 1) α β) - β) ^ 2 ≤
      α ^ 2 * (4 * (c.wireCount : ℝ) * (1 / (m : ℝ)) * Real.sqrt (1 / (m : ℝ))) :=
  sq_le_of_corr_le (by positivity) hpos (hcorr.trans
    (card_eval_eq_andreev_le_of_depth_le_two_wireCount hm hα hβ c hd o))

/-- Canonical wire bound: the counting loss is `b + 2 + log (c.wireCount + 1)`.
For polynomial resources this is linear in `b`, saving one logarithm over unrestricted LTF
  counting. -/
theorem wireCount_ge_of_card_eval_eq_andreev_ge_of_le_eps {b m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ ε)
    (c : Circuit signature (2 ^ b + b * m) 1) (hd : c.depth ≤ 2) (o : Fin 1)
    (hcorr : (2 : ℝ) ^ (2 ^ b + b * m) * (1 / 2 + ε) ≤
      (#{w : BitString (2 ^ b + b * m) | c.eval interpretation w o = andreev b m w} : ℝ)) :
    (m : ℝ) * Real.sqrt (m : ℝ) * (2 : ℝ) ^ b * ε ^ 2 ≤
      36 * ((b : ℝ) + 2 + Real.log (c.wireCount + 1)) * (c.wireCount : ℝ) := by
  have hε0 : 0 ≤ ε := (by positivity : 0 ≤ 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b)).trans hε
  have hex := excess_ge_of_three_mul_div_sqrt_le (b := b) (M := c.wireCount + 1) (by omega) hε
  have hp : 0 ≤ (2 : ℝ) ^ b * (ε - andreevWeightTail b (c.wireCount + 1)
      (andreevWeightScale b (c.wireCount + 1)) (((b : ℝ) + 2) * Real.sqrt ((2 : ℝ) ^ b))) -
      ((b : ℝ) + 2) * Real.sqrt ((2 : ℝ) ^ b) := (by positivity : 0 ≤ (2 : ℝ) ^ b * ε / 3).trans hex
  have h := (pow_le_pow_left₀ (by positivity) hex 2).trans
    (wireCount_ge_of_card_eval_eq_andreev_ge hm
      (sqrt_two_pow_div_two_le_andreevWeightScale b (by omega)) (by positivity) c hd o hp hcorr)
  rw [andreevWeightScale_sq b (by omega)] at h
  simp only [Nat.cast_add, Nat.cast_one] at h ⊢
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hmne : (m : ℝ) ≠ 0 := hmpos.ne'
  have hsne : Real.sqrt (m : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hmpos).ne'
  simp only [one_div, Real.sqrt_inv] at h
  have hmul := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (m : ℝ) * Real.sqrt (m : ℝ))
  have heq : (m : ℝ) * Real.sqrt (m : ℝ) * ((2 : ℝ) ^ b *
      ((b : ℝ) + 2 + Real.log (c.wireCount + 1)) *
      (4 * (c.wireCount : ℝ) * (m : ℝ)⁻¹ * (Real.sqrt (m : ℝ))⁻¹)) =
      (2 : ℝ) ^ b * (4 * ((b : ℝ) + 2 + Real.log (c.wireCount + 1)) * (c.wireCount : ℝ)) := by
    field_simp
  rw [heq] at hmul
  apply le_of_mul_le_mul_left (a := (2 : ℝ) ^ b) _ (by positivity)
  nlinarith

private theorem card_eval_eq_andreev_of_computes {b m : ℕ}
    (c : Circuit signature (2 ^ b + b * m) 1)
    (hcomp : c.Computes interpretation (single (andreev b m))) :
    (2 : ℝ) ^ (2 ^ b + b * m) * (1 / 2 + 1 / 2) ≤
      (#{w : BitString (2 ^ b + b * m) | c.eval interpretation w 0 = andreev b m w} : ℝ) := by
  have hall : (univ.filter fun w => c.eval interpretation w 0 = andreev b m w) = univ :=
    filter_true_of_mem fun w _ => congrFun (hcomp w) 0
  rw [hall, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]; push_cast; linarith

/-- Exact computation specializes the improved average-case bound at `ε = 1 / 2`. -/
theorem size_ge_of_computes_andreev {b m : ℕ} (hm : 0 < m)
    (hb : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ 1 / 2)
    (c : Circuit signature (2 ^ b + b * m) 1) (hd : c.depth ≤ 2)
    (hcomp : c.Computes interpretation (single (andreev b m))) :
    (m : ℝ) * (2 : ℝ) ^ b * (1 / 2) ^ 2 ≤
      36 * ((b : ℝ) + 2 + Real.log (c.size + 1)) * (c.size : ℝ) * Real.sqrt ((2 ^ b + b * m :
        ℕ) : ℝ) :=
  size_ge_of_card_eval_eq_andreev_ge_of_le_eps hm hb c hd 0
    (card_eval_eq_andreev_of_computes c hcomp)

/-- Exact computation specializes the improved average-case bound at `ε = 1 / 2`. -/
theorem wireCount_ge_of_computes_andreev {b m : ℕ} (hm : 0 < m)
    (hb : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ 1 / 2)
    (c : Circuit signature (2 ^ b + b * m) 1) (hd : c.depth ≤ 2)
    (hcomp : c.Computes interpretation (single (andreev b m))) :
    (m : ℝ) * Real.sqrt (m : ℝ) * (2 : ℝ) ^ b * (1 / 2) ^ 2 ≤
      36 * ((b : ℝ) + 2 + Real.log (c.wireCount + 1)) * (c.wireCount : ℝ) :=
  wireCount_ge_of_card_eval_eq_andreev_ge_of_le_eps hm hb c hd 0
    (card_eval_eq_andreev_of_computes c hcomp)

/-- Remove the logarithm of the resource by splitting at `2 ^ (3 * b)`. -/
private theorem resource_bound_of_log_bound (b r : ℕ) {L D : ℝ} (hD : 0 ≤ D)
    (hlarge : L ≤ (2 : ℝ) ^ (3 * b) * D)
    (hsmall : L ≤ 36 * ((b : ℝ) + 2 + Real.log (r + 1)) * r * D) :
    L ≤ 144 * ((b : ℝ) + 2) * r * D := by
  by_cases hr : r < 2 ^ (3 * b)
  · have hlog : Real.log ((r : ℝ) + 1) ≤ 3 * (b : ℝ) := by
      have hr' : (r : ℝ) + 1 ≤ (2 : ℝ) ^ (3 * b) := by exact_mod_cast (show r + 1 ≤ 2 ^ (3 * b)
        by omega)
      have he := Real.two_pow_le_exp (3 * b)
      have hle := Real.log_le_log (by positivity : (0 : ℝ) < (r : ℝ) + 1) (hr'.trans he)
      simpa only [Real.log_exp, Nat.cast_mul, Nat.cast_ofNat] using hle
    refine hsmall.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by linarith : 36 * ((b : ℝ) + 2 + Real.log (r + 1)) ≤ 144 * ((b : ℝ) + 2))
      (Nat.cast_nonneg r)) hD
  · have hr' : (2 : ℝ) ^ (3 * b) ≤ r := by exact_mod_cast not_lt.mp hr
    calc L ≤ (2 : ℝ) ^ (3 * b) * D := hlarge
         _ ≤ (r : ℝ) * D := mul_le_mul_of_nonneg_right hr' hD
         _ ≤ 144 * ((b : ℝ) + 2) * r * D := by
           exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (Nat.cast_nonneg r)
             (by linarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ b)])) hD

/-- Explicit gate bound with a linear counting loss in `b`, valid when `m ≤ 2 ^ b`.
At `b * m = 2 ^ b` this gives `Ω(ε² n^(3/2) / log² n)`. -/
theorem size_ge_of_card_eval_eq_andreev_ge_of_le_two_pow {b m : ℕ} (hm : 0 < m)
    (hmN : m ≤ 2 ^ b) {ε : ℝ}
    (hε : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ ε) (hε1 : ε ≤ 1)
    (c : Circuit signature (2 ^ b + b * m) 1) (hd : c.depth ≤ 2) (o : Fin 1)
    (hcorr : (2 : ℝ) ^ (2 ^ b + b * m) * (1 / 2 + ε) ≤
      (#{w : BitString (2 ^ b + b * m) | c.eval interpretation w o = andreev b m w} : ℝ)) :
    (m : ℝ) * (2 : ℝ) ^ b * ε ^ 2 ≤
      144 * ((b : ℝ) + 2) * (c.size : ℝ) * Real.sqrt ((2 ^ b + b * m : ℕ) : ℝ) := by
  have hε0 : 0 ≤ ε := (by positivity : 0 ≤ 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b)).trans hε
  have hεsq : ε ^ 2 ≤ 1 := by nlinarith
  have hN1 : (1 : ℝ) ≤ (2 : ℝ) ^ b := one_le_pow₀ (by norm_num)
  have hmN' : (m : ℝ) ≤ (2 : ℝ) ^ b := by exact_mod_cast hmN
  have hs1 : (1 : ℝ) ≤ Real.sqrt ((2 ^ b + b * m : ℕ) : ℝ) := by
    apply Real.one_le_sqrt.mpr
    exact_mod_cast (show 1 ≤ 2 ^ b + b * m by have := Nat.one_le_two_pow (n := b); omega)
  apply resource_bound_of_log_bound b c.size (by positivity) _
    (size_ge_of_card_eval_eq_andreev_ge_of_le_eps hm hε c hd o hcorr)
  calc (m : ℝ) * (2 : ℝ) ^ b * ε ^ 2 ≤ (2 : ℝ) ^ b * (2 : ℝ) ^ b * 1 := by gcongr
       _ ≤ (2 : ℝ) ^ b * (2 : ℝ) ^ b * (2 : ℝ) ^ b *
           Real.sqrt ((2 ^ b + b * m : ℕ) : ℝ) := by
           have hprod : 1 ≤ (2 : ℝ) ^ b * Real.sqrt ((2 ^ b + b * m : ℕ) : ℝ) := by
             nlinarith [mul_nonneg (sub_nonneg.mpr hN1) (sub_nonneg.mpr hs1)]
           have hp := mul_le_mul_of_nonneg_left hprod
             (by positivity : 0 ≤ (2 : ℝ) ^ b * (2 : ℝ) ^ b)
           nlinarith
       _ = (2 : ℝ) ^ (3 * b) * Real.sqrt ((2 ^ b + b * m : ℕ) : ℝ) := by
         rw [Nat.mul_comm 3 b, pow_mul]; ring

/-- Explicit active-wire bound with linear counting loss in `b`.
At `b * m = 2 ^ b` this gives `Ω(ε² n^(5/2) / log^(5/2) n)`. -/
theorem wireCount_ge_of_card_eval_eq_andreev_ge_of_le_two_pow {b m : ℕ} (hm : 0 < m)
    (hmN : m ≤ 2 ^ b) {ε : ℝ}
    (hε : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ ε) (hε1 : ε ≤ 1)
    (c : Circuit signature (2 ^ b + b * m) 1) (hd : c.depth ≤ 2) (o : Fin 1)
    (hcorr : (2 : ℝ) ^ (2 ^ b + b * m) * (1 / 2 + ε) ≤
      (#{w : BitString (2 ^ b + b * m) | c.eval interpretation w o = andreev b m w} : ℝ)) :
    (m : ℝ) * Real.sqrt (m : ℝ) * (2 : ℝ) ^ b * ε ^ 2 ≤
      144 * ((b : ℝ) + 2) * (c.wireCount : ℝ) := by
  have hε0 : 0 ≤ ε := (by positivity : 0 ≤ 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b)).trans hε
  have hεsq : ε ^ 2 ≤ 1 := by nlinarith
  have hN1 : (1 : ℝ) ≤ (2 : ℝ) ^ b := one_le_pow₀ (by norm_num)
  have hmN' : (m : ℝ) ≤ (2 : ℝ) ^ b := by exact_mod_cast hmN
  have hsN : Real.sqrt (m : ℝ) ≤ (2 : ℝ) ^ b := by
    have hsq := Real.sq_sqrt (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    nlinarith [Real.sqrt_nonneg (m : ℝ)]
  have h := resource_bound_of_log_bound b c.wireCount (D := 1) (by norm_num)
    (show (m : ℝ) * Real.sqrt (m : ℝ) * (2 : ℝ) ^ b * ε ^ 2 ≤ (2 : ℝ) ^ (3 * b) * 1 by
      calc _ ≤ (2 : ℝ) ^ b * (2 : ℝ) ^ b * (2 : ℝ) ^ b * 1 := by gcongr
           _ = _ := by rw [Nat.mul_comm 3 b, pow_mul]; ring)
    (by simpa using wireCount_ge_of_card_eval_eq_andreev_ge_of_le_eps hm hε c hd o hcorr)
  simpa using h

end Cslib.Circuits.Boolean.WeightedThreshold
