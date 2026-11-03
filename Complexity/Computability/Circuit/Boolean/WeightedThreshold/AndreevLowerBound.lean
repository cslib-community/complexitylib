/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.WeightedThreshold.Andreev
public import Complexity.Computability.Circuit.Boolean.WeightedThreshold.ThresholdCounting
public import Complexity.Foundations.Combinatorics.Hoeffding

/-!
# Depth-two threshold gate and wire lower bounds for Andreev's function

For any `b, m : ℕ` with `m > 0`, any scale parameter `α ≥ √(2 ^ b) / 2`, and any depth-two
weighted threshold circuit `c : Circuit signature (2 ^ b + b * m) 1` (`c.depth ≤ 2`), this module
bounds the number of inputs `w : BitString (2 ^ b + b * m)` (`n = 2 ^ b + b * m`) on which `c`
agrees with Andreev's function `Boolean.andreev b m` using a simultaneous-in-`q` union bound over
all surviving gate counts `q < 2 ^ b` at deviation `t_q = α * √(q + 1)` and Jensen's inequality:

* **Gate correlation and `Ω(ε ^ 2 * n ^ (3 / 2) / log ^ 3 n)` lower bounds**
  (`card_eval_eq_andreev_le_of_depth_le_two_size`, `size_ge_of_card_eval_eq_andreev_ge`,
  `size_ge_of_computes_andreev`):
  `m * ((2 ^ b * (ε - andreevSimultaneousTail b α)) ^ 2 - α ^ 2) ≤ 4 * α ^ 2 * c.size * √n`.
* **Wire correlation and `Ω(ε ^ 2 * n ^ (5 / 2) / log ^ (7 / 2) n)` lower bounds**
  (`card_eval_eq_andreev_le_of_depth_le_two_wireCount`, `wireCount_ge_of_card_eval_eq_andreev_ge`,
  `wireCount_ge_of_computes_andreev`):
  `(2 ^ b * (ε - andreevSimultaneousTail b α)) ^ 2 - α ^ 2 ≤`
  `  4 * α ^ 2 * c.wireCount * (1 / m) * √(1 / m)`.

Avoiding Markov's inequality on the number of surviving bottom gates preserves the quadratic
`ε ^ 2` dependence when squaring the correlation excess, improving the `Ω(ε ^ 3)` gate and wire
bounds of Kane and Williams ([KaneWilliams2016], `arXiv:1511.07860v1`, Theorems 1.1 and 4.1) by a
factor of `1 / ε`.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open BitString Finset Cslib.Combinatorics.LittlewoodOfford

/-! ### Live block variables and subcube evaluation of Andreev's function -/

/-- `andreevBlockVar b m` is jointly injective across blocks `j : Fin b` and slots `t : Fin m`. -/
theorem andreevBlockVar_joint_injective (b m : ℕ) :
    ∀ (j₁ : Fin b) (t₁ : Fin m) (j₂ : Fin b) (t₂ : Fin m),
      andreevBlockVar b m j₁ t₁ = andreevBlockVar b m j₂ t₂ → j₁ = j₂ ∧ t₁ = t₂ := fun _ _ _ _ h =>
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
    (j : Fin b) (t : Fin m) : andreevTableIndex b m idx ≠ andreevBlockVar b m j t := by
  intro h; have hval := congrArg Fin.val h
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

/-- Updating the live block variables `andreevLiveVar b m σ` of `w` with `u : BitString b` shifts
the block parities of `w` to `u + andreevResidualParities b m σ w`. -/
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
    have ⟨h1, h2⟩ := andreevBlockVar_joint_injective b m j' (σ j') j t hj'
    subst h1; exact (mem_erase.mp ht).1 h2.symm

/-- Along the subcube `u ↦ embedUpdate (andreevLiveVar b m σ) w u`, `andreev b m` reads the
truth-table bit of `w` at `u + andreevResidualParities b m σ w`. -/
theorem andreev_embedUpdate_andreevLiveVar (b m : ℕ) (σ : Fin b → Fin m)
    (w : BitString (2 ^ b + b * m)) (u : BitString b) :
    andreev b m (embedUpdate (andreevLiveVar b m σ) w u) =
      w (andreevTableIndex b m (BitString.equivFin b (u + andreevResidualParities b m σ w))) := by
  rw [andreev_eq_table_parities, andreevParities_embedUpdate_andreevLiveVar,
    embedUpdate_of_notMem w u (andreevTableIndex_notMem_image_andreevLiveVar b m σ _)]

/-! ### Measure-preserving truth-table involutions and Hoeffding tail bound -/

/-- The `2 ^ b` truth-table coordinates in `Fin (2 ^ b + b * m)`. -/
def andreevTableCoords (b m : ℕ) : Finset (Fin (2 ^ b + b * m)) :=
  univ.image (andreevTableIndex b m)

/-- `andreevTableIndex b m` is injective. -/
theorem andreevTableIndex_injective (b m : ℕ) : Function.Injective (andreevTableIndex b m) :=
  Fin.castAdd_injective (2 ^ b) (b * m)

/-- `andreevTableCoords b m` has cardinality `2 ^ b`. -/
@[simp] theorem card_andreevTableCoords (b m : ℕ) : #(andreevTableCoords b m) = 2 ^ b := by
  rw [andreevTableCoords, card_image_of_injective _ (andreevTableIndex_injective b m),
    card_univ, Fintype.card_fin]

/-- Involution on `BitString (2 ^ b + b * m)` that translates the truth-table coordinates by
`andreevResidualParities b m σ w` and leaves all `b * m` block coordinates unchanged. -/
def andreevShiftResidual (b m : ℕ) (σ : Fin b → Fin m)
    (w : BitString (2 ^ b + b * m)) : BitString (2 ^ b + b * m) :=
  Fin.addCases (fun idx => w (andreevTableIndex b m
    (BitString.equivFin b ((BitString.equivFin b).symm idx + andreevResidualParities b m σ w))))
    (fun v => w (Fin.natAdd (2 ^ b) v))

@[simp] theorem andreevShiftResidual_tableIndex (b m : ℕ) (σ : Fin b → Fin m)
    (w : BitString (2 ^ b + b * m)) (idx : Fin (2 ^ b)) :
    andreevShiftResidual b m σ w (andreevTableIndex b m idx) =
      w (andreevTableIndex b m (BitString.equivFin b
        ((BitString.equivFin b).symm idx + andreevResidualParities b m σ w))) := by
  simp [andreevShiftResidual, andreevTableIndex]

@[simp] theorem andreevShiftResidual_natAdd (b m : ℕ) (σ : Fin b → Fin m)
    (w : BitString (2 ^ b + b * m)) (v : Fin (b * m)) :
    andreevShiftResidual b m σ w (Fin.natAdd (2 ^ b) v) = w (Fin.natAdd (2 ^ b) v) := by
  simp [andreevShiftResidual]

@[simp] theorem andreevResidualParities_andreevShiftResidual (b m : ℕ) (σ : Fin b → Fin m)
    (w : BitString (2 ^ b + b * m)) :
    andreevResidualParities b m σ (andreevShiftResidual b m σ w) =
      andreevResidualParities b m σ w := by
  funext j; simp [andreevResidualParities, andreevBlockVar]

/-- `andreevShiftResidual b m σ` is an involution. -/
theorem andreevShiftResidual_involutive (b m : ℕ) (σ : Fin b → Fin m) :
    Function.Involutive (andreevShiftResidual b m σ) := fun w => by
  funext i; refine Fin.addCases (fun idx => ?_) (fun v => by simp) i
  change andreevShiftResidual b m σ (andreevShiftResidual b m σ w) (andreevTableIndex b m idx) =
    w (andreevTableIndex b m idx); simp

/-- Involution on `BitString (2 ^ b + b * m)` that XNORs each truth-table coordinate `idx` with
`h ((BitString.equivFin b).symm idx)` and leaves all `b * m` block coordinates unchanged. -/
def andreevAlignTable (b m : ℕ) (h : BitString b → Bool)
    (w : BitString (2 ^ b + b * m)) : BitString (2 ^ b + b * m) :=
  Fin.addCases (fun idx => !(w (andreevTableIndex b m idx) ^^ h ((BitString.equivFin b).symm idx)))
    (fun v => w (Fin.natAdd (2 ^ b) v))

@[simp] theorem andreevAlignTable_tableIndex (b m : ℕ) (h : BitString b → Bool)
    (w : BitString (2 ^ b + b * m)) (idx : Fin (2 ^ b)) :
    andreevAlignTable b m h w (andreevTableIndex b m idx) =
      !(w (andreevTableIndex b m idx) ^^ h ((BitString.equivFin b).symm idx)) := by
  simp [andreevAlignTable, andreevTableIndex]

@[simp] theorem andreevAlignTable_natAdd (b m : ℕ) (h : BitString b → Bool)
    (w : BitString (2 ^ b + b * m)) (v : Fin (b * m)) :
    andreevAlignTable b m h w (Fin.natAdd (2 ^ b) v) = w (Fin.natAdd (2 ^ b) v) := by
  simp [andreevAlignTable]

/-- `andreevAlignTable b m h` is an involution. -/
theorem andreevAlignTable_involutive (b m : ℕ) (h : BitString b → Bool) :
    Function.Involutive (andreevAlignTable b m h) := fun w => by
  funext i; refine Fin.addCases (fun idx => ?_) (fun v => by simp) i
  change andreevAlignTable b m h (andreevAlignTable b m h w) (andreevTableIndex b m idx) =
    w (andreevTableIndex b m idx)
  simp only [andreevAlignTable_tableIndex]
  cases w (andreevTableIndex b m idx) <;> cases h ((BitString.equivFin b).symm idx) <;> rfl

/-- Composite permutation on `BitString (2 ^ b + b * m)`. -/
def andreevSubcubePerm (b m : ℕ) (σ : Fin b → Fin m) (h : BitString b → Bool) :
    Equiv.Perm (BitString (2 ^ b + b * m)) :=
  (andreevShiftResidual_involutive b m σ).toPerm.trans (andreevAlignTable_involutive b m h).toPerm

/-- Under `andreevSubcubePerm b m σ h`, the number of `u : BitString b` where `h u` agrees with
`andreev b m (embedUpdate (andreevLiveVar b m σ) w u)` equals the number of `true` coordinates of
`andreevSubcubePerm b m σ h w` in `andreevTableCoords b m`. -/
theorem card_subcube_agree_andreev_eq_card_tableCoords_true (b m : ℕ) (σ : Fin b → Fin m)
    (h : BitString b → Bool) (w : BitString (2 ^ b + b * m)) :
    #{u : BitString b | h u = andreev b m (embedUpdate (andreevLiveVar b m σ) w u)} =
      #{i ∈ andreevTableCoords b m | andreevSubcubePerm b m σ h w i = true} := by
  rw [andreevTableCoords, filter_image, card_image_of_injective _ (andreevTableIndex_injective b m),
    ← Fintype.card_subtype, ← Fintype.card_subtype]
  refine Fintype.card_congr ((BitString.equivFin b).subtypeEquiv fun u => ?_)
  simp only [andreevSubcubePerm, Equiv.trans_apply, Function.Involutive.coe_toPerm,
    andreevAlignTable_tableIndex, andreevShiftResidual_tableIndex, Equiv.symm_apply_apply,
    andreev_embedUpdate_andreevLiveVar]
  cases h u <;>
    cases w (andreevTableIndex b m (BitString.equivFin b (u + andreevResidualParities b m σ w))) <;>
    decide

/-- **Subcube Hoeffding Tail Bound**: for any `σ : Fin b → Fin m`, fixed `h : BitString b → Bool`,
and `t ≥ 0`, at most `2 ^ (2 ^ b + b * m) * exp (-2 * t ^ 2 / 2 ^ b)` assignments `w` have `h`
agree with `u ↦ andreev b m (embedUpdate (andreevLiveVar b m σ) w u)` on `≥ 2 ^ b / 2 + t` points.
-/
theorem card_subcube_agree_andreev_le (b m : ℕ) (σ : Fin b → Fin m) (h : BitString b → Bool)
    {t : ℝ} (ht : 0 ≤ t) :
    (#{w : BitString (2 ^ b + b * m) |
      t ≤ (#{u : BitString b | h u = andreev b m (embedUpdate (andreevLiveVar b m σ) w u)} : ℝ) -
        (2 : ℝ) ^ b / 2} : ℝ) ≤
      (2 : ℝ) ^ (2 ^ b + b * m) * Real.exp (-(2 * t ^ 2 / (2 : ℝ) ^ b)) := by
  have hcard : #{w : BitString (2 ^ b + b * m) |
      t ≤ (#{u : BitString b | h u = andreev b m (embedUpdate (andreevLiveVar b m σ) w u)} : ℝ) -
        (2 : ℝ) ^ b / 2} = #{w' : BitString (2 ^ b + b * m) |
      t ≤ (#{i ∈ andreevTableCoords b m | w' i = true} : ℝ) -
        (#(andreevTableCoords b m) : ℝ) / 2} := by
    simp_rw [card_subcube_agree_andreev_eq_card_tableCoords_true]
    rw [card_andreevTableCoords, Nat.cast_pow, Nat.cast_ofNat,
      ← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_congr ((andreevSubcubePerm b m σ h).subtypeEquiv fun _ => Iff.rfl)
  rw [hcard]
  simpa [Fintype.card_fin] using
    Cslib.BitString.card_filter_le_card_filter_sub_half_le (andreevTableCoords b m) true ht

/-- **Union Bound over Small Depth-Two Circuits**: for any `σ : Fin b → Fin m`, `Q : ℕ`, and
`t ≥ 0`, at most
`2 ^ (2 ^ b + b * m) * (2 ^ b + 1) ^ ((b + 2) * Q + b + 1) * exp (-2 * t ^ 2 / 2 ^ b)` inputs `w`
have some `IsDepthTwoWithGates Q` function agree with `andreev b m` on `≥ 2 ^ b / 2 + t` points. -/
theorem card_exists_isDepthTwoWithGates_agree_andreev_le (b m Q : ℕ) (σ : Fin b → Fin m)
    {t : ℝ} (ht : 0 ≤ t) :
    (#{w : BitString (2 ^ b + b * m) | ∃ h : BitString b → Bool, IsDepthTwoWithGates Q h ∧
      t ≤ (#{u : BitString b | h u = andreev b m (embedUpdate (andreevLiveVar b m σ) w u)} : ℝ) -
        (2 : ℝ) ^ b / 2} : ℝ) ≤
      (2 : ℝ) ^ (2 ^ b + b * m) * ((2 ^ b + 1) ^ ((b + 2) * Q + b + 1) : ℝ) *
        Real.exp (-(2 * t ^ 2 / (2 : ℝ) ^ b)) := by
  classical
  let H : Finset (BitString b → Bool) := univ.filter (IsDepthTwoWithGates Q)
  have hbi : (#{w : BitString (2 ^ b + b * m) | ∃ h : BitString b → Bool, IsDepthTwoWithGates Q h ∧
      t ≤ (#{u : BitString b | h u = andreev b m (embedUpdate (andreevLiveVar b m σ) w u)} : ℝ) -
        (2 : ℝ) ^ b / 2} : ℝ) ≤ ∑ h ∈ H, (#{w : BitString (2 ^ b + b * m) |
      t ≤ (#{u : BitString b | h u = andreev b m (embedUpdate (andreevLiveVar b m σ) w u)} : ℝ) -
        (2 : ℝ) ^ b / 2} : ℝ) := by
    exact_mod_cast (card_le_card fun w hw => by
      simp only [H, mem_filter, mem_univ, true_and, mem_biUnion] at hw ⊢; exact hw).trans
      card_biUnion_le
  refine hbi.trans ((sum_le_sum fun h _ => card_subcube_agree_andreev_le b m σ h ht).trans ?_)
  rw [sum_const, nsmul_eq_mul]
  have hH : (#H : ℝ) ≤ ((2 ^ b + 1) ^ ((b + 2) * Q + b + 1) : ℝ) := by
    simpa [H, Fintype.card_fin] using
      (Nat.cast_le (α := ℝ)).mpr (card_isDepthTwoWithGates_le (κ := Fin b) Q)
  exact (mul_le_mul_of_nonneg_right hH (by positivity)).trans_eq (by ring)

/-! ### Simultaneous union bound over all surviving gate counts `q < 2 ^ b` -/

/-- The simultaneous union-bound tail over all surviving gate counts `q < 2 ^ b` at deviation
`t_q = α * √(q + 1)`. -/
noncomputable def andreevSimultaneousTail (b : ℕ) (α : ℝ) : ℝ :=
  ∑ q ∈ range (2 ^ b), ((2 ^ b + 1) ^ ((b + 2) * q + b + 1) : ℝ) *
    Real.exp (-(2 * α ^ 2 * ((q : ℝ) + 1) / (2 : ℝ) ^ b))

/-- When the per-gate ratio `((2 ^ b + 1) ^ (b + 2) : ℝ) * exp (-2 * α ^ 2 / 2 ^ b)` is at most `1`,
`andreevSimultaneousTail b α` is at most
`2 ^ b * (2 ^ b + 1) ^ (b + 2) * exp (-2 * α ^ 2 / 2 ^ b)`. -/
theorem andreevSimultaneousTail_le (b : ℕ) {α : ℝ}
    (hα : ((2 ^ b + 1) ^ (b + 2) : ℝ) * Real.exp (-(2 * α ^ 2 / (2 : ℝ) ^ b)) ≤ 1) :
    andreevSimultaneousTail b α ≤
      (2 : ℝ) ^ b * ((2 ^ b + 1) ^ (b + 2) : ℝ) * Real.exp (-(2 * α ^ 2 / (2 : ℝ) ^ b)) := by
  unfold andreevSimultaneousTail
  let r : ℝ := ((2 ^ b + 1) ^ (b + 2) : ℝ) * Real.exp (-(2 * α ^ 2 / (2 : ℝ) ^ b))
  have hr_term (q : ℕ) : ((2 ^ b + 1) ^ ((b + 2) * q + b + 1) : ℝ) *
      Real.exp (-(2 * α ^ 2 * ((q : ℝ) + 1) / (2 : ℝ) ^ b)) ≤ r := by
    have hpow_le : ((2 ^ b + 1) ^ ((b + 2) * q + b + 1) : ℝ) ≤
        (((2 ^ b + 1) ^ (b + 2) : ℝ)) ^ (q + 1) := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ (by linarith [(by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ b)]) (by linarith)
    have hexp_eq : Real.exp (-(2 * α ^ 2 * ((q : ℝ) + 1) / (2 : ℝ) ^ b)) =
        (Real.exp (-(2 * α ^ 2 / (2 : ℝ) ^ b))) ^ (q + 1) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hmul : ((2 ^ b + 1) ^ ((b + 2) * q + b + 1) : ℝ) *
          Real.exp (-(2 * α ^ 2 * ((q : ℝ) + 1) / (2 : ℝ) ^ b)) ≤ r ^ (q + 1) := by
      rw [hexp_eq]; exact (mul_le_mul_of_nonneg_right hpow_le (by positivity)).trans_eq
        (mul_pow _ _ _).symm
    exact hmul.trans (pow_le_of_le_one (by positivity) hα (Nat.succ_ne_zero q))
  refine (sum_le_sum fun q _ => hr_term q).trans_eq ?_
  rw [sum_const, card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc]

/-- **Simultaneous Union Bound over all `q < 2 ^ b`**: for any `σ : Fin b → Fin m` and `α ≥ 0`,
the number of `w : BitString (2 ^ b + b * m)` for which *some* `q < 2 ^ b` and *some*
`h : BitString b → Bool` with `IsDepthTwoWithGates q h` have subcube agreement at least
`2 ^ b / 2 + α * √(q + 1)` is at most `2 ^ (2 ^ b + b * m) * andreevSimultaneousTail b α`. -/
theorem card_exists_lt_two_pow_isDepthTwoWithGates_agree_andreev_le (b m : ℕ)
    (σ : Fin b → Fin m) {α : ℝ} (hα : 0 ≤ α) :
    (#{w : BitString (2 ^ b + b * m) | ∃ q < 2 ^ b, ∃ h : BitString b → Bool,
      IsDepthTwoWithGates q h ∧ α * Real.sqrt ((q : ℝ) + 1) ≤
        (#{u : BitString b | h u = andreev b m (embedUpdate (andreevLiveVar b m σ) w u)} : ℝ) -
          (2 : ℝ) ^ b / 2} : ℝ) ≤
      (2 : ℝ) ^ (2 ^ b + b * m) * andreevSimultaneousTail b α := by
  classical
  have hbi : (#{w : BitString (2 ^ b + b * m) | ∃ q < 2 ^ b, ∃ h : BitString b → Bool,
      IsDepthTwoWithGates q h ∧ α * Real.sqrt ((q : ℝ) + 1) ≤
        (#{u : BitString b | h u = andreev b m (embedUpdate (andreevLiveVar b m σ) w u)} : ℝ) -
          (2 : ℝ) ^ b / 2} : ℝ) ≤ ∑ q ∈ range (2 ^ b), (#{w : BitString (2 ^ b + b * m) |
      ∃ h : BitString b → Bool, IsDepthTwoWithGates q h ∧ α * Real.sqrt ((q : ℝ) + 1) ≤
        (#{u : BitString b | h u = andreev b m (embedUpdate (andreevLiveVar b m σ) w u)} : ℝ) -
          (2 : ℝ) ^ b / 2} : ℝ) := by
    exact_mod_cast (card_le_card fun w hw => by
      simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_range] at hw ⊢; exact hw).trans
      card_biUnion_le
  refine hbi.trans ?_
  unfold andreevSimultaneousTail; rw [mul_sum]
  refine sum_le_sum fun q _ => ?_
  have hq := card_exists_isDepthTwoWithGates_agree_andreev_le b m q σ
    (by positivity : 0 ≤ α * Real.sqrt ((q : ℝ) + 1))
  have hsq : (α * Real.sqrt ((q : ℝ) + 1)) ^ 2 = α ^ 2 * ((q : ℝ) + 1) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [hsq, ← mul_assoc] at hq
  exact hq.trans_eq (by ring)

/-! ### Simultaneous subcube averaging via Jensen / AM-GM -/

/-- Simultaneous-in-`q` correlation bound for `f : BitString (2 ^ b + b * m) → Bool` against
`andreev b m` given an unforced-gate count `U σ w` with average at most `B ≥ 0`. -/
theorem card_eval_eq_andreev_le_of_unforced_mean_le {b m : ℕ} (hm : 0 < m)
    {α B : ℝ} (hα : Real.sqrt ((2 : ℝ) ^ b) / 2 ≤ α) (hB0 : 0 ≤ B)
    (f : BitString (2 ^ b + b * m) → Bool)
    (U : (Fin b → Fin m) → BitString (2 ^ b + b * m) → ℕ)
    (hU : ∀ (σ : Fin b → Fin m) (w : BitString (2 ^ b + b * m)),
      IsDepthTwoWithGates (U σ w)
        (fun u : BitString b => f (embedUpdate (andreevLiveVar b m σ) w u)))
    (hmean : (∑ σ : Fin b → Fin m, ∑ w : BitString (2 ^ b + b * m), (U σ w : ℝ)) ≤
      (Fintype.card (Fin b → Fin m) : ℝ) * (2 : ℝ) ^ (2 ^ b + b * m) * B) :
    (#{w : BitString (2 ^ b + b * m) | f w = andreev b m w} : ℝ) ≤
      (2 : ℝ) ^ (2 ^ b + b * m) *
        (1 / 2 + (α / (2 : ℝ) ^ b) * Real.sqrt (B + 1) + andreevSimultaneousTail b α) := by
  classical
  have hα0 : 0 ≤ α := (by positivity : (0 : ℝ) ≤ Real.sqrt ((2 : ℝ) ^ b) / 2).trans hα
  have h2b_pos : (0 : ℝ) < (2 : ℝ) ^ b := by positivity
  let S : ℝ := Real.sqrt (B + 1)
  have hS_pos : 0 < S := Real.sqrt_pos.mpr (by linarith)
  have hS_sq : S ^ 2 = B + 1 := Real.sq_sqrt (by linarith)
  let agree (σ : Fin b → Fin m) (w : BitString (2 ^ b + b * m)) : ℝ :=
    (#{u : BitString b | f (embedUpdate (andreevLiveVar b m σ) w u) =
      andreev b m (embedUpdate (andreevLiveVar b m σ) w u)} : ℝ)
  have hσ_step (σ : Fin b → Fin m) :
      (#{w : BitString (2 ^ b + b * m) | f w = andreev b m w} : ℝ) ≤
        (2 : ℝ) ^ (2 ^ b + b * m) * (1 / 2 + andreevSimultaneousTail b α) +
          (α / ((2 : ℝ) ^ b * (2 * S))) *
            ∑ w : BitString (2 ^ b + b * m), ((U σ w : ℝ) + 1 + S ^ 2) := by
    let Bad : Finset (BitString (2 ^ b + b * m)) :=
      univ.filter fun w => ∃ q < 2 ^ b, ∃ h : BitString b → Bool, IsDepthTwoWithGates q h ∧
        α * Real.sqrt ((q : ℝ) + 1) ≤
          (#{u : BitString b | h u = andreev b m (embedUpdate (andreevLiveVar b m σ) w u)} : ℝ) -
            (2 : ℝ) ^ b / 2
    have hpt (w : BitString (2 ^ b + b * m)) :
        agree σ w ≤ (2 : ℝ) ^ b / 2 + (α / (2 * S)) * ((U σ w : ℝ) + 1 + S ^ 2) +
          if w ∈ Bad then (2 : ℝ) ^ b else 0 := by
      have hle_2b : agree σ w ≤ (2 : ℝ) ^ b := by
        dsimp [agree]; exact_mod_cast (card_le_univ _).trans_eq (by simp)
      have hsqrt_le : Real.sqrt ((U σ w : ℝ) + 1) ≤ ((U σ w : ℝ) + 1 + S ^ 2) / (2 * S) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (Real.sqrt ((U σ w : ℝ) + 1) - S),
          Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (U σ w : ℝ) + 1)]
      have hα_sqrt : α * Real.sqrt ((U σ w : ℝ) + 1) ≤
          (α / (2 * S)) * ((U σ w : ℝ) + 1 + S ^ 2) :=
        (mul_le_mul_of_nonneg_left hsqrt_le hα0).trans_eq (by ring)
      have hnonneg : (0 : ℝ) ≤ (2 : ℝ) ^ b / 2 +
          (α / (2 * S)) * ((U σ w : ℝ) + 1 + S ^ 2) := by positivity
      by_cases hbad : w ∈ Bad
      · simp only [hbad, ↓reduceIte]; linarith
      · simp only [hbad, ↓reduceIte, add_zero]
        by_cases hlt : U σ w < 2 ^ b
        · have hnot_ge : ¬ (α * Real.sqrt ((U σ w : ℝ) + 1) ≤ agree σ w - (2 : ℝ) ^ b / 2) :=
            fun hge => hbad (mem_filter.mpr ⟨mem_univ w, U σ w, hlt, _, hU σ w, hge⟩)
          linarith [lt_of_not_ge hnot_ge]
        · have h2b_le : (2 : ℝ) ^ b ≤ (U σ w : ℝ) + 1 := by
            exact_mod_cast (by omega : (2 ^ b : ℕ) ≤ U σ w + 1)
          have hhalf : (2 : ℝ) ^ b / 2 ≤ α * Real.sqrt ((U σ w : ℝ) + 1) := by
            calc (2 : ℝ) ^ b / 2
                = (Real.sqrt ((2 : ℝ) ^ b) / 2) * Real.sqrt ((2 : ℝ) ^ b) := by
                  rw [div_mul_eq_mul_div, Real.mul_self_sqrt h2b_pos.le]
              _ ≤ α * Real.sqrt ((U σ w : ℝ) + 1) :=
                  mul_le_mul hα (Real.sqrt_le_sqrt h2b_le) (by positivity) hα0
          linarith
    have hsum_eq : (∑ w : BitString (2 ^ b + b * m), agree σ w) =
        (2 : ℝ) ^ b * (#{w : BitString (2 ^ b + b * m) | f w = andreev b m w} : ℝ) := by
      have hnat := sum_card_filter_embedUpdate (andreevLiveVar_injective b m σ)
        (fun w' => f w' = andreev b m w')
      rw [Fintype.card_fin] at hnat; dsimp [agree]; exact_mod_cast hnat
    have hsum_le := sum_le_sum fun w (_ : w ∈ univ) => hpt w
    rw [hsum_eq, sum_add_distrib, sum_add_distrib, sum_const, card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, ← mul_sum,
      ← sum_filter, filter_mem_eq_inter, univ_inter, sum_const, nsmul_eq_mul] at hsum_le
    have hBad_le := card_exists_lt_two_pow_isDepthTwoWithGates_agree_andreev_le b m σ hα0
    have h2b_ne : (2 : ℝ) ^ b ≠ 0 := h2b_pos.ne'
    have hS_ne : S ≠ 0 := hS_pos.ne'
    refine le_of_mul_le_mul_left ?_ h2b_pos
    exact (hsum_le.trans (add_le_add_right
      (mul_le_mul_of_nonneg_right hBad_le h2b_pos.le) _)).trans_eq (by field_simp; ring)
  have hcard_σ_pos : (0 : ℝ) < (Fintype.card (Fin b → Fin m) : ℝ) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]; positivity
  have hsum_σ := sum_le_sum fun σ (_ : σ ∈ univ) => hσ_step σ
  rw [sum_add_distrib, sum_const, sum_const, card_univ, nsmul_eq_mul, nsmul_eq_mul,
    ← mul_sum] at hsum_σ
  have hsum_U : (∑ σ : Fin b → Fin m, ∑ w : BitString (2 ^ b + b * m),
      ((U σ w : ℝ) + 1 + S ^ 2)) ≤
      (Fintype.card (Fin b → Fin m) : ℝ) * (2 : ℝ) ^ (2 ^ b + b * m) * (2 * S ^ 2) := by
    have h1 : (∑ σ : Fin b → Fin m, ∑ w : BitString (2 ^ b + b * m), ((U σ w : ℝ) + 1 + S ^ 2)) =
        (∑ σ : Fin b → Fin m, ∑ w : BitString (2 ^ b + b * m), (U σ w : ℝ)) +
          (Fintype.card (Fin b → Fin m) : ℝ) * (2 : ℝ) ^ (2 ^ b + b * m) * (1 + S ^ 2) := by
      simp_rw [add_assoc, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
      simp [Fintype.card_fin]; ring
    have h2 : (Fintype.card (Fin b → Fin m) : ℝ) * (2 : ℝ) ^ (2 ^ b + b * m) * B +
        (Fintype.card (Fin b → Fin m) : ℝ) * (2 : ℝ) ^ (2 ^ b + b * m) * (1 + S ^ 2) =
        (Fintype.card (Fin b → Fin m) : ℝ) * (2 : ℝ) ^ (2 ^ b + b * m) * (2 * S ^ 2) := by
      rw [hS_sq]; ring
    linarith
  refine le_of_mul_le_mul_left ?_ hcard_σ_pos
  have hS_ne : S ≠ 0 := hS_pos.ne'
  have h2b_ne : (2 : ℝ) ^ b ≠ 0 := h2b_pos.ne'
  exact (hsum_σ.trans (add_le_add_right
    (mul_le_mul_of_nonneg_left hsum_U (by positivity)) _)).trans_eq (by field_simp; ring)

/-- Algebraic squaring step converting a correlation bound of the form
`2 ^ n * (1 / 2 + ε) ≤ 2 ^ n * (1 / 2 + (α / 2 ^ b) * √(B + 1) + tail)` into
`(2 ^ b * (ε - tail)) ^ 2 - α ^ 2 ≤ α ^ 2 * B`. -/
private theorem sq_sub_le_of_corr_le {b n : ℕ} {α ε tail B : ℝ}
    (hB0 : 0 ≤ B) (htail : tail ≤ ε)
    (hbound : (2 : ℝ) ^ n * (1 / 2 + ε) ≤
      (2 : ℝ) ^ n * (1 / 2 + (α / (2 : ℝ) ^ b) * Real.sqrt (B + 1) + tail)) :
    ((2 : ℝ) ^ b * (ε - tail)) ^ 2 - α ^ 2 ≤ α ^ 2 * B := by
  have h2b_pos : (0 : ℝ) < (2 : ℝ) ^ b := by positivity
  have h1 := le_of_mul_le_mul_left hbound (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)
  have h2 : (2 : ℝ) ^ b * (ε - tail) ≤ α * Real.sqrt (B + 1) := by
    have : ε - tail ≤ (α / (2 : ℝ) ^ b) * Real.sqrt (B + 1) := by linarith
    have hmul := mul_le_mul_of_nonneg_left this h2b_pos.le
    have h2b_ne : (2 : ℝ) ^ b ≠ 0 := h2b_pos.ne'
    exact hmul.trans_eq (by field_simp)
  have hsq : ((2 : ℝ) ^ b * (ε - tail)) ^ 2 ≤ α ^ 2 * (B + 1) :=
    (pow_le_pow_left₀ (mul_nonneg h2b_pos.le (sub_nonneg.mpr htail)) h2 2).trans_eq
      (by rw [mul_pow, Real.sq_sqrt (by linarith)])
  linarith

/-! ### Depth-two gate correlation bound and `Ω(ε ^ 2 * n ^ (3 / 2) / log ^ 3 n)` size bounds -/

/-- **Master Depth-Two Gate Correlation Bound for Andreev's Function**: for `0 < m`,
`√(2 ^ b) / 2 ≤ α`, and any depth-two threshold circuit `c` (`c.depth ≤ 2`), the number of inputs
on which `c` agrees with `andreev b m` is bounded in terms of `c.size`. -/
theorem card_eval_eq_andreev_le_of_depth_le_two_size {b m : ℕ} (hm : 0 < m)
    {α : ℝ} (hα : Real.sqrt ((2 : ℝ) ^ b) / 2 ≤ α)
    (c : Circuit signature (2 ^ b + b * m) 1) (hd : c.depth ≤ 2) (o : Fin 1) :
    (#{w : BitString (2 ^ b + b * m) | c.eval interpretation w o = andreev b m w} : ℝ) ≤
      (2 : ℝ) ^ (2 ^ b + b * m) * (1 / 2 + (α / (2 : ℝ) ^ b) *
        Real.sqrt (4 * (1 / (m : ℝ)) * (c.size : ℝ) * Real.sqrt ((2 ^ b + b * m : ℕ) : ℝ) + 1) +
        andreevSimultaneousTail b α) := by
  refine card_eval_eq_andreev_le_of_unforced_mean_le hm hα (by positivity)
    (fun w => c.eval interpretation w o)
    (fun σ w => circuitUnforcedConstCount c o (blockLiveSet (andreevBlockVar b m) σ) w)
    (fun σ w => by
      rw [← univ_image_andreevLiveVar_eq_blockLiveSet]
      exact isDepthTwoWithGates_eval_embedUpdate_const c hd o (andreevLiveVar_injective b m σ) w) ?_
  simpa [Fintype.card_fin] using sum_circuitUnforcedConstCount_blockLiveSet_le c o
    (andreevBlockVar b m) (andreevBlockVar_joint_injective b m)

/-- **Explicit `Ω(ε ^ 2 * n ^ (3 / 2) / log ^ 3 n)` Depth-Two Gate Lower Bound**. -/
theorem size_ge_of_card_eval_eq_andreev_ge {b m : ℕ} (hm : 0 < m)
    {α ε : ℝ} (hα : Real.sqrt ((2 : ℝ) ^ b) / 2 ≤ α)
    (htail : andreevSimultaneousTail b α ≤ ε)
    (c : Circuit signature (2 ^ b + b * m) 1) (hd : c.depth ≤ 2) (o : Fin 1)
    (hcorr : (2 : ℝ) ^ (2 ^ b + b * m) * (1 / 2 + ε) ≤
      (#{w : BitString (2 ^ b + b * m) | c.eval interpretation w o = andreev b m w} : ℝ)) :
    (m : ℝ) * (((2 : ℝ) ^ b * (ε - andreevSimultaneousTail b α)) ^ 2 - α ^ 2) ≤
      4 * α ^ 2 * (c.size : ℝ) * Real.sqrt ((2 ^ b + b * m : ℕ) : ℝ) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hsq := sq_sub_le_of_corr_le (by positivity) htail
    (hcorr.trans (card_eval_eq_andreev_le_of_depth_le_two_size hm hα c hd o))
  have hm_ne : (m : ℝ) ≠ 0 := hm_pos.ne'
  exact (mul_le_mul_of_nonneg_left hsq hm_pos.le).trans_eq (by field_simp)

/-- **Worst-Case Depth-Two Gate Lower Bound for Andreev's Function**. -/
theorem size_ge_of_computes_andreev {b m : ℕ} (hm : 0 < m)
    {α : ℝ} (hα : Real.sqrt ((2 : ℝ) ^ b) / 2 ≤ α)
    (htail : andreevSimultaneousTail b α ≤ 1 / 2)
    (c : Circuit signature (2 ^ b + b * m) 1) (hd : c.depth ≤ 2)
    (hcomp : c.Computes interpretation (single (andreev b m))) :
    (m : ℝ) * (((2 : ℝ) ^ b * (1 / 2 - andreevSimultaneousTail b α)) ^ 2 - α ^ 2) ≤
      4 * α ^ 2 * (c.size : ℝ) * Real.sqrt ((2 ^ b + b * m : ℕ) : ℝ) := by
  refine size_ge_of_card_eval_eq_andreev_ge hm hα htail c hd 0 ?_
  have hall : (univ.filter fun w : BitString (2 ^ b + b * m) =>
      c.eval interpretation w 0 = andreev b m w) = univ :=
    filter_true_of_mem fun w _ => congrFun (hcomp w) 0
  rw [hall, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]; push_cast; linarith

/-! ### Depth-two wire correlation bound and `Ω(ε ^ 2 * n ^ (5 / 2) / log ^ (7 / 2) n)` bounds -/

/-- **Master Depth-Two Wire Correlation Bound for Andreev's Function**: for `0 < m`,
`√(2 ^ b) / 2 ≤ α`, and any depth-two threshold circuit `c` (`c.depth ≤ 2`), the number of inputs
on which `c` agrees with `andreev b m` is bounded in terms of `c.wireCount`. -/
theorem card_eval_eq_andreev_le_of_depth_le_two_wireCount {b m : ℕ} (hm : 0 < m)
    {α : ℝ} (hα : Real.sqrt ((2 : ℝ) ^ b) / 2 ≤ α)
    (c : Circuit signature (2 ^ b + b * m) 1) (hd : c.depth ≤ 2) (o : Fin 1) :
    (#{w : BitString (2 ^ b + b * m) | c.eval interpretation w o = andreev b m w} : ℝ) ≤
      (2 : ℝ) ^ (2 ^ b + b * m) * (1 / 2 + (α / (2 : ℝ) ^ b) *
        Real.sqrt (4 * (c.wireCount : ℝ) * (1 / (m : ℝ)) * Real.sqrt (1 / (m : ℝ)) + 1) +
        andreevSimultaneousTail b α) := by
  refine card_eval_eq_andreev_le_of_unforced_mean_le hm hα (by positivity)
    (fun w => c.eval interpretation w o)
    (fun σ w => circuitUnforcedAtMostOneCount c o (blockLiveSet (andreevBlockVar b m) σ) w)
    (fun σ w => by
      rw [← univ_image_andreevLiveVar_eq_blockLiveSet]
      exact isDepthTwoWithGates_eval_embedUpdate c hd o (andreevLiveVar_injective b m σ) w) ?_
  simpa [Fintype.card_fin] using sum_circuitUnforcedAtMostOneCount_blockLiveSet_le c o
    (andreevBlockVar b m) (andreevBlockVar_joint_injective b m)

/-- **Explicit `Ω(ε ^ 2 * n ^ (5 / 2) / log ^ (7 / 2) n)` Depth-Two Wire Lower Bound**. -/
theorem wireCount_ge_of_card_eval_eq_andreev_ge {b m : ℕ} (hm : 0 < m)
    {α ε : ℝ} (hα : Real.sqrt ((2 : ℝ) ^ b) / 2 ≤ α)
    (htail : andreevSimultaneousTail b α ≤ ε)
    (c : Circuit signature (2 ^ b + b * m) 1) (hd : c.depth ≤ 2) (o : Fin 1)
    (hcorr : (2 : ℝ) ^ (2 ^ b + b * m) * (1 / 2 + ε) ≤
      (#{w : BitString (2 ^ b + b * m) | c.eval interpretation w o = andreev b m w} : ℝ)) :
    ((2 : ℝ) ^ b * (ε - andreevSimultaneousTail b α)) ^ 2 - α ^ 2 ≤
      4 * α ^ 2 * (c.wireCount : ℝ) * (1 / (m : ℝ)) * Real.sqrt (1 / (m : ℝ)) := by
  have hsq := sq_sub_le_of_corr_le (by positivity) htail
    (hcorr.trans (card_eval_eq_andreev_le_of_depth_le_two_wireCount hm hα c hd o))
  linarith

/-- **Worst-Case Depth-Two Wire Lower Bound for Andreev's Function**. -/
theorem wireCount_ge_of_computes_andreev {b m : ℕ} (hm : 0 < m)
    {α : ℝ} (hα : Real.sqrt ((2 : ℝ) ^ b) / 2 ≤ α)
    (htail : andreevSimultaneousTail b α ≤ 1 / 2)
    (c : Circuit signature (2 ^ b + b * m) 1) (hd : c.depth ≤ 2)
    (hcomp : c.Computes interpretation (single (andreev b m))) :
    ((2 : ℝ) ^ b * (1 / 2 - andreevSimultaneousTail b α)) ^ 2 - α ^ 2 ≤
      4 * α ^ 2 * (c.wireCount : ℝ) * (1 / (m : ℝ)) * Real.sqrt (1 / (m : ℝ)) := by
  refine wireCount_ge_of_card_eval_eq_andreev_ge hm hα htail c hd 0 ?_
  have hall : (univ.filter fun w : BitString (2 ^ b + b * m) =>
      c.eval interpretation w 0 = andreev b m w) = univ :=
    filter_true_of_mem fun w _ => congrFun (hcomp w) 0
  rw [hall, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]; push_cast; linarith

end Cslib.Circuits.Boolean.WeightedThreshold
