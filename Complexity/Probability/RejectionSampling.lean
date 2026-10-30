/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Probability.PMF
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Order.Group.Int

/-!
# Rejection sampling of a translated uniform distribution

Draw `y` uniformly from a finite set `B` of an additive group, shift it by `v`, and keep the
result only if it lands in an acceptance set `S`; otherwise output `none` (an *abort*). When
every accepted value `z ∈ S` has its preimage `z - v` in `B`, the output law does not depend on
`v` at all: the sampler accepts with probability exactly `|S| / |B|`, and given acceptance its
value is uniform on `S` (`PMF.shiftReject_apply_some`, `PMF.shiftReject_apply_none`). This is the
exact, finite form of the rejection-sampling lemma behind Lyubashevsky's identification scheme
and signatures ([Lyubashevsky2009], [Lyubashevsky2012]).

The box instance (`PMF.boxReject`) is the variant used in Dilithium ([DucasEtAl2018]):
`y` is uniform in the integer box `[-γ, γ]^ι` and the shift `v` has sup norm at most `β ≤ γ`.
The accepted values are then uniform on `[-(γ - β), γ - β]^ι`, the acceptance probability is
exactly `((2 (γ - β) + 1) / (2 γ + 1)) ^ |ι|`, and the abort probability is at most
`2 |ι| β / (2 γ + 1)`. Unlike the discrete-Gaussian version, every statement is exact.

## Main definitions

* `Cslib.Probability.intBox`: integer vectors with every coordinate in `[-γ, γ]`.
* `Cslib.Probability.PMF.shiftReject`: rejection sampling of a translate of a uniform set.
* `Cslib.Probability.PMF.boxReject`: its instance for integer boxes.

## Main results

* `Cslib.Probability.PMF.shiftReject_apply_some`, `Cslib.Probability.PMF.shiftReject_apply_none`:
  the exact law, whatever the shift.
* `Cslib.Probability.PMF.shiftReject_eq`: the law does not depend on the shift.
* `Cslib.Probability.PMF.boxReject_apply_some`, `Cslib.Probability.PMF.boxReject_apply_none`,
  `Cslib.Probability.PMF.boxReject_eq`: the same for boxes.
* `Cslib.Probability.PMF.boxReject_apply_none_le`: the abort probability is at most
  `2 |ι| β / (2 γ + 1)`.

## References

* [V. Lyubashevsky, *Fiat-Shamir with Aborts: Applications to Lattice and Factoring-Based
  Signatures*][Lyubashevsky2009]
* [V. Lyubashevsky, *Lattice Signatures without Trapdoors*][Lyubashevsky2012]
* [L. Ducas et al., *CRYSTALS-Dilithium: A Lattice-Based Digital Signature
  Scheme*][DucasEtAl2018]
-/

@[expose] public section

namespace Cslib.Probability

open scoped ENNReal

/-! ### Integer boxes -/

section IntBox

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The integer vectors whose coordinates all lie in `[-γ, γ]`, that is, of sup norm at most
`γ`. -/
def intBox (ι : Type*) [Fintype ι] [DecidableEq ι] (γ : ℕ) : Finset (ι → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(γ : ℤ)) γ

/-- A vector lies in the box `[-γ, γ]^ι` when each coordinate has absolute value at most `γ`. -/
@[simp]
theorem mem_intBox {γ : ℕ} {z : ι → ℤ} : z ∈ intBox ι γ ↔ ∀ i, |z i| ≤ γ := by
  simp only [intBox, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

/-- Membership in a box is decided coordinate by coordinate. -/
instance (γ : ℕ) : DecidablePred (· ∈ intBox ι γ) := fun _ =>
  decidable_of_iff _ mem_intBox.symm

/-- Every box contains the zero vector. -/
theorem zero_mem_intBox (γ : ℕ) : (0 : ι → ℤ) ∈ intBox ι γ := by
  simp

/-- Every box is nonempty, so it supports a uniform distribution. -/
theorem intBox_nonempty (γ : ℕ) : (intBox ι γ).Nonempty :=
  ⟨0, zero_mem_intBox γ⟩

/-- The box `[-γ, γ]^ι` has `(2 γ + 1) ^ |ι|` points. -/
theorem card_intBox (γ : ℕ) : (intBox ι γ).card = (2 * γ + 1) ^ Fintype.card ι := by
  rw [intBox, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Int.card_Icc]
  congr 1
  omega

/-- Boxes grow with their radius. -/
theorem intBox_mono {γ γ' : ℕ} (h : γ ≤ γ') : intBox ι γ ⊆ intBox ι γ' := fun z hz => by
  simp only [mem_intBox] at hz ⊢
  exact fun i => (hz i).trans (by exact_mod_cast h)

/-- Removing a vector of sup norm at most `β` from the inner box `[-(γ - β), γ - β]^ι` stays in
the outer box `[-γ, γ]^ι`. -/
theorem sub_mem_intBox {γ β : ℕ} (hβ : β ≤ γ) {z v : ι → ℤ} (hz : z ∈ intBox ι (γ - β))
    (hv : v ∈ intBox ι β) : z - v ∈ intBox ι γ := by
  simp only [mem_intBox, Pi.sub_apply, Nat.cast_sub hβ] at hz hv ⊢
  intro i
  calc |z i - v i| ≤ |z i| + |v i| := abs_sub _ _
    _ ≤ (γ - β) + β := add_le_add (hz i) (hv i)
    _ = γ := sub_add_cancel _ _

end IntBox

namespace PMF

/-! ### Rejection sampling of a translate -/

section Shift

variable {α : Type*} [AddGroup α] [DecidableEq α]

/-- Rejection sampling of a translate: draw `y` uniformly from `B`, and output `some (y + v)`
when `y + v` lies in the acceptance set `S`, and `none` (an abort) otherwise. -/
noncomputable def shiftReject (B S : Finset α) (hB : B.Nonempty) (v : α) : PMF (Option α) :=
  (uniformOfFinset B hB).map fun y => if y + v ∈ S then some (y + v) else none

variable {B S : Finset α} {hB : B.Nonempty} {v : α}

/-- Accepted values lie in the acceptance set. -/
theorem mem_of_some_mem_support_shiftReject {z : α}
    (h : some z ∈ (shiftReject B S hB v).support) : z ∈ S := by
  obtain ⟨y, -, hy⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  split_ifs at hy with hyS
  · exact Option.some_injective _ hy ▸ hyS

/-- **Rejection sampling, accepted values.** If every accepted value `z ∈ S` comes from some
`z - v ∈ B`, then each `z ∈ S` is output with probability `1 / |B|`, whatever the shift. -/
theorem shiftReject_apply_some (hv : ∀ z ∈ S, z - v ∈ B) (z : α) :
    shiftReject B S hB v (some z) = if z ∈ S then (B.card : ℝ≥0∞)⁻¹ else 0 := by
  rw [shiftReject, PMF.map_apply]
  split_ifs with hz
  · rw [tsum_eq_single (z - v)]
    · simp [hz, hv z hz]
    · intro y hy
      have hyz : y + v ≠ z := fun h => hy (eq_sub_of_add_eq h)
      split_ifs <;> simp_all [eq_comm]
  · refine tsum_eq_zero_iff.mpr fun y => ?_
    split_ifs with h₁ h₂ <;> simp_all

/-- **Rejection sampling, aborts.** Under the same hypothesis, the sampler aborts with
probability exactly `1 - |S| / |B|`, whatever the shift. -/
theorem shiftReject_apply_none (hv : ∀ z ∈ S, z - v ∈ B) :
    shiftReject B S hB v none = 1 - (S.card : ℝ≥0∞) / B.card := by
  have hsome : ∑' z, shiftReject B S hB v (some z) = S.card / B.card := by
    simp_rw [shiftReject_apply_some hv]
    rw [tsum_eq_sum (s := S) fun z hz => by simp [hz], Finset.sum_ite_mem, Finset.inter_self,
      Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  have htotal := (shiftReject B S hB v).tsum_coe
  rw [tsum_eq_add_tsum_ite none, ← (Option.some_injective α).tsum_eq] at htotal
  · simp only [reduceCtorEq, ite_false, hsome] at htotal
    exact ENNReal.eq_sub_of_add_eq
      (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simpa using hB.ne_empty)) htotal
  · intro o ho
    cases o with
    | none => simp at ho
    | some z => exact ⟨z, rfl⟩

/-- **Rejection sampling lemma** (exact form). Given acceptance, the output is uniform on `S`:
the probability of `some z` is the acceptance probability `|S| / |B|` times the uniform
probability of `z` in `S`. -/
theorem shiftReject_apply_some_eq_mul (hv : ∀ z ∈ S, z - v ∈ B) (hS : S.Nonempty) (z : α) :
    shiftReject B S hB v (some z) = (S.card : ℝ≥0∞) / B.card * uniformOfFinset S hS z := by
  rw [shiftReject_apply_some hv, uniformOfFinset_apply]
  split_ifs with hz
  · rw [div_eq_mul_inv, mul_comm (S.card : ℝ≥0∞), mul_assoc, ENNReal.mul_inv_cancel
      (by simpa using hS.ne_empty) (ENNReal.natCast_ne_top _), mul_one]
  · rw [mul_zero]

/-- The output law of rejection sampling is the same for all admissible shifts. -/
theorem shiftReject_eq {v' : α} (hv : ∀ z ∈ S, z - v ∈ B) (hv' : ∀ z ∈ S, z - v' ∈ B) :
    shiftReject B S hB v = shiftReject B S hB v' := by
  ext o
  cases o with
  | none => rw [shiftReject_apply_none hv, shiftReject_apply_none hv']
  | some z => rw [shiftReject_apply_some hv, shiftReject_apply_some hv']

end Shift

/-! ### Rejection sampling in integer boxes -/

section Box

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Rejection sampling in integer boxes: draw `y` uniformly from `[-γ, γ]^ι`, and keep `y + v`
only when it lies in `[-(γ - β), γ - β]^ι`. -/
noncomputable def boxReject (ι : Type*) [Fintype ι] [DecidableEq ι] (γ β : ℕ) (v : ι → ℤ) :
    PMF (Option (ι → ℤ)) :=
  shiftReject (intBox ι γ) (intBox ι (γ - β)) (intBox_nonempty γ) v

variable {γ β : ℕ} {v : ι → ℤ}

/-- The ratio of the box sizes is the acceptance probability. -/
private theorem card_div_card_intBox (γ β : ℕ) :
    ((intBox ι (γ - β)).card : ℝ≥0∞) / (intBox ι γ).card =
      ((2 * (γ - β) + 1 : ℕ) / (2 * γ + 1 : ℝ≥0∞)) ^ Fintype.card ι := by
  rw [card_intBox, card_intBox, Nat.cast_pow, Nat.cast_pow, div_eq_mul_inv, div_eq_mul_inv, mul_pow,
    ENNReal.inv_pow]
  push_cast
  rfl

/-- **Box rejection sampling, accepted values.** If `‖v‖∞ ≤ β ≤ γ`, the sampler accepts with
probability `((2 (γ - β) + 1) / (2 γ + 1)) ^ |ι|`, and given acceptance its value is uniform
on `[-(γ - β), γ - β]^ι`, whatever `v`. -/
theorem boxReject_apply_some (hβ : β ≤ γ) (hv : v ∈ intBox ι β) (z : ι → ℤ) :
    boxReject ι γ β v (some z) =
      ((2 * (γ - β) + 1 : ℕ) / (2 * γ + 1 : ℝ≥0∞)) ^ Fintype.card ι *
        uniformOfFinset (intBox ι (γ - β)) (intBox_nonempty _) z := by
  rw [boxReject, shiftReject_apply_some_eq_mul (fun _ hz => sub_mem_intBox hβ hz hv),
    card_div_card_intBox]

/-- **Box rejection sampling, aborts.** If `‖v‖∞ ≤ β ≤ γ`, the sampler aborts with probability
exactly `1 - ((2 (γ - β) + 1) / (2 γ + 1)) ^ |ι|`. -/
theorem boxReject_apply_none (hβ : β ≤ γ) (hv : v ∈ intBox ι β) :
    boxReject ι γ β v none =
      1 - ((2 * (γ - β) + 1 : ℕ) / (2 * γ + 1 : ℝ≥0∞)) ^ Fintype.card ι := by
  rw [boxReject, shiftReject_apply_none (fun _ hz => sub_mem_intBox hβ hz hv),
    card_div_card_intBox]

/-- The law of box rejection sampling is the same for all shifts of sup norm at most `β`. -/
theorem boxReject_eq {v' : ι → ℤ} (hβ : β ≤ γ) (hv : v ∈ intBox ι β) (hv' : v' ∈ intBox ι β) :
    boxReject ι γ β v = boxReject ι γ β v' :=
  shiftReject_eq (fun _ hz => sub_mem_intBox hβ hz hv) (fun _ hz => sub_mem_intBox hβ hz hv')

/-- Accepted values lie in the inner box. -/
theorem mem_intBox_of_some_mem_support_boxReject {z : ι → ℤ}
    (h : some z ∈ (boxReject ι γ β v).support) : z ∈ intBox ι (γ - β) :=
  mem_of_some_mem_support_shiftReject h

/-- **Abort bound.** If `‖v‖∞ ≤ β ≤ γ`, the sampler aborts with probability at most
`2 |ι| β / (2 γ + 1)`, by Bernoulli's inequality. -/
theorem boxReject_apply_none_le (hβ : β ≤ γ) (hv : v ∈ intBox ι β) :
    boxReject ι γ β v none ≤ 2 * Fintype.card ι * β / (2 * γ + 1) := by
  rw [boxReject_apply_none hβ hv, tsub_le_iff_right]
  set m := Fintype.card ι
  have hb : (0 : ℝ) < 2 * γ + 1 := by positivity
  have hreal : (1 : ℝ) ≤ 2 * m * β / (2 * γ + 1) +
      (((2 * (γ - β) + 1 : ℕ) : ℝ) / (2 * γ + 1)) ^ m := by
    have hx : ((2 * (γ - β) + 1 : ℕ) : ℝ) / (2 * γ + 1) = 1 + -(2 * β / (2 * γ + 1)) := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hβ]
      field_simp
      ring
    have hbern := one_add_mul_le_pow (a := -(2 * (β : ℝ) / (2 * γ + 1))) (by
      rw [neg_le_neg_iff, div_le_iff₀ hb]
      linarith [(Nat.cast_le (α := ℝ)).mpr hβ]) m
    rw [hx]
    have : (m : ℝ) * -(2 * β / (2 * γ + 1)) = -(2 * m * β / (2 * γ + 1)) := by ring
    linarith
  have hlhs : ENNReal.ofReal (2 * m * β / (2 * γ + 1) +
      (((2 * (γ - β) + 1 : ℕ) : ℝ) / (2 * γ + 1)) ^ m) =
      2 * m * β / (2 * γ + 1) + ((2 * (γ - β) + 1 : ℕ) / (2 * γ + 1 : ℝ≥0∞)) ^ m := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_div_of_pos hb,
      ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_div_of_pos hb]
    norm_cast
  rw [← hlhs, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal hreal

end Box

end PMF

end Cslib.Probability
