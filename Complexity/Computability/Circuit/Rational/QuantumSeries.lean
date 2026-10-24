/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Rational.PaddedRank

/-!
# Hahn series with coefficients on monomial lines

Given units `B g` of a `K`-algebra `R`, indexed by an ordered group `Γ` and multiplying like
monomials up to scalars, the Hahn series over `R` whose `g`-th coefficient lies on the line
`K ∙ B g` form a subring. Every nonzero element of this subring has a unit leading coefficient,
and a noncommutative geometric series argument inverts it inside the subring, so the subring is
a division ring. No commutativity of `R` is assumed; `HahnGeometric` adapts Mathlib's
`HahnSeries.SummableFamily.powers`, which requires a commutative coefficient ring.

## Main definitions

* `QuantumSeries.line`: the coefficient line `K ∙ B g`.
* `QuantumSeries.coefficientRing`: the subring of Hahn series with coefficients on these lines.
* `HahnGeometric.geometricPowers`: the summable family of powers of a series of positive order.
* `QuantumSeries.divisionRing`: the division ring structure on `coefficientRing`.

## Main results

* `HahnGeometric.one_sub_self_mul_hsum_geometricPowers`: `(1 - x) * ∑ xⁿ = 1`.
* `HahnGeometric.normalized_right_inverse`: a right inverse of a series with unit leading
  coefficient.
* `QuantumSeries.coefficientRing_isUnit_or_eq_zero`: every element of `coefficientRing` is a
  unit or zero.

## References

* Adapted from OpenAI's formalization [OpenAI2026RationalHitting] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Computability/RationalHitting/QuantumSeries.lean), via the complexitylib port
  [Schlesinger2026RationalHitting] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
* The geometric series construction `HahnGeometric` adapts Mathlib's
  `HahnSeries.SummableFamily.powers` (`Mathlib/RingTheory/HahnSeries/Summable.lean`,
  Copyright (c) 2021 Aaron Anderson, Apache 2.0) from commutative to arbitrary coefficient rings.
-/

@[expose] public section

namespace Cslib.Circuits

namespace Rational.QuantumSeries
open HahnSeries Module
open scoped BigOperators
noncomputable section
variable {Γ K R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field K] [Ring R] [Algebra K R] [Nontrivial R]

/-- Each exponent has the one-dimensional coefficient line of its ordered
quantum monomial. Lexicographic leading terms do not require a domain
matrix coefficient ring. -/
def line (B : Γ → Rˣ) (g : Γ) : Submodule K R := K ∙ (B g : R)

omit [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Nontrivial R] in
private lemma line_mul (B : Γ → Rˣ)
    (hB : ∀ (g h : Γ), ∃ c : K, (B g : R) * (B h : R) = c • (B (g + h) : R))
    {g h : Γ} {x y : R} (hx : x ∈ line (K := K) B g) (hy : y ∈ line (K := K) B h) :
    x * y ∈ line (K := K) B (g + h) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
  obtain ⟨c, hc⟩ := hB g h
  rw [smul_mul_assoc, mul_smul_comm, hc, smul_smul, smul_smul]
  exact Submodule.mem_span_singleton.mpr ⟨a * b * c, rfl⟩

omit [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Nontrivial R] in
private lemma line_isUnit (B : Γ → Rˣ) {g : Γ} {x : R} (hx : x ∈ line (K := K) B g) (hne : x ≠ 0) :
    IsUnit x := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  have ha : a ≠ 0 := by intro h; simp [h] at hne
  rw [Algebra.smul_def]
  exact ((isUnit_iff_ne_zero.mpr ha).map (algebraMap K R)).mul (B g).isUnit

/-- The Hahn-series subring with each coefficient on its prescribed monomial line. -/
def coefficientRing (B : Γ → Rˣ) (h0 : B 0 = 1)
    (hB : ∀ g h, ∃ c : K, (B g : R) * (B h : R) = c • (B (g + h) : R)) :
    Subring (HahnSeries Γ R) where
  carrier := {x | ∀ g, x.coeff g ∈ line (K := K) B g}
  zero_mem' := fun g => (line (K := K) B g).zero_mem
  one_mem' := by
    intro g
    by_cases hg : g = 0
    · subst g
      simp only [HahnSeries.coeff_one, line, h0, Units.val_one]
      exact Submodule.subset_span (Set.mem_singleton _)
    · simp [HahnSeries.coeff_one, hg]
  add_mem' := by
    intro x y hx hy g
    exact (line (K := K) B g).add_mem (hx g) (hy g)
  neg_mem' := by
    intro x hx g
    exact (line (K := K) B g).neg_mem (hx g)
  mul_mem' := by
    intro x y hx hy g
    rw [HahnSeries.coeff_mul]
    apply (line (K := K) B g).sum_mem
    intro ij hij
    have heq := (Finset.mem_antidiagonal.mp hij).2.2
    rw [← heq]
    exact line_mul B hB (hx ij.1) (hy ij.2)

private lemma coefficientRing_noZeroDivisors (B : Γ → Rˣ) (h0 : B 0 = 1)
    (hB : ∀ g h, ∃ c : K, (B g : R) * (B h : R) = c • (B (g + h) : R)) :
    NoZeroDivisors (coefficientRing B h0 hB) := by
  constructor
  intro x y hxy
  by_contra hn
  have hx : x ≠ 0 := fun hx => hn (Or.inl hx)
  have hy : y ≠ 0 := fun hy => hn (Or.inr hy)
  have hx' : (x : HahnSeries Γ R) ≠ 0 := by exact_mod_cast hx
  have hy' : (y : HahnSeries Γ R) ≠ 0 := by exact_mod_cast hy
  have hxu : IsUnit (x : HahnSeries Γ R).leadingCoeff :=
    line_isUnit B (by rw [HahnSeries.leadingCoeff_eq]; exact x.property _)
      (HahnSeries.leadingCoeff_ne_zero.mpr hx')
  have hyu : IsUnit (y : HahnSeries Γ R).leadingCoeff :=
    line_isUnit B (by rw [HahnSeries.leadingCoeff_eq]; exact y.property _)
      (HahnSeries.leadingCoeff_ne_zero.mpr hy')
  have hh := congrArg (fun z : coefficientRing B h0 hB =>
    (z : HahnSeries Γ R).coeff ((x : HahnSeries Γ R).order + (y : HahnSeries Γ R).order)) hxy
  change ((x : HahnSeries Γ R) * (y : HahnSeries Γ R)).coeff _ = 0 at hh
  rw [HahnSeries.coeff_mul_order_add_order] at hh
  exact (hxu.mul hyu).ne_zero hh

end
end Rational.QuantumSeries

/-! ### Geometric series of Hahn series over a noncommutative ring

This section adapts Mathlib's `HahnSeries.SummableFamily.powers` and its lemmas
(`Mathlib/RingTheory/HahnSeries/Summable.lean`, by Aaron Anderson), whose coefficient ring must be
commutative, to an arbitrary ring of coefficients. -/
namespace Rational.HahnGeometric
open HahnSeries HahnSeries.SummableFamily Finset Function
noncomputable section
variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Ring R]

private theorem power_finite_co_support {x : R⟦Γ⟧} (hx : 0 < x.orderTop) (g : Γ) :
    Set.Finite {a | ((fun n ↦ x ^ n) a).coeff g ≠ 0} := by
  have hpwo : Set.IsPWO (⋃ n, support (x ^ n)) :=
    isPWO_iUnion_support_powers (zero_le_orderTop_iff.mp <| le_of_lt hx)
  by_cases h0 : x = 0; · exact h0 ▸ Set.Finite.subset (Set.finite_singleton 0) (co_support_zero g)
  by_cases hg : g ∈ ⋃ n : ℕ, { g | (x ^ n).coeff g ≠ 0 }
  swap; · exact Set.finite_empty.subset fun n hn => hg (Set.mem_iUnion.2 ⟨n, hn⟩)
  apply hpwo.isWF.induction hg
  intro y ys hy
  refine ((((antidiagonal x.isPWO_support hpwo y).finite_toSet.biUnion
    fun ij hij => hy ij.snd (Finset.mem_antidiagonal.1 (mem_coe.1 hij)).2.1 ?_).image
      Nat.succ).union
      (Set.finite_singleton 0)).subset ?_
  · obtain ⟨hi, _, rfl⟩ := Finset.mem_antidiagonal.1 (mem_coe.1 hij)
    exact lt_add_of_pos_left ij.2 <| lt_of_lt_of_le ((zero_lt_orderTop_iff h0).mp hx) <|
      order_le_of_coeff_ne_zero <| Function.mem_support.mp hi
  · rintro (_ | n) hn
    · exact Set.mem_union_right _ (Set.mem_singleton 0)
    · obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset hn
      refine Set.mem_union_left _ ⟨n, Set.mem_iUnion.2 ⟨⟨j, i⟩, Set.mem_iUnion.2 ⟨?_, hi⟩⟩, rfl⟩
      simp only [mem_coe, Finset.mem_antidiagonal, HahnSeries.mem_support, ne_eq, Set.mem_iUnion]
      exact ⟨hj, ⟨n, hi⟩, add_comm j i⟩

/-- The summable family of powers of a Hahn series `x`. If `x` does not have positive
`orderTop`, this returns the junk value obtained by pretending `x = 0`. -/
@[simps]
def geometricPowers (x : R⟦Γ⟧) : SummableFamily Γ R ℕ where
  toFun n := (if 0 < x.orderTop then x else 0) ^ n
  isPWO_iUnion_support' := by
    by_cases h : 0 < x.orderTop
    · simp only [h, ↓reduceIte]
      exact isPWO_iUnion_support_powers (zero_le_orderTop_iff.mp <| le_of_lt h)
    · simp only [h, ↓reduceIte]
      apply isPWO_iUnion_support_powers
      rw [order_zero]
  finite_co_support' g := by
    by_cases h : 0 < x.orderTop
    · simp only [h, ↓reduceIte]
      exact power_finite_co_support h g
    · simp only [h, ↓reduceIte]
      exact power_finite_co_support (orderTop_zero (R := R) (Γ := Γ) ▸ WithTop.top_pos) g

theorem geometricPowers_of_orderTop_pos {x : R⟦Γ⟧} (hx : 0 < x.orderTop) (n : ℕ) :
    geometricPowers x n = x ^ n := by
  simp [hx]

theorem geometricPowers_of_not_orderTop_pos {x : R⟦Γ⟧} (hx : ¬ 0 < x.orderTop) :
    geometricPowers x = .single 0 1 := by
  ext a
  obtain rfl | ha := eq_or_ne a 0 <;> simp [geometricPowers, *]

@[simp]
theorem geometricPowers_zero : geometricPowers (0 : R⟦Γ⟧) = .single 0 1 := by
  ext n
  rw [geometricPowers_of_orderTop_pos (by simp)]
  obtain rfl | ha := eq_or_ne n 0 <;> simp [*]

variable {x : R⟦Γ⟧} (hx : 0 < x.orderTop)

include hx in
@[simp]
theorem coe_geometricPowers : ⇑(geometricPowers x) = HPow.hPow x := by
  ext1 n
  simp [hx]

include hx in
private theorem embDomain_succ_smul_geometricPowers :
    (x • geometricPowers x).embDomain ⟨Nat.succ, Nat.succ_injective⟩ =
      geometricPowers x - SummableFamily.ofFinsupp (Finsupp.single 0 1) := by
  apply SummableFamily.ext
  rintro (_ | n)
  · simp [hx]
  · -- `smul_eq_mul` is excluded: it would rewrite the `HahnModule` action as multiplication of
    -- `HahnSeries`, mixing up the two types.
    simp [embDomain_apply, of_symm_smul_of_eq_mul, geometricPowers_of_orderTop_pos hx, pow_succ',
      -smul_eq_mul]

include hx in
theorem one_sub_self_mul_hsum_geometricPowers : (1 - x) * (geometricPowers x).hsum = 1 := by
  rw [← hsum_smul, sub_smul 1 x (geometricPowers x), one_smul, hsum_sub, ←
    hsum_embDomain (x • geometricPowers x) ⟨Nat.succ, Nat.succ_injective⟩,
      embDomain_succ_smul_geometricPowers hx]
  simp

/-- A unit leading coefficient permits the usual normalization, without any
commutativity assumption on the coefficient ring. -/
lemma normalized_pos (x : HahnSeries Γ R) (u : Rˣ)
    (hu : x.leadingCoeff = (u : R)) :
    0 < (1 - HahnSeries.single (-x.order) (↑u⁻¹ : R) * x).orderTop := by
  let y := x - HahnSeries.single x.order x.leadingCoeff
  have hi : (↑u⁻¹ : R) * x.leadingCoeff = 1 := by rw [hu]; simp
  by_cases hy : y = 0
  · have hx : x = HahnSeries.single x.order x.leadingCoeff := sub_eq_zero.mp hy
    have hh : HahnSeries.single (-x.order) (↑u⁻¹ : R) * x = 1 := by
      calc
        _ = HahnSeries.single (-x.order) (↑u⁻¹ : R) * HahnSeries.single x.order x.leadingCoeff :=
          congrArg (fun z => HahnSeries.single (-x.order) (↑u⁻¹ : R) * z) hx
        _ = 1 := by rw [single_mul_single, hi, neg_add_cancel, single_zero_one]
    simp [hh]
  · have hy' : 0 < (HahnSeries.single (-x.order) (↑u⁻¹ : R) * y).order := by
      rw [order_single_mul_of_isRegular (u⁻¹).isUnit.isRegular hy]
      have : x.order < y.order :=
        order_lt_order_of_eq_add_single (sub_add_cancel x _).symm hy
      simpa using add_lt_add_left this (-x.order)
    have heq : 1 - HahnSeries.single (-x.order) (↑u⁻¹ : R) * x =
        -(HahnSeries.single (-x.order) (↑u⁻¹ : R) * y) := by
      calc
        _ = 1 - HahnSeries.single (-x.order) (↑u⁻¹ : R) *
            (y + HahnSeries.single x.order x.leadingCoeff) :=
          congrArg (fun z => 1 - HahnSeries.single (-x.order) (↑u⁻¹ : R) * z)
            (sub_add_cancel x _).symm
        _ = _ := by rw [mul_add, single_mul_single, hi, neg_add_cancel, single_zero_one]; abel
    rw [heq, orderTop_neg]
    exact zero_lt_orderTop_of_order hy'

lemma normalized_right_inverse (x : HahnSeries Γ R) (u : Rˣ)
    (hu : x.leadingCoeff = (u : R)) :
    x * ((geometricPowers (1 - HahnSeries.single (-x.order) (↑u⁻¹ : R) * x)).hsum *
      HahnSeries.single (-x.order) (↑u⁻¹ : R)) = 1 := by
  let v : HahnSeries Γ R := HahnSeries.single (-x.order) (↑u⁻¹ : R)
  let v' : HahnSeries Γ R := HahnSeries.single x.order (u : R)
  have hv : v' * v = 1 := by simp [v', v, single_mul_single]
  have hh := one_sub_self_mul_hsum_geometricPowers (normalized_pos x u hu)
  rw [sub_sub_cancel] at hh
  change (v * x) * (geometricPowers (1 - v * x)).hsum = 1 at hh
  calc
    _ = (v' * ((v * x) * (geometricPowers (1 - v * x)).hsum)) * v := by
      simp only [← mul_assoc, hv, one_mul]
      rfl
    _ = 1 := by rw [hh, mul_one, hv]

end
end Rational.HahnGeometric

namespace Rational.QuantumSeries
open HahnSeries HahnSeries.SummableFamily
open Rational.HahnGeometric
open scoped BigOperators
noncomputable section
variable {Γ K R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field K] [Ring R] [Algebra K R] [Nontrivial R]
variable (B : Γ → Rˣ) (h0 : B 0 = 1)
  (hB : ∀ g h, ∃ c : K, (B g : R) * (B h : R) = c • (B (g + h) : R))

omit [LinearOrder Γ] [IsOrderedAddMonoid Γ] in
include h0 hB in
private lemma line_inv_unit {g : Γ} (u : Rˣ) (hu : ↑u ∈ line (K := K) B g) :
    ↑u⁻¹ ∈ line (K := K) B (-g) := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hu
  obtain ⟨c, hc⟩ := hB g (-g)
  rw [add_neg_cancel, h0, Units.val_one] at hc
  have ha0 : a ≠ 0 := by intro h; simp only [h, zero_smul] at ha; exact u.ne_zero ha.symm
  have hc0 : c ≠ 0 := by
    intro h
    simp only [h, zero_smul] at hc
    exact ((B g).isUnit.mul (B (-g)).isUnit).ne_zero hc
  have hy : (u : R) * ((a * c)⁻¹ • (B (-g) : R)) = 1 := by
    rw [← ha, smul_mul_assoc, mul_smul_comm, hc, smul_smul, smul_smul]
    rw [show a * (a * c)⁻¹ * c = 1 by field_simp, one_smul]
  have heq : (↑u⁻¹ : R) = (a * c)⁻¹ • (B (-g) : R) := by
    calc
      _ = (↑u⁻¹ : R) * 1 := (mul_one _).symm
      _ = (↑u⁻¹ : R) * ((u : R) * ((a * c)⁻¹ • (B (-g) : R))) := by rw [hy]
      _ = _ := by rw [← mul_assoc]; simp
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

omit [Nontrivial R] in
lemma single_mem {g : Γ} {r : R} (hr : r ∈ line (K := K) B g) :
    HahnSeries.single g r ∈ coefficientRing B h0 hB := by
  intro a
  by_cases h : g = a
  · subst a; simpa using hr
  · simp [Ne.symm h]

omit [Nontrivial R] in
lemma hsum_mem {α : Type*} (x : SummableFamily Γ R α)
    (hx : ∀ i, x i ∈ coefficientRing B h0 hB) :
    x.hsum ∈ coefficientRing B h0 hB := by
  intro g
  rw [coeff_hsum_eq_sum]
  apply Submodule.sum_mem
  intro i hi
  exact hx i g

lemma inverse_candidate_mem (x : HahnSeries Γ R)
    (hx : x ∈ coefficientRing B h0 hB) (u : Rˣ) (hu : x.leadingCoeff = (u : R)) :
    (geometricPowers (1 - HahnSeries.single (-x.order) (↑u⁻¹ : R) * x)).hsum *
      HahnSeries.single (-x.order) (↑u⁻¹ : R) ∈ coefficientRing B h0 hB := by
  have hline : x.leadingCoeff ∈ line (K := K) B x.order := by
    rw [leadingCoeff_eq]; exact hx _
  let v : HahnSeries Γ R := HahnSeries.single (-x.order) (↑u⁻¹ : R)
  have hv : v ∈ coefficientRing B h0 hB :=
    single_mem B h0 hB (line_inv_unit B h0 hB u (hu ▸ hline))
  let z : HahnSeries Γ R := 1 - v * x
  have hz : z ∈ coefficientRing B h0 hB :=
    (coefficientRing B h0 hB).sub_mem (coefficientRing B h0 hB).one_mem
      ((coefficientRing B h0 hB).mul_mem hv hx)
  have hz0 : 0 < z.orderTop := normalized_pos x u hu
  have hpow : ∀ i, geometricPowers z i ∈ coefficientRing B h0 hB := by
    intro i
    rw [geometricPowers_of_orderTop_pos hz0]
    exact (coefficientRing B h0 hB).pow_mem hz i
  exact (coefficientRing B h0 hB).mul_mem (hsum_mem B h0 hB _ hpow) hv

private lemma inverse_exists (x : coefficientRing B h0 hB) (hx : x ≠ 0) :
    ∃ y : coefficientRing B h0 hB, x * y = 1 := by
  have hx' : (x : HahnSeries Γ R) ≠ 0 := by
    intro h; apply hx; exact Subtype.ext h
  have hline : (x : HahnSeries Γ R).leadingCoeff ∈
      line (K := K) B (x : HahnSeries Γ R).order := by
    rw [leadingCoeff_eq]; exact x.property _
  obtain ⟨u, hu⟩ := line_isUnit (K := K) B hline (leadingCoeff_ne_zero.mpr hx')
  let y : HahnSeries Γ R := (geometricPowers
    (1 - HahnSeries.single (-(x : HahnSeries Γ R).order) (↑u⁻¹ : R) * (x : HahnSeries Γ R))).hsum *
      HahnSeries.single (-(x : HahnSeries Γ R).order) (↑u⁻¹ : R)
  have hy : y ∈ coefficientRing B h0 hB :=
    inverse_candidate_mem B h0 hB x x.property u hu.symm
  have heq := normalized_right_inverse (x : HahnSeries Γ R) u hu.symm
  refine ⟨⟨y, hy⟩, ?_⟩
  exact Subtype.ext heq

lemma coefficientRing_isUnit_or_eq_zero (x : coefficientRing B h0 hB) :
    IsUnit x ∨ x = 0 := by
  by_cases hx : x = 0
  · exact Or.inr hx
  left
  let := coefficientRing_noZeroDivisors B h0 hB
  obtain ⟨y, hy⟩ := inverse_exists B h0 hB x hx
  have hh : y * x = 1 := by
    have hz : x * (y * x - 1) = 0 := by rw [mul_sub, ← mul_assoc, hy, one_mul, mul_one, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hx)
  exact ⟨⟨x, y, hy, hh⟩, rfl⟩

/-- An actual division ring containing all ordered quantum-monomial series;
no finite-dimensional-domain or external division-algebra theorem is assumed. -/
abbrev divisionRing : DivisionRing (coefficientRing B h0 hB) :=
  DivisionRing.ofIsUnitOrEqZero (coefficientRing_isUnit_or_eq_zero B h0 hB)

end
end Rational.QuantumSeries

end Cslib.Circuits
