/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.LatticeReduction.Reduced

/-!
# Babai's nearest-plane bound

Let `b : Fin n → E` be a family in a real inner product space with Gram–Schmidt vectors
`b*ⱼ = gramSchmidt ℝ b j`, and let `x ∈ E` be a target. Babai's nearest-plane algorithm
([Babai1986]; [Regev2004], Lecture 3, §1) outputs a point `y` of the integer span of `b` whose
difference with the target has every Gram–Schmidt coordinate in `[-1/2, 1/2]`:
`|⟪b*ⱼ, x - y⟫| ≤ ‖b*ⱼ‖² / 2` for every `j`
(`Cslib.Algorithms.LatticeReduction.IsNearestPlane b x y`).

If `b : Fin (n + 1) → E` is `δ`-reduced with `1/4 < δ ≤ 1`, every such `y` satisfies
`‖x - y‖² ≤ (∑_{i ≤ n} αⁱ) ‖x - v‖²` for every `v` in the integer span of `b`, where
`α = 4/(4δ - 1)` (`Cslib.Algorithms.LatticeReduction.IsNearestPlane.norm_sq_le`). For `δ = 3/4`,
`∑_{i ≤ n} 2ⁱ < 2ⁿ⁺¹`, so `‖x - y‖ ≤ 2^{d/2} ‖x - v‖` for `d` vectors
(`Cslib.Algorithms.LatticeReduction.IsNearestPlane.norm_le_sqrt_two_pow_mul`), which is
Lemma 6 of [Regev2004], Lecture 3: `y` solves the closest vector problem within a factor `2^{d/2}`.
[Regev2004] attributes the sharper factor `2 (2/√3)ᵈ` to [Babai1986]; it is not formalized here.

The proof is not the inductive one of [Regev2004]. Write `T_j(z) = ⟪b*ⱼ, z⟫² / ‖b*ⱼ‖²`, so that
`‖z‖² = ‖z - Pz‖² + ∑ⱼ T_j(z)` with `P` the orthogonal projection onto the span of `b`
(`Cslib.Algorithms.LatticeReduction.norm_sq_eq_norm_sq_sub_add_sum`). The residual `z - Pz` is
unchanged by lattice translations, so it suffices to compare the sums. If `k` is the largest index
where the coefficients of `y` and `v` differ, then `T_j(x - y) = T_j(x - v)` for `j > k`,
`T_k(x - v) ≥ ‖b*ₖ‖² / 4`, and `T_j(x - y) ≤ ‖b*ⱼ‖² / 4 ≤ αᵏ⁻ʲ ‖b*ₖ‖² / 4` for `j ≤ k`.

The statements hold in any real inner product space and do not assume that `b` is linearly
independent.

## Main definitions

* `Cslib.Algorithms.LatticeReduction.gramSchmidtProj`: the orthogonal projection onto the span of
  `b`, written in the Gram–Schmidt basis.
* `Cslib.Algorithms.LatticeReduction.IsNearestPlane`: the output condition of the nearest-plane
  algorithm.

## Main results

* `Cslib.Algorithms.LatticeReduction.IsNearestPlane.norm_sq_le`: the approximation bound for a
  general `δ ∈ (1/4, 1]`.
* `Cslib.Algorithms.LatticeReduction.IsNearestPlane.norm_sq_le_two_pow_mul`,
  `Cslib.Algorithms.LatticeReduction.IsNearestPlane.norm_le_sqrt_two_pow_mul`: the case
  `δ = 3/4`, `‖x - y‖ ≤ 2^{n/2} ‖x - v‖` for `n` vectors.

## References

* [L. Babai, *On Lovász' lattice reduction and the nearest lattice point problem*][Babai1986]
* [O. Regev, *Lattices in Computer Science*, lecture notes][Regev2004]
-/

public section

namespace Cslib.Algorithms.LatticeReduction

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- The component of `z` along the span of `b`, written in the Gram–Schmidt basis:
`∑ⱼ (⟪b*ⱼ, z⟫ / ‖b*ⱼ‖²) b*ⱼ`. -/
noncomputable def gramSchmidtProj (b : Fin n → E) (z : E) : E :=
  ∑ j, (inner ℝ (gramSchmidt ℝ b j) z / ‖gramSchmidt ℝ b j‖ ^ 2) • gramSchmidt ℝ b j

theorem inner_gramSchmidt_gramSchmidtProj (b : Fin n → E) (z : E) (i : Fin n) :
    inner ℝ (gramSchmidt ℝ b i) (gramSchmidtProj b z) = inner ℝ (gramSchmidt ℝ b i) z := by
  rw [gramSchmidtProj, inner_sum, Finset.sum_eq_single i]
  · rw [inner_smul_right, real_inner_self_eq_norm_sq]
    rcases eq_or_ne (gramSchmidt ℝ b i) 0 with h | h
    · simp [h]
    · field_simp [norm_ne_zero_iff.2 h]
  · intro j _ hji
    rw [inner_smul_right, gramSchmidt_orthogonal ℝ b hji.symm, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem inner_gramSchmidtProj_gramSchmidt (b : Fin n → E) (z : E) (i : Fin n) :
    inner ℝ (gramSchmidtProj b z) (gramSchmidt ℝ b i) = inner ℝ z (gramSchmidt ℝ b i) := by
  rw [real_inner_comm, inner_gramSchmidt_gramSchmidtProj, real_inner_comm]

/-- Pythagoras for the decomposition `z = (z - Pz) + Pz`:
`‖z‖² = ‖z - Pz‖² + ∑ⱼ ⟪b*ⱼ, z⟫² / ‖b*ⱼ‖²`. -/
theorem norm_sq_eq_norm_sq_sub_add_sum (b : Fin n → E) (z : E) :
    ‖z‖ ^ 2 = ‖z - gramSchmidtProj b z‖ ^ 2 +
      ∑ j, inner ℝ (gramSchmidt ℝ b j) z ^ 2 / ‖gramSchmidt ℝ b j‖ ^ 2 := by
  have hP : inner ℝ (z - gramSchmidtProj b z) (gramSchmidtProj b z) = 0 := by
    conv_lhs => arg 3; rw [gramSchmidtProj]
    rw [inner_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [inner_smul_right, inner_sub_left, inner_gramSchmidtProj_gramSchmidt, sub_self, mul_zero]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hP
  rw [sub_add_cancel] at h
  have hP2 : ‖gramSchmidtProj b z‖ * ‖gramSchmidtProj b z‖ =
      ∑ j, inner ℝ (gramSchmidt ℝ b j) z ^ 2 / ‖gramSchmidt ℝ b j‖ ^ 2 := by
    rw [← sq, ← real_inner_self_eq_norm_sq]
    conv_lhs => arg 2; rw [gramSchmidtProj]
    rw [sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_left, inner_gramSchmidt_gramSchmidtProj]
    ring
  rw [sq, sq, h, hP2]

/-- The projection fixes the integer span of `b`. -/
theorem gramSchmidtProj_eq_self {b : Fin n → E} {w : E}
    (hw : w ∈ Submodule.span ℤ (Set.range b)) : gramSchmidtProj b w = w := by
  have hw' : w ∈ Submodule.span ℝ (Set.range (gramSchmidt ℝ b)) := by
    rw [span_gramSchmidt ℝ b]
    exact Submodule.span_le_restrictScalars ℤ ℝ _ hw
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hw'
  rw [gramSchmidtProj]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases eq_or_ne (gramSchmidt ℝ b j) 0 with h | h
  · simp [h]
  congr 1
  rw [inner_sum, Finset.sum_eq_single j]
  · rw [inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp [norm_ne_zero_iff.2 h]
  · intro i _ hij
    rw [inner_smul_right, gramSchmidt_orthogonal ℝ b hij.symm, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- Lattice translations do not change the residual `z - Pz`. -/
theorem sub_gramSchmidtProj_add {b : Fin n → E} (z : E) {w : E}
    (hw : w ∈ Submodule.span ℤ (Set.range b)) :
    z + w - gramSchmidtProj b (z + w) = z - gramSchmidtProj b z := by
  have hadd : gramSchmidtProj b (z + w) = gramSchmidtProj b z + gramSchmidtProj b w := by
    simp only [gramSchmidtProj, inner_add_right, add_div, add_smul, Finset.sum_add_distrib]
  rw [hadd, gramSchmidtProj_eq_self hw]
  abel

/-- `⟪b*ⱼ, ∑ᵢ eᵢ bᵢ⟫ = eⱼ ‖b*ⱼ‖²` for integer coefficients that vanish above `j`. -/
theorem inner_gramSchmidt_sum_zsmul (b : Fin n → E) (e : Fin n → ℤ) {j : Fin n}
    (he : ∀ i, j < i → e i = 0) :
    inner ℝ (gramSchmidt ℝ b j) (∑ i, e i • b i) = e j * ‖gramSchmidt ℝ b j‖ ^ 2 := by
  rw [inner_sum, Finset.sum_eq_single j]
  · rw [← Int.cast_smul_eq_zsmul ℝ, inner_smul_right, inner_gramSchmidt_self_right]
    rfl
  · intro i _ hij
    rw [← Int.cast_smul_eq_zsmul ℝ, inner_smul_right]
    rcases lt_or_gt_of_ne hij with h | h
    · rw [gramSchmidt_inv_triangular ℝ b h, mul_zero]
    · rw [he i h, Int.cast_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- The output condition of Babai's nearest-plane algorithm ([Babai1986]; [Regev2004],
Lecture 3, §1): `y` lies in the integer span of `b`, and every Gram–Schmidt coordinate of
`x - y` lies in `[-1/2, 1/2]`, stated without division as `|⟪b*ⱼ, x - y⟫| ≤ ‖b*ⱼ‖² / 2`. -/
structure IsNearestPlane (b : Fin n → E) (x y : E) : Prop where
  /-- The output is a lattice point. -/
  mem_span : y ∈ Submodule.span ℤ (Set.range b)
  /-- Every Gram–Schmidt coordinate of `x - y` lies in `[-1/2, 1/2]`. -/
  abs_inner_le : ∀ j, |inner ℝ (gramSchmidt ℝ b j) (x - y)| ≤ ‖gramSchmidt ℝ b j‖ ^ 2 / 2

/-- Babai's nearest-plane bound for a `δ`-reduced family `b : Fin (n + 1) → E` with
`1/4 < δ ≤ 1`: if `y` satisfies the nearest-plane condition for `x`, then
`‖x - y‖² ≤ (∑_{i ≤ n} αⁱ) ‖x - v‖²` for every `v` in the integer span of `b`, where
`α = 4/(4δ - 1)`. This is the general-`δ` form of [Regev2004], Lecture 3, Lemma 6. -/
theorem IsNearestPlane.norm_sq_le {δ : ℝ} {b : Fin (n + 1) → E} (hb : IsReduced δ b)
    (hδ : 1 / 4 < δ) (hδ1 : δ ≤ 1) {x y : E} (hy : IsNearestPlane b x y) {v : E}
    (hv : v ∈ Submodule.span ℤ (Set.range b)) :
    ‖x - y‖ ^ 2 ≤ (∑ i ∈ Finset.range (n + 1), (4 / (4 * δ - 1)) ^ i) * ‖x - v‖ ^ 2 := by
  classical
  set α : ℝ := 4 / (4 * δ - 1) with hα
  set S : ℝ := ∑ i ∈ Finset.range (n + 1), α ^ i with hS
  have hα1 : 1 ≤ α := by rw [hα, le_div_iff₀ (by linarith)]; linarith
  have hα0 : 0 ≤ α := by linarith
  have hS1 : 1 ≤ S := by
    rw [hS, Finset.sum_range_succ']
    simp only [pow_zero]
    have : 0 ≤ ∑ i ∈ Finset.range n, α ^ (i + 1) :=
      Finset.sum_nonneg fun i _ => pow_nonneg hα0 _
    linarith
  have hSfin : ∑ j : Fin (n + 1), α ^ (n - (j : ℕ)) = S := by
    rw [Fin.sum_univ_eq_sum_range (fun j => α ^ (n - j)) (n + 1), hS,
      ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    congr 1
    omega
  set g := gramSchmidt ℝ b with hg
  let T : E → Fin (n + 1) → ℝ := fun z j => inner ℝ (g j) z ^ 2 / ‖g j‖ ^ 2
  have hT0 : ∀ z j, 0 ≤ T z j := fun z j => div_nonneg (sq_nonneg _) (sq_nonneg _)
  set d := x - y with hd
  set d' := x - v with hd'
  -- the residuals agree
  have hyv : y - v ∈ Submodule.span ℤ (Set.range b) := sub_mem hy.mem_span hv
  have hdd' : d' = d + (y - v) := by rw [hd, hd']; abel
  have hres : d' - gramSchmidtProj b d' = d - gramSchmidtProj b d := by
    rw [hdd']; exact sub_gramSchmidtProj_add d hyv
  have hpyd := norm_sq_eq_norm_sq_sub_add_sum b d
  have hpyd' := norm_sq_eq_norm_sq_sub_add_sum b d'
  rw [hres] at hpyd'
  set R := ‖d - gramSchmidtProj b d‖ ^ 2 with hR
  have hR0 : 0 ≤ R := sq_nonneg _
  -- it suffices to compare the sums
  suffices hsum : ∑ j, T d j ≤ S * ∑ j, T d' j by
    have h1 : ‖d‖ ^ 2 = R + ∑ j, T d j := hpyd
    have h2 : ‖d'‖ ^ 2 = R + ∑ j, T d' j := hpyd'
    rw [h1, h2]
    nlinarith
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hyv
  by_cases hz' : ∃ i, e i ≠ 0
  swap
  · have hz : ∀ i, e i = 0 := fun i => by_contra fun h => hz' ⟨i, h⟩
    have : y - v = 0 := by rw [← he]; simp [hz]
    have hdd : d' = d := by rw [hdd', this, add_zero]
    rw [hdd]
    have : 0 ≤ ∑ j, T d j := Finset.sum_nonneg fun j _ => hT0 d j
    nlinarith
  have hne : (Finset.univ.filter fun i => e i ≠ 0).Nonempty := by
    obtain ⟨i, hi⟩ := hz'
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩⟩
  set k := (Finset.univ.filter fun i => e i ≠ 0).max' hne with hk
  have hek : e k ≠ 0 := (Finset.mem_filter.1 (Finset.max'_mem _ hne)).2
  have habove : ∀ i, k < i → e i = 0 := by
    intro i hi
    by_contra h
    exact absurd (Finset.le_max' _ i (Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩)) (not_le.2 hi)
  -- inner products of `d'` in terms of those of `d`
  have hinner : ∀ j, k ≤ j → inner ℝ (g j) d' = inner ℝ (g j) d + e j * ‖g j‖ ^ 2 := by
    intro j hj
    rw [hdd', inner_add_right, ← he, hg,
      inner_gramSchmidt_sum_zsmul b e fun i hi => habove i (lt_of_le_of_lt hj hi)]
  have hTabove : ∀ j, k < j → T d' j = T d j := by
    intro j hj
    simp only [T]
    rw [hinner j hj.le, habove j hj, Int.cast_zero, zero_mul, add_zero]
  -- the coordinate `k` of `d'` is at least `1/2` in absolute value
  have hTk : ‖g k‖ ^ 2 / 4 ≤ T d' k := by
    simp only [T]
    rcases eq_or_ne (g k) 0 with h0 | h0
    · simp [h0]
    have hN : 0 < ‖g k‖ ^ 2 := by positivity
    have hu := hy.abs_inner_le k
    rw [← hg, ← hd] at hu
    have hek1 : (1 : ℝ) ≤ |(e k : ℝ)| := by exact_mod_cast Int.one_le_abs hek
    have hlow : ‖g k‖ ^ 2 / 2 ≤ |inner ℝ (g k) d'| := by
      rw [hinner k le_rfl]
      have h1 : ‖g k‖ ^ 2 ≤ |(e k : ℝ) * ‖g k‖ ^ 2| := by
        rw [abs_mul, abs_of_pos hN]; nlinarith
      have h2 := abs_sub_abs_le_abs_sub ((e k : ℝ) * ‖g k‖ ^ 2) (-inner ℝ (g k) d)
      rw [abs_neg, sub_neg_eq_add, add_comm] at h2
      linarith
    rw [le_div_iff₀ hN, ← sq_abs (inner ℝ (g k) d')]
    nlinarith [abs_nonneg (inner ℝ (g k) d')]
  -- the coordinates of `d` are at most `1/2` in absolute value
  have hTle : ∀ j, T d j ≤ ‖g j‖ ^ 2 / 4 := by
    intro j
    simp only [T]
    rcases eq_or_ne (g j) 0 with h0 | h0
    · simp [h0]
    have hN : 0 < ‖g j‖ ^ 2 := by positivity
    have hu := hy.abs_inner_le j
    rw [← hg, ← hd] at hu
    rw [div_le_iff₀ hN, ← sq_abs (inner ℝ (g j) d)]
    nlinarith [abs_nonneg (inner ℝ (g j) d)]
  have hTbelow : ∀ j, j ≤ k → T d j ≤ α ^ (n - (j : ℕ)) * T d' k := by
    intro j hj
    have hjk : (j : ℕ) + ((k : ℕ) - j) < n + 1 := by have := k.isLt; omega
    have hchain := hb.norm_sq_gramSchmidt_chain hδ j ((k : ℕ) - j) hjk
    have hidx : (⟨(j : ℕ) + ((k : ℕ) - j), hjk⟩ : Fin (n + 1)) = k := by
      ext; simp only; have := Fin.le_def.1 hj; omega
    rw [hidx, ← hα, ← hg] at hchain
    have hpow : α ^ ((k : ℕ) - j) ≤ α ^ (n - (j : ℕ)) :=
      pow_le_pow_right₀ hα1 (by have := k.isLt; omega)
    calc T d j ≤ ‖g j‖ ^ 2 / 4 := hTle j
      _ ≤ α ^ ((k : ℕ) - j) * ‖g k‖ ^ 2 / 4 := by linarith
      _ ≤ α ^ (n - (j : ℕ)) * ‖g k‖ ^ 2 / 4 := by
          gcongr
      _ = α ^ (n - (j : ℕ)) * (‖g k‖ ^ 2 / 4) := by ring
      _ ≤ α ^ (n - (j : ℕ)) * T d' k :=
          mul_le_mul_of_nonneg_left hTk (pow_nonneg hα0 _)
  -- sum the termwise bounds
  let V : Fin (n + 1) → ℝ := fun j => if k < j then T d' j else 0
  have hterm : ∀ j, T d j ≤ α ^ (n - (j : ℕ)) * T d' k + V j := by
    intro j
    by_cases hj : k < j
    · simp only [V, hj, ↓reduceIte]
      rw [hTabove j hj]
      have := mul_nonneg (pow_nonneg hα0 (n - (j : ℕ))) (hT0 d' k)
      linarith
    · simp only [V, hj, ↓reduceIte, add_zero]
      exact hTbelow j (not_lt.1 hj)
  have hV0 : 0 ≤ ∑ j, V j :=
    Finset.sum_nonneg fun j _ => by simp only [V]; split_ifs <;> simp [hT0]
  have hVle : T d' k + ∑ j, V j ≤ ∑ j, T d' j := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    have hVk : V k = 0 := by simp only [V, lt_irrefl, ↓reduceIte]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), hVk, zero_add]
    gcongr with j hj
    simp only [V]
    split_ifs
    · exact le_rfl
    · exact hT0 d' j
  calc ∑ j, T d j ≤ ∑ j : Fin (n + 1), (α ^ (n - (j : ℕ)) * T d' k + V j) :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = S * T d' k + ∑ j, V j := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hSfin]
    _ ≤ S * (T d' k + ∑ j, V j) := by nlinarith [hT0 d' k]
    _ ≤ S * ∑ j, T d' j := mul_le_mul_of_nonneg_left hVle (by linarith)

/-- Babai's nearest-plane bound for `δ = 3/4`, squared: if `b : Fin n → E` is `3/4`-reduced and
`y` satisfies the nearest-plane condition for `x`, then `‖x - y‖² ≤ 2ⁿ ‖x - v‖²` for every `v` in
the integer span of `b`. -/
theorem IsNearestPlane.norm_sq_le_two_pow_mul {b : Fin n → E} (hb : IsReduced (3 / 4) b)
    {x y : E} (hy : IsNearestPlane b x y) {v : E}
    (hv : v ∈ Submodule.span ℤ (Set.range b)) :
    ‖x - y‖ ^ 2 ≤ 2 ^ n * ‖x - v‖ ^ 2 := by
  cases n with
  | zero =>
    have hspan : ∀ w ∈ Submodule.span ℤ (Set.range b), w = 0 := by
      intro w hw
      rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at hw
      exact hw
    rw [hspan y hy.mem_span, hspan v hv, pow_zero, one_mul]
  | succ n =>
    have h := hy.norm_sq_le hb (by norm_num) (by norm_num) hv
    have h2 : (4 : ℝ) / (4 * (3 / 4) - 1) = 2 := by norm_num
    rw [h2] at h
    have hgeom : ∑ i ∈ Finset.range (n + 1), (2 : ℝ) ^ i ≤ 2 ^ (n + 1) := by
      rw [geom_sum_eq (by norm_num)]; norm_num
    calc ‖x - y‖ ^ 2 ≤ (∑ i ∈ Finset.range (n + 1), (2 : ℝ) ^ i) * ‖x - v‖ ^ 2 := h
      _ ≤ 2 ^ (n + 1) * ‖x - v‖ ^ 2 := by gcongr

/-- Babai's nearest-plane bound for `δ = 3/4` ([Regev2004], Lecture 3, Lemma 6): if
`b : Fin n → E` is `3/4`-reduced and `y` satisfies the nearest-plane condition for `x`, then
`‖x - y‖ ≤ (√2)ⁿ ‖x - v‖` for every `v` in the integer span of `b`. -/
theorem IsNearestPlane.norm_le_sqrt_two_pow_mul {b : Fin n → E} (hb : IsReduced (3 / 4) b)
    {x y : E} (hy : IsNearestPlane b x y) {v : E}
    (hv : v ∈ Submodule.span ℤ (Set.range b)) :
    ‖x - y‖ ≤ Real.sqrt 2 ^ n * ‖x - v‖ := by
  have hsq := hy.norm_sq_le_two_pow_mul hb hv
  have hrhs : (Real.sqrt 2 ^ n * ‖x - v‖) ^ 2 = 2 ^ n * ‖x - v‖ ^ 2 := by
    rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt (by norm_num)]
  rw [← hrhs] at hsq
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _)) two_ne_zero).1 hsq

end Cslib.Algorithms.LatticeReduction
