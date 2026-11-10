/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/LinearAlgebra/Matrix/LinearProgramming.lean`)

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Farkas
public import Mathlib.LinearAlgebra.Matrix.RowCol
public import Mathlib.Order.Bounds.Defs
import Mathlib.Algebra.Order.Pi
import Mathlib.Data.Fintype.Lattice
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Linear-programming duality over linearly ordered fields

For a matrix `A : Matrix ι κ K`, a right-hand side `b` and an objective `c` over a linearly
ordered field `K`, the primal linear program in inequality form maximizes `c ⬝ᵥ x` subject to
`A *ᵥ x ≤ b`. Its dual minimizes `y ⬝ᵥ b` subject to `0 ≤ y` and `y ᵥ* A = c`. The proofs use
Fourier–Motzkin elimination (`Matrix.FourierMotzkin.exists_projection`) and Farkas' lemma
(`Matrix.not_exists_mulVec_le_iff`), so they hold over every linearly ordered field, including
`ℚ`. See also [DvorakKolmogorov2024] for an independent Lean 4 formalization of
linear-programming duality over linearly ordered fields.

## Main results

* `Matrix.dotProduct_le_dotProduct_of_mulVec_le`: weak duality.
* `Matrix.exists_dual_eq_of_bddAbove`: a feasible primal with objective bounded above has a
  primal solution and a dual solution of equal value.
* `Matrix.exists_isGreatest_of_bddAbove`: a feasible primal with objective bounded above attains
  its maximum.
* `Matrix.exists_isGreatest_isLeast_dotProduct`: strong duality. If both programs are feasible,
  both optima are attained and they are equal.
* `Matrix.bddAbove_image_dotProduct_iff`, `Matrix.bddBelow_image_dotProduct_iff`: a feasible
  program is bounded iff the other program is feasible, so a feasible program whose dual is
  infeasible is unbounded.
* `Matrix.dotProduct_eq_dotProduct_iff_of_mulVec_le`: complementary slackness.
* `Matrix.exists_dual_le_of_forall_le`: the affine Farkas lemma.
* `Matrix.exists_isGreatest_isLeast_dotProduct_of_nonneg`: strong duality for the canonical pair
  `max {c ⬝ᵥ x | A *ᵥ x ≤ b, 0 ≤ x}` and `min {y ⬝ᵥ b | c ≤ y ᵥ* A, 0 ≤ y}`.

## References

* [DvorakKolmogorov2024]
* [MatousekGartner2007], Chapter 6
* [Schrijver1986], Sections 7.4, 7.6 and 7.9
-/

public section

open Matrix

namespace Matrix

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Weak duality**: the value of a primal solution `A *ᵥ x ≤ b` is at most the value of any dual
solution `0 ≤ y`, `y ᵥ* A = c` [Schrijver1986, Section 7.4]. -/
theorem dotProduct_le_dotProduct_of_mulVec_le {A : Matrix ι κ K} {b : ι → K} {c : κ → K}
    {x : κ → K} {y : ι → K} (hx : A *ᵥ x ≤ b) (hy : 0 ≤ y) (hyA : y ᵥ* A = c) :
    c ⬝ᵥ x ≤ y ⬝ᵥ b := by
  rw [← hyA, ← dotProduct_mulVec]
  exact dotProduct_le_dotProduct_of_nonneg_left hx hy

/-- A linear objective bounded above on a nonempty polyhedron `A *ᵥ x ≤ b` attains its maximum at
a point `x`, certified by a dual solution `y` of the same value [Schrijver1986, Section 7.4]. -/
theorem exists_dual_eq_of_bddAbove (A : Matrix ι κ K) (b : ι → K) (c : κ → K)
    (hP : ∃ x, A *ᵥ x ≤ b) (hbdd : BddAbove ((c ⬝ᵥ ·) '' {x | A *ᵥ x ≤ b})) :
    ∃ x y, A *ᵥ x ≤ b ∧ 0 ≤ y ∧ y ᵥ* A = c ∧ y ⬝ᵥ b = c ⬝ᵥ x := by
  classical
  obtain ⟨x₀, hx₀⟩ := hP
  obtain ⟨M, hM⟩ := hbdd
  -- project the system `A x ≤ b`, `t - c ⬝ᵥ x ≤ 0` in the variables `x` and `t` onto `t`
  let A' : Matrix (ι ⊕ Unit) κ K := fromRows A (replicateRow Unit (-c))
  let B' : Matrix (ι ⊕ Unit) Unit K := fromRows 0 1
  let b' : ι ⊕ Unit → K := Sum.elim b 0
  obtain ⟨ρ, _, T, hT, hTA, hiff⟩ := FourierMotzkin.exists_projection A' B' b'
  set β : ρ → K := fun r => T r (.inr ())
  set γ : ρ → K := T *ᵥ b'
  have hTB : ∀ t : K, (T * B') *ᵥ (fun _ => t) = fun r => β r * t := by
    intro t
    rw [← mulVec_mulVec, fromRows_mulVec, zero_mulVec, one_mulVec]
    funext r
    simp only [mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, Finset.univ_unique,
      Finset.sum_singleton, PUnit.default_eq_unit, β]
  have hfeas : ∀ t, (∃ x, A *ᵥ x ≤ b ∧ t ≤ c ⬝ᵥ x) ↔ ∀ r, β r * t ≤ γ r := by
    intro t
    have h := hiff fun _ => t
    rw [hTB] at h
    refine Iff.trans ?_ h
    refine exists_congr fun x => ?_
    rw [fromRows_mulVec, fromRows_mulVec, zero_mulVec, one_mulVec, ← Sum.elim_add_add,
      Sum.elim_le_elim_iff, add_zero, replicateRow_mulVec_eq_const]
    refine and_congr Iff.rfl ⟨fun h _ => ?_, fun h => ?_⟩
    · simp only [Pi.add_apply, Function.const_apply, Pi.zero_apply, neg_dotProduct]
      linarith
    · have h := h ()
      simp only [Pi.add_apply, Function.const_apply, Pi.zero_apply, neg_dotProduct] at h
      linarith
  -- some row of the projection bounds `t` from above
  have h₀ := (hfeas (c ⬝ᵥ x₀)).1 ⟨x₀, hx₀, le_rfl⟩
  have hpos : ∃ r, 0 < β r := by
    by_contra! hneg
    obtain ⟨x, hx, htx⟩ := (hfeas (max (c ⬝ᵥ x₀) M + 1)).2 fun r =>
      (mul_le_mul_of_nonpos_left (by linarith [le_max_left (c ⬝ᵥ x₀) M]) (hneg r)).trans (h₀ r)
    linarith [hM ⟨x, hx, rfl⟩, le_max_right (c ⬝ᵥ x₀) M]
  obtain ⟨r₀, hr₀⟩ := hpos
  have : Nonempty {r // 0 < β r} := ⟨⟨r₀, hr₀⟩⟩
  obtain ⟨⟨r, hr⟩, hmin⟩ := Finite.exists_min fun r : {r // 0 < β r} => γ r / β r
  have ht₀ : c ⬝ᵥ x₀ ≤ γ r / β r := by
    rw [le_div_iff₀ hr, mul_comm]
    exact h₀ r
  obtain ⟨x, hx, htx⟩ := (hfeas (γ r / β r)).2 fun s => by
    rcases lt_or_ge 0 (β s) with hs | hs
    · rw [mul_comm, ← le_div_iff₀ hs]
      exact hmin ⟨s, hs⟩
    · exact (mul_le_mul_of_nonpos_left ht₀ hs).trans (h₀ s)
  have hxt : c ⬝ᵥ x ≤ γ r / β r := by
    rw [le_div_iff₀ hr, mul_comm]
    exact (hfeas (c ⬝ᵥ x)).1 ⟨x, hx, le_rfl⟩ r
  -- the row `r` of `T`, rescaled, is the dual solution
  set u : ι → K := fun i => T r (.inl i)
  have hγ : γ r = u ⬝ᵥ b := by
    simp only [γ, b', u, mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  have huA : u ᵥ* A = β r • c := by
    have h : T r ᵥ* A' = 0 := congr_fun hTA r
    rw [vecMul_fromRows] at h
    funext j
    have hj := congr_fun h j
    simp only [Pi.add_apply, Pi.zero_apply, vecMul, dotProduct, replicateRow_apply,
      Finset.univ_unique, Finset.sum_singleton, Function.comp_apply, PUnit.default_eq_unit,
      Pi.neg_apply, mul_neg] at hj
    simp only [vecMul, dotProduct, Pi.smul_apply, smul_eq_mul, u, β]
    linarith
  refine ⟨x, (β r)⁻¹ • u, hx, fun i => ?_, ?_, ?_⟩
  · exact smul_nonneg (inv_nonneg.2 hr.le) (hT r _)
  · rw [smul_vecMul, huA, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  · rw [smul_dotProduct, ← hγ, smul_eq_mul, inv_mul_eq_div]
    exact le_antisymm htx hxt

omit [Fintype ι] in
/-- A linear objective bounded above on a nonempty polyhedron attains its supremum
[Schrijver1986, Section 7.4]. -/
theorem exists_isGreatest_of_bddAbove [Finite ι] (A : Matrix ι κ K) (b : ι → K) (c : κ → K)
    (hP : ∃ x, A *ᵥ x ≤ b) (hbdd : BddAbove ((c ⬝ᵥ ·) '' {x | A *ᵥ x ≤ b})) :
    ∃ x, A *ᵥ x ≤ b ∧ IsGreatest ((c ⬝ᵥ ·) '' {x | A *ᵥ x ≤ b}) (c ⬝ᵥ x) := by
  have := Fintype.ofFinite ι
  obtain ⟨x, y, hx, hy, hyA, hxy⟩ := exists_dual_eq_of_bddAbove A b c hP hbdd
  refine ⟨x, hx, ⟨x, hx, rfl⟩, ?_⟩
  rintro _ ⟨x', hx', rfl⟩
  exact hxy ▸ dotProduct_le_dotProduct_of_mulVec_le hx' hy hyA

/-- **Strong duality**: if the primal `max {c ⬝ᵥ x | A *ᵥ x ≤ b}` and the dual
`min {y ⬝ᵥ b | 0 ≤ y, y ᵥ* A = c}` are both feasible, then both optima are attained and equal
[Schrijver1986, Corollary 7.1g]. -/
theorem exists_isGreatest_isLeast_dotProduct (A : Matrix ι κ K) (b : ι → K) (c : κ → K)
    (hP : ∃ x, A *ᵥ x ≤ b) (hD : ∃ y, 0 ≤ y ∧ y ᵥ* A = c) :
    ∃ v, IsGreatest ((c ⬝ᵥ ·) '' {x | A *ᵥ x ≤ b}) v ∧
      IsLeast ((· ⬝ᵥ b) '' {y | 0 ≤ y ∧ y ᵥ* A = c}) v := by
  obtain ⟨y₀, hy₀, hy₀A⟩ := hD
  obtain ⟨x, y, hx, hy, hyA, hxy⟩ := exists_dual_eq_of_bddAbove A b c hP
    ⟨y₀ ⬝ᵥ b, by
      rintro _ ⟨x, hx, rfl⟩
      exact dotProduct_le_dotProduct_of_mulVec_le hx hy₀ hy₀A⟩
  refine ⟨c ⬝ᵥ x, ⟨⟨x, hx, rfl⟩, ?_⟩, ⟨⟨y, ⟨hy, hyA⟩, hxy⟩, ?_⟩⟩
  · rintro _ ⟨x', hx', rfl⟩
    exact hxy ▸ dotProduct_le_dotProduct_of_mulVec_le hx' hy hyA
  · rintro _ ⟨y', ⟨hy', hy'A⟩, rfl⟩
    exact dotProduct_le_dotProduct_of_mulVec_le hx hy' hy'A

/-- A feasible primal program is bounded above iff its dual is feasible. In particular a feasible
primal program with infeasible dual is unbounded [Schrijver1986, Section 7.4]. -/
theorem bddAbove_image_dotProduct_iff (A : Matrix ι κ K) (b : ι → K) (c : κ → K)
    (hP : ∃ x, A *ᵥ x ≤ b) :
    BddAbove ((c ⬝ᵥ ·) '' {x | A *ᵥ x ≤ b}) ↔ ∃ y, 0 ≤ y ∧ y ᵥ* A = c := by
  refine ⟨fun h => ?_, fun ⟨y, hy, hyA⟩ => ⟨y ⬝ᵥ b, ?_⟩⟩
  · obtain ⟨x, y, -, hy, hyA, -⟩ := exists_dual_eq_of_bddAbove A b c hP h
    exact ⟨y, hy, hyA⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact dotProduct_le_dotProduct_of_mulVec_le hx hy hyA

/-- A feasible dual program is bounded below iff the primal is feasible. In particular a feasible
dual program with infeasible primal is unbounded [Schrijver1986, Section 7.4]. -/
theorem bddBelow_image_dotProduct_iff (A : Matrix ι κ K) (b : ι → K) (c : κ → K)
    (hD : ∃ y, 0 ≤ y ∧ y ᵥ* A = c) :
    BddBelow ((· ⬝ᵥ b) '' {y | 0 ≤ y ∧ y ᵥ* A = c}) ↔ ∃ x, A *ᵥ x ≤ b := by
  refine ⟨fun ⟨m, hm⟩ => ?_, fun ⟨x, hx⟩ => ⟨c ⬝ᵥ x, ?_⟩⟩
  · by_contra hP
    -- move along the Farkas ray `y₀ + s • z` until the value drops below `m`
    obtain ⟨z, hz, hzA, hzb⟩ := (not_exists_mulVec_le_iff A b).1 hP
    obtain ⟨y₀, hy₀, hy₀A⟩ := hD
    set s := (|y₀ ⬝ᵥ b - m| + 1) / -(z ⬝ᵥ b)
    have hs : s * -(z ⬝ᵥ b) = |y₀ ⬝ᵥ b - m| + 1 := div_mul_cancel₀ _ (by linarith)
    have hs0 : 0 ≤ s := div_nonneg (by positivity) (by linarith)
    have := hm ⟨y₀ + s • z, ⟨add_nonneg hy₀ (smul_nonneg hs0 hz), by
      rw [add_vecMul, smul_vecMul, hzA, smul_zero, add_zero, hy₀A]⟩, rfl⟩
    change m ≤ (y₀ + s • z) ⬝ᵥ b at this
    rw [add_dotProduct, smul_dotProduct, smul_eq_mul] at this
    linarith [le_abs_self (y₀ ⬝ᵥ b - m)]
  · rintro _ ⟨y, ⟨hy, hyA⟩, rfl⟩
    exact dotProduct_le_dotProduct_of_mulVec_le hx hy hyA

omit [Fintype κ] in
/-- A dual objective bounded below on a nonempty dual polyhedron attains its infimum
[Schrijver1986, Section 7.4]. -/
theorem exists_isLeast_of_bddBelow [Finite κ] (A : Matrix ι κ K) (b : ι → K) (c : κ → K)
    (hD : ∃ y, 0 ≤ y ∧ y ᵥ* A = c) (hbdd : BddBelow ((· ⬝ᵥ b) '' {y | 0 ≤ y ∧ y ᵥ* A = c})) :
    ∃ v, IsLeast ((· ⬝ᵥ b) '' {y | 0 ≤ y ∧ y ᵥ* A = c}) v := by
  have := Fintype.ofFinite κ
  exact (exists_isGreatest_isLeast_dotProduct A b c
    ((bddBelow_image_dotProduct_iff A b c hD).1 hbdd) hD).imp fun _ h => h.2

/-- **Complementary slackness**: a primal solution `x` and a dual solution `y` have equal values
iff every constraint `i` with `y i ≠ 0` is tight at `x` [Schrijver1986, Section 7.9]. -/
theorem dotProduct_eq_dotProduct_iff_of_mulVec_le {A : Matrix ι κ K} {b : ι → K} {c : κ → K}
    {x : κ → K} {y : ι → K} (hx : A *ᵥ x ≤ b) (hy : 0 ≤ y) (hyA : y ᵥ* A = c) :
    c ⬝ᵥ x = y ⬝ᵥ b ↔ ∀ i, y i = 0 ∨ (A *ᵥ x) i = b i := by
  have hgap : y ⬝ᵥ b - c ⬝ᵥ x = ∑ i, y i * (b i - (A *ᵥ x) i) := by
    rw [← hyA, ← dotProduct_mulVec, ← dotProduct_sub]
    rfl
  have hterm : ∀ i ∈ Finset.univ, 0 ≤ y i * (b i - (A *ᵥ x) i) :=
    fun i _ => mul_nonneg (hy i) (sub_nonneg.2 (hx i))
  constructor
  · intro h i
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 (by rw [← hgap, h, sub_self])
      i (Finset.mem_univ i)
    rcases mul_eq_zero.1 h0 with h' | h'
    · exact .inl h'
    · exact .inr (sub_eq_zero.1 h').symm
  · intro h
    have h0 : ∑ i, y i * (b i - (A *ᵥ x) i) = 0 := Finset.sum_eq_zero fun i _ => by
      rcases h i with h' | h'
      · rw [h', zero_mul]
      · rw [h', sub_self, mul_zero]
    rw [h0, sub_eq_zero] at hgap
    exact hgap.symm

/-- **Affine Farkas lemma**: if the inequality `c ⬝ᵥ x ≤ δ` holds on a nonempty polyhedron
`A *ᵥ x ≤ b`, then it is implied by a nonnegative combination of the constraints
[Schrijver1986, Corollary 7.1h]. -/
theorem exists_dual_le_of_forall_le (A : Matrix ι κ K) (b : ι → K) (c : κ → K) (δ : K)
    (hP : ∃ x, A *ᵥ x ≤ b) (h : ∀ x, A *ᵥ x ≤ b → c ⬝ᵥ x ≤ δ) :
    ∃ y, 0 ≤ y ∧ y ᵥ* A = c ∧ y ⬝ᵥ b ≤ δ := by
  obtain ⟨x, y, hx, hy, hyA, hxy⟩ :=
    exists_dual_eq_of_bddAbove A b c hP ⟨δ, by rintro _ ⟨x, hx, rfl⟩; exact h x hx⟩
  exact ⟨y, hy, hyA, hxy ▸ h x hx⟩

/-! ### The canonical pair `max {c ⬝ᵥ x | A *ᵥ x ≤ b, 0 ≤ x}`, `min {y ⬝ᵥ b | c ≤ y ᵥ* A, 0 ≤ y}` -/

/-- **Weak duality** for the canonical pair [MatousekGartner2007, Chapter 6]. -/
theorem dotProduct_le_dotProduct_of_nonneg_of_mulVec_le {A : Matrix ι κ K} {b : ι → K}
    {c : κ → K} {x : κ → K} {y : ι → K} (hx : 0 ≤ x) (hAx : A *ᵥ x ≤ b) (hy : 0 ≤ y)
    (hc : c ≤ y ᵥ* A) : c ⬝ᵥ x ≤ y ⬝ᵥ b :=
  calc c ⬝ᵥ x ≤ (y ᵥ* A) ⬝ᵥ x := dotProduct_le_dotProduct_of_nonneg_right hc hx
    _ = y ⬝ᵥ (A *ᵥ x) := (dotProduct_mulVec y A x).symm
    _ ≤ y ⬝ᵥ b := dotProduct_le_dotProduct_of_nonneg_left hAx hy

omit [Fintype ι] in
private theorem fromRows_neg_one_mulVec_le_iff [DecidableEq κ] (A : Matrix ι κ K) (b : ι → K)
    (x : κ → K) : fromRows A (-1 : Matrix κ κ K) *ᵥ x ≤ Sum.elim b 0 ↔ A *ᵥ x ≤ b ∧ 0 ≤ x := by
  rw [fromRows_mulVec, Sum.elim_le_elim_iff, neg_mulVec, one_mulVec, neg_nonpos]

/-- **Strong duality** for the canonical pair `max {c ⬝ᵥ x | A *ᵥ x ≤ b, 0 ≤ x}` and
`min {y ⬝ᵥ b | c ≤ y ᵥ* A, 0 ≤ y}`: if both are feasible, both optima are attained and equal
[MatousekGartner2007, Chapter 6]. -/
theorem exists_isGreatest_isLeast_dotProduct_of_nonneg (A : Matrix ι κ K) (b : ι → K)
    (c : κ → K) (hP : ∃ x, 0 ≤ x ∧ A *ᵥ x ≤ b) (hD : ∃ y, 0 ≤ y ∧ c ≤ y ᵥ* A) :
    ∃ v, IsGreatest ((c ⬝ᵥ ·) '' {x | 0 ≤ x ∧ A *ᵥ x ≤ b}) v ∧
      IsLeast ((· ⬝ᵥ b) '' {y | 0 ≤ y ∧ c ≤ y ᵥ* A}) v := by
  classical
  obtain ⟨x₀, hx₀, hAx₀⟩ := hP
  obtain ⟨y₀, hy₀, hcy₀⟩ := hD
  obtain ⟨x, w, hx, hw, hwM, hxw⟩ :=
    exists_dual_eq_of_bddAbove (fromRows A (-1 : Matrix κ κ K)) (Sum.elim b 0) c
    ⟨x₀, (fromRows_neg_one_mulVec_le_iff A b x₀).2 ⟨hAx₀, hx₀⟩⟩ ⟨y₀ ⬝ᵥ b, by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨hAx, hx⟩ := (fromRows_neg_one_mulVec_le_iff A b x).1 hx
      exact dotProduct_le_dotProduct_of_nonneg_of_mulVec_le hx hAx hy₀ hcy₀⟩
  obtain ⟨hAx, hx⟩ := (fromRows_neg_one_mulVec_le_iff A b x).1 hx
  have hc : c ≤ (w ∘ Sum.inl) ᵥ* A := by
    rw [← hwM, vecMul_fromRows, vecMul_neg, vecMul_one]
    intro k
    rw [Pi.add_apply, Pi.neg_apply, Function.comp_apply]
    exact add_le_of_nonpos_right (neg_nonpos.2 (hw _))
  have hval : (w ∘ Sum.inl) ⬝ᵥ b = c ⬝ᵥ x := by
    rw [← hxw]
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero, add_zero, Function.comp_apply]
  refine ⟨c ⬝ᵥ x, ⟨⟨x, ⟨hx, hAx⟩, rfl⟩, ?_⟩,
    ⟨⟨w ∘ Sum.inl, ⟨fun i => hw _, hc⟩, hval⟩, ?_⟩⟩
  · rintro _ ⟨x', ⟨hx', hAx'⟩, rfl⟩
    exact hval ▸ dotProduct_le_dotProduct_of_nonneg_of_mulVec_le hx' hAx' (fun i => hw _) hc
  · rintro _ ⟨y', ⟨hy', hc'⟩, rfl⟩
    exact dotProduct_le_dotProduct_of_nonneg_of_mulVec_le hx hAx hy' hc'

end Matrix
