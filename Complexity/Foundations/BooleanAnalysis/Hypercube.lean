/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Fourier
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Huang's induced subgraph theorem

Every set `V` of more than half of the points of the cube `ι → Bool` contains a point with at least
`√|ι|` neighbors in `V` [Huang2019]. More generally, for any set `S` of coordinates, some point of
`V` has at least `√|S|` neighbors in `V` in the directions of `S`
(`BitString.exists_mem_sqrt_card_le_card_update_mem`).

The theorem and its signed adjacency matrix, which squares to `|ι|`, are Huang's [Huang2019].
Huang counts eigenvalues with Cauchy's interlacing theorem, which Mathlib lacks; here a dimension
count replaces it. Mathlib's Archive/Sensitivity.lean formalizes the case `S = univ`, but the
Archive cannot be imported.

Order the coordinates and sign the edge from `x` in direction `i` by the character of the
coordinates of `S` below `i`. The resulting signed adjacency operator `A` along `S`
(`BitString.signedAdjacency`) squares to `|S|` (`BitString.signedAdjacency_signedAdjacency`),
because the two paths around every square of the cube carry opposite signs. So its eigenspaces for
`√|S|` and `-√|S|` together span all functions on the cube, and one of them has dimension at
least half the number of points. A function in that eigenspace vanishing outside `V` exists by
counting dimensions. Its absolute value `v` satisfies `√|S| v ≤ A_V v` pointwise, where `A_V` is
the adjacency operator of the subgraph induced by `V` along `S`
(`BitString.exists_nonneg_ne_zero_sqrt_card_mul_le_sum`); [AaronsonBenDavidKothariRaoTal2021] read
Huang's sensitivity theorem spectrally through this inequality. At a point where `v` is largest,
it compares `√|S|` times the largest value with a sum of at most as many values as there are
neighbors in `V`.

## Main definitions

* `Cslib.BitString.signedAdjacency`: the signed adjacency operator of the cube along a set of
  coordinates.

## Main results

* `Cslib.BitString.signedAdjacency_signedAdjacency`: the signed adjacency operator along `S`
  squares to `|S|`.
* `Cslib.BitString.exists_nonneg_ne_zero_sqrt_card_mul_le_sum`: Huang's eigenvector bound, the
  spectral form of the induced subgraph theorem.
* `Cslib.BitString.exists_mem_sqrt_card_le_card_update_mem`: **Huang's induced subgraph
  theorem**.

## References

* [H. Huang, *Induced subgraphs of hypercubes and a proof of the Sensitivity
  Conjecture*][Huang2019]
* [S. Aaronson, S. Ben-David, R. Kothari, S. Rao, A. Tal, *Degree vs. approximate degree and
  quantum implications of Huang's sensitivity theorem*][AaronsonBenDavidKothariRaoTal2021]
-/

@[expose] public section

namespace Cslib.BitString

open Finset Function Module

variable {ι : Type*}

/-- Flipping a bit of `T` negates the character of `T`. -/
theorem chi_update_not_of_mem {R : Type*} [CommRing R] [DecidableEq ι] {T : Finset ι}
    {i : ι}
    (hi : i ∈ T) (x : ι → Bool) : chi R T (update x i (!x i)) = -chi R T x := by
  have h := chi_update_of_mem (R := R) hi x (x i)
  rw [update_eq_self] at h
  rw [chi_update_of_mem hi, h]
  cases x i <;> simp

section LinearOrder

variable [LinearOrder ι]

/-- The signed adjacency operator of the cube along the coordinates of `S`: the value at `x` sums
the values at the neighbors of `x` in the directions `i ∈ S`, the edge in direction `i` signed by
the character of the coordinates of `S` below `i`. -/
def signedAdjacency (S : Finset ι) : Module.End ℝ ((ι → Bool) → ℝ) where
  toFun v x := ∑ i ∈ S, chi ℝ {j ∈ S | j < i} x * v (update x i (!x i))
  map_add' v w := funext fun x => by
    simp only [Pi.add_apply, mul_add, sum_add_distrib]
  map_smul' c v := funext fun x => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
    exact sum_congr rfl fun _ _ => mul_left_comm _ _ _

/-- Pointwise evaluation of the signed adjacency operator `signedAdjacency S`. -/
theorem signedAdjacency_apply (S : Finset ι) (v : (ι → Bool) → ℝ) (x : ι → Bool) :
    signedAdjacency S v x = ∑ i ∈ S, chi ℝ {j ∈ S | j < i} x * v (update x i (!x i)) :=
  rfl

/-- Flipping a bit `i` below `j` negates the sign of the edges in direction `j`. -/
private theorem chi_filter_lt_update_of_lt {S : Finset ι} {i j : ι} (hi : i ∈ S) (hij : i < j)
    (x : ι → Bool) :
    chi ℝ {k ∈ S | k < j} (update x i (!x i)) = -chi ℝ {k ∈ S | k < j} x :=
  chi_update_not_of_mem (mem_filter.2 ⟨hi, hij⟩) x

/-- Flipping a bit `j` not below `i` keeps the sign of the edges in direction `i`. -/
private theorem chi_filter_lt_update_of_le {S : Finset ι} {i j : ι} (hij : i ≤ j) (x : ι → Bool)
    (b : Bool) : chi ℝ {k ∈ S | k < i} (update x j b) = chi ℝ {k ∈ S | k < i} x :=
  chi_update_of_notMem (by simp only [mem_filter, not_and, not_lt]; exact fun _ => hij) x b

/-- The two paths from `x` around the square of directions `i < j` carry opposite signs. -/
private theorem square_sign {S : Finset ι} {i j : ι} (hi : i ∈ S) (hij : i < j)
    (v : (ι → Bool) → ℝ) (x : ι → Bool) :
    chi ℝ {k ∈ S | k < i} x * (chi ℝ {k ∈ S | k < j} (update x i (!x i)) *
        v (update (update x i (!x i)) j (!update x i (!x i) j))) =
      -(chi ℝ {k ∈ S | k < j} x * (chi ℝ {k ∈ S | k < i} (update x j (!x j)) *
        v (update (update x j (!x j)) i (!update x j (!x j) i)))) := by
  rw [update_of_ne hij.ne', update_of_ne hij.ne, update_comm hij.ne',
    chi_filter_lt_update_of_lt hi hij, chi_filter_lt_update_of_le hij.le]
  ring

/-- **The signed adjacency operator squares to `|S|`**: the diagonal terms each contribute the
value at `x`, and the two paths around each square cancel. -/
theorem signedAdjacency_signedAdjacency (S : Finset ι) (v : (ι → Bool) → ℝ) :
    signedAdjacency S (signedAdjacency S v) = (#S : ℝ) • v := by
  funext x
  simp only [signedAdjacency_apply, Pi.smul_apply, smul_eq_mul, mul_sum]
  -- the term of the path from `x` in direction `i`, then in direction `j`
  set T : ι → ι → ℝ := fun i j => chi ℝ {k ∈ S | k < i} x *
    (chi ℝ {k ∈ S | k < j} (update x i (!x i)) *
      v (update (update x i (!x i)) j (!update x i (!x i) j))) with hT
  change ∑ i ∈ S, ∑ j ∈ S, T i j = #S * v x
  have hdiag (i : ι) : T i i = v x := by
    simp only [hT, update_self, Bool.not_not, update_idem, update_eq_self,
      chi_filter_lt_update_of_le le_rfl, ← mul_assoc, chi_mul_self, one_mul]
  have hanti (i j : ι) (hi : i ∈ S) (hj : j ∈ S) :
      (if j = i then 0 else T i j) = -(if i = j then 0 else T j i) := by
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp only [hij.ne', hij.ne, ↓reduceIte, hT]
      exact square_sign hi hij v x
    · simp
    · simp only [hij.ne', hij.ne, ↓reduceIte, hT]
      rw [square_sign hj hij v x, neg_neg]
  -- split off the diagonal; the rest is its own negative
  have hsplit : ∑ i ∈ S, ∑ j ∈ S, T i j = ∑ i ∈ S, ∑ j ∈ S, (if j = i then T i j else 0) +
      ∑ i ∈ S, ∑ j ∈ S, (if j = i then 0 else T i j) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun i _ => by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun j _ => by split_ifs <;> simp
  have hoff : ∑ i ∈ S, ∑ j ∈ S, (if j = i then 0 else T i j) = 0 := by
    have h := sum_comm (s := S) (t := S) (f := fun i j => if j = i then (0 : ℝ) else T i j)
    rw [sum_congr rfl fun j hj => sum_congr rfl fun i hi => hanti i j hi hj] at h
    simp only [sum_neg_distrib] at h
    linarith
  rw [hsplit, hoff, add_zero]
  simp only [sum_ite_eq', hdiag]
  rw [sum_ite_of_true fun _ h => h, sum_const, nsmul_eq_mul]

/-- The eigenspaces of the signed adjacency operator along a nonempty `S` for `√|S|` and `-√|S|`
together span all functions on the cube: `v` is `1 / (2√|S|)` times the difference of
`(A + √|S|) v` and `(A - √|S|) v`. -/
private theorem eigenspace_sup_eigenspace_signedAdjacency {S : Finset ι} (hS : S.Nonempty) :
    (signedAdjacency S).eigenspace √(#S : ℝ) ⊔ (signedAdjacency S).eigenspace (-√(#S : ℝ)) = ⊤ := by
  set A := signedAdjacency S
  set c : ℝ := √(#S : ℝ)
  have hc : c * c = #S := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hc0 : c ≠ 0 := Real.sqrt_ne_zero'.2 (by exact_mod_cast hS.card_pos)
  refine eq_top_iff.2 fun v _ => ?_
  have hplus : A v + c • v ∈ A.eigenspace c := by
    rw [Module.End.mem_eigenspace_iff, map_add, map_smul, signedAdjacency_signedAdjacency, ← hc]
    module
  have hminus : A v - c • v ∈ A.eigenspace (-c) := by
    rw [Module.End.mem_eigenspace_iff, map_sub, map_smul, signedAdjacency_signedAdjacency, ← hc]
    module
  have hv : v = (2 * c)⁻¹ • (A v + c • v) + (-(2 * c)⁻¹) • (A v - c • v) := by
    rw [smul_add, smul_sub, smul_smul, smul_smul, neg_mul]
    have : (2 * c)⁻¹ * c = 2⁻¹ := by field_simp
    rw [this]
    module
  rw [hv]
  exact Submodule.add_mem_sup (Submodule.smul_mem _ _ hplus) (Submodule.smul_mem _ _ hminus)

variable [Fintype ι]

/-- One of the eigenspaces of the signed adjacency operator along a nonempty `S` for `±√|S|` has
dimension at least half the number of points of the cube. -/
private theorem exists_abs_eq_sqrt_two_pow_le_two_mul_finrank {S : Finset ι} (hS : S.Nonempty) :
    ∃ μ : ℝ, |μ| = √(#S : ℝ) ∧
      2 ^ Fintype.card ι ≤ 2 * finrank ℝ ((signedAdjacency S).eigenspace μ) := by
  have h := Submodule.finrank_add_le_finrank_add_finrank
    ((signedAdjacency S).eigenspace √(#S : ℝ)) ((signedAdjacency S).eigenspace (-√(#S : ℝ)))
  rw [eigenspace_sup_eigenspace_signedAdjacency hS, finrank_top, Module.finrank_pi,
    Fintype.card_fun, Fintype.card_bool] at h
  by_cases hle : finrank ℝ ((signedAdjacency S).eigenspace (-√(#S : ℝ))) ≤
      finrank ℝ ((signedAdjacency S).eigenspace √(#S : ℝ))
  · exact ⟨√(#S : ℝ), abs_of_nonneg (Real.sqrt_nonneg _),
      h.trans (by rw [two_mul]; exact Nat.add_le_add_left hle _)⟩
  · exact ⟨-√(#S : ℝ), by rw [abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)],
      h.trans (by rw [two_mul]; exact Nat.add_le_add_right (le_of_not_ge hle) _)⟩

/-- Any eigenspace of `signedAdjacency S` of dimension at least `2 ^ |ι| / 2` contains a nonzero
eigenfunction vanishing outside `V` whenever `2 ^ |ι| < 2 * #V`. -/
private theorem exists_ne_zero_mem_eigenspace_and_eq_zero_of_notMem {V : Finset (ι → Bool)}
    (hV : 2 ^ Fintype.card ι < 2 * #V) (S : Finset ι) (μ : ℝ)
    (hdim : 2 ^ Fintype.card ι ≤ 2 * finrank ℝ ((signedAdjacency S).eigenspace μ)) :
    ∃ v ∈ (signedAdjacency S).eigenspace μ, v ≠ 0 ∧ ∀ y ∉ V, v y = 0 := by
  set E := (signedAdjacency S).eigenspace μ
  -- an eigenfunction vanishing outside `V`
  let r : E →ₗ[ℝ] ((Vᶜ : Finset (ι → Bool)) → ℝ) :=
    (LinearMap.funLeft ℝ ℝ Subtype.val).comp E.subtype
  have hr : finrank ℝ ((Vᶜ : Finset (ι → Bool)) → ℝ) < finrank ℝ E := by
    have hVle := card_le_univ V
    rw [Fintype.card_fun, Fintype.card_bool] at hVle
    rw [Module.finrank_pi, Fintype.card_coe, card_compl, Fintype.card_fun, Fintype.card_bool]
    omega
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := r) hr)
  exact ⟨w.1, w.2, fun h => hw0 (Subtype.ext h), fun y hy =>
    congrFun (LinearMap.mem_ker.1 hw) ⟨y, mem_compl.2 hy⟩⟩

/-- Huang's eigenvector bound along `S`, for linearly ordered coordinates. -/
private theorem exists_nonneg_ne_zero_sqrt_card_mul_le_sum_of_linearOrder
    {V : Finset (ι → Bool)} (hV : 2 ^ Fintype.card ι < 2 * #V) (S : Finset ι) :
    ∃ v : (ι → Bool) → ℝ, 0 ≤ v ∧ v ≠ 0 ∧ (∀ y ∉ V, v y = 0) ∧ ∀ x,
      √(#S : ℝ) * v x ≤ ∑ i ∈ S with update x i (!x i) ∈ V, v (update x i (!x i)) := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · -- the indicator of `V`, which is nonempty
    obtain ⟨x, hx⟩ := card_pos.1 (Nat.pos_of_ne_zero fun h => by
      rw [h, mul_zero] at hV
      exact Nat.not_lt_zero _ hV)
    refine ⟨fun y => if y ∈ V then 1 else 0, fun y => by dsimp only; split_ifs <;> norm_num,
      fun h => by simpa [hx] using congrFun h x, fun y hy => by simp [hy], fun y => by simp⟩
  obtain ⟨μ, hμ, hdim⟩ := exists_abs_eq_sqrt_two_pow_le_two_mul_finrank hS
  obtain ⟨v, hvE, hv0, hvV⟩ := exists_ne_zero_mem_eigenspace_and_eq_zero_of_notMem hV S μ hdim
  have hAv : signedAdjacency S v = μ • v := Module.End.mem_eigenspace_iff.1 hvE
  -- the absolute values of an eigenfunction vanishing outside `V`
  refine ⟨fun y => |v y|, fun y => abs_nonneg _, fun h => hv0 (funext fun y =>
    abs_eq_zero.1 (congrFun h y)), fun y hy => by simp only [hvV y hy, abs_zero], fun x => ?_⟩
  calc √(#S : ℝ) * |v x| = |signedAdjacency S v x| := by
        rw [hAv, Pi.smul_apply, smul_eq_mul, abs_mul, hμ]
    _ ≤ ∑ i ∈ S, |v (update x i (!x i))| := by
        rw [signedAdjacency_apply]
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
        rw [abs_mul, abs_chi, one_mul]
    _ = ∑ i ∈ S with update x i (!x i) ∈ V, |v (update x i (!x i))| := by
        refine (sum_filter_of_ne fun i _ h => ?_).symm
        by_contra hi
        exact h (by rw [hvV _ hi, abs_zero])

end LinearOrder

/-- **Huang's eigenvector bound**: if `V` contains more than half of the points of the cube, then
for every set `S` of coordinates some nonzero nonnegative function `v` vanishing outside `V`
satisfies `√|S| v(x) ≤ ∑ v(x ⊕ eᵢ)` at every point `x`, the sum over the directions `i ∈ S` whose
neighbor `x ⊕ eᵢ` lies in `V`. So the adjacency matrix of the subgraph of the cube induced by `V`,
restricted to the directions of `S`, has largest eigenvalue at least `√|S|`. The function is the
absolute value of an eigenfunction for `±√|S|` of the signed adjacency operator [Huang2019]. For
`S` the whole cube and `V` a fiber of `f ⊕ parity`, this is the step (7) in the proof of Theorem 1
of [AaronsonBenDavidKothariRaoTal2021] (arXiv:2010.12629v1) that bounds the spectral sensitivity
of `f` below. -/
theorem exists_nonneg_ne_zero_sqrt_card_mul_le_sum [Fintype ι] [DecidableEq ι]
    {V : Finset (ι → Bool)} (hV : 2 ^ Fintype.card ι < 2 * #V) (S : Finset ι) :
    ∃ v : (ι → Bool) → ℝ, 0 ≤ v ∧ v ≠ 0 ∧ (∀ y ∉ V, v y = 0) ∧ ∀ x,
      √(#S : ℝ) * v x ≤ ∑ i ∈ S with update x i (!x i) ∈ V, v (update x i (!x i)) := by
  let : LinearOrder ι := LinearOrder.lift' _ (Fintype.equivFin ι).injective
  convert exists_nonneg_ne_zero_sqrt_card_mul_le_sum_of_linearOrder hV S using 12

/-- **Huang's induced subgraph theorem**: if `V` contains more than half of the points of the cube,
then for every set `S` of coordinates some point of `V` has at least `√|S|` neighbors in `V` in
the directions of `S`. For `S = univ`, the subgraph of the cube induced by `V` has maximum degree
at least `√|ι|` [Huang2019]. -/
theorem exists_mem_sqrt_card_le_card_update_mem [Fintype ι] [DecidableEq ι]
    {V : Finset (ι → Bool)} (hV : 2 ^ Fintype.card ι < 2 * #V) (S : Finset ι) :
    ∃ x ∈ V, √(#S : ℝ) ≤ #{i ∈ S | update x i (!x i) ∈ V} := by
  obtain ⟨v, hv, hv0, hvV, hS⟩ := exists_nonneg_ne_zero_sqrt_card_mul_le_sum hV S
  -- a point where `v` is largest
  obtain ⟨x, -, hx⟩ := exists_max_image univ v univ_nonempty
  have hpos : 0 < v x := by
    by_contra h
    exact hv0 (funext fun y => le_antisymm ((hx y (mem_univ y)).trans (not_lt.1 h)) (hv y))
  have hxV : x ∈ V := by
    by_contra h
    rw [hvV x h] at hpos
    exact lt_irrefl 0 hpos
  refine ⟨x, hxV, le_of_mul_le_mul_right ((hS x).trans ?_) hpos⟩
  rw [← nsmul_eq_mul]
  exact sum_le_card_nsmul _ _ _ fun i _ => hx _ (mem_univ _)

end Cslib.BitString
