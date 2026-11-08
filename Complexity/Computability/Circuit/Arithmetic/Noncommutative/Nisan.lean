/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.Noncommutative.ABP

/-!
# Nisan's characterization of non-commutative ABPs

Nisan's theorem computes the size of the smallest homogeneous layered non-commutative ABP for a
homogeneous polynomial `f` of degree `d` exactly. The lower bound `∑_{k ≤ d} rank M_k(f)` is
`NoncommABP.sum_rank_nisanMatrix_le_size`. This file supplies the matching construction
([Saptharishi2026Survey], Exercise 11.2).

The *row* of a word `u` is the function `v ↦ coeff (u v) f` (`nisanRow f u`). The rows of the
words of length `k` span `nisanRowSpace f k`. When `f` is homogeneous of degree `k + m`, its
dimension is `rank M_k(f)` (`rank_nisanMatrix_eq_finrank_nisanRowSpace`): a row vanishes off the
words of length `m`, so restricting rows to those words is injective on the span.

The construction gives layer `k` one vertex per vector of a basis of `nisanRowSpace f k`. Reading
a letter `x` maps the row of `u` to the row of `u x`. This map takes `nisanRowSpace f k` into
`nisanRowSpace f (k + 1)`, and the edge weights are its matrix entries in the chosen bases. The
source basis vector is rescaled to the row of the empty word, which is `f` itself, and the sink
basis vectors to evaluate to `1` at the empty word. By induction on `k`, the row of every word
`u` of length `k` is `∑ i, coeff u (pre k i) • b k i`. Evaluating at the empty word for `k = d`
recovers `coeff u f`.

* **Exactness** (`NoncommABP.exists_width_eq_rank`). Every nonzero homogeneous `f` of degree
  `d ≥ 1` is computed by an ABP with layer `k` of width exactly `rank M_k(f)`.
* **Nisan's theorem** (`NoncommABP.isLeast_size`; [Nisan1991NonCommutative], Theorem 1;
  [Saptharishi2026Survey], Theorem 11.2). The least size of an ABP computing such an `f` is
  `∑_{k ≤ d} rank M_k(f)`, the number of vertices, as in Nisan's Theorem 1. The displayed
  statement of the survey's Theorem 11.2 leaves out the final term `rank M_d(f)`, which is `1`.

**Scope.** The ABPs are homogeneous and layered: every edge is labelled by a homogeneous linear
form. The model is `NoncommABP`. The reduction from general non-commutative ABPs, with
`s · poly(d)` blow-up ([Saptharishi2026Survey], Exercise 11.1), is not formalized. The degree
`d = 0` is excluded: a degree-`0` ABP computes the constant `1`, not an arbitrary nonzero scalar.
`f = 0` is excluded because exactness fails there: every Nisan matrix of `0` has rank `0`, while
`width_zero` and `width_deg` force a source and a sink, so every ABP of positive degree has size
at least `2`. ABPs computing `0` exist, for instance with an empty middle layer or zero edge
labels; the lower bound holds for them.

## Main definitions

* `Cslib.Circuits.Arithmetic.nisanRow`, `Cslib.Circuits.Arithmetic.nisanRowSpace`.

## Main results

* `Cslib.Circuits.Arithmetic.rank_nisanMatrix_eq_finrank_nisanRowSpace`: `rank M_k(f)` is the
  dimension of the row space.
* `Cslib.Circuits.Arithmetic.one_le_rank_nisanMatrix`: `rank M_k(f) ≥ 1` for nonzero homogeneous
  `f`.
* `Cslib.Circuits.Arithmetic.rank_nisanMatrix_zero_left`,
  `Cslib.Circuits.Arithmetic.rank_nisanMatrix_zero_right`: the outer ranks are `1`.
* `Cslib.Circuits.Arithmetic.NoncommABP.exists_width_eq_rank`: the optimal widths are attained.
* `Cslib.Circuits.Arithmetic.NoncommABP.isLeast_size`: Nisan's theorem.

## References

* [N. Nisan, *Lower bounds for non-commutative computation*][Nisan1991NonCommutative],
  extended abstract, §3 (Theorem 1). Nisan's sketch of the upper bound removes vertices from a
  layer with more than `rank M_k(f)` vertices; the proof here instead builds the optimal ABP
  directly from the rows, as sketched above.
* [R. Saptharishi, *A survey of lower bounds in arithmetic circuit
  complexity*][Saptharishi2026Survey], Chapter 11 (Theorem 11.2, Exercises 11.1 and 11.2); the
  chapter is unchanged from release v9.0.3. The survey leaves the construction as an exercise.
-/

public section

namespace Cslib.Circuits.Arithmetic

open FreeAlgebra

variable {K : Type*} [Field K] {X : Type*}

/-- The row of the word `u` in Nisan's matrices: the function `v ↦ coeff (u v) f`. -/
noncomputable def nisanRow (f : FreeAlgebra K X) (u : FreeMonoid X) : FreeMonoid X → K :=
  fun v => coeff (u * v) f

/-- The span of the rows of the words of length `k`. -/
noncomputable def nisanRowSpace (f : FreeAlgebra K X) (k : ℕ) :
    Submodule K (FreeMonoid X → K) :=
  Submodule.span K (Set.range fun u : Fin k → X => nisanRow f (FreeMonoid.ofFn u))

/-- Left translation of the argument by the letter `x`. -/
private noncomputable def shiftBy (x : X) : (FreeMonoid X → K) →ₗ[K] (FreeMonoid X → K) :=
  LinearMap.funLeft K K (fun v => FreeMonoid.of x * v)

private theorem shiftBy_nisanRow (f : FreeAlgebra K X) (u : FreeMonoid X) (x : X) :
    shiftBy x (nisanRow f u) = nisanRow f (u * FreeMonoid.of x) := by
  funext v
  simp [shiftBy, nisanRow, LinearMap.funLeft, mul_assoc]

private theorem nisanRowSpace_le_comap_shiftBy (f : FreeAlgebra K X) (k : ℕ) (x : X) :
    nisanRowSpace f k ≤ (nisanRowSpace f (k + 1)).comap (shiftBy x) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨u, rfl⟩
  refine Submodule.subset_span ⟨Fin.snoc u x, ?_⟩
  exact (congrArg (nisanRow f) (FreeMonoid.ofFn_snoc u x)).trans
    (shiftBy_nisanRow f _ x).symm

/-- For `f` homogeneous of degree `d`, elements of the row space of layer `k` vanish off the words
of length `d - k`. -/
theorem apply_eq_zero_of_mem_nisanRowSpace {f : FreeAlgebra K X} {d k : ℕ}
    (hf : f.IsHomogeneous d) {g : FreeMonoid X → K} (hg : g ∈ nisanRowSpace f k) {v : FreeMonoid X}
    (hv : k + v.length ≠ d) : g v = 0 := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨u, rfl⟩ := hg
    refine hf.coeff_eq_zero ?_
    rwa [FreeMonoid.length_mul, FreeMonoid.length_ofFn]
  | zero => rfl
  | add g g' _ _ hg hg' => simp [hg, hg']
  | smul a g _ hg => simp [hg]

/-- For `f` homogeneous of degree `k + m`, `rank M_k(f)` is the dimension of the span of the rows
of the words of length `k`. -/
theorem rank_nisanMatrix_eq_finrank_nisanRowSpace [Fintype X] {f : FreeAlgebra K X}
    {k m : ℕ} (hf : f.IsHomogeneous (k + m)) :
    (nisanMatrix k m f).rank = Module.finrank K (nisanRowSpace f k) := by
  let restr : (FreeMonoid X → K) →ₗ[K] ((Fin m → X) → K) :=
    LinearMap.funLeft K K FreeMonoid.ofFn
  have hrow : Set.range (nisanMatrix k m f).row =
      restr '' Set.range (fun u : Fin k → X => nisanRow f (FreeMonoid.ofFn u)) := by
    rw [← Set.range_comp]
    congr 1
    funext u v
    simp [Matrix.row, nisanRow, restr]
  have hinj : Function.Injective (restr ∘ₗ (nisanRowSpace f k).subtype) := by
    refine (injective_iff_map_eq_zero _).mpr fun g hg => Subtype.ext (funext fun v => ?_)
    by_cases hv : v.length = m
    · obtain ⟨u, rfl⟩ := FreeMonoid.exists_ofFn_eq v hv
      exact congrFun hg u
    · exact apply_eq_zero_of_mem_nisanRowSpace hf g.2 (by omega)
  rw [Matrix.rank_eq_finrank_span_row, hrow, Submodule.span_image,
    ← LinearMap.finrank_range_of_inj hinj, LinearMap.range_comp, Submodule.range_subtype]
  rfl

/-- The row of the empty word lists the coefficients of `f`. -/
theorem nisanRow_one (f : FreeAlgebra K X) : nisanRow f 1 = fun w => coeff w f := by
  funext w
  simp [nisanRow]

/-- For nonzero `f`, the row space of layer `0` is a line: `rank M_0(f) = 1`. -/
theorem finrank_nisanRowSpace_zero {f : FreeAlgebra K X} (hf : f ≠ 0) :
    Module.finrank K (nisanRowSpace f 0) = 1 := by
  have hrange :
      Set.range (fun u : Fin 0 → X => nisanRow f (FreeMonoid.ofFn u)) = {nisanRow f 1} := by
    rw [Set.range_unique, FreeMonoid.ofFn_zero]
  rw [nisanRowSpace, hrange]
  refine finrank_span_singleton fun h => ?_
  obtain ⟨w, hw⟩ := exists_coeff_ne_zero hf
  exact hw (by simpa [nisanRow_one] using congrFun h w)

/-- Over finitely many variables, the row spaces are finite-dimensional. -/
instance [Finite X] (f : FreeAlgebra K X) (k : ℕ) : FiniteDimensional K (nisanRowSpace f k) :=
  FiniteDimensional.span_of_finite K (Set.finite_range _)

/-- For nonzero `f` homogeneous of degree `d`, the row space of layer `d` is a line:
`rank M_d(f) = 1`. -/
theorem finrank_nisanRowSpace_deg [Finite X] {f : FreeAlgebra K X} {d : ℕ}
    (hd : f.IsHomogeneous d) (hf : f ≠ 0) : Module.finrank K (nisanRowSpace f d) = 1 := by
  have := Fintype.ofFinite X
  have hle : Module.finrank K (nisanRowSpace f d) ≤ 1 := by
    rw [← rank_nisanMatrix_eq_finrank_nisanRowSpace (m := 0) hd]
    exact (Matrix.rank_le_card_width _).trans (by simp)
  refine le_antisymm hle (Module.finrank_pos_iff_exists_ne_zero.mpr ?_)
  obtain ⟨w, hw⟩ := exists_coeff_ne_zero hf
  obtain ⟨u, hu⟩ := FreeMonoid.exists_ofFn_eq w (hd w hw)
  refine ⟨⟨nisanRow f w, Submodule.subset_span ⟨u, congrArg (nisanRow f) hu⟩⟩,
    fun h => hw ?_⟩
  have := congrFun (congrArg Subtype.val h) 1
  simpa [nisanRow] using this

/-- For nonzero `f` homogeneous of degree `k + m`, `rank M_k(f) ≥ 1`: the row of the first `k`
letters of a word with nonzero coefficient is nonzero. -/
theorem one_le_rank_nisanMatrix [Fintype X] {f : FreeAlgebra K X} {k m : ℕ}
    (hf : f.IsHomogeneous (k + m)) (hf0 : f ≠ 0) : 1 ≤ (nisanMatrix k m f).rank := by
  rw [rank_nisanMatrix_eq_finrank_nisanRowSpace hf]
  refine Nat.one_le_iff_ne_zero.mpr (Module.finrank_pos_iff_exists_ne_zero.mpr ?_).ne'
  obtain ⟨w, hw⟩ := exists_coeff_ne_zero hf0
  have hlen : w.toList.length = k + m := hf w hw
  obtain ⟨u, hu⟩ := FreeMonoid.exists_ofFn_eq (k := k) (FreeMonoid.ofList (w.toList.take k))
    (by simp [FreeMonoid.length]; omega)
  refine ⟨⟨nisanRow f (FreeMonoid.ofFn u), Submodule.subset_span ⟨u, rfl⟩⟩, fun h => hw ?_⟩
  have h' := congrFun (congrArg Subtype.val h) (FreeMonoid.ofList (w.toList.drop k))
  change coeff (FreeMonoid.ofFn u * _) f = 0 at h'
  rwa [hu, ← FreeMonoid.ofList_append, List.take_append_drop, FreeMonoid.ofList_toList] at h'

/-- For nonzero `f` homogeneous of degree `d`, the first Nisan matrix has rank `1`:
`rank M_0(f) = 1`. -/
theorem rank_nisanMatrix_zero_left [Fintype X] {f : FreeAlgebra K X} {d : ℕ}
    (hd : f.IsHomogeneous d) (hf : f ≠ 0) : (nisanMatrix 0 d f).rank = 1 :=
  le_antisymm ((Matrix.rank_le_card_height _).trans (by simp))
    (one_le_rank_nisanMatrix (by rwa [zero_add]) hf)

/-- For nonzero `f` homogeneous of degree `d`, the last Nisan matrix has rank `1`:
`rank M_d(f) = 1`. -/
theorem rank_nisanMatrix_zero_right [Fintype X] {f : FreeAlgebra K X} {d : ℕ}
    (hd : f.IsHomogeneous d) (hf : f ≠ 0) : (nisanMatrix d 0 f).rank = 1 :=
  le_antisymm ((Matrix.rank_le_card_width _).trans (by simp)) (one_le_rank_nisanMatrix hd hf)

/-- The row space of layer `0` is spanned by the row of the empty word. -/
theorem nisanRowSpace_zero (f : FreeAlgebra K X) : nisanRowSpace f 0 = K ∙ nisanRow f 1 := by
  rw [nisanRowSpace, Set.range_unique, FreeMonoid.ofFn_zero]

section Finite

variable [Fintype X]

/-- A basis of the row space of layer `k`. -/
private noncomputable def rowBasis (f : FreeAlgebra K X) (k : ℕ) :
    Module.Basis (Fin (Module.finrank K (nisanRowSpace f k))) K (nisanRowSpace f k) :=
  Module.finBasis K (nisanRowSpace f k)

/-- A word with a nonzero coefficient. -/
private noncomputable def witness (f : FreeAlgebra K X) : FreeMonoid X :=
  Classical.epsilon fun w => coeff w f ≠ 0

omit [Fintype X] in
private theorem coeff_witness {f : FreeAlgebra K X} (hf : f ≠ 0) : coeff (witness f) f ≠ 0 :=
  Classical.epsilon_spec (exists_coeff_ne_zero hf)

/-- The rescaling making the source vertex the full row and the sink vertex evaluate to one. -/
private noncomputable def rowScale (f : FreeAlgebra K X) (d k : ℕ)
    (i : Fin (Module.finrank K (nisanRowSpace f k))) : K :=
  if k = 0 then nisanRow f 1 (witness f) / (rowBasis f k i : FreeMonoid X → K) (witness f)
  else if k = d then ((rowBasis f k i : FreeMonoid X → K) 1)⁻¹ else 1

omit [Fintype X] in
private theorem smul_eq_nisanRow_one {f : FreeAlgebra K X} (hf : f ≠ 0) {g : FreeMonoid X → K}
    (hg : g ∈ nisanRowSpace f 0) (hg0 : g ≠ 0) :
    g (witness f) ≠ 0 ∧ (nisanRow f 1 (witness f) / g (witness f)) • g = nisanRow f 1 := by
  rw [nisanRowSpace_zero, Submodule.mem_span_singleton] at hg
  obtain ⟨a, rfl⟩ := hg
  have hρ : nisanRow f 1 (witness f) ≠ 0 := by
    simpa [nisanRow] using coeff_witness hf
  have ha : a ≠ 0 := by
    rintro rfl
    exact hg0 (zero_smul K _)
  refine ⟨by simpa using And.intro ha hρ, ?_⟩
  rw [smul_smul]
  convert one_smul K (nisanRow f 1) using 2
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

private theorem rowBasis_apply_one_ne_zero {f : FreeAlgebra K X} {d : ℕ}
    (hd : f.IsHomogeneous d)
    (i : Fin (Module.finrank K (nisanRowSpace f d))) :
    (rowBasis f d i : FreeMonoid X → K) 1 ≠ 0 := by
  intro h
  refine (rowBasis f d).ne_zero i (Subtype.ext (funext fun v => ?_))
  by_cases hv : v.length = 0
  · rw [FreeMonoid.length_eq_zero.mp hv]
    exact h
  · exact apply_eq_zero_of_mem_nisanRowSpace hd (rowBasis f d i).2 (by omega)

private theorem rowScale_ne_zero {f : FreeAlgebra K X} {d : ℕ} (hd : f.IsHomogeneous d)
    (hf : f ≠ 0) (k : ℕ) (i : Fin (Module.finrank K (nisanRowSpace f k))) :
    rowScale f d k i ≠ 0 := by
  unfold rowScale
  split_ifs with hk hkd
  · subst hk
    have hne : (rowBasis f 0 i : FreeMonoid X → K) ≠ 0 := fun h =>
      (rowBasis f 0).ne_zero i (Subtype.ext h)
    have h1 := (smul_eq_nisanRow_one hf (rowBasis f 0 i).2 hne).1
    have h2 : nisanRow f 1 (witness f) ≠ 0 := by simpa [nisanRow] using coeff_witness hf
    exact div_ne_zero h2 h1
  · subst hkd
    exact inv_ne_zero (rowBasis_apply_one_ne_zero hd i)
  · exact one_ne_zero

/-- The rescaled basis vector `i` of the row space of layer `k`. -/
private noncomputable def srow (f : FreeAlgebra K X) (d k : ℕ)
    (i : Fin (Module.finrank K (nisanRowSpace f k))) : FreeMonoid X → K :=
  rowScale f d k i • (rowBasis f k i : FreeMonoid X → K)

omit [Fintype X] in
private theorem shiftBy_mem (f : FreeAlgebra K X) (k : ℕ) (x : X) :
    ∀ g ∈ nisanRowSpace f k, shiftBy x g ∈ nisanRowSpace f (k + 1) :=
  fun _ hg => nisanRowSpace_le_comap_shiftBy f k x hg

/-- The edge coefficients of the optimal ABP. -/
private noncomputable def optWeight (f : FreeAlgebra K X) (d k : ℕ) (x : X)
    (i : Fin (Module.finrank K (nisanRowSpace f k)))
    (j : Fin (Module.finrank K (nisanRowSpace f (k + 1)))) : K :=
  rowScale f d k i *
    (rowBasis f (k + 1)).repr ((shiftBy x).restrict (shiftBy_mem f k x) (rowBasis f k i)) j /
      rowScale f d (k + 1) j

/-- The ABP with one vertex per basis vector of each row space. -/
private noncomputable abbrev optABP (f : FreeAlgebra K X) (d : ℕ) (hd : f.IsHomogeneous d)
    (hf : f ≠ 0) : NoncommABP K X d where
  width k := Module.finrank K (nisanRowSpace f k)
  width_zero := finrank_nisanRowSpace_zero hf
  width_deg := finrank_nisanRowSpace_deg hd hf
  weight k x := optWeight f d k x

private theorem shiftBy_srow {f : FreeAlgebra K X} {d : ℕ} (hd : f.IsHomogeneous d)
    (hf : f ≠ 0) (k : ℕ) (x : X) (i : Fin (Module.finrank K (nisanRowSpace f k))) :
    shiftBy x (srow f d k i) = ∑ j, optWeight f d k x i j • srow f d (k + 1) j := by
  have hsum := (rowBasis f (k + 1)).sum_repr
    ((shiftBy x).restrict (shiftBy_mem f k x) (rowBasis f k i))
  have hval := congrArg Subtype.val hsum
  rw [LinearMap.coe_restrict_apply, Submodule.coe_sum] at hval
  rw [srow, map_smul, ← hval, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj := rowScale_ne_zero hd hf (k + 1) j
  simp only [srow, optWeight, Submodule.coe_smul, smul_smul]
  congr 1
  field_simp

private theorem srow_zero {f : FreeAlgebra K X} {d : ℕ} (hf : f ≠ 0)
    (i : Fin (Module.finrank K (nisanRowSpace f 0))) : srow f d 0 i = nisanRow f 1 := by
  have hne : (rowBasis f 0 i : FreeMonoid X → K) ≠ 0 := fun h =>
    (rowBasis f 0).ne_zero i (Subtype.ext h)
  rw [srow, rowScale, ite_eq_left rfl]
  exact (smul_eq_nisanRow_one hf (rowBasis f 0 i).2 hne).2

private theorem srow_deg_apply_one {f : FreeAlgebra K X} {d : ℕ} (hd : f.IsHomogeneous d)
    (hd0 : d ≠ 0) (i : Fin (Module.finrank K (nisanRowSpace f d))) : srow f d d i 1 = 1 := by
  rw [srow, rowScale, ite_eq_right hd0, ite_eq_left rfl, Pi.smul_apply, smul_eq_mul]
  exact inv_mul_cancel₀ (rowBasis_apply_one_ne_zero hd i)

private theorem nisanRow_ofFn_eq_sum {f : FreeAlgebra K X} {d : ℕ} (hd : f.IsHomogeneous d)
    (hf : f ≠ 0) (k : ℕ) (u : Fin k → X) :
    nisanRow f (FreeMonoid.ofFn u) =
      ∑ i, coeff (FreeMonoid.ofFn u) ((optABP f d hd hf).pre k i) • srow f d k i := by
  induction k with
  | zero =>
    have hw : FreeMonoid.ofFn u = 1 := FreeMonoid.ofFn_zero u
    have hcard : Fintype.card (Fin (Module.finrank K (nisanRowSpace f 0))) = 1 := by
      rw [Fintype.card_fin]
      exact finrank_nisanRowSpace_zero hf
    obtain ⟨i₀, hi₀⟩ := Fintype.card_eq_one_iff.mp hcard
    rw [Fintype.sum_eq_single i₀ (fun i hi => absurd (hi₀ i) hi), hw, srow_zero hf]
    rw [NoncommABP.pre_zero, coeff_one, Finsupp.single_eq_same, one_smul]
  | succ k ih =>
    rw [← Fin.snoc_init_self u, FreeMonoid.ofFn_snoc, ← shiftBy_nisanRow, ih, map_sum]
    simp only [map_smul, shiftBy_srow hd hf, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    exact ((optABP f d hd hf).coeff_pre_succ k j _ _).symm

private theorem polynomial_optABP {f : FreeAlgebra K X} {d : ℕ} (hd : f.IsHomogeneous d)
    (hf : f ≠ 0) (hd0 : d ≠ 0) : (optABP f d hd hf).polynomial = f := by
  refine ext_coeff fun w => ?_
  by_cases hw : w.length = d
  · obtain ⟨u, rfl⟩ := FreeMonoid.exists_ofFn_eq w hw
    have h := congrFun (nisanRow_ofFn_eq_sum hd hf d u) 1
    simp only [nisanRow, mul_one, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      srow_deg_apply_one hd hd0] at h
    rw [h, NoncommABP.polynomial, map_sum]
  · rw [hd.coeff_eq_zero hw, (optABP f d hd hf).isHomogeneous_polynomial.coeff_eq_zero hw]

/-- **Nisan's theorem, exactness** ([Nisan1991NonCommutative], Theorem 1;
[Saptharishi2026Survey], Theorem 11.2 and Exercise 11.2). Every nonzero homogeneous polynomial
of degree `d ≥ 1` is computed by a homogeneous layered ABP whose layer `k` has exactly
`rank M_k(f)` vertices. -/
theorem NoncommABP.exists_width_eq_rank {f : FreeAlgebra K X} {d : ℕ} (hd : f.IsHomogeneous d)
    (hf : f ≠ 0) (hd0 : d ≠ 0) :
    ∃ A : NoncommABP K X d, A.polynomial = f ∧
      ∀ k m, k + m = d → A.width k = (nisanMatrix k m f).rank := by
  refine ⟨optABP f d hd hf, polynomial_optABP hd hf hd0, fun k m hkm => ?_⟩
  subst hkm
  exact (rank_nisanMatrix_eq_finrank_nisanRowSpace hd).symm

/-- **Nisan's theorem** ([Nisan1991NonCommutative], Theorem 1; [Saptharishi2026Survey],
Theorem 11.2). The least size of a homogeneous layered ABP computing a nonzero homogeneous `f` of
degree `d ≥ 1` is `∑_{k ≤ d} rank M_k(f)`, counting every vertex as in Nisan's Theorem 1. The
survey's displayed statement leaves out the final term `rank M_d(f) = 1`. -/
theorem NoncommABP.isLeast_size {f : FreeAlgebra K X} {d : ℕ} (hd : f.IsHomogeneous d)
    (hf : f ≠ 0) (hd0 : d ≠ 0) :
    IsLeast {s | ∃ A : NoncommABP K X d, A.polynomial = f ∧ A.size = s}
      (∑ k ∈ Finset.range (d + 1), (nisanMatrix k (d - k) f).rank) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨A, hA, hw⟩ := NoncommABP.exists_width_eq_rank hd hf hd0
    refine ⟨A, hA, Finset.sum_congr rfl fun k hk => hw k (d - k) ?_⟩
    rw [Finset.mem_range] at hk
    omega
  · rintro s ⟨A, rfl, rfl⟩
    exact A.sum_rank_nisanMatrix_le_size

end Finite

end Cslib.Circuits.Arithmetic
