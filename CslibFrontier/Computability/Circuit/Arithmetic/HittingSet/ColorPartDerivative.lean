/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ColorPart
public import CslibFrontier.Foundations.Data.MvPolynomial.SplitRank
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.MvPolynomial.Tower

/-!
# A derivative-closed space for the colour part

Let `c : σ → Fin r` colour the variables and let `G` be a polynomial of split rank at most `w`
(`MvPolynomial.SplitRankLE`) across the set of variables of every set of colours. Then the colour
part `colorPart c G`, the sum of the monomials of `G` with exactly one variable of each colour,
lies in a space of polynomials that is closed under all partial derivatives and has dimension at
most `2 ^ r * w` (`exists_pderiv_closed_colorPart`). This is [Shpilka2026, Lemma 3.3], and the
bound `2 ^ r * w` is the source's.

The source argues with the coefficient matrices of the colour part: a derivative by a monomial
with set of colours `I` is a row of the matrix that splits the variables by `I`, and this matrix is
a submatrix of the corresponding matrix of `G`. The proof here uses partial evaluations instead,
and needs neither iterated derivatives nor matrices. In particular `G` is not assumed to be
multilinear.

## Proof

The colour part of a product `P * Q`, with `P` in the variables with colours in `I` and `Q` in the
other variables, is the product of the component of `P` that uses every colour of `I` once and
the component of `Q` that uses every other colour once. So the colour part `g` inherits the split
rank of `G` (`splitRankLE_colorPart`).

The space is spanned by the polynomials `ρ I β g`, where `ρ I β` substitutes the constant `β v`
for every variable `v` with a colour in `I`. It contains `g = ρ ∅ β g`. Every monomial of `g`
contains exactly one variable of the colour of `v`, to the first power, so the derivative of
`ρ I β g` by `v` is `0` if the colour of `v` is in `I`, and is otherwise `ρ I' β' g` where `I'`
adds the colour of `v` to `I` and `β'` is `1` at `v` and `0` at the other variables of that
colour. Finally a decomposition `g = ∑ i, p i * q i` across the colours `I` turns under `ρ I β`
into a combination of the `w` polynomials `q i`, so the `2 ^ r * w` polynomials `q i`, over all
`I`, span a space that contains every generator.

## Main results

* `splitRankLE_colorPart`: the colour part inherits the split rank across a set of colours.
* `exists_pderiv_closed_colorPart`: the colour part lies in a derivative-closed space of dimension
  at most `2 ^ r * w`.

## References

* [A. Shpilka, *Polynomial-size hitting sets for multilinear any-order read-once algebraic
  branching programs and for set-multilinear depth-3 circuits with constant-size variable
  sets*][Shpilka2026], Lemma 3.3, §3 p. 8 (unrefereed preprint)
-/

public section

namespace Cslib.Circuits.Arithmetic

open MvPolynomial

section Split

variable {σ R : Type*} [CommSemiring R] {r : ℕ}

private theorem weight_colorWeight_apply (c : σ → Fin r) (d : σ →₀ ℕ) (j : Fin r) :
    Finsupp.weight (colorWeight c) d j = ∑ v ∈ d.support, if c v = j then d v else 0 := by
  rw [Finsupp.weight_apply, Finsupp.coe_sum, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finsupp.smul_apply, colorWeight, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]

private theorem weight_colorWeight_eq_zero {c : σ → Fin r} {d : σ →₀ ℕ} {j : Fin r}
    (h : ∀ v ∈ d.support, c v ≠ j) : Finsupp.weight (colorWeight c) d j = 0 := by
  rw [weight_colorWeight_apply]
  exact Finset.sum_eq_zero fun v hv => ite_eq_right (h v hv)

/-- The colour degree that is one on the colours of `I` and zero elsewhere. -/
private noncomputable def colorInd (I : Finset (Fin r)) : Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun j => if j ∈ I then 1 else 0

private theorem whc_mem_supported {M : Type*} [AddCommMonoid M] {U : Set σ}
    {P : MvPolynomial σ R} (hP : P ∈ supported R U) (w : σ → M) (n : M) :
    weightedHomogeneousComponent w n P ∈ supported R U := by
  classical
  rw [mem_supported] at hP ⊢
  refine subset_trans (fun i hi => ?_) hP
  rw [Finset.mem_coe, mem_vars_iff_mem_support] at hi ⊢
  obtain ⟨d, hd, hid⟩ := hi
  rw [support_weightedHomogeneousComponent] at hd
  exact ⟨d, Finset.mem_of_mem_filter d hd, hid⟩

/-- The colour part of a product across a set of colours is the product of the components that
use every colour on their side once. -/
private theorem colorPart_mul (c : σ → Fin r) (I : Finset (Fin r)) {P Q : MvPolynomial σ R}
    (hP : P ∈ supported R (c ⁻¹' (I : Set (Fin r))))
    (hQ : Q ∈ supported R (c ⁻¹' (I : Set (Fin r)))ᶜ) :
    colorPart c (P * Q) = weightedHomogeneousComponent (colorWeight c) (colorInd I) P *
      weightedHomogeneousComponent (colorWeight c) (colorInd Iᶜ) Q := by
  classical
  ext d
  rw [colorPart, coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul,
    ← Finset.sum_const_zero, ← Finset.sum_ite_irrel]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent,
    ite_zero_mul_ite_zero]
  by_cases h0 : P.coeff x.1 * Q.coeff x.2 = 0
  · rw [h0, ite_self, ite_self]
  have hx1 : ∀ v ∈ x.1.support, c v ∈ I := fun v hv =>
    mem_supported.1 hP (Finset.mem_coe.2 ((mem_vars_iff_mem_support v).2
      ⟨x.1, mem_support_iff.2 (left_ne_zero_of_mul h0), hv⟩))
  have hx2 : ∀ v ∈ x.2.support, c v ∉ I := fun v hv =>
    mem_supported.1 hQ (Finset.mem_coe.2 ((mem_vars_iff_mem_support v).2
      ⟨x.2, mem_support_iff.2 (right_ne_zero_of_mul h0), hv⟩))
  have hw1 : ∀ j ∉ I, Finsupp.weight (colorWeight c) x.1 j = 0 := fun j hj =>
    weight_colorWeight_eq_zero fun v hv e => hj (e ▸ hx1 v hv)
  have hw2 : ∀ j ∈ I, Finsupp.weight (colorWeight c) x.2 j = 0 := fun j hj =>
    weight_colorWeight_eq_zero fun v hv e => hx2 v hv (e ▸ hj)
  refine if_congr ?_ rfl rfl
  rw [← Finset.mem_antidiagonal.1 hx, map_add]
  simp only [Finsupp.ext_iff, Finsupp.add_apply, colorInd, colorOnes,
    Finsupp.equivFunOnFinite_symm_apply_apply, Finset.mem_compl]
  refine ⟨fun h => ⟨fun j => ?_, fun j => ?_⟩, fun h j => ?_⟩
  · have hj := h j
    by_cases hjI : j ∈ I
    · simpa [hjI, hw2 j hjI] using hj
    · simp [hjI, hw1 j hjI]
  · have hj := h j
    by_cases hjI : j ∈ I
    · simp [hjI, hw2 j hjI]
    · simpa [hjI, hw1 j hjI] using hj
  · rw [h.1 j, h.2 j]
    by_cases hjI : j ∈ I <;> simp [hjI]

/-- The colour part of a polynomial inherits its split rank across the variables of a set of
colours. -/
theorem splitRankLE_colorPart (c : σ → Fin r) (I : Finset (Fin r)) {w : ℕ}
    {G : MvPolynomial σ R} (hG : SplitRankLE (c ⁻¹' (I : Set (Fin r))) w G) :
    SplitRankLE (c ⁻¹' (I : Set (Fin r))) w (colorPart c G) := by
  obtain ⟨p, q, hp, hq, rfl⟩ := hG
  refine ⟨fun i => weightedHomogeneousComponent (colorWeight c) (colorInd I) (p i),
    fun i => weightedHomogeneousComponent (colorWeight c) (colorInd Iᶜ) (q i),
    fun i => whc_mem_supported (hp i) _ _, fun i => whc_mem_supported (hq i) _ _, ?_⟩
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => colorPart_mul c I (hp i) (hq i)

end Split

variable {σ F : Type*} [Field F] {r : ℕ}

/-- Every monomial of the colour part is a variable of a given colour times a monomial in the
variables of the other colours. -/
private theorem exists_eq_X_mul_of_mem_support (c : σ → Fin r) {G : MvPolynomial σ F}
    {d : σ →₀ ℕ} (hd : d ∈ (colorPart c G).support) (j : Fin r) :
    ∃ u M, c u = j ∧ M ∈ supported F {x | c x ≠ j} ∧
      monomial d ((colorPart c G).coeff d) = X u * M := by
  classical
  have ha := mem_support_iff.1 hd
  have hwt : Finsupp.weight (colorWeight c) d = colorOnes r := by
    rw [colorPart, coeff_weightedHomogeneousComponent] at ha
    exact (ite_ne_right_iff.1 ha).1
  have hsum : ∑ v ∈ d.support, (if c v = j then d v else 0) = 1 := by
    rw [← weight_colorWeight_apply, hwt]
    rfl
  obtain ⟨u, hu, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum ▸ one_ne_zero)
  have hcu : c u = j := (ite_ne_right_iff.1 hne).1
  rw [← Finset.add_sum_erase _ _ hu, ite_eq_left hcu] at hsum
  have hdu : d u ≠ 0 := Finsupp.mem_support_iff.1 hu
  have hdu1 : d u = 1 := by omega
  have hrest : ∑ v ∈ d.support.erase u, (if c v = j then d v else 0) = 0 := by omega
  refine ⟨u, monomial (d.erase u) ((colorPart c G).coeff d), hcu, ?_, ?_⟩
  · rw [mem_supported, vars_monomial ha, Finsupp.support_erase]
    intro v hv e
    have h := Finset.sum_eq_zero_iff.1 hrest v hv
    rw [ite_eq_left e] at h
    exact Finsupp.mem_support_iff.1 (Finset.mem_of_mem_erase hv) h
  · rw [← pow_one (X u), ← monomial_single_add, ← hdu1, Finsupp.single_add_erase]

/-- The substitution of the constants `β` for the variables with a colour in `I`. -/
private noncomputable def partialEval (c : σ → Fin r) (I : Finset (Fin r)) (β : σ → F) :
    MvPolynomial σ F →ₐ[F] MvPolynomial σ F :=
  aeval fun u => if c u ∈ I then C (β u) else X u

private theorem partialEval_mem_supported (c : σ → Fin r) (I : Finset (Fin r)) (β : σ → F)
    {s : Set σ} {p : MvPolynomial σ F} (hp : p ∈ supported F s) :
    partialEval c I β p ∈ supported F {u | u ∈ s ∧ c u ∉ I} :=
  aeval_mem_of_mem_supported hp _ fun u hu => by
    by_cases h : c u ∈ I
    · simp only [h, ↓reduceIte]
      exact Subalgebra.algebraMap_mem _ (β u)
    · simp only [h, ↓reduceIte]
      exact X_mem_supported.2 ⟨hu, h⟩

private theorem pderiv_eq_zero_of_mem_supported {s : Set σ} {p : MvPolynomial σ F}
    (hp : p ∈ supported F s) {v : σ} (hv : v ∉ s) : pderiv v p = 0 :=
  pderiv_eq_zero_of_notMem_vars fun h => hv (mem_supported.1 hp (Finset.mem_coe.2 h))

private theorem pderiv_partialEval_X_mul [DecidableEq σ] (c : σ → Fin r) {I : Finset (Fin r)}
    (β : σ → F) {v u : σ} (hv : c v ∉ I) (hu : c u = c v) {M : MvPolynomial σ F}
    (hM : M ∈ supported F {x | c x ≠ c v}) :
    pderiv v (partialEval c I β (X u * M)) = partialEval c (insert (c v) I)
      (fun x => if c x = c v then (if x = v then 1 else 0) else β x) (X u * M) := by
  have hXu : partialEval c I β (X u) = X u := by
    rw [partialEval, aeval_X, ite_eq_right (hu ▸ hv)]
  have hXu' : partialEval c (insert (c v) I)
      (fun x => if c x = c v then (if x = v then 1 else 0) else β x) (X u) =
      C (if u = v then 1 else 0) := by
    rw [partialEval, aeval_X, ite_eq_left (hu ▸ Finset.mem_insert_self _ _), ite_eq_left hu]
  have hM' : partialEval c (insert (c v) I)
      (fun x => if c x = c v then (if x = v then 1 else 0) else β x) M = partialEval c I β M :=
    aeval_congr_of_mem_supported hM fun x hx => by
      simp only [Finset.mem_insert, show c x ≠ c v from hx, false_or, ↓reduceIte]
  rw [map_mul (partialEval c _ _), map_mul (partialEval c _ _), hXu, hXu', hM',
    Derivation.leibniz,
    pderiv_eq_zero_of_mem_supported (partialEval_mem_supported c I β hM) fun h => h.1 rfl,
    smul_zero, zero_add, pderiv_X, smul_eq_mul, mul_comm, Pi.single_apply, apply_ite C, C_1, C_0]

/-- The derivative of a partial evaluation of the colour part by a variable of a new colour is
again a partial evaluation of the colour part. -/
private theorem exists_pderiv_partialEval_colorPart (c : σ → Fin r) {I : Finset (Fin r)}
    (β : σ → F) {v : σ} (hv : c v ∉ I) (G : MvPolynomial σ F) :
    ∃ β', pderiv v (partialEval c I β (colorPart c G)) =
      partialEval c (insert (c v) I) β' (colorPart c G) := by
  classical
  refine ⟨fun x => if c x = c v then (if x = v then 1 else 0) else β x, ?_⟩
  rw [← support_sum_monomial_coeff (colorPart c G)]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨u, M, hu, hM, h⟩ := exists_eq_X_mul_of_mem_support c hd (c v)
  rw [h]
  exact pderiv_partialEval_X_mul c β hv hu hM

/-- **A derivative-closed space for the colour part** [Shpilka2026, Lemma 3.3]. If `G` has split
rank at most `w` across the variables of every set of colours, then its colour part lies in a
space of polynomials that is closed under partial derivatives and has dimension at most
`2 ^ r * w`. -/
theorem exists_pderiv_closed_colorPart (c : σ → Fin r) {w : ℕ} {G : MvPolynomial σ F}
    (hG : ∀ I : Finset (Fin r), MvPolynomial.SplitRankLE (c ⁻¹' (I : Set (Fin r))) w G) :
    ∃ V : Submodule F (MvPolynomial σ F), (∀ i, ∀ p ∈ V, MvPolynomial.pderiv i p ∈ V) ∧
      Module.Finite F V ∧ Module.finrank F V ≤ 2 ^ r * w ∧ colorPart c G ∈ V := by
  set g := colorPart c G with hg
  let V : Submodule F (MvPolynomial σ F) := Submodule.span F
    (Set.range fun x : Finset (Fin r) × (σ → F) => partialEval c x.1 x.2 g)
  choose p q hp hq hpq using fun I => splitRankLE_colorPart c I (hG I)
  let W : Submodule F (MvPolynomial σ F) := Submodule.span F
    (Set.range fun x : Finset (Fin r) × Fin w => q x.1 x.2)
  have hVW : V ≤ W := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨I, β⟩, rfl⟩
    change partialEval c I β g ∈ W
    rw [hg, hpq I, map_sum]
    refine W.sum_mem fun i _ => ?_
    have hpi : partialEval c I β (p I i) = C (aeval β (p I i)) := by
      rw [← algebraMap_eq, ← aeval_algebraMap_apply]
      exact aeval_congr_of_mem_supported (hp I i) fun u hu => by
        simp only [show c u ∈ I from hu, ↓reduceIte, Function.comp_apply, algebraMap_eq]
    have hqi : partialEval c I β (q I i) = q I i :=
      (aeval_congr_of_mem_supported (hq I i) fun u hu => by
        simp only [show c u ∉ I from hu, ↓reduceIte]).trans (aeval_X_left_apply _)
    rw [map_mul, hpi, hqi, ← smul_eq_C_mul]
    exact W.smul_mem _ (Submodule.subset_span ⟨(I, i), rfl⟩)
  have hWfin : Module.Finite F W := Module.Finite.span_of_finite F (Set.finite_range _)
  have hWrank : Module.finrank F W ≤ 2 ^ r * w := by
    refine (finrank_range_le_card _).trans_eq ?_
    rw [Fintype.card_prod, Fintype.card_finset, Fintype.card_fin, Fintype.card_fin]
  refine ⟨V, fun v f hf => ?_, Submodule.finiteDimensional_of_le hVW,
    (Submodule.finrank_mono hVW).trans hWrank, Submodule.subset_span ⟨(∅, 0), ?_⟩⟩
  · induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨⟨I, β⟩, rfl⟩ := hf
      change pderiv v (partialEval c I β g) ∈ V
      by_cases hI : c v ∈ I
      · rw [pderiv_eq_zero_of_mem_supported
          (partialEval_mem_supported c I β (s := Set.univ) (by rw [supported_univ]; trivial))
          fun h => h.2 hI]
        exact V.zero_mem
      · obtain ⟨β', h⟩ := exists_pderiv_partialEval_colorPart c β hI G
        rw [hg, h]
        exact Submodule.subset_span ⟨(insert (c v) I, β'), rfl⟩
    | zero => rw [map_zero]; exact V.zero_mem
    | add f₁ f₂ _ _ h₁ h₂ => rw [map_add]; exact V.add_mem h₁ h₂
    | smul a f _ h => rw [Derivation.map_smul]; exact V.smul_mem a h
  · change partialEval c ∅ 0 g = g
    simp only [partialEval, Finset.notMem_empty, ↓reduceIte, aeval_X_left_apply]

end Cslib.Circuits.Arithmetic
