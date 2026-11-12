/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.Basic
public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ColorComponentEval
public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ColorPartDerivative
import CslibFrontier.Foundations.Data.MvPolynomial.Substitution

/-!
# Hitting colour-homogeneous polynomials of any bounded degree per colour

Let `c : Fin n → Fin r` colour the variables and let `g` be a nonzero polynomial that is
homogeneous of a colour degree `ε` with `ε i ≤ δ` for every colour `i`, and of split rank at most
`w` (`MvPolynomial.SplitRankLE`) across the variables of every set of colours. Then `g` does not
vanish at a point of the explicit set `colorHittingSet F c w D δ`, for every `D ≥ g.totalDegree`
(`exists_mem_colorHittingSet_eval_ne_zero`).

When `ε i ≤ 1` for every `i` the polynomial lies in a derivative-closed space of dimension
`2 ^ r * w` [Shpilka2026, Lemma 3.3], so the logarithmic curve hits it. With degree two in some
colour this fails: a product over the colours of sums of squares of the variables has split rank
one and a space of partial derivatives of exponential dimension. The remedy is a recursion on
`δ` that lowers every positive entry of `ε` by one. Let `κ` be the indicator of the colours `i`
with `ε i ≥ 1`. Choosing one variable of each such colour from a monomial of `g`, the iterated
derivative `q` of `g` along these variables is not zero, has colour degree `ε - κ` with entries
at most `δ - 1`, and inherits the split rank of `g`: by recursion it does not vanish at a point
`b`. By Taylor's formula the value `q b` is a coefficient of the component of colour degree `κ`
of `g (X + b)`. This component is therefore not zero, it has at most one variable of each colour
and inherits the split rank of `g`, so the logarithmic curve hits it at a point `a`, and its
values are reached from values of `g (X + b)` by finite differences
(`exists_eval_ne_zero_of_eval_colorComponent_ne_zero`): `g` does not vanish at `z • (y ⊙ a) + b`
for a natural number `z ≤ D` and a zero-one vector `y` indexed by the colours.

This argument is not taken from a source and has not been refereed. The size of the
hitting set grows exponentially in the degree `δ` (`card_colorHittingSet_le`).

## Main definitions

* `colorHittingSet`: the hitting set, by recursion on the bound `δ` on the colour degree.

## Main results

* `exists_mem_colorHittingSet_eval_ne_zero`: the hitting statement above.
* `card_colorHittingSet_le`: the size of the hitting set.

## References

* [A. Shpilka, *Polynomial-size hitting sets for multilinear any-order read-once algebraic
  branching programs and for set-multilinear depth-3 circuits with constant-size variable
  sets*][Shpilka2026], §3 and §4 (unrefereed preprint)
-/

public section

namespace Cslib.Circuits.Arithmetic

open MvPolynomial

section ColorDegree

variable {σ F : Type*} [CommSemiring F] {r : ℕ}

/-- The entries of the colour degree of a monomial add up to its degree. -/
private theorem sum_weight_colorWeight (c : σ → Fin r) (d : σ →₀ ℕ) :
    ∑ j, Finsupp.weight (colorWeight c) d j = d.sum fun _ e => e := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    colorWeight, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  simp

/-- A polynomial that is homogeneous of a colour degree has total degree at most the sum of the
entries of the colour degree. -/
private theorem totalDegree_le_sum_of_isWeightedHomogeneous_colorWeight (c : σ → Fin r)
    {ε : Fin r →₀ ℕ} {p : MvPolynomial σ F} (hp : IsWeightedHomogeneous (colorWeight c) p ε) :
    p.totalDegree ≤ ∑ i, ε i :=
  Finset.sup_le fun d hd => by rw [← sum_weight_colorWeight c, hp (mem_support_iff.1 hd)]

/-- A polynomial that is homogeneous of a colour degree with entries at most one has total degree
at most the number of colours. -/
theorem totalDegree_le_of_isWeightedHomogeneous_colorWeight (c : σ → Fin r)
    {ε : Fin r →₀ ℕ} (hε : ∀ i, ε i ≤ 1) {p : MvPolynomial σ F}
    (hp : IsWeightedHomogeneous (colorWeight c) p ε) : p.totalDegree ≤ r :=
  (totalDegree_le_sum_of_isWeightedHomogeneous_colorWeight c hp).trans
    ((Finset.sum_le_sum fun j _ => hε j).trans_eq (by simp))

/-- A monomial of colour degree positive at a colour has a variable of that colour. -/
private theorem exists_color_eq_of_weight_colorWeight_pos (c : σ → Fin r) {d : σ →₀ ℕ}
    {i : Fin r} (h : 1 ≤ Finsupp.weight (colorWeight c) d i) : ∃ v, c v = i ∧ 1 ≤ d v := by
  classical
  by_contra! hv
  have h0 : Finsupp.weight (colorWeight c) d i = 0 := by
    rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun v _ => ?_
    by_cases hcv : c v = i
    · simp [Nat.lt_one_iff.1 (hv v hcv)]
    · simp [colorWeight, hcv]
  omega

end ColorDegree

variable (F : Type*) [Field F] [CharZero F] {n r : ℕ}

open scoped Classical in
/-- The hitting set for the polynomials that are homogeneous of a colour degree with entries at
most `δ`, of split rank at most `w` across every set of colours and of total degree at most `D`.
For `δ = 0` it is the origin. For `δ + 1` its points are
`fun v => (z : F) * ((y (c v) : ℕ) : F) * a v + b v`, the point `z • (y ⊙ a) + b`, for a point
`b` of the set for `δ`, a point `a` of the logarithmic curve `logHittingSet F n (2 ^ r * w) r`,
a natural number `z ≤ D` and a zero-one vector `y : Fin r → Fin 2` indexed by the colours. -/
noncomputable def colorHittingSet (c : Fin n → Fin r) (w D : ℕ) : ℕ → Finset (Fin n → F)
  | 0 => {0}
  | δ + 1 => (colorHittingSet c w D δ ×ˢ logHittingSet F n (2 ^ r * w) r ×ˢ
      Finset.range (D + 1) ×ˢ (Finset.univ : Finset (Fin r → Fin 2))).image
      fun ⟨b, a, z, y⟩ v => (z : F) * ((y (c v) : ℕ) : F) * a v + b v

/-- **Hitting colour-homogeneous polynomials of bounded degree per colour.** Let `g` be a nonzero
polynomial, homogeneous of a colour degree with entries at most `δ`, of split rank at most `w`
across the variables of every set of colours and of total degree at most `D`. Then `g` does not
vanish at a point of `colorHittingSet F c w D δ`. -/
theorem exists_mem_colorHittingSet_eval_ne_zero (c : Fin n → Fin r) {ε : Fin r →₀ ℕ} {δ w : ℕ}
    (hε : ∀ i, ε i ≤ δ) {g : MvPolynomial (Fin n) F} (hg0 : g ≠ 0)
    (hg : MvPolynomial.IsWeightedHomogeneous (colorWeight c) g ε)
    (hsplit : ∀ I : Finset (Fin r), MvPolynomial.SplitRankLE (c ⁻¹' (I : Set (Fin r))) w g)
    {D : ℕ} (hD : g.totalDegree ≤ D) :
    ∃ x ∈ colorHittingSet F c w D δ, MvPolynomial.eval x g ≠ 0 := by
  classical
  induction δ generalizing ε g with
  | zero =>
    -- The colour degree is zero, so `g` is a nonzero constant.
    have hC := totalDegree_eq_zero_iff_eq_C.1 <| Nat.le_zero.1 <|
      (totalDegree_le_sum_of_isWeightedHomogeneous_colorWeight c hg).trans
        (Finset.sum_nonpos fun i _ => hε i)
    refine ⟨0, Finset.mem_singleton_self _, fun h => hg0 ?_⟩
    rw [hC, eval_C] at h
    rw [hC, h, C_0]
  | succ δ ih =>
    -- A monomial `d` of `g`, and a variable `v i` of each colour `i` that occurs in it.
    obtain ⟨d, hd⟩ := ne_zero_iff.1 hg0
    choose v hcv hdv using fun i : ε.support => exists_color_eq_of_weight_colorWeight_pos c
      (d := d) (i := i) <| by
        rw [hg hd]
        exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 i.2)
    set α : Fin ε.support.card → Fin n := fun j => v (ε.support.equivFin.symm j) with hα
    have hinj : Function.Injective α := fun i j h => ε.support.equivFin.symm.injective <|
      Subtype.ext <| by rw [← hcv, ← hcv, show v _ = v _ from h]
    set μ : Fin n →₀ ℕ := ∑ j, Finsupp.single (α j) 1 with hμ
    have hμd : μ ≤ d := fun u => by
      rw [hμ, Finsupp.finsetSum_apply]
      by_cases hu : ∃ j, α j = u
      · obtain ⟨j, rfl⟩ := hu
        rw [Finset.sum_eq_single j (fun i _ hi => Finsupp.single_eq_of_ne (hinj.ne hi.symm))
          (fun h => absurd (Finset.mem_univ j) h), Finsupp.single_eq_same]
        exact hdv _
      · rw [Finset.sum_eq_zero fun j _ => Finsupp.single_eq_of_ne fun h => hu ⟨j, h.symm⟩]
        exact Nat.zero_le _
    -- The indicator `κ` of the colours that occur is the colour degree of `∏ i, X (v i)`.
    set κ : Fin r →₀ ℕ := ∑ i ∈ ε.support, Finsupp.single i 1 with hκ
    have hκε : ∀ i, κ i = if ε i = 0 then 0 else 1 := fun i => by
      simp [hκ, Finsupp.finsetSum_apply, Finsupp.single_apply]
    have hones : ∑ j, colorWeight c (α j) = κ := by
      simp only [colorWeight, hα, hcv]
      exact (Equiv.sum_comp ε.support.equivFin.symm fun i => Finsupp.single (i : Fin r) 1).trans
        (Finset.sum_coe_sort ε.support fun i => Finsupp.single i 1)
    have hwμ : Finsupp.weight (colorWeight c) μ = κ := by
      rw [hμ, map_sum, ← hones]
      exact Finset.sum_congr rfl fun i _ => (Finsupp.weight_single _ _ _).trans (one_smul _ _)
    have hle : κ ≤ ε := fun i => by rw [hκε]; split <;> omega
    have hκ1 : ∀ i, κ i ≤ 1 := fun i => by rw [hκε]; split <;> omega
    have hε' : ∀ i, (ε - κ) i ≤ δ := fun i => by
      have := hε i
      rw [Finsupp.tsub_apply, hκε]
      split <;> omega
    have hgdeg : ∑ i, ε i ≤ g.totalDegree := by
      rw [← hg hd, sum_weight_colorWeight]
      exact le_totalDegree (mem_support_iff.2 hd)
    -- The derivative `q` of `g` along the `v i` is nonzero of lower colour degree: hit it at `b`.
    set q := iteratedPDeriv α g with hq
    have hq0 : q ≠ 0 := fun h => by
      refine (coeff_iteratedPDeriv_ne_zero_iff α g (d - μ)).2 ?_ (by rw [← hq, h]; rfl)
      rwa [← hμ, tsub_add_cancel_of_le hμd]
    have hqhom : IsWeightedHomogeneous (colorWeight c) q (ε - κ) :=
      IsWeightedHomogeneous.iteratedPDeriv (by rwa [hones, tsub_add_cancel_of_le hle])
    obtain ⟨b, hb, hbq⟩ := ih hε' hq0 hqhom (fun I => (hsplit I).iteratedPDeriv α) <|
      (totalDegree_le_sum_of_isWeightedHomogeneous_colorWeight c hqhom).trans <|
        (Finset.sum_le_sum fun i _ => by rw [Finsupp.tsub_apply]; exact Nat.sub_le _ _).trans <|
          hgdeg.trans hD
    -- By Taylor's formula the component `p` of colour degree `κ` of `P = g (X + b)` is not zero.
    set P := shift b g with hP
    have hPμ : P.coeff μ ≠ 0 := by
      have h := (coeff_iteratedPDeriv_ne_zero_iff α P 0).1
        (by rwa [hP, iteratedPDeriv_shift, coeff_zero_shift])
      rwa [zero_add] at h
    set p := colorComponent c κ P with hp
    have hp0 : p ≠ 0 := fun h => hPμ <| by
      have hc : p.coeff μ = P.coeff μ := by
        simp only [hp, colorComponent, coeff_weightedHomogeneousComponent, hwμ, ↓reduceIte]
      rw [← hc, h]
      rfl
    -- It has at most one variable of each colour: hit it at a point `a` of the curve.
    have hphom : IsWeightedHomogeneous (colorWeight c) p κ :=
      weightedHomogeneousComponent_isWeightedHomogeneous _ _
    obtain ⟨V, hV, hfin, hrank, hpV⟩ := exists_pderiv_closed_of_colorHomogeneous c hκ1 hphom
      fun I => splitRankLE_colorComponent c κ I ((hsplit I).shift b)
    obtain ⟨a, ha, hap⟩ := isHittingSet_logHittingSet (2 ^ r * w) r p
      ⟨totalDegree_le_of_isWeightedHomogeneous_colorWeight c hκ1 hphom, V, hV, hfin, hrank, hpV⟩
      hp0
    -- Go back from the component to `P`, and from `P` to `g`.
    have hPdeg : P.totalDegree ≤ g.totalDegree := totalDegree_aeval_le (fun i =>
      (totalDegree_add _ _).trans (max_le (totalDegree_X i).le (by rw [totalDegree_C]; omega))) g
    obtain ⟨z, hz, y, hy, hzy⟩ := exists_eval_ne_zero_of_eval_colorComponent_ne_zero c κ
      (Λ := (Finset.range (D + 1)).image Nat.cast) (G := P) (x := a)
      (by rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]; omega) hap
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hz
    rw [hP, eval_shift] at hzy
    refine ⟨_, Finset.mem_image.2
      ⟨(b, a, m, fun i => ⟨y i, Nat.lt_succ_of_le ((hy i).trans (hκ1 i))⟩), ?_, rfl⟩, hzy⟩
    simp only [Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨hb, ha, hm⟩

/-- The size of the hitting set `colorHittingSet F c w D δ`: polynomial in the number of
variables, the split rank and the total degree, for fixed `r` and `δ`. -/
theorem card_colorHittingSet_le (c : Fin n → Fin r) (w D δ : ℕ) :
    (colorHittingSet F c w D δ).card ≤
      ((r * (n * (2 ^ r * w) ^ 2 + 2 ^ r * w) + 1) * (D + 1) * 2 ^ r) ^ δ := by
  classical
  induction δ with
  | zero => simp [colorHittingSet]
  | succ δ ih =>
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_product, Finset.card_product, Finset.card_product, Finset.card_range,
      Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, pow_succ]
    exact Nat.mul_le_mul ih <|
      (Nat.mul_le_mul_right _ (card_logHittingSet_le (F := F) _ _)).trans_eq (mul_assoc _ _ _).symm

end Cslib.Circuits.Arithmetic
