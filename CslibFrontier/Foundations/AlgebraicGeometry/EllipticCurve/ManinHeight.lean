/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Heights of primitive polynomial triples

Manin's proof of Hasse's bound measures points of a quadratic twist by degrees of polynomial
triples. A triple `w : Fin 3 → k[X]` is primitive if no prime divides all three components, and
its height is the largest degree of a component. Proportional primitive triples have the same
height; the symmetric product of two coprime pairs is primitive, of height the sum of the
heights of the pairs; and the add-sub map of an elliptic curve over `k`, applied to a primitive
triple over `k[X]`, gives a primitive triple of twice the height.

## Main definitions

* `WeierstrassCurve.Manin.IsPrimTriple`: no prime divides all three components.
* `WeierstrassCurve.Manin.hgt`: the largest degree of a component.
* `WeierstrassCurve.Manin.sym2Pair`: the symmetric product `(r r', r s' + s r', s s')`.

## Main results

* `WeierstrassCurve.Manin.hgt_eq_of_smul_eq`: proportional primitive triples have equal heights.
* `WeierstrassCurve.Manin.isPrim_sym2Pair`, `WeierstrassCurve.Manin.hgt_sym2Pair`: the
  symmetric product of coprime pairs.
* `WeierstrassCurve.Manin.isPrim_addSubMap`, `WeierstrassCurve.Manin.hgt_addSubMap`: the add-sub
  map preserves primitivity and doubles the height.

## References

* Yu. I. Manin's elementary proof of Hasse's bound (1956); Hasse's bound is Theorem 9.72 of
  [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020] (p. 351).
-/

@[expose] public section

noncomputable section

open Polynomial

namespace WeierstrassCurve

/-- `addSubMap` commutes with base change of the curve. -/
lemma addSubMap_map {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)
    (f : R →+* S) (i : Fin 3) :
    (W.map f).addSubMap i = MvPolynomial.map f (W.addSubMap i) := by
  fin_cases i <;> simp [addSubMap, map_b₂, map_b₄, map_b₆, map_b₈, map_ofNat]

namespace Manin

variable {k : Type*} [Field k]

/-- A triple over `k[X]` is primitive if no prime divides all three components. -/
def IsPrimTriple (w : Fin 3 → k[X]) : Prop := ∀ π : k[X], Prime π → ¬ ∀ i, π ∣ w i

/-- The height of a triple over `k[X]`: the largest degree of a component. -/
def hgt (w : Fin 3 → k[X]) : ℕ := Finset.univ.sup fun i ↦ (w i).natDegree

/-- The symmetric product `(r r', r s' + s r', s s')` of the pairs `(r, s)` and `(r', s')`. -/
def sym2Pair (r s r' s' : k[X]) : Fin 3 → k[X] := ![r * r', r * s' + s * r', s * s']

/-! ### The height of a triple -/

lemma natDegree_le_hgt (w : Fin 3 → k[X]) (i : Fin 3) : (w i).natDegree ≤ hgt w :=
  Finset.le_sup (f := fun i ↦ (w i).natDegree) (Finset.mem_univ i)

lemma hgt_le_iff {w : Fin 3 → k[X]} {n : ℕ} : hgt w ≤ n ↔ ∀ i, (w i).natDegree ≤ n := by
  simp [hgt, Finset.sup_le_iff]

lemma exists_natDegree_eq_hgt (w : Fin 3 → k[X]) : ∃ i, (w i).natDegree = hgt w := by
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun i ↦ (w i).natDegree)
  exact ⟨i, hi.symm⟩

lemma hgt_eq_of_le_of_le {w : Fin 3 → k[X]} {n : ℕ} (hle : ∀ i, (w i).natDegree ≤ n)
    (hge : ∃ i, n ≤ (w i).natDegree) : hgt w = n := by
  obtain ⟨i, hi⟩ := hge
  exact le_antisymm (hgt_le_iff.2 hle) (hi.trans (natDegree_le_hgt w i))

/-! ### Primitive triples -/

/-- A triple is primitive iff every common divisor of its components is a unit. -/
lemma isPrimTriple_iff {w : Fin 3 → k[X]} :
    IsPrimTriple w ↔ ∀ d : k[X], (∀ i, d ∣ w i) → IsUnit d := by
  constructor
  · intro hw d hd
    by_contra hu
    by_cases h0 : d = 0
    · subst h0
      exact hw X prime_X fun i ↦ (zero_dvd_iff.1 (hd i)) ▸ dvd_zero X
    · obtain ⟨π, hπ, hπd⟩ := WfDvdMonoid.exists_irreducible_factor hu h0
      exact hw π hπ.prime fun i ↦ hπd.trans (hd i)
  · intro h π hπ hdvd
    exact hπ.not_isUnit (h π hdvd)

private lemma natDegree_mul_of_isUnit {a : k[X]} (ha : IsUnit a) (p : k[X]) :
    (a * p).natDegree = p.natDegree := by
  obtain ⟨r, hr, rfl⟩ := Polynomial.isUnit_iff.1 ha
  exact natDegree_C_mul hr.ne_zero

/-- Primitive triples that are proportional over `RatFunc k` have the same height. -/
theorem hgt_eq_of_smul_eq {v w : Fin 3 → k[X]} (hv : IsPrimTriple v) (hw : IsPrimTriple w)
    {t : RatFunc k} (h : t • (fun i ↦ algebraMap k[X] (RatFunc k) (v i)) =
      fun i ↦ algebraMap k[X] (RatFunc k) (w i)) :
    hgt v = hgt w := by
  have hb : algebraMap k[X] (RatFunc k) t.denom ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective k)).2 t.denom_ne_zero
  have hab : IsCoprime t.num t.denom := RatFunc.isCoprime_num_denom t
  have key : ∀ i, t.num * v i = t.denom * w i := by
    intro i
    have hi := congrFun h i
    simp only [Pi.smul_apply, smul_eq_mul] at hi
    rw [← RatFunc.num_div_denom t, div_mul_eq_mul_div, div_eq_iff hb] at hi
    apply RatFunc.algebraMap_injective k
    rw [map_mul, map_mul, hi, mul_comm]
  have hbu : IsUnit t.denom := isPrimTriple_iff.1 hv _ fun i ↦
    hab.symm.dvd_of_dvd_mul_left (Dvd.intro _ (key i).symm)
  have hau : IsUnit t.num := isPrimTriple_iff.1 hw _ fun i ↦
    hab.dvd_of_dvd_mul_left (Dvd.intro _ (key i))
  unfold hgt
  congr 1
  funext i
  rw [← natDegree_mul_of_isUnit hau, key i, natDegree_mul_of_isUnit hbu]

/-! ### The symmetric product of two coprime pairs -/

/-- The symmetric product of two coprime pairs is primitive. -/
theorem isPrim_sym2Pair {r s r' s' : k[X]} (h : IsCoprime r s) (h' : IsCoprime r' s') :
    IsPrimTriple (sym2Pair r s r' s') := by
  intro π hπ hdvd
  have h0 : π ∣ r * r' := hdvd 0
  have h1 : π ∣ r * s' + s * r' := hdvd 1
  have h2 : π ∣ s * s' := hdvd 2
  rcases hπ.dvd_or_dvd h0 with hr | hr'
  · have hs : ¬ π ∣ s := fun hs ↦ hπ.not_isUnit (h.isUnit_of_dvd' hr hs)
    have hs' : π ∣ s' := (hπ.dvd_or_dvd h2).resolve_left hs
    have hsr' : π ∣ s * r' := (dvd_add_right (dvd_mul_of_dvd_left hr s')).1 h1
    exact hπ.not_isUnit (h'.isUnit_of_dvd' ((hπ.dvd_or_dvd hsr').resolve_left hs) hs')
  · have hs' : ¬ π ∣ s' := fun hs' ↦ hπ.not_isUnit (h'.isUnit_of_dvd' hr' hs')
    have hs : π ∣ s := (hπ.dvd_or_dvd h2).resolve_right hs'
    have hrs' : π ∣ r * s' := (dvd_add_left (dvd_mul_of_dvd_left hs r')).1 h1
    exact hπ.not_isUnit (h.isUnit_of_dvd' ((hπ.dvd_or_dvd hrs').resolve_right hs') hs)

/-- For a coprime pair, a coefficient at `max (deg r) (deg s)` is nonzero. -/
private lemma coeff_max_ne_zero {r s : k[X]} (h : IsCoprime r s) :
    r.coeff (max r.natDegree s.natDegree) ≠ 0 ∨ s.coeff (max r.natDegree s.natDegree) ≠ 0 := by
  by_cases hs : s = 0
  · subst hs
    left
    rw [natDegree_zero, max_eq_left (Nat.zero_le _)]
    exact mt leadingCoeff_eq_zero.1 (isCoprime_zero_right.1 h).ne_zero
  by_cases hr : r = 0
  · subst hr
    right
    rw [natDegree_zero, max_eq_right (Nat.zero_le _)]
    exact mt leadingCoeff_eq_zero.1 hs
  rcases le_total r.natDegree s.natDegree with hle | hle
  · right
    rw [max_eq_right hle]
    exact mt leadingCoeff_eq_zero.1 hs
  · left
    rw [max_eq_left hle]
    exact mt leadingCoeff_eq_zero.1 hr

/-- The product of two nonzero linear forms `(a Z + b)(a' Z + b')` is nonzero. -/
private lemma coeffs_mul_ne_zero {a b a' b' : k} (h : a ≠ 0 ∨ b ≠ 0) (h' : a' ≠ 0 ∨ b' ≠ 0) :
    a * a' ≠ 0 ∨ a * b' + b * a' ≠ 0 ∨ b * b' ≠ 0 := by
  by_contra hc
  simp only [not_or, ne_eq, not_not] at hc
  obtain ⟨h0, h1, h2⟩ := hc
  rcases h with ha | hb <;> rcases h' with ha' | hb' <;> simp_all

/-- The height of the symmetric product of two coprime pairs is the sum of their heights. -/
theorem hgt_sym2Pair {r s r' s' : k[X]} (h : IsCoprime r s) (h' : IsCoprime r' s') :
    hgt (sym2Pair r s r' s') =
      max r.natDegree s.natDegree + max r'.natDegree s'.natDegree := by
  set n := max r.natDegree s.natDegree
  set n' := max r'.natDegree s'.natDegree
  have hr : r.natDegree ≤ n := le_max_left _ _
  have hs : s.natDegree ≤ n := le_max_right _ _
  have hr' : r'.natDegree ≤ n' := le_max_left _ _
  have hs' : s'.natDegree ≤ n' := le_max_right _ _
  have hmul : ∀ {p q : k[X]}, p.natDegree ≤ n → q.natDegree ≤ n' →
      (p * q).natDegree ≤ n + n' := fun hp hq ↦ natDegree_mul_le.trans (add_le_add hp hq)
  apply hgt_eq_of_le_of_le
  · intro i
    fin_cases i
    · exact hmul hr hr'
    · exact natDegree_add_le_of_degree_le (hmul hr hs') (hmul hs hr')
    · exact hmul hs hs'
  · rcases coeffs_mul_ne_zero (coeff_max_ne_zero h) (coeff_max_ne_zero h') with h0 | h1 | h2
    · refine ⟨0, le_natDegree_of_ne_zero ?_⟩
      change (r * r').coeff (n + n') ≠ 0
      rwa [coeff_mul_add_eq_of_natDegree_le hr hr']
    · refine ⟨1, le_natDegree_of_ne_zero ?_⟩
      change (r * s' + s * r').coeff (n + n') ≠ 0
      rwa [coeff_add, coeff_mul_add_eq_of_natDegree_le hr hs',
        coeff_mul_add_eq_of_natDegree_le hs hr']
    · refine ⟨2, le_natDegree_of_ne_zero ?_⟩
      change (s * s').coeff (n + n') ≠ 0
      rwa [coeff_mul_add_eq_of_natDegree_le hs hs']

/-! ### The add-sub map doubles the height -/

/-- A homogeneous polynomial of degree `n` over `k`, evaluated at a triple over `k[X]`, has
degree at most `n * hgt w`. -/
private lemma natDegree_eval₂_C_le {P : MvPolynomial (Fin 3) k} {n : ℕ} (hP : P.IsHomogeneous n)
    (w : Fin 3 → k[X]) : (MvPolynomial.eval₂ C w P).natDegree ≤ n * hgt w := by
  rw [MvPolynomial.eval₂_eq']
  refine natDegree_sum_le_of_forall_le _ _ fun d hd ↦ ?_
  refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
  have hn : n = ∑ i, d i := by
    rw [hP.degree_eq_sum_deg_support hd, ← Finsupp.degree_apply, Finsupp.degree_eq_sum]
  calc ∑ i, (w i ^ d i).natDegree ≤ ∑ i, d i * hgt w :=
        Finset.sum_le_sum fun i _ ↦
          natDegree_pow_le.trans (Nat.mul_le_mul_left _ (natDegree_le_hgt w i))
    _ = n * hgt w := by rw [← Finset.sum_mul, hn]

/-- The coefficient at `T ^ (n * H)` of a homogeneous polynomial of degree `n` over `k`,
evaluated at a triple of polynomials of degree at most `H`, is its value at the coefficients at
`T ^ H`. -/
private lemma coeff_eval₂_C_of_isHomogeneous {P : MvPolynomial (Fin 3) k} {n : ℕ}
    (hP : P.IsHomogeneous n) {w : Fin 3 → k[X]} {H : ℕ} (hw : ∀ i, (w i).natDegree ≤ H) :
    (MvPolynomial.eval₂ C w P).coeff (n * H) =
      MvPolynomial.eval (fun i ↦ (w i).coeff H) P := by
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval_eq', finsetSum_coeff]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hn : n = ∑ i, d i := by
    rw [hP.degree_eq_sum_deg_support hd, ← Finsupp.degree_apply, Finsupp.degree_eq_sum]
  have hp : ∀ i, (w i ^ d i).natDegree ≤ d i * H := fun i ↦
    natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hw i))
  rw [coeff_C_mul, Fin.prod_univ_three, Fin.prod_univ_three, hn, Fin.sum_univ_three, add_mul,
    add_mul, coeff_mul_add_eq_of_natDegree_le (natDegree_mul_le.trans (add_le_add (hp 0) (hp 1)))
      (hp 2), coeff_mul_add_eq_of_natDegree_le (hp 0) (hp 1), coeff_pow_of_natDegree_le (hw 0),
    coeff_pow_of_natDegree_le (hw 1), coeff_pow_of_natDegree_le (hw 2)]

/-- The coefficients at `T ^ hgt w` of a primitive triple are not all zero. -/
private lemma coeff_hgt_ne_zero {w : Fin 3 → k[X]} (hw : IsPrimTriple w) :
    (fun i ↦ (w i).coeff (hgt w)) ≠ 0 := by
  intro h0
  obtain ⟨i, hi⟩ := exists_natDegree_eq_hgt w
  have hwi : w i = 0 := by
    rw [← leadingCoeff_eq_zero, leadingCoeff, hi]
    exact congrFun h0 i
  have hH : hgt w = 0 := by rw [← hi, hwi, natDegree_zero]
  refine hw X prime_X fun j ↦ ?_
  have hj : w j = 0 := by
    rw [eq_C_of_natDegree_le_zero ((natDegree_le_hgt w j).trans hH.le), ← hH]
    rw [congrFun h0 j, Pi.zero_apply, map_zero]
  rw [hj]
  exact dvd_zero X

/-- The add-sub map of `E.map C` sends primitive triples to primitive triples. -/
theorem isPrim_addSubMap (E : WeierstrassCurve k) (hΔ : E.Δ ≠ 0) {w : Fin 3 → k[X]}
    (hw : IsPrimTriple w) :
    IsPrimTriple fun j ↦ MvPolynomial.eval w ((E.map C).addSubMap j) := by
  have : E.IsElliptic := ⟨isUnit_iff_ne_zero.2 hΔ⟩
  intro π hπ hdvd
  refine hw π hπ fun i ↦ hπ.dvd_of_dvd_pow (n := 4) ?_
  rw [← addSubMapCoeff_condition (E.map C) w i]
  exact Finset.dvd_sum fun j _ ↦ dvd_mul_of_dvd_right (hdvd j) _

/-- The add-sub map of `E.map C` doubles the height of a primitive triple. -/
theorem hgt_addSubMap (E : WeierstrassCurve k) (hΔ : E.Δ ≠ 0) {w : Fin 3 → k[X]}
    (hw : IsPrimTriple w) :
    hgt (fun j ↦ MvPolynomial.eval w ((E.map C).addSubMap j)) = 2 * hgt w := by
  have : E.IsElliptic := ⟨isUnit_iff_ne_zero.2 hΔ⟩
  have hA : ∀ j, MvPolynomial.eval w ((E.map C).addSubMap j) =
      MvPolynomial.eval₂ C w (E.addSubMap j) := fun j ↦ by
    rw [addSubMap_map, MvPolynomial.eval_map]
  apply hgt_eq_of_le_of_le
  · intro j
    rw [hA]
    exact natDegree_eval₂_C_le (isHomogeneous_addSubMap E j) w
  · obtain ⟨j, hj⟩ := Function.ne_iff.1 (addSubMap_ne_zero E (coeff_hgt_ne_zero hw))
    refine ⟨j, le_natDegree_of_ne_zero ?_⟩
    rw [hA, coeff_eval₂_C_of_isHomogeneous (isHomogeneous_addSubMap E j) (natDegree_le_hgt w)]
    exact hj

end Manin

end WeierstrassCurve
