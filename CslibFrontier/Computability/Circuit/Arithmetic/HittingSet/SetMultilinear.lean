/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.BoundedDegreeShifts
public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.SetPartitioned
public import CslibFrontier.Foundations.Data.MvPolynomial.WeightedHomogeneous

/-!
# Hitting sets for set-multilinear depth-three circuits with small variable sets

The variables are `x (j, i)`, `j : Fin n`, `i : Fin d`: `n` blocks of `d` variables each. Over a
field of characteristic zero there is an explicit set of points, of size
`poly (n, d, s) * (d + 1) ^ (⌊lg s⌋ + 1)`, on which no nonzero polynomial
`∑ i < s, ∏ j < n, ℓ i j` vanishes, where `ℓ i j` is a linear form in the variables of block `j`
(`isHittingSet_setMultilinearHittingSet_sum_prod`). This is Theorem 1.2 of Shpilka
[Shpilka2026] in characteristic zero. The source also covers positive characteristic, by a
hitting set that is not in the library.

The class that is actually hit is larger (`isHittingSet_setMultilinearHittingSet`): the
set-partitioned polynomials (`MvPolynomial.IsSetPartitioned`) of split rank at most `s` across
every union of blocks.

## Proof

Let `f` be nonzero in the class. The substitution `blockPower`, `x (j, i) ↦ x j ^ (i + 1)`,
maps the monomials of `f` to distinct monomials (`weight_blockWeight_injOn`), so
`q = blockPower f` is nonzero, of individual degree at most `d`
(`degreeOf_blockPower_le`) and of split rank at most `s` across every set of variables
(`SplitRankLE.blockPower`). Some shift `b` from `boundedDegreeShifts` gives `q (x + b)` a
monomial with at most `⌊lg s⌋` variables. For the point `a = (b j ^ (i + 1))`,
`q (x + b) = f (X + a) (ρ)` with `ρ (j, i) = (x j + b j) ^ (i + 1) - b j ^ (i + 1)`, a multiple
of `x j` (`shift_blockPower`). So a monomial of `q (x + b)` contains a variable of every block
that meets some monomial of `f (X + a)`, and `f (X + a)` has a monomial with at most `⌊lg s⌋`
variables (`exists_mem_support_shift_blockPowerPoint`). The passage from this shift to a point
is `exists_mem_setPartitionedHittingSet_eval_ne_zero` ([Shpilka2026], Lemma 3.4).

The shifts are not those of the source, which cites Forbes, Saptharishi and Shpilka for them;
see `BoundedDegreeShifts`.

## Main definitions

* `blockPower`, `blockPowerPoint`: the substitution `x (j, i) ↦ x j ^ (i + 1)` and the point
  `(b j ^ (i + 1))`.
* `setMultilinearHittingSet`: the hitting set.

## Main results

* `isHittingSet_setMultilinearHittingSet`: the hitting set for set-partitioned polynomials of
  split rank at most `s` across every union of blocks.
* `isHittingSet_setMultilinearHittingSet_sum_prod`: [Shpilka2026, Theorem 1.2], in
  characteristic zero.
* `card_setMultilinearHittingSet_le`: the size of the set.

## References

* [A. Shpilka, *Polynomial-size hitting sets for multilinear any-order read-once algebraic
  branching programs and for set-multilinear depth-3 circuits with constant-size variable
  sets*][Shpilka2026], Theorem 1.2 and its proof in §3.1 (unrefereed preprint)
-/

public section

namespace Cslib.Circuits.Arithmetic

open Finset MvPolynomial

variable {F : Type*} [Field F] {n d : ℕ}

/-! ### The substitution of powers -/

/-- The weight of the variable `x (j, i)` under `blockPower`: the exponent vector of
`x j ^ (i + 1)`. -/
noncomputable def blockWeight (v : Fin n × Fin d) : Fin n →₀ ℕ := Finsupp.single v.1 (v.2.val + 1)

variable (F n d) in
/-- The substitution `x (j, i) ↦ x j ^ (i + 1)`. -/
noncomputable def blockPower : MvPolynomial (Fin n × Fin d) F →ₐ[F] MvPolynomial (Fin n) F :=
  aeval fun v => monomial (blockWeight v) 1

/-- The point `(b j ^ (i + 1))`, at which `blockPower f` takes the value of `f` at `b`. -/
def blockPowerPoint (b : Fin n → F) : Fin n × Fin d → F := fun v => b v.1 ^ (v.2.val + 1)

theorem blockPower_X (v : Fin n × Fin d) :
    blockPower F n d (X v) = X v.1 ^ (v.2.val + 1) := by
  rw [blockPower, aeval_X, blockWeight, X_pow_eq_monomial]

/-- The weight of a monomial with at most one variable of each block, to the first power, is
`i + 1` at every block `j` of which the monomial contains the variable `x (j, i)`. -/
private theorem weight_blockWeight_apply {m : Fin n × Fin d →₀ ℕ} (h1 : ∀ v, m v ≤ 1)
    (hinj : Set.InjOn Prod.fst (m.support : Set (Fin n × Fin d))) {v : Fin n × Fin d}
    (hv : v ∈ m.support) : Finsupp.weight blockWeight m v.1 = v.2.val + 1 := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.finsetSum_apply, sum_eq_single_of_mem v hv]
  · rw [le_antisymm (h1 v) (Finsupp.mem_support_iff.1 hv).bot_lt]
    simp [blockWeight]
  · intro u hu huv
    have : u.1 ≠ v.1 := fun h => huv (hinj hu hv h)
    simp [blockWeight, this]

/-- If the weight of a monomial is not zero at a block, the monomial contains a variable of the
block. -/
private theorem exists_mem_support_of_weight_blockWeight_ne_zero {m : Fin n × Fin d →₀ ℕ}
    {j : Fin n} (h : Finsupp.weight blockWeight m j ≠ 0) : ∃ v ∈ m.support, v.1 = j := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.finsetSum_apply] at h
  obtain ⟨v, hv, hvj⟩ := exists_ne_zero_of_sum_ne_zero h
  refine ⟨v, hv, by_contra fun hne => hvj ?_⟩
  simp [blockWeight, hne]

/-- The substitution `blockPower` maps distinct monomials with at most one variable of each
block, to the first power, to distinct monomials. -/
theorem weight_blockWeight_injOn :
    Set.InjOn (Finsupp.weight (blockWeight (n := n) (d := d)))
      {m | (∀ v, m v ≤ 1) ∧ Set.InjOn Prod.fst (m.support : Set (Fin n × Fin d))} := by
  have key : ∀ m m' : Fin n × Fin d →₀ ℕ, (∀ v, m v ≤ 1) →
      Set.InjOn Prod.fst (m.support : Set (Fin n × Fin d)) → (∀ v, m' v ≤ 1) →
      Set.InjOn Prod.fst (m'.support : Set (Fin n × Fin d)) →
      Finsupp.weight blockWeight m = Finsupp.weight blockWeight m' →
      m.support ⊆ m'.support := by
    intro m m' h1 hinj h1' hinj' hw v hv
    have hwv := weight_blockWeight_apply h1 hinj hv
    obtain ⟨u, hu, huv⟩ := exists_mem_support_of_weight_blockWeight_ne_zero
      (m := m') (j := v.1) (by rw [← hw, hwv]; exact Nat.succ_ne_zero _)
    have hwu := weight_blockWeight_apply h1' hinj' hu
    rw [huv, ← hw, hwv] at hwu
    obtain rfl : u = v := Prod.ext huv (Fin.ext (Nat.succ_injective hwu.symm))
    exact hu
  rintro m ⟨h1, hinj⟩ m' ⟨h1', hinj'⟩ hw
  have hs : m.support = m'.support :=
    (key m m' h1 hinj h1' hinj' hw).antisymm (key m' m h1' hinj' h1 hinj hw.symm)
  ext v
  by_cases hv : v ∈ m.support
  · rw [le_antisymm (h1 v) (Finsupp.mem_support_iff.1 hv).bot_lt,
      le_antisymm (h1' v) (Finsupp.mem_support_iff.1 (hs ▸ hv)).bot_lt]
  · rw [Finsupp.notMem_support_iff.1 hv, Finsupp.notMem_support_iff.1 (hs ▸ hv)]

variable {f : MvPolynomial (Fin n × Fin d) F}

/-- A monomial of `blockPower f` is the image of a monomial of `f`. -/
private theorem exists_weight_eq_of_mem_support_blockPower {μ : Fin n →₀ ℕ}
    (hμ : μ ∈ (blockPower F n d f).support) :
    ∃ m ∈ f.support, Finsupp.weight blockWeight m = μ := by
  classical
  rw [mem_support_iff, blockPower, MvPolynomial.coeff_aeval_monomial] at hμ
  have h0 : weightedHomogeneousComponent blockWeight μ f ≠ 0 := fun h => hμ (by rw [h, map_zero])
  obtain ⟨m, hm⟩ := support_nonempty.2 h0
  rw [support_weightedHomogeneousComponent, mem_filter] at hm
  exact ⟨m, hm.1, hm.2⟩

/-- `blockPower` is injective on set-partitioned polynomials. -/
theorem blockPower_ne_zero (hf : IsSetPartitioned Prod.fst f) (hf0 : f ≠ 0) :
    blockPower F n d f ≠ 0 := by
  classical
  obtain ⟨m, hm⟩ := support_nonempty.2 hf0
  refine fun h => mem_support_iff.1 hm ?_
  have hc : (blockPower F n d f).coeff (Finsupp.weight blockWeight m) = 0 := by
    rw [h]
    simp
  rw [blockPower, MvPolynomial.coeff_aeval_monomial] at hc
  have hcomp : weightedHomogeneousComponent blockWeight (Finsupp.weight blockWeight m) f =
      monomial m (f.coeff m) := by
    ext m'
    rw [coeff_weightedHomogeneousComponent, coeff_monomial]
    by_cases hm' : m' ∈ f.support
    · by_cases hmm : m = m'
      · subst hmm
        simp
      · have hne : Finsupp.weight blockWeight m' ≠ Finsupp.weight blockWeight m :=
          fun h => hmm (weight_blockWeight_injOn (hf m hm) (hf m' hm') h.symm)
        simp [hmm, hne]
    · have hne : m ≠ m' := fun h => hm' (h ▸ hm)
      simp [notMem_support_iff.1 hm', hne]
  rw [hcomp, eval_monomial] at hc
  simpa using hc

/-- `blockPower f` has individual degree at most `d` for a set-partitioned `f`. -/
theorem degreeOf_blockPower_le (hf : IsSetPartitioned Prod.fst f) (j : Fin n) :
    (blockPower F n d f).degreeOf j ≤ d := by
  refine degreeOf_le_iff.2 fun μ hμ => ?_
  obtain ⟨m, hm, rfl⟩ := exists_weight_eq_of_mem_support_blockPower hμ
  by_cases h0 : Finsupp.weight blockWeight m j = 0
  · rw [h0]
    exact Nat.zero_le d
  · obtain ⟨v, hv, rfl⟩ := exists_mem_support_of_weight_blockWeight_ne_zero h0
    rw [weight_blockWeight_apply (hf m hm).1 (hf m hm).2 hv]
    exact v.2.isLt

/-- `blockPower` maps a sum of `w` products across a union of blocks to a sum of `w` products
across the corresponding variables. -/
theorem _root_.MvPolynomial.SplitRankLE.blockPower {U : Set (Fin n)} {w : ℕ}
    (h : SplitRankLE (Prod.fst ⁻¹' U) w f) : SplitRankLE U w (blockPower F n d f) := by
  obtain ⟨p, q, hp, hq, rfl⟩ := h
  have hmem : ∀ (S : Set (Fin n)), ∀ v ∈ Prod.fst ⁻¹' S,
      (monomial (blockWeight (d := d) v) 1 : MvPolynomial (Fin n) F) ∈ supported F S :=
    fun S v hv => by
      have hX : (X v.1 : MvPolynomial (Fin n) F) ∈ supported F S :=
        Algebra.subset_adjoin ⟨v.1, hv, rfl⟩
      rw [blockWeight, ← X_pow_eq_monomial]
      exact pow_mem hX _
  exact ⟨fun i => Cslib.Circuits.Arithmetic.blockPower F n d (p i),
    fun i => Cslib.Circuits.Arithmetic.blockPower F n d (q i),
    fun i => aeval_mem_of_mem_supported (hp i) _ (hmem U),
    fun i => aeval_mem_of_mem_supported (hq i) _ (hmem Uᶜ), by simp only [map_sum, map_mul]⟩

/-! ### Transfer of a shift -/

/-- A shift `b` of `blockPower f` is a substitution into the shift of `f` by the point
`(b j ^ (i + 1))`: the variable `x (j, i)` is replaced by
`(x j + b j) ^ (i + 1) - b j ^ (i + 1)`. -/
theorem shift_blockPower (b : Fin n → F) (f : MvPolynomial (Fin n × Fin d) F) :
    shift b (blockPower F n d f) =
      aeval (fun v : Fin n × Fin d => (X v.1 + C (b v.1)) ^ (v.2.val + 1) -
        (C (b v.1 ^ (v.2.val + 1)) : MvPolynomial (Fin n) F)) (shift (blockPowerPoint b) f) := by
  have h : (shift b).comp (blockPower F n d) =
      (aeval fun v : Fin n × Fin d => (X v.1 + C (b v.1)) ^ (v.2.val + 1) -
        (C (b v.1 ^ (v.2.val + 1)) : MvPolynomial (Fin n) F)).comp (shift (blockPowerPoint b)) :=
    algHom_ext fun v => by
      simp [blockPower_X, shift_X, blockPowerPoint]
  exact congrArg (fun φ : MvPolynomial (Fin n × Fin d) F →ₐ[F] MvPolynomial (Fin n) F => φ f) h

/-- [Shpilka2026, proof of Theorem 1.2]: if `f` is set-partitioned and a shift `b` of
`blockPower f` has a monomial `μ`, then the shift of `f` by `(b j ^ (i + 1))` has a monomial
with at most as many variables as `μ`. -/
theorem exists_mem_support_shift_blockPowerPoint (hf : IsSetPartitioned Prod.fst f)
    {b : Fin n → F} {μ : Fin n →₀ ℕ} (hμ : μ ∈ (shift b (blockPower F n d f)).support) :
    ∃ m ∈ (shift (blockPowerPoint b) f).support, m.support.card ≤ μ.support.card := by
  classical
  set G := shift (blockPowerPoint b) f with hG
  rw [shift_blockPower, aeval_def, eval₂_eq] at hμ
  obtain ⟨m, hm, hμm⟩ := mem_biUnion.1 (support_sum hμ)
  refine ⟨m, hm, ?_⟩
  rw [← card_image_of_injOn ((hf.shift _) m hm).2]
  refine card_le_card fun j hj => ?_
  obtain ⟨v, hv, rfl⟩ := mem_image.1 hj
  have key : ∀ P : MvPolynomial (Fin n) F, X v.1 ∣ P → μ ∈ P.support → v.1 ∈ μ.support := by
    rintro _ ⟨Q, rfl⟩ h
    rw [mem_support_iff, coeff_X_mul'] at h
    by_contra hcon
    exact h (ite_eq_right fun h' => absurd h' hcon)
  have h1 := sub_dvd_pow_sub_pow (X v.1 + C (b v.1) : MvPolynomial (Fin n) F) (C (b v.1))
    (v.2.val + 1)
  rw [add_sub_cancel_right, ← C_pow] at h1
  exact key _ (Dvd.dvd.mul_left ((h1.trans (dvd_pow_self _ (Finsupp.mem_support_iff.1 hv))).trans
    (dvd_prod_of_mem (fun u : Fin n × Fin d => ((X u.1 + C (b u.1)) ^ (u.2.val + 1) -
      (C (b u.1 ^ (u.2.val + 1)) : MvPolynomial (Fin n) F)) ^ m u) hv)) _) hμm

/-! ### The hitting set -/

variable (F n d) [CharZero F]

open scoped Classical in
/-- The hitting set for set-partitioned polynomials in `n` blocks of `d` variables, of split rank
at most `s` across every union of blocks: the points of `setPartitionedHittingSet` built from the
shifts `(b j ^ (i + 1))`, for `b` in `boundedDegreeShifts` with individual degree `d` and the
perfect hash family with `⌊lg s⌋ + 1` colours. -/
noncomputable def setMultilinearHittingSet (s : ℕ) : Finset (Fin n × Fin d → F) :=
  setPartitionedHittingSet F Prod.fst
    ((boundedDegreeShifts F d (perfectHashFamily n (Nat.log 2 s + 1))).image blockPowerPoint)
    (Nat.log 2 s) s

variable {F n d}

/-- **Hitting set for set-partitioned polynomials of small split rank.** Over a field of
characteristic zero, `setMultilinearHittingSet F n d s` hits every polynomial in `n` blocks of
`d` variables whose monomials have at most one variable of each block, to the first power, and
that is a sum of `s` products across every union of blocks. -/
theorem isHittingSet_setMultilinearHittingSet (s : ℕ) :
    IsHittingSet (setMultilinearHittingSet F n d s)
      {f | IsSetPartitioned Prod.fst f ∧
        ∀ I : Finset (Fin n), SplitRankLE (Prod.fst ⁻¹' (I : Set (Fin n))) s f} := by
  classical
  rintro f ⟨hpart, hsplit⟩ hf0
  obtain ⟨b, hb, μ, hμ, hμk⟩ := exists_mem_boundedDegreeShifts
    (isPerfectHashFamily_perfectHashFamily n _ (Nat.succ_pos _))
    (Nat.lt_pow_succ_log_self (by norm_num) s) (blockPower_ne_zero hpart hf0)
    (degreeOf_blockPower_le hpart) fun Y _ => (hsplit Y).blockPower
  obtain ⟨m, hm, hmμ⟩ := exists_mem_support_shift_blockPowerPoint hpart hμ
  exact exists_mem_setPartitionedHittingSet_eval_ne_zero hpart hsplit
    (mem_image_of_mem _ hb) hm (Nat.lt_succ_iff.1 (hmμ.trans_lt hμk))

/-- **Hitting sets for set-multilinear depth-three circuits with small variable sets**
([Shpilka2026], Theorem 1.2, in characteristic zero). `setMultilinearHittingSet F n d s` hits
every sum of `s` products of `n` linear forms, the `j`-th in the `d` variables of block `j`. -/
theorem isHittingSet_setMultilinearHittingSet_sum_prod (s : ℕ) :
    IsHittingSet (setMultilinearHittingSet F n d s)
      {f | ∃ c : Fin s → Fin n → Fin d → F,
        f = ∑ i, ∏ j, ∑ t, C (c i j t) * X (j, t)} := by
  classical
  rintro f ⟨c, rfl⟩
  have hlin (i : Fin s) (j : Fin n) : IsSetMultilinear Prod.fst {j}
      (∑ t, C (c i j t) * X (j, t) : MvPolynomial (Fin n × Fin d) F) :=
    IsSetMultilinear.sum _ fun t _ => by
      rw [← smul_eq_C_mul]
      exact (isSetMultilinear_X Prod.fst (j, t)).smul _
  have hmem (i : Fin s) (j : Fin n) (S : Set (Fin n)) (hj : j ∈ S) :
      (∑ t, C (c i j t) * X (j, t) : MvPolynomial (Fin n × Fin d) F) ∈
        supported F (Prod.fst ⁻¹' S) :=
    sum_mem fun t _ => mul_mem ((supported F _).algebraMap_mem _)
      (Algebra.subset_adjoin ⟨(j, t), hj, rfl⟩)
  refine isHittingSet_setMultilinearHittingSet s _ ⟨?_, fun I => ?_⟩
  · have hprod (i : Fin s) : IsSetMultilinear Prod.fst (univ : Finset (Fin n))
        (∏ j, ∑ t, C (c i j t) * X (j, t) : MvPolynomial (Fin n × Fin d) F) := by
      have hT : ((univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
          fun j : Fin n => ({j} : Finset (Fin n)) :=
        fun j _ k _ hjk => disjoint_singleton.2 hjk
      have h := IsSetMultilinear.prod univ hT fun j _ => hlin i j
      rwa [biUnion_singleton_eq_self] at h
    exact (IsSetMultilinear.sum univ fun i _ => hprod i).isSetPartitioned
  · have hI (i : Fin s) (J : Finset (Fin n)) (S : Set (Fin n)) (hJ : ∀ j ∈ J, j ∈ S) :
        (∏ j ∈ J, ∑ t, C (c i j t) * X (j, t) : MvPolynomial (Fin n × Fin d) F) ∈
          supported F (Prod.fst ⁻¹' S) :=
      prod_mem fun j hj => hmem i j S (hJ j hj)
    exact ⟨fun i => ∏ j ∈ I, ∑ t, C (c i j t) * X (j, t),
      fun i => ∏ j ∈ Iᶜ, ∑ t, C (c i j t) * X (j, t),
      fun i => hI i I _ fun j hj => mem_coe.2 hj,
      fun i => hI i Iᶜ (↑I)ᶜ fun j hj h => mem_compl.1 hj (mem_coe.1 h),
      sum_congr rfl fun i _ => (prod_mul_prod_compl I _).symm⟩

/-- The hitting set has at most
`(n d (n 2 ^ (25 (L + 1))) + 1) (n d (d + 1) ^ (L + 1) + 1)` shifts, with `L = ⌊lg s⌋`, each
with at most `1 + ∑ r ≤ L, n 2 ^ (25 r) 2 ^ r (n (n d (2 ^ r s)² + 2 ^ r s) + 1) (n + 1)`
points: a polynomial in `n`, `d` and `s` times `(d + 1) ^ (⌊lg s⌋ + 1)`. -/
theorem card_setMultilinearHittingSet_le (s : ℕ) :
    (setMultilinearHittingSet F n d s).card ≤
      (n * d * (n * 2 ^ (25 * (Nat.log 2 s + 1))) + 1) *
        (n * d * (d + 1) ^ (Nat.log 2 s + 1) + 1) *
        (1 + ∑ r ∈ range (Nat.log 2 s + 1), n * 2 ^ (25 * r) *
          (2 ^ r * ((n * (n * d * (2 ^ r * s) ^ 2 + 2 ^ r * s) + 1) * (n + 1)))) := by
  classical
  refine (card_setPartitionedHittingSet_le _ _ _ _).trans ?_
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  refine Nat.mul_le_mul_right _ (card_image_le.trans
    ((card_boundedDegreeShifts_le d _).trans (Nat.mul_le_mul_right _ ?_)))
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (card_perfectHashFamily_le _ _)) _

end Cslib.Circuits.Arithmetic
