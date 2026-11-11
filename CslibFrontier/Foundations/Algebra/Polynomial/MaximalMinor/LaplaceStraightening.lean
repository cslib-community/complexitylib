/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, generic maximal minors)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.MaximalMinor.LaplaceInclusionExclusion

/-!
# Straightening signed Laplace products

The induction measure and exchange identities have already been separated into
earlier files.  Here we develop the good/bad subset reductions used by the
Laplace straightening theorem.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`LaplaceStraightening.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027]. This general algebra is intended for
Mathlib; its destination is recorded in the upstream marker above.
-/

public section

namespace Cslib

noncomputable section

open scoped BigOperators

namespace GenericMaximalMinor

variable {N : ℕ} {R : Type*} [CommRing R]

/-- A subset is good when it precedes its complement in prefix order. -/
@[expose] def GoodSubset (A : Finset (Fin N)) : Prop := A ≼ₚ Aᶜ

lemma prefixLT_of_ssuperset {A B : Finset (Fin N)}
    (hAB : A ⊆ B) (hne : B ≠ A) : B ≺ₚ A := by
  exact ⟨prefixLE_of_superset hAB, hne⟩

lemma laplacePermSum_eq_zero_of_card_ne
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N))
    (hcard : A.card ≠ B.card) : laplacePermSum Y A B = 0 := by
  classical
  rw [laplacePermSum]
  apply Finset.sum_eq_zero
  intro s _
  rw [ite_eq_right]
  intro heq
  apply hcard
  rw [← heq]
  simp [permImage]

lemma maskedMatrix_transpose
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N)) :
    maskedMatrix Y.transpose B A = (maskedMatrix Y A B).transpose := by
  ext i j
  simp only [maskedMatrix, Matrix.transpose_apply]
  by_cases hi : i ∈ B <;> by_cases hj : j ∈ A <;> simp [hi, hj]

lemma laplacePermSum_transpose
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N)) :
    laplacePermSum Y.transpose B A = laplacePermSum Y A B := by
  rw [laplacePermSum_eq_det_maskedMatrix, laplacePermSum_eq_det_maskedMatrix,
    maskedMatrix_transpose, Matrix.det_transpose]

/-- The prefix of `Fin N` selected by `r`. -/
def prefixFinset (r : Fin (N + 1)) : Finset (Fin N) :=
  Finset.univ.filter fun i ↦ i.val < r.val

@[simp] lemma mem_prefixFinset_iff (r : Fin (N + 1)) (i : Fin N) :
    i ∈ prefixFinset r ↔ i.val < r.val := by
  simp [prefixFinset]

lemma prefixCard_eq_card_inter (A : Finset (Fin N)) (r : Fin (N + 1)) :
    prefixCard A r = (A ∩ prefixFinset r).card := by
  unfold prefixCard
  apply congrArg Finset.card
  ext i
  simp [prefixFinset, and_comm]

lemma prefixFinset_mono {r s : Fin (N + 1)} (hrs : r.val ≤ s.val) :
    prefixFinset r ⊆ prefixFinset s := by
  intro i hi
  simp only [mem_prefixFinset_iff] at hi ⊢
  omega

lemma exists_bad_prefix {B : Finset (Fin N)} (hbad : ¬GoodSubset B) :
    ∃ r : Fin (N + 1), prefixCard B r < prefixCard Bᶜ r := by
  by_contra h
  push Not at h
  apply hbad
  intro r
  exact h r

/-- Small complementary elements at a bad prefix. -/
def exchangeLow (B : Finset (Fin N)) (r : Fin (N + 1)) : Finset (Fin N) :=
  Bᶜ ∩ prefixFinset r

/-- Elements of `B` at or above the chosen prefix cut. -/
def exchangeHigh (B : Finset (Fin N)) (r : Fin (N + 1)) : Finset (Fin N) :=
  B \ prefixFinset r

/-- The enlarged ambient set used in the large-cardinality exchange relation. -/
def exchangeAmbient (B : Finset (Fin N)) (r : Fin (N + 1)) : Finset (Fin N) :=
  B ∪ exchangeLow B r

/-- The set of entries which the inclusion--exclusion relation may remove. -/
def exchangeRemoval (B : Finset (Fin N)) (r : Fin (N + 1)) : Finset (Fin N) :=
  exchangeLow B r ∪ exchangeHigh B r

lemma exchangeRemoval_subset_exchangeAmbient (B : Finset (Fin N))
    (r : Fin (N + 1)) : exchangeRemoval B r ⊆ exchangeAmbient B r := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact Finset.mem_union_right _ hi
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hi).1

lemma card_lt_exchangeRemoval_of_bad_prefix {B : Finset (Fin N)}
    {r : Fin (N + 1)} (hbad : prefixCard B r < prefixCard Bᶜ r) :
    B.card < (exchangeRemoval B r).card := by
  have hdis : Disjoint (exchangeLow B r) (exchangeHigh B r) := by
    rw [Finset.disjoint_left]
    intro i hiLow hiHigh
    exact (Finset.mem_sdiff.mp hiHigh).2 (Finset.mem_inter.mp hiLow).2
  have hlow : (exchangeLow B r).card = prefixCard Bᶜ r := by
    rw [prefixCard_eq_card_inter]
    rfl
  have hhigh : (exchangeHigh B r).card = B.card - prefixCard B r := by
    rw [exchangeHigh, Finset.card_sdiff, Finset.inter_comm,
      ← prefixCard_eq_card_inter]
  rw [exchangeRemoval, Finset.card_union_of_disjoint hdis, hlow, hhigh]
  have hprefix : prefixCard B r ≤ B.card := by
    unfold prefixCard
    exact Finset.card_le_card (Finset.filter_subset _ _)
  omega

/-- Replacing sufficiently many high elements of `B` by the smaller
complementary elements below a bad prefix moves downward in prefix order. -/
lemma exchange_result_prefixLE (B : Finset (Fin N)) (r : Fin (N + 1))
    (W : Finset (Fin N)) (hW : W ⊆ exchangeRemoval B r)
    (hcard : B.card ≤ (exchangeAmbient B r \ W).card) :
    exchangeAmbient B r \ W ≼ₚ B := by
  intro s
  let E := exchangeAmbient B r \ W
  by_cases hsr : s.val ≤ r.val
  · have hprefix : prefixFinset s ⊆ prefixFinset r := prefixFinset_mono hsr
    have hsub : B ∩ prefixFinset s ⊆ E ∩ prefixFinset s := by
      intro i hi
      have hiB : i ∈ B := (Finset.mem_inter.mp hi).1
      have hiS : i ∈ prefixFinset s := (Finset.mem_inter.mp hi).2
      have hiD : i ∈ exchangeAmbient B r := by
        exact Finset.mem_union_left _ hiB
      have hiW : i ∉ W := by
        intro hiWin
        have hiC := hW hiWin
        rcases Finset.mem_union.mp hiC with hiLow | hiHigh
        · exact (Finset.mem_compl.mp (Finset.mem_inter.mp hiLow).1) hiB
        · exact (Finset.mem_sdiff.mp hiHigh).2 (hprefix hiS)
      exact Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨hiD, hiW⟩, hiS⟩
    rw [prefixCard_eq_card_inter, prefixCard_eq_card_inter]
    exact Finset.card_le_card hsub
  · have hrs : r.val ≤ s.val := by omega
    have hprefix : prefixFinset r ⊆ prefixFinset s := prefixFinset_mono hrs
    have hout : E \ prefixFinset s ⊆ B \ prefixFinset s := by
      intro i hi
      have hiE : i ∈ E := (Finset.mem_sdiff.mp hi).1
      have hiNotS : i ∉ prefixFinset s := (Finset.mem_sdiff.mp hi).2
      have hiD : i ∈ exchangeAmbient B r := (Finset.mem_sdiff.mp hiE).1
      have hiB : i ∈ B := by
        rcases Finset.mem_union.mp hiD with hiB | hiLow
        · exact hiB
        · have hiR : i ∈ prefixFinset r := (Finset.mem_inter.mp hiLow).2
          exact (hiNotS (hprefix hiR)).elim
      exact Finset.mem_sdiff.mpr ⟨hiB, hiNotS⟩
    have houtCard : (E \ prefixFinset s).card ≤ (B \ prefixFinset s).card :=
      Finset.card_le_card hout
    have hpartE := Finset.card_inter_add_card_sdiff E (prefixFinset s)
    have hpartB := Finset.card_inter_add_card_sdiff B (prefixFinset s)
    rw [prefixCard_eq_card_inter, prefixCard_eq_card_inter]
    dsimp only [E] at hpartE houtCard ⊢
    omega

lemma exchange_result_prefixLT_of_ne (B : Finset (Fin N)) (r : Fin (N + 1))
    (W : Finset (Fin N)) (hW : W ⊆ exchangeRemoval B r)
    (hcard : B.card ≤ (exchangeAmbient B r \ W).card)
    (hne : exchangeAmbient B r \ W ≠ B) :
    exchangeAmbient B r \ W ≺ₚ B :=
  ⟨exchange_result_prefixLE B r W hW hcard, hne⟩

lemma exchangeAmbient_sdiff_exchangeLow (B : Finset (Fin N))
    (r : Fin (N + 1)) :
    exchangeAmbient B r \ exchangeLow B r = B := by
  ext i
  by_cases hiB : i ∈ B
  · simp [exchangeAmbient, exchangeLow, hiB]
  · simp [exchangeAmbient, exchangeLow, hiB]

lemma exchangeAmbient_sdiff_eq_iff (B : Finset (Fin N))
    (r : Fin (N + 1)) (W : Finset (Fin N))
    (hW : W ⊆ exchangeRemoval B r) :
    exchangeAmbient B r \ W = B ↔ W = exchangeLow B r := by
  constructor
  · intro hE
    ext i
    constructor
    · intro hiW
      have hiC := hW hiW
      rcases Finset.mem_union.mp hiC with hiLow | hiHigh
      · exact hiLow
      · have hiB := (Finset.mem_sdiff.mp hiHigh).1
        have hiD : i ∈ exchangeAmbient B r := Finset.mem_union_left _ hiB
        have hiDiff : i ∈ exchangeAmbient B r \ W :=
          hE.symm ▸ hiB
        exact ((Finset.mem_sdiff.mp hiDiff).2 hiW).elim
    · intro hiLow
      by_contra hiNotW
      have hiD : i ∈ exchangeAmbient B r := Finset.mem_union_right _ hiLow
      have hiDiff : i ∈ exchangeAmbient B r \ W :=
        Finset.mem_sdiff.mpr ⟨hiD, hiNotW⟩
      have hiB : i ∈ B := hE ▸ hiDiff
      exact (Finset.mem_compl.mp (Finset.mem_inter.mp hiLow).1) hiB
  · rintro rfl
    exact exchangeAmbient_sdiff_exchangeLow B r

/-- Values of good Laplace products bounded by `A,B` in prefix order. -/
@[expose] def laplaceStraighteningGenerators
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N)) : Set R :=
  {x | ∃ A' B', A' ≼ₚ A ∧ B' ≼ₚ B ∧ GoodSubset A' ∧ GoodSubset B' ∧
    x = laplacePermSum Y A' B'}

/-- Integral span of the good bounded Laplace products.  `AddSubgroup.closure`
is exactly the ℤ-linear span inside the additive group of `R`. -/
@[expose] def laplaceStraighteningSpan
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N)) : AddSubgroup R :=
  AddSubgroup.closure (laplaceStraighteningGenerators Y A B)

lemma laplacePermSum_mem_straighteningSpan_of_good
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N))
    (hA : GoodSubset A) (hB : GoodSubset B) :
    laplacePermSum Y A B ∈ laplaceStraighteningSpan Y A B := by
  apply AddSubgroup.subset_closure
  exact ⟨A, B, prefixLE_refl A, prefixLE_refl B, hA, hB, rfl⟩

lemma zero_mem_laplaceStraighteningSpan
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N)) :
    (0 : R) ∈ laplaceStraighteningSpan Y A B :=
  (laplaceStraighteningSpan Y A B).zero_mem

lemma negOnePow_mul_mem_laplaceStraighteningSpan_iff
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N))
    (k : ℕ) (x : R) :
    (-1 : R) ^ k * x ∈ laplaceStraighteningSpan Y A B ↔
      x ∈ laplaceStraighteningSpan Y A B := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      have heq : (-1 : R) ^ k * -1 * x = -((-1 : R) ^ k * x) := by ring
      rw [heq, (laplaceStraighteningSpan Y A B).neg_mem_iff, ih]

lemma laplaceStraighteningSpan_mono
    (Y : Matrix (Fin N) (Fin N) R)
    {A B A' B' : Finset (Fin N)} (hA : A' ≼ₚ A) (hB : B' ≼ₚ B) :
    laplaceStraighteningSpan Y A' B' ≤ laplaceStraighteningSpan Y A B := by
  apply AddSubgroup.closure_mono
  intro x hx
  rcases hx with ⟨C, D, hCA, hDB, hC, hD, rfl⟩
  exact ⟨C, D, prefixLE_trans hCA hA, prefixLE_trans hDB hB, hC, hD, rfl⟩

lemma laplaceStraighteningSpan_transpose
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N)) :
    laplaceStraighteningSpan Y.transpose B A = laplaceStraighteningSpan Y A B := by
  apply le_antisymm
  · apply (AddSubgroup.closure_le _).mpr
    intro x hx
    rcases hx with ⟨B', A', hBB, hAA, hB', hA', rfl⟩
    rw [laplacePermSum_transpose]
    apply AddSubgroup.subset_closure
    exact ⟨A', B', hAA, hBB, hA', hB', rfl⟩
  · apply (AddSubgroup.closure_le _).mpr
    intro x hx
    rcases hx with ⟨A', B', hAA, hBB, hA', hB', rfl⟩
    rw [← laplacePermSum_transpose]
    apply AddSubgroup.subset_closure
    exact ⟨B', A', hBB, hAA, hB', hA', rfl⟩

lemma AddSubgroup.mem_of_sum_eq_zero_of_mem_erase
    (H : AddSubgroup R) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → R) (a : ι) (ha : a ∈ s)
    (hsum : ∑ x ∈ s, f x = 0)
    (hmem : ∀ x ∈ s.erase a, f x ∈ H) : f a ∈ H := by
  have herase : (∑ x ∈ s.erase a, f x) ∈ H := H.sum_mem fun x hx ↦ hmem x hx
  have hsplit := Finset.add_sum_erase s f ha
  have hneg : f a = -(∑ x ∈ s.erase a, f x) := by
    rw [hsum] at hsplit
    exact eq_neg_of_add_eq_zero_left hsplit
  rw [hneg]
  exact H.neg_mem herase

/-- The small-cardinality reduction supplied by inclusion--exclusion form II. -/
lemma laplacePermSum_mem_straighteningSpan_of_twice_card_lt
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N))
    (hcard : A.card = B.card) (hsmall : 2 * A.card < N)
    (ih : ∀ A' B' : Finset (Fin N),
      laplaceDefect A' B' < laplaceDefect A B →
        laplacePermSum Y A' B' ∈ laplaceStraighteningSpan Y A' B') :
    laplacePermSum Y A B ∈ laplaceStraighteningSpan Y A B := by
  classical
  let S := supersets A ×ˢ supersets B
  let f : Finset (Fin N) × Finset (Fin N) → R := fun q ↦
    (-1 : R) ^ q.2ᶜ.card * laplacePermSum Y q.1 q.2
  have hrhs : (∑ V ∈ B.powerset, laplacePermSum Y A Vᶜ) = 0 := by
    apply Finset.sum_eq_zero
    intro V hV
    apply laplacePermSum_eq_zero_of_card_ne
    have hVB : V.card ≤ B.card :=
      Finset.card_le_card (Finset.mem_powerset.mp hV)
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  have htotal : ∑ q ∈ S, f q = 0 := by
    rw [Finset.sum_product]
    change (∑ U ∈ supersets A, ∑ W ∈ supersets B,
      (-1 : R) ^ Wᶜ.card * laplacePermSum Y U W) = 0
    rw [laplacePermSum_exchange_inclusionExclusion_two, hrhs]
  have hAB : (A, B) ∈ S := by
    simp [S]
  have hother : ∀ q ∈ S.erase (A, B),
      f q ∈ laplaceStraighteningSpan Y A B := by
    intro q hq
    have hqS : q ∈ S := (Finset.mem_erase.mp hq).2
    have hqne : q ≠ (A, B) := (Finset.mem_erase.mp hq).1
    rcases q with ⟨U, W⟩
    have hqProd : U ∈ supersets A ∧ W ∈ supersets B := by
      simpa [S] using (Finset.mem_product.mp hqS)
    have hAU : A ⊆ U := (mem_supersets_iff A U).mp hqProd.1
    have hBW : B ⊆ W := (mem_supersets_iff B W).mp hqProd.2
    by_cases hUW : U.card = W.card
    · have hUA : U ≠ A ∨ W ≠ B := by
        by_contra h
        push Not at h
        exact hqne (Prod.ext h.1 h.2)
      have hUle : U ≼ₚ A := prefixLE_of_superset hAU
      have hWle : W ≼ₚ B := prefixLE_of_superset hBW
      have hdef : laplaceDefect U W < laplaceDefect A B := by
        rcases hUA with hUA | hWB
        · exact laplaceDefect_lt_of_left_strict ⟨hUle, hUA⟩ hWle
        · exact laplaceDefect_lt_of_right_strict hUle ⟨hWle, hWB⟩
      have hterm := ih U W hdef
      have hterm' : laplacePermSum Y U W ∈ laplaceStraighteningSpan Y A B :=
        laplaceStraighteningSpan_mono Y hUle hWle hterm
      exact (negOnePow_mul_mem_laplaceStraighteningSpan_iff
        Y A B Wᶜ.card (laplacePermSum Y U W)).mpr hterm'
    · have hzero : laplacePermSum Y U W = 0 :=
        laplacePermSum_eq_zero_of_card_ne Y U W hUW
      simp [f, hzero]
  have hdist : f (A, B) ∈ laplaceStraighteningSpan Y A B :=
    GenericMaximalMinor.AddSubgroup.mem_of_sum_eq_zero_of_mem_erase
      (laplaceStraighteningSpan Y A B) S f (A, B) hAB htotal hother
  exact (negOnePow_mul_mem_laplaceStraighteningSpan_iff
    Y A B Bᶜ.card (laplacePermSum Y A B)).mp hdist

/-- Unified bad-second-coordinate reduction.  Unlike the paper's presentation,
this construction works in every cardinality range, so no `2p < N`/`2p ≥ N`
case split is needed. -/
lemma laplacePermSum_mem_straighteningSpan_of_bad_right
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N))
    (hcard : A.card = B.card) (hbad : ¬GoodSubset B)
    (ih : ∀ A' B' : Finset (Fin N),
      laplaceDefect A' B' < laplaceDefect A B →
        laplacePermSum Y A' B' ∈ laplaceStraighteningSpan Y A' B') :
    laplacePermSum Y A B ∈ laplaceStraighteningSpan Y A B := by
  classical
  obtain ⟨r, hr⟩ := exists_bad_prefix hbad
  let J := exchangeLow B r
  let D := exchangeAmbient B r
  let C := exchangeRemoval B r
  let S := supersets A ×ˢ C.powerset
  let f : Finset (Fin N) × Finset (Fin N) → R := fun q ↦
    (-1 : R) ^ q.2.card * laplacePermSum Y q.1 (D \ q.2)
  have hCD : C ⊆ D := exchangeRemoval_subset_exchangeAmbient B r
  have hCcard : A.card < C.card := by
    rw [hcard]
    exact card_lt_exchangeRemoval_of_bad_prefix hr
  have hleft :
      (∑ V ∈ betweenSubsets C D, laplacePermSum Y A V) = 0 := by
    apply Finset.sum_eq_zero
    intro V hV
    apply laplacePermSum_eq_zero_of_card_ne
    have hCV : C ⊆ V := (mem_betweenSubsets_iff C D V).mp hV |>.1
    have hle : C.card ≤ V.card := Finset.card_le_card hCV
    omega
  have htotal : ∑ q ∈ S, f q = 0 := by
    rw [Finset.sum_product]
    change (∑ U ∈ supersets A, ∑ W ∈ C.powerset,
      (-1 : R) ^ W.card * laplacePermSum Y U (D \ W)) = 0
    rw [← laplacePermSum_exchange_inclusionExclusion_one Y A D C hCD, hleft]
  have hJ : J ∈ C.powerset := by
    rw [Finset.mem_powerset]
    intro i hi
    exact Finset.mem_union_left _ hi
  have hAJ : (A, J) ∈ S := by
    exact Finset.mem_product.mpr ⟨(mem_supersets_iff A A).mpr (by rfl), hJ⟩
  have hother : ∀ q ∈ S.erase (A, J),
      f q ∈ laplaceStraighteningSpan Y A B := by
    intro q hq
    have hqS : q ∈ S := (Finset.mem_erase.mp hq).2
    have hqne : q ≠ (A, J) := (Finset.mem_erase.mp hq).1
    rcases q with ⟨U, W⟩
    have hqProd : U ∈ supersets A ∧ W ∈ C.powerset :=
      Finset.mem_product.mp hqS
    have hAU : A ⊆ U := (mem_supersets_iff A U).mp hqProd.1
    have hWC : W ⊆ C := Finset.mem_powerset.mp hqProd.2
    let E := D \ W
    by_cases hUE : U.card = E.card
    · have hAcardU : A.card ≤ U.card := Finset.card_le_card hAU
      have hBcardE : B.card ≤ E.card := by omega
      have hEle : E ≼ₚ B := by
        exact exchange_result_prefixLE B r W hWC hBcardE
      have hUle : U ≼ₚ A := prefixLE_of_superset hAU
      have hdef : laplaceDefect U E < laplaceDefect A B := by
        by_cases hUA : U = A
        · have hWJ : W ≠ J := by
            intro hW
            exact hqne (Prod.ext hUA hW)
          have hEB : E ≠ B := by
            intro hE
            apply hWJ
            exact (exchangeAmbient_sdiff_eq_iff B r W hWC).mp hE
          exact laplaceDefect_lt_of_right_strict hUle ⟨hEle, hEB⟩
        · exact laplaceDefect_lt_of_left_strict ⟨hUle, hUA⟩ hEle
      have hterm := ih U E hdef
      have hterm' : laplacePermSum Y U E ∈ laplaceStraighteningSpan Y A B :=
        laplaceStraighteningSpan_mono Y hUle hEle hterm
      exact (negOnePow_mul_mem_laplaceStraighteningSpan_iff
        Y A B W.card (laplacePermSum Y U E)).mpr hterm'
    · have hzero : laplacePermSum Y U E = 0 :=
        laplacePermSum_eq_zero_of_card_ne Y U E hUE
      simp [f, E, hzero]
  have hdist : f (A, J) ∈ laplaceStraighteningSpan Y A B :=
    GenericMaximalMinor.AddSubgroup.mem_of_sum_eq_zero_of_mem_erase
      (laplaceStraighteningSpan Y A B) S f (A, J) hAJ htotal hother
  have hDB : D \ J = B := exchangeAmbient_sdiff_exchangeLow B r
  change (-1 : R) ^ J.card * laplacePermSum Y A (D \ J) ∈
    laplaceStraighteningSpan Y A B at hdist
  rw [hDB] at hdist
  exact (negOnePow_mul_mem_laplaceStraighteningSpan_iff
    Y A B J.card (laplacePermSum Y A B)).mp hdist

/-- Laplace straightening: every signed Laplace product is an integral linear
combination of bounded products whose two indexing subsets are good. -/
theorem laplacePermSum_mem_straighteningSpan
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N)) :
    laplacePermSum Y A B ∈ laplaceStraighteningSpan Y A B := by
  classical
  generalize hd : laplaceDefect A B = d
  induction d using Nat.strong_induction_on generalizing Y A B with
  | ind d ih =>
      by_cases hcard : A.card = B.card
      · by_cases hA : GoodSubset A
        · by_cases hB : GoodSubset B
          · exact laplacePermSum_mem_straighteningSpan_of_good Y A B hA hB
          · exact laplacePermSum_mem_straighteningSpan_of_bad_right
              Y A B hcard hB fun A' B' hlt ↦
                ih (laplaceDefect A' B') (hlt.trans_eq hd) Y A' B' rfl
        · have ht :
              laplacePermSum Y.transpose B A ∈
                laplaceStraighteningSpan Y.transpose B A :=
            laplacePermSum_mem_straighteningSpan_of_bad_right
              Y.transpose B A hcard.symm hA fun B' A' hlt ↦
                ih (laplaceDefect B' A')
                  (hlt.trans_eq ((laplaceDefect_comm B A).trans hd))
                  Y.transpose B' A' rfl
          rw [laplacePermSum_transpose, laplaceStraighteningSpan_transpose] at ht
          exact ht
      · rw [laplacePermSum_eq_zero_of_card_ne Y A B hcard]
        exact zero_mem_laplaceStraighteningSpan Y A B

end GenericMaximalMinor

end

end Cslib
