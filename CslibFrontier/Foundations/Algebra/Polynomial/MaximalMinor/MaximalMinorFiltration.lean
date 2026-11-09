/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.MaximalMinor.StandardMinorIndependence

/-!
# The maximal-minor filtration in the standard-product basis

This file refines straightening by recording a prefix of maximal minors.
For a standard product, all maximal factors occur first, so this prefix is
the basis-theoretic filtration by powers of the maximal-minor ideal.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`MaximalMinorFiltration.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027]. This general algebra is intended for
Mathlib; its placement exception is recorded in `UPSTREAM.md`.
-/

public section

namespace Cslib

noncomputable section

open scoped BigOperators

namespace GenericMaximalMinor

/-- A finite-set minor of an `n × m` matrix is maximal when its row set has
all `n` possible rows. -/
@[expose] def FinsetMinorIndex.IsMaximal {n m : ℕ}
    (d : FinsetMinorIndex n m) : Prop := d.rows.card = n

/-- The first `r` factors of a list are maximal.  This recursive formulation
is more convenient for the straightening induction than `List.take`. -/
@[expose] def HasMaximalPrefix {n m : ℕ} :
    ℕ → List (FinsetMinorIndex n m) → Prop
  | 0, _ => True
  | _ + 1, [] => False
  | r + 1, d :: l => d.IsMaximal ∧ HasMaximalPrefix r l

@[simp] lemma hasMaximalPrefix_zero {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) : HasMaximalPrefix 0 l := by
  trivial

@[simp] lemma hasMaximalPrefix_succ_nil {n m r : ℕ} :
    ¬HasMaximalPrefix (n := n) (m := m) (r + 1) [] := by
  simp [HasMaximalPrefix]

@[simp] lemma hasMaximalPrefix_succ_cons {n m r : ℕ}
    (d : FinsetMinorIndex n m) (l : List (FinsetMinorIndex n m)) :
    HasMaximalPrefix (r + 1) (d :: l) ↔
      d.IsMaximal ∧ HasMaximalPrefix r l := by
  rfl

lemma FinsetMinorIndex.card_rows_le {n m : ℕ}
    (d : FinsetMinorIndex n m) : d.rows.card ≤ n := by
  simpa using Finset.card_le_univ d.rows

lemma FinsetMinorIndex.isMaximal_of_le_of_isMaximal {n m : ℕ}
    {a d : FinsetMinorIndex n m} (had : a ≼ᵢ d)
    (hd : d.IsMaximal) : a.IsMaximal := by
  unfold FinsetMinorIndex.IsMaximal at hd ⊢
  have hle : d.rows.card ≤ a.rows.card := card_ge_of_prefixLE had.1
  have ha := a.card_rows_le
  omega

/-- Pair reductions retaining the total sum of the two minor sizes. -/
def sizedPairReductionGeneratorsFor {D : Type*} [CommRing D]
    {n m : ℕ} (d e : FinsetMinorIndex n m) :
    Set (GenericPoly D n m) :=
  {x | ∃ a b : FinsetMinorIndex n m,
    a ≺ᵢ d ∧ a ≼ᵢ b ∧
    a.rows.card + b.rows.card = d.rows.card + e.rows.card ∧
    x = a.poly * b.poly}

/-- The additive span of smaller two-minor reductions of a prescribed length. -/
def sizedPairReductionSpan {D : Type*} [CommRing D]
    {n m : ℕ} (d e : FinsetMinorIndex n m) :
    AddSubgroup (GenericPoly D n m) :=
  AddSubgroup.closure (sizedPairReductionGeneratorsFor (D := D) d e)

/-- Two-minor straightening with the size-content equality retained. -/
lemma two_minor_mem_sizedPairReductionSpan
    {D : Type*} [CommRing D] {n m : ℕ}
    (d e : FinsetMinorIndex n m) (hnot : ¬d ≼ᵢ e) :
    d.poly * e.poly ∈ sizedPairReductionSpan (D := D) d e := by
  have h := two_minor_straightening (D := D)
    d.rows e.rows d.cols e.cols d.card_eq e.card_eq hnot
  apply (AddSubgroup.closure_le _).mpr ?_ h
  intro x hx
  rcases hx with ⟨A, C, B, E, hAB, hCE, hAd, hBd,
    hAC, hBE, hstrict, htotal, rfl⟩
  let a : FinsetMinorIndex n m := ⟨A, B, hAB⟩
  let b : FinsetMinorIndex n m := ⟨C, E, hCE⟩
  apply AddSubgroup.subset_closure
  refine ⟨a, b, ?_, ⟨hAC, hBE⟩, htotal, rfl⟩
  refine ⟨⟨hAd, hBd⟩, ?_⟩
  intro hab
  have hrows : A = d.rows := congrArg FinsetMinorIndex.rows hab
  have hcols : B = d.cols := congrArg FinsetMinorIndex.cols hab
  rcases hstrict with hs | hs
  · exact hs.2 hrows
  · exact hs.2 hcols

/-- The coefficient-linear span of standard products whose first `r`
factors are maximal minors. -/
@[expose] def standardMaximalPrefixSubmodule (D : Type*) [CommRing D]
    (n m r : ℕ) : Submodule D (GenericPoly D n m) :=
  Submodule.span D
    {x | ∃ l : List (FinsetMinorIndex n m),
      IsStandardMinorList l ∧ HasMaximalPrefix r l ∧
        x = minorListPoly (D := D) l}

/-- Fixed-length version used internally by the terminating straightening
induction. -/
def standardMaximalPrefixSubmoduleOfLength
    (D : Type*) [CommRing D] (n m r k : ℕ) :
    Submodule D (GenericPoly D n m) :=
  Submodule.span D
    {x | ∃ l : List (FinsetMinorIndex n m),
      IsStandardMinorList l ∧ HasMaximalPrefix r l ∧
        l.length = k ∧ x = minorListPoly (D := D) l}

lemma standard_minorListPoly_mem_maximalPrefixSubmodule
    {D : Type*} [CommRing D] {n m r : ℕ}
    (l : List (FinsetMinorIndex n m))
    (hl : IsStandardMinorList l) (hr : HasMaximalPrefix r l) :
    minorListPoly (D := D) l ∈
      standardMaximalPrefixSubmodule D n m r := by
  apply Submodule.subset_span
  exact ⟨l, hl, hr, rfl⟩

lemma standard_minorListPoly_mem_maximalPrefixSubmoduleOfLength
    {D : Type*} [CommRing D] {n m r : ℕ}
    (l : List (FinsetMinorIndex n m))
    (hl : IsStandardMinorList l) (hr : HasMaximalPrefix r l) :
    minorListPoly (D := D) l ∈
      standardMaximalPrefixSubmoduleOfLength D n m r l.length := by
  apply Submodule.subset_span
  exact ⟨l, hl, hr, rfl, rfl⟩

lemma mul_left_mem_of_mem_submodule_span
    {D R : Type*} [CommRing D] [CommRing R] [Algebra D R]
    (K : Submodule D R) (s : Set R) (c x : R)
    (hgen : ∀ y ∈ s, c * y ∈ K) (hx : x ∈ Submodule.span D s) :
    c * x ∈ K := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hgen y hy
  | zero => simp
  | add x y _ _ hx hy => simpa [mul_add] using K.add_mem hx hy
  | smul a x _ hx =>
      simpa [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm] using
        K.smul_mem a hx

lemma mul_right_mem_of_mem_submodule_span
    {D R : Type*} [CommRing D] [CommRing R] [Algebra D R]
    (K : Submodule D R) (s : Set R) (c x : R)
    (hgen : ∀ y ∈ s, y * c ∈ K) (hx : x ∈ Submodule.span D s) :
    x * c ∈ K := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hgen y hy
  | zero => simp
  | add x y _ _ hx hy => simpa [add_mul] using K.add_mem hx hy
  | smul a x _ hx =>
      simpa [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm] using
        K.smul_mem a hx

theorem standardMaximalPrefixSubmodule_zero_eq_top
    (D : Type*) [CommRing D] (n m : ℕ) :
    standardMaximalPrefixSubmodule D n m 0 = ⊤ := by
  apply top_unique
  rw [← standardMinorProductSubmodule_eq_top D n m]
  rw [standardMinorProductSubmodule, Submodule.span_le]
  rintro x ⟨l, hl, rfl⟩
  exact standard_minorListPoly_mem_maximalPrefixSubmodule l hl trivial

/-- Straightening preserves a prescribed prefix of maximal factors and the
total number of factors. -/
theorem minorListPoly_mem_standardMaximalPrefixSubmoduleOfLength
    {D : Type*} [CommRing D] {n m r : ℕ}
    (l : List (FinsetMinorIndex n m)) (hr : HasMaximalPrefix r l) :
    minorListPoly (D := D) l ∈
      standardMaximalPrefixSubmoduleOfLength D n m r l.length := by
  classical
  generalize hk : l.length = k
  induction k using Nat.strong_induction_on generalizing l r with
  | ind k outer =>
      cases r with
      | zero =>
          have hstraight := minorListPoly_mem_standardSpanOfLength
            (D := D) l
          apply (AddSubgroup.closure_le
            (standardMaximalPrefixSubmoduleOfLength D n m 0 k).toAddSubgroup).mpr
              ?_ hstraight
          intro x hx
          rcases hx with ⟨u, huStd, huLen, rfl⟩
          apply Submodule.subset_span
          exact ⟨u, huStd, trivial, huLen.trans hk, rfl⟩
      | succ r =>
          cases l with
          | nil => simp [HasMaximalPrefix] at hr
          | cons d t =>
              have htlen : t.length < k := by
                simp only [List.length_cons] at hk
                omega
              have hdmax : d.IsMaximal :=
                (hasMaximalPrefix_succ_cons d t).mp hr |>.1
              have htprefix : HasMaximalPrefix r t :=
                (hasMaximalPrefix_succ_cons d t).mp hr |>.2
              have prepend : ∀ (a : FinsetMinorIndex n m)
                  (s : List (FinsetMinorIndex n m)),
                  a.IsMaximal → IsStandardMinorList s →
                  HasMaximalPrefix r s → s.length < k →
                  minorListPoly (D := D) (a :: s) ∈
                    standardMaximalPrefixSubmoduleOfLength
                      D n m (r + 1) (s.length + 1) := by
                intro a s hamax hs hsprefix hslen
                generalize hdef : a.defect = q
                induction q using Nat.strong_induction_on generalizing a s with
                | ind q inner =>
                    cases s with
                    | nil =>
                        cases r with
                        | zero =>
                            exact standard_minorListPoly_mem_maximalPrefixSubmoduleOfLength
                              (D := D) [a] trivial (by
                                exact (hasMaximalPrefix_succ_cons a []).mpr
                                  ⟨hamax, trivial⟩)
                        | succ r => simp [HasMaximalPrefix] at hsprefix
                    | cons b rest =>
                        by_cases hab : a ≼ᵢ b
                        · apply Submodule.subset_span
                          exact ⟨a :: b :: rest, ⟨hab, hs⟩,
                            (hasMaximalPrefix_succ_cons a (b :: rest)).mpr
                              ⟨hamax, hsprefix⟩, rfl, rfl⟩
                        · have hpair := two_minor_mem_sizedPairReductionSpan
                            (D := D) a b hab
                          have hpairTail :
                              (a.poly * b.poly) *
                                  minorListPoly (D := D) rest ∈
                                standardMaximalPrefixSubmoduleOfLength
                                  D n m (r + 1) ((b :: rest).length + 1) := by
                            apply mul_right_mem_of_mem_closure
                              (standardMaximalPrefixSubmoduleOfLength
                                D n m (r + 1) ((b :: rest).length + 1)).toAddSubgroup
                              (sizedPairReductionGeneratorsFor
                                (D := D) a b)
                              (minorListPoly (D := D) rest)
                              (a.poly * b.poly)
                            · intro y hy
                              rcases hy with
                                ⟨a', b', ha'a, ha'b', hsize, rfl⟩
                              have ha'max : a'.IsMaximal :=
                                a'.isMaximal_of_le_of_isMaximal ha'a.1 hamax
                              have hb'prefix :
                                  HasMaximalPrefix r (b' :: rest) := by
                                cases r with
                                | zero => trivial
                                | succ r =>
                                    have hbdata :=
                                      (hasMaximalPrefix_succ_cons b rest).mp hsprefix
                                    have hb'max : b'.IsMaximal := by
                                      have ha_card : a.rows.card = n := hamax
                                      have hb_card : b.rows.card = n := hbdata.1
                                      have ha'_card : a'.rows.card = n := ha'max
                                      have hb'le := b'.card_rows_le
                                      unfold FinsetMinorIndex.IsMaximal
                                      omega
                                    exact ⟨hb'max, hbdata.2⟩
                              have htail :
                                  minorListPoly (D := D) (b' :: rest) ∈
                                    standardMaximalPrefixSubmoduleOfLength
                                      D n m r (b' :: rest).length := by
                                exact outer (b' :: rest).length (by
                                  simpa using hslen) (r := r)
                                    (b' :: rest) hb'prefix rfl
                              rw [mul_assoc]
                              change a'.poly *
                                  minorListPoly (D := D) (b' :: rest) ∈
                                standardMaximalPrefixSubmoduleOfLength
                                  D n m (r + 1) ((b :: rest).length + 1)
                              apply mul_left_mem_of_mem_submodule_span
                                (standardMaximalPrefixSubmoduleOfLength
                                  D n m (r + 1) ((b :: rest).length + 1))
                                {z | ∃ u : List (FinsetMinorIndex n m),
                                  IsStandardMinorList u ∧
                                  HasMaximalPrefix r u ∧
                                  u.length = (b' :: rest).length ∧
                                  z = minorListPoly (D := D) u}
                                a'.poly
                                (minorListPoly (D := D) (b' :: rest))
                              · intro z hz
                                rcases hz with
                                  ⟨u, huStd, huPrefix, huLen, rfl⟩
                                have hdeflt : a'.defect < q :=
                                  (finsetMinorIndex_defect_lt_of_LT ha'a).trans_eq hdef
                                have hpre := inner a'.defect hdeflt a' u
                                  ha'max huStd huPrefix (by
                                    simpa [huLen] using hslen) rfl
                                simpa [huLen] using hpre
                              · exact htail
                            · simpa [sizedPairReductionSpan] using hpair
                          simpa [minorListPoly, mul_assoc] using hpairTail
              have htail := outer t.length htlen (r := r) t htprefix rfl
              change d.poly * minorListPoly (D := D) t ∈
                standardMaximalPrefixSubmoduleOfLength
                  D n m (r + 1) k
              apply mul_left_mem_of_mem_submodule_span
                (standardMaximalPrefixSubmoduleOfLength
                  D n m (r + 1) k)
                {x | ∃ s : List (FinsetMinorIndex n m),
                  IsStandardMinorList s ∧ HasMaximalPrefix r s ∧
                    s.length = t.length ∧
                    x = minorListPoly (D := D) s}
                d.poly (minorListPoly (D := D) t)
              · intro x hx
                rcases hx with ⟨s, hs, hsp, hslen, rfl⟩
                have hp := prepend d s hdmax hs hsp (by
                  simpa [hslen] using htlen)
                have hlength : s.length + 1 = k := by
                  simpa [hslen] using hk
                simpa [hlength] using hp
              · exact htail

theorem minorListPoly_mem_standardMaximalPrefixSubmodule
    {D : Type*} [CommRing D] {n m r : ℕ}
    (l : List (FinsetMinorIndex n m)) (hr : HasMaximalPrefix r l) :
    minorListPoly (D := D) l ∈
      standardMaximalPrefixSubmodule D n m r := by
  have h := minorListPoly_mem_standardMaximalPrefixSubmoduleOfLength
    (D := D) l hr
  apply (show standardMaximalPrefixSubmoduleOfLength D n m r l.length ≤
      standardMaximalPrefixSubmodule D n m r by
    rw [standardMaximalPrefixSubmoduleOfLength, Submodule.span_le]
    rintro x ⟨u, huStd, huPrefix, -, rfl⟩
    exact standard_minorListPoly_mem_maximalPrefixSubmodule
      u huStd huPrefix) h

lemma hasMaximalPrefix_append_right {n m r : ℕ}
    {l : List (FinsetMinorIndex n m)} (u : List (FinsetMinorIndex n m))
    (hl : HasMaximalPrefix r l) : HasMaximalPrefix r (l ++ u) := by
  induction r generalizing l with
  | zero => trivial
  | succ r ih =>
      cases l with
      | nil => simp [HasMaximalPrefix] at hl
      | cons d l =>
          exact ⟨hl.1, ih hl.2⟩

lemma mul_minorListPoly_mem_standardMaximalPrefixSubmodule
    {D : Type*} [CommRing D] {n m r : ℕ}
    (q : GenericPoly D n m) (l : List (FinsetMinorIndex n m))
    (hl : HasMaximalPrefix r l) :
    q * minorListPoly (D := D) l ∈
      standardMaximalPrefixSubmodule D n m r := by
  have hq : q ∈ standardMinorProductSubmodule D n m :=
    mem_standardMinorProductSubmodule q
  induction hq using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨u, huStd, rfl⟩
      have happend := minorListPoly_mem_standardMaximalPrefixSubmodule
        (D := D) (l ++ u) (hasMaximalPrefix_append_right u hl)
      rw [minorListPoly_append] at happend
      simpa [mul_comm] using happend
  | zero => simp
  | add x y _ _ hx hy => simpa [add_mul] using
      (standardMaximalPrefixSubmodule D n m r).add_mem hx hy
  | smul a x _ hx =>
      simpa [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm] using
        (standardMaximalPrefixSubmodule D n m r).smul_mem a hx

/-- The standard-prefix span is closed under multiplication by arbitrary
ambient polynomials. -/
lemma standardMaximalPrefixSubmodule_mul_mem
    {D : Type*} [CommRing D] {n m r : ℕ}
    (q : GenericPoly D n m) {x : GenericPoly D n m}
    (hx : x ∈ standardMaximalPrefixSubmodule D n m r) :
    q * x ∈ standardMaximalPrefixSubmodule D n m r := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨l, hlStd, hlPrefix, rfl⟩
      exact mul_minorListPoly_mem_standardMaximalPrefixSubmodule
        q l hlPrefix
  | zero => simp
  | add x y _ _ hx hy => simpa [mul_add] using
      (standardMaximalPrefixSubmodule D n m r).add_mem hx hy
  | smul a x _ hx =>
      simpa [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm] using
        (standardMaximalPrefixSubmodule D n m r).smul_mem a hx

/-- The same carrier, packaged as an ideal of the ambient polynomial ring. -/
@[expose] def standardMaximalPrefixIdeal
    (D : Type*) [CommRing D] (n m r : ℕ) :
    Ideal (GenericPoly D n m) where
  carrier := standardMaximalPrefixSubmodule D n m r
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  smul_mem' q _x hx := standardMaximalPrefixSubmodule_mul_mem q hx

@[simp] lemma mem_standardMaximalPrefixIdeal_iff
    {D : Type*} [CommRing D] {n m r : ℕ}
    {x : GenericPoly D n m} :
    x ∈ standardMaximalPrefixIdeal D n m r ↔
      x ∈ standardMaximalPrefixSubmodule D n m r :=
  Iff.rfl

/-- The maximal-minor ideal using the finite-set minor indexing native to
the straightening development. -/
def finsetMaximalMinorIdealOver
    (D : Type*) [CommRing D] (n m : ℕ) :
    Ideal (GenericPoly D n m) :=
  Ideal.span
    {x | ∃ d : FinsetMinorIndex n m,
      d.IsMaximal ∧ x = d.poly}

lemma FinsetMinorIndex.poly_mem_finsetMaximalMinorIdealOver
    {D : Type*} [CommRing D] {n m : ℕ}
    (d : FinsetMinorIndex n m) (hd : d.IsMaximal) :
    d.poly ∈ finsetMaximalMinorIdealOver D n m := by
  apply Ideal.subset_span
  exact ⟨d, hd, rfl⟩

lemma minorListPoly_eq_map_prod
    {D : Type*} [CommRing D] {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) :
    minorListPoly (D := D) l = (l.map (·.poly)).prod := by
  induction l with
  | nil => rfl
  | cons d l ih => simp [minorListPoly, ih]

lemma hasMaximalPrefix_length_of_forall_mem {n m : ℕ}
    (l : List (FinsetMinorIndex n m))
    (hl : ∀ d ∈ l, d.IsMaximal) :
    HasMaximalPrefix l.length l := by
  induction l with
  | nil => trivial
  | cons d l ih =>
      exact ⟨hl d (by simp), ih (fun e he ↦ hl e (by simp [he]))⟩

lemma minorListPoly_mem_finsetMaximalMinorIdealOver_pow_of_prefix
    {D : Type*} [CommRing D] {n m r : ℕ}
    (l : List (FinsetMinorIndex n m)) (hr : HasMaximalPrefix r l) :
    minorListPoly (D := D) l ∈
      finsetMaximalMinorIdealOver D n m ^ r := by
  induction r generalizing l with
  | zero => simp
  | succ r ih =>
      cases l with
      | nil => simp [HasMaximalPrefix] at hr
      | cons d l =>
          rw [minorListPoly_cons, pow_succ']
          exact Ideal.mul_mem_mul
            (d.poly_mem_finsetMaximalMinorIdealOver hr.1)
            (ih l hr.2)

theorem standardMaximalPrefixIdeal_le_pow
    (D : Type*) [CommRing D] (n m r : ℕ) :
    standardMaximalPrefixIdeal D n m r ≤
      finsetMaximalMinorIdealOver D n m ^ r := by
  intro x hx
  change x ∈ standardMaximalPrefixSubmodule D n m r at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨l, hlStd, hlPrefix, rfl⟩
      exact minorListPoly_mem_finsetMaximalMinorIdealOver_pow_of_prefix
        l hlPrefix
  | zero => exact Ideal.zero_mem _
  | add x y _ _ hx hy => exact Ideal.add_mem _ hx hy
  | smul a x _ hx =>
      simpa [Algebra.smul_def] using
        (finsetMaximalMinorIdealOver D n m ^ r).mul_mem_left
          (algebraMap D (GenericPoly D n m) a) hx

theorem finsetMaximalMinorIdealOver_pow_le_standardMaximalPrefixIdeal
    (D : Type*) [CommRing D] (n m r : ℕ) :
    finsetMaximalMinorIdealOver D n m ^ r ≤
      standardMaximalPrefixIdeal D n m r := by
  rw [finsetMaximalMinorIdealOver, Submodule.span_pow]
  rw [Ideal.span_le]
  intro x hx
  obtain ⟨f, hf, hprod⟩ := Set.mem_pow_iff_prod.mp hx
  have hex : ∀ i, ∃ d : FinsetMinorIndex n m,
      d.IsMaximal ∧ f i = d.poly := hf
  choose d hdmax hfd using hex
  let l : List (FinsetMinorIndex n m) := List.ofFn d
  have hall : ∀ e ∈ l, e.IsMaximal := by
    intro e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    exact hdmax i
  have hlprefix : HasMaximalPrefix r l := by
    have h := hasMaximalPrefix_length_of_forall_mem l hall
    simpa [l] using h
  have hlmem := minorListPoly_mem_standardMaximalPrefixSubmodule
    (D := D) l hlprefix
  change minorListPoly (D := D) l ∈
    standardMaximalPrefixIdeal D n m r at hlmem
  have hpoly : minorListPoly (D := D) l = ∏ i, f i := by
    rw [minorListPoly_eq_map_prod]
    simp only [l, List.map_ofFn, List.prod_ofFn]
    apply Finset.prod_congr rfl
    intro i _
    exact (hfd i).symm
  rw [← hprod, ← hpoly]
  exact hlmem

/-- Basis description of every power of the generic maximal-minor ideal. -/
theorem standardMaximalPrefixIdeal_eq_pow
    (D : Type*) [CommRing D] (n m r : ℕ) :
    standardMaximalPrefixIdeal D n m r =
      finsetMaximalMinorIdealOver D n m ^ r := by
  apply le_antisymm
  · exact standardMaximalPrefixIdeal_le_pow D n m r
  · exact finsetMaximalMinorIdealOver_pow_le_standardMaximalPrefixIdeal
      D n m r

/-! ## Bridge to the project's order-embedding maximal-minor ideal -/

/-- The finite-set index corresponding to an increasing choice of `n`
columns. -/
def finsetMaximalIndex {n m : ℕ} (S : MaximalMinorIndex n m) :
    FinsetMinorIndex n m where
  rows := Finset.univ
  cols := Finset.univ.map S.toEmbedding
  card_eq := by simp

@[simp] lemma finsetMaximalIndex_isMaximal {n m : ℕ}
    (S : MaximalMinorIndex n m) : (finsetMaximalIndex S).IsMaximal := by
  simp [finsetMaximalIndex, FinsetMinorIndex.IsMaximal]

lemma orderEmbOfFin_univ_eq_id (n : ℕ)
    (h : (Finset.univ : Finset (Fin n)).card = n) :
    Finset.orderEmbOfFin Finset.univ h = OrderEmbedding.id (Fin n) := by
  symm
  exact Finset.orderEmbOfFin_unique' h (fun i ↦ Finset.mem_univ i)

lemma orderEmbOfFin_map_orderEmbedding_eq {n m : ℕ}
    (S : Fin n ↪o Fin m)
    (h : (Finset.univ.map S.toEmbedding).card = n) :
    (Finset.univ.map S.toEmbedding).orderEmbOfFin h = S := by
  symm
  apply Finset.orderEmbOfFin_unique' h
  intro i
  exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩

lemma finsetMaximalIndex_poly
    {D : Type*} [CommRing D] {n m : ℕ} (hnm : n ≤ m)
    (S : MaximalMinorIndex n m) :
    (finsetMaximalIndex S).poly =
      maximalMinorPolyOver (D := D) hnm S := by
  unfold FinsetMinorIndex.poly
  change finsetMinorPoly (D := D) Finset.univ
      (Finset.univ.map S.toEmbedding) = _
  rw [finsetMinorPoly_of_card_eq (D := D)
    (Finset.univ : Finset (Fin n))
    (Finset.univ.map S.toEmbedding) (by simp)]
  unfold maximalMinorPolyOver
  let A : Finset (Fin n) := Finset.univ
  let B : Finset (Fin m) := Finset.univ.map S.toEmbedding
  have hA : A.card = n := by simp [A]
  have hB : B.card = n := by simp [B]
  have hAB : A.card = B.card := hA.trans hB.symm
  let d₀ : MinorIndex n m := minorIndexOfFinsets A B hAB
  let M : Matrix (Fin A.card) (Fin A.card) (GenericPoly D n m) :=
    minorMatrix d₀
  let N : Matrix (Fin n) (Fin n) (GenericPoly D n m) :=
    minorMatrix (maximalIndex hnm S)
  change Matrix.det M = Matrix.det N
  let e : Fin A.card ≃ Fin n := (Fin.castOrderIso hA).toEquiv
  calc
    Matrix.det M = Matrix.det (M.reindex e e) :=
      (Matrix.det_reindex_self e M).symm
    _ = Matrix.det N := by
      congr 1
      funext i j
      change M (e.symm i) (e.symm j) = N i j
      unfold M N d₀ minorMatrix minorIndexOfFinsets maximalIndex
      congr 2
      · have hcross : A.orderEmbOfFin rfl (e.symm i) =
            A.orderEmbOfFin hA i := by
          apply Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr
          simp [e]
        rw [hcross]
        have hid : A.orderEmbOfFin hA = OrderEmbedding.id (Fin n) := by
          simpa [A] using orderEmbOfFin_univ_eq_id n hA
        rw [hid]
      · have hcross : B.orderEmbOfFin hAB.symm (e.symm j) =
            B.orderEmbOfFin hB j := by
          apply Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr
          simp [e]
        rw [hcross]
        have hS : B.orderEmbOfFin hB = S := by
          simpa [B] using orderEmbOfFin_map_orderEmbedding_eq S hB
        rw [hS]

/-- Recover the increasing column embedding from a maximal finite-set
minor index. -/
@[expose] def FinsetMinorIndex.maximalOrderEmbedding {n m : ℕ}
    (d : FinsetMinorIndex n m) (hd : d.IsMaximal) :
    MaximalMinorIndex n m :=
  d.cols.orderEmbOfFin (by
    rw [← d.card_eq]
    exact hd)

lemma FinsetMinorIndex.eq_finsetMaximalIndex_maximalOrderEmbedding
    {n m : ℕ} (d : FinsetMinorIndex n m) (hd : d.IsMaximal) :
    d = finsetMaximalIndex (d.maximalOrderEmbedding hd) := by
  apply finsetMinorIndex_ext
  · apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa using (Nat.le_of_eq hd.symm)
  · change d.cols = Finset.univ.map
        (d.cols.orderEmbOfFin (by rw [← d.card_eq]; exact hd)).toEmbedding
    symm
    exact Finset.map_orderEmbOfFin_univ d.cols
      (by rw [← d.card_eq]; exact hd)

/-- The finite-set and order-embedding presentations generate the same
maximal-minor ideal. -/
theorem finsetMaximalMinorIdealOver_eq_maximalMinorIdealOver
    (D : Type*) [CommRing D] {n m : ℕ} (hnm : n ≤ m) :
    finsetMaximalMinorIdealOver D n m =
      maximalMinorIdealOver D n m hnm := by
  apply le_antisymm
  · rw [finsetMaximalMinorIdealOver, Ideal.span_le]
    rintro x ⟨d, hd, rfl⟩
    rw [d.eq_finsetMaximalIndex_maximalOrderEmbedding hd,
      finsetMaximalIndex_poly (D := D) hnm]
    exact maximalMinorPolyOver_mem_ideal hnm _
  · rw [maximalMinorIdealOver, Ideal.span_le]
    rintro x ⟨S, rfl⟩
    rw [← finsetMaximalIndex_poly (D := D) hnm S]
    exact (finsetMaximalIndex S).poly_mem_finsetMaximalMinorIdealOver
      (finsetMaximalIndex_isMaximal S)

/-- Paper-facing basis description of every power of the existing generic
maximal-minor ideal. -/
theorem standardMaximalPrefixIdeal_eq_maximalMinorIdealOver_pow
    (D : Type*) [CommRing D] {n m : ℕ} (hnm : n ≤ m) (r : ℕ) :
    standardMaximalPrefixIdeal D n m r =
      maximalMinorIdealOver D n m hnm ^ r := by
  rw [standardMaximalPrefixIdeal_eq_pow,
    finsetMaximalMinorIdealOver_eq_maximalMinorIdealOver D hnm]

/-! ## The corner factor -/

lemma prefixLE_singleton_last {N : ℕ}
    (A : Finset (Fin (N + 1))) (hA : A.Nonempty) :
    A ≼ₚ ({Fin.last N} : Finset (Fin (N + 1))) := by
  intro r
  by_cases hr : r = Fin.last (N + 1)
  · subst r
    rw [prefixCard_last, prefixCard_last]
    simpa using hA.card_pos
  · have hrne : r.val ≠ N + 1 := by
      intro heq
      apply hr
      apply Fin.ext
      simpa [Fin.last] using heq
    have hrle : r.val ≤ N := by
      have hrlt := r.isLt
      omega
    have hz : prefixCard ({Fin.last N} : Finset (Fin (N + 1))) r = 0 := by
      rw [prefixCard]
      have hfilter :
          ({Fin.last N} : Finset (Fin (N + 1))).filter
              (fun i ↦ i.val < r.val) = ∅ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_singleton,
          Finset.notMem_empty, iff_false]
        rintro ⟨rfl, hlt⟩
        simp only [Fin.last] at hlt
        omega
      rw [hfilter]
      simp
    rw [hz]
    exact Nat.zero_le _

/-- The bottom-right `1 × 1` minor. -/
def cornerMinorIndex (n m : ℕ) : FinsetMinorIndex (n + 1) (m + 1) :=
  singletonMinorIndex (Fin.last n) (Fin.last m)

@[simp] lemma cornerMinorIndex_poly
    {D : Type*} [CommRing D] (n m : ℕ) :
    (cornerMinorIndex n m).poly =
      (MvPolynomial.X (Fin.last n, Fin.last m) :
        GenericPoly D (n + 1) (m + 1)) := by
  exact singletonMinorIndex_poly (Fin.last n) (Fin.last m)

@[simp] lemma cornerMinorIndex_rows_nonempty (n m : ℕ) :
    (cornerMinorIndex n m).rows.Nonempty := by
  simp [cornerMinorIndex, singletonMinorIndex]

lemma finsetMinorIndex_le_corner {n m : ℕ}
    (d : FinsetMinorIndex (n + 1) (m + 1))
    (hd : d.rows.Nonempty) : d ≼ᵢ cornerMinorIndex n m := by
  constructor
  · simpa [cornerMinorIndex, singletonMinorIndex] using
      prefixLE_singleton_last d.rows hd
  · have hdcols : d.cols.Nonempty := by
      apply Finset.card_pos.mp
      rw [← d.card_eq]
      exact Finset.card_pos.mpr hd
    simpa [cornerMinorIndex, singletonMinorIndex] using
      prefixLE_singleton_last d.cols hdcols

lemma cornerMinorIndex_not_isMaximal {n m : ℕ} (hn : 0 < n) :
    ¬(cornerMinorIndex n m).IsMaximal := by
  simp [FinsetMinorIndex.IsMaximal, cornerMinorIndex,
    singletonMinorIndex]
  omega

lemma isStandardMinorList_append_corner {n m : ℕ}
    {l : List (FinsetMinorIndex (n + 1) (m + 1))}
    (hl : IsStandardMinorList l) (hne : HasNoEmptyMinors l) :
    IsStandardMinorList (l ++ [cornerMinorIndex n m]) := by
  induction l with
  | nil => trivial
  | cons d l ih =>
      cases l with
      | nil =>
          exact ⟨finsetMinorIndex_le_corner d (hne d (by simp)), trivial⟩
      | cons e l =>
          exact ⟨hl.1, ih hl.2 (fun a ha ↦ hne a (by simp [ha]))⟩

lemma hasNoEmptyMinors_append_corner {n m : ℕ}
    {l : List (FinsetMinorIndex (n + 1) (m + 1))}
    (hl : HasNoEmptyMinors l) :
    HasNoEmptyMinors (l ++ [cornerMinorIndex n m]) := by
  intro d hd
  simp only [List.mem_append, List.mem_singleton] at hd
  rcases hd with hd | rfl
  · exact hl d hd
  · exact cornerMinorIndex_rows_nonempty n m

lemma hasMaximalPrefix_append_corner_iff {n m r : ℕ}
    (hn : 0 < n) (l : List (FinsetMinorIndex (n + 1) (m + 1))) :
    HasMaximalPrefix r (l ++ [cornerMinorIndex n m]) ↔
      HasMaximalPrefix r l := by
  induction r generalizing l with
  | zero => simp
  | succ r ih =>
      cases l with
      | nil =>
          simp [HasMaximalPrefix, cornerMinorIndex_not_isMaximal hn]
      | cons d l =>
          simp only [List.cons_append, hasMaximalPrefix_succ_cons]
          exact and_congr_right (fun _ ↦ ih l)

lemma hasMaximalPrefix_eraseEmptyMinors
    {n m r : ℕ} (hn : 0 < n)
    {l : List (FinsetMinorIndex n m)} (hl : HasMaximalPrefix r l) :
    HasMaximalPrefix r (eraseEmptyMinors l) := by
  induction r generalizing l with
  | zero => trivial
  | succ r ih =>
      cases l with
      | nil => simp [HasMaximalPrefix] at hl
      | cons d l =>
          have hdmax : d.IsMaximal := hl.1
          have hdne : d.rows.Nonempty := by
            apply Finset.card_pos.mp
            rw [hdmax]
            exact hn
          change HasMaximalPrefix (r + 1)
            ((d :: l).filter fun e ↦ e.rows.Nonempty)
          simp only [List.filter_cons, decide_eq_true_eq, ite_eq_left hdne,
            hasMaximalPrefix_succ_cons]
          exact ⟨hdmax, ih hl.2⟩

/-- The span of the subset of the standard basis having a maximal prefix. -/
@[expose] def standardBasisPrefixSubmodule
    (D : Type*) [CommRing D] [Nontrivial D] (n m r : ℕ) :
    Submodule D (GenericPoly D n m) :=
  let b := standardMinorProductBasis D n m
  Submodule.span D
    (b '' {s : StandardMinorProductIndex n m |
      HasMaximalPrefix r s.1})

theorem standardMaximalPrefixSubmodule_eq_standardBasisPrefixSubmodule
    (D : Type*) [CommRing D] [Nontrivial D]
    {n m : ℕ} (hn : 0 < n) (r : ℕ) :
    standardMaximalPrefixSubmodule D n m r =
      standardBasisPrefixSubmodule D n m r := by
  apply le_antisymm
  · rw [standardMaximalPrefixSubmodule, Submodule.span_le]
    rintro x ⟨l, hlStd, hlPrefix, rfl⟩
    let s : StandardMinorProductIndex n m :=
      ⟨eraseEmptyMinors l, eraseEmptyMinors_standard hlStd,
        eraseEmptyMinors_hasNoEmptyMinors l⟩
    have hsPrefix : HasMaximalPrefix r s.1 :=
      hasMaximalPrefix_eraseEmptyMinors hn hlPrefix
    rw [← minorListPoly_eraseEmptyMinors (D := D) l]
    change minorListPoly (D := D) s.1 ∈
      standardBasisPrefixSubmodule D n m r
    rw [← standardMinorProductBasis_apply (D := D) s]
    apply Submodule.subset_span
    exact ⟨s, hsPrefix, rfl⟩
  · rw [standardBasisPrefixSubmodule, Submodule.span_le]
    rintro x ⟨s, hsPrefix, rfl⟩
    rw [standardMinorProductBasis_apply]
    exact standard_minorListPoly_mem_maximalPrefixSubmodule
      s.1 s.2.1 hsPrefix

/-- Append the corner factor to a standard-basis index. -/
def cornerAppendIndex {n m : ℕ}
    (s : StandardMinorProductIndex (n + 1) (m + 1)) :
    StandardMinorProductIndex (n + 1) (m + 1) :=
  ⟨s.1 ++ [cornerMinorIndex n m],
    isStandardMinorList_append_corner s.2.1 s.2.2,
    hasNoEmptyMinors_append_corner s.2.2⟩

lemma cornerAppendIndex_injective {n m : ℕ} :
    Function.Injective (cornerAppendIndex (n := n) (m := m)) := by
  intro s t hst
  apply Subtype.ext
  apply List.append_cancel_right
  exact congrArg Subtype.val hst

/-- The injective relabelling of basis indices induced by corner
multiplication. -/
def cornerAppendEmbedding (n m : ℕ) :
    StandardMinorProductIndex (n + 1) (m + 1) ↪
      StandardMinorProductIndex (n + 1) (m + 1) :=
  ⟨cornerAppendIndex, cornerAppendIndex_injective⟩

lemma corner_mul_standardMinorProductBasis
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ}
    (s : StandardMinorProductIndex (n + 1) (m + 1)) :
    (MvPolynomial.X (Fin.last n, Fin.last m) :
        GenericPoly D (n + 1) (m + 1)) *
        standardMinorProductBasis D (n + 1) (m + 1) s =
      standardMinorProductBasis D (n + 1) (m + 1)
        (cornerAppendIndex s) := by
  rw [standardMinorProductBasis_apply,
    standardMinorProductBasis_apply]
  change _ * minorListPoly (D := D) s.1 =
    minorListPoly (D := D) (s.1 ++ [cornerMinorIndex n m])
  rw [minorListPoly_append]
  simp only [minorListPoly_cons, minorListPoly_nil, mul_one,
    cornerMinorIndex_poly]
  rw [mul_comm]

/-- On standard-basis coordinates, multiplication by the corner variable is
the injective domain relabelling which appends the corner factor. -/
lemma standardMinorProductBasis_repr_corner_mul
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ}
    (f : GenericPoly D (n + 1) (m + 1)) :
    (standardMinorProductBasis D (n + 1) (m + 1)).repr
        ((MvPolynomial.X (Fin.last n, Fin.last m) :
          GenericPoly D (n + 1) (m + 1)) * f) =
      Finsupp.embDomain (cornerAppendEmbedding n m)
        ((standardMinorProductBasis D (n + 1) (m + 1)).repr f) := by
  let b := standardMinorProductBasis D (n + 1) (m + 1)
  let z : GenericPoly D (n + 1) (m + 1) :=
    MvPolynomial.X (Fin.last n, Fin.last m)
  let L : GenericPoly D (n + 1) (m + 1) →ₗ[D]
      GenericPoly D (n + 1) (m + 1) :=
    LinearMap.mulLeft D z
  have hmaps :
      (b.repr : GenericPoly D (n + 1) (m + 1) →ₗ[D]
          StandardMinorProductIndex (n + 1) (m + 1) →₀ D).comp L =
        (Finsupp.lmapDomain D D (cornerAppendEmbedding n m)).comp
          (b.repr : GenericPoly D (n + 1) (m + 1) →ₗ[D]
            StandardMinorProductIndex (n + 1) (m + 1) →₀ D) := by
    apply b.ext
    intro s
    simp only [LinearMap.comp_apply, L, LinearMap.mulLeft_apply]
    change b.repr
        ((MvPolynomial.X (Fin.last n, Fin.last m) :
          GenericPoly D (n + 1) (m + 1)) *
          standardMinorProductBasis D (n + 1) (m + 1) s) =
      (Finsupp.lmapDomain D D (cornerAppendEmbedding n m))
        (b.repr (standardMinorProductBasis D (n + 1) (m + 1) s))
    rw [corner_mul_standardMinorProductBasis]
    change b.repr (b (cornerAppendIndex s)) =
      (Finsupp.lmapDomain D D (cornerAppendEmbedding n m))
        (b.repr (b s))
    rw [b.repr_self, b.repr_self, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single]
    rfl
  have happ := LinearMap.congr_fun hmaps f
  simpa [b, z, L, Finsupp.embDomain_eq_mapDomain] using happ

/-- Corner cancellation for every power of the generic maximal-minor ideal. -/
theorem mem_maximalMinorIdealOver_pow_of_corner_mul_mem
    {D : Type*} [CommRing D] [Nontrivial D] {n m r : ℕ}
    (hn : 0 < n) (hnm : n + 1 ≤ m + 1)
    (f : GenericPoly D (n + 1) (m + 1))
    (hf : (MvPolynomial.X (Fin.last n, Fin.last m) :
        GenericPoly D (n + 1) (m + 1)) * f ∈
      maximalMinorIdealOver D (n + 1) (m + 1) hnm ^ r) :
    f ∈ maximalMinorIdealOver D (n + 1) (m + 1) hnm ^ r := by
  let b := standardMinorProductBasis D (n + 1) (m + 1)
  let Q : Set (StandardMinorProductIndex (n + 1) (m + 1)) :=
    {s | HasMaximalPrefix r s.1}
  have hzf := hf
  rw [← standardMaximalPrefixIdeal_eq_maximalMinorIdealOver_pow
    D hnm r] at hzf
  change (MvPolynomial.X (Fin.last n, Fin.last m) :
      GenericPoly D (n + 1) (m + 1)) * f ∈
    standardMaximalPrefixSubmodule D (n + 1) (m + 1) r at hzf
  rw [standardMaximalPrefixSubmodule_eq_standardBasisPrefixSubmodule
    D (Nat.succ_pos n) r] at hzf
  change (MvPolynomial.X (Fin.last n, Fin.last m) :
      GenericPoly D (n + 1) (m + 1)) * f ∈
    Submodule.span D (b '' Q) at hzf
  have hzsupport :
      ↑(b.repr ((MvPolynomial.X (Fin.last n, Fin.last m) :
        GenericPoly D (n + 1) (m + 1)) * f)).support ⊆ Q :=
    (Module.Basis.mem_span_image (b := b)).mp hzf
  rw [standardMinorProductBasis_repr_corner_mul] at hzsupport
  simp only [Finsupp.support_embDomain] at hzsupport
  have hfsupport : ↑(b.repr f).support ⊆ Q := by
    intro s hs
    have hsmap : cornerAppendEmbedding n m s ∈
        (b.repr f).support.map (cornerAppendEmbedding n m) :=
      Finset.mem_map.mpr ⟨s, hs, rfl⟩
    have happ := hzsupport hsmap
    change HasMaximalPrefix r
      (s.1 ++ [cornerMinorIndex n m]) at happ
    exact (hasMaximalPrefix_append_corner_iff hn s.1).mp happ
  have hfbasis : f ∈ standardBasisPrefixSubmodule
      D (n + 1) (m + 1) r := by
    change f ∈ Submodule.span D (b '' Q)
    exact (Module.Basis.mem_span_image (b := b)).mpr hfsupport
  have hfsub : f ∈ standardMaximalPrefixSubmodule
      D (n + 1) (m + 1) r := by
    rw [standardMaximalPrefixSubmodule_eq_standardBasisPrefixSubmodule
      D (Nat.succ_pos n) r]
    exact hfbasis
  have hfideal : f ∈ standardMaximalPrefixIdeal
      D (n + 1) (m + 1) r := hfsub
  rw [standardMaximalPrefixIdeal_eq_maximalMinorIdealOver_pow
    D hnm r] at hfideal
  exact hfideal

theorem corner_mul_mem_maximalMinorIdealOver_pow_iff
    {D : Type*} [CommRing D] [Nontrivial D] {n m r : ℕ}
    (hn : 0 < n) (hnm : n + 1 ≤ m + 1)
    (f : GenericPoly D (n + 1) (m + 1)) :
    (MvPolynomial.X (Fin.last n, Fin.last m) :
        GenericPoly D (n + 1) (m + 1)) * f ∈
        maximalMinorIdealOver D (n + 1) (m + 1) hnm ^ r ↔
      f ∈ maximalMinorIdealOver D (n + 1) (m + 1) hnm ^ r := by
  constructor
  · exact mem_maximalMinorIdealOver_pow_of_corner_mul_mem hn hnm f
  · intro hf
    exact (maximalMinorIdealOver D (n + 1) (m + 1) hnm ^ r).mul_mem_left _ hf

/-- Every power of the corner variable can be cancelled modulo every power
of the generic maximal-minor ideal. -/
theorem corner_pow_mul_mem_maximalMinorIdealOver_pow_iff
    {D : Type*} [CommRing D] [Nontrivial D] {n m r : ℕ}
    (hn : 0 < n) (hnm : n + 1 ≤ m + 1)
    (N : ℕ) (f : GenericPoly D (n + 1) (m + 1)) :
    (MvPolynomial.X (Fin.last n, Fin.last m) :
        GenericPoly D (n + 1) (m + 1)) ^ N * f ∈
        maximalMinorIdealOver D (n + 1) (m + 1) hnm ^ r ↔
      f ∈ maximalMinorIdealOver D (n + 1) (m + 1) hnm ^ r := by
  let z : GenericPoly D (n + 1) (m + 1) :=
    MvPolynomial.X (Fin.last n, Fin.last m)
  change z ^ N * f ∈
      maximalMinorIdealOver D (n + 1) (m + 1) hnm ^ r ↔
    f ∈ maximalMinorIdealOver D (n + 1) (m + 1) hnm ^ r
  induction N with
  | zero => simp
  | succ N ih =>
      rw [pow_succ, mul_comm (z ^ N) z, mul_assoc]
      change z * (z ^ N * f) ∈
          maximalMinorIdealOver D (n + 1) (m + 1) hnm ^ r ↔ _
      rw [corner_mul_mem_maximalMinorIdealOver_pow_iff hn hnm, ih]

end GenericMaximalMinor

end

end Cslib
