/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.Basic
public import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.Privacy
import CslibFrontier.Probability.PMF.Map

/-!
# Distribution Designs and Random-less Composition (ACOR22)

This module formalizes distribution designs and random-less composition of secret-sharing schemes
from Aggarwal, Chung, Obremski, and Ribeiro ([ACOR22]; see also [Aggarwal2026], Section 5,
"Relation to the reductions of ACOR22"):

1. **General distribution designs (`DistributionDesign`):** an assignment `assign : Party → Finset
   Party'` handing each new party the shares of a set of old parties so that a coalition `s` is
   authorized in `A` iff `s.biUnion assign` is authorized in `A'` (equivalently `A'.pullback
   assign = A`).
2. **Random-less composition (`AccessScheme.composeDesign`,**
   **`StatisticallyPrivate.composeDesign`):** composing any scheme over `A'` with a
   `DistributionDesign A A'` yields a scheme over `A` with the *same* key type and source class
   `sources`, preserving universal correctness, perfect privacy, and statistical `δ`-privacy.
3. **Threshold `(t, n, t', n')`-designs (`ThresholdDesignOn`, `ThresholdDesign`):**
   - Exact-cardinality characterization (`ThresholdDesignOn.ofCardEq`).
   - Explicit reduction from `(t', n')` to `(2, 2)` for `2 ≤ t' ≤ n'`
     (`ThresholdDesign.toTwoTwo`, `ThresholdDesignOn.toTwoTwo`, `AccessScheme.toTwoTwo`).
   - Non-existence of `(t, n, 2, 2)` designs for `2 ≤ t ≤ n` and `3 ≤ n`
     (`no_thresholdDesign_two_two`), in particular ruling out `(2, 3, 2, 2)` designs
     (`not_exists_design_2_3_2_2`) and `(r, r, 2, 2)` designs for `r ≥ 3`
     (`not_exists_design_r_r_2_2`).

## Main definitions

* `Cslib.Crypto.Protocols.SecretSharing.DistributionDesign`: distribution design between general
  monotone access structures.
* `Cslib.Crypto.Protocols.SecretSharing.DistributionDesign.id`,
  `Cslib.Crypto.Protocols.SecretSharing.DistributionDesign.comp`: identity and sequential
  composition of distribution designs.
* `Cslib.Crypto.Protocols.SecretSharing.AccessScheme.composeDesign`: random-less scheme
  composition along a distribution design.
* `Cslib.Crypto.Protocols.SecretSharing.ThresholdDesignOn`,
  `Cslib.Crypto.Protocols.SecretSharing.ThresholdDesign`,
  `Cslib.Crypto.Protocols.SecretSharing.ThresholdDesignOn.ofCardEq`: threshold distribution
  designs and exact-cardinality constructor matching the ACOR22 design conditions.
* `Cslib.Crypto.Protocols.SecretSharing.ThresholdDesign.toTwoTwo`,
  `Cslib.Crypto.Protocols.SecretSharing.ThresholdDesignOn.toTwoTwo`,
  `Cslib.Crypto.Protocols.SecretSharing.AccessScheme.toTwoTwo`: `(t', n') → (2, 2)` design
  reduction for `2 ≤ t' ≤ n'`.

## Main results

* `Cslib.Crypto.Protocols.SecretSharing.StatisticallyPrivate.composeDesign`: statistical
  `δ`-privacy is preserved under distribution-design composition.
* `Cslib.Crypto.Protocols.SecretSharing.no_thresholdDesign_two_two`: no `(t, n, 2, 2)`
  distribution design exists when `2 ≤ t ≤ n` and `3 ≤ n`.
* `Cslib.Crypto.Protocols.SecretSharing.not_exists_design_2_3_2_2`,
  `Cslib.Crypto.Protocols.SecretSharing.not_exists_design_r_r_2_2`: non-existence of
  `(2, 3, 2, 2)` designs and `(r, r, 2, 2)` designs for `r ≥ 3`.

## References

* [D. Aggarwal, E. Chung, M. Obremski, J. Ribeiro, *On Secret Sharing, Randomness, and
  Random-less Reductions for Secret Sharing*][ACOR22].
* [D. Aggarwal, *Secret Sharing Despite Non-Extractable Randomness*][Aggarwal2026],
  Section 5 ("Relation to the reductions of ACOR22").
-/

public section

namespace Cslib.Crypto.Protocols.SecretSharing

open Cslib.Probability Cslib.Probability.PMF
open scoped NNReal

section GeneralDesign

/-- A distribution design from `A'` (over `Party'`) to `A` (over `Party`) assigns each party
`i : Party` a finite subset `assign i` of `Party'` such that a coalition `s` is authorized in `A`
iff the union `s.biUnion assign` is authorized in `A'` ([ACOR22]). -/
structure DistributionDesign {Party Party' : Type*}
    (A : AccessStructure Party) (A' : AccessStructure Party')
    [DecidableEq Party'] where
  /-- Old parties whose shares are handed to each new party `i`. -/
  assign : Party → Finset Party'
  /-- Equivalence of authorization between `A` and the pulled-back coalitions in `A'`. -/
  authorized_iff : ∀ s : Finset Party, A.authorized s ↔ A'.authorized (s.biUnion assign)

namespace DistributionDesign

/-- Any access structure pulled back along `assign` yields a canonical distribution design. -/
@[expose] def ofPullback {Party Party' : Type*} [DecidableEq Party']
    (assign : Party → Finset Party') (A' : AccessStructure Party') :
    DistributionDesign (A'.pullback assign) A' where
  assign := assign
  authorized_iff _ := Iff.rfl

/-- A distribution design exhibits `A` as the pullback of `A'` along `d.assign`. -/
theorem pullback_eq {Party Party' : Type*} [DecidableEq Party']
    {A : AccessStructure Party} {A' : AccessStructure Party'}
    (d : DistributionDesign A A') : A'.pullback d.assign = A := by
  ext s
  exact (d.authorized_iff s).symm

/-- The identity distribution design handing each party its own single share. -/
@[expose] def id {Party : Type*} [DecidableEq Party] (A : AccessStructure Party) :
    DistributionDesign A A where
  assign i := {i}
  authorized_iff s := by simp

/-- Sequential composition of distribution designs: composing `d₁ : A₁ ← A₂` with
`d₂ : A₂ ← A₃` assigns `i` the union `(d₁.assign i).biUnion d₂.assign`. -/
@[expose] def comp {Party₁ Party₂ Party₃ : Type*} [DecidableEq Party₂] [DecidableEq Party₃]
    {A₁ : AccessStructure Party₁} {A₂ : AccessStructure Party₂} {A₃ : AccessStructure Party₃}
    (d₁ : DistributionDesign A₁ A₂) (d₂ : DistributionDesign A₂ A₃) :
    DistributionDesign A₁ A₃ where
  assign i := (d₁.assign i).biUnion d₂.assign
  authorized_iff s := by
    have hbi : s.biUnion (fun i => (d₁.assign i).biUnion d₂.assign) =
        (s.biUnion d₁.assign).biUnion d₂.assign := by
      ext k
      simp only [Finset.mem_biUnion]
      constructor
      · rintro ⟨i, hi, j, hj, hk⟩
        exact ⟨j, ⟨i, hi, hj⟩, hk⟩
      · rintro ⟨j, ⟨i, hi, hj⟩, hk⟩
        exact ⟨i, hi, j, hj, hk⟩
    rw [hbi, d₁.authorized_iff, d₂.authorized_iff]

/-- Reinterpret a coalition view on `s.biUnion assign` as the composed view on `s`. -/
@[expose] def projectView {Party Party' : Type*} {Share' : Party' → Type*}
    [DecidableEq Party'] (assign : Party → Finset Party') (s : Finset Party)
    (v' : (j : s.biUnion assign) → Share' j.1) :
    (i : s) → (j : assign i.1) → Share' j.1 :=
  fun i j => v' ⟨j.1, Finset.mem_biUnion.mpr ⟨i.1, i.2, j.2⟩⟩

end DistributionDesign

/-- Random-less composition of an `AccessScheme` along a `DistributionDesign`: each party `i`
receives the tuple of shares of `d.assign i`, keeping the exact same `Key` type and `sources`
class ([ACOR22]). -/
@[expose] noncomputable def AccessScheme.composeDesign
    {Secret Key Party Party' : Type*} {Share' : Party' → Type*}
    (scheme' : AccessScheme Secret Key Party' Share')
    {A : AccessStructure Party} [DecidableEq Party']
    (d : DistributionDesign A scheme'.access) :
    AccessScheme Secret Key Party (fun i => (j : d.assign i) → Share' j.1) where
  access := A
  sources := scheme'.sources
  share k secret _ j := scheme'.share k secret j.1
  reconstruct s v :=
    scheme'.reconstruct (s.biUnion d.assign) fun j =>
      let h := Finset.mem_biUnion.mp j.2
      let i := Classical.choose h
      let hi := Classical.choose_spec h
      v ⟨i, hi.1⟩ ⟨j.1, hi.2⟩
  correct k secret s hs :=
    scheme'.correct k secret (s.biUnion d.assign) ((d.authorized_iff s).mp hs)
  view_indist P hP s hs secret₀ secret₁ := by
    have hnot : ¬ scheme'.access.authorized (s.biUnion d.assign) :=
      mt (d.authorized_iff s).mpr hs
    have hmap (secret : Secret) :
        AccessStructure.viewDistOf P
            (fun k secret' (i : Party) (j : d.assign i) => scheme'.share k secret' j.1) s secret =
          (scheme'.viewDist P (s.biUnion d.assign) secret).map
            (DistributionDesign.projectView d.assign s) := by
      simp only [AccessStructure.viewDistOf, AccessScheme.viewDist, PMF.map_comp]
      rfl
    rw [hmap secret₀, hmap secret₁]
    exact congrArg (PMF.map _)
      (scheme'.view_indist P hP (s.biUnion d.assign) hnot secret₀ secret₁)

@[simp]
theorem AccessScheme.composeDesign_sources
    {Secret Key Party Party' : Type*} {Share' : Party' → Type*}
    (scheme' : AccessScheme Secret Key Party' Share')
    {A : AccessStructure Party} [DecidableEq Party']
    (d : DistributionDesign A scheme'.access) :
    (scheme'.composeDesign d).sources = scheme'.sources :=
  rfl

@[simp]
theorem AccessScheme.composeDesign_access
    {Secret Key Party Party' : Type*} {Share' : Party' → Type*}
    (scheme' : AccessScheme Secret Key Party' Share')
    {A : AccessStructure Party} [DecidableEq Party']
    (d : DistributionDesign A scheme'.access) :
    (scheme'.composeDesign d).access = A :=
  rfl

/-- Composing a `δ`-statistically private sharing map with a distribution design preserves
`δ`-statistical privacy over the exact same source class. -/
theorem StatisticallyPrivate.composeDesign
    {Secret Key Party Party' : Type*} {Share' : Party' → Type*}
    [∀ j, Fintype (Share' j)] [DecidableEq Party] [DecidableEq Party']
    {A : AccessStructure Party} {A' : AccessStructure Party'}
    {sources : SourceClass Key} {share' : Key → Secret → (j : Party') → Share' j}
    {δ : ℝ≥0}
    (d : DistributionDesign A A')
    (h : StatisticallyPrivate A' sources share' δ) :
    StatisticallyPrivate A sources
      (fun k secret (i : Party) (j : d.assign i) => share' k secret j.1) δ := by
  intro P hP s hs m₀ m₁
  have hnot : ¬ A'.authorized (s.biUnion d.assign) :=
    mt (d.authorized_iff s).mpr hs
  have hmap (m : Secret) :
      AccessStructure.viewDistOf P
          (fun k secret' (i : Party) (j : d.assign i) => share' k secret' j.1) s m =
        (AccessStructure.viewDistOf P share' (s.biUnion d.assign) m).map
          (DistributionDesign.projectView d.assign s) := by
    simp only [AccessStructure.viewDistOf, PMF.map_comp]
    rfl
  rw [hmap m₀, hmap m₁]
  exact (h P hP (s.biUnion d.assign) hnot m₀ m₁).map
    (DistributionDesign.projectView d.assign s)

end GeneralDesign

section ThresholdDesign

/-- A threshold distribution design converting a `t'`-threshold scheme over `Party'` to a
`t`-threshold scheme over `Party`. -/
abbrev ThresholdDesignOn (Party Party' : Type*) [DecidableEq Party'] (t t' : ℕ) :=
  DistributionDesign (AccessStructure.threshold Party t)
    (AccessStructure.threshold Party' t')

/-- A `(t, n, t', n')`-distribution design ([ACOR22]; [Aggarwal2026], Section 5). -/
abbrev ThresholdDesign (t n t' n' : ℕ) :=
  ThresholdDesignOn (Fin n) (Fin n') t t'

private theorem exists_superset_card_eq {α : Type*} [Fintype α]
    {s : Finset α} {m : ℕ} (hs : s.card ≤ m) (hm : m ≤ Fintype.card α) :
    ∃ t : Finset α, s ⊆ t ∧ t.card = m := by
  classical
  have hrem : m - s.card ≤ (Finset.univ \ s).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ s), Finset.card_univ]
    omega
  obtain ⟨u, hu_sub, hu_card⟩ := Finset.exists_subset_card_eq hrem
  refine ⟨s ∪ u, Finset.subset_union_left, ?_⟩
  rw [Finset.card_union_of_disjoint
    (Finset.disjoint_of_subset_right hu_sub disjoint_sdiff_self_right), hu_card]
  omega

private theorem biUnion_fin_two {α : Type*} [DecidableEq α] (f : Fin 2 → Finset α) :
    (Finset.univ : Finset (Fin 2)).biUnion f = f 0 ∪ f 1 := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Fin.exists_fin_two, Finset.mem_union]

private theorem biUnion_fin_two_ite {α : Type*} [DecidableEq α] (a b : Finset α) :
    (Finset.univ : Finset (Fin 2)).biUnion (fun i => if i = 0 then a else b) = a ∪ b := by
  have h0 : (if (0 : Fin 2) = 0 then a else b) = a := by simp
  have h1 : (if (1 : Fin 2) = 0 then a else b) = b := by simp
  rw [biUnion_fin_two, h0, h1]

private theorem card_singleton_biUnion_ite_lt {α : Type*} [DecidableEq α] {a b : Finset α}
    {t' : ℕ} (ha : a.card < t') (hb : b.card < t') {s : Finset (Fin 2)} (hs : s.card = 1) :
    (s.biUnion (fun i => if i = 0 then a else b)).card < t' := by
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hs
  rw [Finset.singleton_biUnion]
  split_ifs
  · exact ha
  · exact hb

private theorem card_image_finCast (m n : ℕ) (hmn : m ≤ n) :
    (Finset.univ.image (fun j : Fin m => (⟨j.val, by omega⟩ : Fin n))).card = m := by
  rw [Finset.card_image_of_injective _ (fun a b h => by
    cases a; cases b; simp only [Fin.mk.injEq] at h; simp [h]), Finset.card_univ, Fintype.card_fin]

namespace ThresholdDesignOn

/-- Construct a threshold distribution design from the exact-size conditions: every `t`-element
coalition covers at least `t'` old parties and every `(t - 1)`-element coalition covers strictly
fewer than `t'` old parties (assuming `0 < t` and `t ≤ Fintype.card Party`). -/
@[expose] def ofCardEq {Party Party' : Type*} [Fintype Party]
    [DecidableEq Party'] {t t' : ℕ} (ht : 0 < t) (htn : t ≤ Fintype.card Party)
    (assign : Party → Finset Party')
    (hauth : ∀ s : Finset Party, s.card = t → t' ≤ (s.biUnion assign).card)
    (hunauth : ∀ s : Finset Party, s.card = t - 1 → (s.biUnion assign).card < t') :
    ThresholdDesignOn Party Party' t t' where
  assign := assign
  authorized_iff s := by
    simp only [AccessStructure.threshold_authorized_iff]
    constructor
    · intro hs
      obtain ⟨s₀, hs₀_sub, hs₀_card⟩ := Finset.exists_subset_card_eq hs
      exact (hauth s₀ hs₀_card).trans
        (Finset.card_le_card (Finset.biUnion_subset_biUnion_of_subset_left assign hs₀_sub))
    · intro hbi
      by_contra hlt
      have hs_le : s.card ≤ t - 1 := by omega
      obtain ⟨u, hs_sub, hcard⟩ := exists_superset_card_eq hs_le (by omega)
      have hlt_bi : (u.biUnion assign).card < t' := hunauth u hcard
      have hsub_bi : s.biUnion assign ⊆ u.biUnion assign :=
        Finset.biUnion_subset_biUnion_of_subset_left assign hs_sub
      exact absurd (hbi.trans (Finset.card_le_card hsub_bi)) (not_le.mpr hlt_bi)

theorem le_card_of_card_eq {Party Party' : Type*} [DecidableEq Party'] {t t' : ℕ}
    (d : ThresholdDesignOn Party Party' t t') {s : Finset Party} (hs : s.card = t) :
    t' ≤ (s.biUnion d.assign).card :=
  (d.authorized_iff s).mp (by simp [hs])

theorem card_lt_of_card_eq_sub_one {Party Party' : Type*} [DecidableEq Party'] {t t' : ℕ}
    (d : ThresholdDesignOn Party Party' t t') (ht : 0 < t) {s : Finset Party}
    (hs : s.card = t - 1) : (s.biUnion d.assign).card < t' := by
  have hnot : ¬ (AccessStructure.threshold Party t).authorized s := by
    simp only [AccessStructure.threshold_authorized_iff]
    omega
  have h := (d.authorized_iff s).not.mp hnot
  simp only [AccessStructure.threshold_authorized_iff, not_le] at h
  exact h

/-- Explicit `(2, 2, t', |Party'|)`-distribution design for any finite party type `Party'` with
`2 ≤ t' ≤ |Party'|`: party `0` receives `t' - 1` old shares and party `1` receives `1` disjoint
old share. -/
noncomputable def toTwoTwo (Party' : Type*) [Fintype Party'] [DecidableEq Party']
    {t' : ℕ} (ht' : 2 ≤ t') (htn' : t' ≤ Fintype.card Party') :
    ThresholdDesignOn (Fin 2) Party' 2 t' :=
  have hcardU : t' ≤ (Finset.univ : Finset Party').card := by simpa using htn'
  let U : Finset Party' := (Finset.exists_subset_card_eq hcardU).choose
  have hU : U.card = t' := (Finset.exists_subset_card_eq hcardU).choose_spec.2
  have hU_ne : U.Nonempty := Finset.card_pos.mp (by omega)
  let p₀ : Party' := hU_ne.choose
  have hp₀ : p₀ ∈ U := hU_ne.choose_spec
  ofCardEq (by decide) (by decide) (fun i => if i = 0 then U.erase p₀ else {p₀})
    (fun s hs => by
      have hs_univ : s = Finset.univ := Finset.eq_univ_of_card s (by simpa using hs)
      subst hs_univ
      have hbi : (Finset.univ : Finset (Fin 2)).biUnion
          (fun i => if i = 0 then U.erase p₀ else {p₀}) = U := by
        rw [biUnion_fin_two_ite]
        ext x
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
        constructor
        · rintro (⟨_, hx⟩ | rfl) <;> assumption
        · intro hx
          by_cases hxp : x = p₀
          · exact Or.inr hxp
          · exact Or.inl ⟨hxp, hx⟩
      rw [hbi, hU])
    (fun _ hs => card_singleton_biUnion_ite_lt
      (by rw [Finset.card_erase_of_mem hp₀, hU]; omega)
      (by rw [Finset.card_singleton]; omega) hs)

end ThresholdDesignOn

namespace ThresholdDesign

/-- Explicit computable `(2, 2, t', n')`-distribution design for `2 ≤ t' ≤ n'` ([ACOR22];
[Aggarwal2026], Section 5): party `0` receives old shares `{0, ..., t' - 2}` and party `1`
receives `{t' - 1}`. -/
@[expose] def toTwoTwo {t' n' : ℕ} (ht' : 2 ≤ t') (htn' : t' ≤ n') :
    ThresholdDesign 2 2 t' n' :=
  ThresholdDesignOn.ofCardEq (by decide) (by decide)
    (fun i => if i = 0 then
        Finset.univ.image (fun j : Fin (t' - 1) => (⟨j.val, by omega⟩ : Fin n'))
      else {⟨t' - 1, by omega⟩})
    (fun s hs => by
      have hs_univ : s = Finset.univ := Finset.eq_univ_of_card s (by simpa using hs)
      subst hs_univ
      have hbi : (Finset.univ : Finset (Fin 2)).biUnion
          (fun i => if i = 0 then
              Finset.univ.image (fun j : Fin (t' - 1) => (⟨j.val, by omega⟩ : Fin n'))
            else {⟨t' - 1, by omega⟩}) =
          Finset.univ.image (fun j : Fin t' => (⟨j.val, by omega⟩ : Fin n')) := by
        rw [biUnion_fin_two_ite]
        ext k
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        constructor
        · rintro (⟨⟨j, hj⟩, rfl⟩ | h)
          · exact ⟨⟨j, by omega⟩, rfl⟩
          · exact ⟨⟨t' - 1, by omega⟩, h.symm⟩
        · rintro ⟨⟨j, hj⟩, rfl⟩
          by_cases hlt : j < t' - 1
          · exact Or.inl ⟨⟨j, hlt⟩, rfl⟩
          · exact Or.inr (Fin.ext (by dsimp; omega))
      rw [hbi, card_image_finCast t' n' htn'])
    (fun _ hs => by
      exact card_singleton_biUnion_ite_lt
        (by rw [card_image_finCast (t' - 1) n' (by omega)]; omega)
        (by rw [Finset.card_singleton]; omega) hs)

@[simp]
theorem toTwoTwo_assign_zero {t' n' : ℕ} (ht' : 2 ≤ t') (htn' : t' ≤ n') :
    (toTwoTwo ht' htn').assign 0 =
      Finset.univ.image (fun j : Fin (t' - 1) => (⟨j.val, by omega⟩ : Fin n')) :=
  rfl

@[simp]
theorem toTwoTwo_assign_one {t' n' : ℕ} (ht' : 2 ≤ t') (htn' : t' ≤ n') :
    (toTwoTwo ht' htn').assign 1 = ({⟨t' - 1, by omega⟩} : Finset (Fin n')) :=
  rfl

end ThresholdDesign

/-- Convert any `t'`-threshold `AccessScheme` over a finite `Party'` (`2 ≤ t' ≤ |Party'|`) into
a `(2, 2)`-threshold `AccessScheme` over `Fin 2` with the exact same `Key` type and `sources`
class ([ACOR22]). -/
@[expose] noncomputable def AccessScheme.toTwoTwo
    {Secret Key Party' : Type*} {Share' : Party' → Type*}
    [Fintype Party'] [DecidableEq Party'] {t' : ℕ}
    (scheme' : AccessScheme Secret Key Party' Share')
    (haccess : scheme'.access = AccessStructure.threshold Party' t')
    (ht' : 2 ≤ t') (htn' : t' ≤ Fintype.card Party') :=
  let d : DistributionDesign (AccessStructure.threshold (Fin 2) 2) scheme'.access :=
    haccess ▸ ThresholdDesignOn.toTwoTwo Party' ht' htn'
  scheme'.composeDesign d

@[simp]
theorem AccessScheme.toTwoTwo_access
    {Secret Key Party' : Type*} {Share' : Party' → Type*}
    [Fintype Party'] [DecidableEq Party'] {t' : ℕ}
    (scheme' : AccessScheme Secret Key Party' Share')
    (haccess : scheme'.access = AccessStructure.threshold Party' t')
    (ht' : 2 ≤ t') (htn' : t' ≤ Fintype.card Party') :
    (scheme'.toTwoTwo haccess ht' htn').access = AccessStructure.threshold (Fin 2) 2 :=
  rfl

@[simp]
theorem AccessScheme.toTwoTwo_sources
    {Secret Key Party' : Type*} {Share' : Party' → Type*}
    [Fintype Party'] [DecidableEq Party'] {t' : ℕ}
    (scheme' : AccessScheme Secret Key Party' Share')
    (haccess : scheme'.access = AccessStructure.threshold Party' t')
    (ht' : 2 ≤ t') (htn' : t' ≤ Fintype.card Party') :
    (scheme'.toTwoTwo haccess ht' htn').sources = scheme'.sources :=
  rfl

/-- Convert any `(t', n')`-threshold `AccessScheme` (`2 ≤ t' ≤ n'`) into a `(2, 2)`-threshold
`AccessScheme` over `Fin 2` via the explicit `ThresholdDesign.toTwoTwo` assignment, preserving
`Key` and `sources` ([ACOR22]). -/
@[expose] noncomputable def AccessScheme.toTwoTwoFin
    {Secret Key : Type*} {t' n' : ℕ} {Share' : Fin n' → Type*}
    (scheme' : AccessScheme Secret Key (Fin n') Share')
    (haccess : scheme'.access = AccessStructure.threshold (Fin n') t')
    (ht' : 2 ≤ t') (htn' : t' ≤ n') :=
  let d : DistributionDesign (AccessStructure.threshold (Fin 2) 2) scheme'.access :=
    haccess ▸ ThresholdDesign.toTwoTwo ht' htn'
  scheme'.composeDesign d

@[simp]
theorem AccessScheme.toTwoTwoFin_access
    {Secret Key : Type*} {t' n' : ℕ} {Share' : Fin n' → Type*}
    (scheme' : AccessScheme Secret Key (Fin n') Share')
    (haccess : scheme'.access = AccessStructure.threshold (Fin n') t')
    (ht' : 2 ≤ t') (htn' : t' ≤ n') :
    (scheme'.toTwoTwoFin haccess ht' htn').access = AccessStructure.threshold (Fin 2) 2 :=
  rfl

@[simp]
theorem AccessScheme.toTwoTwoFin_sources
    {Secret Key : Type*} {t' n' : ℕ} {Share' : Fin n' → Type*}
    (scheme' : AccessScheme Secret Key (Fin n') Share')
    (haccess : scheme'.access = AccessStructure.threshold (Fin n') t')
    (ht' : 2 ≤ t') (htn' : t' ≤ n') :
    (scheme'.toTwoTwoFin haccess ht' htn').sources = scheme'.sources :=
  rfl

/-- Non-existence of `(t, n, 2, 2)` distribution designs whenever `2 ≤ t ≤ n` and `3 ≤ n`
([ACOR22]; [Aggarwal2026], Section 5). -/
theorem no_thresholdDesign_two_two {t n : ℕ} (ht : 2 ≤ t) (htn : t ≤ n) (hn : 3 ≤ n) :
    IsEmpty (ThresholdDesign t n 2 2) := by
  refine ⟨fun d => ?_⟩
  by_cases ht2 : t = 2
  · subst ht2
    have hle1 (i : Fin n) : (d.assign i).card ≤ 1 := by
      have h := d.card_lt_of_card_eq_sub_one (by decide) (Finset.card_singleton i)
      rw [Finset.singleton_biUnion] at h
      omega
    have heq1 (i : Fin n) : (d.assign i).card = 1 := by
      have hne : ∃ j : Fin n, j ≠ i := by
        by_cases hi : i = ⟨0, by omega⟩
        · exact ⟨⟨1, by omega⟩, by simp [hi, Fin.ext_iff]⟩
        · exact ⟨⟨0, by omega⟩, Ne.symm hi⟩
      obtain ⟨j, hji⟩ := hne
      have hpair : 2 ≤ (({i, j} : Finset (Fin n)).biUnion d.assign).card :=
        d.le_card_of_card_eq (Finset.card_pair hji.symm)
      rw [Finset.biUnion_insert, Finset.singleton_biUnion] at hpair
      have hle := Finset.card_union_le (d.assign i) (d.assign j)
      have hj1 := hle1 j
      have hi1 := hle1 i
      omega
    have hinj : Function.Injective d.assign := by
      intro i j hij
      by_contra hne
      have hpair : 2 ≤ (({i, j} : Finset (Fin n)).biUnion d.assign).card :=
        d.le_card_of_card_eq (Finset.card_pair hne)
      rw [Finset.biUnion_insert, Finset.singleton_biUnion, hij, Finset.union_idempotent, heq1 j]
        at hpair
      omega
    have hex : ∀ i : Fin n, ∃ x : Fin 2, d.assign i = {x} := fun i =>
      Finset.card_eq_one.mp (heq1 i)
    choose f hf using hex
    have hfinj : Function.Injective f := by
      intro i j hij
      exact hinj (by rw [hf i, hf j, hij])
    have hcard := Fintype.card_le_of_injective f hfinj
    simp only [Fintype.card_fin] at hcard
    omega
  · have ht3 : 3 ≤ t := by omega
    have hpair (i j : Fin n) : (d.assign i ∪ d.assign j).card ≤ 1 := by
      have hij_le : ({i, j} : Finset (Fin n)).card ≤ t - 1 := by
        have h2 : ({i, j} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
        omega
      obtain ⟨u, hu_sup, hcard⟩ :=
        exists_superset_card_eq hij_le (by rw [Fintype.card_fin]; omega)
      have hlt := d.card_lt_of_card_eq_sub_one (by omega) hcard
      have hsub : d.assign i ∪ d.assign j ⊆ u.biUnion d.assign := by
        intro x hx
        rw [Finset.mem_biUnion]
        rcases Finset.mem_union.mp hx with hxi | hxj
        · exact ⟨i, hu_sup (Finset.mem_insert_self i {j}), hxi⟩
        · exact ⟨j, hu_sup (Finset.mem_insert_of_mem (Finset.mem_singleton_self j)), hxj⟩
      have hle := Finset.card_le_card hsub
      omega
    have huniv : 2 ≤ ((Finset.univ : Finset (Fin n)).biUnion d.assign).card := by
      have h := (d.authorized_iff (Finset.univ : Finset (Fin n))).mp (by
        simp only [AccessStructure.threshold_authorized_iff, Finset.card_univ, Fintype.card_fin]
        exact htn)
      simp only [AccessStructure.threshold_authorized_iff] at h
      exact h
    by_cases hnonempty : ∃ i₀ : Fin n, (d.assign i₀).Nonempty
    · obtain ⟨i₀, x, hx₀⟩ := hnonempty
      have hsub_all (j : Fin n) : d.assign j ⊆ {x} := by
        intro y hy
        rw [Finset.mem_singleton]
        by_contra hyx
        have h2 : ({x, y} : Finset (Fin 2)).card ≤ (d.assign i₀ ∪ d.assign j).card := by
          refine Finset.card_le_card ?_
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hzy
          · exact Finset.mem_union_left _ hx₀
          · rw [Finset.mem_singleton.mp hzy]
            exact Finset.mem_union_right _ hy
        rw [Finset.card_pair (Ne.symm hyx)] at h2
        have hp := hpair i₀ j
        omega
      have huniv_sub : (Finset.univ : Finset (Fin n)).biUnion d.assign ⊆ {x} := by
        intro z hz
        obtain ⟨j, _, hzj⟩ := Finset.mem_biUnion.mp hz
        exact hsub_all j hzj
      have hle := Finset.card_le_card huniv_sub
      simp only [Finset.card_singleton] at hle
      omega
    · push Not at hnonempty
      have huniv_empty : (Finset.univ : Finset (Fin n)).biUnion d.assign = ∅ := by
        ext z
        simp [hnonempty]
      rw [huniv_empty, Finset.card_empty] at huniv
      omega

/-- No `(2, 3, 2, 2)` distribution design exists ([ACOR22]; [Aggarwal2026], Section 5). -/
theorem not_exists_design_2_3_2_2 : IsEmpty (ThresholdDesign 2 3 2 2) :=
  no_thresholdDesign_two_two (by decide) (by decide) (by decide)

/-- No `(r, r, 2, 2)` distribution design exists for `r ≥ 3` ([ACOR22]; [Aggarwal2026],
Section 5). -/
theorem not_exists_design_r_r_2_2 {r : ℕ} (hr : 3 ≤ r) : IsEmpty (ThresholdDesign r r 2 2) :=
  no_thresholdDesign_two_two (by omega) le_rfl hr

end ThresholdDesign

end Cslib.Crypto.Protocols.SecretSharing
