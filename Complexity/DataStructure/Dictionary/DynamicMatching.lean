/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Probability.PMF.Expect
public import Complexity.Probability.PMF.Uniform
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Log
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Multi-Round Unit-Circle Dynamic Matching

This file formalizes the multi-round consistent-hashing dynamic matching scheme of Tianxiao Li,
Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic Dictionary with Subconstant Wasted Bits per
Key* ([LiLiangYuZhou2024, Section 3.1, Problem 3.1, Algorithm 1, Lemma 3.2, and Claims 3.3–3.4];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF pp. 6–9 / printed pp. 5–8), building
on consistent hashing on the unit circle ([KargerLehmanLeightonPanigrahyLevineLewin1997]) and
memoryless worker-task assignment ([BergerKuszmaulPolakTidorWein2022]).

Given a key-ID (ball) universe `Fin U'` and a slot (bin) universe `Fin n'` (`n' ≤ U'`), a matching
scheme `h : Scheme U' n'` consists of `U'` permutations on `Fin (U' + n')` (matching the
independent Fisher–Yates permutations sampled at initialization on the Word RAM). In round `i`, all
remaining balls `A_i ⊆ Fin U'` and bins `B_i ⊆ Fin n'` are placed on the discrete circle
`Fin (U' + n')` via `h i`; each ball `a ∈ A_i` whose clockwise-next occupied circle position belongs
to a bin `b ∈ B_i` is matched to `b`, and both `a` and `b` are removed before round `i + 1`.

Because `h` is fixed in advance, the resulting assignment `matching h A` (for `B = Finset.univ` of
all `n'` slots, or more generally `matchOptOn h A B` for any `B` with `A.card ≤ B.card`) depends
solely on `h` and the current active set `A`. For any fixed `h` with `T := rounds h A`, when active
cardinality stays `≤ n'`, a single insertion or deletion changes at most `2 * (T + 1)` ball
assignments ([LiLiangYuZhou2024, Claim 3.4]), and an atomic replacement `insert y (A.erase x)`
changes at most `4 * T + 6` assignments ([LiLiangYuZhou2024, Section 5.2 via Claim 3.4]). Under
uniform independent permutations (`schemePMF`), the expected round count is at most
`⌈log₂ |A|⌉ + 2 = O(log (max |A| 2))` ([LiLiangYuZhou2024, Claim 3.3]), giving expected
`O(log (max |A| 2))` single-update relocation cost ([LiLiangYuZhou2024, Lemma 3.2]).

## Scope note

This module supplies the pure mathematical dynamic-matching primitive for the
large-parameter-regime dynamic dictionary of [LiLiangYuZhou2024, Section 5]. Word-RAM Fisher–Yates
permutation sampling, precomputed lookup-table evaluation, variable-length `B`-way word/bit
adapters (Section 3.3), adapter trees (Section 4), strong history independence, dynamic resizing,
and super-polynomial key universes are not formalized here.

## Main definitions

* `Cslib.DataStructure.Dictionary.DynamicMatching.RoundPerm`, `Scheme`, `schemePMF`: single-round
  permutation on `Fin (U' + n')`, `U'`-round matching scheme, and uniform distribution on schemes.
* `Cslib.DataStructure.Dictionary.DynamicMatching.roundMatchOpt`, `roundStep`, `stateAt`,
  `roundsOn`, `rounds`, `matchOptOn`, `matchOpt`, `matching`, `relocDist`: Algorithm 1 round
  transition, round count `T`, partial assignment `Fin U' → Option (Fin n')`, canonical injection
  `A ↪ Fin n'`, and ball-relocation distance `Δ`.

## Main results

* `card_balls_roundStep_lt`, `stateAt_balls_eq_empty`, `roundsOn_le_card`, `rounds_le_card`,
  `matchOptOn_isSome_iff`, `matchOptOn_injective`, `matchOpt_isSome_iff`, `matchOpt_injective`,
  `matching_apply`: termination within `A.card` rounds and canonical injection properties.
* `expect_roundsOn_le`, `expect_rounds_le`: expected round bound
  `𝔼[T] ≤ ⌈log₂ |A|⌉ + 2 ≤ 3 * ⌈log₂ (max |A| 2)⌉` ([LiLiangYuZhou2024, Claim 3.3]).
* `relocDist_insert_le`, `relocDist_delete_le`, `relocDist_replace_le`,
  `expect_relocDist_insert_le`, `expect_relocDist_delete_le`, `expect_relocDist_replace_le`:
  deterministic `O(T)` and expected `O(log (max |A| 2))` relocation bounds
  ([LiLiangYuZhou2024, Claim 3.4 and Lemma 3.2]).

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
* [D. R. Karger, E. Lehman, F. T. Leighton, R. Panigrahy, M. S. Levine, and D. Lewin,
  *Consistent Hashing and Random Trees: Distributed Caching Protocols for Relieving Hot Spots on
  the World Wide Web*][KargerLehmanLeightonPanigrahyLevineLewin1997]
* [A. Berger, W. Kuszmaul, A. Polak, J. Tidor, and N. Wein,
  *Memoryless Worker-Task Assignment with Polylogarithmic Switching
  Cost*][BergerKuszmaulPolakTidorWein2022]
-/

public section

namespace Cslib.DataStructure.Dictionary.DynamicMatching

open Finset
open scoped symmDiff BigOperators ENNReal

/-- Single-round permutation on the combined universe `Fin (U' + n')` of `U'` balls and `n'`
bins. -/
abbrev RoundPerm (U' n' : ℕ) := Equiv.Perm (Fin (U' + n'))

/-- Predetermined `U'`-round dynamic matching scheme (`Algorithm 1`, line 1). -/
abbrev Scheme (U' n' : ℕ) := Fin U' → RoundPerm U' n'

/-- Uniform distribution over `U'` independent permutations on `Fin (U' + n')`. -/
@[expose]
noncomputable def schemePMF (U' n' : ℕ) : PMF (Scheme U' n') :=
  Cslib.Probability.PMF.uniformOfFintype (Scheme U' n')

theorem schemePMF_eq_uniformOfFintype (U' n' : ℕ) :
    schemePMF U' n' = Cslib.Probability.PMF.uniformOfFintype (Scheme U' n') :=
  rfl

/-- Embed ball `a : Fin U'` into the combined item space `Fin (U' + n')`. -/
private def ballItem {U' : ℕ} (n' : ℕ) (a : Fin U') : Fin (U' + n') :=
  Fin.castAdd n' a

/-- Embed bin `b : Fin n'` into the combined item space `Fin (U' + n')`. -/
private def binItem (U' : ℕ) {n' : ℕ} (b : Fin n') : Fin (U' + n') :=
  Fin.natAdd U' b

private theorem ballItem_injective (U' n' : ℕ) : Function.Injective (ballItem (U' := U') n') :=
  fun _ _ h => Fin.ext (by simpa [ballItem] using congrArg Fin.val h)

private theorem binItem_injective (U' n' : ℕ) : Function.Injective (binItem U' (n' := n')) :=
  fun _ _ h => Fin.ext (by simpa [binItem] using congrArg Fin.val h)

/-- Test whether a combined item `z : Fin (U' + n')` is a bin `binItem U' b`. -/
def asBin? {U' n' : ℕ} (z : Fin (U' + n')) : Option (Fin n') :=
  if h : U' ≤ z.val then some ⟨z.val - U', by omega⟩ else none

@[simp]
private theorem asBin?_ballItem {U' n' : ℕ} (a : Fin U') : asBin? (ballItem n' a) = none := by
  simp [asBin?, ballItem, Nat.not_le_of_gt a.isLt]

@[simp]
private theorem asBin?_binItem {U' n' : ℕ} (b : Fin n') : asBin? (binItem U' b) = some b := by
  ext
  simp [asBin?, binItem]

private theorem asBin?_eq_some_iff {U' n' : ℕ} {z : Fin (U' + n')} {b : Fin n'} :
    asBin? z = some b ↔ z = binItem U' b := by
  constructor
  · intro h
    dsimp only [asBin?] at h
    split_ifs at h with hle
    · injection h with hb
      ext
      have hbval : z.val - U' = b.val := congrArg Fin.val hb
      simp [binItem]; omega
  · rintro rfl
    exact asBin?_binItem b

private theorem asBin?_eq_none_iff {U' n' : ℕ} {z : Fin (U' + n')} :
    asBin? z = none ↔ ∃ a : Fin U', z = ballItem n' a := by
  constructor
  · intro h
    dsimp only [asBin?] at h
    split_ifs at h with hle
    refine ⟨⟨z.val, by omega⟩, ?_⟩
    ext; simp [ballItem]
  · rintro ⟨a, rfl⟩
    exact asBin?_ballItem a

/-- Combined active item set `A ⊕ B` inside `Fin (U' + n')`. -/
private def activeItems {U' n' : ℕ} (A : Finset (Fin U')) (B : Finset (Fin n')) :
    Finset (Fin (U' + n')) :=
  A.map ⟨ballItem n', ballItem_injective U' n'⟩ ∪ B.map ⟨binItem U', binItem_injective U' n'⟩

@[simp]
private theorem ballItem_mem_activeItems {U' n' : ℕ} {A : Finset (Fin U')} {B : Finset (Fin n')}
    {a : Fin U'} : ballItem n' a ∈ activeItems A B ↔ a ∈ A := by
  simp only [activeItems, mem_union, mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro (⟨a', ha', heq⟩ | ⟨b, _, heq⟩)
    · exact ballItem_injective U' n' heq ▸ ha'
    · exfalso
      have hval : (binItem U' b).val = (ballItem n' a).val := congrArg Fin.val heq
      simp only [ballItem, binItem, Fin.val_castAdd, Fin.val_natAdd] at hval
      omega
  · intro ha; exact Or.inl ⟨a, ha, rfl⟩

@[simp]
private theorem binItem_mem_activeItems {U' n' : ℕ} {A : Finset (Fin U')} {B : Finset (Fin n')}
    {b : Fin n'} : binItem U' b ∈ activeItems A B ↔ b ∈ B := by
  simp only [activeItems, mem_union, mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro (⟨a, _, heq⟩ | ⟨b', hb', heq⟩)
    · exfalso
      have hval : (ballItem n' a).val = (binItem U' b).val := congrArg Fin.val heq
      simp only [ballItem, binItem, Fin.val_castAdd, Fin.val_natAdd] at hval
      omega
    · exact binItem_injective U' n' heq ▸ hb'
  · intro hb; exact Or.inr ⟨b, hb, rfl⟩

private theorem mem_activeItems_iff {U' n' : ℕ} {A : Finset (Fin U')} {B : Finset (Fin n')}
    {z : Fin (U' + n')} :
    z ∈ activeItems A B ↔
      (∃ a ∈ A, z = ballItem n' a) ∨ (∃ b ∈ B, z = binItem U' b) := by
  simp only [activeItems, mem_union, mem_map, Function.Embedding.coeFn_mk]
  simp only [eq_comm]

private theorem card_activeItems {U' n' : ℕ} (A : Finset (Fin U')) (B : Finset (Fin n')) :
    (activeItems A B).card = A.card + B.card := by
  rw [activeItems, card_union_of_disjoint, card_map, card_map]
  rw [disjoint_left]
  intro z hzA hzB
  rcases mem_map.mp hzA with ⟨a, _, rfl⟩
  rcases mem_map.mp hzB with ⟨b, _, heq⟩
  have hval : (binItem U' b).val = (ballItem n' a).val := congrArg Fin.val heq
  simp only [ballItem, binItem, Fin.val_castAdd, Fin.val_natAdd] at hval
  omega

/-! ### Clockwise successor on a finite circle subset -/

/-- Clockwise successor of `p` inside `P : Finset (Fin M)`: the smallest element of `P` strictly
greater than `p`, wrapping around to `P.min'` when `p` is at or above all elements of `P`. -/
private def clockwiseNextPos {M : ℕ} (P : Finset (Fin M)) (p : Fin M) : Fin M :=
  let gt := P.filter (p < ·)
  if hgt : gt.Nonempty then gt.min' hgt
  else if hP : P.Nonempty then P.min' hP
  else p

private theorem clockwiseNextPos_mem {M : ℕ} {P : Finset (Fin M)} (hP : P.Nonempty) (p : Fin M) :
    clockwiseNextPos P p ∈ P := by
  dsimp only [clockwiseNextPos]
  split_ifs with hgt
  · exact (mem_filter.mp (min'_mem _ hgt)).1
  · exact min'_mem P hP

private theorem clockwiseNextPos_injective {M : ℕ} (P : Finset (Fin M)) :
    Set.InjOn (clockwiseNextPos P) (P : Set (Fin M)) := by
  intro p₁ hp₁ p₂ hp₂ heq
  have hP : P.Nonempty := ⟨p₁, hp₁⟩
  dsimp only [clockwiseNextPos] at heq
  split_ifs at heq with hgt₁ hgt₂ hgt₂
  · by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hp₂_in : p₂ ∈ P.filter (p₁ < ·) := mem_filter.mpr ⟨hp₂, hlt⟩
      have hle : (P.filter (p₁ < ·)).min' hgt₁ ≤ p₂ := min'_le _ p₂ hp₂_in
      have hgt' : p₂ < (P.filter (p₂ < ·)).min' hgt₂ :=
        (mem_filter.mp (min'_mem _ hgt₂)).2
      exact lt_irrefl _ (lt_of_le_of_lt (heq ▸ hle) hgt')
    · have hp₁_in : p₁ ∈ P.filter (p₂ < ·) := mem_filter.mpr ⟨hp₁, hgt⟩
      have hle : (P.filter (p₂ < ·)).min' hgt₂ ≤ p₁ := min'_le _ p₁ hp₁_in
      have hgt' : p₁ < (P.filter (p₁ < ·)).min' hgt₁ :=
        (mem_filter.mp (min'_mem _ hgt₁)).2
      exact lt_irrefl _ (lt_of_le_of_lt (heq.symm ▸ hle) hgt')
  · exfalso
    have hgt' : p₁ < (P.filter (p₁ < ·)).min' hgt₁ := (mem_filter.mp (min'_mem _ hgt₁)).2
    have hmin : P.min' hP ≤ p₁ := min'_le P p₁ hp₁
    exact lt_irrefl _ (lt_of_le_of_lt hmin (heq ▸ hgt'))
  · exfalso
    have hgt' : p₂ < (P.filter (p₂ < ·)).min' hgt₂ := (mem_filter.mp (min'_mem _ hgt₂)).2
    have hmin : P.min' hP ≤ p₂ := min'_le P p₂ hp₂
    exact lt_irrefl _ (lt_of_le_of_lt hmin (heq.symm ▸ hgt'))
  · have hmax₁ : ∀ q ∈ P, q ≤ p₁ := fun q hq =>
      le_of_not_gt fun hlt => hgt₁ ⟨q, mem_filter.mpr ⟨hq, hlt⟩⟩
    have hmax₂ : ∀ q ∈ P, q ≤ p₂ := fun q hq =>
      le_of_not_gt fun hlt => hgt₂ ⟨q, mem_filter.mpr ⟨hq, hlt⟩⟩
    exact le_antisymm (hmax₂ p₁ hp₁) (hmax₁ p₂ hp₂)

private theorem exists_clockwiseNextPos_notMem {M : ℕ} {P Q : Finset (Fin M)}
    (hQ : Q.Nonempty) (hdiff : (P \ Q).Nonempty) :
    ∃ q ∈ Q, clockwiseNextPos P q ∉ Q := by
  by_contra hclosed
  push Not at hclosed
  by_cases habove : ((P \ Q).filter (Q.min' hQ < ·)).Nonempty
  · set bStar := ((P \ Q).filter (Q.min' hQ < ·)).min' habove
    have hbStar_mem : bStar ∈ (P \ Q).filter (Q.min' hQ < ·) := min'_mem _ habove
    have hbStar_P : bStar ∈ P := (mem_sdiff.mp (mem_filter.mp hbStar_mem).1).1
    have hbStar_notQ : bStar ∉ Q := (mem_sdiff.mp (mem_filter.mp hbStar_mem).1).2
    have hQlt_ne : (Q.filter (· < bStar)).Nonempty :=
      ⟨Q.min' hQ, mem_filter.mpr ⟨min'_mem Q hQ, (mem_filter.mp hbStar_mem).2⟩⟩
    set qStar := (Q.filter (· < bStar)).max' hQlt_ne
    have hqStar_mem : qStar ∈ Q.filter (· < bStar) := max'_mem _ hQlt_ne
    have hqStar_Q : qStar ∈ Q := (mem_filter.mp hqStar_mem).1
    have hqStar_lt : qStar < bStar := (mem_filter.mp hqStar_mem).2
    have hgt_ne : (P.filter (qStar < ·)).Nonempty := ⟨bStar, mem_filter.mpr ⟨hbStar_P, hqStar_lt⟩⟩
    have hnext_eq : clockwiseNextPos P qStar = (P.filter (qStar < ·)).min' hgt_ne := by
      simp [clockwiseNextPos, hgt_ne]
    have hnext_Q : clockwiseNextPos P qStar ∈ Q := hclosed qStar hqStar_Q
    have hnext_gt : qStar < clockwiseNextPos P qStar := by
      rw [hnext_eq]; exact (mem_filter.mp (min'_mem _ hgt_ne)).2
    have hnext_le : clockwiseNextPos P qStar ≤ bStar := by
      rw [hnext_eq]; exact min'_le _ bStar (mem_filter.mpr ⟨hbStar_P, hqStar_lt⟩)
    have hnext_lt : clockwiseNextPos P qStar < bStar :=
      lt_of_le_of_ne hnext_le fun heq => hbStar_notQ (heq ▸ hnext_Q)
    have hle_max : clockwiseNextPos P qStar ≤ qStar :=
      le_max' _ _ (mem_filter.mpr ⟨hnext_Q, hnext_lt⟩)
    exact lt_irrefl _ (lt_of_lt_of_le hnext_gt hle_max)
  · rcases hdiff with ⟨b₀, hb₀⟩
    have hb₀_P : b₀ ∈ P := (mem_sdiff.mp hb₀).1
    have hall_lt : ∀ b ∈ P \ Q, b < Q.min' hQ := by
      intro b hb
      have hle : b ≤ Q.min' hQ :=
        le_of_not_gt fun hgt => habove ⟨b, mem_filter.mpr ⟨hb, hgt⟩⟩
      exact lt_of_le_of_ne hle fun heq => (mem_sdiff.mp hb).2 (heq ▸ min'_mem Q hQ)
    have hP_ne : P.Nonempty := ⟨b₀, hb₀_P⟩
    have hmin_lt : P.min' hP_ne < Q.min' hQ :=
      lt_of_le_of_lt (min'_le P b₀ hb₀_P) (hall_lt b₀ hb₀)
    have hmin_notQ : P.min' hP_ne ∉ Q := fun hm =>
      lt_irrefl _ (lt_of_le_of_lt (min'_le Q _ hm) hmin_lt)
    set qMax := Q.max' hQ
    have hqMax_Q : qMax ∈ Q := max'_mem Q hQ
    have hgt_empty : ¬(P.filter (qMax < ·)).Nonempty := by
      rintro ⟨y, hy⟩
      obtain ⟨hyP, hlt⟩ := mem_filter.mp hy
      by_cases hyQ : y ∈ Q
      · exact lt_irrefl _ (lt_of_lt_of_le hlt (le_max' Q y hyQ))
      · have hy_lt : y < Q.min' hQ := hall_lt y (mem_sdiff.mpr ⟨hyP, hyQ⟩)
        exact lt_irrefl _ (lt_trans (lt_of_le_of_lt (min'_le Q qMax hqMax_Q) hlt) hy_lt)
    have hnext_eq : clockwiseNextPos P qMax = P.min' hP_ne := by
      simp [clockwiseNextPos, hgt_empty, hP_ne]
    exact hmin_notQ (hnext_eq ▸ hclosed qMax hqMax_Q)

/-- Inserting one new point `pStar ∉ P` into a nonempty circle subset `P` splices `pStar`
immediately after a unique predecessor `x₀ ∈ P`, leaving `clockwiseNextPos` unchanged on every
`x ∈ P \ {x₀}`. -/
private theorem exists_insert_clockwiseNextPos {M : ℕ} {P : Finset (Fin M)} (hP : P.Nonempty)
    {pStar : Fin M} (hp : pStar ∉ P) :
    ∃ x₀ ∈ P,
      clockwiseNextPos (insert pStar P) x₀ = pStar ∧
      clockwiseNextPos (insert pStar P) pStar = clockwiseNextPos P x₀ ∧
      ∀ x ∈ P, x ≠ x₀ → clockwiseNextPos (insert pStar P) x = clockwiseNextPos P x := by
  have hP' : (insert pStar P).Nonempty := insert_nonempty pStar P
  by_cases hlt_ne : (P.filter (· < pStar)).Nonempty
  · set x₀ := (P.filter (· < pStar)).max' hlt_ne
    have hx₀_mem : x₀ ∈ P.filter (· < pStar) := max'_mem _ hlt_ne
    have hx₀_P : x₀ ∈ P := (mem_filter.mp hx₀_mem).1
    have hx₀_lt : x₀ < pStar := (mem_filter.mp hx₀_mem).2
    have hgap : ∀ z ∈ P, x₀ < z → pStar < z := by
      intro z hz hxz
      have hle : pStar ≤ z :=
        le_of_not_gt fun hzp =>
          lt_irrefl _ (lt_of_lt_of_le hxz (le_max' _ z (mem_filter.mpr ⟨hz, hzp⟩)))
      exact lt_of_le_of_ne hle fun heq => hp (heq ▸ hz)
    refine ⟨x₀, hx₀_P, ?_, ?_, ?_⟩
    · have hgt' : ((insert pStar P).filter (x₀ < ·)).Nonempty :=
        ⟨pStar, mem_filter.mpr ⟨mem_insert_self pStar P, hx₀_lt⟩⟩
      simp only [clockwiseNextPos, hgt', ↓reduceDIte]
      refine le_antisymm
        (min'_le ((insert pStar P).filter (x₀ < ·)) pStar
          (mem_filter.mpr ⟨mem_insert_self pStar P, hx₀_lt⟩)) ?_
      refine le_min' ((insert pStar P).filter (x₀ < ·)) hgt' pStar fun z hz => ?_
      obtain ⟨hz_ins, hxz⟩ := mem_filter.mp hz
      rcases mem_insert.mp hz_ins with rfl | hzP
      · exact le_rfl
      · exact (hgap z hzP hxz).le
    · have hfilt_eq : (insert pStar P).filter (pStar < ·) = P.filter (x₀ < ·) := by
        ext z
        simp only [mem_filter, mem_insert]
        constructor
        · rintro ⟨rfl | hzP, hpz⟩
          · exact absurd hpz (lt_irrefl _)
          · exact ⟨hzP, lt_trans hx₀_lt hpz⟩
        · rintro ⟨hzP, hxz⟩
          exact ⟨Or.inr hzP, hgap z hzP hxz⟩
      have hmin_eq : (insert pStar P).min' hP' = P.min' hP := by
        refine le_antisymm (min'_le _ _ (mem_insert_of_mem (min'_mem P hP))) ?_
        refine le_min' (insert pStar P) hP' (P.min' hP) fun z hz => ?_
        rcases mem_insert.mp hz with rfl | hzP
        · exact le_trans (min'_le P x₀ hx₀_P) hx₀_lt.le
        · exact min'_le P z hzP
      dsimp only [clockwiseNextPos]
      simp only [hfilt_eq]
      split_ifs with hgt
      · rfl
      · exact hmin_eq
    · intro x hx hxne
      rcases lt_or_gt_of_ne hxne with hxx₀ | hx₀x
      · have hgtP : (P.filter (x < ·)).Nonempty := ⟨x₀, mem_filter.mpr ⟨hx₀_P, hxx₀⟩⟩
        have hgtP' : ((insert pStar P).filter (x < ·)).Nonempty :=
          ⟨x₀, mem_filter.mpr ⟨mem_insert_of_mem hx₀_P, hxx₀⟩⟩
        simp only [clockwiseNextPos, hgtP', hgtP, ↓reduceDIte]
        refine le_antisymm ?_ ?_
        · refine min'_le ((insert pStar P).filter (x < ·)) _
            (mem_filter.mpr ⟨mem_insert_of_mem ?_, ?_⟩)
          · exact (mem_filter.mp (min'_mem _ hgtP)).1
          · exact (mem_filter.mp (min'_mem _ hgtP)).2
        · refine le_min' ((insert pStar P).filter (x < ·)) hgtP' _ fun z hz => ?_
          obtain ⟨hz_ins, hxz⟩ := mem_filter.mp hz
          rcases mem_insert.mp hz_ins with rfl | hzP
          · exact le_trans (min'_le _ x₀ (mem_filter.mpr ⟨hx₀_P, hxx₀⟩)) hx₀_lt.le
          · exact min'_le _ z (mem_filter.mpr ⟨hzP, hxz⟩)
      · have hpx : pStar < x := hgap x hx hx₀x
        have hfilt_eq : (insert pStar P).filter (x < ·) = P.filter (x < ·) := by
          ext z
          simp only [mem_filter, mem_insert]
          constructor
          · rintro ⟨rfl | hzP, hxz⟩
            · exact absurd (lt_trans hpx hxz) (lt_irrefl _)
            · exact ⟨hzP, hxz⟩
          · rintro ⟨hzP, hxz⟩
            exact ⟨Or.inr hzP, hxz⟩
        have hmin_eq : (insert pStar P).min' hP' = P.min' hP := by
          refine le_antisymm (min'_le _ _ (mem_insert_of_mem (min'_mem P hP))) ?_
          refine le_min' (insert pStar P) hP' (P.min' hP) fun z hz => ?_
          rcases mem_insert.mp hz with rfl | hzP
          · exact le_trans (min'_le P x₀ hx₀_P) hx₀_lt.le
          · exact min'_le P z hzP
        dsimp only [clockwiseNextPos]
        simp only [hfilt_eq]
        split_ifs with hgt
        · rfl
        · exact hmin_eq
  · -- `pStar` is strictly below every element of `P`
    have hall_gt : ∀ z ∈ P, pStar < z := by
      intro z hz
      have hle : pStar ≤ z :=
        le_of_not_gt fun hzp => hlt_ne ⟨z, mem_filter.mpr ⟨hz, hzp⟩⟩
      exact lt_of_le_of_ne hle fun heq => hp (heq ▸ hz)
    set x₀ := P.max' hP
    have hx₀_P : x₀ ∈ P := max'_mem P hP
    have hmin_pStar : (insert pStar P).min' hP' = pStar := by
      refine le_antisymm (min'_le _ pStar (mem_insert_self pStar P)) ?_
      refine le_min' (insert pStar P) hP' pStar fun z hz => ?_
      rcases mem_insert.mp hz with rfl | hzP
      · exact le_rfl
      · exact (hall_gt z hzP).le
    refine ⟨x₀, hx₀_P, ?_, ?_, ?_⟩
    · have hgt_empty : ¬((insert pStar P).filter (x₀ < ·)).Nonempty := by
        rintro ⟨z, hz⟩
        obtain ⟨hz_ins, hxz⟩ := mem_filter.mp hz
        rcases mem_insert.mp hz_ins with rfl | hzP
        · exact lt_irrefl _ (lt_trans (hall_gt x₀ hx₀_P) hxz)
        · exact lt_irrefl _ (lt_of_lt_of_le hxz (le_max' P z hzP))
      simp only [clockwiseNextPos, hgt_empty, hP', ↓reduceDIte]
      exact hmin_pStar
    · have hgt_empty_P : ¬(P.filter (x₀ < ·)).Nonempty := by
        rintro ⟨z, hz⟩
        obtain ⟨hzP, hxz⟩ := mem_filter.mp hz
        exact lt_irrefl _ (lt_of_lt_of_le hxz (le_max' P z hzP))
      have hfilt_pStar : (insert pStar P).filter (pStar < ·) = P := by
        ext z
        simp only [mem_filter, mem_insert]
        constructor
        · rintro ⟨rfl | hzP, hpz⟩
          · exact absurd hpz (lt_irrefl _)
          · exact hzP
        · intro hzP
          exact ⟨Or.inr hzP, hall_gt z hzP⟩
      simp only [clockwiseNextPos, hfilt_pStar, hP, hgt_empty_P, ↓reduceDIte]
    · intro x hx hxne
      have hxx₀ : x < x₀ := lt_of_le_of_ne (le_max' P x hx) hxne
      have hgtP : (P.filter (x < ·)).Nonempty := ⟨x₀, mem_filter.mpr ⟨hx₀_P, hxx₀⟩⟩
      have hfilt_eq : (insert pStar P).filter (x < ·) = P.filter (x < ·) := by
        ext z
        simp only [mem_filter, mem_insert]
        constructor
        · rintro ⟨rfl | hzP, hxz⟩
          · exact absurd (lt_trans (hall_gt x hx) hxz) (lt_irrefl _)
          · exact ⟨hzP, hxz⟩
        · rintro ⟨hzP, hxz⟩
          exact ⟨Or.inr hzP, hxz⟩
      simp only [clockwiseNextPos, hfilt_eq, hgtP, ↓reduceDIte]

/-! ### Permuted item circle and single-round matching -/

/-- Clockwise next active item in `S : Finset (Fin (U' + n'))` after `z`, ordered along the circle
by permutation `π`. -/
private def nextItem {M : ℕ} (π : Equiv.Perm (Fin M)) (S : Finset (Fin M)) (z : Fin M) : Fin M :=
  π.symm (clockwiseNextPos (S.map π.toEmbedding) (π z))

private theorem nextItem_mem {M : ℕ} (π : Equiv.Perm (Fin M)) {S : Finset (Fin M)} (hS : S.Nonempty)
    (z : Fin M) : nextItem π S z ∈ S := by
  have hP : (S.map π.toEmbedding).Nonempty := Finset.map_nonempty.mpr hS
  have hmem := clockwiseNextPos_mem hP (π z)
  rcases mem_map.mp hmem with ⟨w, hw, heq⟩
  dsimp only [nextItem]
  rw [← heq]
  simpa using hw

private theorem nextItem_injective {M : ℕ} (π : Equiv.Perm (Fin M)) (S : Finset (Fin M)) :
    Set.InjOn (nextItem π S) (S : Set (Fin M)) := by
  intro z₁ hz₁ z₂ hz₂ heq
  dsimp only [nextItem] at heq
  have heq' := π.symm.injective heq
  have hp₁ : π z₁ ∈ S.map π.toEmbedding := mem_map.mpr ⟨z₁, hz₁, rfl⟩
  have hp₂ : π z₂ ∈ S.map π.toEmbedding := mem_map.mpr ⟨z₂, hz₂, rfl⟩
  exact π.injective (clockwiseNextPos_injective _ hp₁ hp₂ heq')

private theorem exists_nextItem_notMem {M : ℕ} (π : Equiv.Perm (Fin M)) {S Q : Finset (Fin M)}
    (hQ : Q.Nonempty) (hdiff : (S \ Q).Nonempty) :
    ∃ q ∈ Q, nextItem π S q ∉ Q := by
  set P := S.map π.toEmbedding
  set QP := Q.map π.toEmbedding
  have hQP_ne : QP.Nonempty := Finset.map_nonempty.mpr hQ
  have hdiffP : (P \ QP).Nonempty := by
    rcases hdiff with ⟨b, hb⟩
    refine ⟨π b, mem_sdiff.mpr ⟨mem_map.mpr ⟨b, (mem_sdiff.mp hb).1, rfl⟩, ?_⟩⟩
    rintro hmem
    rcases mem_map.mp hmem with ⟨q, hq, heq⟩
    exact (mem_sdiff.mp hb).2 (π.injective heq ▸ hq)
  rcases exists_clockwiseNextPos_notMem hQP_ne hdiffP with ⟨p, hpQP, hpnot⟩
  rcases mem_map.mp hpQP with ⟨q, hq, rfl⟩
  refine ⟨q, hq, fun hnextQ => hpnot ?_⟩
  refine mem_map.mpr ⟨nextItem π S q, hnextQ, ?_⟩
  simp [nextItem, P]

private theorem exists_insert_nextItem {M : ℕ} (π : Equiv.Perm (Fin M)) {S : Finset (Fin M)}
    (hS : S.Nonempty) {zStar : Fin M} (hz : zStar ∉ S) :
    ∃ x₀ ∈ S,
      nextItem π (insert zStar S) x₀ = zStar ∧
      nextItem π (insert zStar S) zStar = nextItem π S x₀ ∧
      ∀ w ∈ S, w ≠ x₀ → nextItem π (insert zStar S) w = nextItem π S w := by
  have hpStar : π zStar ∉ S.map π.toEmbedding := by
    rintro hmem
    rcases mem_map.mp hmem with ⟨w, hw, heq⟩
    exact hz (π.injective heq ▸ hw)
  have hmap_ins : (insert zStar S).map π.toEmbedding = insert (π zStar) (S.map π.toEmbedding) :=
    map_insert π.toEmbedding zStar S
  have hP : (S.map π.toEmbedding).Nonempty := Finset.map_nonempty.mpr hS
  rcases exists_insert_clockwiseNextPos hP hpStar with ⟨p₀, hp₀, h1, h2, h3⟩
  rcases mem_map.mp hp₀ with ⟨x₀, hx₀, rfl⟩
  simp only [Equiv.coe_toEmbedding] at h1 h2 h3
  refine ⟨x₀, hx₀, ?_, ?_, ?_⟩
  · simp [nextItem, hmap_ins, h1]
  · simp [nextItem, hmap_ins, h2]
  · intro w hw hwne
    have hpne : π w ≠ π x₀ := fun h => hwne (π.injective h)
    simp [nextItem, hmap_ins, h3 (π w) (mem_map.mpr ⟨w, hw, rfl⟩) hpne]

/-- Swapping two active items `y₁, y₂ ∈ S \ {x}` on the right of `π` permutes `nextItem π S x` by
`Equiv.swap y₁ y₂` without changing the occupied circle set `S.map π`. -/
private theorem nextItem_mul_swap {M : ℕ} [DecidableEq (Fin M)] (π : Equiv.Perm (Fin M))
    {S : Finset (Fin M)} {x y₁ y₂ : Fin M}
    (hy₁ : y₁ ∈ S) (hy₂ : y₂ ∈ S) (hx₁ : x ≠ y₁) (hx₂ : x ≠ y₂) :
    nextItem (π * Equiv.swap y₁ y₂) S x = (Equiv.swap y₁ y₂) (nextItem π S x) := by
  have hmap : S.map (π * Equiv.swap y₁ y₂).toEmbedding = S.map π.toEmbedding := by
    ext p
    simp only [mem_map, Equiv.coe_toEmbedding, Equiv.Perm.mul_apply]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨Equiv.swap y₁ y₂ z, ?_, rfl⟩
      by_cases hz₁ : z = y₁
      · subst hz₁; simpa using hy₂
      · by_cases hz₂ : z = y₂
        · subst hz₂; simpa using hy₁
        · rw [Equiv.swap_apply_of_ne_of_ne hz₁ hz₂]; exact hz
    · rintro ⟨z, hz, rfl⟩
      refine ⟨Equiv.swap y₁ y₂ z, ?_, by simp⟩
      by_cases hz₁ : z = y₁
      · subst hz₁; simpa using hy₂
      · by_cases hz₂ : z = y₂
        · subst hz₂; simpa using hy₁
        · rw [Equiv.swap_apply_of_ne_of_ne hz₁ hz₂]; exact hz
  have hx_fix : (π * Equiv.swap y₁ y₂) x = π x := by
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hx₁ hx₂]
  dsimp only [nextItem]
  rw [hmap, hx_fix, Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap]

/-- Single-round match attempt (`Algorithm 1`, lines 7–9): ball `a` matches to bin `b` iff `a ∈ A`
and the clockwise-next active item in `activeItems A B` under `π` is `binItem U' b`. -/
def roundMatchOpt {U' n' : ℕ} (π : RoundPerm U' n') (A : Finset (Fin U')) (B : Finset (Fin n'))
    (a : Fin U') : Option (Fin n') :=
  if a ∈ A then asBin? (nextItem π (activeItems A B) (ballItem n' a)) else none

/-- Single-round state update (`Algorithm 1`, lines 5–10): remove matched balls from `A` and
matched bins from `B`. -/
def roundStep {U' n' : ℕ} (π : RoundPerm U' n') (AB : Finset (Fin U') × Finset (Fin n')) :
    Finset (Fin U') × Finset (Fin n') :=
  let A := AB.1
  let B := AB.2
  let matchedBalls := A.filter fun a => (roundMatchOpt π A B a).isSome
  let matchedBins := B.filter fun b => ∃ a ∈ A, roundMatchOpt π A B a = some b
  (A \ matchedBalls, B \ matchedBins)

private theorem roundMatchOpt_mem_bins {U' n' : ℕ} {π : RoundPerm U' n'} {A : Finset (Fin U')}
    {B : Finset (Fin n')} {a : Fin U'} {b : Fin n'} (hm : roundMatchOpt π A B a = some b) :
    a ∈ A ∧ b ∈ B := by
  dsimp only [roundMatchOpt] at hm
  split_ifs at hm with ha
  have hnext_eq : nextItem π (activeItems A B) (ballItem n' a) = binItem U' b :=
    asBin?_eq_some_iff.mp hm
  have hS : (activeItems A B).Nonempty := ⟨ballItem n' a, ballItem_mem_activeItems.mpr ha⟩
  have hmem := hnext_eq ▸ nextItem_mem π hS (ballItem n' a)
  exact ⟨ha, binItem_mem_activeItems.mp hmem⟩

private theorem roundMatchOpt_injective {U' n' : ℕ} (π : RoundPerm U' n') (A : Finset (Fin U'))
    (B : Finset (Fin n')) {a₁ a₂ : Fin U'} {b : Fin n'}
    (h₁ : roundMatchOpt π A B a₁ = some b) (h₂ : roundMatchOpt π A B a₂ = some b) :
    a₁ = a₂ := by
  have ha₁ : a₁ ∈ A := (roundMatchOpt_mem_bins h₁).1
  have ha₂ : a₂ ∈ A := (roundMatchOpt_mem_bins h₂).1
  dsimp only [roundMatchOpt] at h₁ h₂
  simp only [ha₁, ↓reduceIte] at h₁
  simp only [ha₂, ↓reduceIte] at h₂
  have heq : nextItem π (activeItems A B) (ballItem n' a₁) =
      nextItem π (activeItems A B) (ballItem n' a₂) :=
    (asBin?_eq_some_iff.mp h₁).trans (asBin?_eq_some_iff.mp h₂).symm
  have hinj := nextItem_injective π (activeItems A B)
    (ballItem_mem_activeItems.mpr ha₁) (ballItem_mem_activeItems.mpr ha₂) heq
  exact ballItem_injective U' n' hinj

private theorem card_balls_le_card_bins_roundStep {U' n' : ℕ} (π : RoundPerm U' n')
    {A : Finset (Fin U')} {B : Finset (Fin n')} (hle : A.card ≤ B.card) :
    (roundStep π (A, B)).1.card ≤ (roundStep π (A, B)).2.card := by
  set mA := A.filter fun a => (roundMatchOpt π A B a).isSome
  set mB := B.filter fun b => ∃ a ∈ A, roundMatchOpt π A B a = some b
  have hmA_sub : mA ⊆ A := filter_subset _ A
  have hmB_sub : mB ⊆ B := filter_subset _ B
  have hcard_eq : mA.card = mB.card := by
    refine card_bij (fun a ha => (roundMatchOpt π A B a).get (mem_filter.mp ha).2) ?_ ?_ ?_
    · intro a ha
      have hget : roundMatchOpt π A B a =
          some ((roundMatchOpt π A B a).get (mem_filter.mp ha).2) :=
        (Option.some_get _).symm
      exact mem_filter.mpr ⟨(roundMatchOpt_mem_bins hget).2, a, (mem_filter.mp ha).1, hget⟩
    · intro a₁ ha₁ a₂ ha₂ heq
      have h₁ : roundMatchOpt π A B a₁ =
          some ((roundMatchOpt π A B a₁).get (mem_filter.mp ha₁).2) :=
        (Option.some_get _).symm
      have h₂ : roundMatchOpt π A B a₂ =
          some ((roundMatchOpt π A B a₂).get (mem_filter.mp ha₂).2) :=
        (Option.some_get _).symm
      rw [heq] at h₁
      exact roundMatchOpt_injective π A B h₁ h₂
    · intro b hb
      rcases (mem_filter.mp hb).2 with ⟨a, ha, hab⟩
      have hisSome : (roundMatchOpt π A B a).isSome := by simp [hab]
      refine ⟨a, mem_filter.mpr ⟨ha, hisSome⟩, ?_⟩
      simp [hab]
  dsimp only [roundStep]
  rw [card_sdiff_of_subset hmA_sub, card_sdiff_of_subset hmB_sub, hcard_eq]
  exact Nat.sub_le_sub_right hle mB.card

/-- Every round with `A.Nonempty` and `B.Nonempty` matches at least one ball (`Algorithm 1`
termination property, [LiLiangYuZhou2024, Section 3.1]). -/
theorem card_balls_roundStep_lt {U' n' : ℕ} (π : RoundPerm U' n')
    {A : Finset (Fin U')} {B : Finset (Fin n')} (hA : A.Nonempty) (hB : B.Nonempty) :
    (roundStep π (A, B)).1.card < A.card := by
  set S := activeItems A B
  set Q := A.map ⟨ballItem n', ballItem_injective U' n'⟩
  have hQS : Q ⊆ S := subset_union_left
  have hQ : Q.Nonempty := Finset.map_nonempty.mpr hA
  have hdiff : (S \ Q).Nonempty := by
    rcases hB with ⟨b, hb⟩
    refine ⟨binItem U' b, mem_sdiff.mpr ⟨binItem_mem_activeItems.mpr hb, ?_⟩⟩
    intro hm
    rcases mem_map.mp hm with ⟨a, _, heq⟩
    have hval : (ballItem n' a).val = (binItem U' b).val := congrArg Fin.val heq
    simp only [ballItem, binItem, Fin.val_castAdd, Fin.val_natAdd] at hval
    omega
  rcases exists_nextItem_notMem π hQ hdiff with ⟨q, hqQ, hnext_notQ⟩
  rcases mem_map.mp hqQ with ⟨a, haA, rfl⟩
  have hnext_S : nextItem π S (ballItem n' a) ∈ S :=
    nextItem_mem π (hQ.mono hQS) (ballItem n' a)
  rcases mem_activeItems_iff.mp hnext_S with ⟨a', ha', heq⟩ | ⟨b, _, heq⟩
  · exact absurd (heq ▸ mem_map.mpr ⟨a', ha', rfl⟩) hnext_notQ
  · have hm : roundMatchOpt π A B a = some b := by
      simp [roundMatchOpt, haA, S, heq]
    have ha_in : a ∈ A.filter fun x => (roundMatchOpt π A B x).isSome :=
      mem_filter.mpr ⟨haA, by simp [hm]⟩
    dsimp only [roundStep]
    exact sdiff_ssubset (filter_subset _ A) ⟨a, ha_in⟩ |> card_lt_card

/-! ### Multi-round execution, canonical injection, and round count -/

/-- Remaining `(A_i, B_i)` state just before round `i` (0-indexed) when running `Algorithm 1` on
`(A, B)` under scheme `h`. -/
def stateAt {U' n' : ℕ} (h : Scheme U' n') (A : Finset (Fin U')) (B : Finset (Fin n')) :
    ℕ → Finset (Fin U') × Finset (Fin n')
  | 0 => (A, B)
  | i + 1 =>
    if hi : i < U' then roundStep (h ⟨i, hi⟩) (stateAt h A B i) else stateAt h A B i

/-- Partial matching accumulated during the first `k` rounds of `Algorithm 1`. -/
private def matchAux {U' n' : ℕ} (h : Scheme U' n') (A : Finset (Fin U')) (B : Finset (Fin n')) :
    ℕ → Fin U' → Option (Fin n')
  | 0, _ => none
  | i + 1, a =>
    match matchAux h A B i a with
    | some b => some b
    | none =>
      if hi : i < U' then roundMatchOpt (h ⟨i, hi⟩) (stateAt h A B i).1 (stateAt h A B i).2 a
      else none

/-- Partial matching `σ_{A, B} : Fin U' → Option (Fin n')` after all `U'` rounds of `Algorithm 1`
on `(A, B)`. -/
def matchOptOn {U' n' : ℕ} (h : Scheme U' n') (A : Finset (Fin U')) (B : Finset (Fin n')) :
    Fin U' → Option (Fin n') :=
  matchAux h A B U'

/-- Partial matching `σ_A : Fin U' → Option (Fin n')` against all `n'` slots (`B = Finset.univ`). -/
def matchOpt {U' n' : ℕ} (h : Scheme U' n') (A : Finset (Fin U')) : Fin U' → Option (Fin n') :=
  matchOptOn h A Finset.univ

/-- Number of active rounds `T` executed by `Algorithm 1` on `(A, B)`. -/
def roundsOn {U' n' : ℕ} (h : Scheme U' n') (A : Finset (Fin U')) (B : Finset (Fin n')) : ℕ :=
  ((Finset.range U').filter fun i => (stateAt h A B i).1.Nonempty).card

/-- Number of active rounds `T` executed by `Algorithm 1` on `(A, Finset.univ)`. -/
def rounds {U' n' : ℕ} (h : Scheme U' n') (A : Finset (Fin U')) : ℕ :=
  roundsOn h A Finset.univ

/-- Ball-relocation distance `Δ(σ, σ') = #{a : Fin U' | σ a ≠ σ' a}` (`Problem 3.1`,
[LiLiangYuZhou2024, Section 3.1]). -/
@[expose]
def relocDist {U' n' : ℕ} (σ σ' : Fin U' → Option (Fin n')) : ℕ :=
  (Finset.univ.filter fun a => σ a ≠ σ' a).card

theorem relocDist_self {U' n' : ℕ} (σ : Fin U' → Option (Fin n')) : relocDist σ σ = 0 := by
  simp [relocDist]

theorem relocDist_comm {U' n' : ℕ} (σ σ' : Fin U' → Option (Fin n')) :
    relocDist σ σ' = relocDist σ' σ := by
  dsimp only [relocDist]
  congr 1
  ext a
  simp [ne_comm]

theorem relocDist_triangle {U' n' : ℕ} (σ₁ σ₂ σ₃ : Fin U' → Option (Fin n')) :
    relocDist σ₁ σ₃ ≤ relocDist σ₁ σ₂ + relocDist σ₂ σ₃ := by
  dsimp only [relocDist]
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro a ha
  simp only [mem_filter, mem_univ, true_and, mem_union] at ha ⊢
  by_contra h
  push Not at h
  exact ha (h.1.trans h.2)

private theorem stateAt_balls_subset {U' n' : ℕ} (h : Scheme U' n') (A : Finset (Fin U'))
    (B : Finset (Fin n')) (i : ℕ) : (stateAt h A B i).1 ⊆ A := by
  induction i with
  | zero => exact Subset.rfl
  | succ i ih =>
    dsimp only [stateAt]
    split_ifs with hi
    · exact sdiff_subset.trans ih
    · exact ih

private theorem stateAt_balls_succ_subset {U' n' : ℕ} (h : Scheme U' n') (A : Finset (Fin U'))
    (B : Finset (Fin n')) (i : ℕ) : (stateAt h A B (i + 1)).1 ⊆ (stateAt h A B i).1 := by
  dsimp only [stateAt]
  split_ifs with hi
  · exact sdiff_subset
  · exact Subset.rfl

private theorem stateAt_balls_mono {U' n' : ℕ} (h : Scheme U' n') (A : Finset (Fin U'))
    (B : Finset (Fin n')) {i j : ℕ} (hij : i ≤ j) :
    (stateAt h A B j).1 ⊆ (stateAt h A B i).1 := by
  induction j with
  | zero =>
    have hi0 : i = 0 := Nat.le_zero.mp hij
    subst hi0; exact Subset.rfl
  | succ j ih =>
    rcases eq_or_lt_of_le hij with rfl | hlt
    · exact Subset.rfl
    · exact (stateAt_balls_succ_subset h A B j).trans (ih (Nat.lt_succ_iff.mp hlt))

private theorem card_balls_le_card_bins_stateAt {U' n' : ℕ} (h : Scheme U' n')
    {A : Finset (Fin U')} {B : Finset (Fin n')} (hle : A.card ≤ B.card) (i : ℕ) :
    (stateAt h A B i).1.card ≤ (stateAt h A B i).2.card := by
  induction i with
  | zero => exact hle
  | succ i ih =>
    dsimp only [stateAt]
    split_ifs with hi
    · exact card_balls_le_card_bins_roundStep (h ⟨i, hi⟩) ih
    · exact ih

private theorem card_stateAt_balls_le_sub {U' n' : ℕ} (h : Scheme U' n')
    {A : Finset (Fin U')} {B : Finset (Fin n')} (hle : A.card ≤ B.card) {i : ℕ} (hi : i ≤ U') :
    (stateAt h A B i).1.card ≤ A.card - i := by
  induction i with
  | zero => simp [stateAt]
  | succ i ih =>
    have hi' : i < U' := Nat.lt_of_succ_le hi
    have hprev := ih hi'.le
    dsimp only [stateAt]
    simp only [hi', ↓reduceDIte]
    by_cases hne : (stateAt h A B i).1.Nonempty
    · have hBne : (stateAt h A B i).2.Nonempty := card_pos.mp <|
        lt_of_lt_of_le (card_pos.mpr hne) (card_balls_le_card_bins_stateAt h hle i)
      have hlt := card_balls_roundStep_lt (h ⟨i, hi'⟩) hne hBne
      rw [Prod.mk.eta] at hlt
      omega
    · dsimp only [roundStep]
      rw [not_nonempty_iff_eq_empty.mp hne]
      simp

/-- `Algorithm 1` matches all balls within `A.card` rounds whenever `A.card ≤ B.card`. -/
theorem stateAt_balls_eq_empty {U' n' : ℕ} (h : Scheme U' n')
    {A : Finset (Fin U')} {B : Finset (Fin n')} (hle : A.card ≤ B.card)
    {i : ℕ} (hi : A.card ≤ i) : (stateAt h A B i).1 = ∅ := by
  have hAU : A.card ≤ U' := by simpa using A.card_le_univ
  have h0 : (stateAt h A B A.card).1 = ∅ := by
    have hcard := card_stateAt_balls_le_sub h hle hAU
    rw [Nat.sub_self, Nat.le_zero] at hcard
    exact card_eq_zero.mp hcard
  exact subset_empty.mp (h0 ▸ stateAt_balls_mono h A B hi)

theorem roundsOn_le_card {U' n' : ℕ} (h : Scheme U' n')
    {A : Finset (Fin U')} {B : Finset (Fin n')} (hle : A.card ≤ B.card) :
    roundsOn h A B ≤ A.card := by
  dsimp only [roundsOn]
  have hsub : ((Finset.range U').filter fun i => (stateAt h A B i).1.Nonempty) ⊆
      Finset.range A.card := by
    intro i hi
    obtain ⟨_, hne⟩ := mem_filter.mp hi
    rw [mem_range]
    by_contra hge
    exact hne.ne_empty (stateAt_balls_eq_empty h hle (Nat.le_of_not_lt hge))
  exact (card_le_card hsub).trans (by simp)

private theorem matchAux_spec {U' n' : ℕ} (h : Scheme U' n') (A : Finset (Fin U'))
    (B : Finset (Fin n')) (k : ℕ) :
    (∀ a, (matchAux h A B k a).isSome ↔ a ∈ A \ (stateAt h A B k).1) ∧
    (∀ a b, matchAux h A B k a = some b → b ∈ B \ (stateAt h A B k).2) ∧
    (∀ a₁ a₂ b, matchAux h A B k a₁ = some b → matchAux h A B k a₂ = some b → a₁ = a₂) := by
  induction k with
  | zero =>
    simp [matchAux, stateAt]
  | succ k ih =>
    obtain ⟨hdom, hran, hinj⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro a
      dsimp only [matchAux, stateAt]
      cases hmk : matchAux h A B k a with
      | some b =>
        have ha : a ∈ A \ (stateAt h A B k).1 := (hdom a).mp (by simp [hmk])
        split_ifs with hk
        · simp only [Option.isSome_some, true_iff, mem_sdiff] at ha ⊢
          exact ⟨ha.1, fun hm => ha.2 (sdiff_subset hm)⟩
        · simpa using ha
      | none =>
        have ha_not : a ∉ A \ (stateAt h A B k).1 := by
          rw [← hdom a]; simp [hmk]
        split_ifs with hk
        · dsimp only [roundStep]
          by_cases haA : a ∈ A
          · have ha_rem : a ∈ (stateAt h A B k).1 := by
              by_contra hni; exact ha_not (mem_sdiff.mpr ⟨haA, hni⟩)
            by_cases his : (roundMatchOpt (h ⟨k, hk⟩) (stateAt h A B k).1
                (stateAt h A B k).2 a).isSome
            · simp [his, haA, ha_rem]
            · simp [his, haA, ha_rem]
          · have hni : a ∉ (stateAt h A B k).1 := fun hm => haA (stateAt_balls_subset h A B k hm)
            simp [roundMatchOpt, hni, haA]
        · simp [ha_not]
    · intro a b hab
      dsimp only [matchAux, stateAt] at hab ⊢
      cases hmk : matchAux h A B k a with
      | some b' =>
        rw [hmk] at hab
        injection hab with hbb'
        rw [← hbb']
        have hb : b' ∈ B \ (stateAt h A B k).2 := hran a b' hmk
        split_ifs with hk
        · exact mem_sdiff.mpr ⟨(mem_sdiff.mp hb).1, fun hm => (mem_sdiff.mp hb).2 (sdiff_subset hm)⟩
        · exact hb
      | none =>
        rw [hmk] at hab
        split_ifs at hab with hk
        simp only [hk, ↓reduceDIte]
        have hmem := roundMatchOpt_mem_bins hab
        have hbB : b ∈ B := by
          have hsub : (stateAt h A B k).2 ⊆ B := by
            clear * -
            induction k with
            | zero => exact Subset.rfl
            | succ j ihj =>
              dsimp only [stateAt]; split_ifs with hj
              · exact sdiff_subset.trans ihj
              · exact ihj
          exact hsub hmem.2
        dsimp only [roundStep]
        refine mem_sdiff.mpr ⟨hbB, fun hm => ?_⟩
        exact (mem_sdiff.mp hm).2 (mem_filter.mpr ⟨hmem.2, a, hmem.1, hab⟩)
    · intro a₁ a₂ b h₁ h₂
      dsimp only [matchAux] at h₁ h₂
      cases hm₁ : matchAux h A B k a₁ with
      | none =>
        cases hm₂ : matchAux h A B k a₂ with
        | none =>
          rw [hm₁] at h₁; rw [hm₂] at h₂
          split_ifs at h₁ h₂ with hk
          exact roundMatchOpt_injective (h ⟨k, hk⟩) _ _ h₁ h₂
        | some b₂ =>
          rw [hm₁] at h₁; rw [hm₂] at h₂
          injection h₂ with hb₂
          rw [← hb₂] at h₁
          split_ifs at h₁ with hk
          exfalso
          exact (mem_sdiff.mp (hran a₂ b₂ hm₂)).2 (roundMatchOpt_mem_bins h₁).2
      | some b₁ =>
        cases hm₂ : matchAux h A B k a₂ with
        | none =>
          rw [hm₁] at h₁; rw [hm₂] at h₂
          injection h₁ with hb₁
          rw [← hb₁] at h₂
          split_ifs at h₂ with hk
          exfalso
          exact (mem_sdiff.mp (hran a₁ b₁ hm₁)).2 (roundMatchOpt_mem_bins h₂).2
        | some b₂ =>
          rw [hm₁] at h₁; rw [hm₂] at h₂
          injection h₁ with hb₁; injection h₂ with hb₂
          rw [hb₁] at hm₁; rw [hb₂] at hm₂
          exact hinj a₁ a₂ b hm₁ hm₂

theorem matchOptOn_isSome_iff {U' n' : ℕ} (h : Scheme U' n')
    {A : Finset (Fin U')} {B : Finset (Fin n')} (hle : A.card ≤ B.card)
    (a : Fin U') : (matchOptOn h A B a).isSome ↔ a ∈ A := by
  have hAU : A.card ≤ U' := by simpa using A.card_le_univ
  rw [matchOptOn, (matchAux_spec h A B U').1 a,
    stateAt_balls_eq_empty h hle hAU, sdiff_empty]

theorem matchOptOn_injective {U' n' : ℕ} (h : Scheme U' n') (A : Finset (Fin U'))
    (B : Finset (Fin n')) {a₁ a₂ : Fin U'} {b : Fin n'}
    (h₁ : matchOptOn h A B a₁ = some b) (h₂ : matchOptOn h A B a₂ = some b) : a₁ = a₂ :=
  (matchAux_spec h A B U').2.2 a₁ a₂ b h₁ h₂

theorem matchOpt_isSome_iff {U' n' : ℕ} (h : Scheme U' n')
    {A : Finset (Fin U')} (hA : A.card ≤ n') (a : Fin U') :
    (matchOpt h A a).isSome ↔ a ∈ A :=
  matchOptOn_isSome_iff h (by simpa using hA) a

theorem matchOpt_injective {U' n' : ℕ} (h : Scheme U' n') (A : Finset (Fin U'))
    {a₁ a₂ : Fin U'} {b : Fin n'}
    (h₁ : matchOpt h A a₁ = some b) (h₂ : matchOpt h A a₂ = some b) : a₁ = a₂ :=
  matchOptOn_injective h A Finset.univ h₁ h₂

theorem rounds_le_card {U' n' : ℕ} (h : Scheme U' n')
    {A : Finset (Fin U')} (hA : A.card ≤ n') : rounds h A ≤ A.card :=
  roundsOn_le_card h (by simpa using hA)

/-- Canonical history-independent dynamic matching `σ_A : A ↪ Fin n'` (`Problem 3.1`,
`Algorithm 1`) for any active ball set `A ⊆ Fin U'` of size `A.card ≤ n'`. -/
def matching {U' n' : ℕ} (h : Scheme U' n') (A : Finset (Fin U'))
    (hA : A.card ≤ n') : A ↪ Fin n' where
  toFun a := (matchOpt h A a.1).get <|
    (matchOptOn_isSome_iff h (by simpa using hA) a.1).mpr a.2
  inj' a₁ a₂ heq := Subtype.ext <|
    matchOptOn_injective h A Finset.univ
      ((Option.some_get _).symm.trans (congrArg some heq))
      (Option.some_get _).symm

@[simp]
theorem matching_apply {U' n' : ℕ} (h : Scheme U' n') (A : Finset (Fin U'))
    (hA : A.card ≤ n') (a : A) :
    matchOpt h A a.1 = some (matching h A hA a) :=
  (Option.some_get _).symm

/-! ### Expected round bound (`Claim 3.3`) -/

private theorem clockwiseNextPos_ne_self {M : ℕ} {P : Finset (Fin M)} (hcard : 2 ≤ P.card)
    {p : Fin M} (hp : p ∈ P) : clockwiseNextPos P p ≠ p := by
  have hP : P.Nonempty := ⟨p, hp⟩
  dsimp only [clockwiseNextPos]
  split_ifs with hgt
  · exact ((mem_filter.mp (min'_mem _ hgt)).2).ne'
  · have herase : (P.erase p).Nonempty := card_pos.mp (by rw [card_erase_of_mem hp]; omega)
    rcases herase with ⟨q, hq⟩
    have hqP : q ∈ P := mem_of_mem_erase hq
    have hqp : q ≠ p := ne_of_mem_erase hq
    have hle : q ≤ p := le_of_not_gt fun hlt => hgt ⟨q, mem_filter.mpr ⟨hqP, hlt⟩⟩
    exact (lt_of_le_of_lt (min'_le P q hqP) (lt_of_le_of_ne hle hqp)).ne

private theorem nextItem_mem_erase {M : ℕ} (π : Equiv.Perm (Fin M)) {S : Finset (Fin M)}
    (hcard : 2 ≤ S.card) {z : Fin M} (hz : z ∈ S) : nextItem π S z ∈ S.erase z := by
  refine mem_erase.mpr ⟨?_, nextItem_mem π ⟨z, hz⟩ z⟩
  intro heq
  have hp : π z ∈ S.map π.toEmbedding := mem_map.mpr ⟨z, hz, rfl⟩
  have hc : 2 ≤ (S.map π.toEmbedding).card := by simpa using hcard
  have hne := clockwiseNextPos_ne_self hc hp
  exact hne (by simpa [nextItem] using congrArg π heq)

/-- Single-round symmetry bound (`Claim 3.3` core): over a uniform permutation `π`, the expected
number of balls remaining unmatched after one round is at most `A.card / 2`. Stated in exact `ℕ`
counting form without division. -/
private theorem two_mul_sum_card_balls_roundStep_le {U' n' : ℕ} {A : Finset (Fin U')}
    {B : Finset (Fin n')} (hle : A.card ≤ B.card) :
    2 * ∑ π : RoundPerm U' n', (roundStep π (A, B)).1.card ≤
      A.card * Fintype.card (RoundPerm U' n') := by
  have hpoint : ∀ π : RoundPerm U' n',
      (roundStep π (A, B)).1.card =
        ∑ a ∈ A, if (roundMatchOpt π A B a).isSome then 0 else 1 := by
    intro π
    have heq : (roundStep π (A, B)).1 =
        A.filter fun a => ¬(roundMatchOpt π A B a).isSome := by
      ext a; simp only [roundStep, mem_sdiff, mem_filter]; tauto
    rw [heq, card_filter]
    refine sum_congr rfl fun a _ => ?_
    cases roundMatchOpt π A B a <;> rfl
  simp_rw [hpoint]
  rw [sum_comm, mul_sum, ← sum_const_nat (f := fun _ => Fintype.card (RoundPerm U' n'))
    (fun _ _ => rfl)]
  refine sum_le_sum fun a ha => ?_
  set S := activeItems A B
  have hBne : B.Nonempty := card_pos.mp (lt_of_lt_of_le (card_pos.mpr ⟨a, ha⟩) hle)
  rcases hBne with ⟨b₀, hb₀⟩
  have hScard : 2 ≤ S.card := by
    rw [card_activeItems]
    have hApos : 1 ≤ A.card := card_pos.mpr ⟨a, ha⟩
    omega
  set x := ballItem n' a
  have hxS : x ∈ S := ballItem_mem_activeItems.mpr ha
  set y₀ := binItem U' b₀
  have hy₀ : y₀ ∈ S.erase x := by
    refine mem_erase.mpr ⟨?_, binItem_mem_activeItems.mpr hb₀⟩
    intro heq
    have hval : y₀.val = x.val := congrArg Fin.val heq
    simp only [x, y₀, ballItem, binItem, Fin.val_castAdd, Fin.val_natAdd] at hval
    omega
  let fiber : Fin (U' + n') → Finset (RoundPerm U' n') := fun y =>
    Finset.univ.filter fun π => nextItem π S x = y
  have hfiber_card : ∀ y ∈ S.erase x, (fiber y).card = (fiber y₀).card := by
    intro y hy
    have hyS : y ∈ S := mem_of_mem_erase hy
    have hy₀S : y₀ ∈ S := mem_of_mem_erase hy₀
    have hxy : x ≠ y := (mem_erase.mp hy).1.symm
    have hxy₀ : x ≠ y₀ := (mem_erase.mp hy₀).1.symm
    refine card_bij (fun π _ => π * Equiv.swap y y₀) ?_ ?_ ?_
    · intro π hπ
      have hnext : nextItem π S x = y := (mem_filter.mp hπ).2
      refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      rw [nextItem_mul_swap π hyS hy₀S hxy hxy₀, hnext, Equiv.swap_apply_left]
    · intro π₁ _ π₂ _ heq
      exact mul_right_cancel heq
    · intro π hπ
      have hnext : nextItem π S x = y₀ := (mem_filter.mp hπ).2
      refine ⟨π * Equiv.swap y y₀, mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
      · rw [nextItem_mul_swap π hyS hy₀S hxy hxy₀, hnext, Equiv.swap_apply_right]
      · simp [mul_assoc]
  have hdisj : (S.erase x : Set (Fin (U' + n'))).PairwiseDisjoint fiber := by
    intro y₁ _ y₂ _ hne
    change Disjoint (fiber y₁) (fiber y₂)
    rw [disjoint_left]
    intro π h₁ h₂
    exact hne ((mem_filter.mp h₁).2.symm.trans (mem_filter.mp h₂).2)
  have huniv : (Finset.univ : Finset (RoundPerm U' n')) = (S.erase x).biUnion fiber := by
    ext π
    simp only [mem_univ, true_iff, mem_biUnion, fiber, mem_filter, true_and]
    exact ⟨nextItem π S x, nextItem_mem_erase π hScard hxS, rfl⟩
  have htot : Fintype.card (RoundPerm U' n') = (A.card + B.card - 1) * (fiber y₀).card := by
    rw [← card_univ, huniv, card_biUnion hdisj,
      sum_congr rfl fun y hy => hfiber_card y hy, sum_const, smul_eq_mul,
      card_erase_of_mem hxS, card_activeItems]
  set badY := (A.erase a).map ⟨ballItem n', ballItem_injective U' n'⟩
  have hbadY_sub : badY ⊆ S.erase x := by
    intro y hy
    rcases mem_map.mp hy with ⟨a', ha', rfl⟩
    refine mem_erase.mpr ⟨?_, ballItem_mem_activeItems.mpr (mem_of_mem_erase ha')⟩
    intro heq
    exact (mem_erase.mp ha').1 (ballItem_injective U' n' heq)
  have hbad_sub : (Finset.univ.filter fun π : RoundPerm U' n' =>
      ¬(roundMatchOpt π A B a).isSome) ⊆ badY.biUnion fiber := by
    intro π hπ
    have hnis : ¬(roundMatchOpt π A B a).isSome := (mem_filter.mp hπ).2
    have hmem : nextItem π S x ∈ S.erase x := nextItem_mem_erase π hScard hxS
    rcases mem_activeItems_iff.mp (mem_of_mem_erase hmem) with ⟨a', ha', heq⟩ | ⟨b, _, heq⟩
    · have ha'ne : a' ≠ a := fun h => (mem_erase.mp hmem).1 (by simp [heq, x, h])
      exact mem_biUnion.mpr ⟨nextItem π S x,
        heq ▸ mem_map.mpr ⟨a', mem_erase.mpr ⟨ha'ne, ha'⟩, rfl⟩,
        mem_filter.mpr ⟨mem_univ _, rfl⟩⟩
    · exfalso
      apply hnis
      simp [roundMatchOpt, ha, S, x, heq]
  have hsum_eq : (∑ π : RoundPerm U' n', if (roundMatchOpt π A B a).isSome then 0 else 1) =
      (Finset.univ.filter fun π : RoundPerm U' n' => ¬(roundMatchOpt π A B a).isSome).card := by
    rw [card_filter]
    refine sum_congr rfl fun π _ => ?_
    cases roundMatchOpt π A B a <;> rfl
  have hbad_card : (badY.biUnion fiber).card = (A.card - 1) * (fiber y₀).card := by
    rw [card_biUnion (hdisj.subset hbadY_sub),
      sum_congr rfl fun y hy => hfiber_card y (hbadY_sub hy),
      sum_const, smul_eq_mul, card_map, card_erase_of_mem ha]
  have hbad_le : (Finset.univ.filter fun π : RoundPerm U' n' =>
      ¬(roundMatchOpt π A B a).isSome).card ≤ (A.card - 1) * (fiber y₀).card :=
    (card_le_card hbad_sub).trans_eq hbad_card
  rw [hsum_eq, htot]
  have h1 : 1 ≤ A.card := card_pos.mpr ⟨a, ha⟩
  have hcoef : 2 * (A.card - 1) ≤ A.card + B.card - 1 := by omega
  calc 2 * (Finset.univ.filter fun π : RoundPerm U' n' =>
          ¬(roundMatchOpt π A B a).isSome).card
      ≤ 2 * ((A.card - 1) * (fiber y₀).card) := Nat.mul_le_mul_left 2 hbad_le
    _ = (2 * (A.card - 1)) * (fiber y₀).card := by ring
    _ ≤ (A.card + B.card - 1) * (fiber y₀).card := Nat.mul_le_mul_right _ hcoef

private theorem stateAt_congr {U' n' : ℕ} {h₁ h₂ : Scheme U' n'} (A : Finset (Fin U'))
    (B : Finset (Fin n')) {k : ℕ} (heq : ∀ (i : Fin U'), i.val < k → h₁ i = h₂ i) :
    stateAt h₁ A B k = stateAt h₂ A B k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    dsimp only [stateAt]
    have hprev := ih fun i hi => heq i (Nat.lt_succ_of_lt hi)
    split_ifs with hk
    · rw [hprev, heq ⟨k, hk⟩ (Nat.lt_succ_self k)]
    · exact hprev

/-- Multi-round geometric contraction in `ℕ`: after `k ≤ U'` rounds, the sum of `(stateAt h A B k)`
ball counts across all `h : Scheme U' n'`, multiplied by `2 ^ k`, is at most `A.card * |Scheme|`. -/
private theorem two_pow_mul_sum_card_stateAt_le {U' n' : ℕ} {A : Finset (Fin U')}
    {B : Finset (Fin n')} (hle : A.card ≤ B.card) {k : ℕ} (hk : k ≤ U') :
    2 ^ k * ∑ h : Scheme U' n', (stateAt h A B k).1.card ≤
      A.card * Fintype.card (Scheme U' n') := by
  induction k with
  | zero => simp [stateAt, Nat.mul_comm]
  | succ k ih =>
    have hk' : k < U' := Nat.lt_of_succ_le hk
    let idx : Fin U' := ⟨k, hk'⟩
    let e := Equiv.piSplitAt idx (fun _ : Fin U' => RoundPerm U' n')
    have hsum_split : (∑ h : Scheme U' n', (stateAt h A B (k + 1)).1.card) =
        ∑ rest : ({j : Fin U' // j ≠ idx} → RoundPerm U' n'),
          ∑ π : RoundPerm U' n',
            (roundStep π (stateAt (e.symm (π, rest)) A B k)).1.card := by
      rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type_right]
      refine sum_congr rfl fun rest _ => sum_congr rfl fun π _ => ?_
      dsimp only [stateAt]
      simp only [hk', ↓reduceDIte]
      have hidx : e.symm (π, rest) idx = π := by simp [e]
      rw [hidx]
    have hconst : ∀ (π : RoundPerm U' n')
        (rest : {j : Fin U' // j ≠ idx} → RoundPerm U' n'),
        stateAt (e.symm (π, rest)) A B k = stateAt (e.symm (1, rest)) A B k := by
      intro π rest
      refine stateAt_congr A B fun i hik => ?_
      have hne : i ≠ idx := fun h => by subst h; exact Nat.lt_irrefl k hik
      simp [e, Equiv.piSplitAt_symm_apply, hne]
    have hsum_le : 2 * ∑ h : Scheme U' n', (stateAt h A B (k + 1)).1.card ≤
        ∑ h : Scheme U' n', (stateAt h A B k).1.card := by
      rw [hsum_split, mul_sum, ← Equiv.sum_comp e.symm, Fintype.sum_prod_type_right]
      refine sum_le_sum fun rest _ => ?_
      simp_rw [hconst _ rest]
      have hcard_le : (stateAt (e.symm (1, rest)) A B k).1.card ≤
          (stateAt (e.symm (1, rest)) A B k).2.card :=
        card_balls_le_card_bins_stateAt _ hle k
      have hstep := two_mul_sum_card_balls_roundStep_le hcard_le
      rw [Prod.mk.eta] at hstep
      refine hstep.trans_eq ?_
      rw [sum_const, card_univ, smul_eq_mul, Nat.mul_comm]
    calc 2 ^ (k + 1) * ∑ h : Scheme U' n', (stateAt h A B (k + 1)).1.card
        = 2 ^ k * (2 * ∑ h : Scheme U' n', (stateAt h A B (k + 1)).1.card) := by ring
      _ ≤ 2 ^ k * ∑ h : Scheme U' n', (stateAt h A B k).1.card :=
          Nat.mul_le_mul_left _ hsum_le
      _ ≤ A.card * Fintype.card (Scheme U' n') := ih hk'.le

/-- Real-valued expectation of remaining balls after `k ≤ U'` rounds under `schemePMF`:
`𝔼_h[|A_k|] ≤ |A| / 2 ^ k`. -/
private theorem expect_card_balls_stateAt_le {U' n' : ℕ} {A : Finset (Fin U')}
    {B : Finset (Fin n')} (hle : A.card ≤ B.card) {k : ℕ} (hk : k ≤ U') :
    (∑ h : Scheme U' n', ((schemePMF U' n' h).toReal * ((stateAt h A B k).1.card : ℝ))) ≤
      (A.card : ℝ) / (2 : ℝ) ^ k := by
  have hSpos : (0 : ℝ) < Fintype.card (Scheme U' n') := by positivity
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hnat : (2 : ℝ) ^ k * ∑ h : Scheme U' n', ((stateAt h A B k).1.card : ℝ) ≤
      (A.card : ℝ) * Fintype.card (Scheme U' n') := by
    exact_mod_cast two_pow_mul_sum_card_stateAt_le (U' := U') hle hk
  have hpmf : ∀ h : Scheme U' n',
      (schemePMF U' n' h).toReal = (Fintype.card (Scheme U' n') : ℝ)⁻¹ := by
    intro h
    simp [schemePMF, Cslib.Probability.PMF.uniformOfFintype_apply]
  simp_rw [hpmf, ← mul_sum]
  rw [inv_mul_le_iff₀ hSpos, ← mul_div_assoc, le_div_iff₀ h2pos]
  linarith

/-- **Claim 3.3** ([LiLiangYuZhou2024, Section 3.1]): for any `A ⊆ Fin U'`
and `B ⊆ Fin n'` with `A.card ≤ B.card`, the expected number of rounds `T = roundsOn h A B` under
uniform independent permutations is at most `⌈log₂ |A|⌉ + 2`. -/
theorem expect_roundsOn_le {U' n' : ℕ} {A : Finset (Fin U')} {B : Finset (Fin n')}
    (hle : A.card ≤ B.card) :
    (∑ h : Scheme U' n', (schemePMF U' n' h).toReal * (roundsOn h A B : ℝ)) ≤
      (Nat.clog 2 A.card : ℝ) + 2 := by
  rcases A.eq_empty_or_nonempty with rfl | hAne
  · have hzero : ∀ h : Scheme U' n', roundsOn h ∅ B = 0 := by
      intro h
      dsimp only [roundsOn]
      rw [card_eq_zero, filter_eq_empty_iff]
      intro i _
      exact not_nonempty_iff_eq_empty.mpr (subset_empty.mp (stateAt_balls_subset h ∅ B i))
    simp [hzero]
  · set L := Nat.clog 2 A.card
    have hAL : A.card ≤ 2 ^ L := Nat.le_pow_clog Nat.one_lt_two A.card
    have hrounds_eq : ∀ h : Scheme U' n',
        (roundsOn h A B : ℝ) =
          ∑ i ∈ Finset.range U', if (stateAt h A B i).1.Nonempty then (1 : ℝ) else 0 := by
      intro h
      dsimp only [roundsOn]
      rw [card_filter, Nat.cast_sum]
      refine sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    simp_rw [hrounds_eq, mul_sum]
    rw [sum_comm]
    let bound : ℕ → ℝ := fun i => if i < L then 1 else (1 / 2 : ℝ) ^ (i - L)
    have hterm : ∀ i ∈ Finset.range U',
        (∑ h : Scheme U' n',
          (schemePMF U' n' h).toReal * (if (stateAt h A B i).1.Nonempty then (1 : ℝ) else 0)) ≤
          bound i := by
      intro i hi
      have hiU : i ≤ U' := (mem_range.mp hi).le
      by_cases hiL : i < L
      · simp only [bound, hiL, ↓reduceIte]
        refine Cslib.Probability.PMF.sum_mul_le (schemePMF U' n') _ 1 fun h => ?_
        split_ifs <;> norm_num
      · simp only [bound, hiL, ↓reduceIte]
        have hLi : L ≤ i := Nat.le_of_not_lt hiL
        have hind_le : ∀ h : Scheme U' n',
            (if (stateAt h A B i).1.Nonempty then (1 : ℝ) else 0) ≤
              ((stateAt h A B i).1.card : ℝ) := by
          intro h
          split_ifs with hne
          · exact_mod_cast card_pos.mpr hne
          · positivity
        have h1 : (∑ h : Scheme U' n',
            (schemePMF U' n' h).toReal * (if (stateAt h A B i).1.Nonempty then (1 : ℝ) else 0)) ≤
            ∑ h : Scheme U' n', (schemePMF U' n' h).toReal * ((stateAt h A B i).1.card : ℝ) :=
          sum_le_sum fun h _ => mul_le_mul_of_nonneg_left (hind_le h) ENNReal.toReal_nonneg
        refine h1.trans ((expect_card_balls_stateAt_le hle hiU).trans ?_)
        have hALR : (A.card : ℝ) ≤ (2 : ℝ) ^ L := by exact_mod_cast hAL
        calc (A.card : ℝ) / (2 : ℝ) ^ i
            ≤ (2 : ℝ) ^ L / (2 : ℝ) ^ i := by gcongr
          _ = (2 : ℝ) ^ L / ((2 : ℝ) ^ L * (2 : ℝ) ^ (i - L)) := by
              rw [← pow_add, Nat.add_sub_of_le hLi]
          _ = (1 / 2 : ℝ) ^ (i - L) := by
              have h2L : (2 : ℝ) ^ L ≠ 0 := by positivity
              rw [div_mul_eq_div_div, div_self h2L, one_div_pow, one_div]
    refine (sum_le_sum hterm).trans ?_
    -- Split `Finset.range U'` into `< L` and `≥ L`
    have hsplit : (∑ i ∈ Finset.range U', bound i) ≤
        (∑ _i ∈ Finset.range L, (1 : ℝ)) + ∑ j ∈ Finset.range U', (1 / 2 : ℝ) ^ j := by
      have hsub1 : ((Finset.range U').filter (· < L)) ⊆ Finset.range L := by
        intro i hi; exact mem_range.mpr (mem_filter.mp hi).2
      rw [← sum_filter_add_sum_filter_not (Finset.range U') (· < L)]
      refine add_le_add ?_ ?_
      · calc ∑ i ∈ (Finset.range U').filter (· < L), bound i
            = ∑ _i ∈ (Finset.range U').filter (· < L), (1 : ℝ) :=
              sum_congr rfl fun i hi => by simp [bound, (mem_filter.mp hi).2]
          _ ≤ ∑ _i ∈ Finset.range L, (1 : ℝ) :=
              sum_le_sum_of_subset_of_nonneg hsub1 fun _ _ _ => by positivity
      · set S₂ := (Finset.range U').filter (fun i => ¬i < L)
        have hinj_sub : Set.InjOn (fun i => i - L) (S₂ : Set ℕ) := by
          intro i₁ hi₁ i₂ hi₂ heq
          have h₁ : L ≤ i₁ := Nat.le_of_not_lt (mem_filter.mp hi₁).2
          have h₂ : L ≤ i₂ := Nat.le_of_not_lt (mem_filter.mp hi₂).2
          dsimp only at heq
          omega
        have himg_sub : S₂.image (fun i => i - L) ⊆ Finset.range U' := by
          intro j hj
          rcases mem_image.mp hj with ⟨i, hi, rfl⟩
          exact mem_range.mpr
            (Nat.lt_of_le_of_lt (Nat.sub_le i L) (mem_range.mp (mem_filter.mp hi).1))
        calc ∑ i ∈ S₂, bound i
            = ∑ i ∈ S₂, (1 / 2 : ℝ) ^ (i - L) :=
              sum_congr rfl fun i hi => by simp [bound, (mem_filter.mp hi).2]
          _ = ∑ j ∈ S₂.image (fun i => i - L), (1 / 2 : ℝ) ^ j :=
              (sum_image hinj_sub).symm
          _ ≤ ∑ j ∈ Finset.range U', (1 / 2 : ℝ) ^ j :=
              sum_le_sum_of_subset_of_nonneg himg_sub fun _ _ _ => by positivity
    have hgeom : ∑ j ∈ Finset.range U', (1 / 2 : ℝ) ^ j ≤ 2 := by
      have hexact : ∀ m : ℕ, ∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ j = 2 - 2 * (1 / 2 : ℝ) ^ m := by
        intro m
        induction m with
        | zero => norm_num
        | succ m ih => rw [sum_range_succ, ih]; ring
      rw [hexact U']
      have hpos : (0 : ℝ) ≤ 2 * (1 / 2 : ℝ) ^ U' := by positivity
      linarith
    have hLsum : ∑ _i ∈ Finset.range L, (1 : ℝ) = (L : ℝ) := by simp
    linarith

/-- Specialization of **Claim 3.3** to all `n'` slots (`B = Finset.univ`): for `A.card ≤ n'`,
`𝔼[rounds h A] ≤ ⌈log₂ |A|⌉ + 2 ≤ 3 * ⌈log₂ (max |A| 2)⌉`. -/
theorem expect_rounds_le {U' n' : ℕ} {A : Finset (Fin U')} (hA : A.card ≤ n') :
    (∑ h : Scheme U' n', (schemePMF U' n' h).toReal * (rounds h A : ℝ)) ≤
      3 * (Nat.clog 2 (max A.card 2) : ℝ) := by
  have h1 := expect_roundsOn_le (U' := U') (B := (Finset.univ : Finset (Fin n')))
    (by simpa using hA)
  have hclog_pos : 1 ≤ Nat.clog 2 (max A.card 2) :=
    (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr (by simp : 2 ^ 0 < max A.card 2)
  have hclog_mono : Nat.clog 2 A.card ≤ Nat.clog 2 (max A.card 2) :=
    Nat.clog_mono_right 2 (le_max_left _ _)
  have hpos1 : (1 : ℝ) ≤ Nat.clog 2 (max A.card 2) := by exact_mod_cast hclog_pos
  have hmonoR : (Nat.clog 2 A.card : ℝ) ≤ Nat.clog 2 (max A.card 2) := by
    exact_mod_cast hclog_mono
  dsimp only [rounds]
  linarith

/-! ### Single-operation relocation bounds (`Claim 3.4` and `Lemma 3.2`) -/

/-- Total symmetric-difference size `|A ∆ A'| + |B ∆ B'|` between two `(balls, bins)` states. -/
private def pairDiff {U' n' : ℕ} (AB AB' : Finset (Fin U') × Finset (Fin n')) : ℕ :=
  (AB.1 ∆ AB'.1).card + (AB.2 ∆ AB'.2).card

private theorem pairDiff_self {U' n' : ℕ} (AB : Finset (Fin U') × Finset (Fin n')) :
    pairDiff AB AB = 0 := by
  simp [pairDiff]

private theorem pairDiff_comm {U' n' : ℕ} (AB AB' : Finset (Fin U') × Finset (Fin n')) :
    pairDiff AB AB' = pairDiff AB' AB := by
  simp [pairDiff, symmDiff_comm]

private theorem card_symmDiff_insert_of_notMem {α : Type*} [DecidableEq α] {s : Finset α}
    {x : α} (hx : x ∉ s) : (s ∆ insert x s).card = 1 := by
  have heq : s ∆ insert x s = {x} := by
    ext z; simp only [mem_symmDiff, mem_insert, mem_singleton]; grind
  rw [heq, card_singleton]

private theorem card_symmDiff_erase_of_mem {α : Type*} [DecidableEq α] {s : Finset α}
    {x : α} (hx : x ∈ s) : (s ∆ s.erase x).card = 1 := by
  have heq : s ∆ s.erase x = {x} := by
    ext z; simp only [mem_symmDiff, mem_erase, mem_singleton]; grind
  rw [heq, card_singleton]

private theorem mem_sdiff_filter {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Prop)
    [DecidablePred p] (x : α) : x ∈ s \ s.filter p ↔ x ∈ s ∧ ¬p x := by
  simp only [mem_sdiff, mem_filter]; tauto

/-- Inserting a single bin `bStar ∉ B` preserves `pairDiff ≤ 1` across `roundStep` and changes
at most `1` ball's single-round match (`Claim 3.4` bin-insertion case,
[LiLiangYuZhou2024, Section 3.1]). -/
private theorem roundStep_insert_bin {U' n' : ℕ} (π : RoundPerm U' n') (A : Finset (Fin U'))
    {B : Finset (Fin n')} {bStar : Fin n'} (hbStar : bStar ∉ B) :
    pairDiff (roundStep π (A, B)) (roundStep π (A, insert bStar B)) ≤ 1 ∧
      (Finset.univ.filter fun a =>
        roundMatchOpt π A B a ≠ roundMatchOpt π A (insert bStar B) a).card ≤ 1 := by
  set S := activeItems A B
  have hS_ins : activeItems A (insert bStar B) = insert (binItem U' bStar) S := by
    ext z; simp only [S, activeItems, map_insert, mem_union, mem_insert]; tauto
  by_cases hSne : S.Nonempty
  · have hzStar : binItem U' bStar ∉ S := by
      simpa [S] using hbStar
    rcases exists_insert_nextItem π hSne hzStar with ⟨x₀, hx₀S, hnx₀, hnz, hnw⟩
    have hsame : ∀ a : Fin U', ballItem n' a ≠ x₀ →
        roundMatchOpt π A (insert bStar B) a = roundMatchOpt π A B a := by
      intro a hne
      by_cases ha : a ∈ A
      · have hnext := hnw (ballItem n' a) (ballItem_mem_activeItems.mpr ha) hne
        simp [roundMatchOpt, ha, hS_ins, S, hnext]
      · simp [roundMatchOpt, ha]
    rcases mem_activeItems_iff.mp hx₀S with ⟨a₀, ha₀A, rfl⟩ | ⟨b₀, hb₀B, rfl⟩
    · -- `x₀ = ballItem n' a₀`
      have ha₀_new : roundMatchOpt π A (insert bStar B) a₀ = some bStar := by
        simp [roundMatchOpt, ha₀A, hS_ins, hnx₀]
      have hdiff_le : (Finset.univ.filter fun a =>
          roundMatchOpt π A B a ≠ roundMatchOpt π A (insert bStar B) a).card ≤ 1 := by
        refine (card_le_card (s := _) (t := {a₀}) ?_).trans (by simp)
        intro a ha
        simp only [mem_filter, mem_univ, true_and, mem_singleton] at ha ⊢
        by_contra hne
        exact ha (hsame a (fun h => hne (ballItem_injective U' n' h))).symm
      refine ⟨?_, hdiff_le⟩
      cases hold : roundMatchOpt π A B a₀ with
      | none =>
        have hballs : (roundStep π (A, insert bStar B)).1 =
            (roundStep π (A, B)).1.erase a₀ := by
          ext a
          simp only [roundStep, mem_sdiff_filter, mem_erase]
          rcases eq_or_ne a a₀ with rfl | ha
          · simp [ha₀_new]
          · rw [hsame a (fun h => ha (ballItem_injective U' n' h))]; simp [ha]
        have ha₀_rem : a₀ ∈ (roundStep π (A, B)).1 := by
          simp [roundStep, ha₀A, hold]
        have hbins : (roundStep π (A, insert bStar B)).2 = (roundStep π (A, B)).2 := by
          ext b
          simp only [roundStep, mem_sdiff_filter, mem_insert]
          constructor
          · rintro ⟨rfl | hbB, hno⟩
            · exfalso; exact hno ⟨a₀, ha₀A, ha₀_new⟩
            · refine ⟨hbB, ?_⟩
              rintro ⟨a, haA, hab⟩
              rcases eq_or_ne a a₀ with rfl | ha
              · simp [hold] at hab
              · exact hno ⟨a, haA,
                  (hsame a (fun h => ha (ballItem_injective U' n' h))).trans hab⟩
          · rintro ⟨hbB, hno⟩
            have hbne : b ≠ bStar := fun h => hbStar (h ▸ hbB)
            refine ⟨Or.inr hbB, ?_⟩
            rintro ⟨a, haA, hab⟩
            rcases eq_or_ne a a₀ with rfl | ha
            · rw [ha₀_new] at hab; exact hbne (Option.some.inj hab).symm
            · exact hno ⟨a, haA,
                (hsame a (fun h => ha (ballItem_injective U' n' h))).symm.trans hab⟩
        simp [pairDiff, hballs, hbins, card_symmDiff_erase_of_mem ha₀_rem]
      | some b₁ =>
        have hb₁B : b₁ ∈ B := (roundMatchOpt_mem_bins hold).2
        have hballs : (roundStep π (A, insert bStar B)).1 = (roundStep π (A, B)).1 := by
          ext a
          simp only [roundStep, mem_sdiff_filter]
          rcases eq_or_ne a a₀ with rfl | ha
          · simp [hold, ha₀_new]
          · rw [hsame a (fun h => ha (ballItem_injective U' n' h))]
        have hb₁_not_rem : b₁ ∉ (roundStep π (A, B)).2 := by
          simp only [roundStep, mem_sdiff_filter, not_and, Classical.not_not]
          intro _; exact ⟨a₀, ha₀A, hold⟩
        have hbins : (roundStep π (A, insert bStar B)).2 =
            insert b₁ (roundStep π (A, B)).2 := by
          ext b
          simp only [roundStep, mem_sdiff_filter, mem_insert]
          constructor
          · rintro ⟨rfl | hbB, hno⟩
            · exfalso; exact hno ⟨a₀, ha₀A, ha₀_new⟩
            · by_cases hbb₁ : b = b₁
              · exact Or.inl hbb₁
              · refine Or.inr ⟨hbB, ?_⟩
                rintro ⟨a, haA, hab⟩
                rcases eq_or_ne a a₀ with rfl | ha
                · rw [hold] at hab; exact hbb₁ (Option.some.inj hab).symm
                · exact hno ⟨a, haA,
                    (hsame a (fun h => ha (ballItem_injective U' n' h))).trans hab⟩
          · rintro (hb | ⟨hbB, hno⟩)
            · rw [hb]
              refine ⟨Or.inr hb₁B, ?_⟩
              rintro ⟨a, haA, hab⟩
              rcases eq_or_ne a a₀ with rfl | ha
              · rw [ha₀_new] at hab
                exact hbStar ((Option.some.inj hab) ▸ hb₁B)
              · have hold_a : roundMatchOpt π A B a = some b₁ :=
                  (hsame a (fun h => ha (ballItem_injective U' n' h))).symm.trans hab
                exact ha (roundMatchOpt_injective π A B hold_a hold)
            · refine ⟨Or.inr hbB, ?_⟩
              rintro ⟨a, haA, hab⟩
              rcases eq_or_ne a a₀ with rfl | ha
              · rw [ha₀_new] at hab
                exact hbStar ((Option.some.inj hab) ▸ hbB)
              · exact hno ⟨a, haA,
                  (hsame a (fun h => ha (ballItem_injective U' n' h))).symm.trans hab⟩
        simp [pairDiff, hballs, hbins, card_symmDiff_insert_of_notMem hb₁_not_rem]
    · -- `x₀ = binItem U' b₀`: no ball has `ballItem = x₀`, so all `roundMatchOpt` agree
      have hall_same : ∀ a : Fin U',
          roundMatchOpt π A (insert bStar B) a = roundMatchOpt π A B a := by
        intro a
        refine hsame a fun heq => ?_
        have hval := congrArg Fin.val heq
        simp only [ballItem, binItem, Fin.val_castAdd, Fin.val_natAdd] at hval
        omega
      have hdiff_zero : (Finset.univ.filter fun a =>
          roundMatchOpt π A B a ≠ roundMatchOpt π A (insert bStar B) a).card = 0 := by
        simp [hall_same]
      have hballs : (roundStep π (A, insert bStar B)).1 = (roundStep π (A, B)).1 := by
        ext a; simp [roundStep, hall_same]
      have hbStar_not_rem : bStar ∉ (roundStep π (A, B)).2 := fun hm =>
        hbStar (sdiff_subset hm)
      have hbins : (roundStep π (A, insert bStar B)).2 =
          insert bStar (roundStep π (A, B)).2 := by
        ext b
        simp only [roundStep, mem_sdiff_filter, mem_insert, hall_same]
        constructor
        · rintro ⟨rfl | hbB, hno⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hbB, hno⟩
        · rintro (rfl | ⟨hbB, hno⟩)
          · refine ⟨Or.inl rfl, ?_⟩
            rintro ⟨a, _, hab⟩
            exact hbStar (roundMatchOpt_mem_bins hab).2
          · exact ⟨Or.inr hbB, hno⟩
      refine ⟨?_, by omega⟩
      simp [pairDiff, hballs, hbins, card_symmDiff_insert_of_notMem hbStar_not_rem]
  · -- `S = ∅`, so `A = ∅` and `B = ∅`
    have hA : A = ∅ := by
      ext a; simp only [notMem_empty, iff_false]
      intro ha; exact hSne ⟨ballItem n' a, ballItem_mem_activeItems.mpr ha⟩
    have hB : B = ∅ := by
      ext b; simp only [notMem_empty, iff_false]
      intro hb; exact hSne ⟨binItem U' b, binItem_mem_activeItems.mpr hb⟩
    subst hA; subst hB
    have hnone : ∀ (B' : Finset (Fin n')) (a : Fin U'), roundMatchOpt π ∅ B' a = none := by
      intro B' a; simp [roundMatchOpt]
    have hrs1 : roundStep π (∅, ∅) = (∅, ∅) := by simp [roundStep]
    have hrs2 : roundStep π (∅, {bStar}) = (∅, {bStar}) := by
      ext <;> simp [roundStep, hnone]
    have hcard1 : ((∅ : Finset (Fin n')) ∆ {bStar}).card = 1 :=
      card_symmDiff_insert_of_notMem (notMem_empty bStar)
    simp [hnone, hrs1, hrs2, pairDiff, hcard1]

/-- Inserting a single ball `aStar ∉ A` preserves `pairDiff ≤ 1` across `roundStep` and changes
at most `2` balls' single-round matches (`Claim 3.4` ball-insertion case). -/
private theorem roundStep_insert_ball {U' n' : ℕ} (π : RoundPerm U' n') {A : Finset (Fin U')}
    {aStar : Fin U'} (haStar : aStar ∉ A) (B : Finset (Fin n')) :
    pairDiff (roundStep π (A, B)) (roundStep π (insert aStar A, B)) ≤ 1 ∧
      (Finset.univ.filter fun a =>
        roundMatchOpt π A B a ≠ roundMatchOpt π (insert aStar A) B a).card ≤ 2 := by
  set S := activeItems A B
  have hS_ins : activeItems (insert aStar A) B = insert (ballItem n' aStar) S := by
    ext z; simp only [S, activeItems, map_insert, mem_union, mem_insert]; tauto
  by_cases hSne : S.Nonempty
  · have hzStar : ballItem n' aStar ∉ S := by simpa [S] using haStar
    rcases exists_insert_nextItem π hSne hzStar with ⟨x₀, hx₀S, hnx₀, hnz, hnw⟩
    have hsame : ∀ a : Fin U', a ≠ aStar → ballItem n' a ≠ x₀ →
        roundMatchOpt π (insert aStar A) B a = roundMatchOpt π A B a := by
      intro a hneStar hnex₀
      by_cases ha : a ∈ A
      · have hmem : a ∈ insert aStar A := mem_insert_of_mem ha
        simp [roundMatchOpt, ha, hmem, hS_ins, S,
          hnw (ballItem n' a) (ballItem_mem_activeItems.mpr ha) hnex₀]
      · have hnot : a ∉ insert aStar A := by simp [ha, hneStar]
        simp [roundMatchOpt, ha, hnot]
    rcases mem_activeItems_iff.mp hx₀S with ⟨a₀, ha₀A, rfl⟩ | ⟨b₀, hb₀B, rfl⟩
    · -- `x₀ = ballItem n' a₀`
      have ha₀neStar : a₀ ≠ aStar := fun h => haStar (h ▸ ha₀A)
      have ha₀_new : roundMatchOpt π (insert aStar A) B a₀ = none := by
        simp [roundMatchOpt, mem_insert_of_mem ha₀A, hS_ins, hnx₀]
      have haStar_new : roundMatchOpt π (insert aStar A) B aStar = roundMatchOpt π A B a₀ := by
        simp [roundMatchOpt, ha₀A, hS_ins, S, hnz]
      have hdiff_le : (Finset.univ.filter fun a =>
          roundMatchOpt π A B a ≠ roundMatchOpt π (insert aStar A) B a).card ≤ 2 := by
        refine (card_le_card (s := _) (t := {aStar, a₀}) ?_).trans (card_insert_le _ _)
        intro a ha
        simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton] at ha ⊢
        by_contra hnot
        push Not at hnot
        exact ha (hsame a hnot.1 (fun h => hnot.2 (ballItem_injective U' n' h))).symm
      refine ⟨?_, hdiff_le⟩
      cases hold : roundMatchOpt π A B a₀ with
      | none =>
        have haStar_not_rem : aStar ∉ (roundStep π (A, B)).1 := fun hm => haStar (sdiff_subset hm)
        have hballs : (roundStep π (insert aStar A, B)).1 =
            insert aStar (roundStep π (A, B)).1 := by
          ext a
          simp only [roundStep, mem_sdiff_filter, mem_insert]
          rcases eq_or_ne a aStar with rfl | ha₁
          · simp [haStar_new, hold]
          · rcases eq_or_ne a a₀ with rfl | ha₂
            · simp [ha₀neStar, ha₀A, ha₀_new, hold]
            · rw [hsame a ha₁ (fun h => ha₂ (ballItem_injective U' n' h))]; simp [ha₁]
        have hbins : (roundStep π (insert aStar A, B)).2 = (roundStep π (A, B)).2 := by
          ext b
          simp only [roundStep, mem_sdiff_filter, mem_insert]
          constructor
          · rintro ⟨hbB, hno⟩
            refine ⟨hbB, ?_⟩
            rintro ⟨a, haA, hab⟩
            rcases eq_or_ne a a₀ with rfl | ha₂
            · simp [hold] at hab
            · have ha₁ : a ≠ aStar := fun h => haStar (h ▸ haA)
              exact hno ⟨a, Or.inr haA,
                (hsame a ha₁ (fun h => ha₂ (ballItem_injective U' n' h))).trans hab⟩
          · rintro ⟨hbB, hno⟩
            refine ⟨hbB, ?_⟩
            rintro ⟨a, rfl | haA, hab⟩
            · rw [haStar_new, hold] at hab; simp at hab
            · rcases eq_or_ne a a₀ with rfl | ha₂
              · rw [ha₀_new] at hab; simp at hab
              · have ha₁ : a ≠ aStar := fun h => haStar (h ▸ haA)
                exact hno ⟨a, haA,
                  (hsame a ha₁ (fun h => ha₂ (ballItem_injective U' n' h))).symm.trans hab⟩
        simp [pairDiff, hballs, hbins, card_symmDiff_insert_of_notMem haStar_not_rem]
      | some b₁ =>
        have ha₀_not_rem : a₀ ∉ (roundStep π (A, B)).1 := by
          simp [roundStep, ha₀A, hold]
        have hballs : (roundStep π (insert aStar A, B)).1 =
            insert a₀ (roundStep π (A, B)).1 := by
          ext a
          simp only [roundStep, mem_sdiff_filter, mem_insert]
          by_cases ha₁ : a = aStar
          · rw [ha₁]; simp [ha₀neStar.symm, haStar_new, hold, haStar]
          · by_cases ha₂ : a = a₀
            · rw [ha₂]; simp [ha₀A, ha₀_new]
            · rw [hsame a ha₁ (fun h => ha₂ (ballItem_injective U' n' h))]; simp [ha₁, ha₂]
        have hbins : (roundStep π (insert aStar A, B)).2 = (roundStep π (A, B)).2 := by
          ext b
          simp only [roundStep, mem_sdiff_filter, mem_insert]
          constructor
          · rintro ⟨hbB, hno⟩
            refine ⟨hbB, ?_⟩
            rintro ⟨a, haA, hab⟩
            rcases eq_or_ne a a₀ with rfl | ha₂
            · exact hno ⟨aStar, Or.inl rfl, haStar_new.trans hab⟩
            · have ha₁ : a ≠ aStar := fun h => haStar (h ▸ haA)
              exact hno ⟨a, Or.inr haA,
                (hsame a ha₁ (fun h => ha₂ (ballItem_injective U' n' h))).trans hab⟩
          · rintro ⟨hbB, hno⟩
            refine ⟨hbB, ?_⟩
            rintro ⟨a, rfl | haA, hab⟩
            · exact hno ⟨a₀, ha₀A, haStar_new.symm.trans hab⟩
            · rcases eq_or_ne a a₀ with rfl | ha₂
              · rw [ha₀_new] at hab; simp at hab
              · have ha₁ : a ≠ aStar := fun h => haStar (h ▸ haA)
                exact hno ⟨a, haA,
                  (hsame a ha₁ (fun h => ha₂ (ballItem_injective U' n' h))).symm.trans hab⟩
        simp [pairDiff, hballs, hbins, card_symmDiff_insert_of_notMem ha₀_not_rem]
    · -- `x₀ = binItem U' b₀`
      have hsame_A : ∀ a : Fin U', a ≠ aStar →
          roundMatchOpt π (insert aStar A) B a = roundMatchOpt π A B a := by
        intro a hneStar
        refine hsame a hneStar fun heq => ?_
        have hval := congrArg Fin.val heq
        simp only [ballItem, binItem, Fin.val_castAdd, Fin.val_natAdd] at hval
        omega
      have haStar_new : roundMatchOpt π (insert aStar A) B aStar =
          asBin? (nextItem π S (binItem U' b₀)) := by
        simp [roundMatchOpt, hS_ins, hnz]
      have hdiff_le : (Finset.univ.filter fun a =>
          roundMatchOpt π A B a ≠ roundMatchOpt π (insert aStar A) B a).card ≤ 1 := by
        refine (card_le_card (s := _) (t := {aStar}) ?_).trans (by simp)
        intro a ha
        simp only [mem_filter, mem_univ, true_and, mem_singleton] at ha ⊢
        by_contra hne
        exact ha (hsame_A a hne).symm
      refine ⟨?_, by omega⟩
      cases hbin : asBin? (nextItem π S (binItem U' b₀)) with
      | none =>
        have haStar_not_rem : aStar ∉ (roundStep π (A, B)).1 := fun hm => haStar (sdiff_subset hm)
        have hballs : (roundStep π (insert aStar A, B)).1 =
            insert aStar (roundStep π (A, B)).1 := by
          ext a
          simp only [roundStep, mem_sdiff_filter, mem_insert]
          rcases eq_or_ne a aStar with rfl | ha₁
          · simp [haStar_new, hbin]
          · rw [hsame_A a ha₁]; simp [ha₁]
        have hbins : (roundStep π (insert aStar A, B)).2 = (roundStep π (A, B)).2 := by
          ext b
          simp only [roundStep, mem_sdiff_filter, mem_insert]
          constructor
          · rintro ⟨hbB, hno⟩
            refine ⟨hbB, ?_⟩
            rintro ⟨a, haA, hab⟩
            have ha₁ : a ≠ aStar := fun h => haStar (h ▸ haA)
            exact hno ⟨a, Or.inr haA, (hsame_A a ha₁).trans hab⟩
          · rintro ⟨hbB, hno⟩
            refine ⟨hbB, ?_⟩
            rintro ⟨a, rfl | haA, hab⟩
            · rw [haStar_new, hbin] at hab; simp at hab
            · have ha₁ : a ≠ aStar := fun h => haStar (h ▸ haA)
              exact hno ⟨a, haA, (hsame_A a ha₁).symm.trans hab⟩
        simp [pairDiff, hballs, hbins, card_symmDiff_insert_of_notMem haStar_not_rem]
      | some b₁ =>
        have hnext_b₀ : nextItem π S (binItem U' b₀) = binItem U' b₁ :=
          asBin?_eq_some_iff.mp hbin
        have hb₁B : b₁ ∈ B :=
          binItem_mem_activeItems.mp (hnext_b₀ ▸ nextItem_mem π hSne (binItem U' b₀))
        have hno_ball_b₁ : ∀ a ∈ A, roundMatchOpt π A B a ≠ some b₁ := by
          intro a haA hab
          dsimp only [roundMatchOpt] at hab
          simp only [haA, ↓reduceIte] at hab
          have hnext_a : nextItem π S (ballItem n' a) = binItem U' b₁ :=
            asBin?_eq_some_iff.mp hab
          have hinj := nextItem_injective π S
            (ballItem_mem_activeItems.mpr haA) (binItem_mem_activeItems.mpr hb₀B)
            (hnext_a.trans hnext_b₀.symm)
          have hval := congrArg Fin.val hinj
          simp only [ballItem, binItem, Fin.val_castAdd, Fin.val_natAdd] at hval
          omega
        have hb₁_rem : b₁ ∈ (roundStep π (A, B)).2 := by
          simp only [roundStep, mem_sdiff_filter, hb₁B, true_and]
          rintro ⟨a, haA, hab⟩
          exact hno_ball_b₁ a haA hab
        have hballs : (roundStep π (insert aStar A, B)).1 = (roundStep π (A, B)).1 := by
          ext a
          simp only [roundStep, mem_sdiff_filter, mem_insert]
          rcases eq_or_ne a aStar with rfl | ha₁
          · simp [haStar_new, hbin, haStar]
          · rw [hsame_A a ha₁]; simp [ha₁]
        have hbins : (roundStep π (insert aStar A, B)).2 = (roundStep π (A, B)).2.erase b₁ := by
          ext b
          simp only [roundStep, mem_sdiff_filter, mem_insert, mem_erase]
          constructor
          · rintro ⟨hbB, hno⟩
            have hbb₁ : b ≠ b₁ := by
              rintro rfl
              exact hno ⟨aStar, Or.inl rfl, haStar_new.trans hbin⟩
            refine ⟨hbb₁, hbB, ?_⟩
            rintro ⟨a, haA, hab⟩
            have ha₁ : a ≠ aStar := fun h => haStar (h ▸ haA)
            exact hno ⟨a, Or.inr haA, (hsame_A a ha₁).trans hab⟩
          · rintro ⟨hbb₁, hbB, hno⟩
            refine ⟨hbB, ?_⟩
            rintro ⟨a, rfl | haA, hab⟩
            · rw [haStar_new, hbin] at hab
              exact hbb₁ (Option.some.inj hab).symm
            · have ha₁ : a ≠ aStar := fun h => haStar (h ▸ haA)
              exact hno ⟨a, haA, (hsame_A a ha₁).symm.trans hab⟩
        simp [pairDiff, hballs, hbins, card_symmDiff_erase_of_mem hb₁_rem]
  · -- `S = ∅`, so `A = ∅` and `B = ∅`
    have hA : A = ∅ := by
      ext a; simp only [notMem_empty, iff_false]
      intro ha; exact hSne ⟨ballItem n' a, ballItem_mem_activeItems.mpr ha⟩
    have hB : B = ∅ := by
      ext b; simp only [notMem_empty, iff_false]
      intro hb; exact hSne ⟨binItem U' b, binItem_mem_activeItems.mpr hb⟩
    subst hA; subst hB
    have hnone_empty : ∀ a : Fin U', roundMatchOpt π ∅ ∅ a = none := by
      intro a; simp [roundMatchOpt]
    have hnone_sing : ∀ a : Fin U', roundMatchOpt π {aStar} ∅ a = none := by
      intro a
      by_cases ha : a = aStar
      · rw [ha]
        have hS1 : activeItems ({aStar} : Finset (Fin U')) (∅ : Finset (Fin n')) =
            {ballItem n' aStar} := by ext z; simp [activeItems]
        have hmem := nextItem_mem π (singleton_nonempty (ballItem n' aStar)) (ballItem n' aStar)
        rw [mem_singleton] at hmem
        unfold roundMatchOpt
        simp [hS1, hmem]
      · simp [roundMatchOpt, ha]
    have hrs1 : roundStep π (∅, ∅) = (∅, ∅) := by simp [roundStep]
    have hrs2 : roundStep π ({aStar}, ∅) = ({aStar}, ∅) := by
      ext <;> simp [roundStep, hnone_sing]
    have hcard1 : ((∅ : Finset (Fin U')) ∆ {aStar}).card = 1 :=
      card_symmDiff_insert_of_notMem (notMem_empty aStar)
    simp [hnone_empty, hnone_sing, hrs1, hrs2, pairDiff, hcard1]

private theorem symmDiff_card_eq_one_cases {α : Type*} [DecidableEq α] {s t : Finset α}
    (h : (s ∆ t).card = 1) :
    (∃ x ∉ s, t = insert x s) ∨ (∃ x ∉ t, s = insert x t) := by
  rcases card_eq_one.mp h with ⟨x, hx⟩
  have hmem : x ∈ s ∆ t := hx ▸ mem_singleton_self x
  rcases mem_symmDiff.mp hmem with ⟨hxs, hxt⟩ | ⟨hxt, hxs⟩
  · refine Or.inr ⟨x, hxt, ?_⟩
    ext z
    by_cases hz : z = x
    · subst hz; simp [hxs]
    · have hni : z ∉ s ∆ t := by rw [hx]; simp [hz]
      simp only [mem_symmDiff, not_or, not_and, Classical.not_not] at hni
      simp only [mem_insert, hz, false_or]
      exact ⟨hni.1, hni.2⟩
  · refine Or.inl ⟨x, hxs, ?_⟩
    ext z
    by_cases hz : z = x
    · subst hz; simp [hxt]
    · have hni : z ∉ s ∆ t := by rw [hx]; simp [hz]
      simp only [mem_symmDiff, not_or, not_and, Classical.not_not] at hni
      simp only [mem_insert, hz, false_or]
      exact ⟨hni.2, hni.1⟩

/-- Single-round invariant of **Claim 3.4**: whenever `pairDiff AB AB' ≤ 1`, `roundStep π`
preserves `pairDiff ≤ 1` and alters at most `2` balls' single-round match assignments. -/
private theorem pairDiff_roundStep_le_one {U' n' : ℕ} (π : RoundPerm U' n')
    {AB AB' : Finset (Fin U') × Finset (Fin n')} (hp : pairDiff AB AB' ≤ 1) :
    pairDiff (roundStep π AB) (roundStep π AB') ≤ 1 ∧
      (Finset.univ.filter fun a =>
        roundMatchOpt π AB.1 AB.2 a ≠ roundMatchOpt π AB'.1 AB'.2 a).card ≤ 2 := by
  rcases AB with ⟨A, B⟩
  rcases AB' with ⟨A', B'⟩
  dsimp only [pairDiff] at hp
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp with h0 | h1
  · have hA0 : A = A' := symmDiff_eq_bot.mp (card_eq_zero.mp (by omega))
    have hB0 : B = B' := symmDiff_eq_bot.mp (card_eq_zero.mp (by omega))
    subst hA0; subst hB0
    simp [pairDiff]
  · have hcases : ((A ∆ A').card = 1 ∧ (B ∆ B').card = 0) ∨
        ((A ∆ A').card = 0 ∧ (B ∆ B').card = 1) := by omega
    rcases hcases with ⟨hA1, hB0⟩ | ⟨hA0, hB1⟩
    · have hBeq : B = B' := symmDiff_eq_bot.mp (card_eq_zero.mp hB0)
      subst hBeq
      rcases symmDiff_card_eq_one_cases hA1 with ⟨aStar, ha, rfl⟩ | ⟨aStar, ha, rfl⟩
      · exact roundStep_insert_ball π ha B
      · obtain ⟨hpd, hcd⟩ := roundStep_insert_ball π ha B
        rw [pairDiff_comm] at hpd
        have hcd' : (Finset.univ.filter fun a =>
            roundMatchOpt π (insert aStar A') B a ≠ roundMatchOpt π A' B a).card =
            (Finset.univ.filter fun a =>
              roundMatchOpt π A' B a ≠ roundMatchOpt π (insert aStar A') B a).card := by
          congr 1; ext a; simp [ne_comm]
        exact ⟨hpd, hcd' ▸ hcd⟩
    · have hAeq : A = A' := symmDiff_eq_bot.mp (card_eq_zero.mp hA0)
      subst hAeq
      dsimp only
      rcases symmDiff_card_eq_one_cases hB1 with ⟨bStar, hb, rfl⟩ | ⟨bStar, hb, rfl⟩
      · obtain ⟨hpd, hcd⟩ := roundStep_insert_bin π A hb
        exact ⟨hpd, by omega⟩
      · obtain ⟨hpd, hcd⟩ := roundStep_insert_bin π A hb
        rw [pairDiff_comm] at hpd
        have hcd' : (Finset.univ.filter fun a =>
            roundMatchOpt π A (insert bStar B') a ≠ roundMatchOpt π A B' a).card =
            (Finset.univ.filter fun a =>
              roundMatchOpt π A B' a ≠ roundMatchOpt π A (insert bStar B') a).card := by
          congr 1; ext a; simp [ne_comm]
        exact ⟨hpd, by omega⟩

private theorem pairDiff_stateAt_le_one {U' n' : ℕ} (h : Scheme U' n')
    {A A' : Finset (Fin U')} {B B' : Finset (Fin n')}
    (hp : pairDiff (A, B) (A', B') ≤ 1) (i : ℕ) :
    pairDiff (stateAt h A B i) (stateAt h A' B' i) ≤ 1 := by
  induction i with
  | zero => exact hp
  | succ i ih =>
    dsimp only [stateAt]
    split_ifs with hi
    · exact (pairDiff_roundStep_le_one (h ⟨i, hi⟩) ih).1
    · exact ih

private theorem stateAt_balls_eq_empty_of_roundsOn_le {U' n' : ℕ} (h : Scheme U' n')
    {A : Finset (Fin U')} {B : Finset (Fin n')} (hle : A.card ≤ B.card)
    {i : ℕ} (hi : roundsOn h A B ≤ i) : (stateAt h A B i).1 = ∅ := by
  have hAU : A.card ≤ U' := by simpa using A.card_le_univ
  by_cases hiU : i < U'
  · by_contra hne
    have hne' : (stateAt h A B i).1.Nonempty := nonempty_iff_ne_empty.mpr hne
    have hsub : Finset.range (i + 1) ⊆
        (Finset.range U').filter (fun j => (stateAt h A B j).1.Nonempty) := by
      intro j hj
      have hjle : j ≤ i := Nat.lt_succ_iff.mp (mem_range.mp hj)
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_of_le_of_lt hjle hiU),
        hne'.mono (stateAt_balls_mono h A B hjle)⟩
    have hcard := card_le_card hsub
    rw [card_range] at hcard
    dsimp only [roundsOn] at hi
    omega
  · exact stateAt_balls_eq_empty h hle (hAU.trans (Nat.le_of_not_lt hiU))

/-- **Claim 3.4** round-count stability ([LiLiangYuZhou2024, Section 3.1]): under a single-element
change `pairDiff (A, B) (A', B') ≤ 1`, `roundsOn h A' B' ≤ roundsOn h A B + 1`. -/
private theorem roundsOn_le_succ_of_pairDiff_le_one {U' n' : ℕ} (h : Scheme U' n')
    {A A' : Finset (Fin U')} {B B' : Finset (Fin n')}
    (hle : A.card ≤ B.card) (hle' : A'.card ≤ B'.card) (hp : pairDiff (A, B) (A', B') ≤ 1) :
    roundsOn h A' B' ≤ roundsOn h A B + 1 := by
  set T := roundsOn h A B
  have hAT : (stateAt h A B T).1 = ∅ := stateAt_balls_eq_empty_of_roundsOn_le h hle le_rfl
  have hpdT : pairDiff (stateAt h A B T) (stateAt h A' B' T) ≤ 1 :=
    pairDiff_stateAt_le_one h hp T
  have hcard1 : (stateAt h A' B' T).1.card ≤ 1 := by
    dsimp only [pairDiff] at hpdT
    have hsym : ∅ ∆ (stateAt h A' B' T).1 = (stateAt h A' B' T).1 := by ext x; simp [mem_symmDiff]
    rw [hAT, hsym] at hpdT
    omega
  by_cases hTU : T < U'
  · have hAT1 : (stateAt h A' B' (T + 1)).1 = ∅ := by
      dsimp only [stateAt]
      simp only [hTU, ↓reduceDIte]
      by_cases hne : (stateAt h A' B' T).1.Nonempty
      · have hBne : (stateAt h A' B' T).2.Nonempty := card_pos.mp <|
          lt_of_lt_of_le (card_pos.mpr hne) (card_balls_le_card_bins_stateAt h hle' T)
        have hlt := card_balls_roundStep_lt (h ⟨T, hTU⟩) hne hBne
        rw [Prod.mk.eta] at hlt
        exact card_eq_zero.mp (by omega)
      · dsimp only [roundStep]
        rw [not_nonempty_iff_eq_empty.mp hne]
        simp
    have hsub : ((Finset.range U').filter fun j => (stateAt h A' B' j).1.Nonempty) ⊆
        Finset.range (T + 1) := by
      intro j hj
      obtain ⟨_, hne⟩ := mem_filter.mp hj
      rw [mem_range]
      by_contra hge
      exact hne.ne_empty <| subset_empty.mp
        (hAT1 ▸ stateAt_balls_mono h A' B' (Nat.le_of_not_lt hge))
    exact (card_le_card hsub).trans (by simp)
  · have hleU : roundsOn h A' B' ≤ U' :=
      (card_le_card (filter_subset _ _)).trans (by simp)
    omega

/-- **Claim 3.4** relocation bound ([LiLiangYuZhou2024, Section 3.1]): under
`pairDiff (A, B) (A', B') ≤ 1`, at most `2 * (roundsOn h A B + 1)` balls change their assigned bin
(including any inserted or deleted ball). -/
private theorem relocDist_le_of_pairDiff_le_one {U' n' : ℕ} (h : Scheme U' n')
    {A A' : Finset (Fin U')} {B B' : Finset (Fin n')}
    (hle : A.card ≤ B.card) (hle' : A'.card ≤ B'.card)
    (hp : pairDiff (A, B) (A', B') ≤ 1) :
    relocDist (matchOptOn h A B) (matchOptOn h A' B') ≤ 2 * (roundsOn h A B + 1) := by
  set M := min U' (max (roundsOn h A B) (roundsOn h A' B'))
  have haux_diff : ∀ k ≤ M,
      (Finset.univ.filter fun a => matchAux h A B k a ≠ matchAux h A' B' k a).card ≤ 2 * k := by
    intro k hkM
    induction k with
    | zero => simp [matchAux]
    | succ k ih =>
      have hkU : k < U' := Nat.lt_of_succ_le (hkM.trans (min_le_left _ _))
      let Dk := Finset.univ.filter fun a => matchAux h A B k a ≠ matchAux h A' B' k a
      let Rk := Finset.univ.filter fun a =>
        roundMatchOpt (h ⟨k, hkU⟩) (stateAt h A B k).1 (stateAt h A B k).2 a ≠
          roundMatchOpt (h ⟨k, hkU⟩) (stateAt h A' B' k).1 (stateAt h A' B' k).2 a
      have hsub : (Finset.univ.filter fun a =>
          matchAux h A B (k + 1) a ≠ matchAux h A' B' (k + 1) a) ⊆ Dk ∪ Rk := by
        intro a ha
        simp only [mem_filter, mem_univ, true_and, mem_union, Dk, Rk] at ha ⊢
        by_contra hnot
        push Not at hnot
        apply ha
        dsimp only [matchAux]
        rw [hnot.1]
        cases matchAux h A' B' k a with
        | some b => rfl
        | none => simp [hkU, hnot.2]
      have hRk : Rk.card ≤ 2 :=
        (pairDiff_roundStep_le_one (h ⟨k, hkU⟩) (pairDiff_stateAt_le_one h hp k)).2
      have hDk : Dk.card ≤ 2 * k := ih (Nat.le_of_succ_le hkM)
      calc (Finset.univ.filter fun a =>
              matchAux h A B (k + 1) a ≠ matchAux h A' B' (k + 1) a).card
          ≤ (Dk ∪ Rk).card := card_le_card hsub
        _ ≤ Dk.card + Rk.card := card_union_le _ _
        _ ≤ 2 * k + 2 := Nat.add_le_add hDk hRk
        _ = 2 * (k + 1) := by ring
  have hfreeze : ∀ k, M ≤ k → k ≤ U' →
      matchAux h A B k = matchAux h A B M ∧ matchAux h A' B' k = matchAux h A' B' M := by
    intro k hkM hkU
    induction k with
    | zero =>
      have hM0 : M = 0 := Nat.le_zero.mp hkM
      rw [hM0]; exact ⟨rfl, rfl⟩
    | succ k ih =>
      rcases eq_or_lt_of_le hkM with hMeq | hMlt
      · rw [hMeq]; exact ⟨rfl, rfl⟩
      · have hkM' : M ≤ k := Nat.lt_succ_iff.mp hMlt
        have hkU' : k < U' := Nat.lt_of_succ_le hkU
        obtain ⟨ih1, ih2⟩ := ih hkM' hkU'.le
        have hmax_le : max (roundsOn h A B) (roundsOn h A' B') ≤ k := by
          have hMU : M = max (roundsOn h A B) (roundsOn h A' B') :=
            min_eq_right (by omega)
          omega
        have hA_emp : (stateAt h A B k).1 = ∅ :=
          stateAt_balls_eq_empty_of_roundsOn_le h hle ((le_max_left _ _).trans hmax_le)
        have hA'_emp : (stateAt h A' B' k).1 = ∅ :=
          stateAt_balls_eq_empty_of_roundsOn_le h hle' ((le_max_right _ _).trans hmax_le)
        refine ⟨?_, ?_⟩
        · funext a
          dsimp only [matchAux]
          rw [ih1]
          cases matchAux h A B M a with
          | some b => rfl
          | none => simp [hkU', roundMatchOpt, hA_emp]
        · funext a
          dsimp only [matchAux]
          rw [ih2]
          cases matchAux h A' B' M a with
          | some b => rfl
          | none => simp [hkU', roundMatchOpt, hA'_emp]
  obtain ⟨hf1, hf2⟩ := hfreeze U' (min_le_left _ _) le_rfl
  have hT'_le : roundsOn h A' B' ≤ roundsOn h A B + 1 :=
    roundsOn_le_succ_of_pairDiff_le_one h hle hle' hp
  have hM_le : M ≤ roundsOn h A B + 1 :=
    (min_le_right _ _).trans (max_le (Nat.le_succ _) hT'_le)
  dsimp only [relocDist, matchOptOn]
  rw [hf1, hf2]
  exact (haux_diff M le_rfl).trans (Nat.mul_le_mul_left 2 hM_le)

/-- Single-key insertion relocation bound (`Claim 3.4`, `B = Finset.univ`). -/
theorem relocDist_insert_le {U' n' : ℕ} (h : Scheme U' n')
    {A : Finset (Fin U')} (x : Fin U') (hins : (insert x A).card ≤ n') :
    relocDist (matchOpt h A) (matchOpt h (insert x A)) ≤ 2 * (rounds h A + 1) := by
  have hA : A.card ≤ n' := (card_le_card (subset_insert x A)).trans hins
  have hp : pairDiff (A, (Finset.univ : Finset (Fin n')))
      (insert x A, (Finset.univ : Finset (Fin n'))) ≤ 1 := by
    by_cases hx : x ∈ A
    · simp [pairDiff, insert_eq_of_mem hx]
    · simp [pairDiff, card_symmDiff_insert_of_notMem hx]
  exact relocDist_le_of_pairDiff_le_one h (by simpa using hA) (by simpa using hins) hp

/-- Single-key deletion relocation bound (`Claim 3.4`, `B = Finset.univ`). -/
theorem relocDist_delete_le {U' n' : ℕ} (h : Scheme U' n')
    {A : Finset (Fin U')} (x : Fin U') (hA : A.card ≤ n') :
    relocDist (matchOpt h A) (matchOpt h (A.erase x)) ≤ 2 * (rounds h A + 1) := by
  have her : (A.erase x).card ≤ n' := card_erase_le.trans hA
  have hp : pairDiff (A, (Finset.univ : Finset (Fin n')))
      (A.erase x, (Finset.univ : Finset (Fin n'))) ≤ 1 := by
    by_cases hx : x ∈ A
    · simp [pairDiff, card_symmDiff_erase_of_mem hx]
    · simp [pairDiff, erase_eq_of_notMem hx]
  exact relocDist_le_of_pairDiff_le_one h (by simpa using hA) (by simpa using her) hp

/-- Atomic key-replacement relocation bound (`Section 5.2` leaf minimap replacement
`(A \ {x}) ∪ {y}` at fixed capacity `A.card ≤ n'`): decomposes through `A.erase x` without ever
exceeding `n'` active balls. -/
theorem relocDist_replace_le {U' n' : ℕ} (h : Scheme U' n')
    {A : Finset (Fin U')} (x y : Fin U') (hA : A.card ≤ n')
    (hrep : (insert y (A.erase x)).card ≤ n') :
    relocDist (matchOpt h A) (matchOpt h (insert y (A.erase x))) ≤ 4 * rounds h A + 6 := by
  have h1 := relocDist_delete_le h x hA
  have h2 := relocDist_insert_le h (A := A.erase x) y hrep
  have hT : rounds h (A.erase x) ≤ rounds h A + 1 := by
    have hp : pairDiff (A, (Finset.univ : Finset (Fin n')))
        (A.erase x, (Finset.univ : Finset (Fin n'))) ≤ 1 := by
      by_cases hx : x ∈ A
      · simp [pairDiff, card_symmDiff_erase_of_mem hx]
      · simp [pairDiff, erase_eq_of_notMem hx]
    exact roundsOn_le_succ_of_pairDiff_le_one h (by simpa using hA)
      (by simpa using card_erase_le.trans hA) hp
  have htri := relocDist_triangle (matchOpt h A) (matchOpt h (A.erase x))
    (matchOpt h (insert y (A.erase x)))
  omega

/-- **Lemma 3.2** ([LiLiangYuZhou2024, Section 3.1]) for ball insertion:
expected relocation cost is `O(log (max |A| 2))`. -/
theorem expect_relocDist_insert_le {U' n' : ℕ} {A : Finset (Fin U')} (x : Fin U')
    (hins : (insert x A).card ≤ n') :
    (∑ h : Scheme U' n',
      (schemePMF U' n' h).toReal * (relocDist (matchOpt h A) (matchOpt h (insert x A)) : ℝ)) ≤
      8 * (Nat.clog 2 (max A.card 2) : ℝ) := by
  have hA : A.card ≤ n' := (card_le_card (subset_insert x A)).trans hins
  have hpt : ∀ h : Scheme U' n',
      (relocDist (matchOpt h A) (matchOpt h (insert x A)) : ℝ) ≤ 2 + 2 * (rounds h A : ℝ) := by
    intro h
    have hnat := relocDist_insert_le h x hins
    have hR : (relocDist (matchOpt h A) (matchOpt h (insert x A)) : ℝ) ≤
        ((2 * (rounds h A + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hR
    linarith
  have h1 := Cslib.Probability.PMF.sum_le_affine (schemePMF U' n') hpt
  have h2 := expect_rounds_le (U' := U') hA
  have hclog1 : (1 : ℝ) ≤ Nat.clog 2 (max A.card 2) := by
    exact_mod_cast (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr (by simp : 2 ^ 0 < max A.card 2)
  linarith

/-- **Lemma 3.2** for ball deletion: expected relocation cost is `O(log (max |A| 2))`. -/
theorem expect_relocDist_delete_le {U' n' : ℕ} {A : Finset (Fin U')} (x : Fin U')
    (hA : A.card ≤ n') :
    (∑ h : Scheme U' n',
      (schemePMF U' n' h).toReal * (relocDist (matchOpt h A) (matchOpt h (A.erase x)) : ℝ)) ≤
      8 * (Nat.clog 2 (max A.card 2) : ℝ) := by
  have hpt : ∀ h : Scheme U' n',
      (relocDist (matchOpt h A) (matchOpt h (A.erase x)) : ℝ) ≤ 2 + 2 * (rounds h A : ℝ) := by
    intro h
    have hnat := relocDist_delete_le h x hA
    have hR : (relocDist (matchOpt h A) (matchOpt h (A.erase x)) : ℝ) ≤
        ((2 * (rounds h A + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hR
    linarith
  have h1 := Cslib.Probability.PMF.sum_le_affine (schemePMF U' n') hpt
  have h2 := expect_rounds_le (U' := U') hA
  have hclog1 : (1 : ℝ) ≤ Nat.clog 2 (max A.card 2) := by
    exact_mod_cast (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr (by simp : 2 ^ 0 < max A.card 2)
  linarith

/-- **Lemma 3.2** for atomic ball replacement `(A.erase x) ∪ {y}`: expected relocation cost is
`O(log (max |A| 2))`. -/
theorem expect_relocDist_replace_le {U' n' : ℕ} {A : Finset (Fin U')}
    (x y : Fin U') (hA : A.card ≤ n') (hrep : (insert y (A.erase x)).card ≤ n') :
    (∑ h : Scheme U' n',
      (schemePMF U' n' h).toReal *
        (relocDist (matchOpt h A) (matchOpt h (insert y (A.erase x))) : ℝ)) ≤
      18 * (Nat.clog 2 (max A.card 2) : ℝ) := by
  have hpt : ∀ h : Scheme U' n',
      (relocDist (matchOpt h A) (matchOpt h (insert y (A.erase x))) : ℝ) ≤
        6 + 4 * (rounds h A : ℝ) := by
    intro h
    have hnat := relocDist_replace_le h x y hA hrep
    have hR : (relocDist (matchOpt h A) (matchOpt h (insert y (A.erase x))) : ℝ) ≤
        ((4 * rounds h A + 6 : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hR
    linarith
  have h1 := Cslib.Probability.PMF.sum_le_affine (schemePMF U' n') hpt
  have h2 := expect_rounds_le (U' := U') hA
  have hclog1 : (1 : ℝ) ≤ Nat.clog 2 (max A.card 2) := by
    exact_mod_cast (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr (by simp : 2 ^ 0 < max A.card 2)
  linarith

end Cslib.DataStructure.Dictionary.DynamicMatching
