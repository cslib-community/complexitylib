/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.Layout
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Deterministic mask tables for matrix bands

Size-`m` level sets are ordered by their binary masks. The first `K0²` masks are assigned
in row-major order to block pairs. This specifies a deterministic instance of the existing
`Layout`; a native scan can compute the table without receiving indexing data as an input.

## Main definitions

* `MaskTable.maskSet`, `MaskTable.maskCode`: explicit binary masks and level sets.
* `MaskTable.population`: the truncated binary population count computed by division loops.
* `MaskTable.validMasks`: the masks with the required cardinality.

## Main results

* `MaskTable.card_validMasks`: exactly `L.choose m` valid masks exist.
-/

@[expose] public section

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage.MaskTable

open Finset

/-- The set of levels whose binary digit is one. -/
def maskSet {L : ℕ} (a : Fin (2 ^ L)) : Finset (Fin L) :=
  univ.filter fun i => finFunctionFinEquiv.symm a i = (1 : Fin 2)

/-- The integer mask of a finite level set, with level zero least significant. -/
def maskCode {L : ℕ} (Q : Finset (Fin L)) : Fin (2 ^ L) :=
  finFunctionFinEquiv fun i => if i ∈ Q then (1 : Fin 2) else 0

/-- Decoding the explicitly numbered mask recovers the original set. -/
theorem maskSet_maskCode {L : ℕ} (Q : Finset (Fin L)) : maskSet (maskCode Q) = Q := by
  ext i
  simp [maskSet, maskCode]

/-- Encoding a decoded bounded mask recovers the original integer. -/
theorem maskCode_maskSet {L : ℕ} (a : Fin (2 ^ L)) : maskCode (maskSet a) = a := by
  apply finFunctionFinEquiv.symm.injective
  funext i
  simp only [maskCode, Equiv.symm_apply_apply, maskSet, mem_filter, mem_univ, true_and]
  have h := (finFunctionFinEquiv.symm a i).isLt
  split <;> apply Fin.ext <;> simp_all only [Fin.ext_iff, Fin.val_one, Fin.val_zero]
  omega

/-- Binary-mask numbering is an explicit bijection, not a chosen enumeration. -/
def maskEquiv (L : ℕ) : Fin (2 ^ L) ≃ Finset (Fin L) where
  toFun := maskSet
  invFun := maskCode
  left_inv := maskCode_maskSet
  right_inv := maskSet_maskCode

/-- Number of one digits among exactly the first `L` binary digits. -/
def population (L a : ℕ) : ℕ := ∑ i : Fin L, a / 2 ^ i.val % 2

/-- A zero-depth scan has population zero. -/
theorem population_zero (a : ℕ) : population 0 a = 0 := by simp [population]

/-- One native remainder/division step removes the lowest digit. -/
theorem population_succ (L a : ℕ) :
    population (L + 1) a = a % 2 + population L (a / 2) := by
  simp only [population, Fin.sum_univ_succ, Fin.val_zero, pow_zero, Nat.div_one,
    Fin.val_succ, pow_succ', ← Nat.div_div_eq_div_mul]

/-- There are at most `L` one digits, even for an unbounded natural argument. -/
theorem population_le (L a : ℕ) : population L a ≤ L := by
  induction L generalizing a with
  | zero => rw [population_zero]
  | succ L ih =>
    rw [population_succ]
    have hm := Nat.mod_lt a (by decide : 0 < 2)
    have ht := ih (a / 2)
    omega

/-- The loop's digit sum is the cardinality of the represented level set. -/
theorem population_eq_card {L : ℕ} (a : Fin (2 ^ L)) :
    population L a.val = (maskSet a).card := by
  rw [maskSet, card_eq_sum_ones, sum_filter]
  apply sum_congr rfl
  intro i _
  have h : (finFunctionFinEquiv.symm a i).val = a.val / 2 ^ i.val % 2 := rfl
  have hb := (finFunctionFinEquiv.symm a i).isLt
  split <;> simp_all only [Fin.ext_iff, Fin.val_one]
  omega

/-- All valid masks, in the ordinary linear order on bounded naturals. -/
def validMasks (L m : ℕ) : Finset (Fin (2 ^ L)) :=
  univ.filter fun a => population L a.val = m

/-- Every size-`m` subset occurs once in the bounded mask scan. -/
theorem card_validMasks (L m : ℕ) : (validMasks L m).card = K L m := by
  calc
    (validMasks L m).card = ((univ : Finset (Fin L)).powersetCard m).card := by
      apply card_bij (fun a _ => maskSet a)
      · intro a ha
        rw [mem_powersetCard_univ]
        rw [← population_eq_card]
        exact (mem_filter.mp ha).2
      · intro a _ b _ h
        exact (maskEquiv L).injective h
      · intro Q hQ
        refine ⟨maskCode Q, ?_, maskSet_maskCode Q⟩
        simp only [validMasks, mem_filter, mem_univ, true_and, population_eq_card,
          maskSet_maskCode]
        exact mem_powersetCard_univ.mp hQ
    _ = K L m := by rw [card_powersetCard, card_univ, Fintype.card_fin]; rfl

/-- Number of valid masks strictly below the scan counter. -/
def prefixCount (L m t : ℕ) : ℕ := ((range t).filter fun a => population L a = m).card

/-- The scan begins without any accepted mask. -/
theorem prefixCount_zero (L m : ℕ) : prefixCount L m 0 = 0 := by simp [prefixCount]

/-- A scan accepts at most one mask in each iteration. -/
theorem prefixCount_le (L m t : ℕ) : prefixCount L m t ≤ t :=
  (card_filter_le _ _).trans (by rw [card_range])

/-- The actual scalar counter update for one mask. -/
theorem prefixCount_succ (L m t : ℕ) :
    prefixCount L m (t + 1) = prefixCount L m t + if population L t = m then 1 else 0 := by
  by_cases h : population L t = m <;> simp [prefixCount, range_add_one, filter_insert, h]

/-- Extending a scan cannot decrease the accepted-mask counter. -/
theorem prefixCount_mono (L m : ℕ) {a b : ℕ} (h : a ≤ b) :
    prefixCount L m a ≤ prefixCount L m b :=
  card_le_card (filter_subset_filter _ (range_mono h))

/-- Earlier valid masks have strictly smaller accepted-mask ranks. -/
theorem prefixCount_lt {L m a b : ℕ} (ha : population L a = m) (hab : a < b) :
    prefixCount L m a < prefixCount L m b := by
  have h := prefixCount_mono L m (show a + 1 ≤ b by omega)
  rw [prefixCount_succ] at h
  simp only [ha, ↓reduceIte] at h
  omega

/-- The finite complete scan has exactly the binomial count. -/
theorem prefixCount_full (L m : ℕ) : prefixCount L m (2 ^ L) = K L m := by
  rw [← card_validMasks]
  apply card_bij (fun a ha => (⟨a, mem_range.mp (mem_filter.mp ha).1⟩ : Fin (2 ^ L)))
  · intro a ha
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ha).2⟩
  · intro a _ b _ h
    exact congrArg Fin.val h
  · intro a ha
    exact ⟨a.val, mem_filter.mpr ⟨mem_range.mpr a.isLt, (mem_filter.mp ha).2⟩, rfl⟩

private theorem card_below_orderEmb {α : Type*} [LinearOrder α] (s : Finset α)
    {n : ℕ} (h : s.card = n) (i : Fin n) :
    (s.filter fun a => a < s.orderEmbOfFin h i).card = i.val := by
  rw [← card_range i.val]
  symm
  apply card_bij (fun j hj => s.orderEmbOfFin h
    ⟨j, (mem_range.mp hj).trans i.isLt⟩)
  · intro j hj
    exact mem_filter.mpr ⟨s.orderEmbOfFin_mem h _,
      (s.orderEmbOfFin h).strictMono (mem_range.mp hj)⟩
  · intro j hj k hk hjk
    exact congrArg Fin.val ((s.orderEmbOfFin h).injective hjk)
  · intro a ha
    let j := (s.orderIsoOfFin h).symm ⟨a, (mem_filter.mp ha).1⟩
    have hj : s.orderEmbOfFin h j = a :=
      congrArg Subtype.val ((s.orderIsoOfFin h).apply_symm_apply ⟨a, (mem_filter.mp ha).1⟩)
    have hji : j < i := (s.orderEmbOfFin h).lt_iff_lt.mp (hj ▸ (mem_filter.mp ha).2)
    exact ⟨j.val, mem_range.mpr hji, hj⟩

/-- The scalar scan count equals the rank among the bounded valid masks. -/
theorem prefixCount_eq_bounded (L m t : ℕ) (ht : t ≤ 2 ^ L) :
    prefixCount L m t = ((validMasks L m).filter fun a => a.val < t).card := by
  apply card_bij (fun a ha =>
    (⟨a, (mem_range.mp (mem_filter.mp ha).1).trans_le ht⟩ : Fin (2 ^ L)))
  · intro a ha
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ha).2⟩,
      mem_range.mp (mem_filter.mp ha).1⟩
  · intro a _ b _ h
    exact congrArg Fin.val h
  · intro a ha
    exact ⟨a.val, mem_filter.mpr ⟨mem_range.mpr (mem_filter.mp ha).2,
      (mem_filter.mp (mem_filter.mp ha).1).2⟩, rfl⟩

/-- Row-major block-pair rank in the full list of size-`m` masks. -/
def pairRank {L m : ℕ} (gh : Fin (K0 L m) × Fin (K0 L m)) : Fin (K L m) :=
  Fin.castLE (by simpa only [K0] using Nat.sqrt_le (K L m)) (finProdFinEquiv gh)

/-- The selected mask at a block pair is the corresponding mask in increasing order. -/
def selectedMask {L m : ℕ} (gh : Fin (K0 L m) × Fin (K0 L m)) : Fin (2 ^ L) :=
  (validMasks L m).orderEmbOfFin (card_validMasks L m) (pairRank gh)

/-- The computed prefix counter at a selected mask is its row-major block-pair rank. -/
theorem prefixCount_selectedMask {L m : ℕ} (gh : Fin (K0 L m) × Fin (K0 L m)) :
    prefixCount L m (selectedMask gh).val = (pairRank gh).val := by
  rw [prefixCount_eq_bounded _ _ _ (selectedMask gh).isLt.le]
  exact card_below_orderEmb (validMasks L m) (card_validMasks L m) (pairRank gh)

/-- The dense inverse-table word: zero for an unselected mask, otherwise rank plus one. -/
def lookup (L m a : ℕ) : ℕ :=
  if a < 2 ^ L ∧ population L a = m ∧ prefixCount L m a < K0 L m * K0 L m
  then prefixCount L m a + 1 else 0

/-- Exactly the selected valid masks have nonzero inverse-table words. -/
theorem lookup_ne_zero_iff (L m a : ℕ) : lookup L m a ≠ 0 ↔
    a < 2 ^ L ∧ population L a = m ∧ prefixCount L m a < K0 L m * K0 L m := by
  simp [lookup]

/-- Every inverse-table word is bounded by its original mask plus one. -/
theorem lookup_le (L m a : ℕ) : lookup L m a ≤ a + 1 := by
  unfold lookup
  split
  · exact Nat.add_le_add_right (prefixCount_le L m a) 1
  · exact Nat.zero_le _

/-- The inverse-table word at every selected block pair has the promised rank. -/
theorem lookup_selectedMask {L m : ℕ} (gh : Fin (K0 L m) × Fin (K0 L m)) :
    lookup L m (selectedMask gh).val = (pairRank gh).val + 1 := by
  have hm := (validMasks L m).orderEmbOfFin_mem (card_validMasks L m) (pairRank gh)
  have hp := (mem_filter.mp hm).2
  change population L (selectedMask gh).val = m at hp
  have hr : (pairRank gh).val < K0 L m * K0 L m := (finProdFinEquiv gh).isLt
  simp only [lookup, (selectedMask gh).isLt, hp, prefixCount_selectedMask,
    hr, and_self, ↓reduceIte]

/-- A nonzero inverse-table word belongs to one of the selected block pairs. -/
theorem exists_selectedMask_of_lookup {L m a : ℕ} (h : lookup L m a ≠ 0) :
    ∃ gh : Fin (K0 L m) × Fin (K0 L m), (selectedMask gh).val = a := by
  unfold lookup at h
  split_ifs at h with hc
  · obtain ⟨ha, hp, hr⟩ := hc
    let aa : Fin (2 ^ L) := ⟨a, ha⟩
    have hmem : aa ∈ validMasks L m := mem_filter.mpr ⟨mem_univ _, hp⟩
    let j := (validMasks L m).orderIsoOfFin (card_validMasks L m) |>.symm ⟨aa, hmem⟩
    have hj : (validMasks L m).orderEmbOfFin (card_validMasks L m) j = aa :=
      congrArg Subtype.val ((validMasks L m).orderIsoOfFin (card_validMasks L m)
        |>.apply_symm_apply ⟨aa, hmem⟩)
    have hjrank : j.val = prefixCount L m a := by
      rw [prefixCount_eq_bounded L m a ha.le]
      have hbelow := card_below_orderEmb (validMasks L m) (card_validMasks L m) j
      rw [hj] at hbelow
      exact hbelow.symm
    let gh := (@finProdFinEquiv (K0 L m) (K0 L m)).symm ⟨prefixCount L m a, hr⟩
    have hprval : (pairRank gh).val = prefixCount L m a :=
      congrArg Fin.val ((@finProdFinEquiv (K0 L m) (K0 L m)).apply_symm_apply
        ⟨prefixCount L m a, hr⟩)
    have hpr : pairRank gh = j := Fin.ext (hprval.trans hjrank.symm)
    refine ⟨gh, ?_⟩
    change ((validMasks L m).orderEmbOfFin (card_validMasks L m) (pairRank gh)).val = a
    rw [hpr, hj]
  · exact (h rfl).elim

/-- Inverse-table division and remainder recover exactly the two block indices. -/
theorem lookup_blockPair {L m : ℕ} (gh : Fin (K0 L m) × Fin (K0 L m)) :
    (lookup L m (selectedMask gh).val - 1) / K0 L m = gh.1.val ∧
      (lookup L m (selectedMask gh).val - 1) % K0 L m = gh.2.val := by
  rw [lookup_selectedMask, Nat.add_sub_cancel]
  have hpos : 0 < K0 L m := by have := gh.2.isLt; omega
  change (gh.2.val + K0 L m * gh.1.val) / K0 L m = gh.1.val ∧
    (gh.2.val + K0 L m * gh.1.val) % K0 L m = gh.2.val
  rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt gh.2.isLt, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt gh.2.isLt]
  exact ⟨rfl, rfl⟩

/-- Both decoded block indices are in range whenever the inverse-table word is nonzero. -/
theorem lookup_block_lt {L m a : ℕ} (h : lookup L m a ≠ 0) (rightSide : Bool) :
    (if rightSide then (lookup L m a - 1) % K0 L m
      else (lookup L m a - 1) / K0 L m) < K0 L m := by
  obtain ⟨gh, hs⟩ := exists_selectedMask_of_lookup h
  have hp := lookup_blockPair gh
  rw [hs] at hp
  cases rightSide
  · simpa only [Bool.false_eq_true, ↓reduceIte, hp.1] using gh.1.isLt
  · simpa only [↓reduceIte, hp.2] using gh.2.isLt

/-- Selected masks always have exactly the required cardinality. -/
theorem card_selectedMask {L m : ℕ} (gh : Fin (K0 L m) × Fin (K0 L m)) :
    (maskSet (selectedMask gh)).card = m := by
  have h := (validMasks L m).orderEmbOfFin_mem (card_validMasks L m) (pairRank gh)
  exact (population_eq_card _).symm.trans ((mem_filter.mp h).2)

/-- Distinct block pairs receive distinct level sets. -/
theorem selectedMask_injective (L m : ℕ) :
    Function.Injective (fun gh : Fin (K0 L m) × Fin (K0 L m) => maskSet (selectedMask gh)) := by
  intro gh gh' h
  have hmask := (maskEquiv L).injective h
  have hrank := (validMasks L m).orderEmbOfFin (card_validMasks L m) |>.injective hmask
  apply finProdFinEquiv.injective
  apply Fin.ext
  exact congrArg (fun i : Fin (K L m) => i.val) hrank

/-- The thin-dimension pair digit uses row-major order, as do the encoder's inner variables. -/
def innerDigits : Fin 4 ≃ Fin 2 × Fin 2 := (@finProdFinEquiv 2 2).symm

/-- Explicit base-three outer strings and base-four strings of index pairs, with the first
`K0²` binary masks in increasing order as the shared block table. -/
def layout {L m : ℕ} (hmL : m ≤ L) : Layout L m where
  hmL := hmL
  rowIdx := finFunctionFinEquiv.symm
  colIdx := finFunctionFinEquiv.symm
  innerIdx := finFunctionFinEquiv.symm.trans (Equiv.piCongrRight fun _ => innerDigits)
  table gh := maskSet (selectedMask gh)
  table_card := card_selectedMask
  table_injective := selectedMask_injective L m

end Cslib.Algorithms.MatrixMultiplication.Schonhage.MaskTable
