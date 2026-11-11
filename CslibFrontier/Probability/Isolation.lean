/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Data.Finset.Density
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod

/-!
# The isolation lemma

Give every element `i` of a finite universe `U` a weight `val (w i)`, where the labels `w i` are
chosen independently and uniformly from a finite set `W` and `val` is injective, and give a set the
sum of the weights of its elements. The *isolation lemma* of Mulmuley, Vazirani and Vazirani says
that a nonempty family `F` of subsets of `U` then has a unique set of minimum weight, except with
probability at most `|U| / |W|` (`Cslib.Probability.dens_minWeightSets_card_ne_one_le`)
[Mulmuley, Vazirani and Vazirani][MulmuleyVaziraniVazirani1987]. With weights `1, …, N` for
`N ≥ 2 |U|` the minimum is unique with probability at least `1 / 2`
(`Cslib.Probability.half_le_dens_minWeightSets_card_eq_one`). The family is arbitrary: it need
not be given explicitly, and it may be exponentially large.

The proof follows Mulmuley, Vazirani and Vazirani. If two sets have minimum weight, some element
`i` lies in one and not in the other, so `i` is *ambiguous*: some minimum-weight set contains it
and some does not. Fixing the labels of all other elements, at most one label of `i` makes it
ambiguous, since changing the weight of `i` shifts the weights of exactly the sets containing `i`.
A union bound over the elements finishes the proof. Only cancellation of addition is used, so the
weights may be natural numbers.

## Main definitions

* `Cslib.Probability.setWeight`: the weight of a set.
* `Cslib.Probability.minWeightSets`: the sets of minimum weight in a family.
* `Cslib.Probability.Ambiguous`: an element in some but not all sets of minimum weight.

## Main results

* `Cslib.Probability.dens_minWeightSets_card_ne_one_le`: **the isolation lemma**.
* `Cslib.Probability.one_sub_le_dens_minWeightSets_card_eq_one`: the same bound for success.
* `Cslib.Probability.val_eq_of_ambiguous`: at most one label makes an element ambiguous.
* `Cslib.Probability.half_le_dens_minWeightSets_card_eq_one`: weights `1, …, N`, `N ≥ 2 |U|`.

## References

* [K. Mulmuley, U. V. Vazirani, V. V. Vazirani, *Matching is as easy as matrix
  inversion*][MulmuleyVaziraniVazirani1987]
-/

@[expose] public section

namespace Cslib.Probability

open Finset

variable {U W G : Type*} [AddCommMonoid G] [LinearOrder G]

/-- The weight of a set: the sum of the values `val (w i)` of the labels of its elements. -/
def setWeight (val : W → G) (w : U → W) (S : Finset U) : G := ∑ i ∈ S, val (w i)

/-- The sets of minimum weight in the family `F`. -/
def minWeightSets (val : W → G) (w : U → W) (F : Finset (Finset U)) : Finset (Finset U) :=
  F.filter fun S => ∀ T ∈ F, setWeight val w S ≤ setWeight val w T

/-- `S` is a set of minimum weight in `F` exactly when `S ∈ F` and no set of `F` has smaller
weight. -/
theorem mem_minWeightSets {val : W → G} {w : U → W} {F : Finset (Finset U)}
    {S : Finset U} :
    S ∈ minWeightSets val w F ↔ S ∈ F ∧ ∀ T ∈ F, setWeight val w S ≤ setWeight val w T :=
  mem_filter

/-- A nonempty finite family has a set of minimum weight. -/
theorem minWeightSets_nonempty (val : W → G) (w : U → W) {F : Finset (Finset U)}
    (hF : F.Nonempty) : (minWeightSets val w F).Nonempty := by
  obtain ⟨S, hS, hmin⟩ := F.exists_min_image (setWeight val w) hF
  exact ⟨S, mem_minWeightSets.2 ⟨hS, hmin⟩⟩

/-- An element is *ambiguous* when some set of minimum weight contains it and some does not. -/
def Ambiguous (val : W → G) (w : U → W) (F : Finset (Finset U)) (i : U) : Prop :=
  (∃ S ∈ minWeightSets val w F, i ∈ S) ∧ ∃ T ∈ minWeightSets val w F, i ∉ T

/-- Two sets of minimum weight make an element of their symmetric difference ambiguous. -/
private theorem exists_ambiguous_of_card_ne_one (val : W → G) (w : U → W)
    {F : Finset (Finset U)} (hF : F.Nonempty) (h : (minWeightSets val w F).card ≠ 1) :
    ∃ i, Ambiguous val w F i := by
  classical
  obtain ⟨S, hS, T, hT, hST⟩ := one_lt_card.1 (lt_of_le_of_ne
    (card_pos.2 (minWeightSets_nonempty val w hF)) (Ne.symm h))
  obtain ⟨i, hi⟩ : ∃ i, ¬(i ∈ S ↔ i ∈ T) := by
    by_contra! h'
    exact hST (ext h')
  by_cases hiS : i ∈ S
  · exact ⟨i, ⟨S, hS, hiS⟩, T, hT, fun hiT => hi ⟨fun _ => hiT, fun _ => hiS⟩⟩
  · exact ⟨i, ⟨T, hT, by tauto⟩, S, hS, hiS⟩

omit [LinearOrder G] in
/-- Labels that differ only at `i` give the same weight to the sets without `i`. -/
theorem setWeight_eq_of_notMem {val : W → G} {w w' : U → W} {i : U}
    (hw : ∀ j, j ≠ i → w j = w' j) {S : Finset U} (hi : i ∉ S) :
    setWeight val w S = setWeight val w' S :=
  sum_congr rfl fun j hj => by rw [hw j (ne_of_mem_of_not_mem hj hi)]

omit [LinearOrder G] in
/-- Labels that differ only at `i` shift the weights of the sets with `i` by the same amount. -/
theorem setWeight_add_eq_of_mem {val : W → G} {w w' : U → W} {i : U}
    (hw : ∀ j, j ≠ i → w j = w' j) {S : Finset U} (hi : i ∈ S) :
    setWeight val w S + val (w' i) = setWeight val w' S + val (w i) := by
  classical
  have hR : ∑ j ∈ S.erase i, val (w j) = ∑ j ∈ S.erase i, val (w' j) :=
    setWeight_eq_of_notMem hw (notMem_erase i S)
  rw [setWeight, setWeight, ← add_sum_erase _ _ hi, ← add_sum_erase _ _ hi, hR]
  ac_rfl

variable [IsOrderedCancelAddMonoid G]

/-- One half of `val_eq_of_ambiguous`: if labels differing only at `i` have sets of minimum weight
`S ∋ i` for `w` and `T ∌ i` for `w'`, then `val (w i) ≤ val (w' i)`. -/
private theorem val_le_of_mem_of_notMem {val : W → G} {w w' : U → W} {F : Finset (Finset U)}
    {i : U} (hw : ∀ j, j ≠ i → w j = w' j) {S T : Finset U} (hS : S ∈ minWeightSets val w F)
    (hiS : i ∈ S) (hT : T ∈ minWeightSets val w' F) (hiT : i ∉ T) :
    val (w i) ≤ val (w' i) := by
  rw [mem_minWeightSets] at hS hT
  have hA : setWeight val w S ≤ setWeight val w' S :=
    (hS.2 _ hT.1).trans ((setWeight_eq_of_notMem (val := val) hw hiT).trans_le (hT.2 _ hS.1))
  have : setWeight val w S + val (w i) ≤ setWeight val w S + val (w' i) := by
    rw [setWeight_add_eq_of_mem hw hiS]
    exact add_le_add_left hA _
  exact le_of_add_le_add_left this

/-- **At most one label makes an element ambiguous**, once the other labels are fixed: both
labels give the sets containing `i` the minimum weight of the sets without `i`. -/
theorem val_eq_of_ambiguous {val : W → G} {w w' : U → W} {F : Finset (Finset U)} {i : U}
    (hw : ∀ j, j ≠ i → w j = w' j) (h : Ambiguous val w F i) (h' : Ambiguous val w' F i) :
    val (w i) = val (w' i) := by
  obtain ⟨⟨S, hS, hiS⟩, T, hT, hiT⟩ := h
  obtain ⟨⟨S', hS', hiS'⟩, T', hT', hiT'⟩ := h'
  exact le_antisymm (val_le_of_mem_of_notMem hw hS hiS hT' hiT')
    (val_le_of_mem_of_notMem (fun j hj => (hw j hj).symm) hS' hiS' hT hiT)

variable [Fintype U] [DecidableEq U] [Fintype W] {val : W → G}

open Classical in
/-- Each element is ambiguous for at most a `1 / |W|` fraction of the labellings: relabelling
`i` is injective on the ambiguous labellings. -/
private theorem card_ambiguous_mul_le (hval : Function.Injective val) (F : Finset (Finset U))
    (i : U) :
    (univ.filter fun w : U → W => Ambiguous val w F i).card * Fintype.card W ≤
      Fintype.card (U → W) := by
  rw [← card_univ (α := W), ← card_product, ← card_univ (α := U → W)]
  refine card_le_card_of_injOn (fun p => Function.update p.1 i p.2) (fun _ _ => mem_univ _) ?_
  rintro ⟨w, x⟩ hwx ⟨w', x'⟩ hwx' heq
  simp only [coe_product, coe_filter, mem_univ, true_and, Set.mem_prod, Set.mem_ofPred_eq,
    coe_univ, Set.mem_univ, and_true] at hwx hwx'
  have hx : x = x' := by simpa using congrFun heq i
  have hw : ∀ j, j ≠ i → w j = w' j := fun j hj => by
    simpa [Function.update_of_ne hj] using congrFun heq j
  have hwi : w i = w' i := hval (val_eq_of_ambiguous hw hwx hwx')
  refine Prod.ext (funext fun j => ?_) hx
  by_cases hj : j = i
  · subst hj; exact hwi
  · exact hw j hj

open Classical in
/-- **The isolation lemma** [Mulmuley, Vazirani and Vazirani][MulmuleyVaziraniVazirani1987]:
for every nonempty family `F` of subsets of `U`, and labels `w i` drawn uniformly and
independently from `W` with injective values `val`, the probability that `F` has more than one
set of minimum weight is at most `|U| / |W|`. -/
theorem dens_minWeightSets_card_ne_one_le [Nonempty W] (hval : Function.Injective val)
    {F : Finset (Finset U)} (hF : F.Nonempty) :
    dens (univ.filter fun w : U → W => (minWeightSets val w F).card ≠ 1) ≤
      Fintype.card U / Fintype.card W := by
  have hsub : (univ.filter fun w : U → W => (minWeightSets val w F).card ≠ 1) ⊆
      univ.biUnion fun i => univ.filter fun w => Ambiguous val w F i := by
    intro w hw
    obtain ⟨i, hi⟩ := exists_ambiguous_of_card_ne_one val w hF (mem_filter.1 hw).2
    exact mem_biUnion.2 ⟨i, mem_univ _, mem_filter.2 ⟨mem_univ _, hi⟩⟩
  have hcard : (univ.filter fun w : U → W => (minWeightSets val w F).card ≠ 1).card *
      Fintype.card W ≤ Fintype.card U * Fintype.card (U → W) := by
    calc _ ≤ (univ.biUnion fun i => univ.filter fun w : U → W => Ambiguous val w F i).card *
          Fintype.card W := Nat.mul_le_mul_right _ (card_le_card hsub)
      _ ≤ (∑ i, (univ.filter fun w : U → W => Ambiguous val w F i).card) * Fintype.card W :=
          Nat.mul_le_mul_right _ card_biUnion_le
      _ = ∑ i, (univ.filter fun w : U → W => Ambiguous val w F i).card * Fintype.card W :=
          Finset.sum_mul _ _ _
      _ ≤ ∑ _i : U, Fintype.card (U → W) :=
          sum_le_sum fun i _ => card_ambiguous_mul_le hval F i
      _ = _ := by simp
  rw [dens, div_le_div_iff₀ (by simp [Fintype.card_pos]) (by simp [Fintype.card_pos])]
  exact_mod_cast hcard

open Classical in
/-- **The isolation lemma**, for success: a nonempty family has a unique set of minimum weight with
probability at least `1 - |U| / |W|`. -/
theorem one_sub_le_dens_minWeightSets_card_eq_one [Nonempty W] (hval : Function.Injective val)
    {F : Finset (Finset U)} (hF : F.Nonempty) :
    1 - (Fintype.card U / Fintype.card W : ℚ≥0) ≤
      dens (univ.filter fun w : U → W => (minWeightSets val w F).card = 1) := by
  have hsplit := dens_filter_add_dens_filter_not_eq_dens (s := (univ : Finset (U → W)))
    fun w => (minWeightSets val w F).card = 1
  rw [dens_univ] at hsplit
  rw [tsub_le_iff_right, ← hsplit]
  gcongr
  exact dens_minWeightSets_card_ne_one_le hval hF

open Classical in
/-- **Mulmuley, Vazirani and Vazirani**: with weights drawn uniformly and independently from
`1, …, N` for some `N ≥ 2 |U|`, a nonempty family has a unique set of minimum weight with
probability at least `1 / 2`. -/
theorem half_le_dens_minWeightSets_card_eq_one {N : ℕ} [NeZero N] (hN : 2 * Fintype.card U ≤ N)
    {F : Finset (Finset U)} (hF : F.Nonempty) :
    1 / 2 ≤ dens (univ.filter fun w : U → Fin N =>
      (minWeightSets (fun x => x.val + 1) w F).card = 1) := by
  refine le_trans ?_ (one_sub_le_dens_minWeightSets_card_eq_one
    (val := fun x : Fin N => x.val + 1) (fun x y h => Fin.ext (by simpa using h)) hF)
  rw [Fintype.card_fin]
  have hN' : (0 : ℚ≥0) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have : (Fintype.card U : ℚ≥0) / N ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hN' (by norm_num)]
    exact_mod_cast (by omega : Fintype.card U * 2 ≤ 1 * N)
  calc (1 : ℚ≥0) / 2 = 1 - 1 / 2 := eq_tsub_of_add_eq (add_halves 1)
    _ ≤ 1 - Fintype.card U / N := tsub_le_tsub_left this 1

end Cslib.Probability
