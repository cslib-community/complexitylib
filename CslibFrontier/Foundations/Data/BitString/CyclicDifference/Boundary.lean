/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.CyclicDifference
public import CslibFrontier.Foundations.Data.BitString.Flip
import CslibFrontier.Foundations.GroupTheory.Perm.Fin
import Mathlib.Tactic.SplitIfs

/-!
# Ordered boundary operations on cyclic differences

Explicit coordinate maps for adjacent identification and the two-difference cap. These are
operations on Boolean tuples, with the cyclic order retained. In particular the last edge of
an adjacent identification is the last-to-first edge, rather than an implicit permutation.

## Main definitions

* `Cslib.BitString.zeroPort`: identifies the endpoints of one cyclic edge.
* `Cslib.BitString.differencePort`: lists the remaining difference coordinates in order.
* `Cslib.BitString.capPort`: identifies old ports 1 and 3 and hides old port 2.
-/

public section

namespace Cslib.BitString

/-- Identify old ports `i` and `i+1`, keeping `i`; at the last edge identify the last
port with port 0 and keep port 0. All other free ports keep their order. -/
@[expose] def zeroPort {n : ℕ} (i j : Fin (n + 2)) : Fin (n + 1) :=
  if h : j.val ≤ i.val ∧ j.val < n + 1 then ⟨j.val, h.2⟩
  else if i.val = n + 1 then 0 else ⟨j.val - 1, by omega⟩

/-- The retained difference coordinates after deleting difference `i`, in increasing order. -/
@[expose] def differencePort {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    Fin (n + 2) :=
  i.succAbove j

/-- The retained original ports; this is a right inverse of `zeroPort`. -/
@[expose] def retainPort {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    Fin (n + 2) :=
  if j.val ≤ i.val then ⟨j.val, by omega⟩ else ⟨j.val + 1, by omega⟩

private theorem val_zeroPort {n : ℕ} (i j : Fin (n + 2)) :
    (zeroPort i j).val = if j.val ≤ i.val ∧ j.val < n + 1 then j.val
      else if i.val = n + 1 then 0 else j.val - 1 := by
  unfold zeroPort
  split_ifs <;> rfl

private theorem val_retainPort {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (retainPort i j).val = if j.val ≤ i.val then j.val else j.val + 1 := by
  unfold retainPort
  split_ifs <;> rfl

private theorem val_differencePort {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (differencePort i j).val = if j.val < i.val then j.val else j.val + 1 := by
  by_cases h : j.val < i.val
  · rw [differencePort, Fin.succAbove_of_castSucc_lt _ _ (show j.castSucc < i from h)]
    simp only [Fin.val_castSucc, h, ite_true]
  · rw [differencePort, Fin.succAbove_of_le_castSucc _ _
      (show i ≤ j.castSucc from Nat.le_of_not_gt h)]
    simp only [Fin.val_succ, h, ite_false]

/-- Retaining ports after adjacent identification recovers the new free-port labels. -/
@[simp] theorem zeroPort_retainPort {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    zeroPort i (retainPort i j) = j := by
  apply Fin.ext
  simp only [val_zeroPort, val_retainPort]
  split_ifs <;> omega

/-- The deleted edge has equal endpoint labels, including the wraparound case. -/
theorem zeroPort_next {n : ℕ} (i : Fin (n + 2)) :
    zeroPort i (finRotate (n + 2) i) = zeroPort i i := by
  apply Fin.ext
  simp only [val_zeroPort, val_finRotate]
  split_ifs <;> omega

/-- Each retained edge starts at its corresponding new port. -/
theorem zeroPort_differencePort {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    zeroPort i (differencePort i j) = j := by
  apply Fin.ext
  simp only [val_zeroPort, val_differencePort]
  split_ifs <;> omega

/-- Each retained edge ends at the cyclic successor of its corresponding new port. -/
theorem zeroPort_next_differencePort {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    zeroPort i (finRotate (n + 2) (differencePort i j)) = finRotate (n + 1) j := by
  apply Fin.ext
  simp only [val_zeroPort, val_finRotate, val_differencePort]
  split_ifs <;> omega

/-- Adjacent identification forces exactly the deleted difference to zero. -/
theorem cyclicDifference_zeroPort {n : ℕ} (i : Fin (n + 2)) (y : Fin (n + 1) → Bool) :
    cyclicDifference (y ∘ zeroPort i) i = false := by
  simp only [cyclicDifference, Function.comp_apply, zeroPort_next, Bool.xor_self]

/-- All remaining differences are retained in their original cyclic order. -/
theorem cyclicDifference_zeroPort_differencePort {n : ℕ} (i : Fin (n + 2))
    (y : Fin (n + 1) → Bool) :
    cyclicDifference (y ∘ zeroPort i) ∘ differencePort i = cyclicDifference y := by
  funext j
  simp only [cyclicDifference, Function.comp_apply, zeroPort_differencePort,
    zeroPort_next_differencePort]

/-- Old ports 1 and 3 share new free port 1; old port 2 becomes the fresh auxiliary.
The free order is old ports `0,1,4,5,…`, with no permutation of the surviving ports. -/
@[expose] def capPort {n : ℕ} (j : Fin (n + 4)) : Fin (n + 2) ⊕ Fin 1 :=
  if j.val = 2 then .inr 0
  else .inl (if h : j.val < 2 then ⟨j.val, by omega⟩
    else if j.val = 3 then 1 else ⟨j.val - 2, by omega⟩)

/-- Difference coordinates surviving the cap, in the order `0,3,4,…`. -/
@[expose] def capDifferencePort {n : ℕ} (j : Fin (n + 2)) : Fin (n + 4) :=
  if j.val = 0 then 0 else ⟨j.val + 2, by omega⟩

/-- Original ports retained by the cap, in the order `0,1,4,5,…`. -/
@[expose] def capRetainPort {n : ℕ} (j : Fin (n + 2)) : Fin (n + 4) :=
  if h : j.val < 2 then ⟨j.val, by omega⟩ else ⟨j.val + 2, by omega⟩

/-- Complementing a cap assignment complements all old ports, including the hidden one. -/
theorem capPort_not {n : ℕ} (y : Fin (n + 2) → Bool) (z : Fin 1 → Bool) :
    (Sum.elim (fun i => !y i) (fun i => !z i)) ∘ capPort =
      fun i => !((Sum.elim y z) (capPort i)) := by
  funext i
  simp only [Function.comp_apply]
  cases capPort i <;> rfl

/-- Re-expanding a retained port returns the original port except for the merged endpoint. -/
theorem retainPort_zeroPort {n : ℕ} (i j : Fin (n + 2)) :
    retainPort i (zeroPort i j) = j ∨
      (j = finRotate (n + 2) i ∧ retainPort i (zeroPort i j) = i) ∨
      (j = i ∧ retainPort i (zeroPort i j) = finRotate (n + 2) i) := by
  simp only [Fin.ext_iff, val_zeroPort, val_retainPort, val_finRotate]
  split_ifs <;> omega

/-- An assignment with zero difference at `i` is exactly the expansion of its retained ports. -/
theorem comp_retainPort_zeroPort {n : ℕ} (i : Fin (n + 2)) (x : Fin (n + 2) → Bool)
    (h : cyclicDifference x i = false) : (x ∘ retainPort i) ∘ zeroPort i = x := by
  have he : x i = x (finRotate (n + 2) i) := by
    change (x i ^^ x (finRotate (n + 2) i)) = false at h
    cases ha : x i <;> cases hb : x (finRotate (n + 2) i) <;>
      simp_all only [Bool.false_xor, Bool.true_xor, Bool.not_true, Bool.not_false,
        Bool.true_eq_false, eq_self]
  funext j
  rcases retainPort_zeroPort i j with hj | ⟨rfl, hj⟩ | ⟨rfl, hj⟩
  · exact congrArg x hj
  · exact (congrArg x hj).trans he
  · exact (congrArg x hj).trans he.symm

/-- Adjacent equality restriction followed by deletion of the redundant port. -/
@[expose] def zeroRestriction {n : ℕ} (i : Fin (n + 2))
    (P : Set (Fin (n + 2) → Bool)) : Set (Fin (n + 1) → Bool) :=
  {y | y ∘ zeroPort i ∈ P}

instance {n : ℕ} (i : Fin (n + 2)) (P : Set (Fin (n + 2) → Bool))
    [DecidablePred (· ∈ P)] : DecidablePred (· ∈ zeroRestriction i P) := fun y =>
  inferInstanceAs (Decidable (y ∘ zeroPort i ∈ P))

/-- Exact difference semantics of adjacent identification, including deletion of the last edge.
The deleted coordinate must be zero; this is conditioned restriction, not plain projection. -/
theorem mem_cyclicDifferenceRelation_zeroRestriction {n : ℕ} (i : Fin (n + 2))
    (P : Set (Fin (n + 2) → Bool)) (d : Fin (n + 1) → Bool) :
    d ∈ cyclicDifferenceRelation (zeroRestriction i P) ↔
      ∃ s ∈ cyclicDifferenceRelation P, s i = false ∧ s ∘ differencePort i = d := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨cyclicDifference (y ∘ zeroPort i), ⟨_, hy, rfl⟩,
      cyclicDifference_zeroPort i y, cyclicDifference_zeroPort_differencePort i y⟩
  · rintro ⟨s, ⟨x, hx, rfl⟩, hi, hd⟩
    refine ⟨x ∘ retainPort i, ?_, ?_⟩
    · change (x ∘ retainPort i) ∘ zeroPort i ∈ P
      rwa [comp_retainPort_zeroPort i x hi]
    · rw [← hd, ← cyclicDifference_zeroPort_differencePort i (x ∘ retainPort i),
        comp_retainPort_zeroPort i x hi]

/-- Old port 0 is retained as free port 0. -/
@[simp] theorem capPort_zero (n : ℕ) : @capPort n 0 = Sum.inl 0 := by
  simp [capPort]

/-- Old port 1 is retained as free port 1. -/
@[simp] theorem capPort_one (n : ℕ) : @capPort n 1 = Sum.inl 1 := by
  simp [capPort]

/-- Old port 2 becomes the fresh hidden port. -/
@[simp] theorem capPort_two (n : ℕ) : @capPort n 2 = Sum.inr 0 := by
  simp [capPort]

/-- Old port 3 is identified with free port 1. -/
@[simp] theorem capPort_three (n : ℕ) : @capPort n 3 = Sum.inl 1 := by
  simp [capPort, Nat.mod_eq_of_lt (by omega : 3 < n + 4)]

/-- Old ports from 4 onward retain their order, shifted down by two. -/
theorem capPort_of_four_le {n : ℕ} (j : Fin (n + 4)) (h : 4 ≤ j.val) :
    capPort j = Sum.inl ⟨j.val - 2, by omega⟩ := by
  have h2 : j.val ≠ 2 := by omega
  have h3 : j.val ≠ 3 := by omega
  have hlt : ¬j.val < 2 := by omega
  simp only [capPort, h2, h3, hlt, ite_false, dite_false]

/-- Retained difference edges start at the corresponding new free ports of a cap. -/
theorem capPort_capDifferencePort {n : ℕ} (j : Fin (n + 2)) :
    capPort (capDifferencePort j) = Sum.inl j := by
  by_cases h0 : j.val = 0
  · have hj : j = 0 := Fin.ext h0
    subst j
    exact capPort_zero n
  by_cases h1 : j.val = 1
  · have hj : j = 1 := Fin.ext h1
    subst j
    exact capPort_three n
  simp only [capDifferencePort, h0, ite_false]
  rw [capPort_of_four_le _ (by change 4 ≤ j.val + 2; omega)]
  apply congrArg Sum.inl
  exact Fin.ext (by dsimp only; omega)

/-- Retained difference edges end at the corresponding cyclic successors after a cap. -/
theorem capPort_next_capDifferencePort {n : ℕ} (j : Fin (n + 2)) :
    capPort (finRotate (n + 4) (capDifferencePort j)) =
      Sum.inl (finRotate (n + 2) j) := by
  by_cases h0 : j.val = 0
  · have hj : j = 0 := Fin.ext h0
    subst j
    have he : @capDifferencePort n 0 = 0 := rfl
    rw [he, finRotate_apply_zero, finRotate_apply_zero]
    exact capPort_one n
  by_cases hlast : j.val = n + 1
  · have he : capDifferencePort j = Fin.last (n + 3) := by
      apply Fin.ext
      simp only [capDifferencePort, h0, ite_false, Fin.val_mk, Fin.val_last]
      omega
    have hj : j = Fin.last (n + 1) := Fin.ext hlast
    rw [he, hj, finRotate_last, finRotate_last]
    exact capPort_zero n
  have hlt : j.val < n + 1 := by omega
  have he : finRotate (n + 4) (capDifferencePort j) =
      (⟨j.val + 3, by omega⟩ : Fin (n + 4)) := by
    apply Fin.ext
    simp only [val_finRotate, capDifferencePort, h0, ite_false]
    split_ifs <;> omega
  rw [he, capPort_of_four_le _ (by change 4 ≤ j.val + 3; omega)]
  apply congrArg Sum.inl
  apply Fin.ext
  rw [val_finRotate]
  dsimp only
  split_ifs <;> omega

/-- The cap retains precisely the differences in order `0,3,4,…`. -/
theorem cyclicDifference_capPort {n : ℕ} (y : Fin (n + 2) → Bool) (z : Fin 1 → Bool) :
    cyclicDifference ((Sum.elim y z) ∘ capPort) ∘ capDifferencePort =
      cyclicDifference y := by
  funext j
  simp only [cyclicDifference, Function.comp_apply, capPort_capDifferencePort,
    capPort_next_capDifferencePort, Sum.elim_inl]

/-- A cap imposes equality of old differences 1 and 2. -/
theorem cyclicDifference_capPort_pair {n : ℕ} (y : Fin (n + 2) → Bool)
    (z : Fin 1 → Bool) :
    cyclicDifference ((Sum.elim y z) ∘ capPort) 1 =
      cyclicDifference ((Sum.elim y z) ∘ capPort) 2 := by
  change (y 1 ^^ z 0) = (z 0 ^^ y 1)
  exact Bool.xor_comm _ _

/-- Equality of adjacent differences is equality of the two outside ports. -/
theorem cyclicDifference_pair_eq_iff {n : ℕ} (x : Fin (n + 4) → Bool) :
    cyclicDifference x 1 = cyclicDifference x 2 ↔ x 1 = x 3 := by
  change (x 1 ^^ x 2) = (x 2 ^^ x 3) ↔ _
  cases x 1 <;> cases x 2 <;> cases x 3 <;> decide

/-- Reconstruct an old assignment from its retained and hidden cap ports. -/
theorem comp_capRetainPort_capPort {n : ℕ} (x : Fin (n + 4) → Bool)
    (h : x 1 = x 3) :
    (Sum.elim (x ∘ capRetainPort) (fun _ : Fin 1 => x 2)) ∘ capPort = x := by
  funext j
  by_cases h2 : j.val = 2
  · have hj : j = 2 := Fin.ext h2
    subst j
    rfl
  by_cases h3 : j.val = 3
  · have hj : j = 3 := Fin.ext h3
    subst j
    exact h
  by_cases hlt : j.val < 2
  · simp only [Function.comp_apply, capPort, h2, ite_false, hlt, dite_true,
      Sum.elim_inl, capRetainPort]
  · simp only [Function.comp_apply, capPort, h2, ite_false, hlt, dite_false,
      h3, Sum.elim_inl, capRetainPort]
    split_ifs <;> exact congrArg x (by apply Fin.ext; dsimp only; omega)

/-- Identify old ports 1 and 3, hide old port 2, and retain the other free ports in order. -/
@[expose] def capRelation {n : ℕ} (P : Set (Fin (n + 4) → Bool)) :
    Set (Fin (n + 2) → Bool) :=
  {y | ∃ z : Fin 1 → Bool, (Sum.elim y z) ∘ capPort ∈ P}

instance {n : ℕ} (P : Set (Fin (n + 4) → Bool)) [DecidablePred (· ∈ P)] :
    DecidablePred (· ∈ capRelation P) := fun y =>
  inferInstanceAs (Decidable (∃ z : Fin 1 → Bool, (Sum.elim y z) ∘ capPort ∈ P))

/-- Exact two-difference cap semantics. Both inclusions account for the hidden witness. -/
theorem mem_cyclicDifferenceRelation_capRelation {n : ℕ}
    (P : Set (Fin (n + 4) → Bool)) (d : Fin (n + 2) → Bool) :
    d ∈ cyclicDifferenceRelation (capRelation P) ↔
      ∃ s ∈ cyclicDifferenceRelation P, s 1 = s 2 ∧ s ∘ capDifferencePort = d := by
  constructor
  · rintro ⟨y, ⟨z, hz⟩, rfl⟩
    exact ⟨cyclicDifference ((Sum.elim y z) ∘ capPort), ⟨_, hz, rfl⟩,
      cyclicDifference_capPort_pair y z, cyclicDifference_capPort y z⟩
  · rintro ⟨s, ⟨x, hx, rfl⟩, hi, hd⟩
    have he := comp_capRetainPort_capPort x ((cyclicDifference_pair_eq_iff x).mp hi)
    refine ⟨x ∘ capRetainPort, ⟨fun _ => x 2, ?_⟩, ?_⟩
    · change (Sum.elim (x ∘ capRetainPort) (fun _ : Fin 1 => x 2)) ∘ capPort ∈ P
      rwa [he]
    · rw [← hd, ← cyclicDifference_capPort (x ∘ capRetainPort) (fun _ => x 2), he]

/-- The retained difference map is the standard increasing embedding omitting `i`. -/
theorem differencePort_eq_succAbove {n : ℕ} (i : Fin (n + 2)) :
    differencePort i = i.succAbove := rfl

/-- Deleting an edge other than 0 leaves the distinguished difference at 0. -/
@[simp] theorem differencePort_zero {n : ℕ} (i : Fin (n + 2)) (hi : i ≠ 0) :
    differencePort i 0 = 0 := by
  rw [differencePort_eq_succAbove, Fin.succAbove_of_castSucc_lt]
  · rfl
  · change (0 : Fin (n + 2)) < i
    exact Fin.pos_iff_ne_zero.mpr hi

/-- A pair containing difference 0 has exactly the same pair as its zero-conditioned lift. -/
theorem eq_pair_of_zero_restriction {n : ℕ} (i : Fin (n + 2)) (hi : i ≠ 0)
    (j : Fin (n + 1)) (s : Fin (n + 2) → Bool) (hs : s i = false)
    (hd : s ∘ differencePort i = flipOn {0, j} (fun _ => false)) :
    s = flipOn {0, differencePort i j} (fun _ => false) := by
  have hz := differencePort_zero i hi
  funext k
  induction k using i.succAboveCases with
  | x =>
    have hne : i ≠ differencePort i j := Fin.ne_succAbove i j
    simp only [hs, flipOn, Finset.mem_insert, Finset.mem_singleton, hi, hne,
      false_or, ite_false]
  | p l =>
    have he := congrFun hd l
    have h0 : i.succAbove l = 0 ↔ l = 0 := by
      rw [← hz]
      exact Fin.succAbove_right_injective.eq_iff
    simpa [differencePort, flipOn, h0, Fin.succAbove_right_injective.eq_iff] using he

private theorem val_capDifferencePort {n : ℕ} (j : Fin (n + 2)) :
    (capDifferencePort j).val = if j.val = 0 then 0 else j.val + 2 := by
  unfold capDifferencePort
  split_ifs <;> rfl

/-- The cap's retained differences are distinct. -/
theorem capDifferencePort_injective {n : ℕ} :
    Function.Injective (@capDifferencePort n) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [val_capDifferencePort] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega

/-- Exactly differences 1 and 2 are hidden by the cap. -/
theorem exists_capDifferencePort {n : ℕ} (k : Fin (n + 4))
    (h1 : k ≠ 1) (h2 : k ≠ 2) : ∃ j, capDifferencePort j = k := by
  by_cases h0 : k.val = 0
  · exact ⟨0, Fin.ext h0.symm⟩
  have hk1 : k.val ≠ 1 := fun h => h1 (Fin.ext h)
  have hk2 : k.val ≠ 2 := fun h => h2 (Fin.ext h)
  refine ⟨⟨k.val - 2, by omega⟩, ?_⟩
  apply Fin.ext
  simp only [val_capDifferencePort]
  split_ifs <;> omega

/-- A pair after the cap lifts to exactly the old pair or the old quartet. -/
theorem eq_pair_or_quartet_of_cap {n : ℕ} (j : Fin (n + 2)) (hj : j ≠ 0)
    (s : Fin (n + 4) → Bool) (hs : s 1 = s 2)
    (hd : s ∘ capDifferencePort = flipOn {0, j} (fun _ => false)) :
    s = flipOn {0, capDifferencePort j} (fun _ => false) ∨
      s = flipOn {0, 1, 2, capDifferencePort j} (fun _ => false) := by
  have h0 : capDifferencePort j ≠ 0 := by
    intro h
    apply hj
    exact capDifferencePort_injective h
  have h1 : capDifferencePort j ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [val_capDifferencePort] at hv
    simp only [Fin.val_one] at hv
    split_ifs at hv; omega
  have h2 : capDifferencePort j ≠ 2 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [val_capDifferencePort] at hv
    have ht : (2 : Fin (n + 4)).val = 2 := by
      change 2 % (n + 4) = 2
      exact Nat.mod_eq_of_lt (by omega)
    rw [ht] at hv
    split_ifs at hv; omega
  have he (k : Fin (n + 4)) (hk1 : k ≠ 1) (hk2 : k ≠ 2) :
      s k = flipOn {0, capDifferencePort j} (fun _ => false) k := by
    obtain ⟨l, rfl⟩ := exists_capDifferencePort k hk1 hk2
    have hb := congrFun hd l
    have hz : capDifferencePort l = 0 ↔ l = 0 := by
      change capDifferencePort l = capDifferencePort 0 ↔ l = 0
      exact capDifferencePort_injective.eq_iff
    simpa [flipOn, hz, capDifferencePort_injective.eq_iff] using hb
  cases hb : s 1 with
  | false =>
    left
    funext k
    by_cases hk1 : k = 1
    · subst k
      simp [flipOn, hb, Ne.symm h1]
    by_cases hk2 : k = 2
    · subst k
      simp [flipOn, ← hs, hb, Ne.symm h2, Fin.ext_iff,
        Nat.mod_eq_of_lt (by omega : 2 < n + 4)]
    exact he k hk1 hk2
  | true =>
    right
    funext k
    by_cases hk1 : k = 1
    · subst k
      simp [flipOn, hb]
    by_cases hk2 : k = 2
    · subst k
      simp [flipOn, ← hs, hb]
    simpa [flipOn, hk1, hk2] using he k hk1 hk2

/-- Cyclic translation commutes with cyclic differences; orientation is preserved. -/
theorem cyclicDifference_comp_finCycle {n : ℕ} (e : Fin n) (x : Fin n → Bool) :
    cyclicDifference (x ∘ finCycle e) = cyclicDifference x ∘ finCycle e := by
  have := e.neZero
  funext i
  simp only [cyclicDifference, Function.comp_apply, finCycle_apply, finRotate_apply]
  congr 1
  congr 1
  exact add_right_comm i 1 e

/-- Cyclic translation by the inverse shift also commutes with cyclic differences. -/
theorem cyclicDifference_comp_finCycle_symm {n : ℕ} (e : Fin n) (x : Fin n → Bool) :
    cyclicDifference (x ∘ (finCycle e).symm) =
      cyclicDifference x ∘ (finCycle e).symm := by
  have := e.neZero
  funext i
  simp only [cyclicDifference, Function.comp_apply, finCycle_symm_apply, finRotate_apply]
  congr 1
  congr 1
  exact add_sub_right_comm i 1 e

end Cslib.BitString
