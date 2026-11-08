/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.DeltaMatroid.Operations

/-!
# Counting disagreements using even delta-matroid exchange

A forbidden two-coordinate move at a feasible base tuple bounds disagreements on one set
of coordinates by disagreements on another. The proof uses one-sided exchange at a specified
coordinate and induction on Hamming distance; it requires neither simultaneous exchange nor
matching realizability. Common parity may be either even or odd.

## Main results

* `IsEvenDeltaMatroid.card_disagree_le`: a local counting bound from forbidden base moves.
-/

public section

namespace Cslib.BitString

open Finset

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
    {R : Set (ι → Bool)} {x y : ι → Bool}

/-- If every feasible two-coordinate move from `x` entering `I` must also enter `O`, then
any feasible tuple disagrees with `x` on at most as many coordinates of `I` as of `O`.
The sets must be disjoint. This is a counting consequence of one-sided even exchange. -/
theorem IsEvenDeltaMatroid.card_disagree_le (hR : IsEvenDeltaMatroid R)
    (hx : x ∈ R) (hy : y ∈ R) (I O : Finset ι) (hIO : Disjoint I O)
    (hmove : ∀ i ∈ I, ∀ j ∉ O, j ≠ i → flipOn {i, j} x ∉ R) :
    (I.filter fun i => x i ≠ y i).card ≤ (O.filter fun i => x i ≠ y i).card := by
  generalize hn : hammingDist y x = n
  induction n using Nat.strong_induction_on generalizing y with
  | ind n ih =>
    by_cases hO : ∃ e ∈ O, x e ≠ y e
    · obtain ⟨e, heO, he⟩ := hO
      obtain ⟨j, hje, hj, hy'⟩ := hR.exchange hy hx (Ne.symm he)
      let y' := flipOn {e, j} y
      have hd := hammingDist_flipOn_pair_add_two hje.symm (Ne.symm he) hj
      have ht : hammingDist y' x < n := by dsimp only [y']; omega
      have hb := ih _ ht hy' rfl
      have heI : e ∉ I := fun heI => Finset.disjoint_left.mp hIO heI heO
      have hI : (I.filter fun i => x i ≠ y i) ⊆
          insert j (I.filter fun i => x i ≠ y' i) := by
        intro i hi
        obtain ⟨hiI, hi⟩ := mem_filter.mp hi
        by_cases hij : i = j
        · exact mem_insert.mpr (Or.inl hij)
        · have hie : i ≠ e := fun h => heI (h ▸ hiI)
          exact mem_insert_of_mem (mem_filter.mpr ⟨hiI, by
            simpa only [y', flipOn_apply, mem_insert, mem_singleton, hie, hij,
              or_self, ↓reduceIte] using hi⟩)
      have hO' : insert e (O.filter fun i => x i ≠ y' i) ⊆
          (O.filter fun i => x i ≠ y i) := by
        intro i hi
        rcases mem_insert.mp hi with rfl | hi
        · exact mem_filter.mpr ⟨heO, he⟩
        · obtain ⟨hiO, hi⟩ := mem_filter.mp hi
          refine mem_filter.mpr ⟨hiO, ?_⟩
          by_cases hie : i = e
          · exact hie ▸ he
          by_cases hij : i = j
          · exact hij ▸ Ne.symm hj
          · simpa only [y', flipOn_apply, mem_insert, mem_singleton, hie, hij,
              or_self, ↓reduceIte] using hi
      have hen : e ∉ O.filter (fun i => x i ≠ y' i) := by
        simp only [mem_filter, not_and]
        intro _
        dsimp only [y']
        rw [flipOn_apply_of_mem (mem_insert_self e {j})]
        cases hx : x e <;> cases hy : y e <;> simp_all
      have h₁ := (card_le_card hI).trans (card_insert_le j _)
      have h₂ := card_le_card hO'
      rw [card_insert_of_notMem hen] at h₂
      dsimp only [y'] at h₁ h₂
      omega
    · have hzero : I.filter (fun i => x i ≠ y i) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro i hi
        obtain ⟨hiI, hi⟩ := mem_filter.mp hi
        obtain ⟨j, hji, hj, hf⟩ := hR.exchange hx hy hi
        exact hmove i hiI j (fun hjO => hO ⟨j, hjO, hj⟩) hji hf
      rw [hzero, card_empty]
      exact Nat.zero_le _

end Cslib.BitString
