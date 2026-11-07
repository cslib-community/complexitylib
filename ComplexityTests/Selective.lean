/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Selective.Ko
import Complexity.Computability.Complexity.Classes.Selective.LeftCut
import Complexity.Computability.Complexity.Classes.Selective.Selman
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Foundations.Data.Finset.Tournament
import Complexity.Foundations.Data.List.Lex

/-!
# Tests for P-selective sets

Selectors that work and one that fails; left cuts (concrete members and non-members, the all-ones
sequence whose left cut is everything, the lexicographic minimum as an explicit selector, right
cuts, and polynomial-size circuits for every left cut); Selman's theorem as `P ≠ NP` ruling out a
selector for `SAT`; and a tournament that needs more than one dominating vertex.
-/

namespace Cslib.Complexity.Tests.Selective

open Cslib.Circuits.Boolean Cslib.Complexity Turing.MultiTapeTM

/-! ### Selectors -/

/-- The minimum selects for an initial segment of `ℕ`. -/
example : IsSelector {n : ℕ | n ≤ 5} min := fun x y =>
  ⟨min_choice x y, fun h => h.elim (fun hx => (min_le_left x y).trans hx)
    fun hy => (min_le_right x y).trans hy⟩

/-- Always picking the first argument is not a selector for `{1}`: it picks `0` over `1`. -/
example : ¬IsSelector ({1} : Set ℕ) fun x _ => x := fun h =>
  absurd (h.mem (x := 0) (y := 1) (.inr rfl)) (by simp)

/-- Problems in `P`, here the universal one, are P-selective. -/
example : (Set.univ : Set (List Bool)) ∈ PSel encBits := P_subset_PSel univ_mem_P

/-! ### Left cuts -/

/-- The sequence `0, 1, 0, 0, …`, the binary fraction `0.01 = 1/4`. -/
def quarter (i : ℕ) : Bool := i == 1

-- `01` and `00` are at most the prefix `01`; `1` and `011` are above the prefixes `0` and `010`.
example : [false, true] ∈ leftCut quarter ∧ [false, false] ∈ leftCut quarter ∧
    [true] ∉ leftCut quarter ∧ [false, true, true] ∉ leftCut quarter := by
  simp only [mem_leftCut]
  decide

/-- The left cut of the all-ones sequence `0.111… = 1` contains every bit string. -/
example : leftCut (fun _ => true) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  rw [mem_leftCut, List.map_const', List.length_range]
  induction x with
  | nil => exact le_rfl
  | cons a x ih =>
    rw [List.length_cons, List.replicate_succ, List.cons_le_cons_iff']
    cases a
    · exact .inl Bool.false_lt_true
    · exact .inr ⟨rfl, ih⟩

/-- The lexicographic minimum is an explicit selector for every left cut. -/
example (r : ℕ → Bool) : IsSelector (leftCut r) min := fun x y =>
  ⟨min_choice x y, fun h => h.elim (isLowerSet_leftCut r (min_le_left x y))
    (isLowerSet_leftCut r (min_le_right x y))⟩

/-- Right cuts, the complements of left cuts, are P-selective. -/
example (r : ℕ → Bool) : (leftCut r)ᶜ ∈ PSel encBits := compl_mem_PSel (leftCut_mem_PSel r)

/-- Every left cut, however hard the sequence, has polynomial-size circuits (Ko's theorem). -/
example (r : ℕ → Bool) : leftCut r ∈ PPolyOn encBits := PSel_subset_PPolyOn (leftCut_mem_PSel r)

/-! ### Selman's theorem -/

/-- If `P ≠ NP`, `SAT` is not P-selective. -/
example (h : P encCNF ≠ NP encCNF) : SAT ∉ PSel encCNF := fun hSAT =>
  h (NPHard.P_eq_NP_of_mem_PSel CookLevin.SAT_npHard hSAT encCNF)

/-! ### Tournaments -/

/-- The cyclic tournament on three vertices: `y` beats `x` when `y = x` or `y = x + 1`. -/
def cyclic (x y : Fin 3) : Prop := y = x ∨ y = x + 1

instance : DecidableRel cyclic := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

-- No single vertex dominates the cyclic tournament, but since `3 < 2 ^ 2`, two vertices do.
example : (∀ y : Fin 3, ∃ x, ¬cyclic x y) ∧
    ∃ S ⊆ (Finset.univ : Finset (Fin 3)), S.card ≤ 2 ∧ ∀ x ∈ Finset.univ, ∃ y ∈ S, cyclic x y :=
  ⟨by decide, Finset.exists_dominating_subset_of_card_lt_two_pow cyclic 2 _
    (fun x _ y _ => by revert x y; decide) (by decide)⟩

end Cslib.Complexity.Tests.Selective
