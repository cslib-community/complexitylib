/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import CslibFrontier.Foundations.Data.BitString.DeltaMatroid.Operations

/-! # Delta-matroid edge cases and API clients

The tests distinguish nonemptiness, one-sided exchange and common parity of either value.
The final clients exercise transport, feasible connectivity and the four-coordinate alternatives.
-/

namespace CslibFrontierTests.DeltaMatroid

open Cslib Cslib.BitString Finset

example : IsEvenDeltaMatroid ({![true, false, false]} : Set (Fin 3 → Bool)) :=
  isEvenDeltaMatroid_singleton _

example : ¬ IsDeltaMatroid (∅ : Set (Fin 0 → Bool)) := not_isDeltaMatroid_empty

example : IsDeltaMatroid (Set.univ : Set (Fin 1 → Bool)) := isDeltaMatroid_univ

example : ¬ IsEvenDeltaMatroid (Set.univ : Set (Fin 1 → Bool)) := by
  intro h
  have hp := h.parity_eq (x := fun _ => false) (y := fun _ => true)
    (Set.mem_univ _) (Set.mem_univ _)
  revert hp
  decide

example : ¬ IsDeltaMatroid ({![false, false, false], ![true, true, true]} :
    Set (Fin 3 → Bool)) := by
  intro h
  have he := h.exchange (x := ![false, false, false]) (y := ![true, true, true])
    (by simp) (by simp) (i := 0) (by decide)
  revert he
  decide

example (b : Bool) : IsEvenDeltaMatroid {x : Fin 3 → Bool | parityOn univ x = b} := by
  apply isEvenDeltaMatroid_parityOn_fiber
  cases b
  · exact ⟨![false, false, false], by decide⟩
  · exact ⟨![true, false, false], by decide⟩

-- Exactly one true coordinate is even as a relation, although every tuple has odd parity.
example : IsEvenDeltaMatroid {x : Fin 3 → Bool | ∃! i, x i = true} := by
  constructor
  · constructor <;> simp only [Set.Nonempty, Set.mem_ofPred_eq, ExistsUnique] <;> decide
  · simp only [Set.mem_ofPred_eq, ExistsUnique]
    decide

example : ∀ x : Fin 3 → Bool, (∃! i, x i = true) → parityOn univ x = true := by
  simp only [ExistsUnique]
  decide

example : ¬ IsEvenDeltaMatroid {x : Fin 0 → Bool | ∃! i, x i = true} := by
  intro h
  obtain ⟨x, i, _⟩ := h.isDeltaMatroid.nonempty
  exact Fin.elim0 i

example : ¬ ∃ x : Fin 0 → Bool, parityOn univ x = true := by decide

example : IsEvenDeltaMatroid {x : Fin 0 → Bool | parityOn univ x = false} :=
  isEvenDeltaMatroid_parityOn_fiber false ⟨fun _ => false, by decide⟩

-- The two parity classes are exchanged by an odd twist.
example : parityOn univ (flipOn {0} (![false, false, false] : Fin 3 → Bool)) = true ∧
    parityOn univ (flipOn {0, 1} (![false, false, false] : Fin 3 → Bool)) = false := by
  decide

-- A concrete relation satisfying the forbidden-cross-pair hypotheses of the first consequence.
private abbrev paired : Set (Fin 4 → Bool) := {x | x 0 = x 1 ∧ x 2 = x 3}

private theorem paired_even : IsEvenDeltaMatroid paired := by
  constructor
  · constructor <;> simp only [Set.Nonempty, Set.mem_ofPred_eq] <;> decide
  · simp only [Set.mem_ofPred_eq]
    decide

example : flipOn {0, 1, 2, 3} (fun _ : Fin 4 => false) ∈ paired :=
  paired_even.mem_flipOn_four_of_not_mem_cross (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

example : flipOn {0, 2} (fun _ : Fin 4 => false) ∉ paired ∧
    flipOn {0, 3} (fun _ : Fin 4 => false) ∉ paired := by decide

example : hammingDist (flipOn {0, 1} (![false, false, false] : Fin 3 → Bool))
      ![true, true, false] + 2 = hammingDist (![false, false, false] : Fin 3 → Bool)
      ![true, true, false] :=
  hammingDist_flipOn_pair_add_two (by decide) (by decide) (by decide)

example {R : Set (Fin 4 → Bool)} (h : IsEvenDeltaMatroid R) (S : Finset (Fin 4))
    (e : Fin 4 ≃ Fin 4) :
    IsEvenDeltaMatroid {y | flipOn S (fun i => y (e i)) ∈ R} :=
  (h.twist S).reindex e

example {R : Set (Fin 4 → Bool)} (h : IsEvenDeltaMatroid R)
    {x y : Fin 4 → Bool} (hx : x ∈ R) (hy : y ∈ R) :
    Relation.ReflTransGen (fun u v => u ∈ R ∧ v ∈ R ∧
      ∃ i j, i ≠ j ∧ v = flipOn {i, j} u) x y := h.connected hx hy

example {R : Set (Fin 4 → Bool)} (h : IsEvenDeltaMatroid R) {x : Fin 4 → Bool}
    (h01 : flipOn {0, 1} x ∈ R) (h23 : flipOn {2, 3} x ∈ R)
    (h02 : flipOn {0, 2} x ∉ R) (h03 : flipOn {0, 3} x ∉ R) :
    flipOn {0, 1, 2, 3} x ∈ R :=
  h.mem_flipOn_four_of_not_mem_cross (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) h01 h23 h02 h03

example {R : Set (Fin 4 → Bool)} (h : IsEvenDeltaMatroid R) {x : Fin 4 → Bool}
    (hx : x ∈ R) (hf : flipOn {0, 1, 2, 3} x ∈ R) :
    flipOn {2, 3} x ∈ R ∨ flipOn {0, 2} x ∈ R ∨ flipOn {0, 3} x ∈ R :=
  h.mem_pair_or_mem_cross_of_mem_flipOn_four (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hx hf

end CslibFrontierTests.DeltaMatroid
