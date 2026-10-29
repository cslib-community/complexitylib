/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Iteration.SparseDisplacement
import Mathlib.Tactic.FinCases

/-!
# Sparse-counter circuit clients

Check zero-width words, wraparound cuts, an edited counter, negative powers, and charged
identity coordinates. A noninjective example shows why the factor-two theorem needs injectivity.
-/

namespace ComplexityTests.Iteration.SparseDisplacement

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Iteration
open Cslib.FunctionalGraph

-- At width zero there is one state and its displacement never changes; negation has displacement
-- changes at all four edges, including the wraparound edge.
example :
    displacementCuts (id : BitVec 0 → BitVec 0) = ∅ ∧
    displacementCuts (fun x : BitVec 2 => -x) = {0, 1, 2, 3} ∧
    thresholdSum (displacementCuts (fun x : BitVec 2 => -x))
      (fun i => displacement (fun x : BitVec 2 => -x) (BitVec.ofNat 2 (i + 1)) -
        displacement (fun x : BitVec 2 => -x) (BitVec.ofNat 2 i))
      (displacement (fun x : BitVec 2 => -x) 0) 3 = 2 := by
  decide

-- Swapping two counter inputs gives a permutation edited at exactly two successors.
private def editedCounter : Equiv.Perm (BitVec 2) :=
  (Equiv.swap 0 1).trans (Equiv.addRight 1)

private theorem editedCounter_disagreement [Fintype (BitVec 2)] :
    disagreement editedCounter (fun x => x + 1) = {0, 1} := by
  ext x
  simp only [mem_disagreement, Finset.mem_insert, Finset.mem_singleton]
  revert x
  decide

-- The same bound works for every signed exponent, including inverses.
example (T : ℤ) :
    (∃ out : Circuit signature 2 2,
      out.Computes interpretation (fun x i => ((editedCounter ^ T) (word x)).getLsbD i.val) ∧
      out.size ≤ 900) ∧
    (∃ out : Circuit signature 2 2,
      out.Computes interpretation (fun x i => (editedCounter.symm (word x)).getLsbD i.val) ∧
      out.size ≤ 900) := by
  have h1 := sparse_counter_power editedCounter T
  have h2 := sparse_counter_power editedCounter (-1)
  rw [editedCounter_disagreement] at h1 h2
  exact ⟨by simpa using h1, by simpa using h2⟩

-- Coordinate transfer is applicable to actual conversion circuits.
example (T : ℤ) : ∃ out : Circuit signature 2 2,
    out.Computes interpretation (fun x i => ((editedCounter ^ T) (word x)).getLsbD i.val) ∧
    out.size ≤ 900 := by
  have hid : (Circuit.id signature 2).Computes interpretation
      (fun x i => ((Equiv.refl (BitVec 2)) (word x)).getLsbD i.val) := by
    intro x
    funext i
    exact (getLsbD_word x i).symm
  have h := sparse_coordinate_power editedCounter (Equiv.addRight 1) (Equiv.refl _)
      (fun _ => rfl) (Circuit.id signature 2) (Circuit.id signature 2) hid hid T
  have hdiff : disagreement editedCounter (Equiv.addRight (1 : BitVec 2)) = {0, 1} :=
    editedCounter_disagreement
  rw [hdiff] at h
  simpa using h

-- Without injectivity one edited input can create four defects.
private def edit (x : Fin 4) : Fin 4 := if x = 0 then 1 else x

example :
    Function.Commute (fun _ : Fin 4 => 0) id ∧
    disagreement id edit = {0} ∧
    disagreement ((fun _ : Fin 4 => 0) ∘ edit) (edit ∘ (fun _ => 0)) = Finset.univ := by
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · ext x
    fin_cases x <;> simp [mem_disagreement, edit]
  · ext x
    simp [mem_disagreement, edit]

end ComplexityTests.Iteration.SparseDisplacement
