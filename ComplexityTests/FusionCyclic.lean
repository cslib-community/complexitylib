/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Fusion.Cyclic
import Mathlib.Tactic.FinCases

/-!
# Clients of cyclic circuit semantics and semifilter bounds

Unsupported feedback has empty least solution, even though other fixed points exist. A supported
feedback component computes an intersection and shares its outputs, while an unused self-loop
still contributes its AND cost. Explicit semifilter witnesses give a positive minimum-cost bound.
-/

namespace ComplexityTests.FusionCyclic

open Cslib.Circuits Fusion

private abbrev unsupported : CyclicCircuit Monotone.signature 0 1 :=
  ⟨![⟨.or, ![.gate 0, .gate 0]⟩], ![.gate 0]⟩

example {U : Type*} : unsupported.eval (Monotone.setInterpretation U)
    Monotone.setInterpretation_mono Fin.elim0 = ![∅] := by
  have h := unsupported.evalGates_le (Monotone.setInterpretation U)
    Monotone.setInterpretation_mono Fin.elim0 (state := ⊥)
    (by intro i; fin_cases i; exact Set.union_subset Set.Subset.rfl Set.Subset.rfl)
  have heq := le_antisymm h bot_le
  simp only [CyclicCircuit.eval, heq]
  funext i
  fin_cases i
  rfl

-- The full set is also a fixed point; solving arbitrary equations would give the wrong semantics.
example {U : Type*} : unsupported.step (Monotone.setInterpretation U)
    Monotone.setInterpretation_mono Fin.elim0 (fun _ => Set.univ) = fun _ => Set.univ := by
  funext i
  fin_cases i
  exact Set.union_self _

-- g₀ = A ∪ g₁; g₁ = B ∩ g₀; g₂ = g₂ ∩ g₂. The last component is unused.
private abbrev feedback : CyclicCircuit Monotone.signature 2 4 :=
  ⟨![⟨.or, ![.input 0, .gate 1]⟩, ⟨.and, ![.input 1, .gate 0]⟩,
      ⟨.and, ![.gate 2, .gate 2]⟩],
    ![.gate 1, .gate 0, .gate 1, .input 1]⟩

private theorem feedback_values {U : Type*} (A B : Set U) :
    feedback.evalGates (Monotone.setInterpretation U) Monotone.setInterpretation_mono ![A, B] =
      ![A, B ∩ A, ∅] := by
  let values := feedback.evalGates (Monotone.setInterpretation U)
    Monotone.setInterpretation_mono ![A, B]
  have h0 : A ∪ values 1 = values 0 :=
    feedback.evalGates_fixed _ Monotone.setInterpretation_mono ![A, B] 0
  have h1 : B ∩ values 0 = values 1 :=
    feedback.evalGates_fixed _ Monotone.setInterpretation_mono ![A, B] 1
  have hA : A ⊆ values 0 := by rw [← h0]; exact Set.subset_union_left
  apply le_antisymm
  · apply feedback.evalGates_le
    intro i
    fin_cases i
    · exact Set.union_subset Set.Subset.rfl Set.inter_subset_right
    · exact Set.Subset.rfl
    · exact Set.inter_subset_left
  · intro i
    fin_cases i
    · exact hA
    · change B ∩ A ⊆ values 1
      rw [← h1]
      exact Set.inter_subset_inter Set.Subset.rfl hA
    · exact Set.empty_subset _

private theorem feedback_eval {U : Type*} (A B : Set U) :
    feedback.eval (Monotone.setInterpretation U) Monotone.setInterpretation_mono ![A, B] =
      ![B ∩ A, A, B ∩ A, B] := by
  simp only [CyclicCircuit.eval, feedback_values]
  funext i
  fin_cases i <;> rfl

example {U : Type*} (A B : Set U) :
    feedback.cost Monotone.andCost = 2 ∧
      (PairCover.ofCyclicCircuit feedback ![A, B] 0
        (congrFun (feedback_eval A B) 0)).pairs.length = 2 := by
  refine ⟨by decide, ?_⟩
  rw [PairCover.length_ofCyclicCircuit]
  decide

example (weight : Monotone.Op → ℕ) :
    feedback.cost weight = weight .or + weight .and + weight .and := by
  simp [CyclicCircuit.cost, Fin.sum_univ_succ, Nat.add_assoc]

-- Input-only outputs and empty output tuples need no equations.
example {U : Type*} (A : Set U) :
    (Circuit.wiring Monotone.signature ![0, 0]).toCyclic.eval (Monotone.setInterpretation U)
      Monotone.setInterpretation_mono ![A] = ![A, A] := by
  simp only [Circuit.eval_toCyclic, Circuit.eval_wiring]
  funext i
  fin_cases i <;> rfl

example {U : Type*} (A : Set U) :
    (PairCover.ofCyclicCircuit (target := A)
      (Circuit.wiring Monotone.signature ![0]).toCyclic ![A] 0
      (by simp [Circuit.eval_wiring])).pairs.length = 0 := by
  simp

example : CyclicCircuit.ecomplexityFrom (Monotone.setInterpretation Empty)
    Monotone.setInterpretation_mono (fun _ => 1) (fun _ : Empty => Fin.elim0)
      (fun _ => Fin.elim0) = 0 := by
  apply le_antisymm _ zero_le
  exact CyclicCircuit.ecomplexityFrom_le_of_computesFrom
    (Circuit.wiring Monotone.signature (Fin.elim0 : Fin 0 → Fin 0)).toCyclic
    (fun x => x.elim)

private def nonemptySets {U : Type*} [Nonempty U] : Semifilter U where
  toFun s := s.Nonempty
  monotone' _ _ h hs := hs.mono h
  map_top' := by simp
  map_bot' := by simp

private abbrev inputs : Fin 2 → Set (Fin 2 → Bool) :=
  ![{x | x 0 = true}, {x | x 1 = true}]

private abbrev targets : Fin 4 → Set (Fin 2 → Bool) :=
  ![inputs 1 ∩ inputs 0, inputs 0, inputs 1 ∩ inputs 0, inputs 1]

private instance : Nonempty ↥((targets 0)ᶜ) := ⟨⟨![false, true], by simp [targets, inputs]⟩⟩

private def witness : SemifilterWitness (targets 0) inputs where
  point := ⟨![true, true], by simp [targets, inputs]⟩
  filter := nonemptySets
  admissible_filter := trivial
  above i _ := by
    fin_cases i
    · exact ⟨⟨![true, false], by simp [targets, inputs]⟩, rfl⟩
    · exact ⟨⟨![false, true], by simp [targets, inputs]⟩, rfl⟩

private theorem positive_cover (c : PairCover (targets 0) inputs) : 1 ≤ c.pairs.length := by
  by_contra h
  have hempty : c.pairs = [] := List.length_eq_zero_iff.mp (by lia)
  exact c.isCover witness (by simp only [hempty, List.not_mem_nil, false_implies, implies_true])

example (c : CyclicCircuit Monotone.signature 2 4)
    (hc : c.eval (Monotone.setInterpretation (Fin 2 → Bool))
      Monotone.setInterpretation_mono inputs 0 = targets 0) :
    c.cost Monotone.andCost ≠ 0 := by
  have h := pairCover_lowerBound_cyclic positive_cover c 0 hc
  omega

private def acyclic : Circuit Monotone.signature 2 4 :=
  ⟨(Program.empty : Program Monotone.signature 2 0).gate ⟨.and, ![.input 1, .input 0]⟩,
    ![.gate 0, .input 0, .gate 0, .input 1]⟩

example :
    CyclicCircuit.ecomplexityFrom (Monotone.setInterpretation (Fin 2 → Bool))
        Monotone.setInterpretation_mono Monotone.andCost
        (fun _ : Unit => targets) (fun _ => inputs) = 1 ∧
      CyclicCircuit.ecomplexityFrom (Monotone.setInterpretation (Fin 2 → Bool))
        Monotone.setInterpretation_mono (fun _ => 7)
        (fun _ : Unit => targets) (fun _ => inputs) ≤ 7 := by
  refine ⟨le_antisymm ?_ ?_,
    CyclicCircuit.ecomplexityFrom_le_acyclic.trans
      (ecomplexityFrom_le_of_computesFrom acyclic (fun _ => by funext i; fin_cases i <;> rfl))⟩
  · exact CyclicCircuit.ecomplexityFrom_le_of_computesFrom acyclic.toCyclic
      (fun _ => by simp only [Circuit.eval_toCyclic]; funext i; fin_cases i <;> rfl)
  · apply le_trans _ (pairCoverComplexity_le_cyclic_ecomplexityFrom
      (fun _ : Unit => inputs) (fun _ => targets) () 0)
    exact le_pairCoverComplexity_iff.mpr fun c => by exact_mod_cast positive_cover c

private abbrev constants : Circuit Monotone.signature 0 3 :=
  ⟨((Program.empty : Program Monotone.signature 0 0).gate ⟨.const false, Fin.elim0⟩).gate
    ⟨.const true, Fin.elim0⟩, ![.gate 1, .gate 0, .gate 1]⟩

private theorem constants_eval {U : Type*} :
    constants.toCyclic.eval (Monotone.setInterpretation U)
      Monotone.setInterpretation_mono Fin.elim0 = ![Set.univ, ∅, Set.univ] := by
  rw [Circuit.eval_toCyclic]
  funext i
  fin_cases i <;> rfl

example {U : Type*} :
    (PairCover.ofCyclicCircuit constants.toCyclic (Fin.elim0 : Fin 0 → Set U) 0
      (congrFun constants_eval 0)).pairs.length = 0 := by
  rw [PairCover.length_ofCyclicCircuit, Circuit.cost_toCyclic]
  decide

-- An impossible set construction has infinite cyclic complexity too.
private def negationWitness : SemifilterWitness {x : Bool | x = false}
    (fun _ : Fin 1 => {x | x = true}) where
  point := ⟨false, rfl⟩
  filter :=
    { toFun := fun s => (⟨true, by decide⟩ : ↥({x : Bool | x = false}ᶜ)) ∈ s
      monotone' := fun _ _ h hx => h hx
      map_top' := rfl
      map_bot' := rfl }
  admissible_filter := trivial
  above _ h := (Bool.false_ne_true h).elim

example : CyclicCircuit.ecomplexityFrom (Monotone.setInterpretation Bool)
    Monotone.setInterpretation_mono Monotone.andCost
      (fun _ : Unit => ![{x | x = false}]) (fun _ => ![{x | x = true}]) = ⊤ := by
  apply top_le_iff.mp
  apply le_trans _ (pairCoverComplexity_le_cyclic_ecomplexityFrom
    (fun _ : Unit => ![{x : Bool | x = true}]) (fun _ => ![{x | x = false}]) () 0)
  simp only [Matrix.cons_val_zero, Matrix.cons_fin_one]
  refine le_pairCoverComplexity_iff.mpr fun c => (c.isCover negationWitness ?_).elim
  exact fun _ _ ha hb => ⟨ha, hb⟩

private theorem bool_mono (op : Monotone.Op) : Monotone (Monotone.interpretation op) :=
  fun _ _ h => Monotone.interpretation_mono op h

-- This evaluates three concrete synchronous steps; no generic convergence claim is needed.
/-- info: [[false, false, false], [false, false, false], [true, false, false], [true, true, false]] -/
#guard_msgs in
#eval (List.ofFn fun i : Fin 4 =>
  let x : Fin 2 → Bool := ![i.val / 2 == 1, i.val % 2 == 1]
  List.ofFn ((feedback.step Monotone.interpretation bool_mono x)^[3] (fun _ => false)))

end ComplexityTests.FusionCyclic
