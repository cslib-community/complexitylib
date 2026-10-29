/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Fusion.Semifilter
import Mathlib.Tactic.FinCases

/-!
# Semifilter cover clients

Nonempty sets supply an ultra semifilter without intersection closure. A three-point problem
has exact AND complexity one, including with shared outputs. Cover extraction retains unused
AND gates and discards free constants and unions. Empty witness classes and an impossible
cover exercise the zero and infinite boundaries.
-/

namespace ComplexityTests.FusionSemifilter

open Cslib.Circuits Fusion

private def nonemptySets {U : Type*} [Nonempty U] : Semifilter U where
  toFun s := s.Nonempty
  monotone' _ _ h hs := hs.mono h
  map_top' := by simp
  map_bot' := by simp

private theorem nonemptySets_isUltra {U : Type*} [Nonempty U] :
    (nonemptySets : Semifilter U).IsUltra := by
  classical
  intro s
  by_cases h : s.Nonempty
  · exact Or.inl h
  · exact Or.inr ⟨Classical.arbitrary U, fun hx => h ⟨_, hx⟩⟩

-- Both complementary singletons are accepted, but their intersection is rejected.
example : nonemptySets {true} ∧ nonemptySets {false} ∧
    ¬ nonemptySets ({true} ∩ {false}) := by
  change ({true} : Set Bool).Nonempty ∧ ({false} : Set Bool).Nonempty ∧
    ¬ ({true} ∩ {false} : Set Bool).Nonempty
  simp

private theorem no_semifilter {U : Type*} [IsEmpty U] (F : Semifilter U) : False :=
  F.not_apply_empty ((show (Set.univ : Set U) = ∅ from
    Set.univ_eq_empty_iff.mpr inferInstance) ▸ F.apply_univ)

private abbrev target : Set (Fin 3) := {0}
private abbrev inputs : Fin 2 → Set (Fin 3) := ![{0, 1}, {0, 2}]

private instance : Nonempty ↥(targetᶜ) := ⟨⟨1, by decide⟩⟩

private def witness : SemifilterWitness target inputs Semifilter.IsUltra where
  point := ⟨0, by decide⟩
  filter := nonemptySets
  admissible_filter := nonemptySets_isUltra
  above i _ := by
    fin_cases i
    · exact ⟨⟨1, by decide⟩, Or.inr rfl⟩
    · exact ⟨⟨2, by decide⟩, Or.inr rfl⟩

private theorem positive_cover (c : PairCover target inputs Semifilter.IsUltra) :
    1 ≤ c.pairs.length := by
  by_contra h
  have hempty : c.pairs = [] := List.length_eq_zero_iff.mp (by lia)
  exact c.isCover witness (by simp [hempty])

private def intersect : Circuit Monotone.signature 2 3 :=
  ⟨(Program.empty : Program Monotone.signature 2 0).gate ⟨.and, ![.input 0, .input 1]⟩,
    ![.gate 0, .input 0, .gate 0]⟩

private theorem intersect_eval : intersect.eval (Monotone.setInterpretation (Fin 3)) inputs =
    ![target, inputs 0, target] := by
  have h : inputs 0 ∩ inputs 1 = target := by ext x; fin_cases x <;> simp
  funext i
  fin_cases i
  · exact h
  · rfl
  · exact h

private theorem exact_cover : pairCoverComplexity target inputs Semifilter.IsUltra = 1 := by
  apply le_antisymm
  · exact pairCoverComplexity_le_cost intersect inputs 0 (congrFun intersect_eval 0)
      Semifilter.IsUltra
  · exact le_pairCoverComplexity_iff.mpr fun c => by exact_mod_cast positive_cover c

-- A concrete admissible witness forces an AND gate, and one gate attains the bound.
example : ecomplexityFrom (Monotone.setInterpretation (Fin 3)) Monotone.andCost
    (fun _ : Unit => ![target, inputs 0, target]) (fun _ : Unit => inputs) = 1 := by
  apply le_antisymm (ecomplexityFrom_le_of_computesFrom intersect (fun _ => intersect_eval))
  change (1 : ℕ∞) ≤ _
  rw [← exact_cover]
  exact pairCoverComplexity_le_ecomplexityFrom (fun _ : Unit => inputs)
    (fun _ : Unit => ![target, inputs 0, target]) () 0 Semifilter.IsUltra

example (c : Circuit Monotone.signature 2 1)
    (hc : c.eval (Monotone.setInterpretation (Fin 3)) inputs 0 = target) :
    c.program.cost Monotone.andCost ≠ 0 := by
  have h := pairCover_lowerBound positive_cover c 0 hc
  omega

private def shared : Circuit Monotone.signature 2 4 :=
  ⟨((((((Program.empty : Program Monotone.signature 2 0).gate
    ⟨.const false, Fin.elim0⟩).gate ⟨.const true, Fin.elim0⟩).gate
    ⟨.or, ![.input 0, .gate 0]⟩).gate ⟨.and, ![.gate 2, .input 1]⟩).gate
    ⟨.or, ![.gate 3, .gate 0]⟩).gate ⟨.and, ![.gate 2, .input 1]⟩,
    ![.gate 4, .gate 4, .gate 3, .input 0]⟩

private theorem shared_eval : shared.eval (Monotone.setInterpretation (Fin 3)) inputs 0 =
    target := by
  change (inputs 0 ∪ ∅) ∩ inputs 1 ∪ ∅ = target
  ext x
  fin_cases x <;> simp

private def extracted : PairCover target inputs := PairCover.ofCircuit shared inputs 0 shared_eval

-- The same AND pair occurs twice, including the final unused gate; no free gate contributes.
example :
    extracted.pairs =
        [(Subtype.val ⁻¹' inputs 0, Subtype.val ⁻¹' inputs 1),
          (Subtype.val ⁻¹' inputs 0, Subtype.val ⁻¹' inputs 1)] ∧
      extracted.pairs.length = 2 := by
  refine ⟨?_, PairCover.length_ofCircuit _ _ _ _⟩
  change [((Subtype.val ⁻¹' (inputs 0 ∪ ∅)), Subtype.val ⁻¹' inputs 1),
    ((Subtype.val ⁻¹' (inputs 0 ∪ ∅)), Subtype.val ⁻¹' inputs 1)] = _
  simp

/-- info: (6, 2, 2) -/
#guard_msgs in
#eval (shared.size, shared.program.cost Monotone.andCost, extracted.pairs.length)

-- Empty targets cannot provide reference points, so the minimum cover cost is zero.
example {U : Type*} {n : ℕ} (input : Fin n → Set U) :
    pairCoverComplexity ∅ input = 0 := by
  apply le_antisymm _ zero_le
  exact pairCoverComplexity_le (target := ∅) (input := input)
    ⟨[], fun w _ => w.point.property.elim⟩

-- Full targets have empty complements, which admit no semifilter.
example {U : Type*} {n : ℕ} (input : Fin n → Set U) :
    pairCoverComplexity Set.univ input = 0 := by
  let : IsEmpty ↥((Set.univ : Set U)ᶜ) := ⟨fun x => x.property trivial⟩
  apply le_antisymm _ zero_le
  exact pairCoverComplexity_le ⟨[], fun w _ => no_semifilter w.filter⟩

example : pairCoverComplexity target inputs (fun _ => False) = 0 := by
  apply le_antisymm _ zero_le
  exact pairCoverComplexity_le ⟨[], fun w _ => w.admissible_filter⟩

-- With no inputs, a point observation outside the target preserves every pair.
private def pointFilter {U : Type*} (x : U) : Semifilter U where
  toFun s := x ∈ s
  monotone' _ _ h hx := h hx
  map_top' := rfl
  map_bot' := rfl

private def unopposed : SemifilterWitness target (Fin.elim0 : Fin 0 → Set (Fin 3)) where
  point := ⟨0, by decide⟩
  filter := pointFilter ⟨1, by decide⟩
  admissible_filter := trivial
  above i := i.elim0

private theorem unopposed_cover_top :
    pairCoverComplexity target (Fin.elim0 : Fin 0 → Set (Fin 3)) = ⊤ := by
  apply top_le_iff.mp
  refine le_pairCoverComplexity_iff.mpr fun c => (c.isCover unopposed ?_).elim
  exact fun _ _ ha hb => ⟨ha, hb⟩

-- An unopposed witness forces infinite circuit complexity for any output family with `target`.
example : ecomplexityFrom (Monotone.setInterpretation (Fin 3)) Monotone.andCost
    (fun _ : Unit => ![target]) (fun _ : Unit => (Fin.elim0 : Fin 0 → Set (Fin 3))) = ⊤ := by
  apply top_le_iff.mp
  rw [← unopposed_cover_top]
  exact pairCoverComplexity_le_ecomplexityFrom
    (fun _ : Unit => (Fin.elim0 : Fin 0 → Set (Fin 3)))
    (fun _ : Unit => ![target]) () 0 (fun _ => True)

end ComplexityTests.FusionSemifilter
