/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Fusion.Converse

/-!
# Semi-ultrafilter converse clients

The cases include no primary or auxiliary inputs, empty and full targets, the fixed empty
rejection on an empty carrier, a rejected self-pair, simultaneous acceptance of complementary
sets, and a nonconstant XOR function with a one-pair cover and a five-AND universal verifier.
-/

namespace ComplexityTests.FusionConverse

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Fusion PairCertificate

-- The fixed empty slot invalidates every certificate on an empty carrier, even with no pairs.
example : Invalid ([] : List (Set (Fin 0) × Set (Fin 0))) (fun _ : Fin 0 => ∅)
    Fin.elim0 Fin.elim0 := by
  refine ⟨none, rfl, Or.inr (Or.inl ⟨none, ?_, rfl⟩)⟩
  ext i
  exact i.elim0

-- Equal rejected indices must be checked: a rejected universe fails against itself.
example : Invalid ([(Set.univ, ∅)] : List (Set Bool × Set Bool)) (fun _ : Fin 0 => ∅)
    Fin.elim0 (fun _ => false) := by
  refine ⟨some (left _ 0), rfl, Or.inr (Or.inl ⟨some (left _ 0), ?_, rfl⟩)⟩
  simp

private def nonemptyFilter : Semifilter Bool :=
  Semifilter.ofRejected {∅} (by simp) (by
    simpa only [Set.mem_singleton_iff, forall_eq, Set.union_empty] using
      (Set.empty_ne_univ : (∅ : Set Bool) ≠ Set.univ))

example : nonemptyFilter.IsUltra := Semifilter.isUltra_ofRejected _ _ _

-- Semi-ultrafilters may accept both sides of a complementary pair.
example : nonemptyFilter {true} ∧ nonemptyFilter {false} := by
  change (∀ t ∈ ({∅} : Set (Set Bool)), ¬ ({true} : Set Bool) ⊆ t) ∧
    (∀ t ∈ ({∅} : Set (Set Bool)), ¬ ({false} : Set Bool) ⊆ t)
  simp

private def emptyCover : PairCover {_x : BitString 0 | false = true}
    (fun i => {x | AltFormula.literals x i = true}) Semifilter.IsUltra where
  pairs := []
  isCover w := (Bool.false_ne_true w.point.property).elim

private def fullCover : PairCover {_x : BitString 0 | true = true}
    (fun i => {x | AltFormula.literals x i = true}) Semifilter.IsUltra where
  pairs := []
  isCover w _ := w.filter.not_apply_empty (w.filter.monotone
    (fun x _ => (x.property rfl).elim) w.filter.apply_univ)

example : ∃ g : BooleanFunction 0, ∃ c : Circuit Monotone.signature 0 1,
    forallGuess (n := 0) (p := 0) g = (fun _ => false) ∧
      c.ComputesFrom Monotone.interpretation (single g) AltFormula.literals ∧
      c.program.cost Monotone.andCost = 0 :=
  emptyCover.exists_forallGuess (fun _ => false)

example : ∃ g : BooleanFunction 0, ∃ c : Circuit Monotone.signature 0 1,
    forallGuess (n := 0) (p := 0) g = (fun _ => true) ∧
      c.ComputesFrom Monotone.interpretation (single g) AltFormula.literals ∧
      c.program.cost Monotone.andCost = 0 :=
  fullCover.exists_forallGuess (fun _ => true)

private def xorCircuit : Circuit Monotone.signature 4 1 :=
  ⟨(((Program.empty : Program Monotone.signature 4 0).gate ⟨.or, ![.input 0, .input 1]⟩).gate
    ⟨.or, ![.input 2, .input 3]⟩).gate ⟨.and, ![.gate 0, .gate 1]⟩, fun _ => .gate 2⟩

private def xorVerifier : BooleanFunction (2 + 0) := fun x => x 0 ^^ x 1

private theorem xor_computes : xorCircuit.ComputesFrom Monotone.interpretation
    (single xorVerifier) AltFormula.literals := by
  unfold Circuit.ComputesFrom
  decide

-- A nonconstant target has an actual cover, so the converse's input is satisfiable.
example : ∃ a, ∃ g : BooleanFunction (2 + a),
    ∃ c : Circuit Monotone.signature ((2 + a) + (2 + a)) 1,
    forallGuess g = (fun x => x 0 ^^ x 1) ∧
      c.ComputesFrom Monotone.interpretation (single g) AltFormula.literals ∧
      c.program.cost Monotone.andCost = 5 ∧ a = 3 := by
  obtain ⟨cover, hcover⟩ := exists_pairCover_forallGuess xorVerifier xorCircuit xor_computes
  have hc : cover.pairs.length = 1 := hcover
  have hquant : forallGuess xorVerifier = (fun x => x 0 ^^ x 1) := by decide
  obtain ⟨g, c, hg, hcomputes, hcost⟩ := cover.exists_forallGuess (forallGuess xorVerifier)
  exact ⟨size cover.pairs, g, c, hg.trans hquant, hcomputes, by simpa [hc] using hcost,
    by simp [size, hc]⟩

example : econondeterministicAndComplexity (fun x : BitString 2 => x 0 ^^ x 1) ≤ 1 := by
  exact econondeterministicAndComplexity_le_cost xorVerifier (by decide) xorCircuit xor_computes

end ComplexityTests.FusionConverse
