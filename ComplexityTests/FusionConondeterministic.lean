/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Fusion.Conondeterministic

/-!
# Universally quantified Fusion clients

The verifier computes the exclusive-or of two primary inputs, OR the guessed bit. Universal
quantification removes the guessed bit. This checks an auxiliary input that affects the verifier,
with exactly one AND gate, and a separate zero-auxiliary instance.
-/

namespace ComplexityTests.FusionConondeterministic

open Cslib Cslib.Circuits Cslib.Circuits.Fusion Cslib.Circuits.Boolean

private def verifier : BooleanFunction (2 + 1) := fun x => (x 0 ^^ x 1) || x 2

private def circuit : Circuit Monotone.signature ((2 + 1) + (2 + 1)) 1 :=
  ⟨(((((Program.empty : Program Monotone.signature 6 0).gate ⟨.or, ![.input 0, .input 1]⟩).gate
    ⟨.or, ![.input 3, .input 4]⟩).gate ⟨.and, ![.gate 0, .gate 1]⟩).gate
    ⟨.or, ![.gate 2, .input 2]⟩), fun _ => .gate 3⟩

private theorem computes : circuit.ComputesFrom Monotone.interpretation
    (single verifier) AltFormula.literals := by
  unfold Circuit.ComputesFrom
  decide

example : forallGuess verifier = fun x => x 0 ^^ x 1 := by decide

private theorem cost : circuit.program.cost Monotone.andCost = 1 := by decide

example : ∃ cover : PairCover {x | forallGuess verifier x = true}
    (fun i => {x | AltFormula.literals x i = true}) Semifilter.IsUltra,
    cover.pairs.length = 1 := by
  simpa only [cost] using exists_pairCover_forallGuess verifier circuit computes

private def zeroInput : ↥({x | forallGuess verifier x = true}ᶜ) :=
  ⟨![false, false], by decide⟩

private def oneInput : ↥({x | forallGuess verifier x = true}ᶜ) :=
  ⟨![true, true], by decide⟩

private def twoPointFilter : Semifilter ↥({x | forallGuess verifier x = true}ᶜ) where
  toFun s := zeroInput ∈ s ∨ oneInput ∈ s
  monotone' _ _ h := Or.imp (fun hs => h hs) (fun hs => h hs)
  map_top' := propext ⟨fun _ => trivial, fun _ => Or.inl trivial⟩
  map_bot' := propext ⟨fun h => h.elim id id, False.elim⟩

private theorem twoPointFilter_ultra : twoPointFilter.IsUltra := by
  classical
  intro s
  by_cases h : zeroInput ∈ s
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inl h)

-- The target and admissible witness class are nonempty, forcing at least one AND pair.
private def verifierWitness : SemifilterWitness {x | forallGuess verifier x = true}
    (fun i => {x | AltFormula.literals x i = true}) Semifilter.IsUltra :=
  ⟨⟨![false, true], by decide⟩, twoPointFilter, twoPointFilter_ultra, by
    change ∀ i, AltFormula.literals ![false, true] i = true →
      AltFormula.literals ![false, false] i = true ∨ AltFormula.literals ![true, true] i = true
    decide⟩

example : pairCoverComplexity {x | forallGuess verifier x = true}
    (fun i => {x | AltFormula.literals x i = true}) Semifilter.IsUltra = 1 := by
  apply le_antisymm
  · simpa only [cost, Nat.cast_one] using
      pairCoverComplexity_forallGuess_le_cost verifier circuit computes
  · refine le_pairCoverComplexity_iff.mpr fun c => ?_
    have hpos : 1 ≤ c.pairs.length := by
      by_contra h
      have hempty : c.pairs = [] := List.length_eq_zero_iff.mp (by omega)
      exact c.isCover verifierWitness (by simp [hempty])
    exact_mod_cast hpos

private def noGuess : BooleanFunction (1 + 0) := fun x => x 0

example : forallGuess noGuess = noGuess ∧
    pairCoverComplexity {x | forallGuess noGuess x = true}
      (fun i => {x | AltFormula.literals x i = true}) Semifilter.IsUltra = 0 := by
  refine ⟨by decide, le_antisymm ?_ zero_le⟩
  exact pairCoverComplexity_forallGuess_le_cost noGuess
    (Circuit.wiring Monotone.signature (fun _ : Fin 1 => (0 : Fin 2))) (by
      unfold Circuit.ComputesFrom
      decide)

end ComplexityTests.FusionConondeterministic
