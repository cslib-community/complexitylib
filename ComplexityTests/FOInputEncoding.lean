/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.FirstOrder.Ordered.Encoding
import Complexity.Logics.FirstOrder.Ordered.FullTuple.Power

/-! # Native input-layout formulas at markers, payloads, terminators, and padding -/

namespace ComplexityTests.FOInputEncoding

open FirstOrder Language Cslib.Logic Turing.MultiTapeTM

private inductive Relation : ℕ → Type
  | flag : Relation 0
  | mark : Relation 1

private abbrev L : Language where
  Functions _ := Empty
  Relations := Relation

private def vocabulary : Vocabulary L where
  count := 2
  symbol :=
    { toFun := fun i => if i = 0 then ⟨0, .flag⟩ else ⟨1, .mark⟩
      invFun := fun ⟨_, r⟩ => match r with | .flag => 0 | .mark => 1
      left_inv := by intro i; fin_cases i <;> rfl
      right_inv := by rintro ⟨_, r⟩; cases r <;> rfl }

private def input : EncodedStructure := (2, [ [true], [false, true] ])

private theorem wellFormed : vocabulary.WellFormed input := by decide +kernel

private instance : Fact (2 ≤ 16) := ⟨by decide⟩

private instance : Fact (2 ≤ 2) := ⟨by decide⟩

private instance : vocabulary.powerLanguage.Structure (Fin 16) :=
  vocabulary.powerStructure input 16

-- The endpoint is 13, after a cardinality frame and nullary and unary relation frames.
example : vocabulary.inputLength.Realize ![(13 : Fin 16)] := by
  rw [vocabulary.realize_inputLength wellFormed (by decide)]
  rfl

example : ¬ vocabulary.inputLength.Realize ![(12 : Fin 16)] := by
  rw [vocabulary.realize_inputLength wellFormed (by decide)]
  decide

-- Both the nullary payload and the final true unary payload are preserved.
example : vocabulary.inputBit.Realize ![(6 : Fin 16)] ∧
    vocabulary.inputBit.Realize ![(11 : Fin 16)] := by
  rw [vocabulary.realize_inputBit wellFormed (by decide),
    vocabulary.realize_inputBit wellFormed (by decide)]
  decide

-- A marker is true even when the payload that follows it is false.
example : vocabulary.inputBit.Realize ![(8 : Fin 16)] ∧
    ¬ vocabulary.inputBit.Realize ![(9 : Fin 16)] := by
  rw [vocabulary.realize_inputBit wellFormed (by decide),
    vocabulary.realize_inputBit wellFormed (by decide)]
  decide

-- The unary-cardinality terminator, table terminator, and out-of-word padding are false.
example : ¬ vocabulary.inputBit.Realize ![(4 : Fin 16)] ∧
    ¬ vocabulary.inputBit.Realize ![(12 : Fin 16)] ∧
    ¬ vocabulary.inputBit.Realize ![(15 : Fin 16)] := by
  rw [vocabulary.realize_inputBit wellFormed (by decide),
    vocabulary.realize_inputBit wellFormed (by decide),
    vocabulary.realize_inputBit wellFormed (by decide)]
  decide

private def source : FO.Ordered.Structure L where
  size := 2
  size_ge_two := by decide
  input := { RelMap := fun r xs => match r with | .flag => True | .mark => xs 0 = 1 }

private theorem arity_le_two (i : Fin vocabulary.count) : vocabulary.arity i ≤ 2 := by
  fin_cases i <;> decide

-- The power bridge must preserve lexicographic ranks: (0,1) is 1, while (1,0) is 2.
example :
    letI : L.Structure (Fin 2) := source.input
    ((vocabulary.orderedPowerInterpretation 2 arity_le_two).rel vocabulary.powerIsElem).Realize
        (fun p => (![0, 1] : Fin 2 → Fin 2) p.2) ∧
      ¬ ((vocabulary.orderedPowerInterpretation 2 arity_le_two).rel vocabulary.powerIsElem).Realize
        (fun p => (![1, 0] : Fin 2 → Fin 2) p.2) := by
  let _ : L.Structure (Fin 2) := source.input
  constructor
  · apply (vocabulary.realize_orderedPower_rel 2 arity_le_two (by decide) source
      vocabulary.powerIsElem (fun _ => (![0, 1] : Fin 2 → Fin 2))).mpr
    change FO.Ordered.lexRank (![0, 1] : Fin 2 → Fin 2) < 2
    decide
  · intro h
    have hh := (vocabulary.realize_orderedPower_rel 2 arity_le_two (by decide) source
      vocabulary.powerIsElem (fun _ => (![1, 0] : Fin 2 → Fin 2))).mp h
    change FO.Ordered.lexRank (![1, 0] : Fin 2 → Fin 2) < 2 at hh
    exact (by decide : ¬ FO.Ordered.lexRank (![1, 0] : Fin 2 → Fin 2) < 2) hh

end ComplexityTests.FOInputEncoding
