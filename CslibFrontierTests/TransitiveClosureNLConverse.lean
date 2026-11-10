/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.TransitiveClosure.Converse
public import CslibFrontierTests.TransitiveClosureNL

/-! # NL ⊆ FO(TC) clients -/

@[expose] public section

open FirstOrder Language Turing Cslib.Turing Cslib.Logic Cslib.Logic.FO Cslib.Logic.FO.Ordered
open Cslib.Complexity Cslib.Complexity.ConfigurationGraph Turing.MultiTapeNTM.ConfigurationGraph
open Cslib.Tests.TransitiveClosureNL

namespace Cslib.Tests.TransitiveClosureNLConverse

/-! ### The capture theorems -/

/-- Every native `NL` query has a sentence with positive closures. -/
example {L : Language} [L.IsRelational] (v : Vocabulary L) {K : Ordered.Query L}
    (hK : K.encodedLanguage v ∈ NL encStructure) : PosTCDefinable K :=
  PosTCDefinable.of_encodedLanguage_mem_NL v hK

/-- FO(TC) captures native `NL`. -/
example {L : Language} [L.IsRelational] (v : Vocabulary L) (K : Ordered.Query L) :
    TCDefinable K ↔ K.encodedLanguage v ∈ NL encStructure :=
  tcDefinable_iff_encodedLanguage_mem_NL v K

/-- **Non-reachability has a positive sentence.** Its defining sentence `nonReach` negates a
closure and is not positive; the round trip through `NL` replaces it by one with a single
positive closure. -/
example : PosTCDefinable NonReach :=
  (tcDefinable_iff_posTCDefinable vocabulary NonReach).mp ⟨nonReach, realize_nonReach⟩

/-- The sentence `nonReach` itself lies outside the positive fragment. -/
example : ¬ TC.Positive nonReach true := fun h => Bool.false_ne_true h.1

/-! ### The configuration-graph formulas -/

section ConfigurationGraph

variable {k : ℕ} {State : Type} [Fintype State]

/-- The formulas read the input of an actual encoded structure through `inputSymbol` and
`inputLength`, on every power universe longer than the encoding. -/
example (a : EncodedStructure) (ha : vocabulary.WellFormed a) {N : ℕ} [Fact (2 ≤ N)]
    (hN : (encStructure a).length < N) (ntm : MultiTapeNTM k Bool State)
    (x y : Register k → Fin N) :
    letI := vocabulary.powerStructure a N
    (stepFormula vocabulary.powerLanguage vocabulary.inputSymbol vocabulary.inputLength ntm
        (fun i => .var (Sum.inl i)) (fun i => .var (Sum.inr i))).Realize (Sum.elim x y) ↔
      RegisterStep ntm (encStructure a) (fun i => (x i).val) (fun i => (y i).val) :=
  letI := vocabulary.powerStructure a N
  realize_stepFormula (vocabulary.realize_inputSymbol ha hN) (vocabulary.realize_inputLength ha hN)
    hN ntm _ _ _

variable {L : Language} {N : ℕ} [Fact (2 ≤ N)] [L.Structure (Fin N)]
  {inputFormula : Option Bool → (language L).Formula (Fin 1)}
  {lengthFormula : (language L).Formula (Fin 1)} {w : List Bool}
  (hinput : ∀ s (a : Fin N), (inputFormula s).Realize ![a] ↔ inputAt w a.val = s)
  (hlen : ∀ a : Fin N, lengthFormula.Realize ![a] ↔ w.length = a.val) (hn : w.length < N)
include hinput hlen hn

/-- A halted register tuple steps to itself. -/
example (ntm : MultiTapeNTM k Bool State) (x : Register k → Fin N)
    (hx : (x .control).val = stateCode (none : Option State)) :
    (stepFormula L inputFormula lengthFormula ntm (fun i => .var (Sum.inl i))
      (fun i => .var (Sum.inr i))).Realize (Sum.elim x x) :=
  (realize_stepFormula hinput hlen hn ntm _ _ _).mpr (.inl ⟨hx, rfl⟩)

/-- A halted register tuple steps to nothing else. -/
example (ntm : MultiTapeNTM k Bool State) (x y : Register k → Fin N)
    (hx : (x .control).val = stateCode (none : Option State)) (hxy : x ≠ y) :
    ¬ (stepFormula L inputFormula lengthFormula ntm (fun i => .var (Sum.inl i))
      (fun i => .var (Sum.inr i))).Realize (Sum.elim x y) := by
  rw [realize_stepFormula hinput hlen hn]
  rintro (⟨_, h⟩ | ⟨q, _, _, _, _, hc, _⟩)
  · exact hxy (funext fun i => Fin.ext (congrFun h i).symm)
  · exact Option.some_ne_none q (stateCode_injective (hc.symm.trans hx))

end ConfigurationGraph

end Cslib.Tests.TransitiveClosureNLConverse
