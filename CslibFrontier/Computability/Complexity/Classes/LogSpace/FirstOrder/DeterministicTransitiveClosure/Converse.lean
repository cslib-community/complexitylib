/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.TransitiveClosure.Converse
public import CslibFrontier.Logics.FirstOrder.Ordered.DeterministicTransitiveClosure
import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.DeterministicTransitiveClosure
import CslibFrontier.Logics.FirstOrder.Operator.DeterministicTransitiveClosure.Tuple

/-!
# Deterministic logarithmic space in FO(DTC)

On the library's canonically ordered finite structures, every query whose source-only encoded
language belongs to native `L` is defined by one FO(DTC) sentence.

The sentence is the acceptance sentence of the NL ⊆ FO(TC) construction
(`ConfigurationGraph.acceptanceSentence`), read with deterministic closure. A deterministic
machine has at most one successor at every register tuple, with no validity guard
(`rightUnique_registerStep_fin`): the halting tag allows only the tuple itself, and otherwise the
observed state and symbols fix the action. On such a relation the deterministic reduct is the
relation itself, so deterministic closure of `stepFormula` is its closure, and the NL proof applies
through `exists_sentence_of_decidesInSpace` with the deterministic reduct as closure transform.
For a nondeterministic machine the two readings differ: a configuration with two successors has
none in the deterministic reduct.

## Main results

* `Cslib.Complexity.ConfigurationGraph.realize_acceptanceSentence_dtc`: under deterministic
  closure, the acceptance sentence of a deterministic machine holds exactly when it accepts.
* `Cslib.Logic.FO.Ordered.DTCDefinable.of_encodedLanguage_mem_L`: L ⊆ FO(DTC).
* `Cslib.Logic.FO.Ordered.dtcDefinable_iff_encodedLanguage_mem_L`: FO(DTC) captures L, with
  the converse inclusion `DTCDefinable.encodedLanguage_mem_L`.

## References

* [N. Immerman, *Languages That Capture Complexity Classes*, Theorem 4.2][Immerman1987]:
  L is the class of queries definable in FO(DTC) on ordered structures. As for NL, an
  instantaneous description is coded by a fixed tuple of variables; for a deterministic machine
  its successor relation is functional, so its deterministic closure is its closure.
-/

public section

open FirstOrder Language Turing Cslib.Turing Cslib.Logic Cslib.Logic.FO Cslib.Logic.FO.Ordered
open Turing.MultiTapeNTM.ConfigurationGraph

namespace Cslib.Complexity.ConfigurationGraph

variable {L : Language} {k : ℕ} {State : Type} [Fintype State] {N : ℕ} [Fact (2 ≤ N)]
  [L.Structure (Fin N)]

/-- **Deterministic closure decides acceptance of a deterministic machine**: on a universe `Fin N`
that contains the input length and every register of every reachable configuration, the
acceptance sentence read with deterministic closure holds exactly when the machine accepts. -/
theorem realize_acceptanceSentence_dtc
    {inputFormula : Option Bool → (language L).Formula (Fin 1)}
    {lengthFormula : (language L).Formula (Fin 1)} {w : List Bool}
    (hinput : ∀ s (a : Fin N), (inputFormula s).Realize ![a] ↔ inputAt w a.val = s)
    (hlen : ∀ a : Fin N, lengthFormula.Realize ![a] ↔ w.length = a.val) (hn : w.length < N)
    (tm : MultiTapeTM k Bool State)
    (hfit : ∀ v, Relation.ReflTransGen tm.toMultiTapeNTM.ViewStep (tm.toMultiTapeNTM.initView w) v →
      Fits N (registers v)) :
    (acceptanceSentence L inputFormula lengthFormula tm.toMultiTapeNTM).Realize (M := Fin N)
        DTC.interpretation Operator.RelEnv.empty Empty.elim ↔ tm.toMultiTapeNTM.Accepts w := by
  rw [DTC.interpretation_eq_closureBy]
  exact realize_acceptanceSentence_closureBy DTC.transports_deterministicReduct hinput hlen hn
    tm.toMultiTapeNTM
    (DTC.deterministicReduct_eq_self (rightUnique_registerStep_fin tm.deterministic)) hfit

end Cslib.Complexity.ConfigurationGraph

namespace Cslib.Logic.FO.Ordered

open Cslib.Complexity Cslib.Complexity.ConfigurationGraph

/-- **L ⊆ FO(DTC)** on canonically ordered structures: a query whose source-only encoded language
is decided by a native deterministic logarithmic-space machine is defined by one FO(DTC)
sentence. -/
theorem DTCDefinable.of_encodedLanguage_mem_L {L : Language} [L.IsRelational]
    (v : Vocabulary L) {K : Query L} (hK : K.encodedLanguage v ∈ Complexity.L encStructure) :
    DTCDefinable K := by
  obtain ⟨f, ⟨_, _, _, State, _, tm, htm⟩, hA⟩ := hK
  let _ := Fintype.ofFinite State
  obtain ⟨φ, -, hφ⟩ := exists_sentence_of_decidesInSpace v DTC.transports_deterministicReduct
    (htm.decidesInSpace hA) fun _ _ =>
      DTC.deterministicReduct_eq_self (rightUnique_registerStep_fin tm.deterministic)
  exact ⟨φ, hφ⟩

/-- **FO(DTC) captures L** ([Immerman1987], Theorem 4.2): a single FO(DTC) sentence defines an
ordered query exactly when its source-only language is in native deterministic logarithmic
space. -/
theorem dtcDefinable_iff_encodedLanguage_mem_L {L : Language} [L.IsRelational]
    (v : Vocabulary L) (K : Query L) :
    DTCDefinable K ↔ K.encodedLanguage v ∈ Complexity.L encStructure :=
  ⟨fun h => h.encodedLanguage_mem_L v, DTCDefinable.of_encodedLanguage_mem_L v⟩

end Cslib.Logic.FO.Ordered
