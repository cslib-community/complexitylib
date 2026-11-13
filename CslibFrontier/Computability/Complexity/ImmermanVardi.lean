/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.P.FirstOrder
public import CslibFrontier.Computability.Complexity.ImmermanVardi.Tableau.Acceptance
public import CslibFrontier.Computability.Complexity.ImmermanVardi.Input
public import CslibFrontier.Logics.FirstOrder.Ordered.FullTuple.LeastFixedPoint
public import CslibFrontier.Logics.FirstOrder.Ordered.FullTuple.Power
import CslibFrontier.Computability.Complexity.ImmermanVardi.Machine

/-!
# The Immerman–Vardi characterization of polynomial time

On the library's canonically ordered finite structures, a query is definable by one checked
FO(LFP) sentence exactly when its source-only encoded language belongs to native `P`.
The vocabulary is finite and relational; its fixed enumeration determines truth-table order.
Universes are `Fin n` with `n ≥ 2`. Order, BIT, zero, one, and maximum are canonical numeric
symbols, computed from the universe size rather than supplied as input tables.

The forward direction compiles a fixed formula to a native polynomial-time model checker.
For the converse, a native deterministic machine has a positive local tableau. Its input
symbols are defined directly from the actual binary encoding. A fixed tuple width bounds the
machine's time, input length, and finite feature tags for all input sizes. Pullback along the
canonical full-tuple interpretation gives one sentence over the original input universe.

## Main results

* `FO.Ordered.LFPDefinable.of_encodedLanguage_mem_P`: every native polynomial-time ordered
  query has a uniform checked FO(LFP) sentence.
* `FO.Ordered.lfpDefinable_iff_encodedLanguage_mem_P`: FO(LFP) captures native polynomial time.

## References

* [N. Immerman, *Relational Queries Computable in Polynomial Time*][Immerman1986], Theorem 1
  and Section 3. The theorem is instantiated here at the existing canonical ordered vocabulary
  and unary-cardinality/full-truth-table encoding. Malformed table shapes and universes below
  two are rejected.
-/

public section

open FirstOrder Language Turing Turing.MultiTapeTM

namespace Cslib.Logic

namespace FO.Ordered

open Cslib.Complexity

/-- Every ordered query decided by an actual native polynomial-time machine is defined by one
checked FO(LFP) sentence over the original ordered input structures. -/
theorem LFPDefinable.of_encodedLanguage_mem_P {L : Language} [L.IsRelational]
    (v : Vocabulary L) {K : Query L} (hK : K.encodedLanguage v ∈ P encStructure) :
    LFPDefinable K := by
  classical
  obtain ⟨m, State, _, tm, htm⟩ := exists_tm_of_encodedLanguage_mem_P v hK
  obtain ⟨k, hk, har, hb, hdec⟩ := htm (Fintype.card (ImmermanVardi.Tableau.Tag m State))
  let A := {a : EncodedStructure // v.WellFormed a ∧ 2 ≤ a.1}
  let size (a : A) := a.val.1 ^ k
  let inst (a : A) : v.powerLanguage.Structure (Fin (size a)) :=
    v.powerStructure a.val (size a)
  let instSize (a : A) : Fact (2 ≤ size a) := by
    let _ : Fact (2 ≤ a.val.1) := ⟨a.property.2⟩
    exact ⟨FullTupleInterpretation.two_le_pow (n := a.val.1) hk⟩
  have hbA (a : A) := hb a.val a.property.1 a.property.2
  obtain ⟨ψ, hψ⟩ := ImmermanVardi.Tableau.exists_acceptance_sentence
    (L := v.powerLanguage) (size := size) tm (fun a => encStructure a.val) v.inputSymbol
    (fun a s p => v.realize_inputSymbol a.property.1 ((Nat.lt_succ_self _).trans (hbA a).1) s p)
    (fun a => (hbA a).1) (fun a => (hbA a).2)
  let I := v.orderedPowerInterpretation k har
  refine ⟨I.onLFPSentence ψ, fun M => ?_⟩
  let a : A := ⟨encode v M, v.wellFormed_encode M (Equiv.refl M), M.size_ge_two⟩
  have hv (v : Empty → Fin (size a)) : v = Empty.elim := Subsingleton.elim _ _
  have hψ' := hψ a
  simp only [hv] at hψ'
  rw [I.realize_onLFPSentence hk ψ]
  have he := v.inputStructure_orderedPowerInterpretation k har hk M
  change I.inputStructure (n := M.size) = inst a at he
  rw [he]
  exact (hdec M).trans hψ'.symm

/-- **Immerman–Vardi:** a single checked FO(LFP) sentence defines an ordered query exactly
when its source-only language is decidable in native polynomial time. -/
theorem lfpDefinable_iff_encodedLanguage_mem_P {L : Language} [L.IsRelational]
    (v : Vocabulary L) (K : Query L) :
    LFPDefinable K ↔ K.encodedLanguage v ∈ P encStructure :=
  ⟨fun h => h.encodedLanguage_mem_P v, LFPDefinable.of_encodedLanguage_mem_P v⟩

end FO.Ordered
end Cslib.Logic
