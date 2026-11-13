/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.SecondOrder.Horn.Ordered
public import CslibFrontier.Computability.Complexity.Classes.P.FirstOrder
public import CslibFrontier.Computability.Complexity.Fagin.Ordered
import CslibFrontier.Computability.Complexity.Gradel.Tableau
import CslibFrontier.Computability.Complexity.ImmermanVardi.Input
import CslibFrontier.Computability.Complexity.ImmermanVardi.Machine
import CslibFrontier.Logics.FirstOrder.Ordered.FullTuple.Horn
import CslibFrontier.Logics.FirstOrder.Ordered.FullTuple.Power

/-!
# Grädel's characterization of polynomial time

Grädel's theorem says that SO∃-Horn logic captures polynomial time on ordered structures with
successor. On the library's canonically ordered finite structures (`Fin n` with `n ≥ 2`), this
module proves the full equivalence between `HornDefinable` and native `P` over the source-only
binary structure encoding `encStructure`:

* **Upper bound (`SO∃-Horn ⊆ P`):** every `HornDefinable` query translates into FO(LFP)
  (`HornDefinable.lfpDefinable`) and is decided in polynomial time by the FO(LFP) model checker
  (`LFPDefinable.encodedLanguage_mem_P`).
* **Converse (`P ⊆ SO∃-Horn`):** every native deterministic polynomial-time machine has a uniform
  SO∃-Horn acceptance tableau (`Gradel.Tableau.acceptanceHornSentence`) over a fixed tuple-power
  universe `Fin (n ^ k)`. Pulling that sentence back along `Vocabulary.orderedPowerInterpretation`
  via `FullTupleInterpretation.onHornSentence` and eliminating first-order quantifiers from clause
  guards on successor structures (`HornDefinable.of_sentence`) yields a quantifier-free guarded
  SO∃-Horn sentence over `succLanguage L`.

It also places `HornDefinable` inside ordered ESO definability: the SO∃-Horn sentence translates
into an existential second-order sentence with the same meaning (`ESO.Horn.Sentence.toESO`).

## Main results

* `Cslib.Logic.FO.Ordered.HornDefinable.encodedLanguage_mem_P`: SO∃-Horn definable ordered
  queries are in native `P`.
* `Cslib.Logic.FO.Ordered.HornDefinable.of_encodedLanguage_mem_P`: native polynomial-time ordered
  queries are `HornDefinable`.
* `Cslib.Logic.FO.Ordered.hornDefinable_iff_encodedLanguage_mem_P`: **Grädel's theorem** —
  `SO∃-Horn` captures native polynomial time on canonically ordered finite structures.
* `Cslib.Logic.FO.Ordered.ESODefinable.of_horn`,
  `Cslib.Logic.FO.Ordered.HornDefinable.esoDefinable`: SO∃-Horn definability implies ordered
  ESO definability.

## References

* [E. Grädel, *Finite Model Theory and Descriptive Complexity*][Gradel2007], Theorems 3.2.17–3.2.18
  (pp. 147–148) and Exercise 3.2.20 (p. 148), for the upper bound, the Horn computation tableau on
  ordered structures, and guard quantifier elimination using successor.
* [E. Grädel, *Capturing complexity classes by fragments of second-order logic*][Gradel1992],
  for the SO∃-Horn characterization of polynomial time on successor structures. Section and
  theorem locators are unverified.
* [N. Immerman, *Relational Queries Computable in Polynomial Time*][Immerman1986], Theorem 1,
  for the FO(LFP) step.
-/

public section

open FirstOrder Language

namespace Cslib.Logic.FO.Ordered

open Cslib.Complexity

variable {L : Language}

/-- **SO∃-Horn definable queries are in polynomial time.** This is the upper bound of Grädel's
theorem, for the existing source-only structure encoding. -/
theorem HornDefinable.encodedLanguage_mem_P [L.IsRelational] {K : Query L}
    (hK : HornDefinable K) (v : Vocabulary L) : K.encodedLanguage v ∈ P encStructure :=
  hK.lfpDefinable.encodedLanguage_mem_P v

/-- **Every native polynomial-time ordered query is SO∃-Horn definable.** This is the converse
direction of Grädel's theorem: the deterministic polynomial-time tableau is expressed as an
SO∃-Horn sentence over `Fin (M.size ^ k)`, pulled back along the full-tuple power interpretation,
and lowered to quantifier-free guards over `succLanguage L`. -/
theorem HornDefinable.of_encodedLanguage_mem_P [L.IsRelational]
    (v : Vocabulary L) {K : Query L} (hK : K.encodedLanguage v ∈ P encStructure) :
    HornDefinable K := by
  classical
  obtain ⟨m, State, _, tm, htm⟩ := exists_tm_of_encodedLanguage_mem_P v hK
  obtain ⟨k, hk, har, hb, hdec⟩ := htm 0
  let Φ := Gradel.Tableau.acceptanceHornSentence v.powerLanguage tm v.inputSymbol
  let I := v.orderedPowerInterpretation k har
  refine HornDefinable.of_sentence (I.onHornSentence Φ) fun M => ?_
  have hw : v.WellFormed (encode v M) := v.wellFormed_encode M (Equiv.refl M)
  have hlen : (encStructure (encode v M)).length + 1 < M.size ^ k :=
    (hb (encode v M) hw M.size_ge_two).1
  change M ∈ K ↔ (I.onHornSentence Φ).Realize (Fin M.size)
  rw [hdec, I.realize_onHornSentence (n := M.size) (by omega) Φ,
    v.inputStructure_orderedPowerInterpretation k har hk M]
  let _ : v.powerLanguage.Structure (Fin (M.size ^ k)) :=
    v.powerStructure (encode v M) (M.size ^ k)
  let _ : Fact (2 ≤ M.size ^ k) := ⟨FullTupleInterpretation.two_le_pow (n := M.size) hk⟩
  exact (Gradel.Tableau.realize_acceptanceHornSentence tm v.inputSymbol
    (encStructure (encode v M))
    (fun s p => v.realize_inputSymbol hw ((Nat.lt_succ_self _).trans hlen) s p) hlen).symm

/-- **Grädel's theorem (`SO∃-Horn = P`):** an ordered query is SO∃-Horn definable if and only if
its source-only encoded language is decidable in native polynomial time. -/
theorem hornDefinable_iff_encodedLanguage_mem_P [L.IsRelational]
    (v : Vocabulary L) (K : Query L) :
    HornDefinable K ↔ K.encodedLanguage v ∈ P encStructure :=
  ⟨fun h => h.encodedLanguage_mem_P v, HornDefinable.of_encodedLanguage_mem_P v⟩

/-- A query defined by an SO∃-Horn sentence over the ordered vocabulary is ESO definable. -/
theorem ESODefinable.of_horn {K : Query L} (Φ : ESO.Horn.Sentence (language L))
    (hΦ : ∀ M : Structure L, M ∈ K ↔ Φ.Realize M) : ESODefinable K :=
  ⟨Φ.toESO, fun M => (hΦ M).trans (ESO.Horn.Sentence.realize_toESO Φ).symm⟩

/-- **SO∃-Horn definability is a special case of ESO definability.** Successor is eliminated
from the guards first, so the ESO sentence uses only the ordered vocabulary. -/
theorem HornDefinable.esoDefinable {K : Query L} (hK : HornDefinable K) : ESODefinable K := by
  obtain ⟨Φ, hΦ⟩ := hK.exists_sentence
  exact ESODefinable.of_horn Φ hΦ

end Cslib.Logic.FO.Ordered
