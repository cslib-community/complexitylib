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

/-!
# SO∃-Horn definable queries are in polynomial time

Grädel's theorem says that SO∃-Horn logic captures polynomial time on ordered structures with
successor. This module proves its upper bound for the library's canonical ordered structures:
every `HornDefinable` query has its source-only encoded language in native `P`. The proof goes
through FO(LFP) (`HornDefinable.lfpDefinable`) and the FO(LFP) model checker
(`LFPDefinable.encodedLanguage_mem_P`).

It also places `HornDefinable` inside ordered ESO definability: the SO∃-Horn sentence translates
into an existential second-order sentence with the same meaning (`ESO.Horn.Sentence.toESO`).

The converse, that every query in native `P` is `HornDefinable`, is open; `ROADMAP.md` tracks it.

## Main results

* `Cslib.Logic.FO.Ordered.HornDefinable.encodedLanguage_mem_P`: SO∃-Horn definable ordered
  queries are in native `P`.
* `Cslib.Logic.FO.Ordered.ESODefinable.of_horn`,
  `Cslib.Logic.FO.Ordered.HornDefinable.esoDefinable`: SO∃-Horn definability implies ordered
  ESO definability.

## References

* [E. Grädel, *Finite Model Theory and Descriptive Complexity*][Gradel2007], Theorems 3.2.17
  (pp. 147–148) and 3.2.18 (p. 148), for the upper bound and the capture of polynomial time on
  ordered structures.
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
