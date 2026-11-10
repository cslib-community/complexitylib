/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.SecondOrder.Horn.LeastFixedPoint
public import CslibFrontier.Logics.FirstOrder.Ordered.LeastFixedPoint
public import CslibFrontier.Logics.FirstOrder.Ordered.Successor

/-!
# SO∃-Horn definability of ordered queries

An ordered query is `HornDefinable` when one SO∃-Horn sentence with quantifier-free guards defines
it on every canonical ordered structure. The guards are formulas of the ordered vocabulary
extended by a primitive successor, `language (succLanguage L)`: they may use the input relations,
`=`, `≤`, `BIT`, successor and the constants `0`, `1` and `max`.

Grädel's characterization of polynomial time by SO∃-Horn logic is stated for structures with
successor. Successor must be primitive here because guards are quantifier-free: from `≤` alone,
`y = x + 1` needs the universal quantifier of `Cslib.Logic.FO.Ordered.successor`. SO∃-Horn
definability over `≤` and `BIT` without successor is a different fragment and is not treated here.

Every SO∃-Horn sentence is equivalent to one FO(LFP) sentence on canonical ordered structures, so
`HornDefinable` queries are `LFPDefinable`. Successor is first removed from the guards with
`Cslib.Logic.FO.Ordered.elimSucc`. The resulting guards are no longer quantifier-free, which the
FO(LFP) translation allows. The translation packs the relation variables into one fixed point with
one-hot tags. It takes the numeric constants `0` and `1` as the two distinct tag values, which
exist because canonical ordered structures have at least two elements.

## Main definitions

* `Cslib.Logic.ESO.Horn.Sentence.elimSucc`: remove successor from every guard.
* `Cslib.Logic.FO.Ordered.HornDefinable`: definability by one SO∃-Horn sentence whose guards are
  quantifier-free formulas of the ordered vocabulary with successor.

## Main results

* `Cslib.Logic.ESO.Horn.Sentence.realize_elimSucc`: successor elimination preserves truth on
  canonical structures with at least two elements.
* `Cslib.Logic.FO.Ordered.LFPDefinable.of_horn`: a query defined by an SO∃-Horn sentence over the
  ordered vocabulary, with arbitrary first-order guards, is `LFPDefinable`.
* `Cslib.Logic.FO.Ordered.HornDefinable.lfpDefinable`: `HornDefinable` queries are
  `LFPDefinable`.

## References

* [E. Grädel, *Capturing complexity classes by fragments of second-order logic*][Gradel1992],
  for SO∃-Horn logic on successor structures. Section and theorem locators are unverified.
* [N. Immerman, *Descriptive Complexity*][Immerman1999], Chapter 4, for FO(LFP).
-/

public section

open FirstOrder Language

namespace Cslib.Logic

namespace ESO.Horn.Sentence

open FO.Ordered

variable {L : Language}

/-- Replace each successor atom in every guard by its first-order definition from `≤`
(`Cslib.Logic.FO.Ordered.elimSucc`). Quantifier-free guards become guards with one universal
quantifier per eliminated atom. -/
noncomputable def elimSucc (Φ : Sentence (language (succLanguage L))) :
    Sentence (language L) :=
  Φ.mapGuards fun φ => FO.Ordered.elimSucc φ

/-- On canonical structures `Fin n` with `2 ≤ n`, successor elimination preserves truth. -/
theorem realize_elimSucc {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)]
    (Φ : Sentence (language (succLanguage L))) : Φ.elimSucc.Realize (Fin n) ↔ Φ.Realize (Fin n) :=
  realize_mapGuards _ (fun φ v => realize_elimSucc_formula φ v) Φ

end ESO.Horn.Sentence

namespace FO.Ordered

variable {L : Language}

/-- An ordered query is SO∃-Horn definable when one SO∃-Horn sentence with quantifier-free guards
defines it on every canonical ordered structure. Guards are formulas of the ordered vocabulary
with a primitive successor, as in Grädel's successor structures. Successor cannot be omitted:
a quantifier-free guard over `≤` cannot express `y = x + 1`. -/
@[expose] def HornDefinable (K : Query L) : Prop :=
  ∃ Φ : ESO.Horn.Sentence (language (succLanguage L)),
    Φ.IsQF ∧ ∀ M : Structure L, M ∈ K ↔ Φ.Realize M

/-- **SO∃-Horn sentences define FO(LFP) queries.** A query defined by an SO∃-Horn sentence over
the ordered vocabulary is `LFPDefinable`. The guards may be arbitrary first-order formulas.
The fixed-point translation uses the distinct constants `0` and `1` as its tag values. -/
theorem LFPDefinable.of_horn {K : Query L} (Φ : ESO.Horn.Sentence (language L))
    (hΦ : ∀ M : Structure L, M ∈ K ↔ Φ.Realize M) : LFPDefinable K := by
  obtain ⟨φ, hφ⟩ := Φ.exists_lfp_realize_iff (M := fun M : Structure L => Fin M.size)
    (zero L) (one L) fun _ => realize_zero_ne_one _
  exact ⟨φ, fun M => (hΦ M).trans (hφ M).symm⟩

/-- A `HornDefinable` query is defined by an SO∃-Horn sentence over the ordered vocabulary,
with successor eliminated from the guards. -/
theorem HornDefinable.exists_sentence {K : Query L} (hK : HornDefinable K) :
    ∃ Φ : ESO.Horn.Sentence (language L), ∀ M : Structure L, M ∈ K ↔ Φ.Realize M := by
  obtain ⟨Φ, -, hΦ⟩ := hK
  exact ⟨Φ.elimSucc, fun M => (hΦ M).trans (ESO.Horn.Sentence.realize_elimSucc Φ).symm⟩

/-- **SO∃-Horn definable queries are FO(LFP) definable.** -/
theorem HornDefinable.lfpDefinable {K : Query L} (hK : HornDefinable K) : LFPDefinable K := by
  obtain ⟨Φ, hΦ⟩ := hK.exists_sentence
  exact LFPDefinable.of_horn Φ hΦ

end FO.Ordered

end Cslib.Logic
