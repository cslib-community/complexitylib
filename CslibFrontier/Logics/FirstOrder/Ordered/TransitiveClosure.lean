/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.Query
public import CslibFrontier.Logics.FirstOrder.Operator.TransitiveClosure.Positive

/-!
# Transitive-closure definability of ordered queries

An ordered query is `TCDefinable` if a single FO(TC) sentence defines it on all canonically
ordered structures, and `PosTCDefinable` if moreover every closure of that sentence occurs
positively. As for `LFPDefinable`, the input relations vary while order, BIT and the numeric
constants keep the meanings supplied by `Ordered.language`, and structures have at least two
elements. Closure is reflexive transitive closure on tuples of any fixed width, including width
zero.

## Main definitions

* `Cslib.Logic.FO.Ordered.TCDefinable`: definability by one FO(TC) sentence.
* `Cslib.Logic.FO.Ordered.PosTCDefinable`: definability by one FO(positive TC) sentence.

## Main results

* `Cslib.Logic.FO.Ordered.Definable.posTCDefinable`: first-order definable queries are
  FO(positive TC) definable.

## References

* [N. Immerman, *Languages That Capture Complexity Classes*, Section 3][Immerman1987]
-/

public section

open FirstOrder Language
namespace Cslib.Logic.FO.Ordered

/-- One FO(TC) sentence defines the query uniformly over all ordered inputs. -/
@[expose] def TCDefinable {L : Language} (K : Query L) : Prop :=
  ∃ φ : Operator.Formula (language L) TC.shape [] Empty,
    ∀ M : Structure L, M ∈ K ↔ φ.Realize (M := M) TC.interpretation Operator.RelEnv.empty Empty.elim

/-- One FO(TC) sentence whose closure operators all occur positively defines the query. -/
@[expose] def PosTCDefinable {L : Language} (K : Query L) : Prop :=
  ∃ φ : Operator.Formula (language L) TC.shape [] Empty, TC.Positive φ true ∧
    ∀ M : Structure L, M ∈ K ↔ φ.Realize (M := M) TC.interpretation Operator.RelEnv.empty Empty.elim

/-- Positive closure definability is closure definability. -/
theorem PosTCDefinable.tcDefinable {L : Language} {K : Query L} (h : PosTCDefinable K) :
    TCDefinable K :=
  let ⟨φ, _, hφ⟩ := h
  ⟨φ, hφ⟩

/-- Ordinary ordered first-order definability embeds into positive closure definability. -/
theorem Definable.posTCDefinable {L : Language} {K : Query L} (hK : Definable K) :
    PosTCDefinable K := by
  obtain ⟨φ, hφ⟩ := hK
  refine ⟨.ofFO φ, trivial, fun M => ?_⟩
  have he : (default : Empty → M) = Empty.elim := Subsingleton.elim _ _
  simpa only [Operator.Formula.Realize, FirstOrder.Language.Sentence.Realize, he] using hφ M

end Cslib.Logic.FO.Ordered
