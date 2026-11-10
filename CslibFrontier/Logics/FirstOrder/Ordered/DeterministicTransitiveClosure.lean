/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Operator.DeterministicTransitiveClosure
public import CslibFrontier.Logics.FirstOrder.Ordered.TransitiveClosure

/-!
# Deterministic transitive-closure definability of ordered queries

An ordered query is `DTCDefinable` if a single FO(DTC) sentence defines it on all canonically
ordered structures. As for `TCDefinable`, the input relations vary while order, BIT and the
numeric constants keep the meanings supplied by `Ordered.language`, and structures have at least
two elements.

FO(DTC) sentences are FO(TC) syntax trees, `Operator.Formula (language L) TC.shape [] Empty`,
read with `DTC.interpretation` instead of `TC.interpretation`; see
`Cslib.Logic.FO.DTC.interpretation`. Deterministic closure may occur at any polarity and nesting
depth and has any fixed width, including zero.

## Main definitions

* `Cslib.Logic.FO.Ordered.DTCDefinable`: definability by one FO(DTC) sentence.

## Main results

* `Cslib.Logic.FO.Ordered.Definable.dtcDefinable`: first-order definable queries are FO(DTC)
  definable.
* `Cslib.Logic.FO.Ordered.DTCDefinable.tcDefinable`: FO(DTC) definable queries are FO(TC)
  definable.

## References

* [N. Immerman, *Languages That Capture Complexity Classes*, Section 4][Immerman1987]
-/

public section

open FirstOrder Language
namespace Cslib.Logic.FO.Ordered

/-- One FO(DTC) sentence defines the query uniformly over all ordered inputs.

The sentence is FO(TC) syntax, read with deterministic closure `DTC.interpretation`; the same
sentence read with `TC.interpretation` generally defines a different query. -/
@[expose] def DTCDefinable {L : Language} (K : Query L) : Prop :=
  ∃ φ : Operator.Formula (language L) TC.shape [] Empty,
    ∀ M : Structure L,
      M ∈ K ↔ φ.Realize (M := M) DTC.interpretation Operator.RelEnv.empty Empty.elim

/-- Ordinary ordered first-order definability embeds into deterministic closure definability. -/
theorem Definable.dtcDefinable {L : Language} {K : Query L} (hK : Definable K) :
    DTCDefinable K := by
  obtain ⟨φ, hφ⟩ := hK
  refine ⟨.ofFO φ, fun M => ?_⟩
  have he : (default : Empty → M) = Empty.elim := Subsingleton.elim _ _
  simpa only [Operator.Formula.Realize, FirstOrder.Language.Sentence.Realize, he] using hφ M

/-- Deterministic closure definability is closure definability, via `DTC.toTC`. -/
theorem DTCDefinable.tcDefinable {L : Language} {K : Query L} (hK : DTCDefinable K) :
    TCDefinable K :=
  let ⟨φ, hφ⟩ := hK
  ⟨DTC.toTC φ, fun M => (hφ M).trans (DTC.realize_toTC φ _ _).symm⟩

end Cslib.Logic.FO.Ordered
