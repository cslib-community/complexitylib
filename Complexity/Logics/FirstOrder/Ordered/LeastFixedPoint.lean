/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.Query
public import Complexity.Logics.FirstOrder.Operator.LeastFixedPoint

/-!
# Least-fixed-point definability of ordered queries

An ordered query is `LFPDefinable` if a single checked FO(LFP) sentence defines it on all
canonically ordered structures. The input relations vary, while order, BIT, and the numeric
constants retain the meanings supplied by `Ordered.language`. Structures have at least two
elements, as in the existing ordered-query convention.

This is the logical side of the Immerman–Vardi characterization. The machine side uses the
existing source-only `Query.encodedLanguage` and native polynomial-time class.

## References

* [N. Immerman, *Relational Queries Computable in Polynomial Time*][Immerman1986], Theorem 1.
-/

public section

open FirstOrder Language

namespace Cslib.Logic.FO.Ordered

/-- One checked least-fixed-point sentence defines the query uniformly over all ordered inputs. -/
@[expose] def LFPDefinable {L : Language} (K : Query L) : Prop :=
  ∃ φ : LFP.Formula (language L) [] Empty,
    ∀ M : Structure L, M ∈ K ↔ φ.Realize (M := M) Operator.RelEnv.empty Empty.elim

/-- Ordinary ordered first-order definability embeds into least-fixed-point definability. -/
theorem Definable.lfpDefinable {L : Language} {K : Query L} (hK : Definable K) :
    LFPDefinable K := by
  obtain ⟨φ, hφ⟩ := hK
  refine ⟨⟨.ofFO φ, rfl⟩, fun M => ?_⟩
  have he : (default : Empty → M) = Empty.elim := Subsingleton.elim _ _
  simpa only [LFP.Formula.Realize, Operator.Formula.Realize,
    FirstOrder.Language.Sentence.Realize, he] using hφ M

end Cslib.Logic.FO.Ordered
