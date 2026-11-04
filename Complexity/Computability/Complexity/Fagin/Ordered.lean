/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Fagin.Converse
public import Complexity.Logics.FirstOrder.Ordered.StrictOrder
public import Complexity.Computability.Complexity.Classes.LogSpace.FirstOrder.Ordered
import Complexity.Computability.Complexity.Reduction

/-!
# Ordered existential second-order definability

The NP tableau construction applies to arbitrary queries on canonically ordered structures.
The order used to read relation tables is retained, rather than existentially quantified.
Consequently input relations need not be invariant under permutations of the universe.

## Main definitions

* `Cslib.Logic.FO.Ordered.ESODefinable`: existential second-order definability over the canonical
  ordered language.

## Main results

* `Cslib.Logic.FO.Ordered.ESODefinable.of_queryLanguage_mem_NP`: every ordered query whose
  source-only encoding language is in NP is ESO-definable, without assuming invariance under
  permutations of the input relations.
* `Cslib.Logic.FO.Ordered.ESODefinable.of_powerLanguage`: the ordered version of the Fagin
  power-structure bridge.

## References

* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
* [N. Immerman, *Descriptive Complexity*, Theorem 7.8][Immerman1999]
-/

@[expose] public section

universe u v

namespace Cslib.Logic

open FirstOrder Language Structure
open Cslib.Complexity Turing Turing.MultiTapeTM

namespace FO.Ordered

/-- A query is existential second-order definable when one ESO sentence in the public ordered
language defines it on all canonical structures. Numeric predicates and constants retain their
fixed values; only the finitely many second-order relation variables are existentially chosen. -/
def ESODefinable {L : Language.{u, v}} (K : Query L) : Prop :=
  ∃ Φ : ESO.Sentence (language L), ∀ M : Ordered.Structure L, M ∈ K ↔ Φ.Realize M

/-- Every first-order definable ordered query is existential second-order definable. -/
theorem Definable.esoDefinable {L : Language.{u, v}} {K : Query L} (hK : Definable K) :
    ESODefinable K := by
  obtain ⟨φ, hφ⟩ := hK
  exact ⟨ESO.Sentence.ofSentence φ, fun M => (hφ M).trans (ESO.Sentence.realize_ofSentence φ).symm⟩

/-- The existing fixed-sentence encoding is exactly the new arbitrary-query encoding applied
to the class defined by that sentence. Its size and shape rejection behavior is unchanged. -/
theorem encodedLanguage_sentence {L : Language} [L.IsRelational] (v : Vocabulary L)
    (φ : (language L).Sentence) :
    Query.encodedLanguage {M : Ordered.Structure L | φ.Realize M} v =
      queryLanguage v φ := rfl

/-- Every first-order definable ordered query has its source-only encoded language in NP. -/
theorem Definable.encodedLanguage_mem_NP {L : Language} [L.IsRelational] (v : Vocabulary L)
    {K : Query L} (hK : Definable K) : K.encodedLanguage v ∈ NP encStructure := by
  obtain ⟨φ, hφ⟩ := hK
  have hK' : K = {M : Ordered.Structure L | φ.Realize M} := Set.ext hφ
  rw [hK', encodedLanguage_sentence]
  exact P_subset_NP (L_subset_P (queryLanguage_mem_L v φ))

/-- Pulling a strict-order ESO sentence into the public ordered language preserves its truth
on the fixed canonical order. -/
private theorem realize_onESOSentence_strictOrder {L : Language.{u, v}} [L.IsRelational]
    (M : Ordered.Structure L) (Φ : ESO.Sentence (L.sum ESO.orderLanguage)) :
    ((strictOrderInterpretation L).onESOSentence Φ).Realize M ↔
      letI := ESO.varLanguage.structure (arity := fun _ : Unit => 2)
        (ESO.orderRelOfEquiv (Equiv.refl M));
      Φ.Realize M := by
  let _ := ESO.varLanguage.structure (arity := fun _ : Unit => 2)
    (ESO.orderRelOfEquiv (Equiv.refl M))
  rw [(strictOrderInterpretation L).realize_onESOSentence]
  exact Φ.realize_iff_of_equiv (strictOrderEquiv M)

/-- The ordered version of the Fagin power-structure bridge. The canonical numbering is retained,
so arbitrary ordered queries are admitted. -/
theorem ESODefinable.of_powerLanguage {L : Language.{u, v}} [L.IsRelational]
    (v : Vocabulary L) {K : Query L} (k : ℕ) (hk : 1 ≤ k)
    (har : ∀ i : Fin v.count, v.arity i ≤ k) (Ψ : ESO.Sentence v.powerLanguage)
    (hΨ : ∀ M : Ordered.Structure L,
      M ∈ K ↔ letI := v.powerStructure (v.encode M (Equiv.refl M)) (M.size ^ k);
        Ψ.Realize (Fin (M.size ^ k))) : ESODefinable K := by
  refine ⟨(strictOrderInterpretation L).onESOSentence
    ((v.powerInterpretation k har).onESOSentence Ψ), fun M => ?_⟩
  rw [realize_onESOSentence_strictOrder,
    v.realize_onESOSentence_powerInterpretation k hk har M (Equiv.refl M) Ψ]
  exact hΨ M

/-- Every ordered query whose source-only encoding language belongs to NP is definable in
existential second-order logic over the canonical ordered language. The query may depend on
the fixed ordering of its input relations: no isomorphism-invariance assumption is required.
This is the ordered converse of Fagin's characterization [Fagin1974], [Immerman1999]. -/
theorem ESODefinable.of_queryLanguage_mem_NP {L : Language.{u, v}} [L.IsRelational]
    (v : Vocabulary L) {K : Query L} (hNP : K.encodedLanguage v ∈ NP encStructure) :
    ESODefinable K := by
  obtain ⟨k, hk, har, Ψ, hΨ⟩ := v.exists_powerSentence_of_mem_NP hNP
  apply ESODefinable.of_powerLanguage v k hk har Ψ
  intro M
  exact (mem_encodedLanguage_encode v K M).symm.trans
    (hΨ (encode v M) (v.wellFormed_encode M (Equiv.refl M)) M.size_ge_two)

end FO.Ordered

end Cslib.Logic
