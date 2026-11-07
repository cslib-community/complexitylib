/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Fagin.Ordered
public import Complexity.Computability.Complexity.Fagin.Witness

/-!
# Ordered existential second-order queries are in NP

Witness relations are materialized as additional input tables, and the existing native ordered
first-order model checker evaluates the matrix. The numeric constants, order and BIT keep their
canonical interpretations; they are neither guessed nor supplied in the input. Together with the
ordered tableau construction, this gives Fagin's characterization for arbitrary ordered queries
at the source-only structure encoding, with universes of size at least two.

The vocabulary and sentence are fixed. Polynomial bounds may depend on their relation arities
and the formula; this is data complexity. Malformed relation tables and universes of size zero
or one are rejected. The characterization concerns typed inputs under `encStructure`.

## Main definitions

* `Cslib.Logic.ESO.Sentence.orderedMatrix`: move the witness vocabulary before the numeric
  vocabulary so the existing ordered first-order model checker applies.

## Main results

* `Cslib.Logic.ESO.Sentence.realize_orderedMatrix`: the vocabulary reordering preserves the
  matrix's semantics, including numeric constants and predicates.
* `Cslib.Logic.ESO.Sentence.Layout.exists_orderedVerifier`: a native polynomial-time verifier
  with the layout's certificate-length polynomial and an explicit length guard.
* `Cslib.Logic.FO.Ordered.ESODefinable.encodedLanguage_mem_NP`: the ordered ESO-to-NP direction.
* `Cslib.Logic.FO.Ordered.esoDefinable_iff_encodedLanguage_mem_NP`: the ordered characterization.

## References

* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
* [N. Immerman, *Descriptive Complexity*, Proposition 7.6 and Theorem 7.8][Immerman1999].
  The construction guesses relation tables and applies fixed first-order model checking; the
  universal-matrix strengthening of Theorem 7.8 is not asserted.
-/

public section

namespace Cslib.Logic

open FirstOrder Language Structure
open Cslib.Complexity Turing.MultiTapeTM
open FO.Ordered (language numericLanguage)

namespace ESO.Sentence

/-- Reorder the witness and numeric vocabularies without changing either interpretation. -/
private def orderedMatrixMap (L R : Language) :
    (language L).sum R →ᴸ language (L.sum R) where
  onFunction _
    | .inl (.inl f) => .inl (.inl f)
    | .inl (.inr f) => .inr f
    | .inr f => .inl (.inr f)
  onRelation _
    | .inl (.inl r) => .inl (.inl r)
    | .inl (.inr r) => .inr r
    | .inr r => .inl (.inr r)

private instance orderedMatrixMap_isExpansionOn (L R : Language) (M : Type*)
    [L.Structure M] [R.Structure M] [numericLanguage.Structure M] :
    (orderedMatrixMap L R).IsExpansionOn M where
  map_onFunction f _ := by rcases f with (f | f) | f <;> rfl
  map_onRelation r _ := by rcases r with (r | r) | r <;> rfl

variable {L : Language} (Φ : Sentence (language L))

/-- The first-order matrix with witness relations among the input symbols and the canonical
numeric vocabulary last, as required by the ordered first-order model checker. -/
def orderedMatrix : (language (L.sum (varLanguage Φ.arity))).Sentence :=
  (orderedMatrixMap L (varLanguage Φ.arity)).onSentence Φ.matrix

/-- Reordering the vocabulary preserves the first-order matrix on any choice of witness
relations, with the same canonical numeric structure on both sides. -/
theorem realize_orderedMatrix {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)]
    (R : ∀ i, Set (Fin (Φ.arity i) → Fin n)) :
    (letI := varLanguage.structure R; Fin n ⊨ Φ.orderedMatrix) ↔
      (letI := varLanguage.structure R; Fin n ⊨ Φ.matrix) := by
  let _ := varLanguage.structure R
  exact LHom.realize_onSentence (Fin n) (orderedMatrixMap L (varLanguage Φ.arity)) Φ.matrix

namespace Layout

variable {Φ} (ℓ : Layout Φ) {m : ℕ} (e : Fin m ≃ Φ.Var)
    [L.IsRelational] (v : Vocabulary L)

/-- Ordered model checking of the materialized input is exactly checking the original matrix
in the certificate expansion. The shape check also rejects malformed original inputs. -/
theorem mem_queryLanguage_witnessInput (a : EncodedStructure) (w : List Bool) :
    ℓ.witnessInput e (a, w) ∈
        FO.Ordered.queryLanguage (v.sum (varLanguage.vocabulary Φ.arity e)) Φ.orderedMatrix ↔
      v.WellFormed a ∧ ∃ hn : 2 ≤ a.1,
        letI : Fact (2 ≤ a.1) := ⟨hn⟩
        letI := v.decode a
        letI := varLanguage.structure (ℓ.certRel a.1 (encStructure a).length w)
        Fin a.1 ⊨ Φ.matrix := by
  simp only [FO.Ordered.queryLanguage, Set.mem_ofPred_eq,
    wellFormed_witnessInput_iff, witnessInput_card]
  apply and_congr_right
  intro ha
  apply exists_congr
  intro hn
  let _ : Fact (2 ≤ a.1) := ⟨hn⟩
  rw [decode_witnessInput ℓ e v a w ha]
  let _ := v.decode a
  exact Φ.realize_orderedMatrix _

/-- Existentially choosing a certificate of the prescribed length is equivalent to ordered ESO
truth, with exactly the original source-only encoding and shape rejection. -/
theorem exists_witnessInput_mem_queryLanguage_iff (a : EncodedStructure) :
    (∃ w : List Bool, w.length = ℓ.polynomial.eval (encStructure a).length ∧
      ℓ.witnessInput e (a, w) ∈
        FO.Ordered.queryLanguage (v.sum (varLanguage.vocabulary Φ.arity e)) Φ.orderedMatrix) ↔
      a ∈ FO.Ordered.Query.encodedLanguage
        {M : FO.Ordered.Structure L | Φ.Realize M} v := by
  constructor
  · rintro ⟨w, _, hw⟩
    obtain ⟨ha, hn, hmatrix⟩ := (ℓ.mem_queryLanguage_witnessInput e v a w).1 hw
    exact ⟨ha, hn, ℓ.certRel a.1 (encStructure a).length w, hmatrix⟩
  · rintro ⟨ha, hn, R, hR⟩
    have hN : 0 < (encStructure a).length := by
      simp only [encStructure, length_encPair]
      omega
    obtain ⟨w, hw, hrel⟩ := ℓ.exists_certificate (card_le_length_encStructure a) hN R
    refine ⟨w, hw, (ℓ.mem_queryLanguage_witnessInput e v a w).2 ⟨ha, hn, ?_⟩⟩
    rw [hrel]
    exact hR

/-- Every fixed ordered ESO sentence has an actual polynomial-time verifier with the layout's
certificate polynomial. The verifier explicitly rejects certificates of the wrong length. Its
construction composes polynomial-time witness materialization with native ordered FO model
checking; no verifier or efficiency premise is assumed. -/
theorem exists_orderedVerifier :
    ∃ V : EncodedStructure × List Bool → Bool,
      ComputableInPolyTime V (encPair encStructure encBits) encBool ∧
      IsVerifier encStructure ℓ.polynomial V
        (FO.Ordered.Query.encodedLanguage {M : FO.Ordered.Structure L | Φ.Realize M} v) ∧
      ∀ a w, V (a, w) = true → w.length = ℓ.polynomial.eval (encStructure a).length := by
  let e := (Finite.equivFin Φ.Var).symm
  obtain ⟨f, hf, hdec⟩ := L_subset_P
    (FO.Ordered.queryLanguage_mem_L (v.sum (varLanguage.vocabulary Φ.arity e)) Φ.orderedMatrix)
  let V := f ∘ ℓ.witnessInput e
  have hV : ComputableInPolyTime V (encPair encStructure encBits) encBool :=
    hf.comp (ℓ.computableInPolyTime_witnessInput e)
  have hverifies : IsVerifier encStructure ℓ.polynomial V
      (FO.Ordered.Query.encodedLanguage {M : FO.Ordered.Structure L | Φ.Realize M} v) := by
    intro a
    rw [← ℓ.exists_witnessInput_mem_queryLanguage_iff e v a]
    exact exists_congr fun w => and_congr_right fun _ => hdec _
  exact ⟨strictVerifier encStructure ℓ.polynomial V,
    computableInPolyTime_strictVerifier _ _ hV, hverifies.strictVerifier,
    fun _ _ => length_eq_of_strictVerifier_eq_true⟩

end Layout

variable [L.IsRelational] (v : Vocabulary L)

/-- The source-only encoded language of a fixed ordered ESO sentence is in native `NP`.
Universe sizes below two and malformed source tables are excluded by the existing query API. -/
theorem ordered_queryLanguage_mem_NP :
    FO.Ordered.Query.encodedLanguage {M : FO.Ordered.Structure L | Φ.Realize M} v ∈
      NP encStructure := by
  classical
  let ℓ : Layout Φ := Classical.choice inferInstance
  obtain ⟨V, hV, hverifies, _⟩ := ℓ.exists_orderedVerifier v
  exact ⟨ℓ.polynomial, V, hV, hverifies⟩

end ESO.Sentence

namespace FO.Ordered

/-- Every existential second-order definable ordered query has its source-only encoded language
in native nondeterministic polynomial time. No invariance under permutations is required. -/
theorem ESODefinable.encodedLanguage_mem_NP {L : Language} [L.IsRelational] (v : Vocabulary L)
    {K : Query L} (hK : ESODefinable K) : K.encodedLanguage v ∈ NP encStructure := by
  obtain ⟨Φ, hΦ⟩ := hK
  have hK' : K = {M : Ordered.Structure L | Φ.Realize M} := Set.ext hΦ
  rw [hK']
  exact Φ.ordered_queryLanguage_mem_NP v

/-- **Ordered Fagin characterization:** arbitrary queries of canonically ordered finite
structures are ESO-definable exactly when their source-only encoded languages are in native
`NP`. The universe has at least two elements and malformed relation tables are rejected. -/
theorem esoDefinable_iff_encodedLanguage_mem_NP {L : Language} [L.IsRelational]
    (v : Vocabulary L) (K : Query L) : ESODefinable K ↔ K.encodedLanguage v ∈ NP encStructure :=
  ⟨ESODefinable.encodedLanguage_mem_NP v, ESODefinable.of_queryLanguage_mem_NP v⟩

end FO.Ordered

end Cslib.Logic
