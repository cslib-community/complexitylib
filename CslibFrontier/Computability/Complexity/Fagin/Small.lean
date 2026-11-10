/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Basic
public import CslibFrontier.Logics.FirstOrder.Encoding
public import CslibFrontier.Logics.SecondOrder.Projection

/-!
# Small structures and cardinality splitting

In Fagin's theorem, the Cook–Levin tableau of a verifier is encoded by `k`-tuples over the domain
`M`. When `Nat.card M ≥ 2`, `n ^ k` grows large enough to index the tableau's time steps and tape
positions; when `Nat.card M ≤ 1`, `n ^ k ≤ 1` cannot.

Over a fixed finite relational vocabulary `v : Vocabulary L`, however, there are only finitely many
isomorphism classes of structures of cardinality `0` or `1`: every relation table has length
`n ^ a ≤ 1`, so an isomorphism-closed class `K` restricted to `Nat.card M ≤ 1` is determined by a
finite Boolean table of first-order sentences and is therefore first-order definable
(`FO.Definable.inter_card_le_one`). Combining this with Mathlib's `Sentence.cardGe L 2` reduces
existential second-order definability of any isomorphism-closed class `K` to agreeing with `K` on
finite structures of cardinality at least `2` (`ESO.Definable.of_card_ge_two`).

## Main definitions

* `Cslib.Logic.Vocabulary.nullarySymbolSentence`, `Cslib.Logic.Vocabulary.constTupleSentence`:
  first-order sentences reading the single bit of each nullary or singleton relation table.
* `Cslib.Logic.Vocabulary.encodeOfZero`, `Cslib.Logic.Vocabulary.encodeOfOne`: the canonical
  `EncodedStructure` of cardinality `0` or `1` with given single-bit tables.

## Main results

* `Cslib.Logic.FO.Definable.inter_card_le_one`: for any isomorphism-closed class `K` over a finite
  relational vocabulary, `{M ∈ K | Nat.card M ≤ 1}` is first-order definable.
* `Cslib.Logic.ESO.Definable.of_card_ge_two`: to show `ESO.Definable K` for an isomorphism-closed
  class `K`, it suffices to exhibit an `ESO.Sentence` that agrees with `K` on finite structures with
  `2 ≤ Nat.card M`.
* `Cslib.Logic.ESO.Definable.of_withLinearOrder_card_ge_two`: to show `ESO.Definable K` for an
  isomorphism-closed class `K`, it suffices to exhibit an `ESO.Sentence (L.sum orderLanguage)` that
  agrees with `K` on finite structures with `2 ≤ Nat.card M` under every numbering.

## References

* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

universe u v w

open FirstOrder Language Structure CategoryTheory BoundedFormula

namespace Cslib.Logic

variable {L : Language.{u, v}}

/-! ### Small structures over a finite vocabulary -/

namespace Vocabulary

variable (v : Vocabulary L)

/-- The sentence testing whether a relation symbol `r` is nullary and holds on the empty tuple. -/
def nullaryRelSentence : (Σ n, L.Relations n) → L.Sentence
  | ⟨0, r⟩ => Relations.boundedFormula r finZeroElim
  | ⟨_ + 1, _⟩ => ⊥

/-- The sentence testing whether the `i`-th symbol of `v` is nullary and holds on the empty
tuple. -/
def nullarySymbolSentence (i : Fin v.count) : L.Sentence :=
  nullaryRelSentence (v.symbol i)

/-- The sentence testing whether a relation symbol `r` holds on every constant tuple
`fun _ => x`. -/
def constTupleRelSentence (r : Σ n, L.Relations n) : L.Sentence :=
  ∀' Relations.boundedFormula r.2 (fun _ => &0)

/-- The sentence testing whether the `i`-th symbol of `v` holds on every constant tuple
`fun _ => x`. In a singleton structure this is the single bit of the symbol's relation table. -/
def constTupleSentence (i : Fin v.count) : L.Sentence :=
  constTupleRelSentence (v.symbol i)

/-- The `EncodedStructure` of cardinality `0` whose nullary tables are given by `s`. -/
def encodeOfZero (s : Fin v.count → Bool) : EncodedStructure :=
  (0, List.ofFn fun i : Fin v.count => if (v.symbol i).1 = 0 then [s i] else [])

/-- The `EncodedStructure` of cardinality `1` whose singleton tables are given by `s`. -/
def encodeOfOne (s : Fin v.count → Bool) : EncodedStructure :=
  (1, List.ofFn fun i : Fin v.count => [s i])

open scoped Classical in
private theorem relTable_eq_of_equiv_fin_zero {N : Type} [L.Structure N] (e : N ≃ Fin 0)
    (r : Σ n, L.Relations n) :
    Vocabulary.relTable N e r =
      if r.1 = 0 then [decide (N ⊨ nullaryRelSentence r)] else [] := by
  rcases r with ⟨_ | k, r⟩
  · simp only [↓reduceIte, nullaryRelSentence]
    refine List.ext_getElem (by simp [Vocabulary.relTable]) fun j hj₁ hj₂ => ?_
    simp only [Vocabulary.relTable, List.getElem_ofFn, List.getElem_singleton]
    refine decide_eq_decide.2 ?_
    change RelMap r (e.symm ∘ finFunctionFinEquiv.symm ⟨j, _⟩) ↔
      RelMap r fun k : Fin 0 => _
    exact iff_of_eq (congrArg (RelMap r) (funext fun k => k.elim0))
  · simp [Vocabulary.relTable]

open scoped Classical in
private theorem encode_eq_encodeOfZero {N : Type} [L.Structure N] (e : N ≃ Fin 0) :
    v.encode N e = v.encodeOfZero (fun i => decide (N ⊨ v.nullarySymbolSentence i)) := by
  refine Prod.ext rfl (congrArg List.ofFn (funext fun i => ?_))
  exact relTable_eq_of_equiv_fin_zero e (v.symbol i)

open scoped Classical in
private theorem relTable_eq_of_equiv_fin_one {N : Type} [L.Structure N] (e : N ≃ Fin 1)
    (r : Σ n, L.Relations n) :
    Vocabulary.relTable N e r = [decide (N ⊨ constTupleRelSentence r)] := by
  refine List.ext_getElem (by simp [Vocabulary.relTable]) fun j hj₁ hj₂ => ?_
  have hj' : j < 1 ^ r.1 := by simpa [Vocabulary.relTable] using hj₁
  simp only [Vocabulary.relTable, List.getElem_ofFn, List.getElem_singleton]
  refine decide_eq_decide.2 ?_
  have hrel : (N ⊨ constTupleRelSentence r) ↔ ∀ x : N, RelMap r.2 (fun _ => x) := by
    simp [constTupleRelSentence, Sentence.Realize, Formula.Realize, Fin.snoc]
  rw [hrel]
  constructor
  · intro h x
    have hx : (fun _ : Fin r.1 => x) = e.symm ∘ finFunctionFinEquiv.symm ⟨j, hj'⟩ := by
      funext k
      exact e.injective (Subsingleton.elim _ _)
    rwa [hx]
  · intro h
    have hx : (e.symm ∘ finFunctionFinEquiv.symm ⟨j, hj'⟩) = fun _ : Fin r.1 => e.symm 0 := by
      funext k
      exact e.injective (Subsingleton.elim _ _)
    rw [hx]
    exact h (e.symm 0)

open scoped Classical in
private theorem encode_eq_encodeOfOne {N : Type} [L.Structure N] (e : N ≃ Fin 1) :
    v.encode N e = v.encodeOfOne (fun i => decide (N ⊨ v.constTupleSentence i)) := by
  refine Prod.ext rfl (congrArg List.ofFn (funext fun i => ?_))
  exact relTable_eq_of_equiv_fin_one e (v.symbol i)

end Vocabulary

namespace FO

variable [L.IsRelational] (v : Vocabulary L)

open scoped Classical in
/-- If every structure of cardinality `n` encodes as `enc` applied to the truth values of the
sentences `φ i`, then the restriction of an isomorphism-closed class `K` to cardinality `n` is
first-order definable: the sentence checks the cardinality and looks up the truth table. -/
private theorem Definable.inter_card_eq_of_encode {K : Set (Bundled.{0} L.Structure)}
    (hK : IsoClosed K) (n : ℕ) {m : ℕ} (φ : Fin m → L.Sentence)
    (enc : (Fin m → Bool) → EncodedStructure)
    (henc : ∀ {N : Type} [L.Structure N] (e : N ≃ Fin n),
      v.encode N e = enc fun i => decide (N ⊨ φ i)) :
    Definable {M : Bundled.{0} L.Structure | M ∈ K ∧ Nat.card M = n} := by
  refine ⟨cardEqSentence L n ⊓ truthTableSentence φ (fun s => v.decoded (enc s) ∈ K),
    fun M _ => ?_⟩
  rw [Sentence.realize_inf, realize_cardEqSentence, realize_truthTableSentence, Set.mem_ofPred_eq,
    and_comm]
  refine and_congr_right fun hn => ?_
  have e : M ≃ Fin n := hn ▸ Finite.equivFin M
  rw [← henc e]
  exact hK (v.decodeEncodeEquiv M e)

include v in
/-- For any isomorphism-closed class `K` over a finite relational vocabulary, the restriction of
`K` to structures of cardinality at most `1` is first-order definable. -/
theorem Definable.inter_card_le_one {K : Set (Bundled.{0} L.Structure)} (hK : IsoClosed K) :
    Definable {M : Bundled.{0} L.Structure | M ∈ K ∧ Nat.card M ≤ 1} := by
  have heq : {M : Bundled.{0} L.Structure | M ∈ K ∧ Nat.card M ≤ 1} =
      {M : Bundled.{0} L.Structure | M ∈ K ∧ Nat.card M = 0} ∪
        {M : Bundled.{0} L.Structure | M ∈ K ∧ Nat.card M = 1} := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · rintro ⟨hM, hle⟩
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle with h | h
      · exact Or.inl ⟨hM, h⟩
      · exact Or.inr ⟨hM, h⟩
    · rintro (⟨hM, h0⟩ | ⟨hM, h1⟩) <;> exact ⟨hM, by omega⟩
  rw [heq]
  -- Cardinality `0` is read off the nullary tables, cardinality `1` off the constant tuples.
  exact (Definable.inter_card_eq_of_encode v hK 0 v.nullarySymbolSentence v.encodeOfZero
      v.encode_eq_encodeOfZero).union
    (Definable.inter_card_eq_of_encode v hK 1 v.constTupleSentence v.encodeOfOne
      v.encode_eq_encodeOfOne)

end FO

namespace ESO

variable [L.IsRelational]

/-- To prove that an isomorphism-closed class `K` over a finite relational vocabulary is
existential second-order definable, it suffices to exhibit an existential second-order sentence
`Φ` that agrees with `K` on finite structures of cardinality at least `2`. -/
theorem Definable.of_card_ge_two (v : Vocabulary L) {K : Set (Bundled.{0} L.Structure)}
    (hK : IsoClosed K) (Φ : Sentence L)
    (hΦ : ∀ (M : Bundled.{0} L.Structure) [Finite M], 2 ≤ Nat.card M → (M ∈ K ↔ Φ.Realize M)) :
    Definable K := by
  obtain ⟨φ_small, hsmall⟩ := FO.Definable.inter_card_le_one v hK
  refine ⟨Sentence.ofSentence φ_small ⊔ (Sentence.ofSentence (Sentence.cardGe L 2) ⊓ Φ),
    fun M _ => ?_⟩
  rw [Sentence.realize_sup, Sentence.realize_ofSentence, Sentence.realize_inf,
    Sentence.realize_ofSentence, FO.realize_cardGe_iff_le_card, ← hsmall M]
  change M ∈ K ↔ (M ∈ K ∧ Nat.card M ≤ 1) ∨ (2 ≤ Nat.card M ∧ Φ.Realize M)
  by_cases h2 : 2 ≤ Nat.card M
  · rw [hΦ M h2]
    exact ⟨fun h => Or.inr ⟨h2, h⟩, fun h => h.elim (fun ⟨_, hle⟩ => by omega) And.right⟩
  · have hle : Nat.card M ≤ 1 := by omega
    exact ⟨fun h => Or.inl ⟨h, hle⟩, fun h => h.elim And.left fun ⟨hge, _⟩ => by omega⟩

/-- To prove that an isomorphism-closed class `K` over a finite relational vocabulary is
existential second-order definable, it suffices to exhibit an existential second-order sentence
`Φ` over `L.sum orderLanguage` that agrees with `K` on finite structures of cardinality at least `2`
under every numbering `e : M ≃ Fin (Nat.card M)`. -/
theorem Definable.of_withLinearOrder_card_ge_two (v : Vocabulary L)
    {K : Set (Bundled.{0} L.Structure)} (hK : IsoClosed K)
    (Φ : Sentence (L.sum orderLanguage))
    (hΦ : ∀ (M : Bundled.{0} L.Structure) [Finite M] (e : M ≃ Fin (Nat.card M)),
      2 ≤ Nat.card M →
        (M ∈ K ↔
          letI := varLanguage.structure (arity := fun _ : Unit => 2) (orderRelOfEquiv e)
          Φ.Realize M)) :
    Definable K := by
  refine Definable.of_card_ge_two v hK Φ.withLinearOrder fun M _ h2 => ?_
  rw [Sentence.realize_withLinearOrder]
  exact ⟨fun hM => ⟨Finite.equivFin M, (hΦ M (Finite.equivFin M) h2).1 hM⟩,
    fun ⟨e, h⟩ => (hΦ M e h2).2 h⟩

end ESO

end Cslib.Logic
