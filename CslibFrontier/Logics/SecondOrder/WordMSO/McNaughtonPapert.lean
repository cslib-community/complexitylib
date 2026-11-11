/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.SecondOrder.WordMSO.Composition
public import CslibFrontier.Logics.SecondOrder.WordMSO.StarFree

/-!
# First-order definable languages are star-free (McNaughton–Papert)

Over a finite alphabet, every first-order definable language of finite words is star-free. With
`IsStarFree.foDefinable` this gives the **McNaughton–Papert theorem**, `foDefinable_iff_isStarFree`:
over a finite alphabet, a language is first-order definable (in `FO[<]` with letter predicates) if
and only if it is star-free [Libkin, Theorem 7.26][Libkin2004], [McNaughtonPapert1971].

The proof is an adaptation of the second half of the proof of [Libkin, Theorem 7.26][Libkin2004]
(pp. 128–129), by induction on the quantifier rank: every class of rank-`n` equivalence of words
(`rankTypeLanguage`) is star-free. A sentence of quantifier rank `n` defines a union of such classes
(`WordDuplicatorWins.mem_language_iff`), and over a finite alphabet there are finitely many of them,
so its language is star-free.

* Rank `0`. Without pebbles there is nothing to compare, so all words are rank-`0` equivalent and
  a class is empty or everything.
* Rank `n + 1`. Two words are rank-`(n + 1)` equivalent exactly when the same rank-`n` types of
  one-pebble extensions occur in both. So a class is a finite Boolean combination of the languages
  `pointedRankTypeLanguage n τ` of the words with a position of rank-`n` type `τ`.
  Each such language is a finite union of products `L(T₁) · {c} · L(T₂)` of classes of rank `n`
  and a letter: the type of a position `p` of `w = u₁ · c · u₂` (where `p = |u₁|` and `c = w[p]`)
  depends only on `c` and on the rank-`n` types of `u₁` and `u₂`
  (`WordDuplicatorWins.append_cons`).

**Adaptation.** Libkin inducts on the quantifier rank of sentences. He expands the vocabulary by a
constant `max` and writes the language of `∃x φ` as a union of products `L(Ψᵢ) · L(Ψⱼ)` over the
pairs of rank-`k` types of the prefix up to the quantified position `p` and the suffix after `p`,
where `Ψᵢ` defines the `i`-th type. Here the word is split as `u₁ · c · u₂` around the quantified
position instead, which needs no change of vocabulary. The induction runs over the classes of
rank-`n` equivalence rather than over sentences, so no formulas defining types are needed.

The finite alphabet is necessary: over an infinite alphabet `{ε}` is first-order definable but not
star-free (`exists_foDefinable_not_isStarFree`).

## Main definitions

* `Cslib.Logic.WordMSO.rankTypeLanguage`: the words of a given rank-`n` type.
* `Cslib.Logic.WordMSO.pointedRankTypeLanguage`: the words with a position of a given rank-`n`
  type of one-pebble extensions.

## Main results

* `Cslib.Logic.WordMSO.isStarFree_rankTypeLanguage`: over a finite alphabet, each class of
  rank-`n` equivalence of words is star-free.
* `Cslib.Logic.WordMSO.WordFO.isStarFree_language`, `Cslib.Logic.WordMSO.FODefinable.isStarFree`:
  over a finite alphabet, first-order definable languages are star-free.
* `Cslib.Logic.WordMSO.foDefinable_iff_isStarFree`: **the McNaughton–Papert theorem**.

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Theorem 7.26
* [R. McNaughton and S. Papert, *Counter-Free Automata*][McNaughtonPapert1971]
-/

public section

universe u

namespace Cslib.Logic.WordMSO

open Cslib.Language

variable {α : Type u}

/-- The words of rank-`n` type `T`: a class of rank-`n` equivalence of words. -/
def rankTypeLanguage (n : ℕ) (T : FO.RankType (wordLanguage α) n 0) : _root_.Language α :=
  {w | wordRankType n w Fin.elim0 = T}

/-- The words with a position `p` whose one-pebble extension has rank-`n` type `τ`. -/
def pointedRankTypeLanguage (n : ℕ) (τ : FO.RankType (wordLanguage α) n 1) :
    _root_.Language α :=
  {w | ∃ p : Fin w.length, wordRankType n w ![p] = τ}

/-- Equal words, with the same pebbles transported along the equality, have the same rank
type. -/
theorem wordRankType_congr {u v : List α} (h : u = v) (n : ℕ) {k : ℕ}
    (a : Fin k → Fin u.length) :
    wordRankType n u a = wordRankType n v fun i => Fin.cast (congrArg List.length h) (a i) := by
  subst h
  rfl

/-- The pointed words `(u₁ · c · u₂, |u₁|)` of a rank-`n` type: the type depends only on the letter
`c` and the rank-`n` types of `u₁` and `u₂`. -/
theorem wordRankType_append_cons {n : ℕ} {u₁ u₂ v₁ v₂ : List α} (c : α)
    (h₁ : wordRankType n u₁ Fin.elim0 = wordRankType n v₁ Fin.elim0)
    (h₂ : wordRankType n u₂ Fin.elim0 = wordRankType n v₂ Fin.elim0) :
    wordRankType n (u₁ ++ c :: u₂) ![⟨u₁.length, by simp⟩] =
      wordRankType n (v₁ ++ c :: v₂) ![⟨v₁.length, by simp⟩] :=
  wordRankType_eq_iff.2 <|
    WordDuplicatorWins.append_cons c (wordRankType_eq_iff.1 h₁) (wordRankType_eq_iff.1 h₂)

/-- The triples `(T₁, c, T₂)` that produce the one-pebble type `τ`: some (equivalently, every)
words `u₁` of type `T₁` and `u₂` of type `T₂` give `(u₁ · c · u₂, |u₁|)` the type `τ`. -/
def ProducesType (n : ℕ) (τ : FO.RankType (wordLanguage α) n 1)
    (t : FO.RankType (wordLanguage α) n 0 × α × FO.RankType (wordLanguage α) n 0) : Prop :=
  ∃ u₁ u₂ : List α, wordRankType n u₁ Fin.elim0 = t.1 ∧ wordRankType n u₂ Fin.elim0 = t.2.2 ∧
    wordRankType n (u₁ ++ t.2.1 :: u₂) ![⟨u₁.length, by simp⟩] = τ

/-- **Splitting at the pebbled position.** The words with a position of one-pebble type `τ` are
the union of the products `L(T₁) · {c} · L(T₂)` over the triples producing `τ`. -/
theorem pointedRankTypeLanguage_eq (n : ℕ) (τ : FO.RankType (wordLanguage α) n 1) :
    pointedRankTypeLanguage n τ =
      ⨆ t : {t // ProducesType n τ t},
        rankTypeLanguage n t.1.1 * {[t.1.2.1]} * rankTypeLanguage n t.1.2.2 := by
  ext x
  rw [Language.mem_iSup]
  constructor
  · rintro ⟨p, hp⟩
    have hx : x = x.take p ++ x[p] :: x.drop (p + 1) := by
      rw [Fin.getElem_fin, ← List.drop_eq_getElem_cons, List.take_append_drop]
    refine ⟨⟨(wordRankType n (x.take p) Fin.elim0, x[p],
      wordRankType n (x.drop (p + 1)) Fin.elim0), x.take p, x.drop (p + 1), rfl, rfl, ?_⟩, ?_⟩
    · rw [← hp, wordRankType_congr hx.symm]
      congr 1
      funext i
      exact Fin.ext (by simp [Matrix.cons_val_fin_one])
    · refine Language.mem_mul.2 ⟨x.take p ++ [x[p]], Language.mem_mul.2
        ⟨x.take p, rfl, [x[p]], rfl, rfl⟩, x.drop (p + 1), rfl, ?_⟩
      rw [List.append_assoc]
      exact hx.symm
  · rintro ⟨⟨⟨T₁, c, T₂⟩, u₁, u₂, hu₁, hu₂, hτ⟩, hx⟩
    obtain ⟨y, hy, y₂, hy₂, rfl⟩ := Language.mem_mul.1 hx
    obtain ⟨y₁, hy₁, c', hc', rfl⟩ := Language.mem_mul.1 hy
    change c' = [c] at hc'
    subst hc'
    have hx : y₁ ++ c :: y₂ = y₁ ++ [c] ++ y₂ := by simp
    refine ⟨⟨y₁.length, by simp⟩, ?_⟩
    rw [← hτ, wordRankType_congr hx.symm]
    refine Eq.trans ?_ (wordRankType_append_cons c (hy₁.trans hu₁.symm) (hy₂.trans hu₂.symm))
    congr 1
    funext i
    exact Fin.ext (by simp [Matrix.cons_val_fin_one])

theorem mem_rankTypeLanguage {n : ℕ} {T : FO.RankType (wordLanguage α) n 0} {w : List α} :
    w ∈ rankTypeLanguage n T ↔ wordRankType n w Fin.elim0 = T :=
  Iff.rfl

theorem mem_pointedRankTypeLanguage {n : ℕ} {τ : FO.RankType (wordLanguage α) n 1}
    {w : List α} :
    w ∈ pointedRankTypeLanguage n τ ↔ ∃ p : Fin w.length, wordRankType n w ![p] = τ :=
  Iff.rfl

private theorem snoc_elim0 {β : Type*} (x : β) : (Fin.snoc Fin.elim0 x : Fin 1 → β) = ![x] := by
  rw [Fin.snoc_zero, Matrix.vec_single_eq_const]

/-- Rank-`0` equivalence relates all words: without pebbles there is nothing to compare. -/
theorem wordRankType_zero_eq (u v : List α) :
    wordRankType 0 u Fin.elim0 = wordRankType 0 v Fin.elim0 :=
  wordRankType_eq_iff.2 <| WordDuplicatorWins.zero_iff.2 <|
    wordStructure.partialIso_iff.2 ⟨fun i => i.elim0, fun i => i.elim0⟩

/-- Rank-`(n + 1)` equivalence of words is agreement on the rank-`n` types of the one-pebble
extensions: `v` and `w` are rank-`(n + 1)` equivalent exactly when they lie in the same
languages `pointedRankTypeLanguage n τ`. -/
theorem wordRankType_succ_eq_iff {n : ℕ} {v w : List α} :
    wordRankType (n + 1) v Fin.elim0 = wordRankType (n + 1) w Fin.elim0 ↔
      ∀ τ, v ∈ pointedRankTypeLanguage n τ ↔ w ∈ pointedRankTypeLanguage n τ := by
  rw [wordRankType_eq_iff, WordDuplicatorWins.succ_iff]
  constructor
  · rintro ⟨-, hf, hb⟩ τ
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨q, hq⟩ := hf p
      rw [snoc_elim0, snoc_elim0] at hq
      exact ⟨q, (wordRankType_eq_iff.2 hq).symm⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨p, hp⟩ := hb q
      rw [snoc_elim0, snoc_elim0] at hp
      exact ⟨p, wordRankType_eq_iff.2 hp⟩
  · intro h
    refine ⟨wordStructure.partialIso_iff.2 ⟨fun i => i.elim0, fun i => i.elim0⟩, fun p => ?_,
      fun q => ?_⟩
    · obtain ⟨q, hq⟩ := (h (wordRankType n v ![p])).1 ⟨p, rfl⟩
      refine ⟨q, ?_⟩
      rw [snoc_elim0, snoc_elim0]
      exact wordRankType_eq_iff.1 hq.symm
    · obtain ⟨p, hp⟩ := (h (wordRankType n w ![q])).2 ⟨q, rfl⟩
      refine ⟨p, ?_⟩
      rw [snoc_elim0, snoc_elim0]
      exact wordRankType_eq_iff.1 hp

variable [Finite α]

/-- If the classes of rank-`n` equivalence are star-free, so are the languages of the words with a
position of a given one-pebble rank-`n` type: they are finite unions of products of classes and
letters (`pointedRankTypeLanguage_eq`). -/
theorem isStarFree_pointedRankTypeLanguage {n : ℕ}
    (ih : ∀ T, IsStarFree (rankTypeLanguage (α := α) n T)) (τ : FO.RankType (wordLanguage α) n 1) :
    IsStarFree (pointedRankTypeLanguage n τ) := by
  rw [pointedRankTypeLanguage_eq]
  exact IsStarFree.iSup fun t => ((ih _).mul (.char _)).mul (ih _)

/-- **Classes of rank-`n` equivalence are star-free** over a finite alphabet, by induction on `n`.
A class of rank `0` is empty or everything, and a nonempty class of rank `n + 1`, of a word `w`, is
the intersection over the one-pebble types `τ` of the language of words with a position of type
`τ`, or of its complement, according as `w` has such a position. -/
theorem isStarFree_rankTypeLanguage (n : ℕ) (T : FO.RankType (wordLanguage α) n 0) :
    IsStarFree (rankTypeLanguage n T) := by
  classical
  induction n with
  | zero =>
    by_cases hT : ∃ w, w ∈ rankTypeLanguage 0 T
    · obtain ⟨w, hw⟩ := hT
      have : rankTypeLanguage 0 T = ⊤ := by
        ext v
        exact iff_of_true ((wordRankType_zero_eq v w).trans hw) trivial
      rw [this]
      exact IsStarFree.top
    · have : rankTypeLanguage 0 T = 0 := by
        ext v
        exact iff_of_false (fun hv => hT ⟨v, hv⟩) (Language.notMem_zero v)
      rw [this]
      exact IsStarFree.zero
  | succ n ih =>
    by_cases hT : ∃ w, w ∈ rankTypeLanguage (n + 1) T
    · obtain ⟨w, hw⟩ := hT
      have : rankTypeLanguage (n + 1) T = ⨅ τ, if w ∈ pointedRankTypeLanguage n τ then
          pointedRankTypeLanguage n τ else (pointedRankTypeLanguage n τ)ᶜ := by
        ext v
        refine (mem_rankTypeLanguage.trans ?_).trans Set.mem_iInter.symm
        rw [← mem_rankTypeLanguage.1 hw, wordRankType_succ_eq_iff]
        refine forall_congr' fun τ => ?_
        split_ifs with h
        · exact ⟨fun hv => hv.2 h, fun hv => iff_of_true hv h⟩
        · exact ⟨fun hv hv' => h (hv.1 hv'), fun hv => iff_of_false hv h⟩
      rw [this]
      refine IsStarFree.iInf fun τ => ?_
      split_ifs
      · exact isStarFree_pointedRankTypeLanguage ih τ
      · exact (isStarFree_pointedRankTypeLanguage ih τ).compl
    · have : rankTypeLanguage (n + 1) T = 0 := by
        ext v
        exact iff_of_false (fun hv => hT ⟨v, hv⟩) (Language.notMem_zero v)
      rw [this]
      exact IsStarFree.zero

/-- **First-order definable languages are star-free** over a finite alphabet
[Libkin, Theorem 7.26][Libkin2004]. The language of a sentence of quantifier rank `n` is the union
of the classes of rank-`n` equivalence that it meets, finitely many star-free languages. -/
theorem WordFO.isStarFree_language (φ : (wordLanguage α).Sentence) :
    IsStarFree (WordFO.language φ) := by
  have h : WordFO.language φ = ⨆ T : {T // ∃ w ∈ WordFO.language φ,
      wordRankType (FO.quantifierRank φ) w Fin.elim0 = T}, rankTypeLanguage _ T.1 := by
    ext v
    rw [Language.mem_iSup]
    constructor
    · intro hv
      exact ⟨⟨_, v, hv, rfl⟩, rfl⟩
    · rintro ⟨⟨T, w, hw, rfl⟩, hv⟩
      exact ((wordRankType_eq_iff.1 hv).mem_language_iff le_rfl).2 hw
  rw [h]
  exact IsStarFree.iSup fun T => isStarFree_rankTypeLanguage _ _

/-- **First-order definable languages are star-free** over a finite alphabet: the hard direction
of the McNaughton–Papert theorem [Libkin, Theorem 7.26][Libkin2004]. -/
theorem FODefinable.isStarFree {L : _root_.Language α} (h : FODefinable L) : IsStarFree L := by
  obtain ⟨φ, rfl⟩ := foDefinable_iff_exists_sentence.1 h
  exact WordFO.isStarFree_language φ

/-- **The McNaughton–Papert theorem** [Libkin, Theorem 7.26][Libkin2004], [McNaughtonPapert1971].
Over a finite alphabet, a language is first-order definable if and only if it is star-free. The
finite alphabet is necessary (`exists_foDefinable_not_isStarFree`). -/
theorem foDefinable_iff_isStarFree {L : _root_.Language α} : FODefinable L ↔ IsStarFree L :=
  ⟨FODefinable.isStarFree, IsStarFree.foDefinable⟩

end Cslib.Logic.WordMSO
