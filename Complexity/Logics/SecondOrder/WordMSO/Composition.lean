/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.List.Equiv
public import Complexity.Logics.SecondOrder.WordMSO.FirstOrder
public import Complexity.Logics.FirstOrder.EhrenfeuchtFraisse.Hintikka
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.GroupTheory.Congruence.Hom

/-!
# Ehrenfeucht–Fraïssé games on concatenations of words

This module shows that Duplicator's winning strategies on the factors of two concatenations combine
into a winning strategy on the concatenations. If Duplicator wins the `n`-round
Ehrenfeucht–Fraïssé game on the words `u₁, v₁` from the pebbles `(a₁, b₁)` and on `u₂, v₂` from
`(a₂, b₂)`, then she wins it on `u₁ ++ u₂, v₁ ++ v₂` from the combined pebbles
(`WordDuplicatorWins.append`). Her strategy answers each move of Spoiler in the factor where he
played. Every position of the first factor precedes every position of the second, in both words, so
the combined position stays a partial isomorphism. This is the composition argument of
[Libkin, Lemma 3.7 and §7.4][Libkin2004]: Lemma 3.7 composes games on the two sides of a pebble in
a linear order, and §7.4, p. 126, states the corresponding fact for concatenations of words, for
the monadic second-order game.

The game on words is this library's first-order game `Cslib.Logic.FO.DuplicatorWins`, stated over
Mathlib's model theory, on the word vocabulary `wordLanguage α` interpreted by `wordStructure`.
`WordDuplicatorWins` supplies the two word structures explicitly, because `Fin u.length` does not
determine `u` (`wordDuplicatorWins_iff` unfolds it). On word structures a position is a partial
isomorphism exactly when it preserves and reflects the order and the letters
(`wordStructure.partialIso_iff`). The positions of `u ++ v` are those of `u` followed by those of
`v` (`List.appendIndexEquiv`).

Two consequences are recorded:

* `WordDuplicatorWins.append_cons`: one pebble on an inserted letter. If `u₁ ≡ₙ v₁` and
  `u₂ ≡ₙ v₂`, then `u₁ ++ c :: u₂` with a pebble on `c` and `v₁ ++ c :: v₂` with a pebble on `c`
  are `n`-equivalent. A first-order formula `∃x φ` over a word therefore depends only on the
  rank-`n` types of the factors around the position `x`. The converse of the McNaughton–Papert
  theorem, that FO[<] languages are star-free over a finite alphabet, uses this decomposition
  `w = u₁ · c · u₂`.
* `wordCon α n`: rank-`n` equivalence of words, `wordRankType n u = wordRankType n v`, is a
  congruence of the free monoid. Over a finite alphabet it has finite index
  (`wordCon.finite_quotient`). A sentence of quantifier rank at most `n` defines a union of its
  classes (`mem_language_iff_of_wordCon`), so its language is the preimage of a set of classes
  under the quotient map (`wordCon_preimage_image_language`): it is recognized by a finite
  monoid.

## Main definitions

* `Cslib.Logic.WordMSO.WordDuplicatorWins`: Duplicator wins the `n`-round game on two word
  structures from a position.
* `Cslib.Logic.WordMSO.wordRankType`: the rank-`n` type of a word with pebbles.
* `Cslib.Logic.WordMSO.wordCon`: rank-`n` equivalence of words as a congruence of the free monoid.

## Main results

* `Cslib.Logic.WordMSO.wordStructure.partialIso_iff`: partial isomorphisms of word structures.
* `Cslib.Logic.WordMSO.wordDuplicatorWins_iff`, `Cslib.Logic.WordMSO.wordRankType_eq_rankType`:
  the word game and word rank types are the library's game and rank types on word structures.
* `Cslib.Logic.WordMSO.WordDuplicatorWins.append`: **composition of games for concatenation**.
* `Cslib.Logic.WordMSO.WordDuplicatorWins.append_elim0`,
  `Cslib.Logic.WordMSO.WordDuplicatorWins.append_cons`: the forms without pebbles and with one
  pebble on an inserted letter.
* `Cslib.Logic.WordMSO.WordDuplicatorWins.realize_iff`,
  `Cslib.Logic.WordMSO.WordDuplicatorWins.mem_language_iff`: winning positions satisfy the same
  formulas and sentences of bounded quantifier rank.
* `Cslib.Logic.WordMSO.wordRankType_eq_iff`: equal rank types are winning positions.
* `Cslib.Logic.WordMSO.wordCon.finite_quotient`, `Cslib.Logic.WordMSO.mem_language_iff_of_wordCon`,
  `Cslib.Logic.WordMSO.wordCon_preimage_image_language`: over a finite alphabet, rank-`n`
  equivalence has finite index, and the language of a sentence of quantifier rank `n` is a union of
  its classes.

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Lemma 3.7, §7.4 and Theorem 7.26.
-/

public section

open FirstOrder Language Structure

universe u

namespace Cslib.Logic.WordMSO

variable {α : Type u}

/-! ### The game on words -/

/-- Duplicator wins the `n`-round Ehrenfeucht–Fraïssé game on the word structures of `u` and `v`
from the pebbles `(a, b)`. This is `Cslib.Logic.FO.DuplicatorWins` with the word structures
`wordStructure u` and `wordStructure v` supplied explicitly. -/
def WordDuplicatorWins (n : ℕ) (u v : List α) {k : ℕ} (a : Fin k → Fin u.length)
    (b : Fin k → Fin v.length) : Prop :=
  @FO.DuplicatorWins (wordLanguage α) (Fin u.length) (Fin v.length) (wordStructure u)
    (wordStructure v) n k a b

/-- `WordDuplicatorWins` is the game `Cslib.Logic.FO.DuplicatorWins` on the word structures. -/
theorem wordDuplicatorWins_iff {n : ℕ} {u v : List α} {k : ℕ} {a : Fin k → Fin u.length}
    {b : Fin k → Fin v.length} :
    WordDuplicatorWins n u v a b ↔
      @FO.DuplicatorWins (wordLanguage α) _ _ (wordStructure u) (wordStructure v) n k a b :=
  Iff.rfl

/-- A position of word structures is a partial isomorphism iff it preserves and reflects the
order and the letters. -/
theorem wordStructure.partialIso_iff {u v : List α} {k : ℕ} {a : Fin k → Fin u.length}
    {b : Fin k → Fin v.length} :
    @FO.PartialIso (wordLanguage α) _ _ (wordStructure u) (wordStructure v) k a b ↔
      (∀ i j, a i < a j ↔ b i < b j) ∧ ∀ i, u[a i] = v[b i] := by
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · have := @FO.PartialIso.relMap_iff (wordLanguage α) _ _ (wordStructure u) (wordStructure v)
        k a b h 2 wordLanguage.ltSymb ![i, j]
      rwa [wordStructure.relMap_ltSymb, wordStructure.relMap_ltSymb] at this
    · have := @FO.PartialIso.relMap_iff (wordLanguage α) _ _ (wordStructure u) (wordStructure v)
        k a b h 1 (wordLanguage.letterSymb u[a i]) ![i]
      rw [wordStructure.relMap_letterSymb, wordStructure.relMap_letterSymb] at this
      exact (this.1 rfl).symm
  · rintro ⟨hlt, hlet⟩
    refine @FO.PartialIso.mk (wordLanguage α) _ _ (wordStructure u) (wordStructure v) k a b
      (fun i j => ?_) (fun {l} R f => ?_)
    · simp only [le_antisymm_iff, ← not_lt, hlt]
    · cases R with
      | lt =>
        have h1 := wordStructure.relMap_ltSymb u (a ∘ f)
        have h2 := wordStructure.relMap_ltSymb v (b ∘ f)
        exact h1.trans ((hlt (f 0) (f 1)).trans h2.symm)
      | letter c =>
        have h1 := wordStructure.relMap_letterSymb u c (a ∘ f)
        have h2 := wordStructure.relMap_letterSymb v c (b ∘ f)
        refine h1.trans (Iff.trans ?_ h2.symm)
        change u[a (f 0)] = c ↔ v[b (f 0)] = c
        rw [hlet]

namespace WordDuplicatorWins

variable {u v w : List α}

theorem zero_iff {k : ℕ} {a : Fin k → Fin u.length} {b : Fin k → Fin v.length} :
    WordDuplicatorWins 0 u v a b ↔
      @FO.PartialIso (wordLanguage α) _ _ (wordStructure u) (wordStructure v) k a b :=
  @FO.duplicatorWins_zero (wordLanguage α) _ _ (wordStructure u) (wordStructure v) k a b

theorem succ_iff {n k : ℕ} {a : Fin k → Fin u.length} {b : Fin k → Fin v.length} :
    WordDuplicatorWins (n + 1) u v a b ↔
      @FO.PartialIso (wordLanguage α) _ _ (wordStructure u) (wordStructure v) k a b ∧
      (∀ c, ∃ d, WordDuplicatorWins n u v (Fin.snoc a c : Fin _ → _) (Fin.snoc b d : Fin _ → _)) ∧
      (∀ d, ∃ c, WordDuplicatorWins n u v (Fin.snoc a c : Fin _ → _) (Fin.snoc b d : Fin _ → _)) :=
  @FO.duplicatorWins_succ (wordLanguage α) _ _ (wordStructure u) (wordStructure v) n k a b

theorem partialIso {n k : ℕ} {a : Fin k → Fin u.length} {b : Fin k → Fin v.length}
    (h : WordDuplicatorWins n u v a b) :
    @FO.PartialIso (wordLanguage α) _ _ (wordStructure u) (wordStructure v) k a b :=
  @FO.DuplicatorWins.partialIso (wordLanguage α) _ _ (wordStructure u) (wordStructure v) n k a b h

theorem forth {n k : ℕ} {a : Fin k → Fin u.length} {b : Fin k → Fin v.length}
    (h : WordDuplicatorWins (n + 1) u v a b) (c : Fin u.length) :
    ∃ d, WordDuplicatorWins n u v (Fin.snoc a c : Fin _ → _) (Fin.snoc b d : Fin _ → _) :=
  @FO.DuplicatorWins.forth (wordLanguage α) _ _ (wordStructure u) (wordStructure v) n k a b h c

theorem back {n k : ℕ} {a : Fin k → Fin u.length} {b : Fin k → Fin v.length}
    (h : WordDuplicatorWins (n + 1) u v a b) (d : Fin v.length) :
    ∃ c, WordDuplicatorWins n u v (Fin.snoc a c : Fin _ → _) (Fin.snoc b d : Fin _ → _) :=
  @FO.DuplicatorWins.back (wordLanguage α) _ _ (wordStructure u) (wordStructure v) n k a b h d

theorem mono {m n k : ℕ} {a : Fin k → Fin u.length} {b : Fin k → Fin v.length} (hmn : m ≤ n)
    (h : WordDuplicatorWins n u v a b) : WordDuplicatorWins m u v a b :=
  @FO.DuplicatorWins.mono (wordLanguage α) _ _ (wordStructure u) (wordStructure v) m n k a b hmn h

theorem refl (n : ℕ) (u : List α) {k : ℕ} (a : Fin k → Fin u.length) :
    WordDuplicatorWins n u u a a :=
  @FO.DuplicatorWins.refl (wordLanguage α) _ (wordStructure u) n k a

theorem symm {n k : ℕ} {a : Fin k → Fin u.length} {b : Fin k → Fin v.length}
    (h : WordDuplicatorWins n u v a b) : WordDuplicatorWins n v u b a :=
  @FO.DuplicatorWins.symm (wordLanguage α) _ _ (wordStructure u) (wordStructure v) n k a b h

theorem trans {n k : ℕ} {a : Fin k → Fin u.length} {b : Fin k → Fin v.length}
    {c : Fin k → Fin w.length} (h₁ : WordDuplicatorWins n u v a b)
    (h₂ : WordDuplicatorWins n v w b c) : WordDuplicatorWins n u w a c :=
  @FO.DuplicatorWins.trans (wordLanguage α) _ _ _ (wordStructure u) (wordStructure v)
    (wordStructure w) n k a b c h₁ h₂

/-- Equal words, with the same pebbles transported along the equality, are winning positions. -/
theorem of_eq (h : u = v) (n : ℕ) {k : ℕ} (a : Fin k → Fin u.length) :
    WordDuplicatorWins n u v a fun i => Fin.cast (congrArg List.length h) (a i) := by
  subst h
  exact refl n u a

/-- **Ehrenfeucht–Fraïssé, easy direction, on words.** Winning positions of the `n`-round game
satisfy the same formulas of quantifier rank at most `n`, with the pebbles as the variables. -/
theorem realize_iff {n k : ℕ} {a : Fin k → Fin u.length} {b : Fin k → Fin v.length}
    (h : WordDuplicatorWins n u v a b) {φ : (wordLanguage α).BoundedFormula Empty k}
    (hφ : FO.quantifierRank φ ≤ n) :
    @BoundedFormula.Realize (wordLanguage α) _ (wordStructure u) _ _ φ default a ↔
      @BoundedFormula.Realize (wordLanguage α) _ (wordStructure v) _ _ φ default b :=
  @FO.DuplicatorWins.realize_iff (wordLanguage α) _ _ (wordStructure u) (wordStructure v)
    _ n k a b h φ hφ

/-- Two words on which Duplicator wins the `n`-round game without pebbles satisfy the same
sentences of quantifier rank at most `n`. -/
theorem mem_language_iff {n : ℕ} {a : Fin 0 → Fin u.length} {b : Fin 0 → Fin v.length}
    (h : WordDuplicatorWins n u v a b) {φ : (wordLanguage α).Sentence}
    (hφ : FO.quantifierRank φ ≤ n) : u ∈ WordFO.language φ ↔ v ∈ WordFO.language φ := by
  have := h.realize_iff hφ
  rwa [Subsingleton.elim a default, Subsingleton.elim b default] at this

end WordDuplicatorWins

/-! ### Composition -/

/-- Partial isomorphisms of the factors combine into a partial isomorphism of the concatenations.
Each pebble `i` of the combined position lies in the factor named by `σ i`. -/
theorem partialIso_append {u₁ u₂ v₁ v₂ : List α} {k₁ k₂ k : ℕ}
    {a₁ : Fin k₁ → Fin u₁.length} {b₁ : Fin k₁ → Fin v₁.length}
    {a₂ : Fin k₂ → Fin u₂.length} {b₂ : Fin k₂ → Fin v₂.length}
    (σ : Fin k → Fin k₁ ⊕ Fin k₂) {A : Fin k → Fin (u₁ ++ u₂).length}
    {B : Fin k → Fin (v₁ ++ v₂).length}
    (hA : ∀ i, A i = List.appendIndexEquiv u₁ u₂ ((σ i).map a₁ a₂))
    (hB : ∀ i, B i = List.appendIndexEquiv v₁ v₂ ((σ i).map b₁ b₂))
    (h₁ : @FO.PartialIso (wordLanguage α) _ _ (wordStructure u₁) (wordStructure v₁) k₁ a₁ b₁)
    (h₂ : @FO.PartialIso (wordLanguage α) _ _ (wordStructure u₂) (wordStructure v₂) k₂ a₂ b₂) :
    @FO.PartialIso (wordLanguage α) _ _ (wordStructure (u₁ ++ u₂)) (wordStructure (v₁ ++ v₂))
      k A B := by
  rw [wordStructure.partialIso_iff] at h₁ h₂ ⊢
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · rw [hA, hA, hB, hB, List.appendIndexEquiv_lt_iff, List.appendIndexEquiv_lt_iff]
    rcases σ i with i' | i' <;> rcases σ j with j' | j'
    · simp only [Sum.map_inl, Sum.lex_inl_inl]
      exact h₁.1 i' j'
    · exact iff_of_true (Sum.Lex.sep _ _) (Sum.Lex.sep _ _)
    · exact iff_of_false Sum.lex_inr_inl Sum.lex_inr_inl
    · simp only [Sum.map_inr, Sum.lex_inr_inr]
      exact h₂.1 i' j'
  · simp only [hA, hB]
    have key : ∀ x : Fin k₁ ⊕ Fin k₂, (u₁ ++ u₂)[List.appendIndexEquiv u₁ u₂ (x.map a₁ a₂)] =
        (v₁ ++ v₂)[List.appendIndexEquiv v₁ v₂ (x.map b₁ b₂)]
      | .inl i' => by
        simpa only [Sum.map_inl, List.getElem_appendIndexEquiv_inl] using h₁.2 i'
      | .inr i' => by
        simpa only [Sum.map_inr, List.getElem_appendIndexEquiv_inr] using h₂.2 i'
    exact key (σ i)

/-- Bookkeeping for a move in the first factor: the extended combined position puts the new pebble
on the new pebble of the first factor. -/
private theorem snoc_appendIndexEquiv_inl {X Y : List α} {k₁ k₂ k : ℕ}
    {a₁ : Fin k₁ → Fin X.length} {a₂ : Fin k₂ → Fin Y.length} (σ : Fin k → Fin k₁ ⊕ Fin k₂)
    {A : Fin k → Fin (X ++ Y).length}
    (hA : ∀ i, A i = List.appendIndexEquiv X Y ((σ i).map a₁ a₂)) (x : Fin X.length)
    (i : Fin (k + 1)) :
    (Fin.snoc A (List.appendIndexEquiv X Y (.inl x)) : Fin (k + 1) → _) i =
      List.appendIndexEquiv X Y (((Fin.snoc (fun i => (σ i).map Fin.castSucc id)
        (.inl (Fin.last k₁)) : Fin (k + 1) → Fin (k₁ + 1) ⊕ Fin k₂) i).map
          (Fin.snoc a₁ x : Fin (k₁ + 1) → _) a₂) := by
  induction i using Fin.lastCases with
  | last => simp
  | cast i => rcases hσ : σ i with j | j <;> simp [hA, hσ]

/-- Bookkeeping for a move in the second factor. -/
private theorem snoc_appendIndexEquiv_inr {X Y : List α} {k₁ k₂ k : ℕ}
    {a₁ : Fin k₁ → Fin X.length} {a₂ : Fin k₂ → Fin Y.length} (σ : Fin k → Fin k₁ ⊕ Fin k₂)
    {A : Fin k → Fin (X ++ Y).length}
    (hA : ∀ i, A i = List.appendIndexEquiv X Y ((σ i).map a₁ a₂)) (y : Fin Y.length)
    (i : Fin (k + 1)) :
    (Fin.snoc A (List.appendIndexEquiv X Y (.inr y)) : Fin (k + 1) → _) i =
      List.appendIndexEquiv X Y (((Fin.snoc (fun i => (σ i).map id Fin.castSucc)
        (.inr (Fin.last k₂)) : Fin (k + 1) → Fin k₁ ⊕ Fin (k₂ + 1)) i).map a₁
          (Fin.snoc a₂ y : Fin (k₂ + 1) → _)) := by
  induction i using Fin.lastCases with
  | last => simp
  | cast i => rcases hσ : σ i with j | j <;> simp [hA, hσ]

/-- **Composition of Ehrenfeucht–Fraïssé games for concatenation** [Libkin, Lemma 3.7 and §7.4]
[Libkin2004]. If Duplicator wins the `n`-round game on `u₁, v₁` from `(a₁, b₁)` and on `u₂, v₂`
from `(a₂, b₂)`, then she wins it on `u₁ ++ u₂, v₁ ++ v₂` from every position `(A, B)` that puts
each pebble `i` on the corresponding pebble of the factor named by `σ i`. -/
theorem WordDuplicatorWins.append {u₁ u₂ v₁ v₂ : List α} : ∀ (n : ℕ) {k₁ k₂ k : ℕ}
    {a₁ : Fin k₁ → Fin u₁.length} {b₁ : Fin k₁ → Fin v₁.length}
    {a₂ : Fin k₂ → Fin u₂.length} {b₂ : Fin k₂ → Fin v₂.length}
    (σ : Fin k → Fin k₁ ⊕ Fin k₂) {A : Fin k → Fin (u₁ ++ u₂).length}
    {B : Fin k → Fin (v₁ ++ v₂).length},
    (∀ i, A i = List.appendIndexEquiv u₁ u₂ ((σ i).map a₁ a₂)) →
    (∀ i, B i = List.appendIndexEquiv v₁ v₂ ((σ i).map b₁ b₂)) →
    WordDuplicatorWins n u₁ v₁ a₁ b₁ → WordDuplicatorWins n u₂ v₂ a₂ b₂ →
    WordDuplicatorWins n (u₁ ++ u₂) (v₁ ++ v₂) A B
  | 0, _, _, _, _, _, _, _, σ, _, _, hA, hB, h₁, h₂ =>
    WordDuplicatorWins.zero_iff.2 (partialIso_append σ hA hB h₁.partialIso h₂.partialIso)
  | n + 1, k₁, k₂, k, a₁, b₁, a₂, b₂, σ, A, B, hA, hB, h₁, h₂ => by
    refine WordDuplicatorWins.succ_iff.2 ⟨partialIso_append σ hA hB h₁.partialIso h₂.partialIso,
      fun c => ?_, fun d => ?_⟩
    · -- Spoiler plays in `u₁ ++ u₂`; Duplicator answers in the same factor.
      obtain ⟨x | x, rfl⟩ := (List.appendIndexEquiv u₁ u₂).surjective c
      · obtain ⟨y, hy⟩ := h₁.forth x
        exact ⟨List.appendIndexEquiv v₁ v₂ (.inl y), WordDuplicatorWins.append n _
          (snoc_appendIndexEquiv_inl σ hA x) (snoc_appendIndexEquiv_inl σ hB y) hy
          (h₂.mono n.le_succ)⟩
      · obtain ⟨y, hy⟩ := h₂.forth x
        exact ⟨List.appendIndexEquiv v₁ v₂ (.inr y), WordDuplicatorWins.append n _
          (snoc_appendIndexEquiv_inr σ hA x) (snoc_appendIndexEquiv_inr σ hB y)
          (h₁.mono n.le_succ) hy⟩
    · -- Spoiler plays in `v₁ ++ v₂`; Duplicator answers in the same factor.
      obtain ⟨y | y, rfl⟩ := (List.appendIndexEquiv v₁ v₂).surjective d
      · obtain ⟨x, hx⟩ := h₁.back y
        exact ⟨List.appendIndexEquiv u₁ u₂ (.inl x), WordDuplicatorWins.append n _
          (snoc_appendIndexEquiv_inl σ hA x) (snoc_appendIndexEquiv_inl σ hB y) hx
          (h₂.mono n.le_succ)⟩
      · obtain ⟨x, hx⟩ := h₂.back y
        exact ⟨List.appendIndexEquiv u₁ u₂ (.inr x), WordDuplicatorWins.append n _
          (snoc_appendIndexEquiv_inr σ hA x) (snoc_appendIndexEquiv_inr σ hB y)
          (h₁.mono n.le_succ) hx⟩

namespace WordDuplicatorWins

/-- Composition without pebbles: `u₁ ≡ₙ v₁` and `u₂ ≡ₙ v₂` give `u₁ ++ u₂ ≡ₙ v₁ ++ v₂`. -/
theorem append_elim0 {n : ℕ} {u₁ u₂ v₁ v₂ : List α}
    (h₁ : WordDuplicatorWins n u₁ v₁ Fin.elim0 Fin.elim0)
    (h₂ : WordDuplicatorWins n u₂ v₂ Fin.elim0 Fin.elim0) :
    WordDuplicatorWins n (u₁ ++ u₂) (v₁ ++ v₂) Fin.elim0 Fin.elim0 :=
  WordDuplicatorWins.append n (Fin.elim0 : Fin 0 → Fin 0 ⊕ Fin 0) (fun i => i.elim0)
    (fun i => i.elim0) h₁ h₂

/-- Composition around a pebbled letter: if `u₁ ≡ₙ v₁` and `u₂ ≡ₙ v₂`, then Duplicator wins the
`n`-round game on `u₁ ++ c :: u₂` and `v₁ ++ c :: v₂` with one pebble on each copy of `c`. -/
theorem append_cons {n : ℕ} {u₁ u₂ v₁ v₂ : List α} (c : α)
    (h₁ : WordDuplicatorWins n u₁ v₁ Fin.elim0 Fin.elim0)
    (h₂ : WordDuplicatorWins n u₂ v₂ Fin.elim0 Fin.elim0) :
    WordDuplicatorWins n (u₁ ++ c :: u₂) (v₁ ++ c :: v₂) ![⟨u₁.length, by simp⟩]
      ![⟨v₁.length, by simp⟩] := by
  have hmid : WordDuplicatorWins n (c :: u₂) (c :: v₂) ![0] ![0] :=
    WordDuplicatorWins.append n (u₁ := [c]) (v₁ := [c]) (a₂ := Fin.elim0) (b₂ := Fin.elim0)
      (fun _ => .inl 0)
      (fun i => Fin.ext (by simp only [Sum.map_inl]; rw [List.val_appendIndexEquiv_inl]; simp))
      (fun i => Fin.ext (by simp only [Sum.map_inl]; rw [List.val_appendIndexEquiv_inl]; simp))
      (refl n [c] ![0]) h₂
  exact WordDuplicatorWins.append n (a₁ := Fin.elim0) (b₁ := Fin.elim0) (fun _ => .inr 0)
    (fun i => Fin.ext (by simp only [Sum.map_inr]; rw [List.val_appendIndexEquiv_inr]; simp))
    (fun i => Fin.ext (by simp only [Sum.map_inr]; rw [List.val_appendIndexEquiv_inr]; simp))
    h₁ hmid

end WordDuplicatorWins

/-! ### Rank types of words and the congruence -/

/-- The rank-`n` type `Cslib.Logic.FO.rankType` of the word `w` with the pebbles `a`. -/
def wordRankType (n : ℕ) (w : List α) {k : ℕ} (a : Fin k → Fin w.length) :
    FO.RankType (wordLanguage α) n k :=
  @FO.rankType (wordLanguage α) _ (wordStructure w) n k a

/-- `wordRankType` is `Cslib.Logic.FO.rankType` on the word structure. -/
theorem wordRankType_eq_rankType (n : ℕ) (w : List α) {k : ℕ} (a : Fin k → Fin w.length) :
    wordRankType n w a = @FO.rankType (wordLanguage α) _ (wordStructure w) n k a := by
  rw [wordRankType]

/-- Two pebbled words have the same rank-`n` type exactly when Duplicator wins the `n`-round
game between them. -/
theorem wordRankType_eq_iff {n : ℕ} {u v : List α} {k : ℕ} {a : Fin k → Fin u.length}
    {b : Fin k → Fin v.length} :
    wordRankType n u a = wordRankType n v b ↔ WordDuplicatorWins n u v a b :=
  @FO.rankType_eq_iff (wordLanguage α) _ _ (wordStructure u) (wordStructure v) n k a b

variable (α) in
/-- Rank-`n` equivalence of words, as a congruence of the free monoid: two words are related when
they have the same rank-`n` type. Related words satisfy the same sentences of quantifier rank at
most `n` (`mem_language_iff_of_wordCon`). That it is a congruence is the composition
`WordDuplicatorWins.append_elim0`. -/
def wordCon (n : ℕ) : Con (FreeMonoid α) where
  r u v := wordRankType n u.toList Fin.elim0 = wordRankType n v.toList Fin.elim0
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
  mul' {w x y z} h₁ h₂ := by
    rw [wordRankType_eq_iff] at h₁ h₂ ⊢
    rw [FreeMonoid.toList_mul, FreeMonoid.toList_mul]
    exact h₁.append_elim0 h₂

theorem wordCon_iff {n : ℕ} {u v : FreeMonoid α} :
    wordCon α n u v ↔ WordDuplicatorWins n u.toList v.toList Fin.elim0 Fin.elim0 :=
  wordRankType_eq_iff

/-- Over a finite alphabet, rank-`n` equivalence of words has finite index: its classes inject
into the finitely many rank-`n` types. -/
instance wordCon.finite_quotient [Finite α] (n : ℕ) : Finite (wordCon α n).Quotient :=
  Finite.of_injective
    (Quotient.lift (fun w : FreeMonoid α => wordRankType n w.toList Fin.elim0) fun _ _ h => h :
      (wordCon α n).Quotient → FO.RankType (wordLanguage α) n 0)
    (by
      rintro ⟨u⟩ ⟨v⟩ h
      exact Quotient.sound h)

/-- A sentence of quantifier rank at most `n` defines a union of classes of rank-`n`
equivalence. -/
theorem mem_language_iff_of_wordCon {n : ℕ} {u v : FreeMonoid α} (h : wordCon α n u v)
    {φ : (wordLanguage α).Sentence} (hφ : FO.quantifierRank φ ≤ n) :
    u.toList ∈ WordFO.language φ ↔ v.toList ∈ WordFO.language φ :=
  (wordCon_iff.1 h).mem_language_iff hφ

/-- **First-order languages are recognized by finite monoids.** The language of a sentence `φ` is
the preimage, under the quotient map of rank-`n` equivalence with `n` the quantifier rank of `φ`,
of a set of classes. Over a finite alphabet the quotient is a finite monoid
(`wordCon.finite_quotient`). -/
theorem wordCon_preimage_image_language (φ : (wordLanguage α).Sentence) :
    (wordCon α (FO.quantifierRank φ)).mk' ∘ FreeMonoid.ofList ⁻¹'
        ((wordCon α (FO.quantifierRank φ)).mk' ∘ FreeMonoid.ofList '' WordFO.language φ) =
      WordFO.language φ := by
  refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
  rintro x ⟨y, hy, hxy⟩
  change ((FreeMonoid.ofList y : FreeMonoid α) : (wordCon α _).Quotient) = FreeMonoid.ofList x
    at hxy
  exact (mem_language_iff_of_wordCon ((Con.eq _).1 hxy) le_rfl).1 hy

end Cslib.Logic.WordMSO
