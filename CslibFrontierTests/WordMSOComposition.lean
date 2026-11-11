/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Logics.SecondOrder.WordMSO.Composition
import Mathlib.Computability.MyhillNerode

/-!
# Tests: Ehrenfeucht–Fraïssé games on concatenations of words

* rank-`0` equivalence relates every two words, and rank-`1` equivalence does not: the empty word
  and a one-letter word differ;
* `b ≡₁ bb` but not `b ≡₂ bb` (`b = true`), so rank-`1` equivalence is not equality, and the
  rank hierarchy is strict on this pair;
* composition (`WordDuplicatorWins.append_elim0`) gives `ba ≡₁ bba`, and the pebbled form
  (`WordDuplicatorWins.append_cons`) gives `b·a·b ≡₁ bb·a·bb` with a pebble on the inserted `a`;
* the congruence `wordCon` relates the products, has finite index over `Bool`, and the language of
  a sentence is a union of its classes;
* by Myhill–Nerode, the finite index makes the language of every sentence over `Bool` regular.
-/

open Cslib.Logic.WordMSO

namespace CslibFrontierTests.WordMSOComposition

/-- Rank-`0` equivalence relates every two words: there are no pebbles to compare. -/
theorem wordDuplicatorWins_zero (u v : List Bool) :
    WordDuplicatorWins 0 u v Fin.elim0 Fin.elim0 := by
  rw [WordDuplicatorWins.zero_iff, wordStructure.partialIso_iff]
  exact ⟨fun i => i.elim0, fun i => i.elim0⟩

/-- Rank-`1` equivalence separates the empty word from a one-letter word: Spoiler pebbles the
letter and Duplicator has no position to answer with. -/
example : ¬ WordDuplicatorWins 1 ([] : List Bool) [true] Fin.elim0 Fin.elim0 := by
  intro h
  obtain ⟨c, -⟩ := h.back 0
  exact c.elim0

/-- `b ≡₁ bb`: with one pebble only its letter is visible. -/
theorem b_equiv₁_bb : WordDuplicatorWins 1 [true] [true, true] Fin.elim0 Fin.elim0 := by
  have hb : ∀ (w : List Bool), (∀ a ∈ w, a = true) → ∀ x : Fin w.length, w[x] = true :=
    fun w hw x => hw _ (List.getElem_mem _)
  have key : ∀ (c : Fin [true].length) (d : Fin [true, true].length),
      WordDuplicatorWins 0 [true] [true, true] (Fin.snoc Fin.elim0 c : Fin 1 → Fin [true].length)
        (Fin.snoc Fin.elim0 d : Fin 1 → Fin [true, true].length) := by
    intro c d
    rw [WordDuplicatorWins.zero_iff, wordStructure.partialIso_iff]
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · obtain rfl : i = j := Fin.ext (by have := i.isLt; have := j.isLt; omega)
      exact iff_of_false (lt_irrefl _) (lt_irrefl _)
    · exact (hb [true] (by simp) _).trans (hb [true, true] (by simp) _).symm
  exact WordDuplicatorWins.succ_iff.2 ⟨(wordDuplicatorWins_zero _ _).partialIso,
    fun c => ⟨0, key c 0⟩, fun d => ⟨0, key 0 d⟩⟩

/-- `b ≢₂ bb`: Spoiler pebbles the two positions of `bb`, and Duplicator must answer both with the
single position of `b`. -/
example : ¬ WordDuplicatorWins 2 [true] [true, true] Fin.elim0 Fin.elim0 := by
  intro h
  obtain ⟨c₀, h₁⟩ := h.back 0
  obtain ⟨c₁, h₂⟩ := h₁.back 1
  have hp := (wordStructure.partialIso_iff.1 h₂.partialIso).1 (Fin.castSucc (Fin.last 0))
    (Fin.last 1)
  simp only [Fin.snoc_castSucc, Fin.snoc_last] at hp
  obtain rfl : c₀ = c₁ := Fin.ext (by
    have := c₀.isLt; have := c₁.isLt; simp only [List.length_singleton] at *; omega)
  exact lt_irrefl _ (hp.2 (by decide))

/-- Composition: `b ≡₁ bb` and `a ≡₁ a` give `ba ≡₁ bba`. -/
example : WordDuplicatorWins 1 [true, false] [true, true, false] Fin.elim0 Fin.elim0 :=
  b_equiv₁_bb.append_elim0 (WordDuplicatorWins.refl 1 [false] Fin.elim0)

/-- Composition around a pebbled letter: `b·a·b ≡₁ bb·a·bb`, with a pebble on the inserted `a`. -/
example : WordDuplicatorWins 1 ([true] ++ false :: [true]) ([true, true] ++ false :: [true, true])
    ![⟨1, by decide⟩] ![⟨2, by decide⟩] :=
  WordDuplicatorWins.append_cons false b_equiv₁_bb b_equiv₁_bb

/-- The congruence: `b ≡₁ bb` gives `b · a ≡₁ bb · a` in the free monoid. -/
example : wordCon Bool 1 (FreeMonoid.ofList [true] * FreeMonoid.ofList [false])
    (FreeMonoid.ofList [true, true] * FreeMonoid.ofList [false]) :=
  (wordCon Bool 1).mul (wordCon_iff.2 b_equiv₁_bb) ((wordCon Bool 1).refl _)

/-- Over `Bool`, rank-`3` equivalence has finitely many classes. -/
example : Finite (wordCon Bool 3).Quotient := inferInstance

/-- A sentence of quantifier rank at most `1` does not separate `b` from `bb`. -/
example (φ : (Cslib.Logic.WordMSO.wordLanguage Bool).Sentence)
    (hφ : Cslib.Logic.FO.quantifierRank φ ≤ 1) :
    [true] ∈ WordFO.language φ ↔ [true, true] ∈ WordFO.language φ :=
  b_equiv₁_bb.mem_language_iff hφ

/-- The language of every sentence over `Bool` is regular, by Myhill–Nerode: the left quotient by
a word depends only on its rank class, and there are finitely many classes. -/
example (φ : (Cslib.Logic.WordMSO.wordLanguage Bool).Sentence) :
    (WordFO.language φ).IsRegular := by
  let c := wordCon Bool (Cslib.Logic.FO.quantifierRank φ)
  let g : c.Quotient → Language Bool :=
    Quotient.lift (fun x : FreeMonoid Bool => (WordFO.language φ).leftQuotient x.toList)
      fun x x' h => by
        ext y
        exact mem_language_iff_of_wordCon (c.mul (show c x x' from h) (c.refl (.ofList y))) le_rfl
  refine Language.isRegular_iff_finite_range_leftQuotient.2 ((Set.finite_range g).subset ?_)
  rintro _ ⟨x, rfl⟩
  exact ⟨Quotient.mk _ (FreeMonoid.ofList x), rfl⟩

end CslibFrontierTests.WordMSOComposition
