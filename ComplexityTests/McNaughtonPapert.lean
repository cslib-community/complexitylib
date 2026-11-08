/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.SecondOrder.WordMSO.McNaughtonPapert

/-!
# Tests: the McNaughton–Papert theorem

* Over `Bool`, first-order definable languages are closed under concatenation: a consequence of
  `foDefinable_iff_isStarFree` that has no direct first-order proof here.
* The finite alphabet cannot be dropped: over `ℕ` the iff fails, by
  `exists_foDefinable_not_isStarFree`.
* Rank `0`: every class is empty or everything, and the class of `[]` contains `[true, false]`.
* Pointed types: the one-pebble rank-`0` type of `([true], 0)` occurs in `[true]` but not in
  `[false]`, so by `wordRankType_succ_eq_iff` the words `[true]` and `[false]` are not rank-`1`
  equivalent.
* Finite unions and intersections of star-free languages are star-free.
-/

open Cslib.Logic.WordMSO Cslib.Language

namespace ComplexityTests.McNaughtonPapert

/-- Over `Bool`, first-order definable languages are closed under concatenation, through
star-freeness. -/
example {L M : Language Bool} (hL : FODefinable L) (hM : FODefinable M) : FODefinable (L * M) :=
  foDefinable_iff_isStarFree.2 (hL.isStarFree.mul hM.isStarFree)

/-- Over `Bool`, first-order definable languages are closed under complement and finite unions. -/
example {ι : Type} [Finite ι] {L : ι → Language Bool} (hL : ∀ i, FODefinable (L i)) :
    FODefinable (⨆ i, L i)ᶜ :=
  foDefinable_iff_isStarFree.2 (IsStarFree.iSup fun i => (hL i).isStarFree).compl

/-- The finite alphabet is necessary: over `ℕ`, first-order definability and star-freeness
differ. -/
example : ¬ ∀ L : Language ℕ, FODefinable L ↔ IsStarFree L := by
  intro h
  obtain ⟨L, hFO, hSF⟩ := exists_foDefinable_not_isStarFree (α := ℕ)
  exact hSF ((h L).1 hFO)

/-- The rank-`0` class of the empty word contains `[true, false]`: without pebbles all words are
rank-`0` equivalent. -/
example : [true, false] ∈ rankTypeLanguage 0 (wordRankType 0 ([] : List Bool) Fin.elim0) :=
  mem_rankTypeLanguage.2 (wordRankType_zero_eq _ _)

/-- `[false]` has no position of the one-pebble rank-`0` type of `([true], 0)`: the pebbled letters
differ. -/
theorem false_notMem_pointed :
    [false] ∉ pointedRankTypeLanguage 0 (wordRankType 0 [true] ![⟨0, by decide⟩]) := by
  rintro ⟨p, hp⟩
  have h := (wordStructure.partialIso_iff.1
    (WordDuplicatorWins.zero_iff.1 (wordRankType_eq_iff.1 hp))).2 0
  have hp0 : p = ⟨0, by decide⟩ := by
    have : (p : ℕ) < 1 := p.isLt
    exact Fin.ext (by change (p : ℕ) = 0; omega)
  subst hp0
  simp at h

/-- `[true]` and `[false]` are not rank-`1` equivalent: by `wordRankType_succ_eq_iff`, they would
have the same one-pebble rank-`0` types. -/
example : wordRankType 1 [true] Fin.elim0 ≠ wordRankType 1 [false] Fin.elim0 := by
  intro h
  exact false_notMem_pointed ((wordRankType_succ_eq_iff.1 h _).1 ⟨⟨0, by decide⟩, rfl⟩)

/-- A finite intersection of star-free languages is star-free: the words containing each of
`[true]`, `[false]` as a factor. -/
example : IsStarFree (⨅ b : Bool, (⊤ * {[b]} * ⊤ : Language Bool)) :=
  IsStarFree.iInf fun b => (IsStarFree.top.mul (.char b)).mul .top

end ComplexityTests.McNaughtonPapert
