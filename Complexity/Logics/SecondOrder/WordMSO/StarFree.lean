/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Languages.StarFree
public import Complexity.Logics.SecondOrder.WordMSO.FirstOrder
import Complexity.Logics.SecondOrder.WordMSO.Separation

/-!
# Star-free languages are first-order definable

Every star-free language is first-order definable over words (in `FO[<]` with letter predicates).
This is the direction star-free ⇒ FO of [Libkin, Theorem 7.26][Libkin2004], which is due to
McNaughton and Papert [McNaughtonPapert1971]. The translation `starFreeSentence` follows the proof
there, by structural induction: `∅` becomes `⊥`, union disjunction, complement negation, and a
concatenation `e · f` guesses the last position `x` of the `e`-factor and relativizes the
quantifiers of the two translations to the positions up to `x` and after `x`.

Nested concatenations relativize to nested windows, so the translation keeps two optional bounds
`lo < x ≤ hi`, given by bound variables, where a missing bound means the start or the end of the
word. A concatenation whose `e`-factor is empty has no last position `x`; it adds the disjunct for
`f` alone exactly when `e` matches the empty word (`StarFreeExpression.matchEpsilon`). Libkin's
proof sketch quantifies over a split point `x` only, which leaves this case implicit.

With `not_foDefinable_even` this gives [Libkin, Corollary 7.27][Libkin2004]: even length is
regular but not star-free (over a one-letter alphabet, `(aa)*`), over any nonempty alphabet.

The converse, FO ⇒ star-free, holds over a finite alphabet [Libkin, Theorem 7.26][Libkin2004] and
is not formalized here. It fails over an infinite alphabet, where `{ε}` is first-order definable
but not star-free (`exists_foDefinable_not_isStarFree`). This is an elementary remark outside the
finite-alphabet setting of the cited sources, not a result taken from them. For the connections
between automata, logical definability and circuit complexity, Libkin refers to Straubing's book
[Straubing1994].

## Main definitions

* `Cslib.Logic.WordMSO.starFreeSentence`: the first-order sentence of a star-free expression.

## Main results

* `Cslib.Logic.WordMSO.isFO_starFreeSentence`: the translation is first-order.
* `Cslib.Logic.WordMSO.starFreeSentence_language`: it defines the language of the expression.
* `Cslib.Language.IsStarFree.foDefinable`: star-free languages are first-order definable.
* `Cslib.Language.IsStarFree.exists_sentence`: a star-free language is the language of a Mathlib
  first-order sentence over the word vocabulary.
* `Cslib.Logic.WordMSO.not_isStarFree_even`, `Cslib.Logic.WordMSO.exists_isRegular_not_isStarFree`:
  even length is regular but not star-free.
* `Cslib.Logic.WordMSO.foDefinable_one`: `{ε}` is first-order definable.
* `Cslib.Logic.WordMSO.exists_foDefinable_not_isStarFree`: over an infinite alphabet, some
  first-order definable language is not star-free.

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004]
* [R. McNaughton and S. Papert, *Counter-Free Automata*][McNaughtonPapert1971]
* [H. Straubing, *Finite Automata, Formal Logic, and Circuit Complexity*][Straubing1994]
-/

public section

universe u

namespace Cslib.Logic.WordMSO

open Cslib.Language

variable {α : Type u}

/-! ### Windows -/

/-- `lo < x`, where the bound `none` is the start of the word (no constraint). -/
private def afterLo {m n : ℕ} (lo : Option (Fin m)) (x : Fin m) : Formula α m n :=
  match lo with
  | none => .top
  | some l => .lt l x

/-- `x ≤ hi`, where the bound `none` is the end of the word (no constraint). -/
private def upToHi {m n : ℕ} (hi : Option (Fin m)) (x : Fin m) : Formula α m n :=
  match hi with
  | none => .top
  | some h => .not (.lt h x)

/-- `x` lies in the window strictly after `lo` and at most `hi`. -/
private def inWindow {m n : ℕ} (lo hi : Option (Fin m)) (x : Fin m) : Formula α m n :=
  .and (afterLo lo x) (upToHi hi x)

/-- A window bound under one more bound variable. -/
private def liftBound {m : ℕ} (b : Option (Fin m)) : Option (Fin (m + 1)) :=
  b.map Fin.castSucc

/-- The formula expressing that the factor of the word in the window `(lo, hi]` belongs to the
language of `e`. -/
private def window : {m n : ℕ} → StarFreeExpression α → Option (Fin m) → Option (Fin m) →
    Formula α m n
  | _, _, .zero, _, _ => .falsum
  | m, _, .char a, lo, hi =>
    .ex (.and (inWindow (liftBound lo) (liftBound hi) (Fin.last m))
      (.and (.letter a (Fin.last m))
        (.all (.imp
          (inWindow (liftBound (liftBound lo)) (liftBound (liftBound hi)) (Fin.last (m + 1)))
          (.eq (Fin.last (m + 1)) (Fin.castSucc (Fin.last m)))))))
  | _, _, .plus e f, lo, hi => .or (window e lo hi) (window f lo hi)
  | _, _, .compl e, lo, hi => .not (window e lo hi)
  | m, _, .comp e f, lo, hi =>
    .or (if e.matchEpsilon then window f lo hi else .falsum)
      (.ex (.and (inWindow (liftBound lo) (liftBound hi) (Fin.last m))
        (.and (window e (liftBound lo) (some (Fin.last m)))
          (window f (some (Fin.last m)) (liftBound hi)))))

private theorem isFO_inWindow {m n : ℕ} (lo hi : Option (Fin m)) (x : Fin m) :
    (inWindow lo hi x : Formula α m n).IsFO := by
  cases lo <;> cases hi <;> simp [inWindow, afterLo, upToHi]

private theorem isFO_window : ∀ (e : StarFreeExpression α) {m n : ℕ} (lo hi : Option (Fin m)),
    (window e lo hi : Formula α m n).IsFO
  | .zero, _, _, _, _ => Formula.isFO_falsum
  | .char a, _, _, lo, hi => by simp [window, isFO_inWindow]
  | .plus e f, _, _, lo, hi => Formula.isFO_or.2 ⟨isFO_window e lo hi, isFO_window f lo hi⟩
  | .compl e, _, _, lo, hi => Formula.isFO_not.2 (isFO_window e lo hi)
  | .comp e f, m, n, lo, hi => by
    have hε : ((if e.matchEpsilon then window f lo hi else .falsum : Formula α m n)).IsFO := by
      cases e.matchEpsilon
      · exact Formula.isFO_falsum
      · exact isFO_window f lo hi
    exact Formula.isFO_or.2 ⟨hε, Formula.isFO_ex.2 (Formula.isFO_and.2 ⟨isFO_inWindow _ _ _,
      Formula.isFO_and.2 ⟨isFO_window e _ _, isFO_window f _ _⟩⟩)⟩

variable {ℓ : ℕ}

/-- The first position of the window with lower bound `lo`. -/
private def lowerCut {m : ℕ} (v : Fin m → Fin ℓ) : Option (Fin m) → ℕ
  | none => 0
  | some l => v l + 1

/-- One past the last position of the window with upper bound `hi`. -/
private def upperCut {m : ℕ} (v : Fin m → Fin ℓ) : Option (Fin m) → ℕ
  | none => ℓ
  | some h => v h + 1

private theorem upperCut_le {m : ℕ} (v : Fin m → Fin ℓ) (b : Option (Fin m)) :
    upperCut v b ≤ ℓ := by
  cases b with
  | none => exact le_rfl
  | some h => exact (v h).isLt

private theorem lowerCut_liftBound {m : ℕ} (v : Fin m → Fin ℓ) (p : Fin ℓ) (b : Option (Fin m)) :
    lowerCut (Fin.snoc v p) (liftBound b) = lowerCut v b := by
  cases b <;> simp [liftBound, lowerCut]

private theorem upperCut_liftBound {m : ℕ} (v : Fin m → Fin ℓ) (p : Fin ℓ) (b : Option (Fin m)) :
    upperCut (Fin.snoc v p) (liftBound b) = upperCut v b := by
  cases b <;> simp [liftBound, upperCut]

private theorem lowerCut_some_last {m : ℕ} (v : Fin m → Fin ℓ) (p : Fin ℓ) :
    lowerCut (Fin.snoc v p) (some (Fin.last m)) = p + 1 := by
  simp [lowerCut]

private theorem upperCut_some_last {m : ℕ} (v : Fin m → Fin ℓ) (p : Fin ℓ) :
    upperCut (Fin.snoc v p) (some (Fin.last m)) = p + 1 := by
  simp [upperCut]

private theorem realize_inWindow (w : Fin ℓ → α) {m n : ℕ} (lo hi : Option (Fin m)) (x : Fin m)
    (v : Fin m → Fin ℓ) (V : Fin n → Set (Fin ℓ)) :
    (inWindow lo hi x : Formula α m n).Realize w v V ↔
      lowerCut v lo ≤ v x ∧ (v x : ℕ) < upperCut v hi := by
  simp only [inWindow, Formula.realize_and]
  apply and_congr
  · cases lo with
    | none => simp [afterLo, lowerCut]
    | some l =>
      simp only [afterLo, Formula.realize_lt, lowerCut, Fin.lt_def]
      omega
  · cases hi with
    | none => simp [upToHi, upperCut]
    | some h =>
      simp only [upToHi, Formula.realize_not, Formula.realize_lt, upperCut, Fin.lt_def]
      omega

/-! ### Factors of a word -/

private theorem extract_self' (u : List α) (i : ℕ) : u.extract i i = [] := by
  simp

private theorem length_extract' (u : List α) (i j : ℕ) :
    (u.extract i j).length = min (j - i) (u.length - i) := by
  simp

private theorem extract_split (u : List α) {i s j : ℕ} (his : i ≤ s) (hsj : s ≤ j) :
    u.extract i j = u.extract i s ++ u.extract s j := by
  simp only [List.extract_eq_take_drop]
  have h : j - i = (s - i) + (j - s) := by omega
  rw [h, List.take_add, List.drop_drop, Nat.add_sub_cancel' his]

/-- A factor of `u` lies in `L * M` iff it splits, at some position of the factor, into a factor
in `L` and a factor in `M`. -/
private theorem extract_mem_mul {L M : _root_.Language α} (u : List α) {i j : ℕ} (hij : i ≤ j) :
    u.extract i j ∈ L * M ↔ ∃ s, i ≤ s ∧ s ≤ j ∧ u.extract i s ∈ L ∧ u.extract s j ∈ M := by
  rw [Language.mem_mul]
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    have hlen := congrArg List.length hxy
    rw [List.length_append, length_extract'] at hlen
    have hs : i + x.length ≤ j := by omega
    have hsplit := extract_split u (Nat.le_add_right i x.length) hs
    rw [hsplit] at hxy
    have hxl : x.length = (u.extract i (i + x.length)).length := by
      rw [length_extract']
      omega
    obtain ⟨h1, h2⟩ := List.append_inj hxy hxl
    exact ⟨_, Nat.le_add_right _ _, hs, h1 ▸ hx, h2 ▸ hy⟩
  · rintro ⟨s, his, hsj, hL, hM⟩
    exact ⟨_, hL, _, hM, (extract_split u his hsj).symm⟩

/-- A factor of `u` is the one-letter word `a` iff the window has exactly one position, and `u`
has the letter `a` there. -/
private theorem extract_eq_singleton (u : List α) (a : α) {i j : ℕ} (hj : j ≤ u.length) :
    u.extract i j = [a] ↔ ∃ p : Fin u.length, (i ≤ p ∧ (p : ℕ) < j) ∧ u[p] = a ∧
      ∀ q : Fin u.length, i ≤ q ∧ (q : ℕ) < j → q = p := by
  constructor
  · intro h
    have hlen := congrArg List.length h
    rw [length_extract', List.length_singleton] at hlen
    have hji : j = i + 1 := by omega
    have hi : i < u.length := by omega
    subst hji
    have h1 : u.extract i (i + 1) = [u[i]] := by
      simp only [List.extract_eq_take_drop, Nat.add_sub_cancel_left]
      rw [List.take_one_drop_eq_of_lt_length hi]
      rfl
    rw [h1, List.singleton_inj] at h
    exact ⟨⟨i, hi⟩, ⟨le_rfl, Nat.lt_succ_self i⟩, h, fun q hq => Fin.ext (by simp only; omega)⟩
  · rintro ⟨⟨p, hp⟩, ⟨hip, hpj⟩, hpa, huniq⟩
    have hji : j = i + 1 := by
      by_contra hne
      have h1 := huniq ⟨i, by omega⟩ ⟨le_rfl, by simp only; omega⟩
      have h2 := huniq ⟨i + 1, by omega⟩ ⟨by simp only; omega, by simp only; omega⟩
      have := congrArg Fin.val (h1.trans h2.symm)
      simp only at this
      omega
    subst hji
    obtain rfl : p = i := by simp only at hip hpj; omega
    simp only [List.extract_eq_take_drop, Nat.add_sub_cancel_left]
    rw [List.take_one_drop_eq_of_lt_length hp]
    exact congrArg (fun b => [b]) hpa

/-- The window formula of `e` holds iff the factor of the word in the window belongs to the
language of `e`. -/
private theorem realize_window (u : List α) : ∀ (e : StarFreeExpression α) {m n : ℕ}
    (lo hi : Option (Fin m)) (v : Fin m → Fin u.length) (V : Fin n → Set (Fin u.length)),
    lowerCut v lo ≤ upperCut v hi →
    ((window e lo hi : Formula α m n).Realize (fun i : Fin u.length => u[i]) v V ↔
      u.extract (lowerCut v lo) (upperCut v hi) ∈ e.matches')
  | .zero, _, _, lo, hi, v, V, _ => by
    simp only [window, Formula.realize_falsum, StarFreeExpression.matches'_zero, false_iff]
    exact Language.notMem_zero _
  | .char a, m, _, lo, hi, v, V, _ => by
    simp only [window, Formula.realize_ex, Formula.realize_and, realize_inWindow,
      Formula.realize_letter, Formula.realize_all, Formula.realize_imp, Formula.realize_eq,
      Fin.snoc_last, Fin.snoc_castSucc, lowerCut_liftBound, upperCut_liftBound,
      StarFreeExpression.matches'_char]
    exact (extract_eq_singleton u a (upperCut_le v hi)).symm
  | .plus e f, _, _, lo, hi, v, V, h => by
    simp only [window, Formula.realize_or, StarFreeExpression.matches'_plus, Language.mem_add,
      realize_window u e lo hi v V h, realize_window u f lo hi v V h]
  | .compl e, _, _, lo, hi, v, V, h => by
    simp only [window, Formula.realize_not, StarFreeExpression.matches'_compl,
      realize_window u e lo hi v V h]
    exact Iff.rfl
  | .comp e f, m, _, lo, hi, v, V, h => by
    have hj := upperCut_le v hi
    rw [StarFreeExpression.matches'_comp, extract_mem_mul u h]
    simp only [window, Formula.realize_or, Formula.realize_ex, Formula.realize_and,
      realize_inWindow, Fin.snoc_last, lowerCut_liftBound, upperCut_liftBound]
    constructor
    · rintro (hε | ⟨p, ⟨hip, hpj⟩, he, hf⟩)
      · cases hm : e.matchEpsilon with
        | false =>
          simp only [hm, Bool.false_eq_true, ↓reduceIte, Formula.realize_falsum] at hε
        | true =>
          simp only [hm, ↓reduceIte] at hε
          refine ⟨lowerCut v lo, le_rfl, h, ?_, (realize_window u f lo hi v V h).1 hε⟩
          rw [extract_self']
          exact (StarFreeExpression.matchEpsilon_iff e).1 hm
      · rw [realize_window u e _ _ _ V
          (by simp only [lowerCut_liftBound, upperCut_some_last]; omega),
          lowerCut_liftBound, upperCut_some_last] at he
        rw [realize_window u f _ _ _ V
          (by simp only [lowerCut_some_last, upperCut_liftBound]; omega),
          lowerCut_some_last, upperCut_liftBound] at hf
        exact ⟨p + 1, by omega, by omega, he, hf⟩
    · rintro ⟨s, his, hsj, he, hf⟩
      rcases Nat.eq_or_lt_of_le his with rfl | hlt
      · left
        rw [extract_self'] at he
        have hm := (StarFreeExpression.matchEpsilon_iff e).2 he
        simp only [hm, ↓reduceIte]
        exact (realize_window u f lo hi v V h).2 hf
      · right
        have hs1 : s - 1 + 1 = s := by omega
        refine ⟨⟨s - 1, by omega⟩, ⟨by simp only; omega, by simp only; omega⟩, ?_, ?_⟩
        · rw [realize_window u e _ _ _ V
            (by simp only [lowerCut_liftBound, upperCut_some_last]; omega),
            lowerCut_liftBound, upperCut_some_last]
          simp only [hs1]
          exact he
        · rw [realize_window u f _ _ _ V
            (by simp only [lowerCut_some_last, upperCut_liftBound]; omega),
            lowerCut_some_last, upperCut_liftBound]
          simp only [hs1]
          exact hf

/-! ### The translation -/

/-- The first-order sentence defining the language of a star-free expression, following
[Libkin, Theorem 7.26][Libkin2004]. -/
def starFreeSentence (e : StarFreeExpression α) : Sentence α := window e none none

/-- The translation of a star-free expression is first-order. -/
theorem isFO_starFreeSentence (e : StarFreeExpression α) : (starFreeSentence e).IsFO :=
  isFO_window e none none

/-- The translation of a star-free expression defines its language. -/
theorem starFreeSentence_language (e : StarFreeExpression α) :
    (starFreeSentence e).language = e.matches' := by
  ext u
  change (window e none none).Realize (fun i : Fin u.length => u[i]) Fin.elim0 Fin.elim0 ↔ _
  rw [realize_window u e none none Fin.elim0 Fin.elim0 (by simp [lowerCut, upperCut])]
  simp [lowerCut, upperCut]

end Cslib.Logic.WordMSO

namespace Cslib.Language.IsStarFree

open Cslib.Logic.WordMSO

variable {α : Type u}

/-- **Star-free languages are first-order definable** (McNaughton–Papert), the direction
star-free ⇒ FO of [Libkin, Theorem 7.26][Libkin2004]. The alphabet may be infinite. -/
theorem foDefinable {L : _root_.Language α} (h : IsStarFree L) : FODefinable L :=
  let ⟨e, he⟩ := h
  ⟨starFreeSentence e, isFO_starFreeSentence e, (starFreeSentence_language e).trans he⟩

/-- A star-free language is the language of a Mathlib first-order sentence over the word
vocabulary. -/
theorem exists_sentence {L : _root_.Language α} (h : IsStarFree L) :
    ∃ φ : (wordLanguage α).Sentence, WordFO.language φ = L :=
  foDefinable_iff_exists_sentence.1 h.foDefinable

end Cslib.Language.IsStarFree

namespace Cslib.Logic.WordMSO

open Cslib.Language

variable {α : Type u}

/-- **Even length is not star-free**, over any nonempty alphabet: it is not first-order definable.
Over a one-letter alphabet this is `(aa)*` [Libkin, Corollary 7.27][Libkin2004]. -/
theorem not_isStarFree_even [Nonempty α] : ¬ IsStarFree {w : List α | Even w.length} :=
  fun h => not_foDefinable_even h.foDefinable

/-- **Some regular language is not star-free** [Libkin, Corollary 7.27][Libkin2004]: even length,
over any nonempty alphabet. -/
theorem exists_isRegular_not_isStarFree [Nonempty α] :
    ∃ L : _root_.Language α, L.IsRegular ∧ ¬ IsStarFree L :=
  ⟨_, definable_even.isRegular, not_isStarFree_even⟩

/-- `{ε}` is first-order definable, by `¬ ∃ x, ⊤`. -/
theorem foDefinable_one : FODefinable (1 : _root_.Language α) := by
  refine ⟨.not (.ex .top), by simp, Set.ext fun w => ?_⟩
  change (Formula.not (Formula.ex Formula.top) : Sentence α).Realize
    (fun i : Fin w.length => w[i]) Fin.elim0 Fin.elim0 ↔ _
  simp only [Formula.realize_not, Formula.realize_ex, Formula.realize_top, exists_const_iff,
    and_true, not_nonempty_iff, Fin.isEmpty_iff]
  exact List.length_eq_zero_iff.trans (Language.mem_one w).symm

/-- Over an infinite alphabet, some first-order definable language, `{ε}`, is not star-free, so the
direction FO ⇒ star-free of [Libkin, Theorem 7.26][Libkin2004] needs a finite alphabet. This is an
elementary remark (`Cslib.Language.not_isStarFree_one`). -/
theorem exists_foDefinable_not_isStarFree [Infinite α] :
    ∃ L : _root_.Language α, FODefinable L ∧ ¬ IsStarFree L :=
  ⟨1, foDefinable_one, not_isStarFree_one⟩

end Cslib.Logic.WordMSO
