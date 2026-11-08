/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.SecondOrder.WordMSO.ToRegular
public import Mathlib.Computability.DFA
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Fintype.EquivFin

/-!
# The Büchi–Elgot–Trakhtenbrot theorem

Over a finite alphabet, a language of finite words is regular if and only if it is definable in
monadic second-order logic over word structures [Büchi][Buchi1960], [Elgot][Elgot1961],
[Libkin, Theorem 7.21][Libkin2004], [Thomas, Section 3][Thomas1997]. (Trakhtenbrot proved the
same theorem independently.)

This file proves the direction "regular ⇒ MSO-definable" and assembles the equivalence with
`Cslib.Logic.WordMSO.Definable.isRegular`. A DFA `M` with states `σ` is described by the sentence
`dfaSentence M`, which existentially quantifies one set variable `X_q` per state `q` and says that
the sets record a run of `M`: the first position is in `X_{δ(q₀, a)}` for its letter `a`, if
position `x` is in `X_q` and its successor `y` carries `a` then `y` is in `X_{δ(q, a)}`, and the
last position is in no `X_q` with `q` rejecting. Since `M` is deterministic, the sets then contain
the actual run, so the last position is in `X_q` for the final state `q`. The empty word, which
has no positions, is handled by a separate conjunct.

As an example of an MSO-definable language, `evenSentence` defines the words of even length by
guessing the set of even positions. Even length is not first-order definable in `FO[<]`, by an
Ehrenfeucht–Fraïssé argument [Libkin, Chapter 3][Libkin2004]; this file does not prove that
separation.

## Main definitions

* `Cslib.Logic.WordMSO.Formula.exSets`: existential closure over all set variables.
* `Cslib.Logic.WordMSO.dfaSentence`: the MSO sentence describing the accepting runs of a DFA.
* `Cslib.Logic.WordMSO.evenSentence`: the MSO sentence of the words of even length.

## Main results

* `Cslib.Logic.WordMSO.dfaSentence_language`: `dfaSentence M` defines the language of `M`.
* `Cslib.Logic.WordMSO.definable_of_isRegular`: regular languages over a finite alphabet are
  MSO-definable.
* `Cslib.Logic.WordMSO.definable_iff_isRegular`: the Büchi–Elgot–Trakhtenbrot theorem.
* `Cslib.Logic.WordMSO.evenSentence_language`, `Cslib.Logic.WordMSO.definable_even`: words of
  even length are MSO-definable.

## References

* [J. R. Büchi, *Weak second-order arithmetic and finite automata*][Buchi1960]
* [C. C. Elgot, *Decision problems of finite automata design and related arithmetics*][Elgot1961]
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004]
* [W. Thomas, *Languages, automata, and logic*][Thomas1997]
-/

public section

universe u v

namespace Cslib.Logic.WordMSO

variable {α : Type u}

namespace Formula

/-- Existential closure over all set variables: `∃ X₀ ... ∃ X_{n-1}, φ`. -/
def exSets {m : ℕ} : {n : ℕ} → Formula α m n → Formula α m 0
  | 0, φ => φ
  | _ + 1, φ => exSets (exSet φ)

@[simp] theorem realize_exSets {m n ℓ : ℕ} {w : Fin ℓ → α} {v : Fin m → Fin ℓ}
    {V : Fin 0 → Set (Fin ℓ)} (φ : Formula α m n) :
    (exSets φ).Realize w v V ↔ ∃ W : Fin n → Set (Fin ℓ), φ.Realize w v W := by
  induction n with
  | zero =>
    have hV : V = Fin.elim0 := funext fun X => X.elim0
    refine ⟨fun h => ⟨V, h⟩, fun ⟨W, h⟩ => ?_⟩
    have hW : W = Fin.elim0 := funext fun X => X.elim0
    rw [hV]
    rw [hW] at h
    exact h
  | succ n ih =>
    rw [exSets, ih]
    simp only [realize_exSet]
    constructor
    · rintro ⟨W, S, h⟩
      exact ⟨_, h⟩
    · rintro ⟨W, h⟩
      refine ⟨Fin.init W, W (Fin.last n), ?_⟩
      rw [Fin.snoc_init_self]
      exact h

end Formula

open Formula

/-! ### Regular languages are MSO-definable -/

section DFA

variable {σ : Type v}

private theorem eval_take_succ_succ (M : DFA α σ) (w : List α) (i : ℕ) (h : i + 1 < w.length) :
    M.eval (w.take (i + 2)) = M.step (M.eval (w.take (i + 1))) w[i + 1] := by
  rw [List.take_succ_eq_append_getElem h, DFA.eval_append_singleton]

private theorem eval_take_one (M : DFA α σ) (w : List α) (h : 0 < w.length) :
    M.eval (w.take 1) = M.step M.start w[0] := by
  rw [List.take_succ_eq_append_getElem h, DFA.eval_append_singleton, List.take_zero,
    DFA.eval_nil]

variable [Fintype α] [Fintype σ]

open Classical in
/-- The MSO sentence describing the accepting runs of the DFA `M`. With one set variable `X_q`
per state `q` (indexed through `Fintype.equivFin σ`), it says that either the word is empty and
the start state is accepting, or the word is nonempty and there are sets `X_q` such that
* the first position, with letter `a`, is in `X_{δ(q₀, a)}`;
* if `x` is in `X_q` and its successor `y` has letter `a`, then `y` is in `X_{δ(q, a)}`;
* the last position is in no `X_q` with `q` rejecting. -/
noncomputable def dfaSentence (M : DFA α σ) : Sentence α :=
  let X : σ → Fin (Fintype.card σ) := Fintype.equivFin σ
  let init : Formula α 1 (Fintype.card σ) :=
    imp (first (Fin.last 0)) (Formula.iInf Finset.univ fun a =>
      imp (letter a (Fin.last 0)) (mem (Fin.last 0) (X (M.step M.start a))))
  let trans : Formula α 2 (Fintype.card σ) :=
    imp (succ (Fin.castSucc (Fin.last 0)) (Fin.last 1)) (Formula.iInf Finset.univ fun q =>
      Formula.iInf Finset.univ fun a =>
        imp (mem (Fin.castSucc (Fin.last 0)) (X q))
          (imp (letter a (Fin.last 1)) (mem (Fin.last 1) (X (M.step q a)))))
  let final : Formula α 1 (Fintype.card σ) :=
    imp (last (Fin.last 0)) (Formula.iInf (Finset.univ.filter (· ∉ M.accept)) fun q =>
      not (mem (Fin.last 0) (X q)))
  and (imp (not (ex top)) (if M.start ∈ M.accept then top else falsum))
    (imp (ex top) (exSets (and (all init) (and (all (all trans)) (all final)))))

variable (M : DFA α σ)

/-- **Regular ⇒ MSO.** The sentence `dfaSentence M` defines the language accepted by `M`. -/
theorem dfaSentence_language : (dfaSentence M).language = M.accepts := by
  classical
  ext w
  rw [DFA.mem_accepts]
  change (dfaSentence M).Realize (fun i : Fin w.length => w[i]) Fin.elim0 Fin.elim0 ↔ _
  let X : σ → Fin (Fintype.card σ) := Fintype.equivFin σ
  have hX : ∀ q q', X q = X q' ↔ q = q' := fun q q' => (Fintype.equivFin σ).apply_eq_iff_eq
  simp only [dfaSentence, realize_and, realize_imp, realize_not, realize_ex, realize_top,
    realize_exSets, realize_all, realize_iInf, realize_first, realize_succ, realize_last,
    realize_letter, realize_mem, Finset.mem_univ, Finset.mem_filter, true_and, Fin.snoc_last,
    Fin.snoc_castSucc, true_implies]
  by_cases hw : w.length = 0
  · have hno : ¬ ∃ _ : Fin w.length, True := fun ⟨i, _⟩ => absurd i.isLt (by omega)
    have he : M.eval w = M.start := by rw [List.eq_nil_of_length_eq_zero hw, DFA.eval_nil]
    rw [he]
    constructor
    · rintro ⟨h, -⟩
      by_contra hs
      have h' := h hno
      simp only [hs, ↓reduceIte, realize_falsum] at h'
    · intro hs
      refine ⟨fun _ => ?_, fun h => absurd h hno⟩
      simp only [hs, ↓reduceIte, realize_top]
  · have hyes : ∃ _ : Fin w.length, True := ⟨⟨0, by omega⟩, trivial⟩
    constructor
    · rintro ⟨-, h⟩
      obtain ⟨W, hinit, htrans, hfinal⟩ := h hyes
      -- The sets contain the run: position `i` is in `X_q` for the state `q` after `i + 1`
      -- letters.
      have run : ∀ (i : ℕ) (hi : i < w.length),
          (⟨i, hi⟩ : Fin w.length) ∈ W (X (M.eval (w.take (i + 1)))) := by
        intro i
        induction i with
        | zero =>
          intro hi
          rw [eval_take_one M w hi]
          exact hinit ⟨0, hi⟩ rfl w[0] rfl
        | succ i ih =>
          intro hi
          rw [eval_take_succ_succ M w i hi]
          exact htrans ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl _ _ (ih (by omega)) rfl
      by_contra hacc
      have hlast := run (w.length - 1) (by omega)
      rw [Nat.sub_add_cancel (by omega), List.take_length] at hlast
      exact hfinal ⟨w.length - 1, by omega⟩ (by simp only; omega) _ hacc hlast
    · intro hacc
      refine ⟨fun h => absurd hyes h, fun _ => ?_⟩
      refine ⟨fun c => {i | X (M.eval (w.take (i + 1))) = c}, ?_, ?_, ?_⟩
      · intro i hi a ha
        change X (M.eval (w.take (i + 1))) = X (M.step M.start a)
        rw [hX]
        have hi0 : (i : ℕ) = 0 := hi
        obtain ⟨i, hi'⟩ := i
        simp only at hi0
        subst hi0
        rw [eval_take_one M w hi', ← ha]
        rfl
      · intro i j hij q a hq ha
        change X (M.eval (w.take (j + 1))) = X (M.step q a)
        change X (M.eval (w.take (i + 1))) = X q at hq
        rw [hX] at hq ⊢
        obtain ⟨j, hj⟩ := j
        simp only at hij
        subst hij
        rw [eval_take_succ_succ M w i hj, hq, ← ha]
        rfl
      · intro i hi q hq hmem
        change X (M.eval (w.take (i + 1))) = X q at hmem
        rw [hX] at hmem
        rw [hi, List.take_length] at hmem
        exact hq (hmem ▸ hacc)

end DFA

/-- **Regular ⇒ MSO.** Every regular language over a finite alphabet is MSO-definable. -/
theorem definable_of_isRegular [Finite α] {L : Language α} (h : L.IsRegular) : Definable L := by
  have := Fintype.ofFinite α
  obtain ⟨σ, _, M, rfl⟩ := h
  exact ⟨dfaSentence M, dfaSentence_language M⟩

/-- **The Büchi–Elgot–Trakhtenbrot theorem.** Over a finite alphabet, a language of finite words
is MSO-definable if and only if it is regular [Büchi][Buchi1960], [Elgot][Elgot1961],
[Libkin, Theorem 7.21][Libkin2004], [Thomas, Section 3][Thomas1997]. -/
theorem definable_iff_isRegular [Finite α] {L : Language α} : Definable L ↔ L.IsRegular :=
  ⟨Definable.isRegular, definable_of_isRegular⟩

/-! ### Even length -/

/-- The MSO sentence of the words of even length: there is a set `X` containing the first
position, alternating along successors, and not containing the last position. -/
def evenSentence : Sentence α :=
  let X : Fin 1 := Fin.last 0
  let x : Fin 2 := Fin.castSucc (Fin.last 0)
  let y : Fin 2 := Fin.last 1
  exSet (and (all (imp (first (Fin.last 0)) (mem (Fin.last 0) X)))
    (and (all (all (imp (succ x y)
      (and (imp (mem x X) (not (mem y X))) (imp (not (mem x X)) (mem y X))))))
      (all (imp (last (Fin.last 0)) (not (mem (Fin.last 0) X))))))

/-- `evenSentence` defines the words of even length. -/
theorem evenSentence_language : (evenSentence : Sentence α).language = {w | Even w.length} := by
  ext w
  change (evenSentence : Sentence α).Realize (fun i : Fin w.length => w[i]) Fin.elim0 Fin.elim0 ↔
    Even w.length
  simp only [evenSentence, realize_exSet, realize_and, realize_all, realize_imp, realize_first,
    realize_mem, realize_succ, realize_not, realize_last, Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · rintro ⟨S, hfirst, hsucc, hlast⟩
    -- Position `i` is in `S` exactly when `i` is even.
    have key : ∀ (i : ℕ) (hi : i < w.length), ((⟨i, hi⟩ : Fin w.length) ∈ S ↔ Even i) := by
      intro i
      induction i with
      | zero => exact fun hi => ⟨fun _ => ⟨0, rfl⟩, fun _ => hfirst ⟨0, hi⟩ rfl⟩
      | succ i ih =>
        intro hi
        have h := hsucc ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl
        rw [Nat.even_add_one, ← ih (by omega)]
        exact ⟨fun hs hs' => h.1 hs' hs, fun hs => h.2 hs⟩
    rcases Nat.eq_zero_or_pos w.length with h0 | hpos
    · rw [h0]
      exact ⟨0, rfl⟩
    · have h := key (w.length - 1) (by omega)
      have hn := hlast ⟨w.length - 1, by omega⟩ (by simp only; omega)
      rw [h] at hn
      have : w.length = w.length - 1 + 1 := by omega
      rw [this, Nat.even_add_one]
      exact hn
  · intro heven
    refine ⟨{i | Even (i : ℕ)}, fun i hi => ?_, fun i j hij => ?_, fun i hi => ?_⟩
    · change Even (i : ℕ)
      rw [hi]
      exact ⟨0, rfl⟩
    · change (Even (i : ℕ) → ¬ Even (j : ℕ)) ∧ (¬ Even (i : ℕ) → Even (j : ℕ))
      rw [hij, Nat.even_add_one]
      exact ⟨fun h h' => h' h, fun h => h⟩
    · change ¬ Even (i : ℕ)
      have : w.length = (i : ℕ) + 1 := hi.symm
      rw [this, Nat.even_add_one] at heven
      exact heven

/-- The words of even length form an MSO-definable language, over any alphabet. -/
theorem definable_even : Definable {w : List α | Even w.length} :=
  ⟨evenSentence, evenSentence_language⟩

end Cslib.Logic.WordMSO
