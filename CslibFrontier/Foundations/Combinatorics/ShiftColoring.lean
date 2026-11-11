/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Nat.LogStar
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Fin.Tuple
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FinCases

/-!
# Shift colourings and the speedup lemma

A *shift colouring* of the increasing `(k + 1)`-tuples from `{0, …, m - 1}` gives the first and
last `(k + 1)`-entry windows of every increasing `(k + 2)`-tuple different colours. These are the
`(k + 1)`-ary colourings of [Laurinharju and Suomela][LaurinharjuSuomela2014], i.e. proper
colourings of the shift graph. Their *speedup lemma* lowers the arity by one at the cost of an
exponential in the number of colours. Iterating it, a shift colouring of `(k + 1)`-tuples with
`c` colours forces `m ≤ 2 ^ 2 ^ ⋯ ^ c` with `k` exponentials, hence `log* m ≤ k + log* c`. This is
the combinatorial core of Linial's lower bound for colouring oriented cycles.

## Main definitions

* `Cslib.IsShiftColoring`: a shift colouring of increasing tuples.
* `Cslib.IsShiftColoring.speedup`: the colouring of shorter tuples by sets of colours.

## Main results

* `Cslib.IsShiftColoring.speedup_isShiftColoring`: the speedup lemma.
* `Cslib.IsShiftColoring.card_le`: a shift colouring of `1`-tuples needs at least `m` colours.
* `Cslib.IsShiftColoring.le_iterate`: `m ≤ (2 ^ ·)^[k] |C|` for a shift colouring of
  `(k + 1)`-tuples with colours in `C`.
* `Cslib.IsShiftColoring.logStar_le`: `log* m ≤ k + log* |C|`.

## References

* [J. Laurinharju and J. Suomela, *Brief announcement: Linial's lower bound made
  easy*][LaurinharjuSuomela2014]
-/

public section

namespace Cslib

/-- A colouring `f` of the increasing `(k + 1)`-tuples from `{0, …, m - 1}` is a *shift colouring*
if every increasing `(k + 2)`-tuple `a` gives its first and last `(k + 1)`-entry windows different
colours: `f (init a) ≠ f (tail a)`. These are the `(k + 1)`-ary colourings of
[Laurinharju and Suomela][LaurinharjuSuomela2014], i.e. proper colourings of the shift graph. -/
@[expose] def IsShiftColoring {C : Type*} (m k : ℕ) (f : (Fin (k + 1) → ℕ) → C) : Prop :=
  ∀ a : Fin (k + 2) → ℕ, StrictMono a → (∀ i, a i < m) → f (Fin.init a) ≠ f (Fin.tail a)

namespace IsShiftColoring

variable {C : Type*} {m k : ℕ}

open Classical in
/-- The speedup of a colouring of `(k + 2)`-tuples: an increasing `(k + 1)`-tuple `b` receives the
set of colours of all its increasing extensions `snoc b y` with `y < m`. -/
noncomputable def speedup (m : ℕ) (f : (Fin (k + 2) → ℕ) → C) : (Fin (k + 1) → ℕ) → Finset C :=
  fun b => ((Finset.range m).filter (fun y => b (Fin.last k) < y)).image
    (fun y => f (Fin.snoc b y))

private theorem tail_snoc {n : ℕ} (a : Fin (n + 1) → ℕ) (y : ℕ) :
    Fin.tail (Fin.snoc a y : Fin (n + 2) → ℕ) = Fin.snoc (Fin.tail a) y := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.tail, Fin.succ_last, Fin.snoc_last]
  · simp only [Fin.tail, Fin.succ_castSucc, Fin.snoc_castSucc]

private theorem strictMono_snoc {n : ℕ} {a : Fin (n + 1) → ℕ} (ha : StrictMono a) {y : ℕ}
    (hy : a (Fin.last n) < y) : StrictMono (Fin.snoc a y : Fin (n + 2) → ℕ) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]
    exact hy
  · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
    exact ha Fin.castSucc_lt_succ

/-- **The speedup lemma** [Laurinharju and Suomela][LaurinharjuSuomela2014]: the speedup of a shift
colouring of `(k + 2)`-tuples is a shift colouring of `(k + 1)`-tuples, with colours the subsets of
the original colours. -/
theorem speedup_isShiftColoring {f : (Fin (k + 2) → ℕ) → C} (hf : IsShiftColoring m (k + 1) f) :
    IsShiftColoring m k (speedup m f) := by
  classical
  intro a ha ham heq
  -- the colour of `a` itself lies in the speedup of `init a`, hence in that of `tail a`
  have hmem : f a ∈ speedup m f (Fin.init a) := by
    refine Finset.mem_image.2 ⟨a (Fin.last _), ?_, ?_⟩
    · refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (ham _), ?_⟩
      simp only [Fin.init]
      exact ha (Fin.castSucc_lt_last _)
    · rw [Fin.snoc_init_self]
  rw [heq] at hmem
  obtain ⟨y, hy, hfy⟩ := Finset.mem_image.1 hmem
  obtain ⟨hym, hlt⟩ := Finset.mem_filter.1 hy
  have hlt' : a (Fin.last _) < y := by simpa [Fin.tail] using hlt
  -- so some increasing extension `snoc a y` has the colour of `a`
  refine hf (Fin.snoc a y) (strictMono_snoc ha hlt') (fun i => ?_) ?_
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using Finset.mem_range.1 hym
    · simpa using ham j
  · rw [Fin.init_snoc, tail_snoc, hfy]

/-- A shift colouring of the `1`-tuples from `{0, …, m - 1}` is injective, so it needs at least
`m` colours. -/
theorem card_le {f : (Fin 1 → ℕ) → C} [Fintype C] (hf : IsShiftColoring m 0 f) :
    m ≤ Fintype.card C := by
  have hinj : Function.Injective (fun y : Fin m => f ![(y : ℕ)]) := by
    suffices h : ∀ y y' : Fin m, (y : ℕ) < y' → f ![(y : ℕ)] ≠ f ![(y' : ℕ)] by
      intro y y' hyy
      by_contra hne
      rcases lt_or_gt_of_ne (Fin.val_injective.ne hne) with hlt | hlt
      · exact h y y' hlt hyy
      · exact h y' y hlt hyy.symm
    intro y y' hlt
    have hmono : StrictMono (![(y : ℕ), y'] : Fin 2 → ℕ) := by
      rw [Fin.strictMono_iff_lt_succ]
      intro i
      fin_cases i
      exact hlt
    have h := hf ![(y : ℕ), y'] hmono (fun i => by fin_cases i <;> simp)
    have hinit : Fin.init (![(y : ℕ), y'] : Fin 2 → ℕ) = ![(y : ℕ)] := by
      funext i; fin_cases i; rfl
    have htail : Fin.tail (![(y : ℕ), y'] : Fin 2 → ℕ) = ![(y' : ℕ)] := by
      funext i; fin_cases i; rfl
    rwa [hinit, htail] at h
  simpa using Fintype.card_le_of_injective _ hinj

/-- A shift colouring of increasing `(k + 1)`-tuples from `{0, …, m - 1}` with colours in `C`
forces `m ≤ 2 ^ 2 ^ ⋯ ^ |C|` with `k` exponentials. -/
theorem le_iterate {C : Type*} [Fintype C] {f : (Fin (k + 1) → ℕ) → C}
    (hf : IsShiftColoring m k f) : m ≤ (2 ^ ·)^[k] (Fintype.card C) := by
  induction k generalizing C with
  | zero => exact hf.card_le
  | succ k ih =>
    classical
    have := ih (speedup_isShiftColoring hf)
    rwa [Fintype.card_finset, ← Function.iterate_succ_apply] at this

/-- A shift colouring of increasing `(k + 1)`-tuples from `{0, …, m - 1}` with colours in `C` has
`log* m ≤ k + log* |C|`. -/
theorem logStar_le {C : Type*} [Fintype C] {f : (Fin (k + 1) → ℕ) → C}
    (hf : IsShiftColoring m k f) : Nat.logStar m ≤ k + Nat.logStar (Fintype.card C) :=
  Nat.logStar_le_iff.2 ((hf.le_iterate).trans (Nat.iterate_two_pow_le_twoTower _ _))

end IsShiftColoring

end Cslib
