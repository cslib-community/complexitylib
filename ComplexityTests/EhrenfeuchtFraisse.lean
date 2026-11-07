/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.EhrenfeuchtFraisse.FiniteLinearOrder

/-! # Ehrenfeucht–Fraïssé games: checked instances

Concrete games on the finite linear orders `Fin m`, at the sharp threshold `2 ^ n - 1`, a
distinguishing sentence of quantifier rank `2`, and a client of the nondefinability of EVEN. -/

@[expose] public section

namespace Cslib.Tests.EhrenfeuchtFraisse

open FirstOrder Language Structure
open Cslib.Logic.FO Cslib.Logic.FO.FiniteLinearOrder

instance (m : ℕ) : Language.order.Structure (Fin m) := orderStructure _

instance (m : ℕ) : Language.order.OrderedStructure (Fin m) := ⟨fun _ => Iff.rfl⟩

/-- "Some element has an element below it and an element above it": a sentence of quantifier
rank `2` that holds in `Fin 3` and fails in `Fin 2`. -/
def hasMiddle : Language.order.Sentence :=
  ∃' ((∃' ((&1).lt (&0))) ⊓ ∃' ((&0).lt (&1)))

theorem quantifierRank_hasMiddle : quantifierRank hasMiddle = 2 := by
  simp [hasMiddle, Term.lt, Term.le]

theorem fin3_realize_hasMiddle : Fin 3 ⊨ hasMiddle := by
  simp only [hasMiddle, Sentence.Realize, Formula.Realize, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, Term.realize_lt]
  exact ⟨1, ⟨0, by decide⟩, ⟨2, by decide⟩⟩

theorem fin2_not_realize_hasMiddle : ¬ Fin 2 ⊨ hasMiddle := by
  simp only [hasMiddle, Sentence.Realize, Formula.Realize, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, Term.realize_lt, not_exists, not_and]
  decide

/-- Spoiler wins the `2`-round game on `Fin 2` and `Fin 3`, as `hasMiddle` predicts. -/
example : ¬ DuplicatorWins Language.order 2 (default : Fin 0 → Fin 2) (default : Fin 0 → Fin 3) :=
  fun h => fin2_not_realize_hasMiddle ((duplicatorWins_iff_forall_sentence.1 h hasMiddle
    quantifierRank_hasMiddle.le).2 fin3_realize_hasMiddle)

/-- The same conclusion from the size characterization. -/
example :
    ¬ DuplicatorWins Language.order 2 (default : Fin 0 → Fin 2) (default : Fin 0 → Fin 3) := by
  rw [duplicatorWins_iff_card, Nat.card_fin, Nat.card_fin]
  decide

/-- Duplicator wins the `2`-round game on `Fin 3` and `Fin 4`: both sizes reach the sharp
threshold `2 ^ 2 - 1 = 3`, below the threshold `2 ^ 2 = 4` of the textbook statement. -/
example : DuplicatorWins Language.order 2 (default : Fin 0 → Fin 3) (default : Fin 0 → Fin 4) := by
  rw [duplicatorWins_iff_card, Nat.card_fin, Nat.card_fin]
  decide

/-- Duplicator wins the `3`-round game on `Fin 7` and `Fin 1000`, so `hasMiddle` cannot tell
them apart; it cannot win the `3`-round game on `Fin 6` and `Fin 7`. -/
example : DuplicatorWins Language.order 3 (default : Fin 0 → Fin 7) (default : Fin 0 → Fin 1000) ∧
    ¬ DuplicatorWins Language.order 3 (default : Fin 0 → Fin 6) (default : Fin 0 → Fin 7) := by
  simp only [duplicatorWins_iff_card, Nat.card_fin]
  decide

/-- The Ehrenfeucht–Fraïssé theorem transfers truth of rank-`2` sentences between `Fin 3` and
`Fin 4`. -/
example : Fin 4 ⊨ hasMiddle :=
  (realize_iff_of_two_pow_le_card (M := Fin 3) (N := Fin 4) (n := 2) (by simp) (by simp)
    quantifierRank_hasMiddle.le).1 fin3_realize_hasMiddle

/-- A sentence of rank at most `2` separating `Fin 2` from `Fin 3` exists by sharpness. -/
example : ∃ φ : Language.order.Sentence, quantifierRank φ ≤ 2 ∧ Fin 2 ⊨ φ ∧ ¬ Fin 3 ⊨ φ :=
  exists_sentence_of_card_ne (by simp) (.inl (by simp))

/-- Client: ODD is not first-order definable on finite linear orders either. -/
example : ¬ ∃ φ : Language.order.Sentence, ∀ (M : Type) [_root_.LinearOrder M] [Finite M]
    [Language.order.Structure M] [Language.order.OrderedStructure M],
    M ⊨ φ ↔ ¬ Even (Nat.card M) := by
  rintro ⟨φ, hφ⟩
  refine not_exists_sentence_realize_iff_even 0 ⟨φ.not, fun M _ _ _ _ _ => ?_⟩
  rw [Sentence.realize_not, hφ, not_not]

/-- Back-and-forth systems are nonvacuous: positions related by an isomorphism form one, and
Duplicator wins from every position of it. -/
example (n : ℕ) (a : Fin 2 → Fin 3) :
    DuplicatorWins Language.order n a (Equiv.refl (Fin 3) ∘ a) :=
  IsBackAndForth.duplicatorWins (I := fun _ _ a b => b = Equiv.refl (Fin 3) ∘ a)
    ⟨fun h => h ▸ PartialIso.refl _, fun h c => ⟨c, by rw [h, Fin.comp_snoc]; rfl⟩,
      fun h d => ⟨d, by rw [h, Fin.comp_snoc]; rfl⟩⟩ rfl

/-! ### Formulas with free variables -/

/-- "Something lies strictly below the pebble `x₀`": a formula of quantifier rank `1` with one free
variable. -/
def hasBelow : Language.order.Formula (Fin 1) :=
  ∃' ((&0).lt (Term.var (Sum.inl 0)))

theorem quantifierRank_hasBelow : quantifierRank hasBelow = 1 := by
  simp [hasBelow, Term.lt, Term.le]

/-- Spoiler wins one round from the position `(0, 1)` on `Fin 3`: `hasBelow` separates the
pebbles, by the Ehrenfeucht–Fraïssé theorem for formulas with free variables. -/
example : ¬ DuplicatorWins Language.order 1 ![(0 : Fin 3)] ![(1 : Fin 3)] := by
  rw [duplicatorWins_iff_forall_formula]
  intro h
  have := h hasBelow quantifierRank_hasBelow.le
  simp only [hasBelow, Formula.Realize, BoundedFormula.realize_ex, Term.realize_lt,
    Term.realize_var, Sum.elim_inl] at this
  revert this
  decide

/-- The relabelings between formulas with free variables and bounded formulas preserve rank. -/
example : quantifierRank (BoundedFormula.relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1) hasBelow) = 1 ∧
    quantifierRank (hasBelow.relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)) = 1 := by
  rw [quantifierRank_relabel, quantifierRank_formula_relabel, quantifierRank_hasBelow]
  exact ⟨rfl, rfl⟩

/-! ### Explicit strategies, built and checked outside the defining module -/

/-- The copycat strategy on a structure against itself: answer every move with the same element.
Built by recursion through the exposed body of `Strategy`. -/
def copycat {M : Type} : (n : ℕ) → {k : ℕ} → (a : Fin k → M) → Strategy n a a
  | 0, _, _ => PUnit.unit
  | n + 1, _, a =>
    (fun c => ⟨c, copycat n (Fin.snoc a c)⟩, fun d => ⟨d, copycat n (Fin.snoc a d)⟩)

/-- Spoiler's move `c` is answered by `c`. -/
example {M : Type} (n k : ℕ) (a : Fin k → M) (c : M) : ((copycat (n + 1) a).1 c).1 = c := rfl

/-- The copycat strategy wins, by unfolding `Strategy.IsWinning` round by round. -/
theorem copycat_isWinning {M : Type} [Language.order.Structure M] :
    ∀ (n : ℕ) {k : ℕ} (a : Fin k → M), (copycat n a).IsWinning Language.order
  | 0, _, a => (Strategy.isWinning_zero _).2 (PartialIso.refl a)
  | n + 1, _, a => (Strategy.isWinning_succ _).2
      ⟨PartialIso.refl a, fun _ => copycat_isWinning n _, fun _ => copycat_isWinning n _⟩

/-- A one-round strategy between the orders `Fin 2` and `Fin 3` that is not a copy: every move is
answered by the least element. It wins, since one pebble cannot detect anything. -/
def toBottom : Strategy 1 (default : Fin 0 → Fin 2) (default : Fin 0 → Fin 3) :=
  (fun _ => ⟨0, PUnit.unit⟩, fun _ => ⟨0, PUnit.unit⟩)

theorem partialIso_one {M N : Type} [_root_.LinearOrder M] [_root_.LinearOrder N]
    [Language.order.Structure M] [Language.order.OrderedStructure M]
    [Language.order.Structure N] [Language.order.OrderedStructure N]
    (a : Fin 1 → M) (b : Fin 1 → N) : PartialIso Language.order a b := by
  refine ⟨fun i j => by simp [Subsingleton.elim i j], fun R f => ?_⟩
  cases R
  change RelMap (leSymb : Language.order.Relations 2) (a ∘ f) ↔
    RelMap (leSymb : Language.order.Relations 2) (b ∘ f)
  rw [relMap_leSymb, relMap_leSymb]
  simp only [Function.comp_apply, Subsingleton.elim (f 0) (f 1), le_refl]

theorem toBottom_isWinning : toBottom.IsWinning Language.order := by
  rw [Strategy.isWinning_succ]
  refine ⟨⟨fun i => i.elim0, fun R f => ?_⟩, fun c => ?_, fun d => ?_⟩
  · cases R
    exact (f 0).elim0
  · exact (Strategy.isWinning_zero _).2 (partialIso_one _ _)
  · exact (Strategy.isWinning_zero _).2 (partialIso_one _ _)

/-- Through `duplicatorWins_iff_exists_strategy`, the explicit strategy proves that Duplicator
wins the one-round game. -/
example : DuplicatorWins Language.order 1 (default : Fin 0 → Fin 2) (default : Fin 0 → Fin 3) :=
  duplicatorWins_iff_exists_strategy.2 ⟨toBottom, toBottom_isWinning⟩

/-- Conversely, a winning strategy can be extracted from a win and queried. -/
example : ∃ σ : Strategy 1 (default : Fin 0 → Fin 3) (default : Fin 0 → Fin 4),
    σ.IsWinning Language.order ∧ ∀ c, ((σ.1 c).2).IsWinning Language.order := by
  have h : DuplicatorWins Language.order 1 (default : Fin 0 → Fin 3) (default : Fin 0 → Fin 4) := by
    rw [duplicatorWins_iff_card, Nat.card_fin, Nat.card_fin]
    decide
  obtain ⟨σ, hσ⟩ := duplicatorWins_iff_exists_strategy.1 h
  exact ⟨σ, hσ, ((Strategy.isWinning_succ σ).1 hσ).2.1⟩

end Cslib.Tests.EhrenfeuchtFraisse
