/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Resolution.Proof

/-!
# The Boolean existential pebble game

**Width lower bounds from Duplicator strategies** [Atserias and Dalmau, Lemma 3]
[AtseriasDalmau2008]. Atserias and Dalmau characterize resolution width by the Boolean existential
pebble game on a CNF formula `φ`. Spoiler places pebbles on variables, Duplicator answers with truth
values, and Spoiler wins when the pebbled partial assignment falsifies a clause of `φ`. A **winning
strategy for Duplicator with `k` pebbles** (`Cslib.Logic.PL.CNF.DuplicatorStrategy`, their
Definition 2) is a nonempty family of partial assignments on at most `k` variables that falsify no
clause of `φ`, closed under restriction, and such that each assignment on fewer than `k` variables
extends to any further variable.

A partial assignment is a total assignment `σ` read only on a finite set `d` of variables, as in
`Complexity.Logics.Propositional.Resolution.SpaceWidth`, and `Cslib.Logic.PL.CNF.Falsifies σ d c`
says that every literal of `c` is on a variable of `d` and false under `σ`.

If Duplicator has a winning strategy with `w + 1` pebbles, then `φ` has no refutation of width `w`
(`Cslib.Logic.PL.CNF.DuplicatorStrategy.not_refutableInWidth`). By induction along a proof of width
`w`, no position of the strategy falsifies a line: a position falsifying a resolvent restricts to
the at most `w` variables of the resolvent and extends to the resolved variable, and the extension
falsifies one of the two premises. Since the strategy is nonempty and every position falsifies the
empty clause, the proof is not a refutation.

This is the direction of Atserias and Dalmau's characterization (their Theorem 2) used for lower
bounds. The converse direction, from the absence of narrow refutations to a strategy (their
Lemma 2), is the first step of the proof of the space–width inequality in
`Complexity.Logics.Propositional.Resolution.SpaceWidth`, where the strategy is kept internal.

The mathematical symbols of the available copy of Atserias and Dalmau's paper do not extract; the
statements here are ours, with the off-by-one conventions of the library's
`Cslib.Logic.PL.CNF.RefutableInWidth`. The game is unrelated to the black pebble game of
`Complexity.Computability.Pebbling`.

## Main definitions

* `Cslib.Logic.PL.CNF.Falsifies`: a partial assignment falsifies a clause.
* `Cslib.Logic.PL.CNF.DuplicatorStrategy`: a winning strategy for Duplicator in the Boolean
  existential `k`-pebble game.

## Main results

* `Cslib.Logic.PL.CNF.DuplicatorStrategy.not_falsifies_of_isProof`: no position falsifies a line of
  a proof of width `w`, for `w + 1` pebbles.
* `Cslib.Logic.PL.CNF.DuplicatorStrategy.not_refutableInWidth`: **a Duplicator strategy with
  `w + 1` pebbles rules out refutations of width `w`**.

## References

* [A. Atserias, V. Dalmau, *A combinatorial characterization of resolution
  width*][AtseriasDalmau2008]
-/

public section

namespace Cslib.Logic.PL

open scoped Finset

namespace CNF

variable {V : Type*}

/-- The assignment `σ`, read on `d`, **falsifies** `c`: every literal of `c` is on a variable of
`d` and false under `σ`. -/
@[expose] def Falsifies (σ : V → Bool) (d : Finset V) (c : Clause V) : Prop :=
  ∀ l ∈ c, l.1 ∈ d ∧ σ l.1 ≠ l.2

/-- Falsifying on `d` depends only on the values on `d`. -/
theorem Falsifies.congr {σ τ : V → Bool} {d : Finset V} {c : Clause V} (h : Falsifies σ d c)
    (hστ : ∀ x ∈ d, τ x = σ x) : Falsifies τ d c := fun l hl =>
  ⟨(h l hl).1, by rw [hστ _ (h l hl).1]; exact (h l hl).2⟩

/-- Every partial assignment falsifies the empty clause. -/
@[simp] theorem falsifies_nil (σ : V → Bool) (d : Finset V) : Falsifies σ d [] := by
  simp [Falsifies]

/-- A **winning strategy for Duplicator in the Boolean existential `k`-pebble game** on `φ`
[Atserias and Dalmau, Definition 2][AtseriasDalmau2008]: a nonempty family of partial assignments
`(σ, d)`, read on at most `k` variables, that falsify no clause of `φ`, closed under restriction,
and such that every assignment on fewer than `k` variables extends to any further variable. -/
structure DuplicatorStrategy [DecidableEq V] (φ : CNF V) (k : ℕ) where
  /-- The positions of the strategy: `σ` read on `d`. -/
  Mem : (V → Bool) → Finset V → Prop
  /-- There is a position. -/
  nonempty : ∃ σ d, Mem σ d
  /-- Positions are read on at most `k` variables. -/
  card_le {σ : V → Bool} {d : Finset V} : Mem σ d → #d ≤ k
  /-- Positions are closed under restriction. -/
  restrict {σ : V → Bool} {d e : Finset V} : Mem σ d → e ⊆ d → Mem σ e
  /-- A position on fewer than `k` variables extends to any further variable. -/
  extend {σ : V → Bool} {d : Finset V} : Mem σ d → #d < k → ∀ v, ∃ τ : V → Bool,
    (∀ x ∈ d, τ x = σ x) ∧ Mem τ (insert v d)
  /-- No position falsifies a clause of `φ`. -/
  not_falsifies {σ : V → Bool} {d : Finset V} : Mem σ d → ∀ c ∈ φ, ¬ Falsifies σ d c

namespace DuplicatorStrategy

variable [DecidableEq V] {φ : CNF V} {w : ℕ}

/-- **No position falsifies a line of a narrow proof** [Atserias and Dalmau, Lemma 3]
[AtseriasDalmau2008]: for a strategy with `w + 1` pebbles, no position falsifies a line of a proof
from `φ` whose lines have width at most `w`. -/
theorem not_falsifies_of_isProof (S : DuplicatorStrategy φ (w + 1)) {ls : List (Clause V)}
    (hp : φ.IsProof ls) (hw : ∀ c ∈ ls, c.width ≤ w) :
    ∀ c ∈ ls, ∀ σ d, S.Mem σ d → ¬ Falsifies σ d c := by
  induction hp with
  | nil => simp
  | mem h hc ih =>
    intro c' hc' σ d hσ
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact S.not_falsifies hσ _ hc
    · exact ih (fun c h => hw c (List.mem_cons_of_mem _ h)) c' hc' σ d hσ
  | @resolvent ls c₁ c₂ v h h₁ h₂ hv₁ hv₂ ih =>
    intro c' hc' σ d hσ hf
    have ih' := ih (fun c h => hw c (List.mem_cons_of_mem _ h))
    rcases List.mem_cons.1 hc' with rfl | hc'
    · -- restrict to the variables of the resolvent and extend to `v`
      set R := c₁.resolvent c₂ v
      set d₀ := R.toFinset.image Prod.fst
      have hd₀ : d₀ ⊆ d := by
        intro x hx
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hx
        exact (hf l (List.mem_toFinset.1 hl)).1
      have hcard : #d₀ < w + 1 :=
        Nat.lt_succ_of_le (Finset.card_image_le.trans (hw R List.mem_cons_self))
      obtain ⟨τ, hτ, hτm⟩ := S.extend (S.restrict hσ hd₀) hcard v
      have hfR : Falsifies τ d₀ R := fun l hl =>
        ⟨Finset.mem_image_of_mem _ (List.mem_toFinset.2 hl),
          by rw [hτ _ (Finset.mem_image_of_mem _ (List.mem_toFinset.2 hl))]; exact (hf l hl).2⟩
      -- the extension falsifies the premise whose literal on `v` it makes false
      cases hτv : τ v
      · refine ih' c₁ h₁ τ _ hτm fun l hl => ?_
        by_cases hl' : l = (v, true)
        · subst hl'
          exact ⟨Finset.mem_insert_self _ _, by simp [hτv]⟩
        · have := hfR l (Clause.mem_resolvent.2 (Or.inl ⟨hl, hl'⟩))
          exact ⟨Finset.mem_insert_of_mem this.1, this.2⟩
      · refine ih' c₂ h₂ τ _ hτm fun l hl => ?_
        by_cases hl' : l = (v, false)
        · subst hl'
          exact ⟨Finset.mem_insert_self _ _, by simp [hτv]⟩
        · have := hfR l (Clause.mem_resolvent.2 (Or.inr ⟨hl, hl'⟩))
          exact ⟨Finset.mem_insert_of_mem this.1, this.2⟩
    · exact ih' c' hc' σ d hσ hf

/-- **A Duplicator strategy with `w + 1` pebbles rules out refutations of width `w`** [Atserias and
Dalmau, Lemma 3][AtseriasDalmau2008]. -/
theorem not_refutableInWidth (S : DuplicatorStrategy φ (w + 1)) : ¬ φ.RefutableInWidth w := by
  rintro ⟨ls, hp, hnil, hw⟩
  obtain ⟨σ, d, hσ⟩ := S.nonempty
  exact S.not_falsifies_of_isProof hp hw [] hnil σ d hσ (falsifies_nil σ d)

end DuplicatorStrategy

end CNF

end Cslib.Logic.PL
