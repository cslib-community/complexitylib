/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.Resolution.PigeonholeSpace
import Complexity.Logics.Propositional.Resolution.SpaceWidth

/-!
# Tests: Duplicator strategies and the extended pigeonhole formula

Duplicator strategies exist for satisfiable formulas and with no pebble, and fail for `x ∧ ¬x`
with one pebble. The extended pigeonhole formula is a `3`-CNF that is unsatisfiable exactly when
there are more pigeons than holes. Its width and clause-space lower bounds apply to formulas that
are refutable, and the space bound beats the bound `3` that holds for every formula without the
empty clause. Atserias and Dalmau's Lemma 2 gives back a strategy from the width bound, and the
space bound also follows from the strategy directly.
-/

namespace ComplexityTests.ProofComplexity.PigeonholeSpace

open Cslib Cslib.Logic.PL

/-! ### Duplicator strategies -/

/-- A satisfying assignment, read on any set of at most `k` variables, is a Duplicator strategy
with `k` pebbles. -/
private def strategyOfEval {V : Type*} [DecidableEq V] {φ : CNF V} {σ : V → Bool}
    (hσ : φ.eval σ = true) (k : ℕ) : CNF.DuplicatorStrategy φ k where
  Mem τ d := Finset.card d ≤ k ∧ ∀ x ∈ d, τ x = σ x
  nonempty := ⟨σ, ∅, by simp⟩
  card_le h := h.1
  restrict h hed := ⟨(Finset.card_le_card hed).trans h.1, fun x hx => h.2 x (hed hx)⟩
  extend h hd v := ⟨σ, fun x hx => (h.2 x hx).symm, (Finset.card_insert_le _ _).trans hd,
    fun _ _ => rfl⟩
  not_falsifies h c hc hf := by
    obtain ⟨l, hl, hσl⟩ := (Clause.eval_eq_true_iff σ c).1 ((CNF.eval_eq_true_iff σ φ).1 hσ c hc)
    exact (hf l hl).2 (by rw [h.2 _ (hf l hl).1]; exact hσl)

/-- So satisfiable formulas are refutable in no width (a sanity check of
`CNF.DuplicatorStrategy.not_refutableInWidth`). -/
example {V : Type*} [DecidableEq V] {φ : CNF V} (hφ : φ.Satisfiable) (w : ℕ) :
    ¬ φ.RefutableInWidth w :=
  hφ.elim fun _ hσ => (strategyOfEval hσ (w + 1)).not_refutableInWidth

/-- `x₀ ∧ ¬x₀`. -/
private def ψ : CNF ℕ := [[(0, true)], [(0, false)]]

/-- With no pebble, the strategy containing only the empty position wins on any formula without the
empty clause, here `x₀ ∧ ¬x₀`. -/
example : CNF.DuplicatorStrategy ψ 0 where
  Mem _ d := d = ∅
  nonempty := ⟨fun _ => false, ∅, rfl⟩
  card_le h := by simp [h]
  restrict h hed := Finset.subset_empty.1 (h ▸ hed)
  extend _ hd := absurd hd (Nat.not_lt_zero _)
  not_falsifies h c hc hf := by
    subst h
    simp only [ψ, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simpa using (hf _ List.mem_cons_self).1

/-- With one pebble, Duplicator loses on `x₀ ∧ ¬x₀`: extending the empty position to `x₀`
falsifies one of the two unit clauses. -/
example : CNF.DuplicatorStrategy ψ 1 → False := by
  intro S
  obtain ⟨σ, d, h⟩ := S.nonempty
  have h₀ := S.restrict h (Finset.empty_subset d)
  obtain ⟨τ, -, hτ⟩ := S.extend h₀ (by simp) 0
  cases hτ0 : τ 0
  · refine S.not_falsifies hτ [(0, true)] (by simp [ψ]) fun l hl => ?_
    rw [List.mem_singleton.1 hl]
    simp [hτ0]
  · refine S.not_falsifies hτ [(0, false)] (by simp [ψ]) fun l hl => ?_
    rw [List.mem_singleton.1 hl]
    simp [hτ0]

/-! ### The extended pigeonhole formula -/

/-- `EPHP^2_1`: two start, two stop, two step and one hole clause. -/
example : (CNF.pigeonholeExt 2 1).length = 7 := by decide

/-- `EPHP^3_2` is unsatisfiable and `EPHP^2_2` is satisfiable. -/
example : ¬ (CNF.pigeonholeExt 3 2).Satisfiable ∧ (CNF.pigeonholeExt 2 2).Satisfiable :=
  ⟨fun h => absurd (CNF.satisfiable_pigeonholeExt_iff.1 h) (by decide),
    CNF.satisfiable_pigeonholeExt_iff.2 le_rfl⟩

/-- `EPHP^3_2` is refutable in some clause space, hence in some width, but not in width `1`. -/
example : (∃ w, (CNF.pigeonholeExt 3 2).RefutableInWidth w) ∧
    ¬ (CNF.pigeonholeExt 3 2).RefutableInWidth 1 := by
  refine ⟨?_, CNF.not_refutableInWidth_pigeonholeExt 3 1⟩
  obtain ⟨s, hs⟩ := CNF.exists_refutableInSpace_iff_not_satisfiable.2
    (CNF.not_satisfiable_pigeonholeExt (by decide : 2 < 3))
  exact ⟨_, hs.refutableInWidth fun _ hc => CNF.width_le_three_of_mem_pigeonholeExt hc⟩

/-- `EPHP^6_5` is refutable in some clause space, and every such refutation needs clause space at
least `5`, more than the bound `3` for formulas without the empty clause. -/
example : (∃ s, (CNF.pigeonholeExt 6 5).RefutableInSpace s) ∧
    ∀ s, (CNF.pigeonholeExt 6 5).RefutableInSpace s → 5 ≤ s :=
  ⟨CNF.exists_refutableInSpace_iff_not_satisfiable.2
      (CNF.not_satisfiable_pigeonholeExt (by decide : 5 < 6)),
    fun _ h => CNF.le_of_refutableInSpace_pigeonholeExt h⟩

/-- Atserias and Dalmau's Lemma 2 rebuilds a strategy from the width bound: `EPHP^m_4` is a
`3`-CNF with no refutation of width `3`, so Duplicator wins with `4` pebbles. -/
example (m : ℕ) : Nonempty (CNF.DuplicatorStrategy (CNF.pigeonholeExt m 4) 4) :=
  (CNF.DuplicatorStrategy.nonempty_iff_not_refutableInWidth
    fun _ hc => (Nat.lt_succ_of_le (CNF.width_le_three_of_mem_pigeonholeExt hc)).ne).2
    (CNF.not_refutableInWidth_pigeonholeExt m 3)

/-- The space bound straight from the strategy: `n + 1` pebbles on a `3`-CNF give clause space at
least `n + 1`. -/
example (m n s : ℕ) (h : (CNF.pigeonholeExt m (n + 1)).RefutableInSpace s) : n + 1 ≤ s := by
  have := (CNF.pigeonholeExtStrategy m n).add_three_le
    (fun _ hc => CNF.width_le_three_of_mem_pigeonholeExt hc) h
  omega

/-- The width and space bounds for any numbers of pigeons and holes. -/
example (m n w s : ℕ) (hw : (CNF.pigeonholeExt m n).RefutableInWidth w)
    (hs : (CNF.pigeonholeExt m n).RefutableInSpace s) : n ≤ w ∧ n ≤ s :=
  ⟨CNF.le_of_refutableInWidth_pigeonholeExt hw, CNF.le_of_refutableInSpace_pigeonholeExt hs⟩

end ComplexityTests.ProofComplexity.PigeonholeSpace
