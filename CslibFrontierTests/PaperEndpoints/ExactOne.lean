/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.ExactOneCounting
import Mathlib.Tactic.FinCases

/-! Signed exact-one compilation, rank-derived query budgets and declared unused bits. -/

open Cslib.Logic.PL Cslib.Logic.PL.ExactOne

/-- Two repeated signed rows on the first two bits; the third bit is unused. -/
@[expose] public def signedScopes (_ : Fin 2) : Finset (Fin 3) := {0, 1}

/-- The repeated equation is `x₀ + (1 - x₁) = 1`. -/
@[expose] public def signs (_ : Fin 2) (v : Fin 3) : Bool := v == 0

private theorem query_card (β : Bool) :
    Fintype.card {x : Fin 3 ⊕ Fin 1 → Bool //
      (query signedScopes signs β).eval x = true} =
    Fintype.card {x : Fin 3 ⊕ Fin 1 → Bool //
      (∀ j v, v ∈ signedScopes j → ∀ w, w ∈ signedScopes j →
        x (.inl v) = signs j v → x (.inl w) = signs j w → v = w) ∧
      ∀ j, (∃ v ∈ signedScopes j, x (.inl v) = signs j v) →
        TwoBoundary.atomEval x (TwoBoundary.port 1 β j.castSucc) =
          TwoBoundary.atomEval x (TwoBoundary.port 1 β j.succ)} := by
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  exact (TwoBoundary.query_eval _ _ _ _ _).trans
    (by simp only [exclusions_eval, coverage_eval])

/-- The source has four assignments, including both choices for the unused bit. -/
example : Fintype.card {x : Fin 3 → Bool // ∀ j, Holds (signedScopes j) (signs j) x} = 4 := by
  decide +kernel

/-- Four valid models plus four cancelling invalid extensions. -/
example : Fintype.card {x : Fin 3 ⊕ Fin 1 → Bool //
    (query signedScopes signs false).eval x = true} = 8 := by
  rw [query_card]
  decide +kernel

/-- Failed repeated coverages contribute equally under either boundary. -/
example : Fintype.card {x : Fin 3 ⊕ Fin 1 → Bool //
    (query signedScopes signs true).eval x = true} = 4 := by
  rw [query_card]
  decide +kernel

/-- Side constraints fix an otherwise unused bit; repeated side clauses are harmless. -/
@[expose] public def side : CNF (Fin 3) := [[(2, true)], [(2, true)]]

example : Fintype.card {x : Fin 3 ⊕ Fin 1 → Bool //
    (sideQuery side signedScopes signs false).eval x = true} = 4 := by
  calc
    _ = Fintype.card {x : Fin 3 ⊕ Fin 1 → Bool //
      x (.inl 2) = true ∧
      (∀ j v, v ∈ signedScopes j → ∀ w, w ∈ signedScopes j →
        x (.inl v) = signs j v → x (.inl w) = signs j w → v = w) ∧
      ∀ j, (∃ v ∈ signedScopes j, x (.inl v) = signs j v) →
        TwoBoundary.atomEval x (TwoBoundary.port 1 false j.castSucc) =
          TwoBoundary.atomEval x (TwoBoundary.port 1 false j.succ)} := by
        apply Fintype.card_congr
        apply Equiv.subtypeEquivRight
        intro x
        exact (TwoBoundary.query_eval _ _ _ _ _).trans (by
          simp only [CNF.eval_append, Bool.and_eq_true, exclusions_eval, coverage_eval,
            and_assoc]
          simp [side, CNF.eval, Clause.eval, Literal.eval])
    _ = 4 := by decide +kernel

example : Fintype.card {x : Fin 3 → Bool //
    side.eval x = true ∧ ∀ j, Holds (signedScopes j) (signs j) x} = 2 := by
  decide +kernel

/-- The signed equation really has coefficients `(1,-1,0)` and right-hand side zero. -/
example : coefficients (signedScopes 0) (signs 0) 0 = 1 ∧
    coefficients (signedScopes 0) (signs 0) 1 = -1 ∧
    coefficients (signedScopes 0) (signs 0) 2 = 0 ∧ rhs (signedScopes 0) (signs 0) = 0 := by
  decide +kernel

/-- Rank selection starts with the repeated original signed system, rather than
assuming any reduced system or counting query. The side constraint is arbitrary binary CNF. -/
public theorem rank_derived_queries :
    ∃ k : ℕ, ∃ Q : Bool → CNF (Fin 3 ⊕ Fin k),
      k + 1 < 3 ∧
      Fintype.card {x : Fin 3 → Bool //
        side.eval x = true ∧ ∀ j, Holds (signedScopes j) (signs j) x} =
        Fintype.card {x : Fin 3 ⊕ Fin k → Bool // (Q false).eval x = true} -
        Fintype.card {x : Fin 3 ⊕ Fin k → Bool // (Q true).eval x = true} ∧
      (∀ β c, c ∈ Q β → c.length ≤ 3) ∧
      (∀ β, (Q β).length ≤ 117) ∧ Fintype.card (Fin 3 ⊕ Fin k) ≤ 4 := by
  obtain ⟨k, Q, hk, _, hc, hw, hl, _, hv⟩ := exists_queries_of_two_rational_solutions
    side (by intro c hc; simp only [side, List.mem_cons, List.not_mem_nil, or_false] at hc
             rcases hc with rfl | rfl <;> decide)
    signedScopes signs (rationalPoint (fun _ => false)) (rationalPoint (fun _ => true))
    (by intro i; exact (equation_iff _ _ _).mpr (by fin_cases i <;> decide))
    (by intro i; exact (equation_iff _ _ _).mpr (by fin_cases i <;> decide))
    (by intro h; have := rationalPoint_injective h; have h0 := congrFun this 0; contradiction)
  exact ⟨k, Q, hk, hc, hw, hl, hv⟩

/-- Empty scopes force rejection, including when unused declared variables remain. -/
example : Fintype.card {x : Fin 3 → Bool //
    CNF.eval x ([] : CNF (Fin 3)) = true ∧
      ∀ _j : Fin 1, Holds (∅ : Finset (Fin 3)) (fun _ => true) x} = 0 := by
  apply count_eq_zero_of_empty_scope _ (fun _ : Fin 1 => ∅) _ 0 rfl

/-- Indexed equal candidate sets remain two alternative exact covers. An empty third
candidate is optional, giving four covers rather than identifying equal contents. -/
@[expose] public def candidates (v : Fin 3) : Finset (Fin 1) := if v = 2 then ∅ else {0}

example : Fintype.card {x : Fin 3 → Bool //
    ∀ i, Holds (coverScopes candidates i) (fun _ => true) x} = 4 := by
  decide +kernel

/-- A Boolean full-rank candidate is checked against the side clauses. -/
example : fullRankCount ([[(0, true)]] : CNF (Fin 1)) (fun _ => 1) = 1 ∧
    fullRankCount ([[(0, false)]] : CNF (Fin 1)) (fun _ => 1) = 0 := by
  decide +kernel

/-- A unique rational candidate need not be Boolean. -/
example : fullRankCount ([] : CNF (Fin 1)) (fun _ => 1 / 2) = 0 := by
  decide +kernel

/-- Zero declared variables retain the single empty assignment. -/
example : Fintype.card {x : Fin 0 → Bool //
    ∀ _j : Fin 0, Holds (∅ : Finset (Fin 0)) (fun _ => true) x} = 1 := by
  decide +kernel
