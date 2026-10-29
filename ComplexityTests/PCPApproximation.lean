/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.Approximation.LabelCover
import Complexity.Computability.PCP.Approximation.MaxThreeSAT

/-!
# Tests: gap problems and hardness of approximation

Gap problems on concrete objectives, including instance-dependent thresholds and instances outside
the promise; the agreement of promise reductions and NP-hardness with the decision notions; yes- and
no-instances of the headline gap problems for MAX-2CSP, MAX-3SAT and Unique Games, so that their
NP-hardness statements are not vacuous; the translation of a small constraint graph into a formula;
and Label Cover satisfiability.
-/

namespace ComplexityTests.PCPApproximation

open Cslib Cslib.Complexity Cslib.Logic.PL Cslib.PCP Cslib.PCP.Encoded Turing.MultiTapeTM

/-! ### Gap problems -/

/-- The gap problem of the identity objective on natural numbers, between `3` and `1`. -/
private noncomputable def gapNat : PromiseProblem ℕ :=
  PromiseProblem.gapMax (fun n => (n : ℝ)) (fun _ => 3) (fun _ => 1)

example : (5 : ℕ) ∈ gapNat.yes := by norm_num [gapNat]

example : (0 : ℕ) ∈ gapNat.no := by norm_num [gapNat]

/-- `2` is in neither set: it is outside the promise. -/
example : (2 : ℕ) ∉ gapNat.yes ∧ (2 : ℕ) ∉ gapNat.no := by norm_num [gapNat]

/-- With instance-dependent thresholds `c n = n` and `s n = n / 2`, an instance with `c n ≤ s n` is
never a no-instance. -/
example : (0 : ℕ) ∉ (PromiseProblem.gapMax (fun _ => (0 : ℝ)) (fun n : ℕ => (n : ℝ))
    (fun n : ℕ => (n : ℝ) / 2)).no := by
  norm_num

/-- On decision problems, promise reductions are polynomial-time reductions. -/
example {A : Set (List Bool)} :
    PromiseProblem.PolyTimeReducible encBits encBits (.ofSet A) (.ofSet A) :=
  PromiseProblem.polyTimeReducible_ofSet_iff.2 (PolyTimeReducible.refl encBits A)

/-- `SAT` is NP-hard as a promise problem. -/
example : PromiseProblem.NPHard encCNF (.ofSet SAT) :=
  PromiseProblem.npHard_ofSet_iff.2 CookLevin.SAT_npHard

/-- Restricting a promise problem intersects both sets. -/
example : (gapNat.restrict {n | n ≠ 5}).yes = {n : ℕ | (3 : ℝ) ≤ n} ∩ {n | n ≠ 5} := rfl

/-! ### MAX-2CSP -/

/-- The labels of the hardness theorem: one bit and six more. -/
private abbrev Label := Bool × (Fin 6 → Bool)

/-- A constraint graph with one loop forbidding every pair of labels. -/
private def unsatGraph : Graph (Label → Label → Bool) := ⟨1, [⟨0, 0, fun _ _ => false⟩]⟩

/-- Every labelling violates the only edge of `unsatGraph`. -/
private theorem one_le_unsatVal_unsatGraph : 1 ≤ (unsatGraph.toGraph id).unsatVal := by
  have h := (unsatGraph.toGraph id).inv_card_le_unsatVal fun ⟨σ, hσ⟩ => by
    simpa [ConstraintGraph.Satisfies, Graph.toGraph, unsatGraph] using hσ ⟨0, by decide⟩
  simpa [unsatGraph] using h

/-- The gap problem of the hardness theorem has a no-instance. -/
example : unsatGraph ∈ (GapTwoCSP Label (1 - 1 / 2 ^ 61)).no := by
  rw [mem_no_GapTwoCSP (by norm_num)]
  linarith [one_le_unsatVal_unsatGraph]

/-- The graph without edges is a yes-instance. -/
example : (⟨3, []⟩ : Graph (Label → Label → Bool)) ∈ (GapTwoCSP Label (1 - 1 / 2 ^ 61)).yes :=
  mem_yes_GapTwoCSP.2 ⟨fun _ => default, fun i => i.elim0⟩

/-- A loop whose constraint is equality is satisfiable. -/
example : (⟨1, [⟨0, 0, fun a b => decide (a = b)⟩]⟩ : Graph (Label → Label → Bool)) ∈
    (GapTwoCSP Label (1 - 1 / 2 ^ 61)).yes :=
  mem_yes_GapTwoCSP.2 ⟨fun _ => default, fun i => by
    simp [ConstraintGraph.Satisfies, Graph.toGraph]⟩

/-! ### Constraint graphs as formulas -/

/-- One-bit labels. -/
private def bit : Bool ≃ (Fin 1 → Bool) := (Equiv.funUnique (Fin 1) Bool).symm

/-- Every pair of one-bit labels. -/
private def bitPairs : List (Bool × Bool) :=
  [(false, false), (false, true), (true, false), (true, true)]

/-- An edge from `0` to `1` whose constraint is inequality. -/
private def neGraph : Graph (Bool → Bool → Bool) := ⟨2, [⟨0, 1, fun a b => a != b⟩]⟩

/-- Inequality forbids two pairs, each excluded by a clause of width two. -/
example : Graph.toCNF bit bitPairs neGraph =
    [[(Nat.pair 0 0, true), (Nat.pair 1 0, true)],
      [(Nat.pair 0 0, false), (Nat.pair 1 0, false)]] := by
  decide

example : (Graph.toCNF bit bitPairs neGraph).Satisfiable :=
  Graph.satisfiable_toCNF bit bitPairs ⟨fun v => decide (v = 0), fun i => by
    fin_cases i
    simp [ConstraintGraph.Satisfies, Graph.toGraph, neGraph]⟩

/-! ### MAX-3SAT -/

/-- `x₀ ∧ ¬x₀`: every assignment falsifies one of the two clauses. -/
private def contradiction : CNF ℕ := [[(0, true)], [(0, false)]]

private theorem unsatVal_contradiction : contradiction.unsatVal = 1 / 2 := by
  have h1 : contradiction.countUnsat (fun _ => true) = 1 := by decide
  refine le_antisymm ((contradiction.unsatVal_le fun _ => true).trans_eq ?_) ?_
  · rw [h1]
    norm_num [contradiction]
  refine contradiction.le_unsatVal_iff.2 fun σ => ?_
  cases h : σ 0 <;> simp [contradiction, CNF.countUnsat, h]

/-- The gap problem of the hardness theorem has a no-instance. -/
example : contradiction ∈ (GapThreeSAT (1 - 1 / (3 * 2 ^ 77))).no := by
  refine (mem_no_GapThreeSAT (by norm_num)).2 ⟨by decide, ?_⟩
  rw [unsatVal_contradiction]
  norm_num

/-- Its yes-instances are the satisfiable 3CNF formulas. -/
example : ([[(0, true), (1, false), (2, true)]] : CNF ℕ) ∈
    (GapThreeSAT (1 - 1 / (3 * 2 ^ 77))).yes := by
  rw [yes_GapThreeSAT]
  exact ⟨by decide, fun _ => true, rfl⟩

/-- A satisfiable formula with a wide clause is outside the promise. -/
example : ([[(0, true), (1, true), (2, true), (3, true)]] : CNF ℕ) ∉
    (GapThreeSAT (1 - 1 / (3 * 2 ^ 77))).yes := by
  rw [yes_GapThreeSAT]
  exact fun h => absurd (h.1 _ List.mem_cons_self) (by decide)

/-! ### Label Cover and Unique Games -/

/-- An edge projecting a pair of bits to its first bit. -/
example : ((⟨2, [⟨0, 1, fun p : Bool × Bool => p.1⟩]⟩ : Graph (Bool × Bool → Bool)).toGraph
    projectionEval).Satisfiable :=
  (satisfiable_toGraph_projectionEval_iff _).2 ⟨fun _ => (true, false), fun _ => true, by simp⟩

/-- A loop carrying negation: every labelling violates it. -/
private def negationLoop : Graph (Bool → Bool) := ⟨1, [⟨0, 0, not⟩]⟩

private theorem isUniqueGame_negationLoop : IsUniqueGame negationLoop := by
  simp only [IsUniqueGame, negationLoop, List.mem_singleton, forall_eq]
  exact ⟨fun a b h => by simpa using h, fun b => ⟨!b, by simp⟩⟩

private theorem one_le_unsatVal_negationLoop :
    1 ≤ (negationLoop.toGraph permutationEval).unsatVal := by
  have h := (negationLoop.toGraph permutationEval).inv_card_le_unsatVal fun ⟨σ, hσ⟩ => by
    have := hσ ⟨0, by decide⟩
    cases hσ0 : σ 0 <;>
      simp [ConstraintGraph.Satisfies, Graph.toGraph, negationLoop, permutationEval, hσ0] at this
  simpa [negationLoop] using h

/-- Unique Games has no-instances for every gap with `0 ≤ δ < 1 - ε`. -/
example {ε δ : ℝ} (hδ : 0 ≤ δ) (hεδ : δ < 1 - ε) :
    negationLoop ∈ (GapUniqueGames Bool (1 - ε) δ).no :=
  ⟨⟨by linarith [one_le_unsatVal_negationLoop], hεδ⟩, isUniqueGame_negationLoop⟩

/-- A loop carrying the identity is a yes-instance for every completeness at most one. -/
example {c s : ℝ} (hc : c ≤ 1) :
    (⟨1, [⟨0, 0, id⟩]⟩ : Graph (Bool → Bool)) ∈ (GapUniqueGames Bool c s).yes := by
  refine ⟨?_, by simp [IsUniqueGame]⟩
  have : ((⟨1, [⟨0, 0, id⟩]⟩ : Graph (Bool → Bool)).toGraph permutationEval).unsatVal = 0 :=
    (ConstraintGraph.unsatVal_eq_zero_iff _).2 ⟨fun _ => true, fun i => by
      simp [ConstraintGraph.Satisfies, Graph.toGraph, permutationEval]⟩
  simp only [PromiseProblem.mem_yes_gapMax, this, sub_zero]
  exact hc

/-- The conjecture is a proposition; nothing assumes it. -/
example : UniqueGamesConjecture → ∃ L : ℕ, PromiseProblem.NPHard
    (Graph.encoding (encPi (encFinEnum (Fin L)))) (GapUniqueGames (Fin L) (1 / 2) (1 / 4)) :=
  fun h => (h (1 / 2) (1 / 4) (by norm_num) (by norm_num) (by norm_num)).imp fun _ hL => by
    norm_num at hL ⊢
    exact hL

end ComplexityTests.PCPApproximation
