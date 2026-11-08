/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.PCP.Approximation.Hastad
import CslibFrontier.Computability.PCP.Approximation.MaxExactThreeSAT

/-!
# Tests: Håstad's 3-bit linear test and its soundness against Label Cover

Concrete evaluations and non-vacuity checks for exact 3-clauses (`Clause.IsExactThreeDistinct`,
`CNF.IsExactThreeDistinct`), the `7 / 8` random-assignment bound (`unsatVal_le_one_eighth`), the
Long Code and table folding (`longCode`, `foldTable`), mod-2 subset projection (`projectSet`),
and Håstad's 3-bit linear test on concrete Label Cover graphs, including genuine no-instances
with proved optimum value.
-/

namespace ComplexityTests.Hastad

open Cslib Cslib.BitString Cslib.Complexity Cslib.Logic.PL Cslib.PCP Cslib.PCP.Encoded Finset

/-! ### Exact 3-clauses and the `7 / 8` bound -/

/-- A concrete clause with three distinct variables satisfies `Clause.IsExactThreeDistinct`. -/
example : Clause.IsExactThreeDistinct ([(0, true), (1, false), (2, true)] : Clause ℕ) := by
  decide

/-- A clause with a repeated variable does not satisfy `Clause.IsExactThreeDistinct`. -/
example : ¬ Clause.IsExactThreeDistinct ([(0, true), (0, false), (2, true)] : Clause ℕ) := by
  decide

/-- The eight clauses on the distinct variables `0, 1, 2`, one for each sign pattern: every
assignment falsifies exactly one of them. -/
private def eightClauses : CNF ℕ :=
  [[(0, true), (1, true), (2, true)], [(0, true), (1, true), (2, false)],
    [(0, true), (1, false), (2, true)], [(0, true), (1, false), (2, false)],
    [(0, false), (1, true), (2, true)], [(0, false), (1, true), (2, false)],
    [(0, false), (1, false), (2, true)], [(0, false), (1, false), (2, false)]]

/-- `eightClauses` has three distinct variables per clause and `unsatVal = 1 / 8`, witnessing
tightness of `unsatVal_le_one_eighth`. -/
example : eightClauses.unsatVal = 1 / 8 := by
  have h3 : eightClauses.IsExactThreeDistinct := by decide
  refine le_antisymm h3.unsatVal_le_one_eighth ((CNF.le_unsatVal_iff _).2 fun σ => ?_)
  have hlen : eightClauses.length = 8 := rfl
  have hcount : eightClauses.countUnsat σ = 1 := by
    cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2 <;>
      simp [eightClauses, CNF.countUnsat, h0, h1, h2]
  rw [hcount, hlen]
  norm_num

/-! ### Long Code, folding, mod-2 projection, and multi-edge Label Cover -/

example : longCode (0 : Fin 2) (fun i => i == 0) = true := rfl

example : IsOdd (foldTable false (fun _ : Bool → Bool => false)) :=
  isOdd_foldTable false _

/-- Under the constant projection `fun _ : Bool => ()`, a two-element set `{false, true}` has even
fiber cardinality and therefore projects to `∅`. -/
example : projectSet (fun _ : Bool => ()) ({false, true} : Finset Bool) = ∅ := by
  decide

/-- A singleton `{false}` has odd fiber cardinality and therefore projects to `{()}`. -/
example : projectSet (fun _ : Bool => ()) ({false} : Finset Bool) = {()} := by
  decide

/-- A concrete 1-edge Label Cover instance on `Bool` with identity projection `id`. -/
private def oneEdgeGraph : Graph (Bool → Bool) :=
  ⟨1, [⟨0, 0, id⟩]⟩

/-- On `oneEdgeGraph`, the constant `false` labelling satisfies the single edge and yields Long Code
tables achieving linear acceptance `1 - δ`. -/
example (δ : ℝ) :
    (∀ w, IsOdd (longCode ((fun _ : ℕ => false) w))) ∧
      Hastad.graphLinearProb oneEdgeGraph δ
        (fun _ => longCode false) (fun _ => longCode false) = 1 - δ :=
  Hastad.graphLinearProb_longCode_of_satisfies (by decide : oneEdgeGraph.edges ≠ []) δ
    (fun d hd => by
      simp only [oneEdgeGraph, List.mem_singleton] at hd
      subst hd
      rfl)

/-- The soundness threshold `η` of `gapLabelCover_dichotomy` does not depend on the label
sets: one `η` serves instances over `Bool → Bool` and over `Fin 3 → Bool`. This checks the
quantifier order only: with two right labels a random labelling satisfies at least half of the
edges, so both no-instance sets are empty unless `η ≥ 1 / 2`. -/
example : ∃ η : ℝ, 0 < η ∧
    (∀ g : Graph (Bool → Bool), g.edges ≠ [] → g ∈ (GapLabelCover Bool Bool 1 η).no →
      ∀ B A, (∀ w, IsOdd (B w)) →
        Hastad.graphLinearProb g (1 / 4) B A ≤ 1 / 2 + 4 * (1 / 16)) ∧
    (∀ g : Graph (Fin 3 → Bool), g.edges ≠ [] → g ∈ (GapLabelCover (Fin 3) Bool 1 η).no →
      ∀ B A, (∀ w, IsOdd (B w)) →
        Hastad.graphLinearProb g (1 / 4) B A ≤ 1 / 2 + 4 * (1 / 16)) := by
  obtain ⟨η, hη, h⟩ := Hastad.gapLabelCover_dichotomy (ε := 1 / 16) (δ := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨η, hη, fun _ hg => (h hg).2, fun _ hg => (h hg).2⟩

/-! ### A genuine soundness no-instance

The parallel constant-projection construction comes from Samuel's supplied codebase review.
The analytic soundness theorem and its source credit remain in the imported Håstad module.
-/

/-- There are `n + 1` parallel edges and right labels. Edge `i` constantly projects to label `i`,
so every labelling satisfies exactly one edge, independently of its left label. -/
private def parallelGraph (n : ℕ) : Graph (Unit → Fin (n + 1)) :=
  ⟨1, List.ofFn fun i : Fin (n + 1) => ⟨0, 0, fun _ => i⟩⟩

private theorem parallelGraph_nonempty (n : ℕ) : (parallelGraph n).edges ≠ [] := by
  simp [parallelGraph]

private theorem parallelGraph_wellFormed (n : ℕ) : (parallelGraph n).WellFormed := by
  simp [Graph.WellFormed, parallelGraph]

/-- Every labelling attains the optimum: precisely the edge indexed by its right label is
satisfied. This proves the bound and its attainment rather than assuming a no-instance. -/
private theorem parallelGraph_unsatFrac (n : ℕ) (σ : ℕ → Unit × Fin (n + 1)) :
    ((parallelGraph n).toGraph projectionEval).unsatFrac σ = 1 - 1 / (n + 1 : ℝ) := by
  classical
  let a : Fin (parallelGraph n).edges.length :=
    ⟨(σ 0).2.val, by simpa only [parallelGraph, List.length_ofFn] using (σ 0).2.isLt⟩
  have hsat (i : Fin (parallelGraph n).edges.length) :
      ((parallelGraph n).toGraph projectionEval).Satisfies σ i ↔ i = a := by
    rw [satisfies_toGraph_projectionEval_iff]
    dsimp only [parallelGraph] at i a ⊢
    rw [List.get_ofFn]
    simp only [Fin.ext_iff]
    rfl
  have hu : ((parallelGraph n).toGraph projectionEval).unsatEdges σ = {a}ᶜ := by
    ext i
    simp only [ConstraintGraph.mem_unsatEdges, hsat, mem_compl, mem_singleton]
  rw [ConstraintGraph.unsatFrac, hu, card_compl, card_singleton]
  simp only [Fintype.card_fin, parallelGraph, List.length_ofFn, Nat.add_sub_cancel,
    Nat.cast_add, Nat.cast_one]
  field_simp
  ring

private theorem parallelGraph_unsatVal (n : ℕ) :
    ((parallelGraph n).toGraph projectionEval).unsatVal = 1 - 1 / (n + 1 : ℝ) := by
  apply le_antisymm
  · exact (((parallelGraph n).toGraph projectionEval).unsatVal_le
      (fun _ => ((), 0))).trans_eq (parallelGraph_unsatFrac n _)
  · exact (ConstraintGraph.le_unsatVal_iff _).2 fun σ =>
      (parallelGraph_unsatFrac n σ).ge

/-- The theorem's positive threshold admits an actual graph no-instance with nonempty edges,
and therefore bounds the concrete odd Long Code tables on that graph. This exercises retained
analytic soundness; it makes no SAT reduction or hardness claim. The threshold is chosen from
`gapLabelCover_dichotomy_lt_one` before the label sets. Its strict upper bound ensures
that the no-instance domain is not empty merely because the gap thresholds overlap. -/
theorem exists_soundness_noInstance : ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ n : ℕ,
    (parallelGraph n).edges ≠ [] ∧ (parallelGraph n).WellFormed ∧
    1 - ((parallelGraph n).toGraph projectionEval).unsatVal = 1 / (n + 1 : ℝ) ∧
    parallelGraph n ∈ (GapLabelCover Unit (Fin (n + 1)) 1 η).no ∧
    (∀ _w : ℕ, IsOdd (longCode (0 : Fin (n + 1)))) ∧
    Hastad.graphLinearProb (parallelGraph n) (1 / 4)
      (fun _ => longCode 0) (fun _ => longCode ()) ≤ 1 / 2 + 4 * (1 / 64) := by
  obtain ⟨η, hη, hη1, h⟩ := Hastad.gapLabelCover_dichotomy_lt_one
    (ε := 1 / 64) (δ := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hη
  have hval : 1 - ((parallelGraph n).toGraph projectionEval).unsatVal =
      1 / (n + 1 : ℝ) := by rw [parallelGraph_unsatVal]; ring
  have hno : parallelGraph n ∈ (GapLabelCover Unit (Fin (n + 1)) 1 η).no := by
    simp only [GapLabelCover, PromiseProblem.mem_no_gapMax]
    exact ⟨by rw [hval]; exact hn.le, hη1⟩
  have hB : ∀ w : ℕ, IsOdd (longCode (0 : Fin (n + 1))) := fun _ => isOdd_longCode _
  exact ⟨η, hη, hη1, n, parallelGraph_nonempty n, parallelGraph_wellFormed n, hval, hno, hB,
    (h (parallelGraph_nonempty n)).2 hno _ _ hB⟩

end ComplexityTests.Hastad
