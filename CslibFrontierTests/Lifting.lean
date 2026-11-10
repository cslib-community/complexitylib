/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Communication.Lifting.Simulation

/-!
Regression clients for deterministic query-to-communication lifting: the greedy Janson bound,
the index gadget and its decision-tree simulation, density, and the lifting theorem, with a
parameter choice satisfying its hypotheses.
-/

open Cslib Cslib.Communication Cslib.Communication.Lifting Finset

namespace LiftingTests

/-! ### The greedy Janson bound -/

/-- A single set `{0}` is avoided by half of the subsets of `Fin 2`; the bound gives `3 / 4`. -/
example : (#((univ : Finset (Finset (Fin 2))).filter fun y => ∀ k < 1,
    ¬ (fun _ => ({0} : Finset (Fin 2))) k ⊆ y) : ℝ) ≤ 2 ^ 2 * (1 - (1 / 2) ^ 2) := by
  have := card_filter_forall_not_subset_le (fun _ => ({0} : Finset (Fin 2))) 1 (by
    intro k hk
    have : k = 0 := by omega
    subst this
    simp)
  simpa using this

/-! ### The index gadget -/

example : ind (n := 2) (m := 3) ![0, 2] ![![true, false, false], ![false, false, true]] =
    ![true, true] := by
  funext i; fin_cases i <;> rfl

/-- The protocol simulating the one-query tree outputs the queried bit of the lifted input. -/
example (x : Fin 1 → Fin 4) (y : Fin 1 → Fin 4 → Bool) :
    (ofDecisionTree (.node 0 (.leaf false) (.leaf true) : DecisionTree (Fin 1) Bool)).run x y =
      y 0 (x 0) := by
  simp only [run_ofDecisionTree, DecisionTree.eval_node, ind_apply]
  cases y 0 (x 0) <;> rfl

/-- Querying one bit costs `⌈log₂ 4⌉ + 1 = 3` bits. -/
example : Protocol.ecomplexity (lift (m := 4) fun (z : Fin 1 → Bool) o => o = z 0)
    Set.univ Set.univ ≤ 3 := by
  have h := ecomplexity_lift_le (m := 4) (R := fun (z : Fin 1 → Bool) o => o = z 0)
    (t := .node 0 (.leaf false) (.leaf true)) (fun z => by cases h : z 0 <;> simp [h])
  have hc : Nat.clog 2 4 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.clog_pow 2 2 (by norm_num)]
  simpa [hc] using h

/-! ### Density -/

/-- All pointer vectors are dense, so the density hypotheses are satisfiable. -/
example : IsDense (n := 3) (m := 8) 8 univ univ := isDense_univ (by norm_num) (by norm_num) _

/-! ### The lifting theorem -/

/-- The hypotheses of the lifting theorem hold for `n = 1`, `m = 2 ^ 30` and `τ = 2 ^ 15`. -/
theorem lifting_hypotheses :
    (4 : ℝ) ≤ 2 ^ 15 ∧ ((2 : ℝ) ^ 15) ^ 2 ≤ ((2 ^ 30 : ℕ) : ℝ) ∧
      320 * ((1 : ℕ) : ℝ) ^ 2 * (Nat.log 2 (2 ^ 30) + 1) ≤ 2 ^ 15 := by
  rw [Nat.log_pow (by norm_num)]
  norm_num

/-- The lifting theorem applied to the dictator search problem on one bit. -/
example {p : Protocol (Fin 1 → Fin (2 ^ 30)) (Fin 1 → Fin (2 ^ 30) → Bool) Bool}
    (hp : p.Solves (lift fun z o => o = z 0) Set.univ Set.univ) :
    ∃ t : DecisionTree (Fin 1) Bool, (∀ z, t.eval z = z 0) ∧
      (((2 ^ 30 : ℕ) : ℝ) / 2 ^ 15) ^ t.depth ≤ 4 ^ p.depth := by
  obtain ⟨h4, hm, hn⟩ := lifting_hypotheses
  obtain ⟨t, ht, hd⟩ := exists_decisionTree_of_solves h4 hm hn hp
  exact ⟨t, ht, hd⟩

end LiftingTests
