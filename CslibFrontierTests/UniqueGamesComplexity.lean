/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.PCP.Approximation.UniqueGames.Complexity
import Mathlib.Tactic.NormNum

/-!
# Polynomial-time membership for satisfiable unique games: tests

Kernel-checked checks (no `native_decide`) exercising
`CslibFrontier.Computability.PCP.Approximation.UniqueGames.Complexity`:

* `GapUniqueGames (Fin L) 1 s ∈ PromiseP` for `0 < L` (`gapUniqueGames_one_mem_PromiseP_of_pos`,
  `gapUniqueGames_one_mem_PromiseP`) and `isUniqueGame_mem_P`, `satisfiable_uniqueGame_mem_P`;
* the `L = 0` empty-alphabet separation (`gapUniqueGames_zero_yes`, `gapUniqueGames_zero_no`,
  `not_satisfiable_fin_zero`, `gapUniqueGames_zero_mem_PromiseP`);
* positive, negative, and non-unique `Fin L` instances showing `(solve (List.finRange L) ·).isSome`
  separates satisfiable unique games from unsatisfiable unique games (`GapUniqueGames (Fin 3) 1 s`)
  and rejects non-unique satisfiable tables.
-/

public section

namespace CslibFrontierTests.UniqueGamesComplexity

open Cslib.Complexity Cslib.Complexity.UniqueGames.Propagation Cslib.PCP Cslib.PCP.Encoded
open Turing.MultiTapeTM

/-- `GapUniqueGames (Fin 3) 1 s` is in `PromiseP` under the `UniqueGamesConjecture` encoding. -/
example (s : ℝ) :
    GapUniqueGames (Fin 3) 1 s ∈ PromiseP (Graph.encoding (encPi (encFinEnum (Fin 3)))) :=
  gapUniqueGames_one_mem_PromiseP_of_pos (by decide) s

/-- The unconditional theorem also covers `L = 0` and positive `L`. -/
example (L : ℕ) (s : ℝ) :
    GapUniqueGames (Fin L) 1 s ∈ PromiseP (Graph.encoding (encPi (encFinEnum (Fin L)))) :=
  gapUniqueGames_one_mem_PromiseP L s

/-- Exact unique-game recognition and satisfiability belong to `P`. -/
example (L : ℕ) :
    {g : Graph (Fin L → Fin L) | IsUniqueGame g} ∈
        P (Graph.encoding (encPi (encFinEnum (Fin L)))) ∧
      {g : Graph (Fin L → Fin L) | IsUniqueGame g ∧ (g.toGraph permutationEval).Satisfiable} ∈
        P (Graph.encoding (encPi (encFinEnum (Fin L)))) :=
  ⟨isUniqueGame_mem_P L, satisfiable_uniqueGame_mem_P L⟩

/-- Over `Fin 0`, an edgeless graph is vacuously a yes-instance of `GapUniqueGames (Fin 0) 1 s`,
no no-instances exist, yet the graph is not satisfiable. -/
example (s : ℝ) :
    let g : Graph (Fin 0 → Fin 0) := ⟨1, []⟩
    g ∈ (GapUniqueGames (Fin 0) 1 s).yes ∧
      (GapUniqueGames (Fin 0) 1 s).no = ∅ ∧
      ¬ (g.toGraph permutationEval).Satisfiable ∧
      GapUniqueGames (Fin 0) 1 s ∈ PromiseP (Graph.encoding (encPi (encFinEnum (Fin 0)))) := by
  refine ⟨?_, gapUniqueGames_zero_no s, not_satisfiable_fin_zero _,
    gapUniqueGames_zero_mem_PromiseP s⟩
  rw [gapUniqueGames_zero_yes]
  intro d hd
  cases hd

/-- Rotation by one on three labels. -/
def rot3 : Fin 3 → Fin 3 := fun a => a + 1

/-- The satisfiable 3-cycle of `rot3`. -/
def cyc3 : Graph (Fin 3 → Fin 3) :=
  ⟨3, [⟨0, 1, rot3⟩, ⟨1, 2, rot3⟩, ⟨2, 0, rot3⟩]⟩

/-- The unsatisfiable 3-cycle replacing the last rotation with `id`. -/
def cycBad3 : Graph (Fin 3 → Fin 3) :=
  ⟨3, [⟨0, 1, rot3⟩, ⟨1, 2, rot3⟩, ⟨2, 0, id⟩]⟩

/-- Every edge of `cyc3` carries a bijection. -/
theorem isUniqueGame_cyc3 : IsUniqueGame cyc3 := by
  simp only [IsUniqueGame, cyc3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  decide

/-- Every edge of `cycBad3` carries a bijection. -/
theorem isUniqueGame_cycBad3 : IsUniqueGame cycBad3 := by
  simp only [IsUniqueGame, cycBad3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  decide

/-- The polynomial-time decider `(solve (List.finRange 3) ·).isSome` accepts `cyc3`, which lies
in `(GapUniqueGames (Fin 3) 1 s).yes` and in the exact satisfiable unique-game set. -/
example (s : ℝ) :
    (solve (List.finRange 3) cyc3).isSome = true ∧
      cyc3 ∈ (GapUniqueGames (Fin 3) 1 s).yes ∧
      cyc3 ∈ {g : Graph (Fin 3 → Fin 3) |
        IsUniqueGame g ∧ (g.toGraph permutationEval).Satisfiable} := by
  have hsol : (solve (List.finRange 3) cyc3).isSome = true := by decide
  have hsat : (cyc3.toGraph permutationEval).Satisfiable :=
    (solve_isSome_iff (fun a => List.mem_finRange a) isUniqueGame_cyc3).1 hsol
  exact ⟨hsol, mem_yes_gapUniqueGames_one_iff.2 ⟨isUniqueGame_cyc3, hsat⟩,
    ⟨isUniqueGame_cyc3, hsat⟩⟩

/-- On the unsatisfiable 3-cycle `cycBad3`, `(solve (List.finRange 3) ·).isSome` returns `false`,
and `cycBad3` is a no-instance of `GapUniqueGames (Fin 3) 1 s` for `2 / 3 ≤ s < 1`. -/
example {s : ℝ} (hs : 2 / 3 ≤ s) (hs1 : s < 1) :
    (solve (List.finRange 3) cycBad3).isSome = false ∧
      cycBad3 ∈ (GapUniqueGames (Fin 3) 1 s).no ∧
      cycBad3 ∉ {g : Graph (Fin 3 → Fin 3) |
        IsUniqueGame g ∧ (g.toGraph permutationEval).Satisfiable} := by
  have hsol : (solve (List.finRange 3) cycBad3).isSome = false := by decide
  have hunsat : ¬ (cycBad3.toGraph permutationEval).Satisfiable := by
    rw [← solve_isSome_iff (fun a => List.mem_finRange a) isUniqueGame_cycBad3]
    simp [hsol]
  have hval : (cycBad3.toGraph permutationEval).unsatVal ≥ (1 : ℝ) / 3 := by
    have h := (cycBad3.toGraph permutationEval).inv_card_le_unsatVal hunsat
    change ((Fintype.card (Fin 3) : ℕ) : ℝ)⁻¹ ≤ _ at h
    rw [Fintype.card_fin] at h
    norm_num at h ⊢
    exact h
  refine ⟨hsol, ⟨⟨?_, hs1⟩, isUniqueGame_cycBad3⟩, fun ⟨_, hsat⟩ => hunsat hsat⟩
  linarith

/-- Satisfiable non-unique instance over `Fin 2` with constant edge constraints. -/
def const2 : Graph (Fin 2 → Fin 2) :=
  ⟨3, [⟨0, 1, fun _ => 0⟩, ⟨2, 1, fun _ => 0⟩, ⟨2, 2, fun _ => 1⟩]⟩

/-- `const2` is satisfiable, yet is neither a unique game nor accepted by `solve`. -/
example :
    (const2.toGraph permutationEval).Satisfiable ∧
      ¬ IsUniqueGame const2 ∧
      (solve (List.finRange 2) const2).isSome = false ∧
      const2 ∉ {g : Graph (Fin 2 → Fin 2) |
        IsUniqueGame g ∧ (g.toGraph permutationEval).Satisfiable} := by
  have hsat : (const2.toGraph permutationEval).Satisfiable :=
    ⟨fun v => if v = 2 then 1 else 0, (check_eq_true_iff _ _).1 (by decide)⟩
  have hnu : ¬ IsUniqueGame const2 := by
    intro h
    have hinj := (h ⟨0, 1, fun _ => 0⟩ (by simp [const2])).1
    have h01 : (0 : Fin 2) = 1 := hinj rfl
    contradiction
  exact ⟨hsat, hnu, by decide, fun ⟨h, _⟩ => hnu h⟩

end CslibFrontierTests.UniqueGamesComplexity
