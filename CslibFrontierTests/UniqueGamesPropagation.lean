/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.PCP.Approximation.UniqueGames.PropagationTime

/-!
# Label propagation for unique games: worked examples

Kernel-checked runs (no `native_decide`) of `Cslib.Complexity.UniqueGames.Propagation.solve`:

* a satisfiable 3-cycle of rotations, the same cycle with its edges reversed (so that propagation
  inverts the bijections), and an unsatisfiable variant;
* the odd and even cycles of negations over two labels, i.e. 2-colouring a triangle and a square;
  the triangle is also a no-instance of `GapUniqueGames Bool 1 s` for `2/3 ≤ s < 1`;
* a disconnected instance, whose second component pins its seed's label by a loop;
* edges outside the declared vertex range, and the empty instance;
* a satisfiable instance with non-injective tables on which `solve` fails, showing that
  completeness needs injective tables;
* an exact charge of `solveM`, against the bound of `solveM_time_le`.
-/

public section

namespace CslibFrontierTests.UniqueGamesPropagation

open Cslib.Complexity Cslib.Complexity.UniqueGames.Propagation Cslib.PCP Cslib.PCP.Encoded

/-- Rotation by one on three labels. -/
def rot : Fin 3 → Fin 3 := fun a => a + 1

/-- Rotation by two on three labels, the inverse of `rot`. -/
def rot' : Fin 3 → Fin 3 := fun a => a + 2

/-! ### Cycles of rotations -/

/-- The 3-cycle `0 → 1 → 2 → 0` carrying `rot`: going around adds three, which is zero. -/
def cyc : Graph (Fin 3 → Fin 3) := ⟨3, [⟨0, 1, rot⟩, ⟨1, 2, rot⟩, ⟨2, 0, rot⟩]⟩

/-- Every edge of `cyc` carries a bijection. -/
theorem isUniqueGame_cyc : IsUniqueGame cyc := by
  simp only [IsUniqueGame, cyc, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  decide

example : (solve (List.finRange 3) cyc).map (fun σ => (List.range 3).map σ) = some [0, 1, 2] := by
  decide

example : (cyc.toGraph permutationEval).Satisfiable :=
  (solve_isSome_iff (fun a => List.mem_finRange a) isUniqueGame_cyc).1 (by decide)

/-- A yes-instance of `GapUniqueGames (Fin 3) 1 s`, for every `s`. -/
example (s : ℝ) : cyc ∈ (GapUniqueGames (Fin 3) 1 s).yes :=
  mem_yes_gapUniqueGames_one_iff.2 ⟨isUniqueGame_cyc,
    (solve_isSome_iff (fun a => List.mem_finRange a) isUniqueGame_cyc).1 (by decide)⟩

/-- The same cycle traversed backwards, `1 → 0`, `2 → 1`, `0 → 2`, carrying `rot'`: propagation
from the seed `1` runs against the edge directions and inverts `rot'`. -/
def cycRev : Graph (Fin 3 → Fin 3) := ⟨3, [⟨1, 0, rot'⟩, ⟨2, 1, rot'⟩, ⟨0, 2, rot'⟩]⟩

example : (solve (List.finRange 3) cycRev).map (fun σ => (List.range 3).map σ) =
    some [2, 0, 1] := by
  decide

/-- The 3-cycle with its last rotation replaced by the identity: going around adds two. -/
def cycBad : Graph (Fin 3 → Fin 3) := ⟨3, [⟨0, 1, rot⟩, ⟨1, 2, rot⟩, ⟨2, 0, id⟩]⟩

example : ¬ (cycBad.toGraph permutationEval).Satisfiable := by
  rw [← solve_isSome_iff (fun a => List.mem_finRange a)
    (by simp only [IsUniqueGame, cycBad, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]; decide)]
  decide

/-! ### Cycles of negations: 2-colouring -/

/-- The triangle with negation on every edge: a 2-colouring of an odd cycle. -/
def oddFlip : Graph (Bool → Bool) := ⟨3, [⟨0, 1, not⟩, ⟨1, 2, not⟩, ⟨2, 0, not⟩]⟩

/-- Every edge of `oddFlip` carries a bijection. -/
theorem isUniqueGame_oddFlip : IsUniqueGame oddFlip := by
  simp only [IsUniqueGame, oddFlip, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, and_self]
  exact ⟨fun a b h => by simpa using h, fun b => ⟨!b, by simp⟩⟩

example : (solve [false, true] oddFlip).isSome = false := by decide

/-- The odd triangle of negations has no 2-colouring, as `solve` finds. -/
theorem not_satisfiable_oddFlip : ¬ (oddFlip.toGraph permutationEval).Satisfiable := by
  rw [← solve_isSome_iff (labels := [false, true]) (by decide) isUniqueGame_oddFlip]
  decide

/-- The odd triangle is a no-instance of `GapUniqueGames Bool 1 s` for `2/3 ≤ s < 1`: every
labelling violates at least one of its three edges. -/
example {s : ℝ} (hs : 2 / 3 ≤ s) (hs1 : s < 1) : oddFlip ∈ (GapUniqueGames Bool 1 s).no := by
  refine ⟨⟨?_, hs1⟩, isUniqueGame_oddFlip⟩
  have h := (oddFlip.toGraph permutationEval).inv_card_le_unsatVal not_satisfiable_oddFlip
  change ((Fintype.card (Fin 3) : ℕ) : ℝ)⁻¹ ≤ _ at h
  rw [Fintype.card_fin] at h
  norm_num at h
  linarith

/-- The square with negation on every edge: a 2-colouring of an even cycle. -/
def evenFlip : Graph (Bool → Bool) :=
  ⟨4, [⟨0, 1, not⟩, ⟨1, 2, not⟩, ⟨2, 3, not⟩, ⟨3, 0, not⟩]⟩

example : (solve [false, true] evenFlip).map (fun σ => (List.range 4).map σ) =
    some [false, true, false, true] := by
  decide

/-! ### A disconnected instance -/

/-- The swap of `0` and `1`, fixing `2`. -/
def swap01 : Fin 3 → Fin 3 := fun a => if a = 0 then 1 else if a = 1 then 0 else a

/-- Two components: the cycle `cyc` on `0, 1, 2`, and on `3, 4` the edges `4 → 3` carrying `rot`
and the loop `4 → 4` carrying `swap01`, whose only fixed point `2` pins the label of `4`. The
vertex `5` lies on no edge. -/
def disc : Graph (Fin 3 → Fin 3) :=
  ⟨6, [⟨0, 1, rot⟩, ⟨1, 2, rot⟩, ⟨2, 0, rot⟩, ⟨4, 3, rot⟩, ⟨4, 4, swap01⟩]⟩

example : (solve (List.finRange 3) disc).map (fun σ => (List.range 6).map σ) =
    some [0, 1, 2, 0, 2, 0] := by
  decide

/-! ### Degenerate instances -/

/-- Edges outside the declared vertex range are still handled: `slots` covers every endpoint. -/
example : (solve [false, true] (⟨0, [⟨0, 1, not⟩]⟩ : Graph (Bool → Bool))).map
    (fun σ => (List.range 2).map σ) = some [false, true] := by
  decide

example : slots (⟨0, [⟨0, 1, not⟩]⟩ : Graph (Bool → Bool)) = 2 := by decide

/-- The empty instance is satisfiable. -/
example : (solve [false, true] (⟨0, []⟩ : Graph (Bool → Bool))).isSome = true := by decide

/-! ### Completeness needs injective tables -/

/-- The edges `0 → 1` and `2 → 1` carry the constant `0` and the loop `2 → 2` the constant `1`.
The labelling `0, 0, 1` satisfies it, but propagation reaches `2` from `1` and inverts the
constant `0` there to the label `0`, which the loop refutes. -/
def constTables : Graph (Fin 2 → Fin 2) :=
  ⟨3, [⟨0, 1, fun _ => 0⟩, ⟨2, 1, fun _ => 0⟩, ⟨2, 2, fun _ => 1⟩]⟩

example : (constTables.toGraph permutationEval).Satisfiable :=
  ⟨fun v => if v = 2 then 1 else 0, (check_eq_true_iff _ _).1 (by decide)⟩

example : (solve (List.finRange 2) constTables).isSome = false := by decide

/-! ### Charged steps -/

/-- The exact charge of `solveM` on the cycle: `4` for the slots, `9` for the incidence lists,
`3` to allocate the table, `102` for the outer loop (one component of three pops, each visiting
two edges), `3` to extract the labelling and `9` for the check. -/
example : (solveM (List.finRange 3) cyc).time = 130 := by decide

/-- The general bound on the cycle: `(3 + 5) · 3 + (9 · 3 + 16) · 3 + 1 = 154`. -/
example : (solveM (List.finRange 3) cyc).time ≤ 154 :=
  solveM_time_le (List.finRange 3) cyc

end CslibFrontierTests.UniqueGamesPropagation
