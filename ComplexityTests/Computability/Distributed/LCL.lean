/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Distributed.OrientedCycle.LCL.Flexible
import Complexity.Computability.Distributed.OrientedCycle.MIS

/-! LCL problems on oriented cycles: 3-colouring and maximal independent sets (flexible, no loop,
`Θ(log* n)`), 2-colouring (no flexible state), a problem with a loop, the node-edge-checkable
bridge, and concrete anchors and fillings. -/

namespace ComplexityTests.Distributed.OrientedCycle.LCL

open Cslib Cslib.Distributed.OrientedCycle Cslib.Distributed.OrientedCycle.LCL

/-! ### 3-colouring -/

/-- Proper 3-colouring as an LCL problem. -/
abbrev threeCol : Fin 3 → Fin 3 → Prop := (· ≠ ·)

/-- A proper 3-colouring of the 5-cycle. -/
def good5 : ZMod 5 → Fin 3 := ![0, 1, 2, 0, 1]

/-- An improper 3-colouring of the 5-cycle: nodes `3` and `4` clash. -/
def bad5 : ZMod 5 → Fin 3 := ![0, 1, 2, 0, 0]

example : IsSolution threeCol good5 := by decide
example : ¬IsSolution threeCol bad5 := by decide
-- The one-node cycle is its own successor: no solution.
example : ∀ ℓ : ZMod 1 → Fin 3, ¬IsSolution threeCol ℓ := by decide

-- Closed walks `0 → 1 → 0` and `0 → 1 → 2 → 0` make state `0` flexible with flexibility `2`.
theorem threeCol_isFlexible : IsFlexible threeCol 0 2 :=
  IsFlexible.of_two_three ⟨fun i => if i = 1 then 1 else 0, rfl, rfl, by decide⟩
    ⟨fun i => if i = 1 then 1 else if i = 2 then 2 else 0, rfl, rfl, by decide⟩

-- Upper bound: for every `n ≥ 2`, `⌈log* n / 2⌉ + 9` rounds.
example {n : ℕ} (hn : 2 ≤ n) : ∃ A : Algorithm ℕ (ℤ → ℕ) (Fin 3),
    A.SolvesLCL threeCol n ((Nat.logStar n + 1) / 2 + 9) := by
  obtain ⟨A, hA⟩ := threeCol_isFlexible.exists_solvesLCL hn (s := (Nat.logStar n + 1) / 2)
    (by omega)
  exact ⟨A, by simpa using hA⟩

-- Lower bound: `log* n ≤ 2t + 2`, Linial's bound again.
example {S : Type} {A : Algorithm ℕ S (Fin 3)} {n t : ℕ} (hA : A.SolvesLCL threeCol n t) :
    Nat.logStar n ≤ 2 * t + 2 := by
  have h := hA.logStar_le (fun a h => h rfl)
  have h3 : Nat.logStar (Fintype.card (Fin 3)) = 2 := by decide
  omega

-- No 0-round algorithm 3-colours a 4-cycle.
example {S : Type} (A : Algorithm ℕ S (Fin 3)) : ¬A.SolvesLCL threeCol 4 0 := fun hA => by
  obtain ⟨a, ha⟩ := hA.exists_loop_of_zero (by decide)
  exact ha rfl

/-! ### Node-edge-checkable 3-colouring -/

-- Both ports of an edge carry the colour of its tail, and a node's two ports must differ: the
-- node-edge-checkable form of 3-colouring.
/-- The node-edge-checkable labelling induced by `good5`. -/
def goodPorts5 : ZMod 5 → Fin 3 × Fin 3 := ![(0, 0), (1, 1), (2, 2), (0, 0), (1, 1)]

/-- A labelling whose node `3` has two different port labels. -/
def badPorts5 : ZMod 5 → Fin 3 × Fin 3 := ![(0, 0), (1, 1), (2, 2), (0, 1), (1, 1)]

example : IsSolution (nodeEdge (· = ·) (· ≠ ·)) goodPorts5 := by decide
example : ¬IsSolution (nodeEdge (· = ·) (· ≠ ·)) badPorts5 := by decide

/-! ### Maximal independent sets -/

/-- MIS as an LCL problem: node `v` outputs `(s v, s (v + 1))`; consecutive outputs agree on the
shared bit, no two adjacent nodes are in the set, and a node outside it has a neighbour in it. -/
def misLCL (p p' : Bool × Bool) : Prop :=
  p.2 = p'.1 ∧ ¬(p.1 = true ∧ p.2 = true) ∧ (p'.1 = false → p.1 = true ∨ p'.2 = true)

instance : DecidableRel misLCL := fun _ _ => by unfold misLCL; infer_instance

theorem isSolution_misLCL_iff {n : ℕ} (s : ZMod n → Bool) :
    IsSolution misLCL (fun v => (s v, s (v + 1))) ↔ IsMIS s := by
  simp only [IsSolution, misLCL, IsMIS]
  constructor
  · intro h
    refine ⟨fun v hv => ?_, fun v => ?_⟩
    · have := (h v).2.1
      cases hs : s (v + 1) <;> simp_all
    · have := (h (v - 1)).2.2
      rw [sub_add_cancel] at this
      cases hs : s v <;> simp_all
  · intro h v
    refine ⟨trivial, fun hv => ?_, fun hv => ?_⟩
    · rw [h.1 v hv.1] at hv
      exact Bool.false_ne_true hv.2
    · have := h.2 (v + 1)
      rw [add_sub_cancel_right] at this
      rcases this with h1 | h1 | h1
      · rw [hv] at h1
        exact absurd h1 Bool.false_ne_true
      · exact Or.inl h1
      · exact Or.inr h1

-- MIS has no loop: `(true, true)` is not independent and `(false, false)` is not dominating.
theorem misLCL_irrefl : ∀ a, ¬misLCL a a := by decide

-- Closed walks of lengths `2` and `3` at `(true, false)`.
theorem misLCL_isFlexible : IsFlexible misLCL (true, false) 2 :=
  IsFlexible.of_two_three
    ⟨fun i => if i = 1 then (false, true) else (true, false), rfl, rfl, by decide⟩
    ⟨fun i => if i = 1 then (false, false) else if i = 2 then (false, true) else (true, false),
      rfl, rfl, by decide⟩

-- `Θ(log* n)` for MIS from the classification.
example {n : ℕ} (hn : 2 ≤ n) :=
  misLCL_isFlexible.exists_solvesLCL_and_logStar_le misLCL_irrefl hn

/-! ### 2-colouring is not flexible -/

/-- Proper 2-colouring as an LCL problem. -/
abbrev twoCol : Bool → Bool → Prop := (· ≠ ·)

theorem twoCol_walk {w : ℕ → Bool} {m : ℕ} (hw : ∀ i < m, twoCol (w i) (w (i + 1))) :
    ∀ i ≤ m, w i = (w 0 ^^ decide (i % 2 = 1)) := by
  intro i hi
  induction i with
  | zero => simp
  | succ i ih =>
    have h := hw i (by omega)
    rw [ih (by omega)] at h
    rcases Nat.mod_two_eq_zero_or_one i with h2 | h2 <;>
      cases hw0 : w 0 <;> cases hwi : w (i + 1) <;> simp_all <;> omega

theorem twoCol_not_isFlexible (q : Bool) (K : ℕ) : ¬IsFlexible twoCol q K := by
  intro h
  obtain ⟨w, h0, hm, hw⟩ := h (2 * K + 1) (by omega)
  have := twoCol_walk hw (2 * K + 1) le_rfl
  rw [hm, h0] at this
  cases q <;> simp at this

-- 2-colouring has no loop either, so it still needs `Ω(log* n)` rounds.
example {S : Type} {A : Algorithm ℕ S Bool} {n t : ℕ} (hA : A.SolvesLCL twoCol n t) :
    Nat.logStar n ≤ 2 * t + 1 := by
  have h := hA.logStar_le (fun a h => h rfl)
  have h2 : Nat.logStar (Fintype.card Bool) = 1 := by decide
  omega

/-! ### A problem with a loop -/

-- "All labels equal" has loops, so the constant algorithm solves it in `0` rounds.
example (n : ℕ) : (Algorithm.const true : Algorithm ℕ Unit Bool).SolvesLCL (· = ·) n 0 :=
  Algorithm.solvesLCL_const rfl n 0

/-! ### Anchors and filling -/

/-- A distance-1 colouring (a proper colouring) of the 6-cycle. -/
def col6 : ZMod 6 → ℕ := ![0, 2, 1, 3, 0, 1]

-- Anchors for `k = 1` are the strict local minima: nodes `0`, `2` and `4`.
example : (List.finRange 6).map (fun v => (anchorRule 1).apply col6 v) =
    [true, false, true, false, true, false] := by decide

-- Filling with walks `0 → 1 → ⋯ → 0` labelled by the position in the gap, then `0` at anchors.
example : (List.finRange 6).map
    (fun v => (fillRule (fun g d => if d = g then 0 else d) 1).apply
      ((anchorRule 1).apply col6) v) = [0, 1, 0, 1, 0, 1] := by decide

end ComplexityTests.Distributed.OrientedCycle.LCL
