/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Distributed.OrientedCycle.MIS
import Complexity.Computability.Distributed.OrientedCycle.RoundComplexity

/-! Concrete Cole–Vishkin runs on a 5-cycle, the infinite path and the one-node cycle; shift
colourings; the flooding simulation; instances of Linial's lower bound; the bridge to Mathlib's
`cycleGraph`; and maximal independent sets. -/

namespace ComplexityTests.Distributed.OrientedCycle

open Cslib Cslib.Distributed.OrientedCycle

/-! ### The bit-index reduction step -/

-- `5 = 101₂` and `6 = 110₂` first differ at bit `0`, where `5` has a `1`: colour `2·0 + 1`.
example : lowestDiffBit 5 6 = 0 ∧ cvColor 5 6 = 1 := by decide
-- `4 = 100₂` and `6 = 110₂` first differ at bit `1`, where `4` has a `0`: colour `2·1 + 0`.
example : lowestDiffBit 4 6 = 1 ∧ cvColor 4 6 = 2 := by decide
-- Properness needs only `a ≠ b`: here `cvColor 4 6 = 2 ≠ 3 = cvColor 6 7`.
example : cvColor 4 6 ≠ cvColor 6 7 := cvColor_ne (by decide)

example : freeColor 0 1 = 2 ∧ freeColor 2 1 = 0 ∧ freeColor 0 0 = 1 := by decide
-- Only nodes of the removed colour move.
example : reduceColor 5 0 5 1 = 2 ∧ reduceColor 5 0 4 1 = 4 := by decide

-- One round from colours below `2 ^ 16` leaves colours below `32`; colours below `6` stay so.
example : cvBound 65536 = 32 ∧ cvBound 6 = 6 := by decide

/-! ### A run on the oriented 5-cycle -/

/-- Identifiers `3, 0, 4, 1, 2` on the nodes `0, …, 4` of the oriented 5-cycle. -/
def ids5 : ZMod 5 → ℕ := ![3, 0, 4, 1, 2]

-- `log* 5 = 3` reduction rounds, then removal of colours `5, 4, 3`: `6` rounds in all.
example : Nat.logStar 5 = 3 := by decide

-- After one round: `cvColor 3 0 = 1`, `cvColor 0 4 = 4`, `cvColor 4 1 = 0`, ….
example : (List.finRange 5).map (fun v => (threeColoring 3).run ids5 1 v) = [1, 4, 0, 1, 0] := by
  decide
-- Three reduction rounds leave colours below `6`; the removal rounds then recolour node `0`.
example : (List.finRange 5).map (fun v => (threeColoring 3).run ids5 3 v) = [4, 1, 0, 1, 0] := by
  decide
example : (List.finRange 5).map (fun v => (threeColoring 3).run ids5 6 v) = [2, 1, 0, 1, 0] := by
  decide
example : IsProperColoring ((threeColoring 3).run ids5 6) := by decide

-- The theorem applies to these identifiers, so its hypotheses are satisfiable.
example : IsProperColoring ((threeColoring (Nat.logStar 5)).run ids5 6) ∧
    ∀ v, (threeColoring (Nat.logStar 5)).run ids5 6 v < 3 :=
  threeColoring_run_of_injective (N := 5) (by decide) (by decide) (by decide) (by decide)

-- Two reduction steps per round: `fastThreeColoring 2` needs `2 + 3` rounds.
example : (List.finRange 5).map (fun v => (cvRule 2).apply ids5 v) = [1, 4, 0, 1, 0] := by
  decide
example : (List.finRange 5).map (fun v => (fastThreeColoring 2).run ids5 5 v) =
    [1, 2, 0, 1, 0] := by
  decide
example : (fastThreeColoring 2).ColorsCycle 5 5 3 :=
  fastThreeColoring_colorsCycle (by decide) (by decide) le_rfl

/-! ### Proper colourings -/

/-- Alternating colours on the oriented 5-cycle. -/
def alternating5 : ZMod 5 → ℕ := ![0, 1, 0, 1, 0]

-- A 2-colouring of an odd cycle is not proper.
example : ¬IsProperColoring alternating5 := by decide

-- On the one-node cycle the node is its own successor: no algorithm colours it properly.
example {S : Type} (A : Algorithm ℕ S ℕ) (t c : ℕ) : ¬A.ColorsCycle 1 t c := by
  intro hA
  have hinj : Function.Injective (fun _ : ZMod 1 => 0) := fun a b _ => Subsingleton.elim a b
  exact (hA _ hinj fun _ => Nat.one_pos).1 0 rfl

/-- Parity on the infinite oriented path `ZMod 0 = ℤ`. -/
def parity : ZMod 0 → ℕ := fun v : ℤ => (v % 2).toNat

-- Parity is a proper colouring of the infinite path with colours below `2`, and
-- `log* 2 + 3 = 4` Cole–Vishkin rounds turn it into a proper 3-colouring.
example : IsProperColoring ((threeColoring (Nat.logStar 2)).run parity 4) ∧
    ∀ v, (threeColoring (Nat.logStar 2)).run parity 4 v < 3 := by
  refine threeColoring_run ?_ ?_ (by decide)
  · change ∀ v : ℤ, (v % 2).toNat ≠ ((v + 1) % 2).toNat
    intro v
    omega
  · change ∀ v : ℤ, (v % 2).toNat < 2
    intro v
    omega

/-! ### The LOCAL model: views and messages -/

/-- The largest identifier among a node and its two neighbours, a rule of radius `1`. -/
def maxRule : LocalRule ℕ ℕ 1 where
  toFun w := max (w (-1)) (max (w 0) (w 1))
  dependsOn w w' h := by
    change max (w (-1)) (max (w 0) (w 1)) = max (w' (-1)) (max (w' 0) (w' 1))
    rw [h (-1) ⟨by decide, by decide⟩, h 0 ⟨by decide, by decide⟩, h 1 ⟨by decide, by decide⟩]

example : (List.finRange 5).map (fun v => maxRule.apply ids5 v) = [3, 4, 4, 4, 3] := by decide
-- The flooding algorithm computes the rule in one round.
example : (List.finRange 5).map (fun v => maxRule.toAlgorithm.run ids5 1 v) = [3, 4, 4, 4, 3] := by
  decide

/-- Each node sends its input to its successor and outputs what it receives. -/
def predecessorInput : MessageAlgorithm ℕ ℕ ℕ ℕ where
  init a := a
  toPred _ s := s
  toSucc _ s := s
  receive _ _ m₁ _ := m₁
  output s := s

example : (List.finRange 5).map (fun v => predecessorInput.state ids5 1 v) = [2, 3, 0, 4, 1] := by
  decide
example : (List.finRange 5).map (fun v => predecessorInput.toAlgorithm.run ids5 2 v) =
    [1, 2, 3, 0, 4] := by
  decide

/-! ### Shift colourings -/

-- A `1`-tuple coloured by its entry is a shift colouring with `m` colours.
example (m : ℕ) : IsShiftColoring m 0 (fun b : Fin 1 → ℕ => b 0) := fun a ha _ =>
  (ha (show (0 : Fin 2) < 1 by decide)).ne

-- A constant colouring is not a shift colouring once there are two values.
example : ¬IsShiftColoring 2 0 (fun _ : Fin 1 → ℕ => ()) := fun h =>
  h ![0, 1] (Fin.strictMono_iff_lt_succ.2 fun i => by fin_cases i; decide)
    (fun i => by fin_cases i <;> decide) rfl

-- Two colours cannot shift-colour the `1`-tuples from `{0, 1, 2}`.
example (f : (Fin 1 → ℕ) → Bool) : ¬IsShiftColoring 3 0 f := fun h => by
  have := h.card_le
  rw [Fintype.card_bool] at this
  omega

/-! ### Linial's lower bound -/

-- No algorithm 3-colours the oriented 5-cycle without communication (`log* 5 = 3 > 2`).
example {S : Type} (A : Algorithm ℕ S ℕ) : ¬A.ColorsCycle 5 0 3 := fun hA => by
  have h := hA.logStar_le_of_three
  rw [show Nat.logStar 5 = 3 by decide] at h
  omega

-- One round does not suffice on the oriented cycle of length `65537` (`log* 65537 = 5 > 4`).
example {S : Type} (A : Algorithm ℕ S ℕ) : ¬A.ColorsCycle 65537 1 3 := fun hA => by
  have h := hA.logStar_le_of_three
  rw [show Nat.logStar 65537 = 5 by decide] at h
  omega

-- Two rounds do not suffice on the cycle of length `2 ↑↑ 6 + 1`, which has `log* = 7 > 6`.
example {S : Type} (A : Algorithm ℕ S ℕ) : ¬A.ColorsCycle (Nat.twoTower 6 + 1) 2 3 := fun hA => by
  have h := hA.logStar_le_of_three
  rw [Nat.logStar_twoTower_add_one] at h
  omega

-- Identifiers from `{1, …, 5}`: no algorithm 3-colours the oriented 5-cycle without
-- communication either.
example {S : Type} (A : Algorithm ℕ S ℕ) :
    ¬∀ x : ZMod 5 → ℕ, Function.Injective x → (∀ v, 1 ≤ x v ∧ x v ≤ 5) →
      IsProperColoring (A.run x 0) ∧ ∀ v, A.run x 0 v < 3 := fun hA => by
  have h := ((A.colorsCycle_comapInput_succ_iff 5 0 3).2 hA).logStar_le_of_three
  rw [show Nat.logStar 5 = 3 by decide] at h
  omega

-- The `Θ(log* n)` summary for `n = 5`: `⌈3 / 2⌉ + 3 = 5` rounds suffice and are within `4`
-- rounds of optimal.
example : ∃ (S : Type) (A : Algorithm ℕ S ℕ), A.ColorsCycle 5 5 3 :=
  (exists_colorsCycle_three_and_logStar_le.{0} (n := 5) (by decide)).1


/-! ### The graph of the oriented cycle -/

-- The graph of the oriented 5-cycle is Mathlib's `cycleGraph 5`.
example : graph 5 = SimpleGraph.cycleGraph 5 := graph_succ_eq_cycleGraph 4

-- The Cole–Vishkin output on the 5-cycle as a Mathlib colouring with three colours.
example : ∃ C : (graph 5).Coloring (Fin 3), ∀ v, (C v : ℕ) = (fastThreeColoring 2).run ids5 5 v :=
  (fastThreeColoring_colorsCycle (n := 5) (s := 2) (by decide) (by decide) le_rfl).exists_coloring
    (by decide) (by decide) (by decide)

-- A proper colouring of `ZMod (k + 1)` transported to Mathlib's `cycleGraph (k + 1)`.
example (k : ℕ) (hk : k ≠ 0) {c : ZMod (k + 1) → ℕ} (hc : IsProperColoring c) :
    (SimpleGraph.cycleGraph (k + 1)).Coloring ℕ :=
  graph_succ_eq_cycleGraph k ▸ hc.toColoring (by omega)

/-! ### Maximal independent sets -/

/-- A proper 3-colouring of the 5-cycle. -/
def col5 : ZMod 5 → ℕ := ![1, 2, 1, 2, 0]

-- Greedy colour classes: after round `0` only the colour-`0` node has joined, which is not yet
-- maximal; after round `1` the set `{2, 4}` is maximal.
example : (List.finRange 5).map (fun v => misOfColoring.run col5 0 v) =
    [false, false, false, false, true] := by decide
example : ¬IsMIS (misOfColoring.run col5 0) := by decide
example : (List.finRange 5).map (fun v => misOfColoring.run col5 1 v) =
    [false, false, true, false, true] := by decide
example : IsMIS (misOfColoring.run col5 1) := by decide

-- One round from the MIS back to a proper 3-colouring.
example : (List.finRange 5).map (fun v => colorOfMIS.apply (misOfColoring.run col5 1) v) =
    [1, 2, 0, 1, 0] := by decide

-- The full MIS algorithm on the 5-cycle with identifiers `3, 0, 4, 1, 2` (`s = 2`, `2 + 5` rounds).
example : (List.finRange 5).map (fun v => (misAlgorithm 2).run ids5 7 v) =
    [false, false, true, false, true] := by decide
example : IsMIS ((misAlgorithm 2).run ids5 7) := by decide

-- The one-node cycle has no MIS in the sense of `IsMIS`: its node is its own neighbour.
example : ∀ s : ZMod 1 → Bool, ¬IsMIS s := by decide

-- `IsMIS` agrees with Mathlib's maximal independent sets on the 5-cycle.
example : Maximal (graph 5).IsIndepSet {v | misOfColoring.run col5 1 v = true} :=
  (isMIS_iff_maximal (by decide)).1 (by decide)

-- No MIS algorithm works without communication on the cycle of length `65537`.
example {S : Type} (A : Algorithm ℕ S Bool) : ¬A.FindsMIS 65537 0 := fun hA => by
  have h := hA.logStar_le
  rw [show Nat.logStar 65537 = 5 by decide] at h
  omega

-- The `Θ(log* n)` MIS summary for `n = 5`: `⌈3 / 2⌉ + 5 = 7` rounds suffice.
example : ∃ (S : Type) (A : Algorithm ℕ S Bool), A.FindsMIS 5 7 :=
  (exists_findsMIS_and_logStar_le.{0} (n := 5) (by decide)).1

end ComplexityTests.Distributed.OrientedCycle
