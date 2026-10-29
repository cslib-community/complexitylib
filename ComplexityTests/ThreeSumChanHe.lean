/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.ThreeSum.ChanHe.FromNumbers

/-!
# Nonvacuous clients of the core Chan–He reduction

These tests exercise collisions and failed candidates, light-element arrays and signed padding,
recursion, and the correctness theorem composed with the distinct-position frontend.
-/

namespace ComplexityTests.ThreeSumChanHe

open Cslib.Algorithms.ThreeSum Cslib.Algorithms.ThreeSum.ChanHe

-- Each unordered collision contributes both ordered pairs; negative residues are included.
example : coll {-3, 1, 2} 4 = 2 ∧ heavy {-3, 1, 2} 4 = {-3, 1} := by decide
example : light {-3, 1, 2} 4 = {2} := by decide
example : coll {-3, 1, 2} 0 = 0 ∧ heavy {-3, 1, 2} 0 = ∅ := by decide

-- The first candidate 2 fails: 2*7 > 3*1*2²; the next candidate 3 succeeds.
private def candidates : Finset ℕ := {2, 3, 5, 7, 11, 13, 17}
example : firstP candidates 1 {0, 2} {0, 2} {0, 2} = 3 := by decide
example : secondP candidates 1 {0, 2} {0, 2} {0, 2} 3 = 2 := by decide
example : modulus candidates 1 {0, 2} {0, 2} {0, 2} = 6 := by decide
example : firstP ∅ 1 {0} {0} {0} = 1 := by decide

-- A real instance of the simultaneous-prime theorem, with all hypotheses discharged.
example : ∀ S ∈ ([{-3, 1, 2}, {0}, {-2}] : List (Finset ℤ)),
    coll S (modulus candidates (labelBits 3) {-3, 1, 2} {0} {-2}) * candidates.card ^ 2 ≤
      9 * labelBits 3 ^ 2 * S.card ^ 2 := by
  exact (modulus_spec (by decide : candidates.Nonempty) (by decide)
    (by unfold Bdd; decide : Bdd 3 {-3, 1, 2}) (by unfold Bdd; decide : Bdd 3 {0})
    (by unfold Bdd; decide : Bdd 3 {-2})).2.2

-- -1 + 2 - 1 = 0. The sum of residues 4+2 wraps, so the third array needs its second copy.
example : arrXY {-1} 5 2 4 = -1 ∧ arrXY {2} 5 2 2 = 2 ∧
    arrZ {-1} 5 2 1 = 1 ∧ arrZ {-1} 5 2 6 = 1 ∧ arrZ {-1} 5 2 10 = -5 := by decide

example : HasConvolutionSolution 10 (arrXY {-1} 5 2) (arrXY {2} 5 2) (arrZ {-1} 5 2) :=
  ⟨4, 2, by decide, by decide⟩

-- A colliding set has no light representative at that residue; the padding is rejected.
example : arrXY {-3, 1} 4 3 1 = 7 ∧ arrZ {-3, 1} 4 3 3 = -7 := by decide
example : ¬HasConvolutionSolution 8 (arrXY {-3, 1} 4 3) (arrXY {0} 4 3)
    (arrZ {-1} 4 3) := by
  rw [node_correct (by decide : 1 ≤ 4) (by decide : 2 * 4 ≤ 8)
    (by unfold Bdd; decide : Bdd 3 {-3, 1}) (by unfold Bdd; decide : Bdd 3 {0})
    (by unfold Bdd; decide : Bdd 3 {-1})]
  unfold HasThreeSetSolution
  decide

example : (nodes candidates 1 0 {0} {0} {0}).length = 0 ∧
    nodes candidates 1 2 ∅ {0} {0} = [] := by decide

-- The replacement invariant is satisfiable and forces emptiness once the height is reached.
example : Replaced 2 3 0 {-3, 1} := .zero (by unfold Bdd; decide) (by decide)
example {T : Finset ℤ} (h : Replaced 2 3 (height 2) T) : T = ∅ := h.eq_empty le_rfl

private def yes : Fin 3 → ℤ := ![-2, 1, 1]
private def no : Fin 3 → ℤ := ![1, 1, 1]

example : ∃ y ∈ instances 3 2 yes, Convolution (8 * mPar 3 4 ^ 2) y :=
  (instances_correct 3 2 (by decide) yes (by decide)).mp (by unfold HasSolution yes; decide)

example : ¬∃ y ∈ instances 3 1 no, Convolution (8 * mPar 3 2 ^ 2) y := by
  rw [← instances_correct 3 1 (by decide) no (by decide)]
  unfold HasSolution no
  decide

example : ∃ y ∈ instances 3 0 (fun _ => 0), Convolution (8 * mPar 3 0 ^ 2) y :=
  (instances_correct 3 0 (by decide) (fun _ => 0) (by decide)).mp
    (by unfold HasSolution; decide)

example : ¬∃ y ∈ instances 2 0 (fun _ => 0), Convolution (8 * mPar 2 0 ^ 2) y := by
  rw [← instances_correct 2 0 (by decide) (fun _ => 0) (by decide)]
  unfold HasSolution
  decide

example : allNodes 0 0 (Fin.elim0 : Fin 0 → ℤ) = [] := by decide

example : (instances 3 2 yes).length ≤
    (2 * labelBits 4 ^ 2 + 2) * (2 * Nat.log 2 3 + 2) ^ 5 := length_instances_le ..

example {y : ℕ → ℤ} (hy : y ∈ instances 3 2 yes) (i : ℕ) : |y i| ≤ 280 := by
  exact abs_instances_le (by decide : 1 ≤ 3) (by decide : ∀ i, |yes i| ≤ (2 : ℤ)) hy i

end ComplexityTests.ThreeSumChanHe
