/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Problems.StatisticalDifference
import CslibFrontier.Probability.StatisticalDistance.ClosedForm
import CslibFrontier.Probability.StatisticalDistance.Event

/-! # Statistical Difference and polarization of circuit samplers

Checked instances: completion of selector bits to a parity, the XOR construction on two constant
circuits evaluated on concrete selector bits, the distance of the XOR construction on circuits,
a far instance (two different constant circuits, at distance `1`) in the yes-set and outside the
no-set of `SD^{2/3,1/3}`, a near instance (two equal circuits, at distance `0`) in the no-set, and
the Polarization Lemma on instances applied to both.
-/

namespace ComplexityTests.StatisticalDifference

open Cslib Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity
open Cslib.Probability.PMF

/-! ### Completion to a parity -/

example : parityComplete true (![true, true] : BitString 2) = ![true, true, true] := by
  decide

example : parityComplete false (![true, false] : BitString 2) = ![true, false, true] := by
  decide

example : parityComplete false (fun i : Fin 0 => i.elim0) = ![false] := by
  decide

/-! ### Constant circuits -/

/-- The circuit with no inputs and one output, the constant `b`. -/
def constCircuit (b : Bool) : Circuit signature 0 1 :=
  ⟨Program.empty.gate ⟨.const b, Fin.elim0⟩, fun _ => .gate (Fin.last 0)⟩

theorem eval_constCircuit (b : Bool) :
    (constCircuit b).eval interpretation = Function.const _ (fun _ => b) := by
  funext x i
  exact (Program.eval_gate_last _ _ interpretation x).trans rfl

theorem outputDist_constCircuit (b : Bool) :
    (constCircuit b).outputDist interpretation = PMF.pure (fun _ => b) := by
  rw [Circuit.outputDist, eval_constCircuit, PMF.map_const]

theorem dist_pure_const : dist (PMF.pure (fun _ : Fin 1 => false))
    (PMF.pure (fun _ : Fin 1 => true)) = 1 := by
  rw [dist_pure_left, PMF.pure_apply_of_ne]
  · simp
  · intro h
    simpa using congrFun h 0

/-! ### The XOR construction on circuits -/

theorem parityComplete_true_false :
    parityComplete true (![false] : BitString 1) = ![false, true] := by
  decide

theorem parityComplete_false_false :
    parityComplete false (![false] : BitString 1) = ![false, false] := by
  decide

-- Two coordinates, one selector bit `r = false`, parity `true`: the completed selector is
-- `[false, true]`, so the two output blocks are `C₀ = false` and `C₁ = true`, whatever the (empty)
-- data blocks.
example (d : Fin 2 → BitString 0) :
    BitString.block ((xorMixCircuit (constCircuit false) (constCircuit true) 1 true).eval
      interpretation (Fin.append ![false] (BitString.blocksEquiv.symm d))) =
      (![fun _ => false, fun _ => true] : Fin 2 → BitString 1) := by
  rw [eval_xorMixCircuit, eval_constCircuit, eval_constCircuit, parityComplete_true_false]
  funext i
  fin_cases i <;> rfl

-- The same with parity `false`: the completed selector is `[false, false]`.
example (d : Fin 2 → BitString 0) :
    BitString.block ((xorMixCircuit (constCircuit false) (constCircuit true) 1 false).eval
      interpretation (Fin.append ![false] (BitString.blocksEquiv.symm d))) =
      (![fun _ => false, fun _ => false] : Fin 2 → BitString 1) := by
  rw [eval_xorMixCircuit, eval_constCircuit, eval_constCircuit, parityComplete_false_false]
  funext i
  fin_cases i <;> rfl

/-- The XOR construction on two different constant circuits, with two coordinates, keeps them at
distance `1`. -/
example : dist ((xorMixCircuit (constCircuit false) (constCircuit true) 1 false).outputDist
      interpretation)
    ((xorMixCircuit (constCircuit false) (constCircuit true) 1 true).outputDist interpretation) =
      1 := by
  rw [outputDist_xorMixCircuit, outputDist_xorMixCircuit,
    dist_map_of_injective _ _ (Equiv.injective _), dist_xorMix _ _ (by norm_num),
    outputDist_constCircuit, outputDist_constCircuit, dist_pure_const, one_pow]

/-! ### Statistical Difference -/

/-- Two different constant circuits. -/
def far : SDInstance := ⟨0, 1, constCircuit false, constCircuit true⟩

/-- Two equal constant circuits. -/
def near : SDInstance := ⟨0, 1, constCircuit false, constCircuit false⟩

theorem far_distance : far.distance = 1 := by
  rw [SDInstance.distance, far, outputDist_constCircuit, outputDist_constCircuit]
  exact dist_pure_const

theorem near_distance : near.distance = 0 :=
  dist_self _

example : far ∈ (StatisticalDifference (2 / 3) (1 / 3)).yes := by
  rw [mem_yes_statisticalDifference, far_distance]
  norm_num

example : far ∉ (StatisticalDifference (2 / 3) (1 / 3)).no := by
  rw [mem_no_statisticalDifference (by norm_num), far_distance]
  norm_num

example : near ∈ (StatisticalDifference (2 / 3) (1 / 3)).no := by
  rw [mem_no_statisticalDifference (by norm_num), near_distance]
  norm_num

example : near ∉ (StatisticalDifference (2 / 3) (1 / 3)).yes := by
  rw [mem_yes_statisticalDifference, near_distance]
  norm_num

/-! ### Polarization of instances -/

/-- Polarizing the far instance with the parameters of `SDInstance.exists_polarize` gives distance
at least `1 - 2⁻⁽ᵏ⁺¹⁾`, and polarizing the near instance gives distance at most `2⁻⁽ᵏ⁺¹⁾`. -/
example : ∃ m b : ℕ, ∀ k : ℕ,
    1 - (1 / 2 : ℝ) ^ (k + 1) ≤
      (far.polarize (m * (Nat.log 2 (k + 1) + 1) - 1) (2 ^ (b * (Nat.log 2 (k + 1) + 1)))
        k).distance ∧
    (near.polarize (m * (Nat.log 2 (k + 1) + 1) - 1) (2 ^ (b * (Nat.log 2 (k + 1) + 1)))
        k).distance ≤ (1 / 2 : ℝ) ^ (k + 1) := by
  obtain ⟨m, b, -, -, -, h⟩ := SDInstance.exists_polarize (α := 2 / 3) (β := 1 / 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨m, b, fun k => ⟨(h far k).1 (by rw [far_distance]; norm_num),
    (h near k).2 (by rw [near_distance]; norm_num)⟩⟩

/-- With `k = 1`, polarization maps the far instance into the yes-set and the near instance into
the no-set of `SD^{3/4,1/4}`. -/
example : ∃ lam ell : ℕ,
    far.polarize lam ell 1 ∈ (StatisticalDifference (1 - (1 / 2) ^ 2) ((1 / 2) ^ 2)).yes ∧
    near.polarize lam ell 1 ∈ (StatisticalDifference (1 - (1 / 2) ^ 2) ((1 / 2) ^ 2)).no := by
  obtain ⟨m, b, -, -, -, h⟩ := StatisticalDifference.exists_mapsTo_polarize (α := 2 / 3)
    (β := 1 / 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨hyes, hno⟩ := h 1 one_ne_zero
  refine ⟨_, _, hyes ?_, hno ?_⟩
  · rw [mem_yes_statisticalDifference, far_distance]
    norm_num
  · rw [mem_no_statisticalDifference (by norm_num), near_distance]
    norm_num

end ComplexityTests.StatisticalDifference
