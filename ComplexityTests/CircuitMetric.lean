/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Metric
import Cslib.Computability.Circuit.Full
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.FinCases

/-! Exact computational Hamming distances between projections, negations and constants on one
and two bits, the Lipschitz and ball statements on them, and a non-Boolean instance of the
generic hypotheses, the full binary basis over `ZMod 3`, where the difference distance is not
symmetric. -/

namespace ComplexityTests.CircuitMetric

open Cslib Cslib.Circuits

/-! ### One bit -/

namespace OneBit

open Boolean

/-- The input bit. -/
private abbrev x₀ : BooleanFunction 1 := fun x => x 0

/-- Its negation. -/
private abbrev nx₀ : BooleanFunction 1 := fun x => !x 0

private theorem x₀_ne_zero : x₀ ≠ 0 := fun h => absurd (congrFun h fun _ => true) (by decide)

private theorem nx₀_ne_zero : nx₀ ≠ 0 := fun h => absurd (congrFun h fun _ => false) (by decide)

private theorem x₀_ne_nx₀ : x₀ ≠ nx₀ := fun h => absurd (congrFun h fun _ => true) (by decide)

/-- The constant `true` needs exactly one gate. -/
private theorem complexity_single_true :
    complexity interpretation (single fun _ : BitString 1 => true) = 1 :=
  le_antisymm (Synthesis.const (s := inputs 1) true).complexity_le
    (one_le_complexity_single fun i h => by
      fin_cases i
      exact absurd (congrFun h fun _ => false) (by decide))

/-- The negated input needs exactly one gate. -/
private theorem complexity_single_nx₀ : complexity interpretation (single nx₀) = 1 :=
  le_antisymm ((complexity_not_le x₀).trans (by rw [complexity_single_proj]))
    (one_le_complexity_single fun i h => by
      fin_cases i
      exact absurd (congrFun h fun _ => true) (by decide))

/-- The input bit is at distance four from zero: the projection needs no gates. -/
theorem circuitDist_x₀_zero : circuitDist x₀ 0 = 4 := by
  rw [circuitDist_of_ne x₀_ne_zero, show (fun x : BitString 1 => x₀ x ^^ (0 : BooleanFunction 1) x)
    = x₀ from funext fun x => Bool.xor_false _, complexity_single_proj]

theorem circuitDist_nx₀_zero : circuitDist nx₀ 0 = 5 := by
  rw [circuitDist_of_ne nx₀_ne_zero,
    show (fun x : BitString 1 => nx₀ x ^^ (0 : BooleanFunction 1) x) = nx₀ from
      funext fun x => Bool.xor_false _,
    complexity_single_nx₀]

/-- A bit and its negation differ everywhere, by the constant `true`. -/
theorem circuitDist_x₀_nx₀ : circuitDist x₀ nx₀ = 5 := by
  rw [circuitDist_of_ne x₀_ne_nx₀, show (fun x : BitString 1 => x₀ x ^^ nx₀ x) = fun _ => true
    from funext fun x => by cases h : x 0 <;> simp [x₀, nx₀, h], complexity_single_true]

/-- Self-distance, distance between constants, symmetry, the Lipschitz bound on `x₀` and `nx₀`,
norm of `x₀`, and closed-ball membership around zero. -/
example :
    letI := circuitNormedAddCommGroup 1
    circuitDist x₀ x₀ = 0 ∧
    circuitDist (0 : BooleanFunction 1) 1 = 5 ∧
    circuitDist nx₀ x₀ = 5 ∧
    Nat.dist (complexity interpretation (single x₀)) (complexity interpretation (single nx₀)) ≤ 5 ∧
    circuitNorm 1 x₀ = 4 ∧
    x₀ ∈ Metric.closedBall 0 4 ∧
    nx₀ ∉ Metric.closedBall 0 4 := by
  have hx := (complexity_single_le_iff_mem_closedBall x₀_ne_zero 0).mp
    (complexity_single_proj (0 : Fin 1)).le
  have hnx := (complexity_single_le_iff_mem_closedBall nx₀_ne_zero 0).not.mp
    (by rw [complexity_single_nx₀]; omega)
  simp only [Nat.cast_zero, zero_add] at hx hnx
  exact ⟨circuitDist_self x₀,
    by
      rw [circuitDist_of_ne fun h => absurd (congrFun h fun _ => true) (by decide),
        show (fun x : BitString 1 => (0 : BooleanFunction 1) x ^^ (1 : BooleanFunction 1) x) =
          fun _ => true from rfl, complexity_single_true],
    by rw [circuitDist_comm, circuitDist_x₀_nx₀],
    circuitDist_x₀_nx₀ ▸ dist_complexity_single_le_circuitDist x₀ nx₀,
    by rw [circuitNorm_apply, circuitDist_x₀_zero]; norm_num,
    hx, hnx⟩

end OneBit

/-! ### Two bits -/

namespace TwoBits

open Boolean

/-- The first input bit. -/
private abbrev y₀ : BooleanFunction 2 := fun x => x 0

/-- The second input bit. -/
private abbrev y₁ : BooleanFunction 2 := fun x => x 1

/-- The two projections are at distance between five and eight. -/
theorem circuitDist_y₀_y₁ : 5 ≤ circuitDist y₀ y₁ ∧ circuitDist y₀ y₁ ≤ 8 := by
  have hne : y₀ ≠ y₁ := fun h => absurd (congrFun h ![true, false]) (by decide)
  rw [circuitDist_of_ne hne]
  have hupper := complexity_xor_le y₀ y₁
  rw [complexity_single_proj, complexity_single_proj] at hupper
  have hlower : 1 ≤ complexity interpretation (single fun x => y₀ x ^^ y₁ x) :=
    one_le_complexity_single fun i h => by
      fin_cases i
      · exact absurd (congrFun h ![false, true]) (by decide)
      · exact absurd (congrFun h ![true, false]) (by decide)
  omega

/-- Adding the same function to both projections, however complex it is, keeps them within
distance eight: the distance sees the shared part. -/
example (f : BooleanFunction 2) : circuitDist (f + y₀) (f + y₁) ≤ 8 := by
  rw [circuitDist_add_left]
  exact circuitDist_y₀_y₁.2

end TwoBits

/-! ### The full binary basis over `ZMod 3` -/

namespace Full

/-- The full binary basis over `ZMod 3`, which is complete. -/
private abbrev full3 : Interpretation (fullSignature 2 (ZMod 3)) (ZMod 3) := fullInterpretation

/-- Addition costs one gate. -/
private theorem full3_add : complexity full3 (single fun y : Fin 2 → ZMod 3 => y 0 + y 1) ≤ 1 :=
  (Synthesis.full_binary (Synthesis.of_mem (s := inputs 2) ⟨0, rfl⟩)
    (Synthesis.of_mem ⟨1, rfl⟩) (· + ·)).complexity_le

/-- Negation costs one gate. -/
private theorem full3_neg : complexity full3 (single fun y : Fin 1 → ZMod 3 => -y 0) ≤ 1 :=
  (Synthesis.full_gate (k := 2) (s := inputs 1) (by norm_num) (fun v : Fin 1 → ZMod 3 => -v 0)
    (fun _ x => x 0) fun _ => ⟨0, rfl⟩).complexity_le

/-- The input. -/
private abbrev z₀ : (Fin 1 → ZMod 3) → ZMod 3 := fun x => x 0

private theorem z₀_ne_zero : z₀ ≠ 0 := fun h => absurd (congrFun h fun _ => 1) (by decide)

/-- The input is at distance one from zero: the projection needs no gates. -/
theorem diffDist_z₀_zero : diffDist full3 1 z₀ 0 = 1 := by
  rw [diffDist_of_ne z₀_ne_zero, sub_zero, complexity_single_proj]

/-- Zero is at distance two from the input: its negation needs a gate. -/
theorem diffDist_zero_z₀ : diffDist full3 1 0 z₀ = 2 := by
  rw [diffDist_of_ne (Ne.symm z₀_ne_zero), zero_sub]
  have hle : complexity full3 (single (-z₀)) ≤ 1 := full3_neg
  have hge : 1 ≤ complexity full3 (single (-z₀)) :=
    one_le_complexity_single fun i h => by
      fin_cases i
      exact absurd (congrFun h fun _ => 1) (by decide)
  omega

/-- Completeness, translation-invariant quasi-metric laws with `c = 1`, and asymmetry of
`diffDist full3 1` on `z₀` and `0`. -/
example (f g h a : (Fin 1 → ZMod 3) → ZMod 3) :
    full3.IsComplete ∧
    diffDist full3 1 f h ≤ diffDist full3 1 f g + diffDist full3 1 g h ∧
    diffDist full3 1 g f ≤ diffDist full3 1 f g + 1 ∧
    diffDist full3 1 (f + a) (g + a) = diffDist full3 1 f g ∧
    diffDist full3 1 z₀ 0 ≠ diffDist full3 1 0 z₀ :=
  ⟨inferInstance,
    diffDist_triangle full3_add f g h,
    diffDist_comm_le full3_neg f g,
    diffDist_add_right f g a,
    by rw [diffDist_z₀_zero, diffDist_zero_z₀]; decide⟩

end Full

end ComplexityTests.CircuitMetric
