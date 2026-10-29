/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Iteration.Active
import Complexity.Computability.Circuit.Boolean.Iteration.DepthSearch
import Complexity.Computability.Circuit.Boolean.Iteration.Eventual
import Complexity.Computability.Circuit.Boolean.Iteration.LongTime
import Complexity.Computability.Circuit.Boolean.Iteration.NavigationWord

/-!
# Cycle labels, depths, targets and eventual queries

Evaluate the word computations on concrete inputs: streaming remainders including a zero-bit
number, modular differences in both orders, minimum and first-position scans, the binary threshold
search, label words and their correction, and the time compression below and above `2 ^ n`.
Then instantiate every circuit theorem on small circuits: the bit flip, and a constant circuit
whose single halting state satisfies the absorption and termination hypotheses of the halting
theorems.
-/

namespace ComplexityTests.Iteration.Dynamics

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Iteration
open Cslib.FunctionalGraph

/-! ### Word computations -/

-- `13 = 1 + 4 + 8` modulo `5`, streamed from the most significant bit; a zero-bit number has
-- remainder zero; modular differences in both orders; minimum and first-position scans; binary
-- threshold search; label correction; and time compression below and above `2 ^ n`.
example (d : BitVec 3) :
    (streamRemainder (BitVec.ofNat 4 5) ![true, false, true, true]).toNat = 3 ∧
    streamRemainder d (fun i : Fin 0 => i.elim0) = 0 ∧
    (subMod (BitVec.ofNat 4 2) (BitVec.ofNat 4 7) (BitVec.ofNat 4 5)).toNat = 0 ∧
    (subMod (BitVec.ofNat 4 1) (BitVec.ofNat 4 3) (BitVec.ofNat 4 5)).toNat = 3 ∧
    scanMin ![3, 1, 2] 5 3 = 1 ∧
    scanMin ![3, 1, 2] 5 0 = 5 ∧
    firstIndex (w := 3) ![false, true, true] = BitVec.ofNat 3 1 ∧
    firstIndex (w := 3) ![false, false] = 0 ∧
    (∀ μ < 8, (if μ = 0 then 0 else searchBelow 3 μ 3 + 1) = μ) ∧
    labelPhase (correctLabel (labelBits ![true] (BitVec.ofNat 3 3) (BitVec.ofNat 3 1)) 5) =
      BitVec.ofNat 3 2 ∧
    compressedTime 2 (BitVec.ofNat 5 3) ![true, false, true, false] = BitVec.ofNat 5 5 ∧
    compressedTime 2 (BitVec.ofNat 5 3) ![false, false, true, true] = BitVec.ofNat 5 6 :=
  ⟨by decide, rfl, by decide, by decide, by decide, rfl, by decide, by decide,
   by decide, by decide, by decide, by decide⟩

/-! ### Circuits -/

/-- The one-bit negation circuit. -/
private def flip : Circuit signature 1 1 :=
  ⟨.gate .empty ⟨.not, fun _ => .input 0⟩, fun _ => .gate 0⟩

/-- The one-bit circuit with constant output `false`. -/
private def zero : Circuit signature 1 1 :=
  ⟨.gate .empty ⟨.const false, Fin.elim0⟩, fun _ => .gate 0⟩

private theorem eval_zero (x : BitString 1) : zero.eval interpretation x = fun _ => false := by
  funext i
  rfl

-- Canonical labels of the flip, its depths, and depths by binary search.
example : ∃ out : Circuit signature 1 (labelWidth 1),
    out.Computes interpretation (canonicalLabel (flip.eval interpretation)) ∧
      out.size ≤ 60000 * powerBudget 1 1 2 1 := by
  simpa [flip] using cycle_label_circuit flip 1 one_pos (by decide)

example : ∃ out : Circuit signature 1 (1 + 2),
    (∀ x, word (out.eval interpretation x) =
      BitVec.ofNat 3 (transientDepth (flip.eval interpretation) x)) ∧
      out.size ≤ 50000 * powerBudget 1 1 2 1 := by
  simpa [flip] using checkpoint_depth_circuit flip 1 one_pos (by decide)

example (c : Circuit signature 2 2) : ∃ out : Circuit signature 2 (2 + 2),
    (∀ x, word (out.eval interpretation x) =
      BitVec.ofNat 4 (transientDepth (c.eval interpretation) x)) ∧
      (out.size : ℝ) ≤ 600000 * (2 + 1 : ℝ) ^ 2 * optimizedBudget 2 c.size 4 := by
  simpa using depth_circuit_optimized c

-- Reaching the state `![true]` under the flip, with its first time.
example : ∃ out : Circuit signature 1 (1 + (1 + 2)),
    (∀ x, out.eval interpretation x 0 = true ↔
      ∃ t, (Circuit.id signature 1).eval interpretation ((flip.eval interpretation)^[t] x) 0 =
        true) ∧
    (∀ x, out.eval interpretation x 0 = true →
      let t := (word fun i : Fin (1 + 2) => out.eval interpretation x (Fin.natAdd 1 i)).toNat
      (Circuit.id signature 1).eval interpretation ((flip.eval interpretation)^[t] x) 0 = true ∧
        (∀ j < t, (Circuit.id signature 1).eval interpretation
          ((flip.eval interpretation)^[j] x) 0 ≠ true) ∧ t < 2 ^ 1) ∧
    out.size ≤ 90000 * powerBudget 1 (flip.size + (Circuit.id signature 1).size + 4 * 1) 2 1 +
      (Circuit.id signature 1).size :=
  first_target_time flip (Circuit.id signature 1) 1 one_pos (by decide)

-- The constant circuit fixes its only halting state, and every orbit halts.
example : ∃ out : Circuit signature 1 (1 + 2),
    (∀ x ∈ Set.univ, let t := (word (out.eval interpretation x)).toNat
      (zero.eval interpretation)^[t] x = (fun _ => false) ∧
        (∀ j < t, ¬(zero.eval interpretation)^[j] x = (fun _ => false)) ∧ t < 2 ^ 1) ∧
    (out.size : ℝ) ≤ 150000 * optimizedBudget 1 zero.size (2 ^ 1) :=
  halting_time zero (fun x => x = fun _ => false) Set.univ
    (fun x hx => by rw [eval_zero, hx]) fun x _ => ⟨1, by simp [eval_zero]⟩

example : ∃ out : Circuit signature 1 1,
    (∀ x ∈ (Set.univ : Set (BitString 1)), out.eval interpretation x = (fun _ => false) ∧
      ∃ t < 2 ^ 1, out.eval interpretation x = (zero.eval interpretation)^[t] x ∧
        ∀ j < t, ¬(zero.eval interpretation)^[j] x = (fun _ => false)) ∧
    out.size ≤ 40000 * powerBudget 1 zero.size (2 ^ 1) 1 :=
  halting_computation zero (fun x => x = fun _ => false) Set.univ
    (fun x hx => by rw [eval_zero, hx]) (fun x _ => ⟨1, by simp [eval_zero]⟩) 1 one_pos
    (by decide)

-- Two flipped bits never meet at equal times unless they start equal.
example : ∃ out : Circuit signature (1 + 1) 1,
    (∀ z, out.eval interpretation z 0 = true ↔
      ∃ t, (flip.eval interpretation)^[t] (fun i => z (Fin.castAdd 1 i)) =
        (flip.eval interpretation)^[t] (fun i => z (Fin.natAdd 1 i))) ∧
    out.size ≤ 80000 * powerBudget 1 flip.size (2 ^ 1) 1 + 6 * 1 + 1 :=
  synchronous_coalescence flip 1 one_pos (by decide)

-- Every flipped input returns to true arbitrarily late, so the recurring-target query is true.
example : ∃ out : Circuit signature 1 1,
    (∀ x, out.eval interpretation x 0 = true) ∧
    (out.size : ℝ) ≤
      240000 * optimizedBudget 1 (flip.size + (Circuit.id signature 1).size + 4 * 1) (2 ^ 1) +
        (Circuit.id signature 1).size := by
  obtain ⟨out, hcorrect, hsize⟩ := recurring_target_optimized flip (Circuit.id signature 1)
  refine ⟨out, ?_, hsize⟩
  intro x
  apply (hcorrect x).mpr
  intro a
  by_cases hx : ((flip.eval interpretation)^[a] x) 0 = true
  · exact ⟨a, le_rfl, hx⟩
  · refine ⟨a + 1, Nat.le_succ a, ?_⟩
    rw [Function.iterate_succ_apply']
    change !(((flip.eval interpretation)^[a] x) 0) = true
    cases hb : ((flip.eval interpretation)^[a] x) 0 <;> simp_all

-- After one step zero stays false, so no input is eventually always in the true target.
example : ∃ out : Circuit signature 1 1,
    (∀ x, out.eval interpretation x 0 = false) ∧
    (out.size : ℝ) ≤
      240000 *
        optimizedBudget 1 (zero.size + ((Circuit.id signature 1).size + 1) + 4 * 1) (2 ^ 1) +
        (Circuit.id signature 1).size + 2 := by
  obtain ⟨out, hcorrect, hsize⟩ := eventually_always_target_optimized zero (Circuit.id signature 1)
  refine ⟨out, ?_, hsize⟩
  intro x
  have hnot : ¬ out.eval interpretation x 0 = true := by
    intro hx
    obtain ⟨a, ha⟩ := (hcorrect x).mp hx
    have hbad := ha (a + 1) (Nat.le_succ a)
    rw [Function.iterate_succ_apply'] at hbad
    change false = true at hbad
    cases hbad
  simpa only [Bool.not_eq_true] using hnot

-- Long input times on the flip, for a time much wider than the state.
example : ∃ out : Circuit signature (1 + 10) 1,
    out.Computes interpretation (inputTimeIterate (flip.eval interpretation) 10) ∧
      out.size ≤ 200000 * (1 + 1) * powerBudget 1 1 2 1 + 80 * 10 * (1 + 1) := by
  simpa [flip] using variable_time_additive flip 10 1 one_pos (by decide)

-- And for a time narrower than the state.
example (c : Circuit signature 3 3) : ∃ out : Circuit signature (3 + 1) 3,
    out.Computes interpretation (inputTimeIterate (c.eval interpretation) 1) ∧
      (out.size : ℝ) ≤ 600000 * (3 + 1) * optimizedBudget 3 c.size (2 ^ 3) + 80 * 1 * (3 + 1) := by
  simpa using variable_time_additive_optimized c 1

-- Fixed powers charged to the active states.
example (T : ℕ) : ∃ out : Circuit signature 1 1,
    out.Computes interpretation (flip.eval interpretation)^[T] ∧
      out.size ≤ 120000 * powerBudget 1 flip.size
        (activeVertices (flip.eval interpretation) 1).card 1 :=
  active_mass_fixed_power 1 flip T 1 one_pos (by decide)

-- Remainders of a three-bit number modulo a two-bit modulus.
example : ∃ out : Circuit signature (3 + 2) 2,
    (∀ x, 0 < (word fun i : Fin 2 => x (Fin.natAdd 3 i)).toNat →
      (word (out.eval interpretation x)).toNat =
        (word fun i : Fin 3 => x (Fin.castAdd 2 i)).toNat %
          (word fun i : Fin 2 => x (Fin.natAdd 3 i)).toNat) ∧
    out.size ≤ 1 + 3 * (22 * (2 + 1) + 3) :=
  bounded_modulus_remainder 3 2

/-! ### Semantics -/

-- The first hit on a reachable target, on an arbitrary finite linear order.
example (f : Fin 5 → Fin 5) (x y : Fin 5) (h : ∃ t, f^[t] x = y) :
    f^[hittingTime f x y] x = y ∧ hittingTime f x y < 5 := by
  obtain ⟨he, -, hlt⟩ := hittingTime_spec f x y ((reaches_iff f x y).mpr h)
  exact ⟨he, by simpa using hlt⟩

-- A long time normalizes below twice the number of states.
example (f : Fin 5 → Fin 5) (x : Fin 5) :
    f^[normalizedTime f x 1000] x = f^[1000] x ∧ normalizedTime f x 1000 < 10 :=
  ⟨iterate_normalizedTime f x 1000, by simpa using normalizedTime_lt f x 1000⟩

end ComplexityTests.Iteration.Dynamics
