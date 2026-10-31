/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.BQP.TensorContraction

/-! Quantum circuits by tensor contraction: the bipartition and admissibility of the network of a
circuit, the value the simulator computes on small circuits, a member of `BQTIME`, and the class
containment applied to it. -/

namespace ComplexityTests.BQPTensorContraction

open Cslib Cslib.Quantum Cslib.Quantum.PathNetwork Cslib.Complexity
  Cslib.Complexity.QuantumContraction Turing.MultiTapeTM

/-! ### The bipartition -/

-- A Hadamard gate copied by a CNOT: every edge joins a row to a column.
example :
    (network (-1 : ℤ) [0] [false, false] [(true, 1, []), (false, 0, [1])]).2.IsRowsFirstBipartite
      (network (-1 : ℤ) [0] [false, false] [(true, 1, []), (false, 0, [1])]).1 := by decide

example :
    (network (-1 : ℤ) [0] [false, false] [(true, 1, []), (false, 0, [1])]).2.IsRowsFirstBipartite
      (network (-1 : ℤ) [0] [false, false] [(true, 1, []), (false, 0, [1])]).1 :=
  isRowsFirstBipartite_network _ _ _ (by decide)

-- The hypothesis that the qubits of a gate are distinct is needed: a CNOT whose control is its
-- target reads the same link edge twice.
example :
    ¬(network (-1 : ℤ) [0] [false, false] [(true, 0, []), (false, 0, [0])]).2.IsRowsFirstBipartite
      (network (-1 : ℤ) [0] [false, false] [(true, 0, []), (false, 0, [0])]).1 := by decide

-- A Toffoli gate: three occurrences, so twelve edges, admissible at size twelve.
example : CountingSimulation.ExplicitAdmissible 6 12
    (network 7 [0] [false, false, false] [(false, 2, [0, 1])]) :=
  explicitAdmissible_network 7 [0] [false, false, false] (by decide) (by decide)

/-! ### The simulator -/

-- One Hadamard gate on `|0⟩`: the gap is `1`, so the acceptance probability is `1 / 2`.
example : gapValue [0] [(true, 0, [])] [false] = 1 := by decide

example : acceptProb 1 [(true, 0, [])] [false] = 1 / 2 := by
  rw [acceptProb_eq_onesProb, onesProb_eq_gapValue (by decide) [0] (by decide)]
  rw [show gapValue [0] [(true, 0, [])] ([false] ++ List.replicate (1 - [false].length) false) = 1
    by decide]
  norm_num [hadamardCount]

-- Without gates, the simulator reads the measured qubits.
example : gapValue [0] [] [true, false] = 1 := by decide
example : gapValue [0] [] [false, true] = 0 := by decide
example : gapValue [0, 1] [] [true, true] = 1 := by decide

-- Two Hadamard gates on `|1⟩` interfere: the gap is `2 ^ 2`.
example : gapValue [0] [(true, 0, []), (true, 0, [])] [true] = 4 := by
  rw [gapValue_eq _ (by decide)]
  decide

-- Measuring no qubit gives `2 ^ h`, the denominator of the bounded-error rule.
example : gapValue [] [(true, 0, []), (true, 0, [])] [true] = 4 := by
  rw [gapValue_eq _ (by decide)]
  decide

/-! ### A member of `BQTIME` -/

/-- The family with one qubit more than the input and no gates: it measures the first input bit. -/
def readFirst : UniformCircuitFamily where
  width n := n + 1
  gates _ := []
  computableInPolyTime_width := by fun_prop
  computableInPolyTime_gates := ComputableInPolyTime.const _
  le_width n := Nat.le_succ n
  width_pos n := Nat.succ_pos n
  wellFormed _ _ h := by simp at h

theorem acceptProb_readFirst (x : List Bool) :
    readFirst.acceptProb x = if x.headD false then 1 else 0 := by
  change measureProb (Circuit.run (Circuit.ofCodes (x.length + 1) []) (inputState _ x))
    (accepting _) = _
  simp only [Circuit.ofCodes_nil, Circuit.run, Circuit.eval_nil, measureProb_ket,
    mem_accepting (Nat.succ_pos _), inputState]
  cases x <;> rfl

/-- The words whose first bit is one. -/
def FirstBit : Set (List Bool) := {x | x.headD false = true}

/-- Deciding the first bit takes no gates. -/
theorem firstBit_mem_BQTIME (t : ℕ → ℕ) : FirstBit ∈ BQTIME encBits t := by
  refine ⟨readFirst, 0, 0, fun n => by simp [readFirst], fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · rw [encBits_apply, acceptProb_readFirst]
    simp only [show x.headD false = true from hx, ite_true]
    norm_num
  · rw [encBits_apply, acceptProb_readFirst]
    simp only [show x.headD false = false from Bool.eq_false_iff.mpr hx, Bool.false_eq_true,
      ite_false]
    norm_num

example : FirstBit ∈ BQP encBits := BQTIME_subset_BQP _ (firstBit_mem_BQTIME fun _ => 0)

example : FirstBit ∈ BQP encBits :=
  BQP_eq_iUnion_BQTIME ▸ Set.mem_iUnion.mpr ⟨1, firstBit_mem_BQTIME _⟩

-- The containment applies with the clock `T n = n + 2`, which satisfies `max n 2 ≤ T n`.
example : FirstBit ∈ ⋃ C, DTIME encBits fun n =>
    2 ^ (C * (n + 2) / Nat.sqrt (Nat.log 2 (n + 2))) :=
  BQTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two (T := fun n => n + 2)
    (fun n => max_le (by omega) (by omega)) (firstBit_mem_BQTIME _)

example : ∃ C d : ℕ, DecidableInTimeAndSpace FirstBit encBits
    (fun x => 2 ^ (C * ((encBits x).length + 2) / Nat.sqrt (Nat.log 2 ((encBits x).length + 2))))
    (fun x => ((encBits x).length + 2) ^ d) :=
  exists_decidableInTimeAndSpace_of_mem_BQTIME (T := fun n => n + 2)
    (fun n => max_le (by omega) (by omega)) (firstBit_mem_BQTIME _)

end ComplexityTests.BQPTensorContraction
