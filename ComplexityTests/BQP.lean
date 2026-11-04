/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.BQP

/-! `BQP`: uniform families that decide a language exactly, interference, closure under
complement, and a family whose acceptance probability `1 / 2` decides nothing. -/

namespace ComplexityTests.BQP

open Cslib Cslib.Quantum Cslib.Complexity Turing.MultiTapeTM

/-! ### Gate codes -/

-- A Toffoli gate with controls `0, 1` and target `2` is well formed on three qubits, but not on
-- two, nor with a repeated qubit, nor with three controls; Hadamard gates take no controls.
example : GateCode.WellFormed 3 (false, 2, [0, 1]) := by decide
example : ¬GateCode.WellFormed 2 (false, 2, [0, 1]) := by decide
example : ¬GateCode.WellFormed 3 (false, 1, [1]) := by decide
example : ¬GateCode.WellFormed 5 (false, 0, [1, 2, 3]) := by decide
example : GateCode.WellFormed 1 (true, 0, []) := by decide
example : ¬GateCode.WellFormed 2 (true, 0, [1]) := by decide

-- The Toffoli code maps `|110⟩` to `|111⟩`.
example : ∃ g, GateCode.toPlacedGate? 3 (false, 2, [0, 1]) = some g ∧
    g.eval (ket ![true, true, false]) = ket ![true, true, true] := by
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp
    (GateCode.isSome_toPlacedGate?_iff.mpr (by decide : GateCode.WellFormed 3 (false, 2, [0, 1])))
  refine ⟨g, hg, ?_⟩
  rw [GateCode.eval_toPlacedGate_ket hg (by decide)]
  congr 1
  funext i
  fin_cases i <;> rfl

/-! ### A family that reads the first input bit -/

/-- The family with one qubit more than the input and no gates: it measures the first input bit. -/
def readFirst : UniformCircuitFamily where
  width n := n + 1
  gates _ := []
  computableInPolyTime_width := by fun_prop
  computableInPolyTime_gates := ComputableInPolyTime.const _
  le_width n := Nat.le_succ n
  width_pos n := Nat.succ_pos n
  wellFormed _ _ h := by simp at h

/-- With no gates, the input basis state is measured, so the first input bit is read exactly. -/
theorem acceptProb_readFirst (x : List Bool) :
    readFirst.acceptProb x = if x.headD false then 1 else 0 := by
  change measureProb (Circuit.run (Circuit.ofCodes (x.length + 1) []) (inputState _ x))
    (accepting _) = _
  simp only [Circuit.ofCodes_nil, Circuit.run, Circuit.eval_nil, measureProb_ket,
    mem_accepting (Nat.succ_pos _), inputState]
  cases x <;> rfl

/-- The words whose first bit is one. -/
def FirstBit : Set (List Bool) := {x | x.headD false = true}

/-- Deciding the first bit, exactly: a member and a nonmember of `BQP`. -/
theorem firstBit_mem_BQP : FirstBit ∈ BQP encBits := by
  refine ⟨readFirst, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · rw [encBits_apply, acceptProb_readFirst]
    simp only [show x.headD false = true from hx, ite_true]
    norm_num
  · rw [encBits_apply, acceptProb_readFirst]
    simp only [show x.headD false = false from Bool.eq_false_iff.mpr hx, Bool.false_eq_true,
      ite_false]
    norm_num

example : FirstBitᶜ ∈ BQP encBits := compl_mem_BQP firstBit_mem_BQP

-- The bounds are not vacuous: `readFirst` accepts `[true]` with probability one, so it does not
-- witness that the complement of `FirstBit` is in `BQP`.
example : ¬(readFirst.acceptProb (encBits [true]) ≤ 1 / 3) := by
  rw [encBits_apply, acceptProb_readFirst]
  norm_num

/-! ### Interference -/

/-- Two Hadamard gates on qubit `0`: they cancel. -/
def hadamardTwice : UniformCircuitFamily where
  width n := n + 1
  gates _ := [(true, 0, []), (true, 0, [])]
  computableInPolyTime_width := by fun_prop
  computableInPolyTime_gates := ComputableInPolyTime.const _
  le_width n := Nat.le_succ n
  width_pos n := Nat.succ_pos n
  wellFormed n g hg := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hg
    subst hg
    exact ⟨Nat.succ_pos n, rfl⟩

-- `HH = I`: the two gates interfere, and the family reads the first bit like `readFirst`.
example (x : List Bool) : hadamardTwice.acceptProb x = readFirst.acceptProb x := by
  have hrun (m : ℕ) (hm : 0 < m) (z : Fin m → Bool) :
      Circuit.run (Circuit.ofCodes m [(true, 0, []), (true, 0, [])]) z = ket z := by
    simp only [Circuit.ofCodes, List.filterMap_cons, List.filterMap_nil, GateCode.toPlacedGate?,
      hm, ↓reduceDIte, Circuit.run, Circuit.eval_cons, Circuit.eval_nil, PlacedGate.eval,
      ← unitaryEquiv_mul, PlacedGate.matrix, ← map_mul, Gate.hadamard_mul_self, map_one,
      unitaryEquiv_one]
  change measureProb (Circuit.run (Circuit.ofCodes (x.length + 1) [(true, 0, []), (true, 0, [])])
      (inputState _ x)) (accepting _) =
    measureProb (Circuit.run (Circuit.ofCodes (x.length + 1) []) (inputState _ x)) (accepting _)
  rw [hrun _ (Nat.succ_pos _)]
  simp only [Circuit.ofCodes_nil, Circuit.run, Circuit.eval_nil]

/-! ### A family that decides nothing -/

/-- One Hadamard gate on qubit `0`. -/
def hadamardOnce : UniformCircuitFamily where
  width n := n + 1
  gates _ := [(true, 0, [])]
  computableInPolyTime_width := by fun_prop
  computableInPolyTime_gates := ComputableInPolyTime.const _
  le_width n := Nat.le_succ n
  width_pos n := Nat.succ_pos n
  wellFormed n g hg := by
    rw [List.mem_singleton.mp hg]
    exact ⟨Nat.succ_pos n, rfl⟩

/-- A Hadamard gate on qubit `0` makes it read `1` with probability `1 / 2`, whatever the input. -/
theorem acceptProb_hadamardOnce (x : List Bool) : hadamardOnce.acceptProb x = 1 / 2 := by
  set m := x.length + 1
  have hm : 0 < m := Nat.succ_pos _
  obtain ⟨g, hg⟩ : ∃ g, GateCode.toPlacedGate? m (true, 0, []) = some g :=
    Option.isSome_iff_exists.mp (GateCode.isSome_toPlacedGate?_iff.mpr
      (⟨hm, rfl⟩ : GateCode.WellFormed m (true, 0, [])))
  set z := inputState m x
  have hrun : Circuit.run (Circuit.ofCodes m [(true, 0, [])]) z = g.eval (ket z) := by
    simp [Circuit.ofCodes, hg, Circuit.run]
  have hnorm (c : ℂ) (hc : ‖c‖ = 1) : ‖c * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)‖ ^ 2 = 1 / 2 := by
    rw [norm_mul, hc, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (Real.sqrt_nonneg 2), inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  -- only the outcome `z[0 ↦ 1]` is accepting and reachable
  have hentry (y : Fin m → Bool) (hy : y ∈ accepting m) :
      ‖(g.eval (ket z)).ofLp y‖ ^ 2 = if y = Function.update z ⟨0, hm⟩ true then 1 / 2 else 0 := by
    rw [mem_accepting hm] at hy
    have hne : y ≠ Function.update z ⟨0, hm⟩ false := fun h => by
      simp [h] at hy
    rw [GateCode.eval_toPlacedGate_hadamard_ket hg hm, Fintype.sum_bool]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, ket_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero, hne, ite_false, add_zero]
    split_ifs <;> first | exact hnorm _ (by simp) | simp
  have hmem : Function.update z ⟨0, hm⟩ true ∈ accepting m := by
    rw [mem_accepting hm, Function.update_self]
  simp only [UniformCircuitFamily.acceptProb, acceptProb, hadamardOnce]
  change measureProb (Circuit.run (Circuit.ofCodes m [(true, 0, [])]) z) (accepting m) = 1 / 2
  rw [hrun, measureProb, Finset.sum_congr rfl hentry, Finset.sum_ite_eq' _ _ _]
  simp only [hmem, ite_true]

/-- Acceptance probability `1 / 2` is neither at least `2 / 3` nor at most `1 / 3`, so
`hadamardOnce` decides no set of words with bounded error. -/
example (A : Set (List Bool)) : ¬∀ x,
    (x ∈ A → 2 / 3 ≤ hadamardOnce.acceptProb (encBits x)) ∧
      (x ∉ A → hadamardOnce.acceptProb (encBits x) ≤ 1 / 3) := by
  intro h
  by_cases hx : ([] : List Bool) ∈ A
  · have := (h []).1 hx
    rw [acceptProb_hadamardOnce] at this
    norm_num at this
  · have := (h []).2 hx
    rw [acceptProb_hadamardOnce] at this
    norm_num at this

end ComplexityTests.BQP
