/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.MCSP.Magnification.MergeTree.Circuit

/-!
# Tests: the McKay–Murray–Williams merge tree as an oracle circuit

The tree with no merge level is a single oracle gate on the whole truth table; each merge level
adds one oracle gate per state bit of each node; the McKay–Murray–Williams parameters give three
levels of two bits on `12` inputs with `s = 4`, and, within the corollary's regime `n ≤ s`, one
level of four bits on `16` inputs with `s = 16`; and the five facts of the `[MMW19]` bullet hold
together for one circuit.
-/

namespace CslibFrontierTests.MagnificationMergeTreeCircuit

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.MCSP Cslib.MCSP.MergeTree

/-- With no merge level the tree is one leaf: a single oracle gate deciding `MCSP[s]`. -/
example (s : ℕ → ℕ) (n k : ℕ) (T : BitString (2 ^ n)) :
    (circuit n (s n) k 0).eval (oracleInterpretation oracle) T 0 =
        (GapMCSP.yesSet s).slice (2 ^ n) T ∧
      (circuit n (s n) k 0).program.cost OracleOp.queryWeight = 1 :=
  ⟨eval_circuit s (by simp) T, by simp [cost_program_circuit]⟩

/-- One merge level of `k` bits adds one oracle gate per state bit of each of the `2 ^ k`
children. -/
example (n s k : ℕ) :
    (circuit n s k 1).program.cost OracleOp.queryWeight = 1 + stateWidth n s * 2 ^ k := by
  simp [cost_program_circuit]

/-- The McKay–Murray–Williams parameters on `12` inputs with `s = 4`: three levels of
`⌊log₂ 4⌋ = 2` bits, leaving leaves of `2 ^ 6 = s ³` points. -/
example : Nat.log 2 4 = 2 ∧ mmwLevels 12 4 = 3 := by
  have h : Nat.log 2 4 = 2 := by
    rw [show 4 = 2 ^ 2 by rfl, Nat.log_pow (by norm_num)]
  exact ⟨h, by simp [mmwLevels, h]⟩

/-- Within the corollary's regime `n ≤ s`: on `16` inputs with `s = 16` there is one merge level
of `⌊log₂ 16⌋ = 4` bits, above leaves of `2 ^ 12 = s ³` points. -/
example : mmwLevels 16 16 = 1 := by
  have h : Nat.log 2 16 = 4 := by
    rw [show 16 = 2 ^ 4 by rfl, Nat.log_pow (by norm_num)]
  simp [mmwLevels, h]

/-- **The `[MMW19]` bullet**, for `2 ≤ s` and `n ≤ s`: one circuit deciding `MCSP[s]` under the
merge-tree oracle with at most `1 + 128 N / s` oracle gates and `3 + 129 N / s` gates, adaptivity
`O(n / log s)` and fan-in `O(s ⁴)`. -/
example (s : ℕ → ℕ) (n : ℕ) (hns : n ≤ s n) (hs : 2 ≤ s n) (T : BitString (2 ^ n)) :
    (mmwCircuit n (s n)).eval (oracleInterpretation oracle) T 0 =
        (GapMCSP.yesSet s).slice (2 ^ n) T ∧
      s n * (mmwCircuit n (s n)).program.cost OracleOp.queryWeight ≤ s n + 128 * 2 ^ n ∧
      s n * (mmwCircuit n (s n)).size ≤ 129 * 2 ^ n + 3 * s n ∧
      (mmwCircuit n (s n)).depthWith OracleOp.queryWeight ≤ n / Nat.log 2 (s n) + 1 ∧
      (mmwCircuit n (s n)).FanInAtMost (12 * s n ^ 4) :=
  ⟨eval_mmwCircuit s n T, mul_cost_program_mmwCircuit_le hns, mul_size_mmwCircuit_le hns,
    depthWith_mmwCircuit_le _ _, fanInAtMost_mmwCircuit hns hs⟩

end CslibFrontierTests.MagnificationMergeTreeCircuit
