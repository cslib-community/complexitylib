/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.BinaryCost
public import Complexity.Foundations.Data.BitString.Parity
public import Cslib.Computability.Circuit.Boolean.Complexity
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Circuits for parity

Chaining `x ⊕ y = (x ∨ y) ∧ ¬(x ∧ y)` computes the parity of `n + 1` bits with `4 n` De Morgan
gates, `3 n` of them AND or OR gates (`exists_computes_parity`) [Jukna, Section 1.6][Jukna2012].
The number of binary gates is optimal by Schnorr's bound,
`Cslib.Circuits.Boolean.three_mul_le_cost_of_computes_parity`.

## Main definitions

* `Cslib.Circuits.Program.appendXor`: append four De Morgan gates computing the exclusive or of two
  wires.
* `Cslib.Circuits.Boolean.parityProgram`: a De Morgan program for the parity of the first bits.

## Main results

* `Cslib.Circuits.Boolean.exists_computes_parity`: the parity of `n + 1` bits has circuits with
  `3 n` binary gates and `4 n` gates in all.
* `Cslib.Circuits.Boolean.complexity_parity_le`: its circuit complexity is at most `4 n`.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits

variable {n g : ℕ}

/-- Append `u ⊕ v = (u ∨ v) ∧ ¬(u ∧ v)` to a De Morgan program: four gates, three of them binary,
the last of which computes the exclusive or of the wires `u` and `v`. -/
def Program.appendXor (p : Program Boolean.signature n g) (u v : Wire n g) :
    Program Boolean.signature n (g + 4) :=
  (((p.gate ⟨.or, ![u, v]⟩).gate ⟨.and, ![u.castSucc, v.castSucc]⟩).gate
    ⟨.not, ![Wire.gate (Fin.last (g + 1))]⟩).gate
    ⟨.and, ![Wire.gate (Fin.last g).castSucc.castSucc, Wire.gate (Fin.last (g + 2))]⟩

private theorem Program.trace_appendXor (p : Program Boolean.signature n g) (u v : Wire n g)
    (x : BitString n) :
    (p.appendXor u v).trace Boolean.interpretation x (.gate (Fin.last (g + 3))) =
      (p.trace Boolean.interpretation x u ^^ p.trace Boolean.interpretation x v) := by
  have trace_eq : ∀ {g'} (q : Program Boolean.signature n g') (w : Wire n g'),
      Wire.elim x (q.eval Boolean.interpretation x) w = q.trace Boolean.interpretation x w :=
    fun _ _ => rfl
  simp only [appendXor, trace_gateWire, gateFunction_apply, eval_gate_last, eval_gate_castSucc,
    Line.eval, Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one,
    Boolean.interpretation, trace_eq, trace_gate_castSucc]
  cases p.trace Boolean.interpretation x u <;> cases p.trace Boolean.interpretation x v <;> rfl

/-- Appending an exclusive-or gadget adds `3` to the binary gate cost of a De Morgan program. -/
@[simp] theorem Program.cost_appendXor (p : Program Boolean.signature n g) (u v : Wire n g) :
    (p.appendXor u v).cost Boolean.binaryCost = p.cost Boolean.binaryCost + 3 := by
  simp [appendXor]

namespace Boolean

open Finset

/-- A De Morgan program computing the parity of the bits `0, …, k`, and its output wire: `4 k`
gates, `3 k` of them binary. -/
def parityProgram : (k : ℕ) → k < n → Program signature n (4 * k) × Wire n (4 * k)
  | 0, hk => (.empty, .input ⟨0, hk⟩)
  | k + 1, hk =>
    let pw := parityProgram k (by omega)
    (pw.1.appendXor pw.2 (.input ⟨k + 1, hk⟩), .gate (Fin.last _))

private theorem trace_parityProgram (k : ℕ) (hk : k < n) (x : BitString n) :
    (parityProgram k hk).1.trace interpretation x (parityProgram k hk).2 =
      parityOn (Iic ⟨k, hk⟩) x := by
  induction k with
  | zero =>
    have : Iic (⟨0, hk⟩ : Fin n) = insert ⟨0, hk⟩ ∅ := by
      ext i
      simp [Fin.le_def, Fin.ext_iff]
    rw [this, parityOn_insert (notMem_empty _), parityOn_empty, Bool.xor_false]
    rfl
  | succ k ih =>
    have : Iic (⟨k + 1, hk⟩ : Fin n) = insert ⟨k + 1, hk⟩ (Iic ⟨k, by omega⟩) := by
      ext i
      simp only [mem_Iic, mem_insert, Fin.le_def, Fin.ext_iff]
      omega
    rw [this, parityOn_insert (by simp [Fin.le_def]), ← ih (by omega), Bool.xor_comm]
    exact Program.trace_appendXor _ _ _ x

private theorem cost_parityProgram (k : ℕ) (hk : k < n) :
    (parityProgram k hk).1.cost binaryCost = 3 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [parityProgram, Program.cost_appendXor, ih]
    omega

/-- **Parity has circuits with `3 n` binary gates.** The parity of `n + 1` bits has a De Morgan
circuit with `3 n` AND and OR gates, which matches Schnorr's lower bound, and `4 n` gates in all. -/
theorem exists_computes_parity (n : ℕ) :
    ∃ C : Circuit signature (n + 1) 1, C.Computes interpretation (single (parity (n + 1))) ∧
      C.program.cost binaryCost = 3 * n ∧ C.size = 4 * n := by
  refine ⟨⟨(parityProgram n n.lt_succ_self).1, fun _ => (parityProgram n n.lt_succ_self).2⟩,
    fun x => funext fun _ => ?_, cost_parityProgram n _, rfl⟩
  have : Iic (⟨n, n.lt_succ_self⟩ : Fin (n + 1)) = univ := by
    ext i
    simpa [Fin.le_def] using Nat.lt_succ_iff.1 i.isLt
  exact (trace_parityProgram n _ x).trans (by rw [this]; rfl)

/-- The parity of no bits is computed by one constant gate, which is not binary. -/
theorem exists_computes_parity_zero :
    ∃ C : Circuit signature 0 1, C.Computes interpretation (single (parity 0)) ∧
      C.program.cost binaryCost = 0 := by
  refine ⟨⟨Program.empty.gate ⟨.const false, Fin.elim0⟩, fun _ => .gate (Fin.last 0)⟩,
    fun x => ?_, rfl⟩
  funext
  change (Program.empty.gate _).eval interpretation x (Fin.last 0) = parity 0 x
  rw [Program.eval_gate_last]
  simp [Line.eval, interpretation, parity, parityOn]

/-- The circuit complexity of the parity of `n + 1` bits is at most `4 n`. -/
theorem complexity_parity_le (n : ℕ) :
    complexity interpretation (single (parity (n + 1))) ≤ 4 * n := by
  obtain ⟨C, hC, -, hsize⟩ := exists_computes_parity n
  exact hsize ▸ complexity_le_of_computes C hC

end Boolean

end Cslib.Circuits
