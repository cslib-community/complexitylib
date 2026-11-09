/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.FairCoin.Clocked
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.InputTable

/-!
# Native initialized serialization of the clocked coin matrix

`clockedCoinTable` stores two threshold bits for every ordered pair of numeric clock/base IDs.
At horizon `T = 2 * (2 * (n + 1)) ^ d`, the dimension is `(T + 1) * N`, where `N` is the
ordinary compact box. The count is the existing base count on remainders exactly when the
target quotient is one greater than the source quotient. Thus terminal rows are zero.

`clockedCoinTableProgram` uses the same header, loops, original-input reader and emitter as
the ordinary table. It starts from zero registers on `frame w`, queries using the base source,
and emits the full table in native logarithmic space. Only the bound, query and value expressions
differ. The exact semantic matrix interpretation is in `Randomized.ClockedTable`.

This output is the matrix payload. A complete serialized instance containing dimension, start
and reward fields, directed paired ports, and the native estimator remain separate.

## Main definitions

* `Turing.MultiTapePTM.ConfigurationGraph.clockedCoinTable`: the two-bit matrix payload.
* `Turing.MultiTapePTM.ConfigurationGraph.clockedCoinTableProgram`: its initialized writer.

## Main results

* `Turing.MultiTapePTM.ConfigurationGraph.length_clockedCoinTable`,
  `Turing.MultiTapePTM.ConfigurationGraph.getD_clockedCoinTable`,
  `Turing.MultiTapePTM.ConfigurationGraph.clockedCoinTable_count`: exact length and decoding.
* `Turing.MultiTapePTM.ConfigurationGraph.reachesOut_clockedCoinTableProgram`: bounded run.
* `Turing.MultiTapePTM.ConfigurationGraph.computableInLogSpace_clockedCoinTable`: native space.
-/

public section

namespace Turing.MultiTapePTM.ConfigurationGraph

open MultiTapeNTM.ConfigurationGraph CounterProgram Expr MultiTapeTM

variable {k : ℕ} {State : Type} [Fintype State]

/-- Every pair of clock/base IDs, with two threshold bits encoding the next-clock coin count.
The one original-input read uses the base source, obtained by remainder modulo the base box. -/
noncomputable def clockedCoinTable (machine : MultiTapePTM k Bool State)
    (D d : ℕ) (w : List Bool) : List Bool :=
  let B := radix D w.length
  let N := vertexBound (k := k) B
  List.twoBitTable (clockedVertexBound (k := k) D d w.length) fun u v =>
    clockedCoinCountWithSymbol machine B w.length u v w[queryIndex (k := k) B (u % N)]?

variable (machine : MultiTapePTM k Bool State) (D d : ℕ) (w : List Bool)

/-- Exactly two bits are emitted for every ordered pair of clocked IDs. -/
@[simp] theorem length_clockedCoinTable :
    (clockedCoinTable machine D d w).length =
      2 * clockedVertexBound (k := k) D d w.length ^ 2 := by
  simp only [clockedCoinTable, List.length_twoBitTable]

/-- Each bit at its row-major address is the corresponding exact clocked-count threshold. -/
theorem getD_clockedCoinTable (u v : Fin (clockedVertexBound (k := k) D d w.length))
    (b : Fin 2) :
    (clockedCoinTable machine D d w).getD
        (2 * (u.val * clockedVertexBound (k := k) D d w.length + v.val) + b.val) false =
      decide (b.val < clockedCoinCountWithSymbol machine (radix D w.length) w.length u v
        w[queryIndex (k := k) (radix D w.length)
          (u.val % vertexBound (k := k) (radix D w.length))]?) := by
  simpa only [clockedCoinTable] using List.getD_twoBitTable
    (clockedVertexBound (k := k) D d w.length)
    (fun u v => clockedCoinCountWithSymbol machine (radix D w.length) w.length u v
      w[queryIndex (k := k) (radix D w.length)
        (u % vertexBound (k := k) (radix D w.length))]?) u v b

/-- Summing the two bits recovers the exact count, including two coincident coin branches. -/
theorem clockedCoinTable_count (u v : Fin (clockedVertexBound (k := k) D d w.length)) :
    ((clockedCoinTable machine D d w).getD
        (2 * (u.val * clockedVertexBound (k := k) D d w.length + v.val)) false).toNat +
      ((clockedCoinTable machine D d w).getD
        (2 * (u.val * clockedVertexBound (k := k) D d w.length + v.val) + 1) false).toNat =
      clockedCoinCountWithSymbol machine (radix D w.length) w.length u v
        w[queryIndex (k := k) (radix D w.length)
          (u.val % vertexBound (k := k) (radix D w.length))]? := by
  simpa only [clockedCoinTable] using List.count_twoBitTable
    (clockedVertexBound (k := k) D d w.length)
    (fun u v => clockedCoinCountWithSymbol machine (radix D w.length) w.length u v
      w[queryIndex (k := k) (radix D w.length)
        (u % vertexBound (k := k) (radix D w.length))]?) u v
    (clockedCoinCountWithSymbol_le_two ..)

/-- Both encoded bits are zero throughout a terminal row, for every bounded target ID. -/
theorem getD_clockedCoinTable_terminal
    (u v : Fin (clockedVertexBound (k := k) D d w.length)) (b : Fin 2)
    (hu : u.val / vertexBound (k := k) (radix D w.length) =
      2 * (2 * (w.length + 1)) ^ d) :
    (clockedCoinTable machine D d w).getD
      (2 * (u.val * clockedVertexBound (k := k) D d w.length + v.val) + b.val) false = false := by
  rw [getD_clockedCoinTable, clockedCoinCountWithSymbol_terminal machine u v hu]
  simp

/-- The same 23-label four-register writer as the ordinary table, with clocked arithmetic.
Registers are length, flat row, flat column and scratch; no parameter is preloaded. -/
@[expose] noncomputable def clockedCoinTableProgram : CounterProgram :=
  inputCountTableProgram (clockedVertexBoundExpr k D d (reg 0))
    (queryIndexExpr k (radixExpr D (reg 0))
      (mod (reg 1) (vertexBoundExpr k (radixExpr D (reg 0)))))
    (clockedCoinCountExpr machine (radixExpr D (reg 0)) (reg 0) (reg 1) (reg 2) (reg 3))

variable {S : ℕ}

/-- Starting from the actual zeroed initializer on the original frame, the writer emits the
whole clocked table and reaches label twenty-two with all registers within the common bound. -/
theorem reachesOut_clockedCoinTableProgram (hinput : (frame w).length ≤ S)
    (hN : clockedVertexBound (k := k) D d w.length ≤ S) (h2 : 2 ≤ S) :
    ∃ regs, (clockedCoinTableProgram machine D d).ReachesOut (frame w)
      ((clockedCoinTableProgram machine D d).Active S) (clockedCoinTableProgram machine D d).init
      (22, regs) (clockedCoinTable machine D d w) ∧ ∀ r ∈ regs, r ≤ S := by
  apply reachesOut_inputCountTableProgram
    (count := fun u v => clockedCoinCountWithSymbol machine (radix D w.length) w.length u v
      w[queryIndex (k := k) (radix D w.length)
        (u % vertexBound (k := k) (radix D w.length))]?)
    (fun u v y => by simp) ?_ (fun u v => clockedCoinCountWithSymbol_le_two ..) hinput hN h2
  intro u v y
  simpa only [eval_queryIndexExpr, eval_radixExpr, eval_reg, eval_mod, eval_vertexBoundExpr,
    List.getD_cons_zero, List.getD_cons_succ] using
      eval_clockedCoinCountExpr machine (B := radixExpr D (reg 0))
        (n := reg 0) (u := reg 1) (v := reg 2) (sym := reg 3)
        (regs := [w.length, u, v, symbolCode w[queryIndex (k := k) (radix D w.length)
          (u % vertexBound (k := k) (radix D w.length))]?]) rfl

/-- The entire clocked matrix payload is computed in native deterministic logarithmic space
from the original framed word, with no preloaded length, clock or configuration IDs. -/
theorem computableInLogSpace_clockedCoinTable :
    ComputableInLogSpace (clockedCoinTable machine D d) (encFramed encBits) encBits := by
  refine (clockedCoinTableProgram machine D d).computableInLogSpace_of_reachesOut
    (D * Fintype.card (Register k) + d + 2) fun w => ?_
  simp only [encFramed_apply, encBits_apply]
  have hframe : (frame w).length + 1 = 2 * (w.length + 1) := by rw [length_frame]; omega
  have hN : clockedVertexBound (k := k) D d w.length + 1 ≤
      ((frame w).length + 1) ^ (D * Fintype.card (Register k) + d + 2) := by
    simpa only [clockedVertexBound, hframe] using
      clockedVertexBound_add_one_le_pow (k := k) D d w.length
  have hF : (frame w).length + 1 ≤
      ((frame w).length + 1) ^ (D * Fintype.card (Register k) + d + 2) :=
    le_self_pow (by omega) (by omega)
  have h2 : 2 ≤ ((frame w).length + 1) ^ (D * Fintype.card (Register k) + d + 2) :=
    (by rw [hframe]; omega : 2 ≤ (frame w).length + 1).trans hF
  obtain ⟨regs, hr, hregs⟩ := reachesOut_clockedCoinTableProgram machine D d w
    ((Nat.le_succ _).trans hF) (by omega) h2
  exact ⟨(22, regs), _, [], hr, rfl, by simp, hregs⟩

end Turing.MultiTapePTM.ConfigurationGraph
