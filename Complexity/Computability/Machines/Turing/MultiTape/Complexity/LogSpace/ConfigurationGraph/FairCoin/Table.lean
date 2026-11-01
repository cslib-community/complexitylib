/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.FairCoin.ReadInput
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.InputTable
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.CounterBounds

/-!
# A native writer for the compact fair-coin table

`coinTable` enumerates the polynomial compact box, including its guarded invalid IDs. Each entry
has two bits: `[false, false]`, `[true, false]`, or `[true, true]` records a coin count of zero,
one, or two. The order is row-major, with the two bits consecutive at each entry.

`coinTableProgram` starts from its actual zeroed initializer on the original framed word. It
reads the input length with the existing word header, enumerates both compact IDs with bounded
counter loops, and evaluates the shared `coinCountExpr` after reading each entry's original input
symbol. No input length or vertex ID is supplied in advance. `computableInLogSpace_coinTable`
is a native space certificate for the entire writer.

This is the ambient ordinary coin-count table. Invalid compact IDs retain the existing edge
predicate's behavior. The clocked writer reuses the same program in `FairCoin.ClockedTable`;
paired ports and the recursive estimator remain separate.

## Main definitions

* `Turing.MultiTapePTM.ConfigurationGraph.coinTable`: the row-major two-bit count table.
* `Turing.MultiTapePTM.ConfigurationGraph.coinTableProgram`: its initialized counter transducer.

## Main results

* `Turing.MultiTapePTM.ConfigurationGraph.getD_coinTable`: the exact bit at a row-major index.
* `Turing.MultiTapePTM.ConfigurationGraph.coinTable_count`: decoding the two bits gives the count.
* `Turing.MultiTapePTM.ConfigurationGraph.reachesOut_coinTableProgram`: the actual initialized run.
* `Turing.MultiTapePTM.ConfigurationGraph.computableInLogSpace_coinTable`: native logarithmic space.
-/

public section

namespace Turing.MultiTapePTM.ConfigurationGraph

open MultiTapeNTM.ConfigurationGraph CounterProgram Instr Expr MultiTapeTM
open Cslib.Turing

variable {k : ℕ} {State : Type} [Fintype State]

/-- Every compact row and column, with two consecutive threshold bits encoding its coin count.
The original input is read at the source's existing `queryIndex`. -/
noncomputable def coinTable (machine : MultiTapePTM k Bool State) (D : ℕ) (w : List Bool) :
    List Bool :=
  let B := radix D w.length
  let N := vertexBound (k := k) B
  List.twoBitTable N fun u v =>
    coinCountWithSymbol machine B w.length u v w[queryIndex (k := k) B u]?

variable (machine : MultiTapePTM k Bool State) (D : ℕ) (w : List Bool)

/-- The finite-index definition agrees with the natural-counter enumeration used by the writer. -/
theorem coinTable_eq_flatMap :
    coinTable machine D w =
      (List.range (vertexBound (k := k) (radix D w.length))).flatMap fun u =>
        (List.range (vertexBound (k := k) (radix D w.length))).flatMap fun v =>
          let c := coinCountWithSymbol machine (radix D w.length) w.length u v
            w[queryIndex (k := k) (radix D w.length) u]?
          [decide (0 < c), decide (1 < c)] := by
  simpa only [coinTable] using List.twoBitTable_eq_flatMap
    (vertexBound (k := k) (radix D w.length))
    (fun u v => coinCountWithSymbol machine (radix D w.length) w.length u v
      w[queryIndex (k := k) (radix D w.length) u]?)

/-- The table has exactly two bits for each ordered pair of compact IDs. -/
@[simp] theorem length_coinTable :
    (coinTable machine D w).length =
      2 * vertexBound (k := k) (radix D w.length) ^ 2 := by
  simp only [coinTable, List.length_twoBitTable]

/-- Reading either bit at its ordinary row-major address returns the corresponding threshold. -/
theorem getD_coinTable
    (u v : Fin (vertexBound (k := k) (radix D w.length))) (b : Fin 2) :
    (coinTable machine D w).getD
        (2 * (u.val * vertexBound (k := k) (radix D w.length) + v.val) + b.val) false =
      decide (b.val < coinCountWithSymbol machine (radix D w.length) w.length u v
        w[queryIndex (k := k) (radix D w.length) u]?) := by
  simpa only [coinTable] using List.getD_twoBitTable
    (vertexBound (k := k) (radix D w.length))
    (fun u v => coinCountWithSymbol machine (radix D w.length) w.length u v
      w[queryIndex (k := k) (radix D w.length) u]?) u v b

/-- Summing the two stored bits recovers the exact count, including coincident successors. -/
theorem coinTable_count (u v : Fin (vertexBound (k := k) (radix D w.length))) :
    ((coinTable machine D w).getD
        (2 * (u.val * vertexBound (k := k) (radix D w.length) + v.val)) false).toNat +
      ((coinTable machine D w).getD
        (2 * (u.val * vertexBound (k := k) (radix D w.length) + v.val) + 1) false).toNat =
      coinCountWithSymbol machine (radix D w.length) w.length u v
        w[queryIndex (k := k) (radix D w.length) u]? := by
  simpa only [coinTable] using List.count_twoBitTable
    (vertexBound (k := k) (radix D w.length))
    (fun u v => coinCountWithSymbol machine (radix D w.length) w.length u v
      w[queryIndex (k := k) (radix D w.length) u]?) u v (coinCountWithSymbol_le_two ..)

/-- The initialized writer. The header occupies labels zero to three, the two loops start at
four and seven, the count reader starts at ten, and labels sixteen to twenty-one emit its bits.
Label twenty-two halts. The four registers are length, row, column, and count scratch. -/
@[expose] noncomputable def coinTableProgram : CounterProgram :=
  inputCountTableProgram (vertexBoundExpr k (radixExpr D (reg 0)))
    (queryIndexExpr k (radixExpr D (reg 0)) (reg 1))
    (coinCountExpr machine (radixExpr D (reg 0)) (reg 0) (reg 1) (reg 2) (reg 3))

variable {machine D w} {S : ℕ}

variable (machine D w)

/-- The actual zero-initialized program counts the input length, enumerates every compact pair,
emits the whole table, and reaches its halt with all final registers within the common bound. -/
theorem reachesOut_coinTableProgram
    (hinput : (frame w).length ≤ S)
    (hN : vertexBound (k := k) (radix D w.length) ≤ S) (h2 : 2 ≤ S) :
    ∃ regs, (coinTableProgram machine D).ReachesOut (frame w)
      ((coinTableProgram machine D).Active S) (coinTableProgram machine D).init
      (22, regs) (coinTable machine D w) ∧ ∀ r ∈ regs, r ≤ S := by
  apply reachesOut_inputCountTableProgram
    (count := fun u v => coinCountWithSymbol machine (radix D w.length) w.length u v
      w[queryIndex (k := k) (radix D w.length) u]?)
    (fun u v y => by simp) ?_ (fun u v => coinCountWithSymbol_le_two ..) hinput hN h2
  intro u v y
  simpa only [eval_queryIndexExpr, eval_radixExpr, eval_reg,
    List.getD_cons_zero, List.getD_cons_succ] using
      eval_coinCountExpr machine (B := radixExpr D (reg 0))
        (n := reg 0) (u := reg 1) (v := reg 2) (sym := reg 3)
        (regs := [w.length, u, v, symbolCode
          w[queryIndex (k := k) (radix D w.length) u]?]) rfl

/-- The entire compact coin table is computed from the original framed word in native
deterministic logarithmic space. No parameters or counters are preloaded. -/
theorem computableInLogSpace_coinTable :
    ComputableInLogSpace (coinTable machine D) (encFramed encBits) encBits := by
  refine (coinTableProgram machine D).computableInLogSpace_of_reachesOut
    (D * Fintype.card (Register k) + 1) fun w => ?_
  simp only [encFramed_apply, encBits_apply]
  obtain ⟨hN, _, h2⟩ := configurationCounter_bounds (k := k) D w
  have hinput : (frame w).length ≤
      ((frame w).length + 1) ^ (D * Fintype.card (Register k) + 1) := by
    rw [pow_succ]
    have hone : 1 ≤ ((frame w).length + 1) ^ (D * Fintype.card (Register k)) :=
      Nat.one_le_pow _ _ (by omega)
    exact (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ hone)
  obtain ⟨regs, hr, hregs⟩ := reachesOut_coinTableProgram machine D w hinput (by omega) h2
  exact ⟨(22, regs), _, [], hr, rfl, by simp, hregs⟩

end Turing.MultiTapePTM.ConfigurationGraph
