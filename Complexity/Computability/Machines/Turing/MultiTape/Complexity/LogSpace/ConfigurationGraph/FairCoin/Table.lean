/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.FairCoin.ReadInput
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Words
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.CounterBounds
import Complexity.Foundations.Data.List.RowMajor

/-!
# A native writer for the compact fair-coin table

`coinTable` enumerates the polynomial compact box, including its guarded invalid IDs. Each entry
has two bits: `[false, false]`, `[true, false]`, or `[true, true]` records a coin count of zero,
one, or two. The order is row-major, with the two bits consecutive at each entry.

`coinTableProgram` starts from its actual zeroed initializer on the original framed word. It
reads the input length with the existing word header, enumerates both compact IDs with bounded
counter loops, and calls `coinCountCode` for every entry. No input length or vertex ID is supplied
in advance. `computableInLogSpace_coinTable` is a native space certificate for the entire writer.

This is the ambient ordinary coin-count table. Invalid compact IDs retain the existing edge
predicate's behavior. Clocked enumeration, the bridge to the strict-forward configuration system,
paired ports, and the recursive estimator remain separate.

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
  (List.finRange N).flatMap fun u : Fin N => (List.finRange N).flatMap fun v : Fin N =>
    List.ofFn fun b : Fin 2 => decide (b.val <
      coinCountWithSymbol machine B w.length u v w[queryIndex (k := k) B u]?)

variable (machine : MultiTapePTM k Bool State) (D : ℕ) (w : List Bool)

/-- The finite-index definition agrees with the natural-counter enumeration used by the writer. -/
theorem coinTable_eq_flatMap :
    coinTable machine D w =
      (List.range (vertexBound (k := k) (radix D w.length))).flatMap fun u =>
        (List.range (vertexBound (k := k) (radix D w.length))).flatMap fun v =>
          let c := coinCountWithSymbol machine (radix D w.length) w.length u v
            w[queryIndex (k := k) (radix D w.length) u]?
          [decide (0 < c), decide (1 < c)] := by
  have hval (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem <;> simp
  dsimp only [coinTable]
  conv_rhs => rw [← hval]; simp only [List.flatMap_map]
  apply List.flatMap_congr
  intro u _
  apply List.flatMap_congr
  intro v _
  simp [List.ofFn_succ]

/-- The table has exactly two bits for each ordered pair of compact IDs. -/
@[simp] theorem length_coinTable :
    (coinTable machine D w).length =
      2 * vertexBound (k := k) (radix D w.length) ^ 2 := by
  dsimp only [coinTable]
  simp_rw [List.flatMap_ofFn_prod]
  simp only [List.length_ofFn]
  ring

/-- Reading either bit at its ordinary row-major address returns the corresponding threshold. -/
theorem getD_coinTable
    (u v : Fin (vertexBound (k := k) (radix D w.length))) (b : Fin 2) :
    (coinTable machine D w).getD
        (2 * (u.val * vertexBound (k := k) (radix D w.length) + v.val) + b.val) false =
      decide (b.val < coinCountWithSymbol machine (radix D w.length) w.length u v
        w[queryIndex (k := k) (radix D w.length) u]?) := by
  let p := finProdFinEquiv (u, finProdFinEquiv (v, b))
  have hp : 2 * (u.val * vertexBound (k := k) (radix D w.length) + v.val) + b.val = p.val := by
    simp only [p, finProdFinEquiv, Equiv.coe_fn_mk]
    ring
  rw [hp]
  dsimp only [coinTable]
  simp_rw [List.flatMap_ofFn_prod]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  simp only [Fin.eta, p, Equiv.symm_apply_apply]

/-- Summing the two stored bits recovers the exact count, including coincident successors. -/
theorem coinTable_count (u v : Fin (vertexBound (k := k) (radix D w.length))) :
    ((coinTable machine D w).getD
        (2 * (u.val * vertexBound (k := k) (radix D w.length) + v.val)) false).toNat +
      ((coinTable machine D w).getD
        (2 * (u.val * vertexBound (k := k) (radix D w.length) + v.val) + 1) false).toNat =
      coinCountWithSymbol machine (radix D w.length) w.length u v
        w[queryIndex (k := k) (radix D w.length) u]? := by
  have h0 := getD_coinTable machine D w u v 0
  have h1 := getD_coinTable machine D w u v 1
  simp only [Fin.val_zero, Fin.val_one, Nat.add_zero] at h0 h1
  rw [h0, h1]
  have hc := coinCountWithSymbol_le_two machine (radix D w.length) w.length u v
    w[queryIndex (k := k) (radix D w.length) u]?
  interval_cases coinCountWithSymbol machine (radix D w.length) w.length u v
    w[queryIndex (k := k) (radix D w.length) u]? <;> rfl

/-- The initialized writer. The header occupies labels zero to three, the two loops start at
four and seven, the count reader starts at ten, and labels sixteen to twenty-one emit its bits.
Label twenty-two halts. The four registers are length, row, column, and count scratch. -/
@[expose] noncomputable def coinTableProgram : CounterProgram where
  code :=
    Words.headerCode ++
    forCode 4 1 (vertexBoundExpr k (radixExpr D (reg 0))) 7 22 ++
    forCode 7 2 (vertexBoundExpr k (radixExpr D (reg 0))) 10 6 ++
    coinCountCode machine D 10 16 ++
    [lt (const 0) (reg 3) 17 18, emit true 19, emit false 19,
     lt (const 1) (reg 3) 20 21, emit true 9, emit false 9, halt []]
  registers := 4

variable {machine D w} {S : ℕ}

private theorem bounded_regs {a b c d : ℕ} (ha : a ≤ S) (hb : b ≤ S)
    (hc : c ≤ S) (hd : d ≤ S) : ∀ r ∈ [a, b, c, d], r ≤ S := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

private theorem reachesOut_entry {u v y : ℕ}
    (hregs : ∀ r ∈ [w.length, u, v, y], r ≤ S) (h2 : 2 ≤ S) :
    let c := coinCountWithSymbol machine (radix D w.length) w.length u v
      w[queryIndex (k := k) (radix D w.length) u]?
    (coinTableProgram machine D).ReachesOut (frame w) ((coinTableProgram machine D).Active S)
      (10, [w.length, u, v, y]) (9, [w.length, u, v, c])
      [decide (0 < c), decide (1 < c)] := by
  let P := coinTableProgram machine D
  let c := coinCountWithSymbol machine (radix D w.length) w.length u v
    w[queryIndex (k := k) (radix D w.length) u]?
  have hc : c ≤ 2 := coinCountWithSymbol_le_two ..
  have hb : ∀ r ∈ [w.length, u, v, c], r ≤ S :=
    bounded_regs (hregs _ (by simp)) (hregs _ (by simp)) (hregs _ (by simp)) (hc.trans h2)
  have hcode : P.CodeAt 10 (coinCountCode machine D 10 16) := by
    simp only [coinCountCode, readSymbolCode, codeAt_append,
      codeAt_cons, codeAt_nil, and_true]
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  have hr := reachesOut_coinCountCode machine hcode hregs h2
  have hfirst : P.ReachesOut (frame w) (P.Active S)
      (16, [w.length, u, v, c]) (19, [w.length, u, v, c]) [decide (0 < c)] := by
    refine ReachesOut.lt (show P.instr 16 = _ from rfl) hb ?_
    simp only [eval_const, eval_reg, List.getD_cons_zero, List.getD_cons_succ]
    by_cases h : 0 < c
    · simpa [h] using ReachesOut.emit (show P.instr 17 = _ from rfl) hb (ReachesOut.refl _)
    · simpa [h] using ReachesOut.emit (show P.instr 18 = _ from rfl) hb (ReachesOut.refl _)
  have hsecond : P.ReachesOut (frame w) (P.Active S)
      (19, [w.length, u, v, c]) (9, [w.length, u, v, c]) [decide (1 < c)] := by
    refine ReachesOut.lt (show P.instr 19 = _ from rfl) hb ?_
    simp only [eval_const, eval_reg, List.getD_cons_zero, List.getD_cons_succ]
    by_cases h : 1 < c
    · simpa [h] using ReachesOut.emit (show P.instr 20 = _ from rfl) hb (ReachesOut.refl _)
    · simpa [h] using ReachesOut.emit (show P.instr 21 = _ from rfl) hb (ReachesOut.refl _)
  exact (hr.trans (hfirst.trans hsecond)).of_eq (by simp [c])

private theorem reachesOut_row
    (hL : w.length ≤ S) (hN : vertexBound (k := k) (radix D w.length) ≤ S) (h2 : 2 ≤ S)
    {u x y : ℕ} (hu : u < vertexBound (k := k) (radix D w.length))
    (hx : x ≤ vertexBound (k := k) (radix D w.length)) (hy : y ≤ 2) :
    ∃ y' ≤ 2, (coinTableProgram machine D).ReachesOut (frame w)
      ((coinTableProgram machine D).Active S)
      (7, [w.length, u, x, y])
      (6, [w.length, u, vertexBound (k := k) (radix D w.length), y'])
      ((List.range (vertexBound (k := k) (radix D w.length))).flatMap fun v =>
        let c := coinCountWithSymbol machine (radix D w.length) w.length u v
          w[queryIndex (k := k) (radix D w.length) u]?
        [decide (0 < c), decide (1 < c)]) := by
  have hcode : (coinTableProgram machine D).CodeAt 7
      (forCode 7 2 (vertexBoundExpr k (radixExpr D (reg 0))) 10 6) := by
    simp only [forCode, codeAt_cons, codeAt_nil, and_true]
    exact ⟨rfl, rfl, rfl⟩
  obtain ⟨regs', hreach, y', rfl, -, hy'⟩ := reachesOut_forCode (w := frame w)
    (o := fun v =>
      let c := coinCountWithSymbol machine (radix D w.length) w.length u v
        w[queryIndex (k := k) (radix D w.length) u]?
      [decide (0 < c), decide (1 < c)])
    (N := vertexBound (k := k) (radix D w.length)) hcode
    (fun v regs => ∃ y, regs = [w.length, u, v, y] ∧
      v ≤ vertexBound (k := k) (radix D w.length) ∧ y ≤ 2) hN
    (by
      rintro v regs ⟨y, rfl, hv, hy⟩
      exact ⟨rfl, by simp, by simp, bounded_regs hL (by omega) (by omega) (by omega)⟩)
    (by
      rintro v hv regs ⟨y, rfl, -, hy⟩
      let c := coinCountWithSymbol machine (radix D w.length) w.length u v
        w[queryIndex (k := k) (radix D w.length) u]?
      have hc : c ≤ 2 := coinCountWithSymbol_le_two ..
      exact ⟨[w.length, u, v, c],
        reachesOut_entry (bounded_regs hL (by omega) (by omega) (by omega)) h2,
        rfl, bounded_regs hL (by omega) (by omega) (hc.trans h2), c, by simp, by omega, hc⟩)
    [w.length, u, x, y] (bounded_regs hL (by omega) (by omega) (by omega))
    ⟨y, by simp, by omega, hy⟩
  exact ⟨y', hy', hreach⟩

private theorem reachesOut_table
    (hL : w.length ≤ S) (hN : vertexBound (k := k) (radix D w.length) ≤ S) (h2 : 2 ≤ S) :
    ∃ regs, (coinTableProgram machine D).ReachesOut (frame w)
      ((coinTableProgram machine D).Active S)
      (4, [w.length, 0, 0, 0]) (22, regs) (coinTable machine D w) ∧
      ∀ r ∈ regs, r ≤ S := by
  have hcode : (coinTableProgram machine D).CodeAt 4
      (forCode 4 1 (vertexBoundExpr k (radixExpr D (reg 0))) 7 22) := by
    simp only [forCode, codeAt_cons, codeAt_nil, and_true]
    exact ⟨rfl, rfl, rfl⟩
  obtain ⟨regs', hreach, x, y, rfl, -, hx, hy⟩ := reachesOut_forCode (w := frame w)
    (o := fun u => (List.range (vertexBound (k := k) (radix D w.length))).flatMap fun v =>
      let c := coinCountWithSymbol machine (radix D w.length) w.length u v
        w[queryIndex (k := k) (radix D w.length) u]?
      [decide (0 < c), decide (1 < c)])
    (N := vertexBound (k := k) (radix D w.length)) hcode
    (fun u regs => ∃ x y, regs = [w.length, u, x, y] ∧
      u ≤ vertexBound (k := k) (radix D w.length) ∧
      x ≤ vertexBound (k := k) (radix D w.length) ∧ y ≤ 2) hN
    (by
      rintro u regs ⟨x, y, rfl, hu, hx, hy⟩
      exact ⟨rfl, by simp, by simp, bounded_regs hL (by omega) (by omega) (by omega)⟩)
    (by
      rintro u hu regs ⟨x, y, rfl, -, hx, hy⟩
      obtain ⟨y', hy', hr⟩ := reachesOut_row (machine := machine) hL hN h2 hu hx hy
      exact ⟨_, hr, rfl, bounded_regs hL (by omega) (by omega) (by omega),
        _, y', by simp, by omega, le_rfl, hy'⟩)
    [w.length, 0, 0, 0] (bounded_regs hL (by omega) (by omega) (by omega))
    ⟨0, 0, by simp, by omega, by omega, by omega⟩
  exact ⟨_, hreach.of_eq (coinTable_eq_flatMap machine D w).symm,
    bounded_regs hL (by omega) (by omega) (by omega)⟩

variable (machine D w)

/-- The actual zero-initialized program counts the input length, enumerates every compact pair,
emits the whole table, and reaches its halt with all final registers within the common bound. -/
theorem reachesOut_coinTableProgram
    (hinput : (frame w).length ≤ S)
    (hN : vertexBound (k := k) (radix D w.length) ≤ S) (h2 : 2 ≤ S) :
    ∃ regs, (coinTableProgram machine D).ReachesOut (frame w)
      ((coinTableProgram machine D).Active S) (coinTableProgram machine D).init
      (22, regs) (coinTable machine D w) ∧ ∀ r ∈ regs, r ≤ S := by
  have hcode : (coinTableProgram machine D).CodeAt 0 Words.headerCode := by
    simp only [Words.headerCode, codeAt_cons, codeAt_nil, and_true]
    exact ⟨rfl, rfl, rfl, rfl⟩
  have hh := Words.reachesOut_header (w := w) (k := 0) hcode (by
    simpa only [length_frame, Nat.add_zero] using hinput)
  simp only [List.replicate_zero, List.append_nil] at hh
  have hL : w.length ≤ S := by rw [length_frame] at hinput; omega
  obtain ⟨regs, hr, hregs⟩ := reachesOut_table (machine := machine) hL hN h2
  exact ⟨regs, (hh.trans hr).of_eq (by simp), hregs⟩

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
