/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.ReadSymbol
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Words
public import Complexity.Foundations.Data.List.TwoBitTable

/-!
# Initialized two-bit table writers with original-input queries

One four-register counter program reads the original word length, enumerates a square table,
reads one original input symbol per entry and emits the two threshold bits of an arithmetic count.
The bound, query and count are expressions; the header, loops, reader and emitter are shared.
This is the existing ordinary fair-coin table program factored for its clocked client.

Registers zero through three hold the word length, row, column and scratch. The input must be
`frame w`; the program starts from its actual zeroed initializer. The expression contracts below
are discharged by each client, including the requirement that the count be at most two.

## Main definitions

* `Turing.MultiTapeNTM.ConfigurationGraph.inputCountTableProgram`: the shared initialized writer.

## Main results

* `Turing.MultiTapeNTM.ConfigurationGraph.reachesOut_inputCountTableProgram`: bounded initialized
  execution emits exactly the shared row-major `List.twoBitTable` representation.
-/

public section

namespace Turing.MultiTapeNTM.ConfigurationGraph

open CounterProgram Instr Expr MultiTapeTM

/-- The header occupies labels zero to three, loops start at four and seven, the input read at
ten, and count assignment at fifteen. Labels sixteen through twenty-one emit its two bits;
twenty-two halts. Registers hold length, row, column and symbol/count scratch. -/
@[expose] def inputCountTableProgram (bound query value : Expr) : CounterProgram where
  code :=
    Words.headerCode ++ forCode 4 1 bound 7 22 ++ forCode 7 2 bound 10 6 ++
    readSymbolCode 10 3 15 (reg 0) query ++ [assign 3 value 16] ++
    [lt (const 0) (reg 3) 17 18, emit true 19, emit false 19,
     lt (const 1) (reg 3) 20 21, emit true 9, emit false 9, halt []]
  registers := 4

variable {bound query value : Expr} {w : List Bool} {N S : ℕ} {count : ℕ → ℕ → ℕ}
  (hbound : ∀ u v y, bound.eval [w.length, u, v, y] = N)
  (hvalue : ∀ u v y,
    value.eval [w.length, u, v, symbolCode w[query.eval [w.length, u, v, y]]?] = count u v)
  (hcount : ∀ u v, count u v ≤ 2)

private theorem bounded_regs {a b c d : ℕ} (ha : a ≤ S) (hb : b ≤ S)
    (hc : c ≤ S) (hd : d ≤ S) : ∀ r ∈ [a, b, c, d], r ≤ S := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

include hvalue in
private theorem reachesOut_count {u v y : ℕ}
    (hregs : ∀ r ∈ [w.length, u, v, y], r ≤ S) (h2 : 2 ≤ S) :
    (inputCountTableProgram bound query value).ReachesOut (frame w)
      ((inputCountTableProgram bound query value).Active S)
      (10, [w.length, u, v, y]) (16, [w.length, u, v, count u v]) [] := by
  let P := inputCountTableProgram bound query value
  let sym := symbolCode w[query.eval [w.length, u, v, y]]?
  have hcode : P.CodeAt 10 (readSymbolCode 10 3 15 (reg 0) query) := by
    simp only [readSymbolCode, codeAt_cons, codeAt_nil, and_true]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hr : P.ReachesOut (frame w) (P.Active S)
      (10, [w.length, u, v, y]) (15, [w.length, u, v, sym]) [] := by
    simpa [sym] using reachesOut_readSymbolCode hcode rfl hregs
  have hb : ∀ r ∈ [w.length, u, v, sym], r ≤ S :=
    bounded_regs (hregs _ (by simp)) (hregs _ (by simp)) (hregs _ (by simp))
      ((Nat.le_of_lt_succ (symbolCode_lt _)).trans h2)
  refine (hr.trans (ReachesOut.assign (show P.instr 15 = _ from rfl) hb ?_)).of_eq rfl
  rw [hvalue]
  exact ReachesOut.refl _

include hvalue hcount in
private theorem reachesOut_entry {u v y : ℕ}
    (hregs : ∀ r ∈ [w.length, u, v, y], r ≤ S) (h2 : 2 ≤ S) :
    (inputCountTableProgram bound query value).ReachesOut (frame w)
      ((inputCountTableProgram bound query value).Active S)
      (10, [w.length, u, v, y]) (9, [w.length, u, v, count u v])
      [decide (0 < count u v), decide (1 < count u v)] := by
  let P := inputCountTableProgram bound query value
  let c := count u v
  have hb : ∀ r ∈ [w.length, u, v, c], r ≤ S :=
    bounded_regs (hregs _ (by simp)) (hregs _ (by simp)) (hregs _ (by simp))
      ((hcount u v).trans h2)
  have hr := reachesOut_count (bound := bound) hvalue hregs h2
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

include hbound hvalue hcount in
private theorem reachesOut_row (hL : w.length ≤ S) (hN : N ≤ S) (h2 : 2 ≤ S)
    {u x y : ℕ} (hu : u < N) (hx : x ≤ N) (hy : y ≤ 2) :
    ∃ y' ≤ 2, (inputCountTableProgram bound query value).ReachesOut (frame w)
      ((inputCountTableProgram bound query value).Active S)
      (7, [w.length, u, x, y]) (6, [w.length, u, N, y'])
      ((List.range N).flatMap fun v => [decide (0 < count u v), decide (1 < count u v)]) := by
  have hcode : (inputCountTableProgram bound query value).CodeAt 7
      (forCode 7 2 bound 10 6) := by
    simp only [forCode, codeAt_cons, codeAt_nil, and_true]
    exact ⟨rfl, rfl, rfl⟩
  obtain ⟨regs', hreach, y', rfl, -, hy'⟩ := reachesOut_forCode (w := frame w)
    (o := fun v => [decide (0 < count u v), decide (1 < count u v)]) (N := N) hcode
    (fun v regs => ∃ y, regs = [w.length, u, v, y] ∧ v ≤ N ∧ y ≤ 2) hN
    (by
      rintro v regs ⟨y, rfl, hv, hy⟩
      exact ⟨rfl, hbound u v y, by simp, bounded_regs hL (by omega) (by omega) (by omega)⟩)
    (by
      rintro v hv regs ⟨y, rfl, -, hy⟩
      have hc := hcount u v
      exact ⟨[w.length, u, v, count u v],
        reachesOut_entry hvalue hcount
          (bounded_regs hL (by omega) (by omega) (by omega)) h2,
        rfl, bounded_regs hL (by omega) (by omega) (hc.trans h2),
        count u v, by simp, by omega, hc⟩)
    [w.length, u, x, y] (bounded_regs hL (by omega) (by omega) (by omega))
    ⟨y, by simp, by omega, hy⟩
  exact ⟨y', hy', hreach⟩

include hbound hvalue hcount in
private theorem reachesOut_table (hL : w.length ≤ S) (hN : N ≤ S) (h2 : 2 ≤ S) :
    ∃ regs, (inputCountTableProgram bound query value).ReachesOut (frame w)
      ((inputCountTableProgram bound query value).Active S)
      (4, [w.length, 0, 0, 0]) (22, regs) (List.twoBitTable N count) ∧
      ∀ r ∈ regs, r ≤ S := by
  have hcode : (inputCountTableProgram bound query value).CodeAt 4
      (forCode 4 1 bound 7 22) := by
    simp only [forCode, codeAt_cons, codeAt_nil, and_true]
    exact ⟨rfl, rfl, rfl⟩
  obtain ⟨regs', hreach, x, y, rfl, -, hx, hy⟩ := reachesOut_forCode (w := frame w)
    (o := fun u => (List.range N).flatMap fun v =>
      [decide (0 < count u v), decide (1 < count u v)]) (N := N) hcode
    (fun u regs => ∃ x y, regs = [w.length, u, x, y] ∧ u ≤ N ∧ x ≤ N ∧ y ≤ 2) hN
    (by
      rintro u regs ⟨x, y, rfl, hu, hx, hy⟩
      exact ⟨rfl, hbound u x y, by simp, bounded_regs hL (by omega) (by omega) (by omega)⟩)
    (by
      rintro u hu regs ⟨x, y, rfl, -, hx, hy⟩
      obtain ⟨y', hy', hr⟩ := reachesOut_row hbound hvalue hcount hL hN h2 hu hx hy
      exact ⟨_, hr, rfl, bounded_regs hL (by omega) (by omega) (by omega),
        _, y', by simp, by omega, le_rfl, hy'⟩)
    [w.length, 0, 0, 0] (bounded_regs hL (by omega) (by omega) (by omega))
    ⟨0, 0, by simp, by omega, by omega, by omega⟩
  exact ⟨_, hreach.of_eq (List.twoBitTable_eq_flatMap N count).symm,
    bounded_regs hL (by omega) (by omega) (by omega)⟩

include hbound hvalue hcount in
/-- Starting from zero registers on the original framed word, the shared writer emits exactly
the specified two-bit count table and reaches its halt. The three expression contracts state
that the bound is fixed by the input length and that each actual read produces the intended
count at most two. All registers stay within the supplied common bound before halting. -/
theorem reachesOut_inputCountTableProgram
    (hinput : (frame w).length ≤ S) (hN : N ≤ S) (h2 : 2 ≤ S) :
    ∃ regs, (inputCountTableProgram bound query value).ReachesOut (frame w)
      ((inputCountTableProgram bound query value).Active S)
      (inputCountTableProgram bound query value).init
      (22, regs) (List.twoBitTable N count) ∧ ∀ r ∈ regs, r ≤ S := by
  have hcode : (inputCountTableProgram bound query value).CodeAt 0 Words.headerCode := by
    simp only [Words.headerCode, codeAt_cons, codeAt_nil, and_true]
    exact ⟨rfl, rfl, rfl, rfl⟩
  have hh := Words.reachesOut_header (w := w) (k := 0) hcode (by
    simpa only [length_frame, Nat.add_zero] using hinput)
  simp only [List.replicate_zero, List.append_nil] at hh
  have hL : w.length ≤ S := by rw [length_frame] at hinput; omega
  obtain ⟨regs, hr, hregs⟩ := reachesOut_table hbound hvalue hcount hL hN h2
  exact ⟨regs, (hh.trans hr).of_eq (by simp), hregs⟩

end Turing.MultiTapeNTM.ConfigurationGraph
