/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.FairCoin
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Expr
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.ReadSymbol

/-!
# A fair-coin count block reading the original input

The six-instruction `coinCountCode` reads the one original input symbol requested by a compact
source ID, then evaluates both fixed-coin edges and adds their multiplicities. It uses four
registers: the original word length, source ID, target ID, and one scratch register. The scratch
register first holds the symbol code and then the count, which is zero, one, or two.

`reachesOut_coinCountCode` proves execution on the actual framed input. The other registers do
not change, no output is emitted, and every intermediate register is bounded by any common bound
for the initial registers and two. Invalid compact IDs retain the existing guarded behavior.

The concrete `coinCountProgram` places this block at label zero and a halt at label six. Its
query and execution callbacks have native linear-space certificates in the binary register-state
encoding. The execution theorem starts with the length and IDs already in registers; it does not
parse those parameters or enumerate a matrix. Connecting an ambient enumeration, paired ports,
and the time-layered matrix remains separate from this input-reading component.

## Main definitions

* `Turing.MultiTapePTM.ConfigurationGraph.coinCountExpr`: arithmetic counting both coin edges.
* `Turing.MultiTapePTM.ConfigurationGraph.coinCountCode`: the placed input-reading count block.
* `Turing.MultiTapePTM.ConfigurationGraph.coinCountProgram`: the concrete four-register program.

## Main results

* `Turing.MultiTapePTM.ConfigurationGraph.reachesOut_coinCountCode`: bounded execution from the
  actual framed input, yielding the exact compact transition count.
* `Turing.MultiTapePTM.ConfigurationGraph.reachesOut_coinCountProgram`: the concrete program run.
* `Turing.MultiTapePTM.ConfigurationGraph.coinCountProgram_query_inSpace`,
  `Turing.MultiTapePTM.ConfigurationGraph.coinCountProgram_exec_inSpace`: native space certificates
  for the actual query and register-update routines.
-/

public section

namespace Turing.MultiTapePTM.ConfigurationGraph

open MultiTapeNTM.ConfigurationGraph CounterProgram Instr Expr MultiTapeTM
open Cslib.Turing

variable {k : ℕ} {State : Type} [Fintype State]

/-- Add the two fixed-coin arithmetic edge tests, retaining multiplicity when the successors
coincide. The symbol expression contains the ternary code used by `readSymbolCode`. -/
noncomputable def coinCountExpr (machine : MultiTapePTM k Bool State)
    (B n u v sym : Expr) : Expr :=
  add (edgeExpr (machine.withCoin false).toTM.toMultiTapeNTM B n u v sym)
    (edgeExpr (machine.withCoin true).toTM.toMultiTapeNTM B n u v sym)

/-- The count expression computes the existing compact fair-coin transition count. -/
theorem eval_coinCountExpr (machine : MultiTapePTM k Bool State)
    {B n u v sym : Expr} {regs : List ℕ} {symbol : Option Bool}
    (hs : sym.eval regs = symbolCode symbol) :
    (coinCountExpr machine B n u v sym).eval regs =
      coinCountWithSymbol machine (B.eval regs) (n.eval regs) (u.eval regs) (v.eval regs)
        symbol := by
  rw [coinCountExpr, eval_add, eval_edgeExpr _ hs, eval_edgeExpr _ hs]
  rfl

/-- Read from `frame w` and store the coin count in register three, then continue at `exit`.
Registers zero through two hold `w.length`, the source ID, and the target ID. The radix is
`(w.length + 2) ^ D`; the six instructions start at `b`. -/
@[expose] noncomputable def coinCountCode (machine : MultiTapePTM k Bool State)
    (D b exit : ℕ) : List Instr :=
  readSymbolCode b 3 (b + 5) (reg 0) (queryIndexExpr k (radixExpr D (reg 0)) (reg 1)) ++
    [assign 3 (coinCountExpr machine (radixExpr D (reg 0))
      (reg 0) (reg 1) (reg 2) (reg 3)) exit]

/-- The reader and the arithmetic assignment occupy six consecutive labels. -/
@[simp] theorem length_coinCountCode (machine : MultiTapePTM k Bool State) (D b exit : ℕ) :
    (coinCountCode machine D b exit).length = 6 := rfl

/-- The actual block reads the original input and returns its exact fair-coin edge multiplicity.
All pre-exit register states satisfy the supplied common bound. No valid-ID or reachable-view
premise is needed: the existing compact edge predicates also define the invalid-ID cases. -/
theorem reachesOut_coinCountCode (machine : MultiTapePTM k Bool State)
    {P : CounterProgram} {D b exit S u v y : ℕ} {w : List Bool}
    (hcode : P.CodeAt b (coinCountCode machine D b exit))
    (hS : ∀ r ∈ [w.length, u, v, y], r ≤ S) (h2 : 2 ≤ S) :
    P.ReachesOut (frame w) (P.Active S) (b, [w.length, u, v, y])
      (exit, [w.length, u, v, coinCountWithSymbol machine (radix D w.length) w.length u v
        w[queryIndex (k := k) (radix D w.length) u]?]) [] := by
  simp only [coinCountCode, codeAt_append, length_readSymbolCode, codeAt_cons] at hcode
  obtain ⟨hread, hassign, -⟩ := hcode
  let symbol := w[queryIndex (k := k) (radix D w.length) u]?
  have hr : P.ReachesOut (frame w) (P.Active S) (b, [w.length, u, v, y])
      (b + 5, [w.length, u, v, symbolCode symbol]) [] := by
    simpa [symbol] using reachesOut_readSymbolCode (w := w) hread (by simp) hS
  have hbound : ∀ r ∈ [w.length, u, v, symbolCode symbol], r ≤ S := by
    intro r hr
    have hm : r ∈ [w.length, u, v, y].set 3 (symbolCode symbol) := hr
    rcases List.mem_or_eq_of_mem_set hm with hm | rfl
    · exact hS r hm
    · exact (Nat.le_of_lt_succ (symbolCode_lt symbol)).trans h2
  have heval :
      (coinCountExpr machine (radixExpr D (reg 0)) (reg 0) (reg 1) (reg 2) (reg 3)).eval
        [w.length, u, v, symbolCode symbol] =
      coinCountWithSymbol machine (radix D w.length) w.length u v symbol := by
    simpa using eval_coinCountExpr machine (symbol := symbol)
      (B := radixExpr D (reg 0)) (n := reg 0) (u := reg 1) (v := reg 2) (sym := reg 3)
      (regs := [w.length, u, v, symbolCode symbol]) rfl
  refine (hr.trans (ReachesOut.assign hassign hbound ?_)).of_eq rfl
  rw [heval]
  exact ReachesOut.refl _

/-- The count block followed by a halt. The caller supplies the original input length and the
two compact IDs in registers zero through two before entering the block. -/
@[expose] noncomputable def coinCountProgram (machine : MultiTapePTM k Bool State)
    (D : ℕ) : CounterProgram where
  code := coinCountCode machine D 0 6 ++ [halt []]
  registers := 4

/-- The concrete program reaches its halt label, returning the count in register three and
emitting nothing. The initial register values are explicit; they are not the zeroed program
initializer. -/
theorem reachesOut_coinCountProgram (machine : MultiTapePTM k Bool State)
    {D S u v y : ℕ} {w : List Bool}
    (hS : ∀ r ∈ [w.length, u, v, y], r ≤ S) (h2 : 2 ≤ S) :
    (coinCountProgram machine D).ReachesOut (frame w) ((coinCountProgram machine D).Active S)
      (0, [w.length, u, v, y])
      (6, [w.length, u, v, coinCountWithSymbol machine (radix D w.length) w.length u v
        w[queryIndex (k := k) (radix D w.length) u]?]) [] :=
  reachesOut_coinCountCode machine
    (codeAt_of_code_eq (pre := []) (post := [halt []]) rfl) hS h2

/-- The concrete reader's query-index routine has a native linear-space certificate in its
binary label-and-register encoding, rather than the length of the original input word. -/
theorem coinCountProgram_query_inSpace (machine : MultiTapePTM k Bool State) (D : ℕ) :
    ComputableInSpace (coinCountProgram machine D).query Simulation.encConfig encNat
      (fun s => (Simulation.encConfig s).length) :=
  (Simulation.query_inSpace (P := coinCountProgram machine D)).computableInSpace

/-- The concrete reader's register-update routine has a native linear-space certificate in the
binary register state together with the one optional input bit returned by the native query. -/
theorem coinCountProgram_exec_inSpace (machine : MultiTapePTM k Bool State) (D : ℕ) :
    ComputableInSpace
      (fun p : Config × Option Bool => (coinCountProgram machine D).exec p.1 p.2)
      Simulation.encConfigRead Simulation.encConfig
      (fun p => (Simulation.encConfigRead p).length) :=
  (Simulation.exec_inSpace (P := coinCountProgram machine D)).computableInSpace

end Turing.MultiTapePTM.ConfigurationGraph
