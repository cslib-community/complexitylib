/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Tape
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Output
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Frame

/-!
# Reading a configuration graph's input symbol

`readSymbolCode` is the five-instruction block used by the STCON reduction to obtain the ternary
code of one original input bit. It checks the query against the stored input length, reads position
`2 * query + 1` of the framed input when in range, and stores zero otherwise. The block changes only
its destination register and emits no output.

The query is a zero-based position in the original word. Configuration-head boundary conventions
are handled separately by the compact graph's edge test: this block returns the actual optional
word symbol, not the symbol after that boundary correction.

## Main definitions

* `Turing.MultiTapeNTM.ConfigurationGraph.readSymbolCode`: the relocatable input-reading block.

## Main results

* `Turing.MultiTapeNTM.ConfigurationGraph.reachesOut_readSymbolCode`: the actual block reads
  `w[query]?` from `frame w`, preserving the bound on every pre-exit register state.
-/

public section

namespace Turing.MultiTapeNTM.ConfigurationGraph

open CounterProgram Instr Expr MultiTapeTM

/-- Read one original input symbol from a framed word into `dst`, then continue at `exit`.
The five instructions start at `b`; `len` is the original word length and `query` its zero-based
index. The result is `symbolCode`: zero for no symbol, one for false, and two for true. -/
@[expose] def readSymbolCode (b dst exit : ℕ) (len query : Expr) : List Instr :=
  [lt query len (b + 1) (b + 4),
   read (add (mul (const 2) query) (const 1)) (b + 2) (b + 3) (b + 3),
   assign dst (const 2) exit,
   assign dst (const 1) exit,
   assign dst (const 0) exit]

/-- The reader occupies five consecutive instruction labels. -/
@[simp] theorem length_readSymbolCode (b dst exit : ℕ) (len query : Expr) :
    (readSymbolCode b dst exit len query).length = 5 := rfl

/-- The placed block reads the original word's optional symbol, changes only `dst`, and emits
nothing. All states before the exit have the original registers, so their bound needs no extra
assumption. The final destination is at most two by `symbolCode_lt`. -/
theorem reachesOut_readSymbolCode {P : CounterProgram} {b dst exit S : ℕ}
    {len query : Expr} {regs : List ℕ} {w : List Bool}
    (hcode : P.CodeAt b (readSymbolCode b dst exit len query))
    (hlen : len.eval regs = w.length) (hS : ∀ r ∈ regs, r ≤ S) :
    P.ReachesOut (frame w) (P.Active S) (b, regs)
      (exit, regs.set dst (symbolCode w[query.eval regs]?)) [] := by
  simp only [readSymbolCode, codeAt_cons] at hcode
  obtain ⟨h₀, h₁, h₂, h₃, h₄, -⟩ := hcode
  simp only [Nat.add_assoc] at h₂ h₃ h₄
  refine ReachesOut.lt h₀ hS ?_
  rw [hlen]
  by_cases hq : query.eval regs < w.length
  · obtain ⟨bit, hb⟩ : ∃ bit, w[query.eval regs]? = some bit :=
      ⟨w[query.eval regs], List.getElem?_eq_getElem hq⟩
    rw [ite_eq_left hq, hb]
    refine ReachesOut.read h₁ hS ?_
    simp only [eval_add, eval_mul, eval_const, getElem?_frame_two_mul_add_one hq, hb]
    cases bit
    · refine ReachesOut.assign h₃ hS ?_
      simpa only [eval_const, symbolCode] using ReachesOut.refl _
    · refine ReachesOut.assign h₂ hS ?_
      simpa only [eval_const, symbolCode] using ReachesOut.refl _
  · rw [ite_eq_right hq, List.getElem?_eq_none (by omega)]
    refine ReachesOut.assign h₄ hS ?_
    simpa only [eval_const, symbolCode] using ReachesOut.refl _

end Turing.MultiTapeNTM.ConfigurationGraph
