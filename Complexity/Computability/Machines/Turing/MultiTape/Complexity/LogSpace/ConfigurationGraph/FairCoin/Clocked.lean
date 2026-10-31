/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.FairCoin.ReadInput
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.CounterBounds

/-!
# Local arithmetic for clocked compact configurations

A clocked identifier is `clock * N + baseID`, with `N = vertexBound B`. Division and remainder
recover the clock and base ID. A transition has the existing fair-coin count exactly when the
target clock is the next one; every other count is zero. The polynomial horizon and terminal
acceptance test also have native space-budget certificates on their short binary arguments.

The start at clock zero retains its ordinary numeric ID, so the existing `startID_budget`
applies unchanged. These local certificates do not serialize a complete matrix-instance header,
reward vector or start field. The initialized matrix payload is supplied by `ClockedTable`.

## Main definitions

* `Turing.MultiTapeNTM.ConfigurationGraph.clockedVertexBound`: the polynomial clocked box size.
* `Turing.MultiTapeNTM.ConfigurationGraph.clockedAccept`: the terminal accepting-ID test.
* `Turing.MultiTapePTM.ConfigurationGraph.clockedCoinCountWithSymbol`: the guarded clocked count.
* `Turing.MultiTapePTM.ConfigurationGraph.clockedCoinCountExpr`: its arithmetic expression.

## Main results

* `Turing.MultiTapeNTM.ConfigurationGraph.clockedVertexBound_budget`,
  `Turing.MultiTapeNTM.ConfigurationGraph.clockedAccept_budget`: local native space certificates.
* `Turing.MultiTapePTM.ConfigurationGraph.clockedCoinCountWithSymbol_le_two`: count bound.
* `Turing.MultiTapePTM.ConfigurationGraph.eval_clockedCoinCountExpr`: exact expression evaluation.
-/

public section

namespace Turing.MultiTapeNTM.ConfigurationGraph

open CounterProgram Expr MultiTapeTM ComputableInSpace

variable {k : ℕ}

/-- Number of compact clock/base pairs at the standard polynomial horizon. -/
@[expose] def clockedVertexBound (D d n : ℕ) : ℕ :=
  (2 * (2 * (n + 1)) ^ d + 1) * vertexBound (k := k) (radix D n)

/-- The dimension as a counter expression in the original word length. -/
noncomputable def clockedVertexBoundExpr (k D d : ℕ) (n : Expr) : Expr :=
  mul (add (mul (const 2) (pow (mul (const 2) (add n (const 1))) d)) (const 1))
    (vertexBoundExpr k (radixExpr D n))

/-- The dimension expression has exactly the polynomial clocked-box value. -/
@[simp] theorem eval_clockedVertexBoundExpr (k D d : ℕ) (n : Expr) (regs : List ℕ) :
    (clockedVertexBoundExpr k D d n).eval regs = clockedVertexBound (k := k) D d (n.eval regs) := by
  simp [clockedVertexBoundExpr, clockedVertexBound]

/-- The last layer pays the accepting-halt indicator of the base compact ID. -/
@[expose] noncomputable def clockedAccept {State : Type} [Fintype State] (B n T u : ℕ) : Bool :=
  if u / vertexBound (k := k) B = T then
    bad (k := k) (State := State) B n (u % vertexBound (k := k) B) else false

variable {α : Type} {enc : α ↪ List Bool} {S : α → ℕ} {B n T u : α → ℕ}

/-- Computing the clocked dimension preserves any common native space budget for the input
length. The exponents are fixed with the source machine. -/
theorem clockedVertexBound_budget (D d : ℕ) (hn : ComputableInSpace n enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => clockedVertexBound (k := k) D d (n a)) enc encNat S := by
  have htwo : ComputableInSpace (fun _ : α => 2) enc encNat S := budget_const 2 hin
  exact budget_natMul
    (budget_natSucc (budget_natMul htwo
      (budget_natPow (budget_natMul htwo (budget_natSucc hn)) hin d)))
    (vertexBound_budget (k := k) (budget_natPow (budget_natAdd hn htwo) hin D) hin)

/-- The terminal reward test preserves the native space budget of its binary arguments. -/
theorem clockedAccept_budget {State : Type} [Fintype State]
    (hB : ComputableInSpace B enc encNat S) (hn : ComputableInSpace n enc encNat S)
    (hT : ComputableInSpace T enc encNat S) (hu : ComputableInSpace u enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => clockedAccept (k := k) (State := State)
      (B a) (n a) (T a) (u a)) enc encBool S := by
  have hN := vertexBound_budget (k := k) hB hin
  simpa only [clockedAccept, decide_eq_true_eq] using
    budget_ite (budget_natEq (budget_natDiv hu hN) hT)
      (bad_budget (State := State) hB hn (budget_natMod hu hN) hin) (budget_const false hin)

end Turing.MultiTapeNTM.ConfigurationGraph

namespace Turing.MultiTapePTM.ConfigurationGraph

open MultiTapeNTM.ConfigurationGraph CounterProgram Expr MultiTapeTM ComputableInSpace

variable {k : ℕ} {State : Type} [Fintype State]

/-- The ordinary base-ID coin count on a next-clock pair, and zero otherwise. No represented
view premise is required; the base-ID predicates still guard invalid configurations. -/
@[expose] noncomputable def clockedCoinCountWithSymbol (machine : MultiTapePTM k Bool State)
    (B n u v : ℕ) (symbol : Option Bool) : ℕ :=
  let N := vertexBound (k := k) B
  if u / N + 1 = v / N then coinCountWithSymbol machine B n (u % N) (v % N) symbol else 0

/-- Clock gating preserves the exact zero/one/two range of a fair-coin count. -/
theorem clockedCoinCountWithSymbol_le_two (machine : MultiTapePTM k Bool State)
    (B n u v : ℕ) (symbol : Option Bool) :
    clockedCoinCountWithSymbol machine B n u v symbol ≤ 2 := by
  dsimp only [clockedCoinCountWithSymbol]
  split_ifs
  · exact coinCountWithSymbol_le_two ..
  · decide

/-- Every terminal row has zero count at every bounded clocked target, regardless of validity
or reachability of either base configuration. -/
theorem clockedCoinCountWithSymbol_terminal (machine : MultiTapePTM k Bool State)
    {B n T : ℕ} (u v : Fin ((T + 1) * vertexBound (k := k) B))
    (hu : u.val / vertexBound (k := k) B = T) (symbol : Option Bool) :
    clockedCoinCountWithSymbol machine B n u v symbol = 0 := by
  have hv : v.val / vertexBound (k := k) B < T + 1 := v.divNat.isLt
  dsimp only [clockedCoinCountWithSymbol]
  rw [hu, ite_eq_right (by omega)]

/-- Clock division, base remainders and the same coin-count expression form one arithmetic
expression. The symbol is still read separately from the original input at the base source. -/
noncomputable def clockedCoinCountExpr (machine : MultiTapePTM k Bool State)
    (B n u v sym : Expr) : Expr :=
  let N := vertexBoundExpr k B
  iteB (eqB (add (div u N) (const 1)) (div v N))
    (coinCountExpr machine B n (mod u N) (mod v N) sym) (const 0)

/-- The clocked expression is exactly the guarded count, including off-clock pairs. -/
theorem eval_clockedCoinCountExpr (machine : MultiTapePTM k Bool State)
    {B n u v sym : Expr} {regs : List ℕ} {symbol : Option Bool}
    (hs : sym.eval regs = symbolCode symbol) :
    (clockedCoinCountExpr machine B n u v sym).eval regs =
      clockedCoinCountWithSymbol machine (B.eval regs) (n.eval regs) (u.eval regs) (v.eval regs)
        symbol := by
  rw [clockedCoinCountExpr, eval_iteB eval_eqB, eval_coinCountExpr machine hs]
  simp only [eval_add, eval_div, eval_const, eval_vertexBoundExpr, eval_mod,
    decide_eq_true_eq, clockedCoinCountWithSymbol]

variable {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
  {B n u v : α → ℕ} {symbol : α → Option Bool}

/-- The local clocked count has the same native space-budget contract as its base count. -/
theorem clockedCoinCountWithSymbol_budget (machine : MultiTapePTM k Bool State)
    (hB : ComputableInSpace B enc encNat S) (hn : ComputableInSpace n enc encNat S)
    (hu : ComputableInSpace u enc encNat S) (hv : ComputableInSpace v enc encNat S)
    (hs : ComputableInSpace symbol enc (encOption encBool) S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => clockedCoinCountWithSymbol machine
      (B a) (n a) (u a) (v a) (symbol a)) enc encNat S := by
  have hN := vertexBound_budget (k := k) hB hin
  simpa only [clockedCoinCountWithSymbol, decide_eq_true_eq] using
    budget_ite (budget_natEq (budget_natSucc (budget_natDiv hu hN)) (budget_natDiv hv hN))
      (coinCountWithSymbol_budget machine hB hn (budget_natMod hu hN)
        (budget_natMod hv hN) hs hin) (budget_const 0 hin)

end Turing.MultiTapePTM.ConfigurationGraph
