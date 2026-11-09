/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Boolean

/-!
# The compact configuration graph as counter-program expressions

The local functions of the compact configuration graph
(`Turing.MultiTapeNTM.ConfigurationGraph`) are arithmetic in the input length, the vertex
identifiers and the one requested input symbol: radix digits are quotients and remainders, the
tape registers are ternary stacks, and the transition table is a fixed finite list. So each of them
is an expression of a counter program (`Turing.CounterProgram.Expr`), with Boolean values
represented by `0` and `1` and the input symbol by its ternary code `symbolCode`. This is how a
counter program computes the configuration graph of a fixed machine on its input, as the
logarithmic-space reduction to directed connectivity requires [Sipser, Theorem 8.25][Sipser2013].
The radix is itself an expression, such as `Turing.MultiTapeNTM.ConfigurationGraph.radixExpr`.

## Main definitions

* `Turing.MultiTapeNTM.ConfigurationGraph.vertexBoundExpr`,
  `Turing.MultiTapeNTM.ConfigurationGraph.startIDExpr`,
  `Turing.MultiTapeNTM.ConfigurationGraph.queryIndexExpr`,
  `Turing.MultiTapeNTM.ConfigurationGraph.edgeExpr`,
  `Turing.MultiTapeNTM.ConfigurationGraph.badExpr`: the expressions.

## Main results

* `Turing.MultiTapeNTM.ConfigurationGraph.eval_vertexBoundExpr`,
  `Turing.MultiTapeNTM.ConfigurationGraph.eval_startIDExpr`,
  `Turing.MultiTapeNTM.ConfigurationGraph.eval_queryIndexExpr`,
  `Turing.MultiTapeNTM.ConfigurationGraph.eval_edgeExpr`,
  `Turing.MultiTapeNTM.ConfigurationGraph.eval_badExpr`: their values.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.25][Sipser2013]
-/

@[expose] public section

namespace Turing.MultiTapeNTM.ConfigurationGraph

open CounterProgram Expr

variable {k : ℕ} {State : Type} [Fintype State] {regs : List ℕ} {D : ℕ} {B n u v sym : Expr}

/-- The radix `(n + 2) ^ D`. -/
def radixExpr (D : ℕ) (n : Expr) : Expr := pow (add n (const 2)) D

@[simp]
theorem eval_radixExpr : (radixExpr D n).eval regs = radix D (n.eval regs) := by
  simp [radixExpr, radix]

variable (k) in
/-- The number of vertices of the ambient graph. -/
noncomputable def vertexBoundExpr (B : Expr) : Expr :=
  pow B (Fintype.card (Register k))

@[simp]
theorem eval_vertexBoundExpr :
    (vertexBoundExpr k B).eval regs = vertexBound (k := k) (B.eval regs) := by
  simp [vertexBoundExpr, vertexBound]

/-- A register of a vertex. -/
noncomputable def readRegistersExpr (B u : Expr) (i : Register k) : Expr :=
  mod (div u (pow B (Fintype.equivFin (Register k) i))) B

@[simp]
theorem eval_readRegistersExpr (i : Register k) :
    (readRegistersExpr B u i).eval regs =
      readRegisters (k := k) (B.eval regs) (u.eval regs) i := by
  simp [readRegistersExpr, readRegisters, Cslib.Radix.component, Cslib.Radix.digit_eq_div_pow_mod]

/-- Pack registers in the radix `B`. -/
noncomputable def packExpr (B : Expr) (f : Register k → Expr) : Expr :=
  ofDigits B (List.ofFn fun j => f ((Fintype.equivFin (Register k)).symm j))

theorem eval_packExpr {B : Expr} {f : Register k → Expr} {g : Register k → ℕ}
    (hf : ∀ i, (f i).eval regs = g i) :
    (packExpr B f).eval regs = Cslib.Radix.pack (B.eval regs) g := by
  simp [packExpr, Cslib.Radix.pack, List.map_ofFn, Function.comp_def, hf]

variable (k State) in
/-- Syntactic validity of a vertex. -/
noncomputable def validExpr (B n u : Expr) : Expr :=
  andB (andB (andB (andB (ltB u (vertexBoundExpr k B))
    (ltB (readRegistersExpr (k := k) B u .inputPos) (add n (const 2))))
    (ltB (readRegistersExpr (k := k) B u .control) (const (Fintype.card (Option State)))))
    (ltB (readRegistersExpr (k := k) B u .output) (const 3)))
    (allB (List.ofFn fun i : Fin k => ltB (readRegistersExpr (k := k) B u (.head i)) (const 3)))

@[simp]
theorem eval_validExpr :
    (validExpr k State B n u).eval regs =
      (valid (k := k) (State := State) (B.eval regs) (n.eval regs) (u.eval regs)).toNat := by
  rw [validExpr, eval_andB (eval_andB (eval_andB (eval_andB eval_ltB eval_ltB) eval_ltB) eval_ltB)
    (eval_allB_ofFn _ _ fun i => eval_ltB)]
  simp [valid]

/-- The code of the input symbol seen at the input position `p`, blank at the boundaries. -/
def inputSymbolExpr (n p sym : Expr) : Expr :=
  iteB (orB (eqB p (const 0)) (eqB p (add n (const 1)))) (const 0) sym

theorem eval_inputSymbolExpr {p : Expr} {symbol : Option Bool}
    (hs : sym.eval regs = symbolCode symbol) :
    (inputSymbolExpr n p sym).eval regs =
      symbolCode (inputSymbol (n.eval regs) (p.eval regs) symbol) := by
  rw [inputSymbolExpr, eval_iteB (eval_orB eval_eqB eval_eqB), inputSymbol]
  by_cases h : p.eval regs = 0 ∨ p.eval regs = n.eval regs + 1
  · rcases h with h | h <;> simp [h, symbolCode]
  · push Not at h
    simp [h.1, h.2, hs]

/-- The test that a vertex observes a fixed entry of the transition table. -/
noncomputable def matchesExpr (n : Expr) (r : Register k → Expr) (sym : Expr)
    (t : Instruction k State) : Expr :=
  andB (andB (eqB (r .control) (const (stateCode (some t.1))))
    (eqB (inputSymbolExpr n (r .inputPos) sym) (const (symbolCode t.2.1))))
    (allB (List.ofFn fun i : Fin k => eqB (r (.head i)) (const (symbolCode (t.2.2.1 i)))))

theorem eval_matchesExpr {r : Register k → Expr} {g : Register k → ℕ} {symbol : Option Bool}
    (hr : ∀ i, (r i).eval regs = g i) (hs : sym.eval regs = symbolCode symbol)
    (t : Instruction k State) :
    (matchesExpr n r sym t).eval regs = (matchesEntry (n.eval regs) g symbol t).toNat := by
  rw [matchesExpr, eval_andB (eval_andB eval_eqB eval_eqB) (eval_allB_ofFn _ _ fun i => eval_eqB)]
  simp only [eval_inputSymbolExpr hs, hr, eval_const, matchesEntry, symbolCode_injective.eq_iff]

/-- The registers after a tape action, as expressions in the head, left and right registers. -/
def tapeStepExpr (a : Option (Option Bool) × SignType) (h l r : Expr) : Expr × Expr × Expr :=
  let hw := match a.1 with
    | none => h
    | some b => const (symbolCode b)
  match a.2 with
  | .neg => (mod l (const 3), div l (const 3), add hw (mul (const 3) r))
  | .zero => (hw, l, r)
  | .pos => (mod r (const 3), add hw (mul (const 3) l), div r (const 3))

theorem eval_tapeStepExpr (a : Option (Option Bool) × SignType) (h l r : Expr) :
    ((tapeStepExpr a h l r).1.eval regs, (tapeStepExpr a h l r).2.1.eval regs,
      (tapeStepExpr a h l r).2.2.eval regs) =
      tapeStep a (h.eval regs, l.eval regs, r.eval regs) := by
  rcases a with ⟨w, d⟩
  cases w <;> cases d <;> simp [tapeStepExpr, tapeStep]

/-- The registers after a fixed action. -/
noncomputable def nextExpr (n : Expr) (r : Register k → Expr) (a : Action k Bool State) :
    Register k → Expr
  | .inputPos =>
    match a.inputTape with
    | .neg => sub (r .inputPos) (const 1)
    | .zero => r .inputPos
    | .pos => sub (add (r .inputPos) (const 1))
        (sub (add (r .inputPos) (const 1)) (add n (const 1)))
  | .control => const (stateCode a.state)
  | .output =>
    match a.output with
    | none => r .output
    | some b => iteB (eqB (r .output) (const 0)) (const (if b then 1 else 2)) (const 2)
  | .head i => (tapeStepExpr (a.workTapes i) (r (.head i)) (r (.left i)) (r (.right i))).1
  | .left i => (tapeStepExpr (a.workTapes i) (r (.head i)) (r (.left i)) (r (.right i))).2.1
  | .right i => (tapeStepExpr (a.workTapes i) (r (.head i)) (r (.left i)) (r (.right i))).2.2

theorem eval_nextExpr {r : Register k → Expr} {g : Register k → ℕ}
    (hr : ∀ i, (r i).eval regs = g i) (a : Action k Bool State) (i : Register k) :
    (nextExpr n r a i).eval regs = nextRegisters (n.eval regs) g a i := by
  have ht (j : Fin k) := eval_tapeStepExpr (regs := regs) (a.workTapes j) (r (.head j))
    (r (.left j)) (r (.right j))
  cases i with
  | inputPos =>
    cases h : a.inputTape <;> simp [nextExpr, nextRegisters, inputMove, h, hr]
    omega
  | control => simp [nextExpr, nextRegisters]
  | output =>
    cases h : a.output with
    | none => simp [nextExpr, nextRegisters, outputStep, h, hr]
    | some b =>
      simp only [nextExpr, nextRegisters, outputStep, h]
      rw [eval_iteB eval_eqB]
      simp [hr]
  | head j =>
    simp only [nextExpr, nextRegisters, ← hr]
    rw [← ht j]
  | left j =>
    simp only [nextExpr, nextRegisters, ← hr]
    rw [← ht j]
  | right j =>
    simp only [nextExpr, nextRegisters, ← hr]
    rw [← ht j]

/-- The test that all registers fit below the radix. -/
noncomputable def fitsExpr (B : Expr) (r : Register k → Expr) : Expr :=
  allB ((Finset.univ.toList : List (Register k)).map fun i => ltB (r i) B)

theorem eval_fitsExpr {B : Expr} {r : Register k → Expr} {g : Register k → ℕ}
    (hr : ∀ i, (r i).eval regs = g i) :
    (fitsExpr B r).eval regs = (fitsB (B.eval regs) g).toNat := by
  rw [fitsExpr, eval_allB_map _ _ (fun i => decide (g i < B.eval regs)) fun i _ => by simp [hr]]
  rfl

/-- The guarded local edge test, with the input symbol given by its code. -/
noncomputable def edgeExpr (ntm : MultiTapeNTM k Bool State) (B n u v sym : Expr) : Expr :=
  andB (andB (validExpr k State B n u) (validExpr k State B n v))
    (orB (andB (eqB (readRegistersExpr (k := k) B u .control)
        (const (stateCode (none : Option State)))) (eqB v u))
      (anyB ((instructions ntm).map fun t =>
        andB (andB (matchesExpr n (readRegistersExpr B u) sym t)
          (fitsExpr B (nextExpr n (readRegistersExpr B u) t.2.2.2)))
          (eqB v (packExpr B (nextExpr n (readRegistersExpr B u) t.2.2.2))))))

/-- **The edge expression computes the local edge test.** -/
theorem eval_edgeExpr (ntm : MultiTapeNTM k Bool State) {symbol : Option Bool}
    (hs : sym.eval regs = symbolCode symbol) :
    (edgeExpr ntm B n u v sym).eval regs =
      (edgeWithSymbol ntm (B.eval regs) (n.eval regs) (u.eval regs) (v.eval regs)
        symbol).toNat := by
  have hr : ∀ i, (readRegistersExpr (k := k) B u i).eval regs =
      readRegisters (k := k) (B.eval regs) (u.eval regs) i := fun i =>
    eval_readRegistersExpr i
  rw [edgeExpr, eval_andB (eval_andB eval_validExpr eval_validExpr)
    (eval_orB (eval_andB eval_eqB eval_eqB) (eval_anyB_map _ _
      (fun t => matchesEntry (n.eval regs) (readRegisters (B.eval regs) (u.eval regs)) symbol t
        && fitsB (B.eval regs)
          (nextRegisters (n.eval regs) (readRegisters (B.eval regs) (u.eval regs)) t.2.2.2)
        && decide (v.eval regs = Cslib.Radix.pack (B.eval regs)
          (nextRegisters (n.eval regs) (readRegisters (B.eval regs) (u.eval regs)) t.2.2.2)))
      fun t _ => ?_))]
  · simp [edgeWithSymbol, hr]
  · rw [eval_andB (eval_andB (eval_matchesExpr hr hs t) (eval_fitsExpr (eval_nextExpr hr _)))
      eval_eqB, eval_packExpr (eval_nextExpr hr _)]

variable (k State) in
/-- The test for accepting halted vertices. -/
noncomputable def badExpr (B n u : Expr) : Expr :=
  andB (andB (validExpr k State B n u)
    (eqB (readRegistersExpr (k := k) B u .control) (const (stateCode (none : Option State)))))
    (eqB (readRegistersExpr (k := k) B u .output) (const 1))

@[simp]
theorem eval_badExpr :
    (badExpr k State B n u).eval regs =
      (bad (k := k) (State := State) (B.eval regs) (n.eval regs) (u.eval regs)).toNat := by
  rw [badExpr, eval_andB (eval_andB eval_validExpr eval_eqB) eval_eqB]
  simp [bad]

/-- The start vertex. -/
noncomputable def startIDExpr (ntm : MultiTapeNTM k Bool State) (B : Expr) : Expr :=
  packExpr B fun i : Register k => match i with
    | .inputPos => const 1
    | .control => const (stateCode (some ntm.q₀))
    | _ => const 0

@[simp]
theorem eval_startIDExpr (ntm : MultiTapeNTM k Bool State) :
    (startIDExpr ntm B).eval regs = startID ntm (B.eval regs) := by
  rw [startIDExpr, eval_packExpr (g := fun i : Register k => match i with
    | .inputPos => 1
    | .control => stateCode (some ntm.q₀)
    | _ => 0) fun i => by cases i <;> rfl]
  rfl

variable (k) in
/-- The requested input position. -/
noncomputable def queryIndexExpr (B u : Expr) : Expr :=
  sub (readRegistersExpr (k := k) B u .inputPos) (const 1)

@[simp]
theorem eval_queryIndexExpr :
    (queryIndexExpr k B u).eval regs = queryIndex (k := k) (B.eval regs) (u.eval regs) := by
  simp [queryIndexExpr, queryIndex]

end Turing.MultiTapeNTM.ConfigurationGraph
