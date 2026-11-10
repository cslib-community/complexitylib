/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Step.Init
public import CslibFrontier.Foundations.Data.List.Lookup
public meta import Lean.Elab.Tactic

/-!
# Stepping through counter programs

The tactic `cp_step` takes one step of a counter program in a goal
`P.Reaches w Q (l, regs) s'` (`Turing.CounterProgram.Reaches`). It applies the stepping rule of the
instruction at `l`, proves the side conditions of the rule, and simplifies the configuration the
step reaches, so that a straight-line part of a reachability proof is a sequence of `cp_step`
calls instead of a `refine Reaches.assign h hB ?_` and a `simp only [eval_add, …]` per
instruction.

The rules are those of running configurations (`Turing.CounterProgram.Reaches.assign`, `.lt`,
`.read`), of oblivious configurations (`.oassign`, `.olt`, `.oread`) and of shifted instructions
(`.sassign`, `.slt`). A rule is tried only when the module proving it is imported, so this module
imports neither `CounterProgram.AllBranches` nor `CounterProgram.Block`.

## Main definitions

* `cp_step`, `cp_step [h₁, h₂]`: take one step, simplifying with the simp set `cp_simps` and the
  given lemmas.
-/

public section

attribute [cp_simps] Turing.CounterProgram.Expr.eval_const Turing.CounterProgram.Expr.eval_reg
  Turing.CounterProgram.Expr.eval_add Turing.CounterProgram.Expr.eval_sub
  Turing.CounterProgram.Expr.eval_mul Turing.CounterProgram.Expr.eval_div
  Turing.CounterProgram.Expr.eval_mod Turing.CounterProgram.Expr.eval_bit
  Turing.CounterProgram.Expr.eval_pow Turing.CounterProgram.Expr.eval_sum
  Turing.CounterProgram.readLabel lt_self_iff_false

end

public meta section

namespace Turing.CounterProgram.StepTactic

open Lean Meta Elab Tactic

/-- The stepping rules `cp_step` tries, in order. The names are resolved when the tactic runs, so
that a rule is available exactly when its module is imported. -/
private def rules : List Name :=
  [`Turing.CounterProgram.Reaches.assign, `Turing.CounterProgram.Reaches.lt,
    `Turing.CounterProgram.Reaches.read, `Turing.CounterProgram.Reaches.sassign,
    `Turing.CounterProgram.Reaches.slt, `Turing.CounterProgram.Reaches.oassign,
    `Turing.CounterProgram.Reaches.olt, `Turing.CounterProgram.Reaches.oread]

/-- Close the goal `g` with the tactic `tac`, or restore the state and report failure. -/
private def closesWith (tac : TSyntax `tactic) (g : MVarId) : TacticM Bool := do
  let s ← saveState
  try
    if (← evalTacticAt tac g).isEmpty then return true
    s.restore
    return false
  catch _ =>
    s.restore
    return false

/-- Prove a bound `x ≤ B` on a value written to a register, by a hypothesis or `omega`. -/
private def closeValue (g : MVarId) : TacticM Bool := do
  closesWith (← `(tactic| first | with_reducible assumption | omega)) g

/-- Prove a bound `∀ r ∈ regs, r ≤ B` on the registers: by a hypothesis, or entry by entry for
`regs'.set i x` (from the bound on `regs'`) and for a list written out, with the bounds on the
entries by a hypothesis or `omega`. -/
private partial def closeBound (g : MVarId) : TacticM Bool := do
  if ← closesWith (← `(tactic| with_reducible assumption)) g then return true
  if ← closesWith (← `(tactic| with_reducible exact List.forall_mem_nil _)) g then return true
  let s ← saveState
  try
    let lem ← mkConstWithFreshMVarLevels ``List.forall_mem_set_of_forall_mem
    if let [h, hx] ← withReducible <| g.apply lem then
      if (← closeBound h) && (← closeValue hx) then return true
  catch _ => pure ()
  s.restore
  try
    if let [hx, h] ← evalTacticAt
        (← `(tactic| with_reducible refine List.forall_mem_cons.mpr ⟨?_, ?_⟩)) g then
      if (← closeValue hx) && (← closeBound h) then return true
  catch _ => pure ()
  s.restore
  return false

/-- Prove a side condition of a stepping rule: a bound on the registers, `c ≤ B` or `i ≠ 0` by
`omega`, or `e.readsChoice = false` by evaluation. -/
private def closeSide (g : MVarId) : TacticM Bool := do
  if ← g.isAssigned then return true
  if ← closeBound g then return true
  closesWith (← `(tactic| first
    | omega
    | rfl
    | decide
    | (simp only [Turing.CounterProgram.Expr.readsChoice, Bool.or_eq_false_iff,
        beq_eq_false_iff_ne, ne_eq] <;> omega))) g

/-- Apply the rule `rule` to `g` if the instruction at the label of `g` is that of the rule, by a
hypothesis or by evaluation. Returns the side conditions and the goal after the step. -/
private def tryRule (g : MVarId) (rule : Name) : TacticM (Option (Array MVarId × MVarId)) := do
  unless (← getEnv).contains rule do return none
  let s ← saveState
  try
    let c ← mkConstWithFreshMVarLevels rule
    let (args, binfos, concl) ← forallMetaTelescope (← inferType c)
    unless ← withReducible <| isDefEq concl (← g.getType) do
      s.restore
      return none
    let explicit := (args.zip binfos).filterMap fun (a, b) => if b.isExplicit then some a else none
    let some hinstr := explicit[0]? | s.restore; return none
    let some next := explicit.back? | s.restore; return none
    unless ← closesWith (← `(tactic| first | with_reducible assumption | rfl)) hinstr.mvarId! do
      s.restore
      return none
    g.assign (mkAppN c args)
    return some ((explicit.extract 1 (explicit.size - 1)).map (·.mvarId!), next.mvarId!)
  catch _ =>
    s.restore
    return none

/-- The label of the source configuration of a goal `P.Reaches w Q (l, regs) s'`, when it is a
conditional or the label a read jumps to, which no rule applies to. -/
private def undecidedLabel? (tgt : Lean.Expr) : Option Lean.Expr := do
  let src ← tgt.getAppArgs[3]?
  guard (src.isAppOfArity ``Prod.mk 4)
  let l := src.getArg! 2
  guard (l.isAppOf ``ite || l.isAppOf ``Turing.CounterProgram.readLabel)
  return l

/-- Close `g` by `Reaches.refl` or by a hypothesis, when its target has no metavariables. -/
private def close (g : MVarId) : TacticM Bool := do
  if (← instantiateMVars (← g.getType)).hasMVar then return false
  closesWith (← `(tactic| first
    | with_reducible exact Turing.CounterProgram.Reaches.refl _
    | with_reducible assumption)) g

/-- `cp_step` takes one step of a counter program in a goal `P.Reaches w Q (l, regs) s'`. It
applies the stepping rule of the instruction at `l`, given by a hypothesis `P.instr l = i` or by
evaluation of `P.instr l`, then simplifies the configuration after the step with the simp set
`cp_simps`, numeral comparisons and the decided conditionals, and closes the goal by
`Reaches.refl` or by a hypothesis when it can.

* `cp_step [h₁, h₂]` adds simp lemmas, typically the values of the registers read
  (`regs.getD 0 0 = n`), the input bit read (`w[k]? = some true`) and the outcome of a
  comparison.

The side conditions of the rule must be proved automatically: a bound `∀ r ∈ regs, r ≤ B` on the
registers by a hypothesis, or entry by entry for `regs'.set i x` (from a bound on `regs'`) and for
a list written out, with the bounds on the entries by a hypothesis or `omega`; `c ≤ B` and `i ≠ 0`
by `omega`; and `e.readsChoice = false` by evaluation. Otherwise `cp_step` fails and names the
rule and the condition. The rules are those of running configurations (`Reaches.assign`,
`Reaches.lt`, `Reaches.read`), and, when their modules are imported, of oblivious configurations
(`Reaches.oassign`, `Reaches.olt`, `Reaches.oread`) and of shifted instructions
(`Reaches.sassign`, `Reaches.slt`). A label that is a conditional the given lemmas do not decide
stops `cp_step`: split on the condition first. -/
syntax (name := cpStep) "cp_step"
  (" [" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
    Lean.Parser.Tactic.simpLemma),* "]")? : tactic

/-- Simplify the configuration in `g` after a step, with the given simp lemmas `args`. -/
private def simpNext (g : MVarId) (args : Array Syntax) : TacticM (List MVarId) := do
  let args : Syntax.TSepArray [``Lean.Parser.Tactic.simpStar, ``Lean.Parser.Tactic.simpErase,
    ``Lean.Parser.Tactic.simpLemma] "," := ⟨(Syntax.mkSep args (mkAtom ",")).getArgs⟩
  evalTacticAt (← `(tactic| simp -failIfUnchanged only [cp_simps, reduceIte, Nat.reduceLT,
    $args,*])) g

elab_rules : tactic
  | `(tactic| cp_step $[[$args,*]]?) => withMainContext do
    let args := args.map (·.getElems.map (·.raw)) |>.getD #[]
    let g ← getMainGoal
    let tgt ← instantiateMVars (← g.getType)
    unless (← whnfR tgt).isAppOf ``Turing.CounterProgram.Reaches do
      throwError "cp_step: the goal is not a reachability goal `P.Reaches w Q s s'`{indentExpr tgt}"
    let mut found : Option (Name × Array MVarId × MVarId) := none
    for rule in rules do
      if let some r ← tryRule g rule then
        found := some (rule, r)
        break
    if found.isNone then
      if let some l := undecidedLabel? (← whnfR tgt) then
        throwError "cp_step: the label{indentExpr l}\nis not decided. Split on its condition \
          and pass the case to `cp_step` as a simp lemma."
    let some (rule, sides, next) := found
      | throwError "cp_step: no stepping rule applies to{indentExpr tgt}\nIt needs a hypothesis \
          `P.instr l = i` for the label `l`, or a program `P` whose instruction at `l` evaluates, \
          an assignment, comparison or read `i` with its rule imported, and a label that is not a \
          conditional."
    for side in sides do
      unless ← closeSide side do
        throwError "cp_step: could not prove the side condition{indentExpr (← instantiateMVars
          (← side.getType))}\nof `{rule}`. Add it as a hypothesis."
    let gs ← simpNext next args
    let gs ← gs.filterM fun g => return !(← close g)
    replaceMainGoal gs

end Turing.CounterProgram.StepTactic

end
