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
  given lemmas, and deciding conditional labels by a hypothesis or `omega`.
-/

public section

attribute [cp_simps] Turing.CounterProgram.Expr.eval_const Turing.CounterProgram.Expr.eval_reg
  Turing.CounterProgram.Expr.eval_add Turing.CounterProgram.Expr.eval_sub
  Turing.CounterProgram.Expr.eval_mul Turing.CounterProgram.Expr.eval_div
  Turing.CounterProgram.Expr.eval_mod Turing.CounterProgram.Expr.eval_bit
  Turing.CounterProgram.Expr.eval_pow Turing.CounterProgram.Expr.eval_sum
  Turing.CounterProgram.readLabel lt_self_iff_false
  List.getD_cons_zero List.getD_cons_succ List.set_cons_zero List.set_cons_succ

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

/-- Run `x`, keeping its effect when it returns `true` and restoring the state otherwise, also
when it throws. -/
private def attempt (x : TacticM Bool) : TacticM Bool := do
  let s ← saveState
  try
    if ← x then return true
    s.restore
    return false
  catch _ =>
    s.restore
    return false

/-- Close the goal `g` with the tactic `tac`. -/
private def closesWith (tac : TSyntax `tactic) (g : MVarId) : TacticM Bool :=
  attempt do return (← evalTacticAt tac g).isEmpty

/-- Close the goal `g` by a hypothesis, up to reducible unfolding. -/
private def byAssumption (g : MVarId) : TacticM Bool :=
  attempt <| withReducible g.assumptionCore

/-- Prove a bound `x ≤ B` on a value written to a register, by a hypothesis or `omega`. -/
private def closeValue (g : MVarId) : TacticM Bool := do
  if ← byAssumption g then return true
  closesWith (← `(tactic| omega)) g

/-- The list `l` of a bound `∀ r ∈ l, r ≤ B`. -/
private def boundList? (t : Lean.Expr) : Option Lean.Expr := do
  let .forallE _ _ body _ := t | none
  let .forallE _ mem _ _ := body | none
  guard (mem.isAppOfArity ``Membership.mem 5)
  return mem.getArg! 3

/-- Prove a bound `∀ r ∈ regs, r ≤ B` on the registers: by a hypothesis, or entry by entry for
`regs'.set i x` (from the bound on `regs'`) and for a list written out, with the bounds on the
entries by a hypothesis or `omega`. -/
private partial def closeBound (g : MVarId) : TacticM Bool := do
  if ← byAssumption g then return true
  let some l := boundList? (← instantiateMVars (← g.getType)) | return false
  let l := l.getAppFn
  if l.isConstOf ``List.set then
    attempt do
      let lem ← mkConstWithFreshMVarLevels ``List.forall_mem_set_of_forall_mem
      let [h, hx] ← withReducible <| g.apply lem | return false
      return (← closeBound h) && (← closeValue hx)
  else if l.isConstOf ``List.cons then
    attempt do
      let [hx, h] ← evalTacticAt
          (← `(tactic| with_reducible refine List.forall_mem_cons.mpr ⟨?_, ?_⟩)) g
        | return false
      return (← closeValue hx) && (← closeBound h)
  else if l.isConstOf ``List.nil then
    closesWith (← `(tactic| exact List.forall_mem_nil _)) g
  else
    return false

/-- Prove a side condition of a stepping rule: a bound on the registers, `c ≤ B` or `i ≠ 0` by a
hypothesis, `Nat.zero_le` or `omega`, or `e.readsChoice = false` by evaluation. -/
private def closeSide (g : MVarId) : TacticM Bool := do
  if ← g.isAssigned then return true
  if (boundList? (← instantiateMVars (← g.getType))).isSome then return ← closeBound g
  if ← byAssumption g then return true
  closesWith (← `(tactic| first
    | exact Nat.zero_le _
    | decide
    | omega
    | (simp only [Turing.CounterProgram.Expr.readsChoice, Bool.or_eq_false_iff,
        beq_eq_false_iff_ne, ne_eq] <;> omega))) g

/-- Apply the rule `rule` to `g` if the instruction at the label of `g` is that of the rule: by a
hypothesis, or, when `eval` is set, by evaluation. Returns the side conditions and the goal after
the step. -/
private def tryRule (g : MVarId) (eval : Bool) (rule : Name) :
    TacticM (Option (Array MVarId × MVarId)) := do
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
    let closed ← if eval then attempt do hinstr.mvarId!.refl; return true
      else byAssumption hinstr.mvarId!
    unless closed do
      s.restore
      return none
    g.assign (mkAppN c args)
    return some ((explicit.extract 1 (explicit.size - 1)).map (·.mvarId!), next.mvarId!)
  catch _ =>
    s.restore
    return none

/-- The label of the source configuration of a goal `P.Reaches w Q (l, regs) s'`, when it is a
conditional, the label a read jumps to, or the `match` on the bit read that `readLabel` unfolds to,
which no rule applies to. -/
private def undecidedLabel? (tgt : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let some src := tgt.getAppArgs[3]? | return none
  unless src.isAppOfArity ``Prod.mk 4 do return none
  let l := src.getArg! 2
  if l.isAppOf ``ite || l.isAppOf ``dite || l.isAppOf ``Turing.CounterProgram.readLabel ||
      (← isMatcherApp l) then
    return some l
  return none

/-- Whether `p` is a comparison `<`, `≤`, `>`, `≥`, `=` or `≠` of natural numbers or integers, or
its negation, which `omega` may decide. -/
private def isArith (p : Lean.Expr) : Bool :=
  let p := if p.isAppOfArity ``Not 1 then p.getArg! 0 else p
  let cmp := p.isAppOfArity ``LT.lt 4 || p.isAppOfArity ``LE.le 4 ||
    p.isAppOfArity ``GT.gt 4 || p.isAppOfArity ``GE.ge 4 ||
    p.isAppOfArity ``Eq 3 || p.isAppOfArity ``Ne 3
  cmp && ((p.getArg! 0).isConstOf ``Nat || (p.getArg! 0).isConstOf ``Int)

/-- A proof of `p` by `tac`. -/
private def proveWith (tac : MVarId → TacticM Bool) (p : Lean.Expr) :
    TacticM (Option Lean.Expr) := do
  let g ← mkFreshExprSyntheticOpaqueMVar p
  if ← tac g.mvarId! then return some (← instantiateMVars g)
  return none

/-- A proof of `p` or of `¬p` by a hypothesis, for a comparison `p` of natural numbers also by a
hypothesis stating the comparison or its negation the other way around (`b ≤ a` for `¬a < b`).
`true` marks a proof of `p`. -/
private def byHyp (p : Lean.Expr) : TacticM (Option (Bool × Lean.Expr)) := do
  if let some h ← proveWith byAssumption p then return some (true, h)
  if let some h ← proveWith byAssumption (mkNot p) then return some (false, h)
  let some (lt, a, b) :=
      if p.isAppOfArity ``LT.lt 4 then some (true, p.getArg! 2, p.getArg! 3)
      else if p.isAppOfArity ``LE.le 4 then some (false, p.getArg! 2, p.getArg! 3)
      else none
    | return none
  unless (p.getArg! 0).isConstOf ``Nat do return none
  -- `¬a < b ↔ b ≤ a` and `¬a ≤ b ↔ b < a`
  let flip ← if lt then mkAppM ``LE.le #[b, a] else mkAppM ``LT.lt #[b, a]
  if let some h ← proveWith byAssumption flip then
    return some (false, ← mkAppM (if lt then ``Nat.not_lt_of_le else ``Nat.not_le_of_lt) #[h])
  if let some h ← proveWith byAssumption (mkNot flip) then
    return some (true, ← mkAppM (if lt then ``Nat.lt_of_not_ge else ``Nat.le_of_not_lt) #[h])
  return none

/-- The equation `ite c t e = t` or `ite c t e = e` for the conditional `l = ite c t e`, when `c`
or `¬c` is a hypothesis or, for a comparison of numbers, follows by `omega`. -/
private def decideIte (l : Lean.Expr) : TacticM (Option Lean.Expr) := do
  let #[α, c, inst, t, e] := l.getAppArgs | return none
  let eq (pos : Bool) (h : Lean.Expr) : TacticM (Option Lean.Expr) := do
    return some (mkAppN (mkConst (if pos then ``if_pos else ``if_neg) [← getLevel α])
      #[c, inst, h, α, t, e])
  if let some (pos, h) ← byHyp c then return ← eq pos h
  unless isArith c do return none
  let tac ← `(tactic| omega)
  if let some h ← proveWith (closesWith tac) c then return ← eq true h
  if let some h ← proveWith (closesWith tac) (mkNot c) then return ← eq false h
  return none

/-- The label of the configuration at argument `i` of a goal `P.Reaches w Q s s'`. -/
private def labelAt? (tgt : Lean.Expr) (i : Nat) : Option Lean.Expr := do
  let s ← tgt.getAppArgs[i]?
  guard (s.isAppOfArity ``Prod.mk 4)
  return s.getArg! 2

/-- Decide the label `if c then l₁ else l₂` of the source configuration of a goal
`P.Reaches w Q (l, regs) s'` when `c` or `¬c` is a hypothesis or, for a comparison of numbers,
follows by `omega`: rewrite it to `l₁` or `l₂`. When `both` is set, decide instead the label of
either configuration when the label of the other is `l₁` or `l₂`, which can close the goal. Returns
the goal unchanged otherwise. -/
private def decideLabel (g : MVarId) (both : Bool) : TacticM MVarId := g.withContext do
  let mut g := g
  for i in if both then [3, 4] else [3] do
    let tgt ← instantiateMVars (← g.getType)
    let some l := labelAt? tgt i | continue
    unless l.isAppOfArity ``ite 5 do continue
    if both then
      let some other := labelAt? tgt (7 - i) | continue
      unless other == l.getArg! 3 || other == l.getArg! 4 do continue
    let some eq ← decideIte l | continue
    try
      let r ← g.rewrite tgt eq
      g ← g.replaceTargetEq r.eNew r.eqProof
    catch _ => continue
  return g

/-- Close `g` by `Reaches.refl` or by a hypothesis, when its target has no metavariables. -/
private def close (g : MVarId) : TacticM Bool := do
  if (← instantiateMVars (← g.getType)).hasMVar then return false
  if ← attempt do
      let refl ← mkConstWithFreshMVarLevels ``Turing.CounterProgram.Reaches.refl
      return (← withReducible <| g.apply refl).isEmpty then
    return true
  byAssumption g

/-- `cp_step` takes one step of a counter program in a goal `P.Reaches w Q (l, regs) s'`. It
applies the stepping rule of the instruction at `l`, given by a hypothesis `P.instr l = i` or by
evaluation of `P.instr l`, then simplifies the configuration after the step and closes the goal by
`Reaches.refl` or by a hypothesis when it can. The simplification uses the simp set `cp_simps`
(expressions, reads of written-out register lists), numeral `+`, `-`, `*` and `<`, and the decided
conditionals.

* `cp_step [h₁, h₂]` adds simp lemmas, typically the values of the registers read
  (`regs.getD 0 0 = n`) and the input bit read (`w[k]? = some true`), or simprocs such as
  `Nat.reduceDiv`. A fact about expressions that `cp_simps` evaluates, such as
  `(const 0).eval regs < e.eval regs ↔ p`, is passed as `↓h`, to apply before they are evaluated.

A conditional label `if c then l₁ else l₂` is decided when `c` or `¬c` is a hypothesis or, for a
comparison of natural numbers or integers, follows by `omega`: that of the configuration before
the step, and after the step that of either configuration when the label of the other is `l₁` or
`l₂`. The goal is then closed when it can be; otherwise it is left with that label decided.

The side conditions of the rule must be proved automatically: a bound `∀ r ∈ regs, r ≤ B` on the
registers by a hypothesis, or entry by entry for `regs'.set i x` (from a bound on `regs'`) and for
a list written out, with the bounds on the entries by a hypothesis or `omega`; `c ≤ B` and `i ≠ 0`
by a hypothesis, `decide` or `omega`; and `e.readsChoice = false` by evaluation. Otherwise
`cp_step` fails and names the rule and the condition. The rules are those of running
configurations (`Reaches.assign`, `Reaches.lt`, `Reaches.read`), and, when their modules are
imported, of oblivious configurations (`Reaches.oassign`, `Reaches.olt`, `Reaches.oread`) and of
shifted instructions (`Reaches.sassign`, `Reaches.slt`). A label left undecided, or as a `match`
on the bit read, stops `cp_step` with a diagnostic: split into cases first. -/
syntax (name := cpStep) "cp_step"
  (" [" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
    Lean.Parser.Tactic.simpLemma),* "]")? : tactic

/-- Simplify the configuration in `g` after a step, with the given simp lemmas `args`. -/
private def simpNext (g : MVarId) (args : Array Syntax) : TacticM (List MVarId) := do
  let args : Syntax.TSepArray [``Lean.Parser.Tactic.simpStar, ``Lean.Parser.Tactic.simpErase,
    ``Lean.Parser.Tactic.simpLemma] "," := ⟨(Syntax.mkSep args (mkAtom ",")).getArgs⟩
  evalTacticAt (← `(tactic| simp -failIfUnchanged only [cp_simps, reduceIte, Nat.reduceLT,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, $args,*])) g

elab_rules : tactic
  | `(tactic| cp_step $[[$args,*]]?) => withMainContext do
    let args := args.map (·.getElems.map (·.raw)) |>.getD #[]
    let g ← getMainGoal
    unless (← whnfR (← instantiateMVars (← g.getType))).isAppOf ``Turing.CounterProgram.Reaches do
      throwError "cp_step: the goal is not a reachability goal `P.Reaches w Q s s'`{indentExpr
        (← g.getType)}"
    let g ← decideLabel g false
    replaceMainGoal [g]
    let tgt ← instantiateMVars (← g.getType)
    let mut found : Option (Name × Array MVarId × MVarId) := none
    for eval in [false, true] do
      for rule in rules do
        if let some r ← tryRule g eval rule then
          found := some (rule, r)
          break
      if found.isSome then break
    if found.isNone then
      if let some l ← undecidedLabel? (← whnfR tgt) then
        throwError "cp_step: the label{indentExpr l}\nis not decided. Split into cases on its \
          condition, which `cp_step` then decides by a hypothesis or `omega`, or pass the bit read \
          (`w[i]? = some b`) as a simp lemma."
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
    let gs ← gs.filterMapM fun g => do
      if ← close g then return none
      let g' ← decideLabel g true
      if g' != g && (← close g') then return none
      return some g'
    replaceMainGoal gs

end Turing.CounterProgram.StepTactic

end
