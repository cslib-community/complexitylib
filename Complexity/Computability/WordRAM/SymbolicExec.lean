/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Structured

/-!
# Symbolic execution of structured word-RAM code

`Cslib.WordRAM.WP w c x Q` states that the structured program `c` leads from `x` to some data `y`
within some number `T` of instructions such that `Q y T`. It is the weakest-precondition form of
`Cslib.WordRAM.ExecWithin`: its rules run backwards through a program, one instruction at a time,
and hand the rest of the program the data in closed form. A goal `∃ y, ExecWithin w c x y T ∧ P y`
is the special case `WP w c x fun y t => t ≤ T ∧ P y` (`Cslib.WordRAM.WP.exists_execWithin`).

The tactic `wram_exec` applies these rules along the syntax of the program. It is meant for the
straight-line glue of correctness proofs, between loops and calls of subprograms with their own
specifications: it executes data instructions and conditionals, and stops at a loop, at a random
sample and at a program given by name, leaving the goal `WP w c y Q` with the data `y` reached.
`Cslib.WordRAM.WP.of_execWithin` then continues from a specification of `c`, and `wram_exec`
resumes on the remaining program.

The registers and memory cells an instruction reads are simplified as it executes. Reads after
`Cslib.WordRAM.Data.set` and `Cslib.WordRAM.Data.write` reduce when the register names are
literals and when the discharger decides whether two addresses are equal; the given simp lemmas
rewrite the values, so facts such as `x.regs zeroP = 0` replace the registers of the initial
data. A conditional takes the branch its simplified condition decides, by `simp` or by the
discharger, and otherwise splits into both alternatives with the hypothesis `hc`;
`wram_exec -split` stops there instead, so that `Cslib.WordRAM.WP.cut` can join the alternatives
before the rest of the program. Side conditions of instructions (`Fits w v`, a subtrahend at most
its minuend, a nonzero divisor) are proved by `simp` or the discharger; the others remain as
goals, after the main goals, tagged `hfit`, `hle` or `hb`.

`wram_simp` simplifies the reads in the postcondition left at the end, and `wram_bounded` proves
that the data reached is word-sized; `Cslib.WordRAM.WP.bounded` assumes this instead at the end of
a program.

## Main definitions

* `Cslib.WordRAM.WP`: the weakest-precondition form of `ExecWithin`.
* `wram_exec`: symbolic execution of the straight-line parts of structured code.
* `wram_simp`: reads of registers and memory after writes, with the simp set of `wram_exec`.
* `wram_bounded`: word-sizedness of data built by writes.

## Main results

* `Cslib.WordRAM.WP.exists_execWithin`, `Cslib.WordRAM.WP.execWithin`: back to `ExecWithin`.
* `Cslib.WordRAM.WP.seq`, `Cslib.WordRAM.WP.branch_lt`, `Cslib.WordRAM.WP.branch_eq`,
  `Cslib.WordRAM.WP.copy`, `Cslib.WordRAM.WP.load`, `Cslib.WordRAM.WP.store`, …: the rules for
  each construct, with the values read given in closed form.
* `Cslib.WordRAM.WP.cut`: an intermediate assertion, to join the alternatives of a conditional
  before the rest of a program.
* `Cslib.WordRAM.WP.bounded`: the data reached from word-sized data is word-sized.
* `Cslib.WordRAM.WP.name`: a name for the data reached, at a stop.
-/

@[expose] public section

namespace Cslib.WordRAM

variable {B : Basis} {r : ℕ}

/-! ## Reading registers and memory after writes -/

namespace Data

/-- Reading the register just set. -/
theorem set_regs_self (x : Data r) (i : Fin r) (v : ℕ) : (x.set i v).regs i = v := by
  rw [set_regs, Function.update_self]

/-- Reading another register than the one set. -/
theorem set_regs_of_ne {x : Data r} {i j : Fin r} (h : j ≠ i) (v : ℕ) :
    (x.set i v).regs j = x.regs j := by
  rw [set_regs, Function.update_of_ne h]

/-- Reading the memory cell just written. -/
theorem write_mem_self (x : Data r) (a v : ℕ) : (x.write a v).mem a = v := by
  rw [write_mem, Function.update_self]

/-- Reading the memory cell just written, at an address equal to it. -/
theorem write_mem_of_eq {x : Data r} {a b : ℕ} (h : b = a) (v : ℕ) : (x.write a v).mem b = v :=
  h ▸ write_mem_self x a v

/-- Reading another memory cell than the one written. -/
theorem write_mem_of_ne {x : Data r} {a b : ℕ} (h : b ≠ a) (v : ℕ) :
    (x.write a v).mem b = x.mem b := by
  rw [write_mem, Function.update_of_ne h]

end Data

/-! ## Weakest preconditions -/

/-- `WP w c x Q`: at word size `w`, the structured program `c` leads from data `x` to some data `y`
within some number `T` of instructions such that `Q y T`. -/
def WP (w : ℕ) (c : Code B r) (x : Data r) (Q : Data r → ℕ → Prop) : Prop :=
  ∃ y T, ExecWithin w c x y T ∧ Q y T

namespace WP

variable {w : ℕ} {c c₁ c₂ pos neg : Code B r} {cond : Cond r} {x y : Data r} {T : ℕ}
  {Q Q' : Data r → ℕ → Prop}

/-- Continue from an execution of `c` within `T` instructions. -/
theorem of_execWithin (h : ExecWithin w c x y T) (hQ : Q y T) : WP w c x Q := ⟨y, T, h, hQ⟩

/-- Weaken the postcondition. -/
theorem mono (h : WP w c x Q) (hQ : ∀ y T, Q y T → Q' y T) : WP w c x Q' :=
  let ⟨y, T, he, hy⟩ := h
  ⟨y, T, he, hQ y T hy⟩

/-- Name the data reached: continue from a variable `y` with the equation `y = x`, for instance
to state the hypotheses of a specification of a subprogram. -/
theorem name (h : ∀ y, y = x → WP w c y Q) : WP w c x Q := h x rfl

/-- Executions from word-sized data reach word-sized data, so the postcondition may assume it. -/
theorem bounded (hx : x.Bounded w) (h : WP w c x fun y T => y.Bounded w → Q y T) : WP w c x Q :=
  let ⟨y, T, he, hy⟩ := h
  ⟨y, T, he, hy (he.bounded hx)⟩

/-- A run within a bound `T` reaching data with property `P`. -/
theorem exists_execWithin {P : Data r → Prop} (h : WP w c x fun y t => t ≤ T ∧ P y) :
    ∃ y, ExecWithin w c x y T ∧ P y :=
  let ⟨y, _, he, ht, hy⟩ := h
  ⟨y, he.mono ht, hy⟩

/-- A run within a bound `T` reaching the given data `y`. -/
theorem execWithin (h : WP w c x fun y' t => t ≤ T ∧ y' = y) : ExecWithin w c x y T :=
  let ⟨_, _, he, ht, hy⟩ := h
  hy ▸ he.mono ht

/-- Run `c₁`, then `c₂` from the data it reaches, adding the instruction counts. -/
theorem seq (h : WP w c₁ x fun y T₁ => WP w c₂ y fun z T₂ => Q z (T₁ + T₂)) :
    WP w (.seq c₁ c₂) x Q :=
  let ⟨_, T₁, he₁, _, T₂, he₂, hz⟩ := h
  ⟨_, T₁ + T₂, he₁.seq he₂, hz⟩

/-- Run `c` to data satisfying an intermediate assertion `R`, and continue from any such data:
the join point of the alternatives of a conditional before the rest of a program. -/
theorem cut (R : Data r → ℕ → Prop) (h : WP w c x R) (hR : ∀ y T, R y T → Q y T) :
    WP w c x Q :=
  h.mono hR

/-- A conditional, by cases on its condition. -/
theorem branch (hpos : cond.Holds x → WP w pos x fun y T => Q y (T + 1))
    (hneg : ¬cond.Holds x → WP w neg x fun y T => Q y (T + 2)) :
    WP w (.branch cond pos neg) x Q := by
  by_cases hc : cond.Holds x
  · obtain ⟨y, T, he, hy⟩ := hpos hc
    exact ⟨y, T + 1, he.branch_pos hc, hy⟩
  · obtain ⟨y, T, he, hy⟩ := hneg hc
    exact ⟨y, T + 2, he.branch_neg hc, hy⟩

/-- A conditional on `x.regs i < x.regs j`, with the compared values in closed form. -/
theorem branch_lt {i j : Fin r} {a b : ℕ} (hi : x.regs i = a) (hj : x.regs j = b)
    (hpos : a < b → WP w pos x fun y T => Q y (T + 1))
    (hneg : ¬a < b → WP w neg x fun y T => Q y (T + 2)) :
    WP w (.branch (.lt i j) pos neg) x Q :=
  branch (fun hc => hpos (hi ▸ hj ▸ hc)) (fun hc => hneg (hi ▸ hj ▸ hc))

/-- A conditional on `x.regs i = x.regs j`, with the compared values in closed form. -/
theorem branch_eq {i j : Fin r} {a b : ℕ} (hi : x.regs i = a) (hj : x.regs j = b)
    (hpos : a = b → WP w pos x fun y T => Q y (T + 1))
    (hneg : ¬a = b → WP w neg x fun y T => Q y (T + 2)) :
    WP w (.branch (.eq i j) pos neg) x Q :=
  branch (fun hc => hpos (hi ▸ hj ▸ hc)) (fun hc => hneg (hi ▸ hj ▸ hc))

/-! ### Data instructions

Each rule names the values the instruction reads (`hi`, `hj`, `hs`, `ha`) and computes (`hv`),
so that the continuation `h` receives them in closed form. -/

section Ops

variable {d s a i j : Fin r} {u v b' : ℕ}

/-- Setting register `d` to a fitting constant `v`. -/
theorem const (hfit : Fits w v) (h : Q (x.set d v) 1) : WP (B := B) w (.op (.const d v)) x Q :=
  of_execWithin (ExecWithin.const hfit) h

/-- Copying register `s`, which holds `v`, into register `d`. -/
theorem copy (hs : x.regs s = v) (h : Q (x.set d v) 1) : WP (B := B) w (.op (.copy d s)) x Q :=
  of_execWithin ExecWithin.copy (hs ▸ h)

/-- Loading the memory cell at address `u`, held by register `a`, into register `d`. -/
theorem load (ha : x.regs a = u) (hv : x.mem u = v) (h : Q (x.set d v) 1) :
    WP (B := B) w (.op (.load d a)) x Q :=
  of_execWithin ExecWithin.load (ha ▸ hv ▸ h)

/-- Storing register `s`, which holds `v`, at address `u`, held by register `a`. -/
theorem store (ha : x.regs a = u) (hs : x.regs s = v) (h : Q (x.write u v) 1) :
    WP (B := B) w (.op (.store a s)) x Q :=
  of_execWithin ExecWithin.store (ha ▸ hs ▸ h)

/-- A standard binary operation on registers holding `u` and `b'`, with fitting value `v`. -/
theorem bin {f : BinOp} (hi : x.regs i = u) (hj : x.regs j = b') (hv : f.eval u b' = v)
    (hfit : Fits w v) (h : Q (x.set d v) 1) : WP w (.op (.bin f d i j)) x Q :=
  of_execWithin (ExecWithin.bin (hi ▸ hj ▸ hv ▸ hfit)) (hi ▸ hj ▸ hv ▸ h)

/-- Reading the word size into register `d`. -/
theorem width (h : Q (x.set d w) 1) : WP w (.op (.width d)) x Q :=
  of_execWithin ExecWithin.width h

/-- An exact binary operation on registers holding `u` and `b'`, defined with fitting value `v`. -/
theorem exactBin {f : BinOp} (hi : x.regs i = u) (hj : x.regs j = b')
    (hv : f.evalExact u b' = some v) (hfit : Fits w v) (h : Q (x.set d v) 1) :
    WP w (.op (.exactBin f d i j)) x Q :=
  of_execWithin (ExecWithin.op (by
    rw [Op.eval_exactBin, hi, hj, hv, Option.bind_some]
    exact Data.put_of_fits hfit)) h

/-- An exact subtraction `u - b'`, defined since `b' ≤ u`. -/
theorem exactSub (hi : x.regs i = u) (hj : x.regs j = b') (hle : b' ≤ u) (hv : u - b' = v)
    (hfit : Fits w v) (h : Q (x.set d v) 1) : WP w (.op (.exactBin .sub d i j)) x Q :=
  exactBin hi hj (by simp only [BinOp.evalExact, hle, ↓reduceIte, hv]) hfit h

/-- An exact division `u / b'`, defined since `b' ≠ 0`. -/
theorem exactDiv (hi : x.regs i = u) (hj : x.regs j = b') (hb : b' ≠ 0) (hv : u / b' = v)
    (hfit : Fits w v) (h : Q (x.set d v) 1) : WP w (.op (.exactBin .div d i j)) x Q :=
  exactBin hi hj (by simp only [BinOp.evalExact, hb, ↓reduceIte, hv]) hfit h

/-- An exact remainder `u % b'`, defined since `b' ≠ 0`. -/
theorem exactMod (hi : x.regs i = u) (hj : x.regs j = b') (hb : b' ≠ 0) (hv : u % b' = v)
    (hfit : Fits w v) (h : Q (x.set d v) 1) : WP w (.op (.exactBin .mod d i j)) x Q :=
  exactBin hi hj (by simp only [BinOp.evalExact, hb, ↓reduceIte, hv]) hfit h

/-- Reading the word size into register `d`, over the exact basis. -/
theorem exactWidth (h : Q (x.set d w) 1) : WP w (.op (.exactWidth d)) x Q :=
  of_execWithin (ExecWithin.op (Op.eval_exactWidth w d x)) h

end Ops

end WP

/-! ## The tactic -/

namespace WP.Exec

open Lean Meta Elab Tactic

/-- Close the goal `g` with the tactic `tac`, or restore the state and report failure. -/
meta def closesWith (tac : TSyntax `tactic) (g : MVarId) : TacticM Bool := do
  let s ← saveState
  try
    if (← evalTacticAt tac g).isEmpty then return true
    s.restore
    return false
  catch _ =>
    s.restore
    return false

/-- Beta-reduce the head of `e` until it is no longer a λ-abstraction applied to arguments. -/
meta partial def headBetaAll (e : Expr) : Expr :=
  if e.getAppFn.isLambda then headBetaAll e.headBeta else e

/-- The simplification context of one `wram_exec` call, the discharger for side conditions, and
the goals the call leaves for them. -/
meta structure Config where
  /-- The simp context. -/
  ctx : Simp.Context
  /-- The simprocs. -/
  simprocs : Simp.SimprocsArray
  /-- The discharger of conditional simp lemmas. -/
  simpDischarge : Option Simp.Discharge
  /-- The discharger of side conditions and branch conditions. -/
  disch : TSyntax `tactic
  /-- The side conditions left as goals. -/
  sideGoals : IO.Ref (Array MVarId)
  /-- The number of rules applied. -/
  steps : IO.Ref ℕ
  /-- Whether to split a conditional that is not decided, rather than stop at it. -/
  split : Bool

/-- Simplify `e` with the simp set of the call. -/
meta def simpExpr (cfg : Config) (e : Expr) : MetaM Simp.Result :=
  return (← Lean.Meta.simp e cfg.ctx cfg.simprocs cfg.simpDischarge).1

/-- Prove the proposition `p` by simplification to `True` or by `disch`. Returns the proof, or the
simplification of `p`. -/
meta def tryProve (cfg : Config) (disch : TSyntax `tactic) (p : Expr) :
    TacticM (Option Expr × Simp.Result) := do
  let res ← simpExpr cfg p
  if res.expr.isTrue then return (some (← mkOfEqTrue (← res.getProof)), res)
  if res.expr.isFalse then return (none, res)
  let g ← mkFreshExprSyntheticOpaqueMVar res.expr
  if ← closesWith disch g.mvarId! then
    return (some (← mkEqMPR (← res.getProof) g), res)
  return (none, res)

/-- Apply `rule` to the goal `g`, returning its arguments with the names of their binders. -/
meta def applyRule (cfg : Config) (g : MVarId) (rule : Name) : MetaM (Array (Name × Expr)) := do
  let c ← mkConstWithFreshMVarLevels rule
  let ty ← inferType c
  let (args, _, concl) ← forallMetaTelescope ty
  unless ← isDefEq concl (← g.getType) do
    throwError "wram_exec: `{rule}` does not apply to the goal{indentExpr (← g.getType)}"
  g.assign (mkAppN c args)
  cfg.steps.modify (· + 1)
  let names ← forallTelescope ty fun xs _ => xs.mapM (·.fvarId!.getUserName)
  return names.zip args

/-- Evaluate the premise `arg : lhs = rhs` by simplifying `lhs` and unifying the result with
`rhs`, which determines the values it names. -/
meta def evalPremise (cfg : Config) (arg lhs rhs : Expr) : MetaM Unit := do
  let res ← simpExpr cfg lhs
  unless ← isDefEq rhs res.expr do
    throwError "wram_exec: could not evaluate{indentExpr lhs}\nIt simplifies to\
      {indentExpr res.expr}\nwhich does not have the form{indentExpr rhs}"
  arg.mvarId!.assign (← res.getProof)

/-- Prove the side condition `arg`, or leave its simplification as a goal tagged `tag`. -/
meta def sidePremise (cfg : Config) (tag : Name) (arg : Expr) : TacticM Unit := do
  let ty ← instantiateMVars (← inferType arg)
  let (prf?, res) ← tryProve cfg cfg.disch ty
  match prf? with
  | some prf => arg.mvarId!.assign prf
  | none =>
    let g ← mkFreshExprSyntheticOpaqueMVar res.expr tag
    arg.mvarId!.assign (← mkEqMPR (← res.getProof) g)
    cfg.sideGoals.modify (·.push g.mvarId!)

/-- A fresh goal, with the given tag, for the premise `arg`, whose statement is beta-reduced. -/
meta def premiseGoal (arg : Expr) (tag : Name) : MetaM MVarId := do
  let ty ← instantiateMVars (← inferType arg)
  let g ← mkFreshExprSyntheticOpaqueMVar (headBetaAll ty) tag
  arg.mvarId!.assign g
  return g.mvarId!

/-- The rule executing the data instruction `o`, if there is one. -/
meta def opRule? (o : Expr) : Option Name :=
  match o.getAppFn.constName? with
  | some ``Op.const => some ``WP.const
  | some ``Op.copy => some ``WP.copy
  | some ``Op.load => some ``WP.load
  | some ``Op.store => some ``WP.store
  | some ``Op.bin => some ``WP.bin
  | some ``Op.width => some ``WP.width
  | some ``Op.exactWidth => some ``WP.exactWidth
  | some ``Op.exactBin =>
    match (o.getArg! 1).constName? with
    | some ``BinOp.sub => some ``WP.exactSub
    | some ``BinOp.div => some ``WP.exactDiv
    | some ``BinOp.mod => some ``WP.exactMod
    | _ => some ``WP.exactBin
  | _ => none

mutual

/-- Execute the program of the goal `g : WP w c x Q` instruction by instruction, and return the
goals where execution stops: `Q y T` at the end of the program, and `WP w c' y Q'` at a loop, a
random sample or a program given by name. -/
meta partial def walk (cfg : Config) (g : MVarId) : TacticM (Array MVarId) := g.withContext do
  let tgt := headBetaAll (← instantiateMVars (← g.getType))
  let g ← g.replaceTargetDefEq tgt
  let tgt := tgt.consumeMData
  unless tgt.isAppOfArity ``WP 6 do return #[g]
  let code ← whnfR (tgt.getArg! 3)
  match code.getAppFn.constName? with
  | some ``Code.seq => step cfg g ``WP.seq
  | some ``Code.op =>
    match opRule? (code.getArg! 2) with
    | some rule => step cfg g rule
    | none => return #[g]
  | some ``Code.branch =>
    match (code.getArg! 2).getAppFn.constName? with
    | some ``Cond.lt => branch cfg g ``WP.branch_lt
    | some ``Cond.eq => branch cfg g ``WP.branch_eq
    | _ => return #[g]
  | _ => return #[g]

/-- Apply the rule `rule` to `g`: evaluate the values it reads, prove or leave its side
conditions, and continue with its continuation `h`. -/
meta partial def step (cfg : Config) (g : MVarId) (rule : Name) : TacticM (Array MVarId) := do
  let tag ← g.getTag
  let args ← applyRule cfg g rule
  let mut cont := none
  for (n, arg) in args do
    if ← arg.mvarId!.isAssigned then continue
    let ty ← instantiateMVars (← inferType arg)
    unless ← isProp ty do continue
    if n == `h then
      cont := some arg
    else if let some (_, lhs, rhs) := ty.eq? then
      if rhs.hasExprMVar then evalPremise cfg arg lhs rhs else sidePremise cfg n arg
    else
      sidePremise cfg n arg
  let some arg := cont | throwError "wram_exec: `{rule}` has no continuation"
  walk cfg (← premiseGoal arg tag)

/-- Apply the conditional rule `rule` to `g`: evaluate the compared values, take the branch that
`simp` or the discharger decides, and otherwise continue in both with the hypothesis `hc`, or stop
at the conditional if `cfg.split` is false. -/
meta partial def branch (cfg : Config) (g : MVarId) (rule : Name) : TacticM (Array MVarId) := do
  let tag ← g.getTag
  let saved ← saveState
  let args ← applyRule cfg g rule
  for (n, arg) in args do
    if n == `hi || n == `hj then
      let ty ← instantiateMVars (← inferType arg)
      let some (_, lhs, rhs) := ty.eq? | throwError "wram_exec: unexpected premise of `{rule}`"
      evalPremise cfg arg lhs rhs
  let some hpos := args.find? (·.1 == `hpos) |>.map (·.2) | throwError "wram_exec: no `hpos`"
  let some hneg := args.find? (·.1 == `hneg) |>.map (·.2) | throwError "wram_exec: no `hneg`"
  let .forallE _ cond _ _ ← instantiateMVars (← inferType hpos)
    | throwError "wram_exec: unexpected premise of `{rule}`"
  -- `take keep drop contra`: continue with `keep`, and close `drop`, whose hypothesis `hc` gives
  -- the contradiction `contra hc`.
  let take (keep drop : Expr) (contra : Expr → Expr) : TacticM (Array MVarId) := do
    let .forallE _ dom body _ ← instantiateMVars (← inferType keep)
      | throwError "wram_exec: unexpected premise of `{rule}`"
    let .forallE _ ndom nbody _ ← instantiateMVars (← inferType drop)
      | throwError "wram_exec: unexpected premise of `{rule}`"
    drop.mvarId!.assign (← withLocalDeclD `hc ndom fun hc => do
      mkLambdaFVars #[hc] (← mkFalseElim nbody (contra hc)))
    let k ← mkFreshExprSyntheticOpaqueMVar (headBetaAll body) tag
    keep.mvarId!.assign (.lam `hc dom k .default)
    walk cfg k.mvarId!
  match (← tryProve cfg cfg.disch cond).1 with
  | some p => take hpos hneg fun hc => mkApp hc p
  | none =>
    match (← tryProve cfg cfg.disch (mkNot cond)).1 with
    | some np => take hneg hpos fun hc => mkApp np hc
    | none =>
      unless cfg.split do
        saved.restore
        cfg.steps.modify (· - 1)
        return #[g]
      let (_, gpos) ← (← premiseGoal hpos (tag ++ `pos)).intro `hc
      let (_, gneg) ← (← premiseGoal hneg (tag ++ `neg)).intro `hc
      return (← walk cfg gpos) ++ (← walk cfg gneg)

end

/-- Turn a goal `∃ y, ExecWithin w c x y T ∧ P y`, `ExecWithin w c x y T` or
`∃ y T, ExecWithin w c x y T ∧ Q y T` into a `WP` goal. Returns the new goal, and whether its
postcondition states the data reached, `t ≤ T ∧ y' = y`. -/
meta def toWP (g : MVarId) : MetaM (MVarId × Bool) := g.withContext do
  let tgt := (headBetaAll (← instantiateMVars (← g.getType))).consumeMData
  if tgt.isAppOfArity ``WP 6 then return (g, false)
  let s ← saveState
  for (rule, eq) in [(``WP.exists_execWithin, false), (``WP.execWithin, true)] do
    try
      let [g'] ← g.apply (← mkConstWithFreshMVarLevels rule) | failure
      return (g', eq)
    catch _ => s.restore
  let wp ← mkConstWithFreshMVarLevels ``WP
  let (args, _, _) ← forallMetaTelescope (← inferType wp)
  let e := mkAppN wp args
  if ← isDefEq e tgt then return (← g.replaceTargetDefEq (← instantiateMVars e), false)
  s.restore
  throwError "wram_exec: expected a goal `WP w c x Q`, `∃ y, ExecWithin w c x y T ∧ P y`, \
    `ExecWithin w c x y T` or `∃ y T, ExecWithin w c x y T ∧ Q y T`, got{indentExpr tgt}"

/-- At the end of a program, prove a leading instruction bound `t ≤ T` of the postcondition by
`omega`, and leave the rest, unless `eq` and it is an equation between data closed by reducible
`rfl`. -/
meta def closeBound (cfg : Config) (eq : Bool) (g : MVarId) : TacticM (Option MVarId) :=
    g.withContext do
  let tgt := (← instantiateMVars (← g.getType)).consumeMData
  let some (A, B) := tgt.and? | return some g
  unless A.isAppOfArity ``LE.le 4 do return some g
  let some prf := (← tryProve cfg (← `(tactic| omega)) A).1 | return some g
  let g' ← mkFreshExprSyntheticOpaqueMVar B (← g.getTag)
  g.assign (← mkAppM ``And.intro #[prf, g'])
  if eq then
    try
      withReducible g'.mvarId!.refl
      return none
    catch _ => pure ()
  return some g'.mvarId!

end WP.Exec

open Lean Meta Elab Tactic in
/-- The simp call of `wram_exec` and `wram_simp`: the lemmas reading registers and memory after
`Data.set` and `Data.write`, arithmetic on numerals, and the given lemmas `args`, with register
names compared by `decide` and other side conditions of the lemmas proved by `disch`. -/
meta def WP.Exec.simpCall (disch : TSyntax ``Lean.Parser.Tactic.tacticSeq) (args : Array Syntax)
    (loc? : Option (TSyntax ``Lean.Parser.Tactic.location)) : MacroM (TSyntax `tactic) := do
  let args : Syntax.TSepArray [``Lean.Parser.Tactic.simpStar, ``Lean.Parser.Tactic.simpErase,
    ``Lean.Parser.Tactic.simpLemma] "," := ⟨(Syntax.mkSep args (mkAtom ",")).getArgs⟩
  `(tactic| simp (disch := first | decide | assumption | $disch) only [
    Cslib.WordRAM.Data.set_regs_self, Cslib.WordRAM.Data.set_regs_of_ne,
    Cslib.WordRAM.Data.set_mem, Cslib.WordRAM.Data.write_regs,
    Cslib.WordRAM.Data.write_mem_self, Cslib.WordRAM.Data.write_mem_of_ne,
    Cslib.WordRAM.Data.write_mem_of_eq, Cslib.WordRAM.BinOp.eval, Cslib.WordRAM.BinOp.evalExact,
    Cslib.WordRAM.fits_zero, Nat.add_zero, Nat.zero_add, Nat.add_sub_cancel,
    Nat.add_sub_cancel_left, Nat.sub_zero, Nat.sub_self, Nat.lt_irrefl, Nat.not_lt_zero,
    Nat.zero_lt_succ, Nat.add_one_ne_zero, not_true_eq_false, not_false_eq_true, and_self,
    and_true, true_and, ↓reduceIte, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceLT, Nat.reduceGT,
    Nat.reduceLeDiff, Nat.reduceEqDiff, $args,*] $[$loc?]?)

/-- `wram_exec` symbolically executes structured word-RAM code (`Cslib.WordRAM.Code`) on a goal
`∃ y, ExecWithin w c x y T ∧ P y`, `ExecWithin w c x y T` or `Cslib.WordRAM.WP w c x Q`. It runs
the data instructions and conditionals of `c` in order, with the data in closed form, until the
end of the program, where `t ≤ T ∧ P y` (respectively `t ≤ T ∧ y' = y`, or `Q y t`) remains for
the data `y` and instruction count `t` reached; a leading bound `t ≤ T` is closed by `omega` when
it can. It stops at a loop, a random sample or a program given by name, leaving `WP w c' y Q'`:
continue with `refine WP.of_execWithin h ?_` from a specification `h` of `c'`, then `wram_exec`
again. Unfold programs given by name to execute them instead.

* `wram_exec [h₁, h₂]` adds simp lemmas for the values read, typically the contents of the
  registers of `x`, such as `x.regs zeroP = 0`, and the memory cells it reads.
* `wram_exec (disch := tac)` sets the discharger, `omega` by default. It proves side conditions
  (`Fits w v`, `b ≤ a` for an exact subtraction, a nonzero divisor), decides conditions of
  branches, and decides whether two memory addresses are equal. Register names, and side
  conditions on numerals, are decided by `decide`.

A conditional neither `simp` nor the discharger decides splits into both alternatives, tagged
`pos` and `neg`, with the hypothesis `hc` on the compared values; `wram_exec -split` stops at it
instead, leaving `WP w (.branch …) y Q'`, for instance to join the alternatives with `WP.cut`.
Side conditions that remain are left as goals after the main ones, tagged by the premise they come
from (`hfit`, `hle`, `hb`). -/
syntax (name := wramExec) "wram_exec" Lean.Parser.Tactic.optConfig (Lean.Parser.Tactic.discharger)?
  (" [" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
    Lean.Parser.Tactic.simpLemma),* "]")? : tactic

/-- `wram_simp [h₁, h₂]` simplifies reads of registers and memory after `Data.set` and
`Data.write` with the simp set of `wram_exec`, typically in the postcondition `wram_exec` leaves.
`wram_simp (disch := tac)` sets the discharger, `omega` by default, and `wram_simp at h` works on
hypotheses. -/
syntax (name := wramSimp) "wram_simp" (Lean.Parser.Tactic.discharger)?
  (" [" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
    Lean.Parser.Tactic.simpLemma),* "]")? (Lean.Parser.Tactic.location)? : tactic

/-- `wram_bounded` proves `y.Bounded w` for data `y` built by `Data.set` and `Data.write` from data
`x` with a hypothesis `x.Bounded w`. It proves the fitting conditions of values read from `x`, and
leaves those of the other written values as goals. -/
syntax (name := wramBounded) "wram_bounded" : tactic

macro_rules
  | `(tactic| wram_bounded) => `(tactic| repeat' (first
      | assumption
      | apply Cslib.WordRAM.Data.Bounded.set
      | apply Cslib.WordRAM.Data.Bounded.write
      | exact (by assumption : Cslib.WordRAM.Data.Bounded _ _).1 _
      | exact (by assumption : Cslib.WordRAM.Data.Bounded _ _).2 _))

open Lean in
/-- The discharger of a `wram_exec` or `wram_simp` call. -/
meta def WP.Exec.dischOf (d? : Option (TSyntax ``Lean.Parser.Tactic.discharger)) :
    MacroM (TSyntax ``Lean.Parser.Tactic.tacticSeq) :=
  match d? with
  | some d => pure ⟨d.raw[3]⟩
  | none => `(Lean.Parser.Tactic.tacticSeq| omega)

macro_rules
  | `(tactic| wram_simp $[$d?:discharger]? $[[$args,*]]? $[$loc?:location]?) => do
    WP.Exec.simpCall (← WP.Exec.dischOf d?) (args.map (·.getElems.map (·.raw)) |>.getD #[]) loc?

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| wram_exec $cfg:optConfig $[$d?:discharger]? $[[$args,*]]?) => withMainContext do
    let mut split := true
    for item in cfg.raw[0].getArgs do
      match item[0] with
      | `(Lean.Parser.Tactic.negConfigItem| -split) => split := false
      | `(Lean.Parser.Tactic.posConfigItem| +split) => split := true
      | _ => throwErrorAt item "wram_exec: unknown option; the only option is `-split`"
    let userDisch ← liftMacroM <| WP.Exec.dischOf d?
    let sideDisch ← `(tactic| first | decide | assumption | $userDisch)
    let stx ← liftMacroM <|
      WP.Exec.simpCall userDisch (args.map (·.getElems.map (·.raw)) |>.getD #[]) none
    let { ctx, simprocs, dischargeWrapper, .. } ← mkSimpContext stx (eraseLocal := false)
    dischargeWrapper.with fun discharge? => do
      let sideGoals ← IO.mkRef #[]
      let steps ← IO.mkRef 0
      let cfg : WP.Exec.Config :=
        { ctx, simprocs, simpDischarge := discharge?, disch := sideDisch, sideGoals, steps, split }
      let (g, eq) ← WP.Exec.toWP (← getMainGoal)
      let mains ← WP.Exec.walk cfg g
      if (← cfg.steps.get) == 0 then
        let tgt ← instantiateMVars (← g.getType)
        throwError "wram_exec: nothing to execute in{indentExpr tgt}\nThe program starts with a \
          loop, a random sample or a program given by name. Apply its specification with \
          `WP.of_execWithin`, or unfold it."
      let mains ← mains.filterMapM (WP.Exec.closeBound cfg eq)
      replaceMainGoal (mains ++ (← cfg.sideGoals.get)).toList

end Cslib.WordRAM

end
