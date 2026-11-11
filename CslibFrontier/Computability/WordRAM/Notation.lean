/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Structured
public import CslibFrontier.Computability.WordRAM.Notation.Init
public import CslibFrontier.Tactic.Fits
public meta import Lean.Elab.Tactic.Simp

/-!
# Notation for structured word-RAM programs

`ram[ s₁; s₂; … ]` writes a structured program (`Cslib.WordRAM.Code`) as a sequence of statements,
one per data instruction, in the style of word-RAM pseudocode. Registers are named by identifiers,
for instance local abbreviations of elements of `Fin r`. The statements are:

* `d ← #v`: set register `d` to the constant `v`;
* `d ← s`: copy register `s` into register `d`;
* `d ← i + j`, and likewise `-`, `*`, `/`, `%`, `&&&`, `|||`, `^^^`, `<<<`, `>>>`: a binary
  operation (`Cslib.WordRAM.BinOp`) on registers `i` and `j`;
* `d ← *a`, `*a ← s`: load from and store to the memory cell whose address is in register `a`;
* `d ← width%`: set register `d` to the word size;
* `d ← rand s`: sample uniformly from `[0, regs s]` into register `d`;
* `if i = j then [ … ] else [ … ]`, `if i < j then [ … ] else [ … ]`: a conditional;
* `while i = j do [ … ]`, `while i < j do [ … ]`: a loop;
* `⟪c⟫`: the structured program `c`, for instance a subroutine.

The notation unfolds to the constructors of `Cslib.WordRAM.Code`, so it adds nothing to the
semantics. The binary operations and `width%` are instructions of the standard basis
(`Cslib.WordRAM.Op.bin`, `Cslib.WordRAM.Op.width`); the other statements work over every basis.
It is scoped: `open Cslib.WordRAM` enables it, with its statement forms, their expansions and the
tactic `ram_eval`. Only the category `wramStmt` and the syntax abbreviation `wramBlock` are
global, since Lean cannot scope them; without the open, `wramStmt` has no rules, so they parse
nothing. The statement forms follow the word-RAM notation of [Algolean][Algolean2026]. Its only
new tokens are `ram[`, `width%` and the internal `ram_stmt%` and `ram_block%`, so it reserves no
identifiers: `ram` and `width` remain ordinary names.

## Main definitions

* `ram[ s₁; s₂; … ]`: scoped notation for structured word-RAM programs (`Cslib.WordRAM.Code`).

## Tactics

* `ram_eval`, `ram_eval n` (scoped, like the notation): symbolic execution. On a goal
  `Cslib.WordRAM.ExecWithin w c x y T` or `Cslib.WordRAM.Exec w c x y T`, it runs the interpreter
  `Cslib.WordRAM.Code.eval` on `c` and `x` with `simp`, allowing each loop `n` iterations (default
  `0`, for loop-free code), and closes the goal when the result is `y` within (exactly, for `Exec`)
  `T` instructions; with `y` a metavariable, it determines `y`. Which constants and results fit a
  word is decided for numerals, by `omega` from the `Fits` hypotheses in context
  (`Cslib.WordRAM.reduceFits`), so that a bound implied by a fact such as `Fits w (base + n)`
  needs no statement of its own, or else by the given simp lemmas. Programs given by name are
  unfolded by passing their definitions among the simp lemmas, as in `ram_eval [myProgram, h]`.
  When it fails, the error names the failing step: the goal has neither form, a given simp lemma
  does not elaborate, `simp` cannot evaluate the program, the interpreter returns `none`, a
  condition remains undecided (shown), or `omega` cannot prove the instruction bound (shown).
  Under `try` and `first`, which discard the message, it fails without this replay, at the cost of
  the attempt alone. `ram_eval` and `ram_exact_eval` both
  expand to the internal tactic `ram_eval_core`, which holds the shared steps; they differ only in
  their simp set, `ram_eval_simps` or `ram_exact_eval_simps`, whose lemmas for the instructions of
  the basis differ. The sets are filled, and so indexed, once (`ram_eval_simp_set`), so a call
  indexes only the simp lemmas it is given.

## References

* [S. Srinivas et al., *Algolean*][Algolean2026]
-/

public section

namespace Cslib.WordRAM

/-- A statement of a structured word-RAM program. -/
declare_syntax_cat wramStmt

/-- A block of statements, separated by semicolons. -/
syntax wramBlock := "[" sepBy1(wramStmt, "; ") "]"

/-- A structured word-RAM program, written as a block of statements. -/
scoped syntax "ram[" sepBy1(wramStmt, "; ") "]" : term

/-- Internal: a nested block of statements, as a structured program. -/
scoped syntax "ram_block%" wramBlock : term

/-- Internal: a single statement, as a structured program. -/
scoped syntax "ram_stmt%" wramStmt : term

/-- Set a register to a constant. -/
scoped syntax ident " ← " "#" term:max : wramStmt
/-- Copy a register. -/
scoped syntax ident " ← " ident : wramStmt
/-- Addition. -/
scoped syntax ident " ← " ident " + " ident : wramStmt
/-- Truncated subtraction. -/
scoped syntax ident " ← " ident " - " ident : wramStmt
/-- Multiplication. -/
scoped syntax ident " ← " ident " * " ident : wramStmt
/-- Division. -/
scoped syntax ident " ← " ident " / " ident : wramStmt
/-- Remainder. -/
scoped syntax ident " ← " ident " % " ident : wramStmt
/-- Bitwise and. -/
scoped syntax ident " ← " ident " &&& " ident : wramStmt
/-- Bitwise or. -/
scoped syntax ident " ← " ident " ||| " ident : wramStmt
/-- Bitwise exclusive or. -/
scoped syntax ident " ← " ident " ^^^ " ident : wramStmt
/-- Shift left. -/
scoped syntax ident " ← " ident " <<< " ident : wramStmt
/-- Shift right. -/
scoped syntax ident " ← " ident " >>> " ident : wramStmt
/-- Load from the memory cell whose address is in a register. -/
scoped syntax ident " ← " "*" ident : wramStmt
/-- Store to the memory cell whose address is in a register. -/
scoped syntax "*" ident " ← " ident : wramStmt
/-- Read the word size. -/
scoped syntax ident " ← " "width%" : wramStmt
/-- Sample uniformly from `[0, regs s]` into a register. -/
scoped syntax ident " ← " &"rand" ppSpace ident : wramStmt
/-- A conditional on the equality of two registers. -/
scoped syntax "if " ident " = " ident " then " wramBlock " else " wramBlock : wramStmt
/-- A conditional on the comparison of two registers. -/
scoped syntax "if " ident " < " ident " then " wramBlock " else " wramBlock : wramStmt
/-- A loop while two registers are equal. -/
scoped syntax "while " ident " = " ident " do " wramBlock : wramStmt
/-- A loop while one register is smaller than another. -/
scoped syntax "while " ident " < " ident " do " wramBlock : wramStmt
/-- A structured program given as a term. -/
scoped syntax "⟪" term "⟫" : wramStmt

scoped macro_rules
  | `(ram[ $s:wramStmt ]) => `(ram_stmt% $s)
  | `(ram[ $s:wramStmt; $ss;* ]) => `(Cslib.WordRAM.Code.seq (ram_stmt% $s) (ram[ $ss;* ]))
  | `(ram_block% [ $ss;* ]) => `(ram[ $ss;* ])

scoped macro_rules
  | `(ram_stmt% $d:ident ← #$v) => `(Cslib.WordRAM.Code.op (.const $d $v))
  | `(ram_stmt% $d:ident ← $s:ident) => `(Cslib.WordRAM.Code.op (.copy $d $s))
  | `(ram_stmt% $d:ident ← $i:ident + $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .add $d $i $j))
  | `(ram_stmt% $d:ident ← $i:ident - $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .sub $d $i $j))
  | `(ram_stmt% $d:ident ← $i:ident * $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .mul $d $i $j))
  | `(ram_stmt% $d:ident ← $i:ident / $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .div $d $i $j))
  | `(ram_stmt% $d:ident ← $i:ident % $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .mod $d $i $j))
  | `(ram_stmt% $d:ident ← $i:ident &&& $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .and $d $i $j))
  | `(ram_stmt% $d:ident ← $i:ident ||| $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .or $d $i $j))
  | `(ram_stmt% $d:ident ← $i:ident ^^^ $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .xor $d $i $j))
  | `(ram_stmt% $d:ident ← $i:ident <<< $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .shiftLeft $d $i $j))
  | `(ram_stmt% $d:ident ← $i:ident >>> $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .shiftRight $d $i $j))
  | `(ram_stmt% $d:ident ← *$a:ident) => `(Cslib.WordRAM.Code.op (.load $d $a))
  | `(ram_stmt% *$a:ident ← $s:ident) => `(Cslib.WordRAM.Code.op (.store $a $s))
  | `(ram_stmt% $d:ident ← width%) => `(Cslib.WordRAM.Code.op (.width $d))
  | `(ram_stmt% $d:ident ← rand $s:ident) => `(Cslib.WordRAM.Code.rand $d $s)
  | `(ram_stmt% if $i:ident = $j:ident then $p:wramBlock else $n:wramBlock) =>
    `(Cslib.WordRAM.Code.branch (.eq $i $j) (ram_block% $p) (ram_block% $n))
  | `(ram_stmt% if $i:ident < $j:ident then $p:wramBlock else $n:wramBlock) =>
    `(Cslib.WordRAM.Code.branch (.lt $i $j) (ram_block% $p) (ram_block% $n))
  | `(ram_stmt% while $i:ident = $j:ident do $b:wramBlock) =>
    `(Cslib.WordRAM.Code.loop (.eq $i $j) (ram_block% $b))
  | `(ram_stmt% while $i:ident < $j:ident do $b:wramBlock) =>
    `(Cslib.WordRAM.Code.loop (.lt $i $j) (ram_block% $b))
  | `(ram_stmt% ⟪$c⟫) => `(($c : Cslib.WordRAM.Code _ _))

/-- Symbolically execute structured code on a goal `ExecWithin w c x y T` or `Exec w c x y T`,
allowing each loop the given number of iterations (default `0`). Whether a written number fits a
word is decided by `omega` from the `Fits` hypotheses in context (`Cslib.WordRAM.reduceFits`),
or by the given simp lemmas.

On failure the error names the step that failed: the goal has neither form, a given simp lemma
does not elaborate, `simp` cannot evaluate the program (pass its definition, as in
`ram_eval [myProgram]`), the interpreter returns `none` (a fault, or too few loop iterations), a
branch or `Fits` condition remains (shown), or `omega` cannot prove the instruction bound (shown).
Under `try` or `first`, which discard the message, it fails without working out which step. -/
scoped syntax (name := ramEval) "ram_eval" (ppSpace num)? (" [" Lean.Parser.Tactic.simpArg,* "]")? :
  tactic

/-- Internal: the symbolic execution behind `ram_eval` and `ram_exact_eval`. The string names the
calling tactic in error messages and the number is the loop fuel; the identifier names the simp set
that evaluates the program, `ram_eval_simps` or `ram_exact_eval_simps`, and the list holds the
caller's simp lemmas. -/
scoped syntax (name := ramEvalCore) "ram_eval_core " str num ident
  " [" Lean.Parser.Tactic.simpArg,* "]" : tactic

scoped macro_rules
  | `(tactic| ram_eval) => `(tactic| ram_eval 0 [])
  | `(tactic| ram_eval [$args,*]) => `(tactic| ram_eval 0 [$args,*])
  | `(tactic| ram_eval $n:num) => `(tactic| ram_eval $n [])
  | `(tactic| ram_eval $n:num [$args,*]) => `(tactic|
      ram_eval_core "ram_eval" $n ram_eval_simps [$args,*])

/-- Internal: `simp +decide only` with the simp set `set` (`ram_eval_simps` or
`ram_exact_eval_simps`), the simplification procedures of `ram_eval`
(`Cslib.WordRAM.RamEval.simprocs`), and the given simp lemmas. It is
`simp +decide only [l₁, …, lₙ, args]` for the lemmas `l₁, …, lₙ` with which `ram_eval_simp_set`
filled `set`, but it does not index them again. -/
scoped syntax (name := ramEvalSimp) "ram_eval_simp " ident
  " [" Lean.Parser.Tactic.simpArg,* "]" : tactic

/-- Internal: fill the empty simp set `set` with the entries that `simp only [names]` builds from
the simp lemmas and definitions `names`, in their order, so that `ram_eval_simp set [args]` is
`simp +decide only [names, args]`. Simplification procedures belong in
`Cslib.WordRAM.RamEval.simprocs`. -/
scoped syntax (name := ramEvalSimpSet) "ram_eval_simp_set " ident " [" ident,* "]" : command

namespace RamEval

open Lean Meta Elab Tactic

/-- The simplification procedures of `ram_eval` and `ram_exact_eval`, in the order in which they
are added, with `true` for those that rewrite after visiting the subterms (`post`). They are added
by name on each call, since the builtin ones cannot be tagged into a simp set in a module. -/
meta def simprocs : List (Name × Bool) :=
  [(``Cslib.WordRAM.reduceFits, true), (``reduceIte, false), (``Nat.reduceAdd, true),
    (``Nat.reduceMul, true), (``Nat.reduceSub, true), (``Nat.reduceDiv, true),
    (``Nat.reduceMod, true), (``Nat.reducePow, true), (``Nat.reduceAnd, true),
    (``Nat.reduceOr, true), (``Nat.reduceXor, true), (``Nat.reduceShiftLeft, true),
    (``Nat.reduceShiftRight, true), (``Nat.reduceLT, true), (``Nat.reduceLeDiff, true),
    (``Nat.reduceEqDiff, true)]

/-- The simp context of `ram_eval_simp set [args]`, given `stx := simp +decide only [args]`: the
context that `mkSimpContext` builds for `simp +decide only [l₁, …, lₙ, args]`, where
`ram_eval_simp_set` filled `set` with `l₁, …, lₙ`, and `simprocs` come among the `lᵢ`. The theorems
of `set` are taken as indexed, and `args` are elaborated into the same tree, so `simp` searches one
tree, as it does for the literal list. -/
meta def mkContext (set : Name) (stx : TSyntax `tactic) : TacticM MkSimpContextResult := do
  let some ext ← getSimpExtension? set | throwError "ram_eval: unknown simp set `{set}`"
  let mut procs : Simp.Simprocs := {}
  for (proc, post) in simprocs do
    procs ← procs.add proc post
  let { config, userConfig } ← elabSimpConfig stx.raw[1] (kind := .simp)
  let ctx ← Simp.mkContext (config := config) (userConfig := userConfig)
    (simpTheorems := #[← ext.getTheorems]) (← getSimpCongrTheorems)
  let r ← elabSimpArgs stx.raw[4] ctx (simprocs := #[procs]) (eraseLocal := false) (kind := .simp)
  return { r with dischargeWrapper := .default }

/-- Run `tac`, restoring the state and returning `false` if it fails. -/
private meta def succeeds (tac : TSyntax `tactic) : TacticM Bool := do
  let s ← saveState
  try evalTactic tac; return true
  catch _ => s.restore; return false

/-- The target of the first unsolved goal, with the context to display it. -/
private meta def firstTarget? : TacticM (Option MessageData) := do
  let g :: _ ← getUnsolvedGoals | return none
  g.withContext do
    return some (← addMessageContext (indentExpr (← instantiateMVars (← g.getType))))

/-- Whether `ex` was raised while elaborating one of the caller's simp lemmas `args`, judged by its
position: an unknown or ill-typed lemma is reported at the lemma. -/
private meta def inSimpArg (args : Array Syntax) (ex : Exception) : Bool := Id.run do
  let some pos := ex.getRef.getPos? | return false
  return args.any fun arg => match arg.getPos?, arg.getTailPos? with
    | some start, some stop => decide (start ≤ pos ∧ pos < stop)
    | _, _ => false

/-- The error of `ram_eval` when `simp` fails on the interpreter goal. -/
private meta def simpFailed (name : String) (args : Array Syntax) (ex : Exception) : MessageData :=
  if inSimpArg args ex then
    m!"{name}: a given simp lemma does not elaborate:{indentD ex.toMessageData}"
  else
    m!"{name}: simp could not evaluate the program:{indentD ex.toMessageData}\nPass the \
      program's definition among the simp lemmas, as in `{name} [myProgram]`."

/-- After both rules of `ram_eval` failed, replay them step by step to name the step that failed:
the goal does not have the form of either rule, a simp lemma in `args` does not elaborate, `simp`
fails, the program does not run to completion, or `omega` does not prove the instruction bound. -/
private meta def explain (name : String) (fuel : TSyntax `num) (simpCall : TSyntax `tactic)
    (args : Array Syntax) : TacticM (Option MessageData) := withoutRecover do
  let g ← getMainGoal
  if ← succeeds (← `(tactic| apply Cslib.WordRAM.ExecWithin.of_eval (fuel := $fuel))) then
    let h :: rest ← getUnsolvedGoals | return none
    setGoals [h]
    try evalTactic simpCall
    catch ex => return some (simpFailed name args ex)
    discard <| succeeds (← `(tactic| rfl))
    if let g :: _ ← getUnsolvedGoals then
      if let some (_, lhs, _) := (← instantiateMVars (← g.getType)).eq? then
        if lhs.isAppOf ``Option.none then
          return some m!"{name}: the interpreter returns `none`: the program faults (a written \
            value does not fit a word, an exact operation is undefined, or it samples with \
            `rand`), or a loop needs more iterations than allowed, as in `{name} 3`."
    if let some t ← firstTarget? then
      return some m!"{name}: symbolic execution did not finish; there remains{t}\nPass the \
        definitions of called programs and facts that decide the remaining branches and `Fits` \
        conditions among the simp lemmas, or allow more loop iterations, as in `{name} 3`."
    setGoals rest
    discard <| succeeds (← `(tactic| omega))
    if let some t ← firstTarget? then
      return some m!"{name}: the program runs to completion, but `omega` could not prove the \
        instruction bound{t}"
    return none
  if ← succeeds (← `(tactic| apply Cslib.WordRAM.Exec.of_eval (fuel := $fuel))) then
    try evalTactic simpCall
    catch ex => return some (simpFailed name args ex)
    return none
  g.withContext do
    return some m!"{name}: expected a goal `ExecWithin w c x y T` or `Exec w c x y T`, got\
      {indentExpr (← instantiateMVars (← g.getType))}"

end RamEval

open Lean Elab Tactic in
scoped elab_rules : tactic
  | `(tactic| ram_eval_simp $set:ident [$args,*]) => withMainContext do withSimpDiagnostics do
    let r@{ ctx, simprocs, dischargeWrapper, .. } ← RamEval.mkContext set.getId.eraseMacroScopes
      (← `(tactic| simp +decide only [$args,*]))
    let stats ← dischargeWrapper.with fun discharge? =>
      withLoopChecking r do
        simpLocation ctx simprocs discharge? (.targets #[] true)
    return stats.diag

-- The entries are those of `elabSimpArgs` for a lemma or definition given by name, built as the
-- `[simp]` attribute builds them for a global entry, under `withExporting` and with a public prefix
-- for auxiliary names, so that the auxiliary lemmas of preprocessed statements are public.
open Lean Meta Elab Command in
scoped elab_rules : command
  | `(command| ram_eval_simp_set $set:ident [$names,*]) => do
    let set := set.getId.eraseMacroScopes
    let some ext ← liftCoreM (getSimpExtension? set) | throwError "unknown simp set `{set}`"
    unless (ext.getState (← getEnv)).lemmaNames.isEmpty do
      throwError "the simp set `{set}` is already filled"
    let entries ← liftTermElabM <| withDeclNameForAuxNaming (`Cslib.WordRAM.RamEval ++ set) <|
        withExporting do
      let mut entries : Array SimpEntry := #[]
      for builtin in Tactic.simpOnlyBuiltins do
        entries := entries ++ (← mkSimpTheoremFromConst builtin).map .thm
      for name in names.getElems do
        let declName ← realizeGlobalConstNoOverloadWithInfo name
        if ← Simp.isSimproc declName then
          throwErrorAt name "`{.ofConstName declName}` is a simproc; add it to \
            `Cslib.WordRAM.RamEval.simprocs`"
        if ← isProp (← getConstVal declName).type then
          entries := entries ++ (← mkSimpTheoremFromConst declName).map .thm
        else
          entries := entries ++ (← mkSimpEntryOfDeclToUnfold declName)
      return entries
    for entry in entries do
      ext.add entry .global

open Lean Elab Tactic in
scoped elab_rules : tactic
  | `(tactic| ram_eval_core $name:str $n:num $set:ident [$args,*]) => do
    let simpCall ← `(tactic| ram_eval_simp $set [$args,*])
    try
      evalTactic (← `(tactic|
        first
        | (apply Cslib.WordRAM.ExecWithin.of_eval (fuel := $n)
           · $simpCall:tactic
             try rfl
           · try omega)
        | (apply Cslib.WordRAM.Exec.of_eval (fuel := $n)
           $simpCall:tactic
           try rfl)))
    catch ex =>
      unless ex matches .error .. do throw ex
      -- Without error recovery, as under `try` and `first`, the message is discarded, so an
      -- expected failure does not pay for the replay.
      unless (← read).recover do throw ex
      let s ← saveState
      -- The replay may exhaust the heartbeats left; the original error is then reported.
      let msg? ← tryCatchRuntimeEx
        (RamEval.explain name.getString n simpCall (args.getElems.map (·.raw))) fun _ => pure none
      s.restore
      let some msg := msg? | throw ex
      throwError msg

/-- Internal: fill the simp set `set` of `ram_eval` (`ram_eval_simps`) or `ram_exact_eval`
(`ram_exact_eval_simps`), given the simp lemmas `basis` that evaluate the instructions of the
basis. The simplification procedures among the lemmas are `Cslib.WordRAM.RamEval.simprocs`. -/
scoped syntax (name := ramEvalSimpSetFor) "ram_eval_simp_set_for " ident " [" ident,* "]" : command

scoped macro_rules
  | `(command| ram_eval_simp_set_for $set:ident [$basis,*]) => `(command|
      ram_eval_simp_set $set [Cslib.WordRAM.Code.eval, Cslib.WordRAM.Code.evalLoop,
        Cslib.WordRAM.Op.eval_const, Cslib.WordRAM.Op.eval_copy, Cslib.WordRAM.Op.eval_alu,
        Cslib.WordRAM.Op.eval_load, Cslib.WordRAM.Op.eval_store, $basis,*,
        Cslib.WordRAM.Data.put, Cslib.WordRAM.fits_zero,
        Cslib.WordRAM.Cond.holds_eq, Cslib.WordRAM.Cond.holds_lt,
        Cslib.WordRAM.Data.set_regs, Cslib.WordRAM.Data.set_mem,
        Cslib.WordRAM.Data.write_regs, Cslib.WordRAM.Data.write_mem, Function.update_self,
        Function.update_apply, bind, Option.map_some, Option.bind_some, Option.map_none,
        Option.bind_none])

ram_eval_simp_set_for ram_eval_simps
  [Cslib.WordRAM.Op.eval_bin, Cslib.WordRAM.Op.eval_width,
    Cslib.WordRAM.Basis.standard_interp_bin, Cslib.WordRAM.Basis.standard_interp_width,
    Cslib.WordRAM.BinOp.eval]

end Cslib.WordRAM

end
