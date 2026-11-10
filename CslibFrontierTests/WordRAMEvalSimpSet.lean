/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.WordRAM.ExactNotation

/-!
# The simp sets of `ram_eval` and `ram_exact_eval`

`ram_eval` and `ram_exact_eval` take their lemmas from the simp sets `ram_eval_simps` and
`ram_exact_eval_simps`, indexed once, instead of elaborating a literal lemma list on every call.
These tests check that their simp context is the one that `simp +decide only` builds from the
literal list the tactics used before: the same theorems in the same order, with the same index
keys, priorities, directions, origins and statements; the same definitions to unfold; and the same
simplification procedures. This also holds with the caller's lemmas, local hypotheses, `←`, `↓` and
erasures (`-`), which are elaborated into the same tree. On sample programs, both rewrite the
interpreter goal to the same result.
-/

namespace CslibFrontierTests.WordRAMEvalSimpSet

open Lean Meta Elab Tactic Cslib.WordRAM

/-- The origin of a simp theorem. A term given to `simp` has a fresh name, which is left out. -/
meta def originData : Origin → String
  | .decl n post inv => s!"decl {n} {post} {inv}"
  | .fvar id => s!"fvar {id.name}"
  | .stx _ ref => s!"stx {ref}"
  | .other n => s!"other {n}"

/-- What the attempts of `simp` with a theorem depend on: index keys, priority, direction, origin
and statement. A statement that `simp` preprocesses is proved by an auxiliary lemma whose name
depends on where it was made, so such a proof is compared by its statement. -/
meta def thmData (thm : SimpTheorem) : MetaM String := do
  let (proof, type) ← match thm.proof with
    | .const n _ => do
      let name := if n.components.any (·.toString.startsWith "_simp") then "aux" else toString n
      pure (name, (← getConstInfo n).type)
    | e => do pure ("term", ← inferType e)
  return s!"{reprStr thm.keys} prio {thm.priority} post {thm.post} perm {thm.perm} \
    rfl {thm.rfl} {originData thm.origin} {proof} {thm.levelParams} : {type}"

/-- The theorems of a simp set in the order of its index, and what it unfolds and erases. -/
meta def setData (s : SimpTheorems) : MetaM (Array String) := do
  let sorted (l : List String) := (l.toArray.qsort (· < ·)).toList
  let mut out := #[]
  for thm in s.pre.values do out := out.push s!"pre {← thmData thm}"
  for thm in s.post.values do out := out.push s!"post {← thmData thm}"
  out := out.push s!"unfold {sorted (s.toUnfold.toList.map toString)}"
  out := out.push s!"unfoldThms {sorted (s.toUnfoldThms.toList.map fun (n, ns) => s!"{n} {ns}")}"
  out := out.push s!"erased {sorted (s.erased.toList.map originData)}"
  out := out.push s!"lemmas {sorted (s.lemmaNames.toList.map originData)}"
  return out

/-- The simplification procedures of a set in the order of its index, and its names and erasures. -/
meta def procsData (s : Simp.Simprocs) : Array String := Id.run do
  let sorted (l : List Name) := (l.toArray.map toString |>.qsort (· < ·)).toList
  let mut out := #[]
  for p in s.pre.values do out := out.push s!"pre {p.declName} {reprStr p.keys}"
  for p in s.post.values do out := out.push s!"post {p.declName} {reprStr p.keys}"
  out := out.push s!"names {sorted s.simprocNames.toList} erased {sorted s.erased.toList}"
  return out

/-- Fail at the first entry where `a` (from the literal list) and `b` (from the simp set) differ. -/
meta def compareData (what : String) (a b : Array String) : MetaM Unit := do
  for x in a, y in b do
    unless x == y do throwError "{what} differ:\n{x}\n{y}"
  unless a.size == b.size do
    throwError "{what}: {a.size} entries from the literal list, {b.size} from the simp set"

/-- `simp +decide only` with the literal lemma list of `ram_eval` before its simp sets, given the
lemmas `basis` for the instructions of the basis, and `args`. -/
meta def literalSimp (basis args : Syntax.TSepArray
      [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma]
      ",") :
    TacticM (TSyntax `tactic) :=
  `(tactic|
    simp +decide only [Cslib.WordRAM.Code.eval, Cslib.WordRAM.Code.evalLoop,
      Cslib.WordRAM.Op.eval_const, Cslib.WordRAM.Op.eval_copy, Cslib.WordRAM.Op.eval_alu,
      Cslib.WordRAM.Op.eval_load, Cslib.WordRAM.Op.eval_store, $basis,*,
      Cslib.WordRAM.Data.put, Cslib.WordRAM.fits_zero, Cslib.WordRAM.reduceFits,
      Cslib.WordRAM.Cond.holds_eq, Cslib.WordRAM.Cond.holds_lt,
      Cslib.WordRAM.Data.set_regs, Cslib.WordRAM.Data.set_mem,
      Cslib.WordRAM.Data.write_regs, Cslib.WordRAM.Data.write_mem, Function.update_self,
      Function.update_apply, bind, Option.map_some, Option.bind_some, Option.map_none,
      Option.bind_none, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub,
      Nat.reduceDiv, Nat.reduceMod, Nat.reducePow, Nat.reduceAnd, Nat.reduceOr,
      Nat.reduceXor, Nat.reduceShiftLeft, Nat.reduceShiftRight, Nat.reduceLT,
      Nat.reduceLeDiff, Nat.reduceEqDiff, $args,*])

/-- `check_ram_eval_ctx set [basis] [args]` checks that `ram_eval_simp set [args]` builds the simp
context of `simp +decide only` with the literal list of `ram_eval` before its simp sets, given the
lemmas `basis` for the instructions of the basis, and `args`; and reports its size. -/
syntax "check_ram_eval_ctx " ident " [" Lean.Parser.Tactic.simpArg,* "]"
  " [" Lean.Parser.Tactic.simpArg,* "]" : tactic

elab_rules : tactic
  | `(tactic| check_ram_eval_ctx $set:ident [$basis,*] [$args,*]) => withMainContext do
    let literal ← literalSimp basis args
    let a ← mkSimpContext literal (eraseLocal := false)
    let b ← RamEval.mkContext set.getId (← `(tactic| simp +decide only [$args,*]))
    unless a.ctx.config == b.ctx.config do throwError "configurations differ"
    compareData "theorem arrays" #[s!"{a.ctx.simpTheorems.size}"] #[s!"{b.ctx.simpTheorems.size}"]
    for sa in a.ctx.simpTheorems, sb in b.ctx.simpTheorems do
      compareData "simp theorems" (← setData sa) (← setData sb)
    compareData "simproc arrays" #[s!"{a.simprocs.size}"] #[s!"{b.simprocs.size}"]
    for pa in a.simprocs, pb in b.simprocs do
      compareData "simprocs" (procsData pa) (procsData pb)
    let s := b.ctx.simpTheorems[0]!
    logInfo m!"{s.pre.values.size + s.post.values.size} theorems, \
      {s.toUnfold.toList.length} unfolded, {b.simprocs[0]!.simprocNames.toList.length} simprocs"

/-- `check_ram_eval_goal set [basis] [args] t` checks that `ram_eval_simp set [args]` and
`simp +decide only` with the literal list rewrite the goal `t` to the same result. -/
syntax "check_ram_eval_goal " ident " [" Lean.Parser.Tactic.simpArg,* "]"
  " [" Lean.Parser.Tactic.simpArg,* "]" term : tactic

elab_rules : tactic
  | `(tactic| check_ram_eval_goal $set:ident [$basis,*] [$args,*] $t) => withMainContext do
    let literal ← literalSimp basis args
    let type ← Term.elabTermAndSynthesize t (some (.sort 0))
    let s ← saveState
    let run (tac : TSyntax `tactic) : TacticM (Option Expr) := do
      let g ← mkFreshExprMVar type
      setGoals [g.mvarId!]
      evalTactic tac
      match ← getGoals with
      | [] => return none
      | [g'] => return some (← instantiateMVars (← g'.getType))
      | _ => throwError "expected at most one goal"
    let ra ← run literal
    let rb ← run (← `(tactic| ram_eval_simp $set [$args,*]))
    s.restore
    unless ra == rb do throwError "results differ:\n{ra}\n{rb}"

private abbrev a : Fin 2 := 0
private abbrev b : Fin 2 := 1

private def prog : Code .standard 2 :=
  ram[ a ← #3; if a < b then [ b ← a + b ] else [ b ← #0 ]; *a ← b; a ← *b ]
private def loop : Code .standard 2 := ram[ a ← #0; b ← #2; while a < b do [ a ← width% ] ]
private def under : Code .exact 2 := ram_exact[ a ← #3; b ← a - b; b ← b / a ]

/-! The simp contexts, without and with the caller's lemmas, local hypotheses, `←`, `↓` and
erasures. The checks leave the goal unchanged. -/

/-- info: 42 theorems, 5 unfolded, 16 simprocs -/
#guard_msgs in
set_option linter.unusedTactic false in
example : True := by
  check_ram_eval_ctx ram_eval_simps
    [Cslib.WordRAM.Op.eval_bin, Cslib.WordRAM.Op.eval_width,
      Cslib.WordRAM.Basis.standard_interp_bin, Cslib.WordRAM.Basis.standard_interp_width,
      Cslib.WordRAM.BinOp.eval] []
  trivial

/-- info: 42 theorems, 5 unfolded, 16 simprocs -/
#guard_msgs in
set_option linter.unusedTactic false in
example : True := by
  check_ram_eval_ctx ram_exact_eval_simps
    [Cslib.WordRAM.Op.eval_exactBin, Cslib.WordRAM.Op.eval_exactWidth,
      Cslib.WordRAM.Basis.exact_interp_bin, Cslib.WordRAM.Basis.exact_interp_width,
      Cslib.WordRAM.BinOp.evalExact] []
  trivial

/-- info: 46 theorems, 6 unfolded, 14 simprocs -/
#guard_msgs in
set_option linter.unusedTactic false in
set_option linter.unusedVariables false in
example (h : 2 + 2 = 4) : True := by
  check_ram_eval_ctx ram_eval_simps
    [Cslib.WordRAM.Op.eval_bin, Cslib.WordRAM.Op.eval_width,
      Cslib.WordRAM.Basis.standard_interp_bin, Cslib.WordRAM.Basis.standard_interp_width,
      Cslib.WordRAM.BinOp.eval]
    [prog, h, ← Nat.add_zero, ↓Nat.zero_add, Cslib.WordRAM.Data.set_regs,
      -Function.update_apply, -Nat.reduceMul, -Cslib.WordRAM.reduceFits]
  trivial

/-! The rewritten goals. The checks leave the goal unchanged. -/

set_option linter.unusedTactic false in
set_option linter.unusedVariables false in
example (x : Data 2) : True := by
  check_ram_eval_goal ram_eval_simps
    [Cslib.WordRAM.Op.eval_bin, Cslib.WordRAM.Op.eval_width,
      Cslib.WordRAM.Basis.standard_interp_bin, Cslib.WordRAM.Basis.standard_interp_width,
      Cslib.WordRAM.BinOp.eval] [prog] (Code.eval 8 0 prog x = none)
  check_ram_eval_goal ram_eval_simps
    [Cslib.WordRAM.Op.eval_bin, Cslib.WordRAM.Op.eval_width,
      Cslib.WordRAM.Basis.standard_interp_bin, Cslib.WordRAM.Basis.standard_interp_width,
      Cslib.WordRAM.BinOp.eval] [loop] (Code.eval 8 3 loop x = none)
  check_ram_eval_goal ram_exact_eval_simps
    [Cslib.WordRAM.Op.eval_exactBin, Cslib.WordRAM.Op.eval_exactWidth,
      Cslib.WordRAM.Basis.exact_interp_bin, Cslib.WordRAM.Basis.exact_interp_width,
      Cslib.WordRAM.BinOp.evalExact] [under] (Code.eval 8 0 under x = none)
  trivial

end CslibFrontierTests.WordRAMEvalSimpSet
