/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Call
public import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Continuing symbolic execution through routine contracts

The tactic `wram_call` consumes an existential routine specification at the current `WP` goal.
Its continuation receives the returned state and complete postcondition, with the routine's
instruction allowance already added by `WP.seq`. Resume straight-line execution with `wram_exec`.
The routine's definition stays closed: correctness, safety conditions and its charge come from
the contract, not from symbolic execution of its body.

The renamed form first applies the existing `ExecWithin.rename_post` and retains the caller's
outside-register frame. Both forms normalize memory and register projections of bank views once,
including the facts passed to the continuation. The supplied contract retains all word-fit,
alias, memory and frame obligations.

An existing time-indexed `WP` specification is also accepted; its continuation binds the returned
data, the instruction allowance and its postcondition. At a `WP.Exact` goal, which counts
instructions exactly, the contract states an exact count, `∃ y, Exec w c x y T ∧ P y`, or is a
time-indexed `WP.Exact` specification. No alternative execution or resource model
is added.

When no rule applies, `wram_call` fails with one error that shows the goal and the contracts
accepted there, followed by Lean's error for the rule matching the contract's form, or by the
contract's type when it has no accepted form. The word `renamed` is not reserved: importers may
still use it as an identifier.

## Main results

* `WP.of_spec`, `WP.Exact.of_spec`: continue from a fixed-time existential routine contract.
* `wram_call`: consume a proved routine contract without unfolding its program.
-/

public section

namespace Cslib.WordRAM

/-- Continue from a routine's complete postcondition at its given instruction allowance. -/
theorem WP.of_spec {B : Basis} {r w T : ℕ} {c : Code B r} {x : Data r}
    {P : Data r → Prop} {Q : Data r → ℕ → Prop}
    (h : ∃ y, ExecWithin w c x y T ∧ P y) (hQ : ∀ y, P y → Q y T) :
    WP w c x Q := by
  obtain ⟨y, hy, hP⟩ := h
  exact WP.of_execWithin hy (hQ y hP)

/-- Continue from a routine's complete postcondition at its exact instruction count. -/
theorem WP.Exact.of_spec {B : Basis} {r w T : ℕ} {c : Code B r} {x : Data r}
    {P : Data r → Prop} {Q : Data r → ℕ → Prop}
    (h : ∃ y, Exec w c x y T ∧ P y) (hQ : ∀ y, P y → Q y T) :
    WP.Exact w c x Q := by
  obtain ⟨y, hy, hP⟩ := h
  exact WP.Exact.of_exec hy (hQ y hP)

/-- Apply a fixed-time or time-indexed routine contract and expose its continuation.
Only bank-view projections are normalized; the callee program remains closed. -/
syntax (name := wramCall) "wram_call " term:max " with" (ppSpace colGt rintroPat)+ : tactic

namespace WramCall

open Lean Meta Elab Tactic

/-- The error raised by `tac`, or `none` if it succeeds; the state is restored either way. -/
private meta def errorOf (tac : TSyntax `tactic) : TacticM (Option MessageData) := do
  let s ← saveState
  try withoutRecover (evalTactic tac); s.restore; return none
  catch ex => s.restore; return some ex.toMessageData

/-- The head constant of the contract `h`'s type, with that type for display, when `h` elaborates
on its own; the state is restored. -/
private meta def contractType (h : Term) : TacticM (Option (Name × MessageData)) := do
  let s ← saveState
  try
    let ty ← whnfR (← instantiateMVars (← inferType (← Tactic.elabTerm h none true)))
    let r := (ty.getAppFn.constName, ← addMessageContext (indentExpr ty))
    s.restore; return some r
  catch _ => s.restore; return none

/-- Why no rule of a `wram_call` form applies. `rules` gives, for the head of the goal (`WP` or
`WP.Exact`), a sentence saying which contracts the form accepts there and, for each head of the
contract's type, the rule that applies it; Lean's failure for the rule matching the contract names
the mismatch. -/
private meta def explain (h : Term) (rules : Name → Option (MessageData × List (Name × Syntax))) :
    TacticM MessageData := withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let some (expected, rs) := rules (← whnfR tgt).getAppFn.constName
    | return m!"wram_call: expected a goal `WP w c x Q` or `WP.Exact w c x Q`, which `wram_exec` \
        leaves at a routine, got{indentExpr tgt}"
  let head := m!"wram_call: the contract does not apply to the goal{indentExpr tgt}\n{expected}"
  let ty? ← contractType h
  let pick := match ty? with
    | some (n, _) => rs.lookup n
    | none => rs.head?.map (·.2)
  match pick, ty? with
  | some rule, _ =>
    let err ← errorOf ⟨rule⟩
    return m!"{head}{(err.map fun e => m!"\n{e}").getD m!""}"
  | none, some (_, ty) => return m!"{head}\nThe contract has type{ty}"
  | none, none => return head

/-- Refine the goal with the first of `tacs` that succeeds and run `cont`; if none succeeds,
explain the failure with `rules` (see `explain`). -/
meta def run (h : Term) (tacs : List (TSyntax `tactic)) (cont : TSyntax `tactic)
    (rules : Name → Option (MessageData × List (Name × Syntax))) : TacticM Unit := do
  let rec go : List (TSyntax `tactic) → TacticM Unit
    | [] => do throwError (← explain h rules)
    | tac :: tacs => do
      let s ← saveState
      try withoutRecover (evalTactic tac)
      catch _ => s.restore; go tacs
  go tacs
  evalTactic cont

end WramCall

elab_rules : tactic
  | `(tactic| wram_call $h with $pats*) => do
    let ofSpec ← `(tactic| refine Cslib.WordRAM.WP.of_spec $h ?_)
    let mono ← `(tactic| refine Cslib.WordRAM.WP.mono $h ?_)
    let exactOfSpec ← `(tactic| refine Cslib.WordRAM.WP.Exact.of_spec $h ?_)
    let exactMono ← `(tactic| refine Cslib.WordRAM.WP.Exact.mono $h ?_)
    WramCall.run h [ofSpec, mono, exactOfSpec, exactMono]
      (← `(tactic|
        (rintro $pats*
         try simp only [Cslib.WordRAM.Data.comap_regs, Cslib.WordRAM.Data.comap_mem] at *)))
      fun
      | ``WP => some (m!"The contract must have type `∃ y, ExecWithin w c x y T ∧ P y` or \
          `WP w c x Q'`.",
          [(``Exists, ofSpec), (``WP, mono)])
      | ``WP.Exact => some (m!"The contract must have type `∃ y, Exec w c x y T ∧ P y` or \
          `WP.Exact w c x Q'`.",
          [(``Exists, exactOfSpec), (``WP.Exact, exactMono)])
      | _ => none

/-- Apply a routine contract in an injective bank and retain the outside-register frame. -/
tactic_extension wramCall

@[tactic_alt wramCall]
syntax (name := wramCallRenamed) "wram_call " term:max &" renamed " term:max " with"
  (ppSpace colGt rintroPat)+ : tactic

elab_rules : tactic
  | `(tactic| wram_call $h renamed $hf with $pats*) => do
    let within ← `(tactic|
      refine Cslib.WordRAM.WP.of_spec (Cslib.WordRAM.ExecWithin.rename_post $hf $h) ?_)
    let exact ← `(tactic|
      refine Cslib.WordRAM.WP.Exact.of_spec (Cslib.WordRAM.Exec.rename_post $hf $h) ?_)
    WramCall.run h [within, exact]
      (← `(tactic|
        (rintro $pats*
         try simp only [Cslib.WordRAM.Data.comap_regs, Cslib.WordRAM.Data.comap_mem] at *)))
      fun
      | ``WP => some (m!"For the goal `WP w (c.rename f) x Q`, the contract must have type \
          `∃ y, ExecWithin w c (x.comap f) y T ∧ P y`, with `hf : f.Injective`.",
          [(``Exists, within)])
      | ``WP.Exact => some (m!"For the goal `WP.Exact w (c.rename f) x Q`, the contract must \
          have type `∃ y, Exec w c (x.comap f) y T ∧ P y`, with `hf : f.Injective`.",
          [(``Exists, exact)])
      | _ => none

end Cslib.WordRAM
