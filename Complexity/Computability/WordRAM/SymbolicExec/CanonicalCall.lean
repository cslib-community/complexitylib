/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.RegisterFrame
public import Complexity.Computability.WordRAM.SymbolicExec.Call

/-!
# Canonical continuations of renamed calls

`WP.of_spec_rename` passes the small returned state to a continuation whose caller state is
explicitly `Data.extend`. The optional `wram_call … canonical … with …` form uses this rule.
Outside-bank reads use the original caller; inside-bank reads need the callee's actual output
or preservation facts. Memory is the callee's returned memory, with no implied memory frame.

`Data.reduceExtendRegs` normalizes one read at a time for closed finite register banks in
`wram_exec` and `wram_simp`. It never unfolds the noncomputable `Function.extend` or expands
an entire register function. For symbolic banks, use the explicit read lemmas instead.
-/

public section

namespace Cslib.WordRAM

attribute [wram_simps] Data.comap_regs Data.comap_mem
  Data.extend_mem Matrix.cons_val_zero Matrix.cons_val_one Matrix.cons_val

/-- Continue a renamed fixed-time routine at its canonical caller state, with exact allowance. -/
theorem WP.of_spec_rename {B : Basis} {r s w T : ℕ} {f : Fin r → Fin s}
    (hf : f.Injective) {c : Code B r} {x : Data s}
    {P : Data r → Prop} {Q : Data s → ℕ → Prop}
    (h : ∃ y, ExecWithin w c (x.comap f) y T ∧ P y)
    (hQ : ∀ y, P y → Q (y.extend f x) T) : WP w (c.rename f) x Q := by
  obtain ⟨y, hy, hP⟩ := h
  exact WP.of_execWithin (hy.rename hf) (hQ y hP)

open Lean Meta in
/-- Normalize only the selected read of a closed finite bank. The proof is kernel checked;
unknown banks and register names are left for explicit lemmas. -/
simproc ↓ [wram_simps] Data.reduceExtendRegs (Data.regs _ _) := fun e => do
  let_expr Data.regs s d j := e | return .continue
  let_expr Data.extend r _ f y x := d | return .continue
  let some n ← getNatValue? (← whnf r) | return .continue
  let some jv ← WP.Exec.regValue? s j | return .continue
  for k in [:n] do
    let i ← mkNumeral (mkApp (mkConst ``Fin) r) k
    let some iv ← WP.Exec.regValue? s (mkApp f i) | return .continue
    if iv == jv then
      let hp ← mkAppM ``Function.Injective #[f]
      let some (some hf) ← WP.Exec.decideClosed? hp | return .continue
      let h ← mkDecideProof (← mkEq (mkApp f i) j)
      let proof ← mkAppM ``Data.extend_regs_of_eq #[hf, y, x, i, j, h]
      return .visit { expr := mkApp3 (mkConst ``Data.regs) r y i, proof? := proof }
  let hp := mkAppN (mkConst ``Data.extend_regs_of_forall_ne) #[r, s, f, y, x, j]
  let .forallE _ p _ _ ← inferType hp | return .continue
  let some (some hi) ← WP.Exec.decideClosed? p | return .continue
  return .visit { expr := mkApp3 (mkConst ``Data.regs) s x j, proof? := mkApp hp hi }

/-- Apply a renamed routine contract with its small returned state and canonical caller view
`small.extend bank caller`. -/
tactic_extension wramCall

@[tactic_alt wramCall]
syntax (name := wramCallCanonical) "wram_call " term:max " canonical " term:max " with"
  (ppSpace colGt rintroPat)+ : tactic

macro_rules
  | `(tactic| wram_call $h canonical $hf with $pats*) =>
    `(tactic| (
      refine Cslib.WordRAM.WP.of_spec_rename $hf $h ?_
      rintro $pats*
      try simp only [Cslib.WordRAM.Data.comap_regs, Cslib.WordRAM.Data.comap_mem] at *))

end Cslib.WordRAM
