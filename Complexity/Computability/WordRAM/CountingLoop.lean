/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Structured

/-!
# Constant-cost counting loops

An indexed semantic invariant describes the state after each completed iteration. The native
counter increases by exactly one, and the limit register keeps the fixed endpoint. The rule
derives the counter bounds, decreasing rank and final index from these facts; clients still
prove execution of the actual body, including its word fits and memory semantics.

## Main results

* `ExecWithin.loop_count`: count from the current index to `N` with a body allowance `T`,
  charging `(N - index) * (T + 2) + 2`, including both loop-control instructions per iteration
  and the final test/exit. No one-past-end word-fit premise is required.

This is an original specialization of `ExecWithin.loop_invariant`.
-/

public section

namespace Cslib.WordRAM

/-- Execute a native counting loop with an indexed semantic invariant. The invariant supplies
the unchanged limit register. Each body execution advances the counter by exactly one and
establishes the next semantic state. The bound excludes setup and the final program halt. -/
theorem ExecWithin.loop_count {B : Basis} {r w N T : ℕ} {index limit : Fin r}
    {body : Code B r} (P : ℕ → Data r → Prop)
    (hlimit : ∀ y, P (y.regs index) y → y.regs limit = N)
    (hbody : ∀ y, P (y.regs index) y → y.regs index < N →
      ∃ z, ExecWithin w body y z T ∧ P (y.regs index + 1) z ∧
        z.regs index = y.regs index + 1)
    {x : Data r} (hle : x.regs index ≤ N) (hx : P (x.regs index) x) :
    ∃ y, ExecWithin w (.loop (.lt index limit) body) x y
      ((N - x.regs index) * (T + 2) + 2) ∧ P N y ∧ y.regs index = N := by
  let I (y : Data r) := y.regs index ≤ N ∧ P (y.regs index) y
  obtain ⟨y, hy, hI, hstop⟩ := loop_invariant
    (cond := .lt index limit) (body := body) I (fun y => N - y.regs index) (by
    intro s hs hc
    have hlt : s.regs index < N := by
      simpa only [Cond.holds_lt, hlimit s hs.2] using hc
    obtain ⟨t, ht, hp, hi⟩ := hbody s hs.2 hlt
    refine ⟨t, ht, ⟨by omega, ?_⟩, by omega⟩
    simpa only [hi] using hp) ⟨hle, hx⟩
  have hend : y.regs index = N := by
    have := hI.1
    simp only [Cond.holds_lt, hlimit y hI.2] at hstop
    omega
  exact ⟨y, hy, hend ▸ hI.2, hend⟩

end Cslib.WordRAM
