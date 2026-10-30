/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Structured

/-!
# Native loop invariants with explicit proof state

An invariant may relate the native data to additional mathematical proof state, such as the
represented worklist and emitted output. The decreasing measure then applies directly to that
proof state. It need not be reconstructed by an additional machine program or a choice of
representation from the native data alone.

## Main results

* `ExecWithin.loop_invariant_state`: the native loop rule with explicit proof state and a natural
  decreasing measure, including all loop-control instructions in the bound.

This is an original extension of the existing native invariant/measure rule. The body premise
is actual `ExecWithin` execution of the given native code, not a source execution or time oracle.
-/

@[expose] public section

namespace Cslib.WordRAM

/-- Native loop rule carrying explicit mathematical proof state. The body must execute the
actual native code, preserve the relation and strictly decrease the proof-state measure. -/
theorem ExecWithin.loop_invariant_state {B : Basis} {r w T : ℕ} {σ : Type*}
    (I : σ → Data r → Prop) (μ : σ → ℕ) {cond : Cond r} {body : Code B r}
    (hbody : ∀ s x, I s x → cond.Holds x →
      ∃ s' y, ExecWithin w body x y T ∧ I s' y ∧ μ s' < μ s)
    {s : σ} {x : Data r} (hx : I s x) :
    ∃ s' y, ExecWithin w (.loop cond body) x y (μ s * (T + 2) + 2) ∧
      I s' y ∧ ¬cond.Holds y := by
  have aux : ∀ n, ∀ s x, μ s ≤ n → I s x →
      ∃ s' y, ExecWithin w (.loop cond body) x y (n * (T + 2) + 2) ∧
        I s' y ∧ ¬cond.Holds y := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro s x hμ hI
      by_cases hc : cond.Holds x
      · obtain ⟨s₁, y, hy, hIy, hdec⟩ := hbody s x hI hc
        obtain ⟨s₂, z, hz, hIz, hexit⟩ := ih (μ s₁) (by omega) s₁ y le_rfl hIy
        refine ⟨s₂, z, (ExecWithin.loop_iter hc hy hz).mono ?_, hIz, hexit⟩
        have hm := Nat.mul_le_mul_right (T + 2) (show μ s₁ + 1 ≤ n by omega)
        rw [Nat.add_mul, Nat.one_mul] at hm
        omega
      · exact ⟨s, x, (ExecWithin.loop_exit hc).mono (by omega), hI, hc⟩
  exact aux (μ s) s x le_rfl hx

end Cslib.WordRAM
