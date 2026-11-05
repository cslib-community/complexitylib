/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
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

## Main definitions

* `iterationSum`: sum a state-dependent charge along a fixed semantic transition.

## Main results

* `ExecWithin.loop_potential_state`: variable charged work paid by an explicit ghost potential.
* `ExecWithin.loop_invariant_state`: the native loop rule with explicit proof state and a natural
  decreasing measure, including all loop-control instructions in the bound.
* `ExecWithin.loop_invariant_state_additive`: same-code bounds with additive control overhead.
* `ExecWithin.loop_invariant_state_charged`: bounded native loops carrying explicit semantic proof
  state and charging state-dependent body work plus one control unit per iteration.

This is an original extension of the existing native invariant/measure rule. The body premise
is actual `ExecWithin` execution of the given native code, not a source execution or time oracle.
-/

@[expose] public section

namespace Cslib.WordRAM

/-- Native loop rule with an explicit proof-state potential. Each actual body execution and
its two loop-control instructions must be paid by the potential decrease. Semantic successor
states and body charges may depend on the reached native state. -/
theorem ExecWithin.loop_potential_state {B : Basis} {r w : ℕ} {σ : Type*}
    (I : σ → Data r → Prop) (μ : σ → ℕ) {cond : Cond r} {body : Code B r}
    (hbody : ∀ s x, I s x → cond.Holds x →
      ∃ s' y t, ExecWithin w body x y t ∧ I s' y ∧ t + 2 + μ s' ≤ μ s)
    {s : σ} {x : Data r} (hx : I s x) :
    ∃ s' y, ExecWithin w (.loop cond body) x y (μ s + 2) ∧
      I s' y ∧ ¬cond.Holds y := by
  have aux : ∀ n, ∀ s x, μ s ≤ n → I s x →
      ∃ s' y, ExecWithin w (.loop cond body) x y (n + 2) ∧
        I s' y ∧ ¬cond.Holds y := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro s x hμ hI
      by_cases hc : cond.Holds x
      · obtain ⟨s₁, y, t, hy, hIy, hpay⟩ := hbody s x hI hc
        have hdec : μ s₁ < n := by omega
        obtain ⟨s₂, z, hz, hIz, hexit⟩ := ih (μ s₁) hdec s₁ y le_rfl hIy
        exact ⟨s₂, z, (ExecWithin.loop_iter hc hy hz).mono (by omega), hIz, hexit⟩
      · exact ⟨s, x, (ExecWithin.loop_exit hc).mono (by omega), hI, hc⟩
  exact aux (μ s) s x le_rfl hx

/-- Native loop rule carrying explicit mathematical proof state. The body must execute the
actual native code, preserve the relation and strictly decrease the proof-state measure. -/
theorem ExecWithin.loop_invariant_state {B : Basis} {r w T : ℕ} {σ : Type*}
    (I : σ → Data r → Prop) (μ : σ → ℕ) {cond : Cond r} {body : Code B r}
    (hbody : ∀ s x, I s x → cond.Holds x →
      ∃ s' y, ExecWithin w body x y T ∧ I s' y ∧ μ s' < μ s)
    {s : σ} {x : Data r} (hx : I s x) :
    ∃ s' y, ExecWithin w (.loop cond body) x y (μ s * (T + 2) + 2) ∧
      I s' y ∧ ¬cond.Holds y := by
  apply ExecWithin.loop_potential_state I (fun s => μ s * (T + 2)) ?_ hx
  intro s x hI hc
  obtain ⟨s', y, he, hIy, hdec⟩ := hbody s x hI hc
  refine ⟨s', y, T, he, hIy, ?_⟩
  have hpay := Nat.mul_le_mul_right (T + 2) (show μ s' + 1 ≤ μ s by omega)
  simp only [Nat.add_mul, Nat.one_mul] at hpay
  omega

/-- Sum a state-dependent charge along a fixed semantic transition. -/
def iterationSum {σ : Type*} (next : σ → σ) (charge : σ → ℕ) : ℕ → σ → ℕ
  | 0, _ => 0
  | n + 1, s => charge s + iterationSum next charge n (next s)

/-- Charge each body at its actual proof state and pay native loop control additively.
The code, register bank and exchange constants are fixed before fuel; no query is required. -/
theorem ExecWithin.loop_invariant_state_additive {σ : Type*} {B : Basis} {r : ℕ}
    {cond : Cond r} {code : Code B r} {w C D : ℕ}
    (I : ℕ → σ → Data r → Prop) (next : σ → σ) (charge : σ → ℕ)
    (hexit : ∀ s x, I 0 s x → ¬cond.Holds x)
    (hbody : ∀ n s x, I (n + 1) s x →
      cond.Holds x ∧ ∃ y, ExecWithin w code x y (C * (charge s + 1) + D) ∧
        I n (next s) y)
    {n : ℕ} {s : σ} {x : Data r} (hx : I n s x) :
    ∃ y, ExecWithin w (.loop cond code) x y
        (C * iterationSum next charge n s + (C + D + 2) * n + 2) ∧
      I 0 ((next^[n]) s) y := by
  induction n generalizing s x with
  | zero =>
    refine ⟨x, (ExecWithin.loop_exit (hexit s x hx)).mono ?_, hx⟩
    simp [iterationSum]
  | succ n ih =>
    obtain ⟨hc, a, ha, hI⟩ := hbody n s x hx
    obtain ⟨y, hy, hIy⟩ := ih hI
    refine ⟨y, (ExecWithin.loop_iter hc ha hy).mono ?_, ?_⟩
    · simp only [iterationSum, Nat.mul_add, Nat.add_mul, Nat.mul_one]
      omega
    · simpa only [Function.iterate_succ_apply] using hIy

/-- A bounded native loop may charge variable body work and one unit per iteration without
issuing a memory query. Its body, register bank and exchange constants are fixed before fuel.
The remaining-fuel relation also carries arbitrary semantic proof state. -/
theorem ExecWithin.loop_invariant_state_charged {σ : Type*} {B : Basis} {r : ℕ}
    {cond : Cond r} {code : Code B r} {w C D : ℕ}
    (I : ℕ → σ → Data r → Prop) (next : σ → σ) (charge : σ → ℕ)
    (hexit : ∀ s x, I 0 s x → ¬cond.Holds x)
    (hbody : ∀ n s x, I (n + 1) s x →
      cond.Holds x ∧ ∃ y, ExecWithin w code x y (C * (charge s + 1) + D) ∧
        I n (next s) y)
    {n : ℕ} {s : σ} {x : Data r} (hx : I n s x) :
    ∃ y, ExecWithin w (.loop cond code) x y
        ((C + D + 2) * (iterationSum next charge n s + n + 1)) ∧
      I 0 ((next^[n]) s) y := by
  obtain ⟨y, hy, hIy⟩ := ExecWithin.loop_invariant_state_additive I next charge hexit hbody hx
  refine ⟨y, hy.mono ?_, hIy⟩
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]
  omega

end Cslib.WordRAM

end
