/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate
-- vendored: machine assembly from crei/tidy-universal @7f7c0696.
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelIte
import Mathlib.Tactic.Linarith

/-! # A conditional assembled from supplied machine witnesses

This is the machine-witness portion of the existing conditional computability proof. Its constant
absorbs the finite Boolean code and machine overhead; time and workspace remain independent.
-/

@[expose] public section
namespace Turing.MultiTapeTM.Internal

/-- Assemble the existing test/composition/conditional machines at independent branch bounds. -/
theorem conditional {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {encC : Bool ↪ List Bool} {c : α → Bool} {f g : α → β}
    {tc sc tf sf tg sg : α → ℕ} {kc kf kg : ℕ} {Qc Qf Qg : Type}
    [Finite Qc] [Finite Qf] [Finite Qg]
    {tmc : MultiTapeTM kc Bool Qc} {tmf : MultiTapeTM kf Bool Qf}
    {tmg : MultiTapeTM kg Bool Qg}
    (hc : ∀ a, tmc.ComputesTidilyInTimeAndSpace (encIn a) (encC (c a)) (tc a) (sc a))
    (hf : ∀ a : {a // c a = true}, tmf.ComputesTidilyInTimeAndSpace
      (encIn a) (encOut (f a)) (tf a) (sf a))
    (hg : ∀ a : {a // c a = false}, tmg.ComputesTidilyInTimeAndSpace
      (encIn a) (encOut (g a)) (tg a) (sg a)) :
    ∃ C, ∃ (k : ℕ) (Q : Type) (_ : Finite Q) (tm : MultiTapeTM k Bool Q), ∀ a,
      tm.ComputesTidilyInTimeAndSpace (encIn a) (encOut (if c a then f a else g a))
        (tc a + (if c a then tf a else tg a) + C)
        (sc a + (if c a then sf a else sg a) + C) := by
  let τ := eqWordT (encC true)
  have htest (a : α) : (τ.toTM.seq (rewindInput Bool)).ComputesTidilyInTimeAndSpace
      (encC (c a)) (encTest (c a)) (4 * (encC (c a)).length + 8) 0 := by
    convert τ.computesTidily (encC (c a)) using 1
    simp only [τ, eqWordT_run_q₀, encC.injective.eq_iff]
    cases c a <;> simp [encTest_true, encTest_false]
  let l := (encC true).length + (encC false).length
  have hl (a : α) : (encC (c a)).length ≤ l := by cases c a <;> dsimp [l] <;> omega
  let K := 8 * l + 6 * max kc 0 + 40
  have hct (a : α) := ((hc a).comp (htest a) true).mono
    (t' := tc a + K) (s' := sc a + K)
    (by have hb := hl a; dsimp [l] at hb; dsimp [K, l]; omega)
    (by have hb := hl a; dsimp [l] at hb; dsimp [K, l]; omega)
  refine ⟨K + 5 * max (max kc 0 + 2) (max kf kg) + 20,
    _, _, inferInstance, iteTM ((τ.toTM.seq (rewindInput Bool)).comp tmc true) tmf tmg,
    fun a => ?_⟩
  have h := (hct a).ite (tm₁ := tmf) (tm₂ := tmg)
    (y := encOut (if c a then f a else g a))
    (t₁ := tf a) (s₁ := sf a) (t₂ := tg a) (s₂ := sg a)
    (fun hw => by
      have ha : c a = true := by cases ha : c a <;> simp_all [encTest_true, encTest_false]
      simpa [ha] using hf ⟨a, ha⟩)
    (fun hw => by
      have ha : c a = false := by cases ha : c a <;> simp_all [encTest_true, encTest_false]
      simpa [ha] using hg ⟨a, ha⟩)
  refine h.mono ?_ ?_ <;> cases ha : c a <;> simp_all [encTest_true, encTest_false] <;> omega

end Turing.MultiTapeTM.Internal
