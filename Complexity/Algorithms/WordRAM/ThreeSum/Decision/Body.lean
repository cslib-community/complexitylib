/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Call
public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Width

/-!
# One actual ordinary-host catalogue iteration

The loaded pointer is read from actual memory, and every local fit follows from the global
logarithmic width and the preprocessing polynomial word bound. Both catalogue and signed payloads
are preserved below the shared matrix workspace.

## Main results

* `exec_body`: one full Convolution call, exact Boolean update, index advance and prefix frame.

These native composition proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision

open Cslib.WordRAM

/-- One pointed-to call, including all index/address/argument/Boolean work. -/
theorem exec_body {r κ n w tab num N H k b : ℕ} (c : Host.Callee r)
    (x : Data (registerCount r)) (μ : ℕ → ℤ)
    (hw : width κ c.widthCoefficient n ≤ w)
    (hN : N < (n + 2) ^ envelopeExponent κ)
    (hH : H ≤ (n + 2) ^ envelopeExponent κ)
    (htable : tab + num ≤ H) (hknum : k < num)
    (hc : Controls tab num N ((n + 2) ^ envelopeExponent κ) H x)
    (hk : x.regs (controllerRegisters r current) = k)
    (hb : x.regs (controllerRegisters r answer) = b) (hb1 : b ≤ 1)
    (hbelow : x.mem (tab + k) + N ≤ H)
    (hvalues : ∀ i < N, |μ i| ≤ (((n + 2) ^ envelopeExponent κ : ℕ) : ℤ))
    (hmem : ∀ i < N, x.mem (x.mem (tab + k) + i) = Signed.encode (μ i)) :
    ∃ y, ExecWithin w (body c.code) x y
        (Host.callerTime N
          (c.time (Host.sideLength N) (2 * (n + 2) ^ envelopeExponent κ + 1)) + 10) ∧
      Controls tab num N ((n + 2) ^ envelopeExponent κ) H y ∧
      y.regs (controllerRegisters r current) = k + 1 ∧
      y.regs (controllerRegisters r answer) ≤ 1 ∧
      (y.regs (controllerRegisters r answer) = 1 ↔
        b = 1 ∨ Cslib.Algorithms.ThreeSum.Convolution N μ) ∧
      ∀ p < H, y.mem p = x.mem p := by
  let V := (n + 2) ^ envelopeExponent κ
  have hfit := (caller_fits hN hH hw).2.2.2.2.2.2.2
  obtain ⟨a, ha, haN, haV, hap, haw, hac, hak, hab, ham⟩ :=
    exec_loadSetup x hc hk (hfit.of_le (by omega))
  obtain ⟨hi, hF, hnF, hμ, hsize, hfill, hsqrt, _⟩ := caller_fits hN hH hw
  have hw2 : w - 2 + 2 = w := by have := (four_le_width κ c.widthCoefficient n).trans hw; omega
  have hcall := Host.exec_at (w := w - 2) c μ
    (a.comap (hostRegisters r)) haN haV hap haw hbelow
    hvalues (fun i hi => (congrFun ham _).trans (hmem i hi)) hi hF hnF
    (fun i hi => hμ _ (hvalues i hi))
    (by simpa only [hw2] using hsize) (by simpa only [hw2] using hfill)
    (by simpa only [hw2] using hsqrt) (by simpa only [hw2] using callee_width hN hH hw)
  rw [hw2] at hcall
  rw [show ∀ t : ℕ, t + 10 = 6 + t + 4 by omega]
  unfold body
  apply ExecWithin.call (host_injective r) ha hcall
  intro q ⟨_, hans, hm⟩ hframe
  have hqc (i : Fin 16) : q.regs (controllerRegisters r i) = a.regs (controllerRegisters r i) :=
    hframe _ (fun j => (controller_ne_host i j).symm)
  have hqctrl : Controls tab num N V H q := hac.congr (fun i _ _ _ _ => hqc i)
  have hqk : q.regs (controllerRegisters r current) = k := (hqc _).trans hak
  have hqa : q.regs (controllerRegisters r answer) = b := (hqc _).trans (hab.trans hb)
  obtain ⟨y, hy, hyk, hya, hyr, hym⟩ := exec_finish q hqctrl.one hqk hqa rfl
    (hfit.of_le (by omega))
  refine ⟨y, hy, hqctrl.congr (fun i hi hj _ _ => hyr i hi hj), hyk, ?_, ?_, ?_⟩
  · rw [hya]
    split_ifs <;> omega
  · rw [hya]
    by_cases hv : q.regs (hostRegisters r (Host.hostRegisters Host.found)) = 1
    · simp only [hv, ↓reduceIte, true_iff]
      exact Or.inr (hans.mp hv)
    · simp only [hv, ↓reduceIte]
      exact (or_iff_left (fun h => hv (hans.mpr h))).symm
  · intro p hp
    exact (congrFun hym p).trans ((hm p hp).trans (congrFun ham p))

end Cslib.Algorithms.WordRAM.ThreeSum.Decision
