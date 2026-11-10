/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.Program
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.Width
import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.Registers
import CslibFrontier.Computability.WordRAM.Call

/-!
# Charged in-place Convolution calls during Chan–He traversal

The callback reads the current actual packed pointer and allocation endpoint. Its disjoint
host bank preserves every traversal register, while the existing callee contract protects the
complete memory prefix below that endpoint and permits arbitrary higher scratch writes.

## Main results

* `exec_prepareHost`: four actual argument copies with complete outer-register frames.
* `exec_receive`: actual Boolean accumulation, without a catalogue index or table access.
* `exec_consume`: complete charged host call and the live-prefix/traversal-register frames.

These calling-convention proofs are original.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor

open Cslib.WordRAM

/-- Every argument is copied from the reached runtime state; no layout is supplied for free. -/
theorem exec_prepareHost {r w : ℕ} (x : Data (registerCount r)) :
    ∃ y, ExecWithin w prepareHost x y 4 ∧
      (y.comap (hostRegisters r)).regs (Host.hostRegisters Host.len) =
        x.regs (preprocessingRegisters r ChanHe.Preprocessing.packedLength) ∧
      (y.comap (hostRegisters r)).regs (Host.hostRegisters Host.upper) =
        x.regs (controllerRegisters r envelope) ∧
      (y.comap (hostRegisters r)).regs (Host.hostRegisters Host.base) =
        x.regs (preprocessingRegisters r ChanHe.Traversal.packed) ∧
      (y.comap (hostRegisters r)).regs (Host.hostRegisters Host.matAB) =
        x.regs (preprocessingRegisters r ChanHe.Traversal.heap) ∧
      (∀ i, y.regs (preprocessingRegisters r i) = x.regs (preprocessingRegisters r i)) ∧
      (∀ i, y.regs (controllerRegisters r i) = x.regs (controllerRegisters r i)) ∧
      y.mem = x.mem := by
  let p := preprocessingRegisters r
  let m := controllerRegisters r
  let h := fun i => hostRegisters r (Host.hostRegisters (r := r + 7) i)
  let y := x.set (h Host.len) (x.regs (p ChanHe.Preprocessing.packedLength))
    |>.set (h Host.upper) (x.regs (m envelope))
    |>.set (h Host.base) (x.regs (p ChanHe.Traversal.packed))
    |>.set (h Host.matAB) (x.regs (p ChanHe.Traversal.heap))
  have hh (i j : Fin 64) : h i = h j ↔ i = j :=
    ((host_injective r).comp Host.hostRegisters_injective).eq_iff
  have hph (i : Fin 128) (j : Fin 64) : p i ≠ h j := preprocessing_ne_host i _
  have hmh (i : Fin 16) (j : Fin 64) : m i ≠ h j := controller_ne_host i _
  have he : ExecWithin w prepareHost x y 4 := by
    ram_eval [prepareHost, y, p, m, h, hh, hph, hmh,
      Host.len, Host.upper, Host.base, Host.matAB, Fin.mk.injEq]
  refine ⟨y, he, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · change y.regs (h Host.len) = x.regs (p ChanHe.Preprocessing.packedLength)
    simp +decide [y, h, hh, Host.len, Host.upper, Host.base, Host.matAB]
  · change y.regs (h Host.upper) = x.regs (m envelope)
    simp +decide [y, h, hh, Host.upper, Host.base, Host.matAB]
  · change y.regs (h Host.base) = x.regs (p ChanHe.Traversal.packed)
    simp +decide [y, h, hh, Host.base, Host.matAB]
  · change y.regs (h Host.matAB) = x.regs (p ChanHe.Traversal.heap)
    simp [y, h]
  · intro i
    change y.regs (p i) = x.regs (p i)
    simp only [y, Data.set_regs, Function.update_apply, hph, ↓reduceIte]
  · intro i
    change y.regs (m i) = x.regs (m i)
    simp only [y, Data.set_regs, Function.update_apply, hmh, ↓reduceIte]

/-- Boolean OR costs at most three native instructions and changes no other register or cell. -/
theorem exec_receive {r w b v : ℕ} (x : Data (registerCount r))
    (ho : x.regs (controllerRegisters r one) = 1)
    (hb : x.regs (controllerRegisters r answer) = b)
    (hv : x.regs (hostRegisters r (Host.hostRegisters Host.found)) = v) :
    ∃ y, ExecWithin w receive x y 3 ∧
      y.regs (controllerRegisters r answer) = (if v = 1 then 1 else b) ∧
      (∀ i, i ≠ controllerRegisters r answer → y.regs i = x.regs i) ∧ y.mem = x.mem := by
  let m := controllerRegisters r
  let y := x.set (m answer) (if v = 1 then 1 else b)
  have hm (i j : Fin 16) : m i = m j ↔ i = j := (controller_injective r).eq_iff
  have hmh (i : Fin 16) (j : Fin 64) :
      m i ≠ hostRegisters r (Host.hostRegisters j) := controller_ne_host i _
  have he : ExecWithin w receive x y 3 := by
    by_cases h : v = 1 <;>
      ram_eval [receive, y, m, ho, hb, hv, hm, hmh, h, one, answer, Fin.mk.injEq]
  refine ⟨y, he, ?_, ?_, rfl⟩
  · simp [y, m]
  · intro i hi
    exact Function.update_of_ne hi ..

/-- Invoke the existing certified solver on the current actual packed block, preserving the
entire live prefix and traversal bank. Argument copies and Boolean accumulation are charged. -/
theorem exec_consume {r κ n w N H b : ℕ} (c : Host.Callee r)
    (x : Data (registerCount r)) (μ : ℕ → ℤ)
    (hw : width κ c.widthCoefficient n ≤ w)
    (hN : N < (n + 2) ^ envelopeExponent κ)
    (hH : H ≤ (n + 2) ^ envelopeExponent κ)
    (hlen : x.regs (preprocessingRegisters r ChanHe.Preprocessing.packedLength) = N)
    (hbound : x.regs (controllerRegisters r envelope) = (n + 2) ^ envelopeExponent κ)
    (hheap : x.regs (preprocessingRegisters r ChanHe.Traversal.heap) = H)
    (hone : x.regs (controllerRegisters r one) = 1)
    (hans : x.regs (controllerRegisters r answer) = b) (hb : b ≤ 1)
    (hbelow : x.regs (preprocessingRegisters r ChanHe.Traversal.packed) + N ≤ H)
    (hvalues : ∀ i < N, |μ i| ≤ (((n + 2) ^ envelopeExponent κ : ℕ) : ℤ))
    (hmem : ∀ i < N, x.mem
      (x.regs (preprocessingRegisters r ChanHe.Traversal.packed) + i) = Signed.encode (μ i)) :
    ∃ y, ExecWithin w (consume c.code) x y
        (Host.callerTime N
          (c.time (Host.sideLength N) (2 * (n + 2) ^ envelopeExponent κ + 1)) + 7) ∧
      y.regs (controllerRegisters r answer) ≤ 1 ∧
      (y.regs (controllerRegisters r answer) = 1 ↔
        b = 1 ∨ Cslib.Algorithms.ThreeSum.Convolution N μ) ∧
      (∀ i, y.regs (preprocessingRegisters r i) = x.regs (preprocessingRegisters r i)) ∧
      (∀ i, i ≠ answer →
        y.regs (controllerRegisters r i) = x.regs (controllerRegisters r i)) ∧
      ∀ p < H, y.mem p = x.mem p := by
  obtain ⟨a, ha, haN, haV, hap, haw, hapr, hac, ham⟩ := exec_prepareHost (w := w) x
  obtain ⟨hi, hF, -, hμ, hsize, hfill, hsqrt, _⟩ := caller_fits hN hH hw
  have hw2 : w - 2 + 2 = w := by
    have := (four_le_width κ c.widthCoefficient n).trans hw
    omega
  have hcall := Host.exec_at (w := w - 2) c μ (a.comap (hostRegisters r))
    (haN.trans hlen) (haV.trans hbound) hap (haw.trans hheap) hbelow hvalues
    (fun i hi => (congrFun ham _).trans (hmem i hi)) hi hF
    (fun i hi => hμ _ (hvalues i hi))
    (by simpa only [hw2] using hsize) (by simpa only [hw2] using hfill)
    (by simpa only [hw2] using hsqrt) (by simpa only [hw2] using callee_width hN hH hw)
  rw [hw2] at hcall
  rw [show ∀ t : ℕ, t + 7 = 4 + t + 3 by omega]
  unfold consume
  apply ExecWithin.call (host_injective r) ha hcall
  intro q ⟨_, hqans, hqm⟩ hframe
  have hqp (i : Fin 128) :
      q.regs (preprocessingRegisters r i) = x.regs (preprocessingRegisters r i) :=
    (hframe _ (fun j => (preprocessing_ne_host i j).symm)).trans (hapr i)
  have hqc (i : Fin 16) :
      q.regs (controllerRegisters r i) = x.regs (controllerRegisters r i) :=
    (hframe _ (fun j => (controller_ne_host i j).symm)).trans (hac i)
  obtain ⟨y, hy, hya, hyr, hym⟩ := exec_receive q ((hqc _).trans hone)
    ((hqc _).trans hans) rfl
  refine ⟨y, hy, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hya]
    split_ifs <;> omega
  · rw [hya]
    by_cases hv : q.regs (hostRegisters r (Host.hostRegisters Host.found)) = 1
    · simp only [hv, ↓reduceIte, true_iff]
      exact Or.inr (hqans.mp hv)
    · simp only [hv, ↓reduceIte]
      exact (or_iff_left (fun h => hv (hqans.mpr h))).symm
  · intro i
    exact (hyr _ (controller_ne_preprocessing answer i).symm).trans (hqp i)
  · intro i hi
    have hne : controllerRegisters r i ≠ controllerRegisters r answer :=
      fun he => hi ((controller_injective r) he)
    exact (hyr _ hne).trans (hqc i)
  · intro p hp
    exact (congrFun hym p).trans ((hqm p hp).trans (congrFun ham p))

end Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor
