/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Loop
public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Reserve
public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Boundary

/-!
# Composing actual preprocessing with every Convolution call

The original initialized preprocessing execution supplies its actual pointer table, count and
common packed length. Its uniform polynomial word theorem bounds the pointers and signed cells.
The charged native controller then runs the complete caller-safe host on every stored payload.

## Main definitions

* `instanceLength`, `instanceBound`: existing finite reduction length and count bound.
* `cost`: complete host bound with the actual packed length and concrete callee time.

## Main results

* `exec_large`: exact existing distinct-position verdict from the actual preprocessing bank.

This native composition is original and reuses the finite Chan–He reduction correctness theorem.
A fast Exact Triangle backend and the final 1.9992 endpoint remain separate obligations.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum (HasSolution Convolution)

/-- The exact common packed length already produced by native preprocessing. -/
def instanceLength (κ n : ℕ) : ℕ :=
  8 * Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ) ^ 2

/-- The existing finite count bound, with the same original-input magnitude. -/
def instanceBound (κ n : ℕ) : ℕ :=
  (2 * Cslib.Algorithms.ThreeSum.labelBits (2 * (n + 2) ^ κ) ^ 2 + 2) *
    (2 * Nat.log 2 n + 2) ^ 5

/-- Every preprocessing, pointer, matrix, callee and control instruction, including halt.
The callee is charged at the packed side and coarse polynomial filler actually passed to it. -/
def cost {r : ℕ} (κ : ℕ) (c : Host.Callee r) (n : ℕ) : ℕ :=
  ChanHe.Preprocessing.cost κ n + 4 * envelopeExponent κ + 32 +
    instanceBound κ n * (Host.callerTime (instanceLength κ n)
      (c.time (Host.sideLength (instanceLength κ n)) (2 * (n + 2) ^ envelopeExponent κ + 1)) + 12)

/-- Complete ordinary execution after the saved-header prefix, with no solver oracle. -/
theorem exec_large {κ w r : ℕ} (input : List ℤ) (c : Host.Callee r)
    (x : Data (registerCount r))
    (hw : width κ c.widthCoefficient input.length ≤ w) (hn : 3 ≤ input.length)
    (hvalues : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ))
    (hinit : x.comap (preprocessingRegisters r) = Data.init (input.map Signed.encode))
    (hlen : x.regs (controllerRegisters r inputLength) = input.length)
    (hans : x.regs (controllerRegisters r answer) = 0) :
    ∃ y, ExecWithin w (large κ c) x y (cost κ c input.length - 7) ∧
      y.regs (controllerRegisters r answer) ≤ 1 ∧
      (y.regs (controllerRegisters r answer) = 1 ↔
        HasSolution (fun i : Fin input.length => input[i])) := by
  let n := input.length
  let U := (n + 2) ^ κ
  let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * U)
  let V := (n + 2) ^ envelopeExponent κ
  have hppw := (preprocessing_width_le κ c.widthCoefficient n).trans hw
  obtain ⟨out, p, hp, hout, hstored, hnum, htab, hN⟩ :=
    ChanHe.Preprocessing.exec_input input hppw hvalues
  have hpoly : (∀ i, p.regs i < V) ∧ ∀ a, p.mem a < V := by
    obtain ⟨steps, _, he⟩ := hp
    have hr := he.runs (pc := 0) (p := ChanHe.Preprocessing.flatProgram κ)
      (Program.Contains.self _).append_left
    exact ChanHe.Preprocessing.intermediates_polynomial input hppw hvalues hr
  let q := p.extend (preprocessingRegisters r) x
  have hq : ExecWithin w ((ChanHe.Preprocessing.program κ).rename (preprocessingRegisters r))
      x q (ChanHe.Preprocessing.cost κ n - 1) := by
    apply ExecWithin.rename (preprocessing_injective r)
    simpa only [hinit] using hp
  have hqr (i : Fin 128) : q.regs (preprocessingRegisters r i) = p.regs i :=
    (preprocessing_injective r).extend_apply _ _ i
  have hqc (i : Fin 16) : q.regs (controllerRegisters r i) = x.regs (controllerRegisters r i) :=
    extend_preprocessing_controller _ _ i
  obtain ⟨a, ha, hac, hak, hab, ham⟩ := exec_initialize q hw ((hqc _).trans hlen)
    ((hqr _).trans htab) ((hqr _).trans hnum) ((hqr _).trans hN)
  have hnumV : out.length < V := by rw [← hnum]; exact hpoly.1 _
  have htabV : (ChanHe.Preprocessing.arena κ n p.mem).table < V := by
    rw [← htab]
    exact hpoly.1 _
  have hNV : 4 * (2 * m ^ 2) < V := by
    have h := hpoly.1 ChanHe.Preprocessing.packedLength
    rw [hN] at h
    change 8 * m ^ 2 < V at h
    omega
  have haN : Controls (ChanHe.Preprocessing.arena κ n p.mem).table out.length
      (4 * (2 * m ^ 2)) V a := by
    convert hac using 1
    dsimp only [m, U, n]
    omega
  have ham' : a.mem = p.mem := ham
  have haStored : ChanHe.Traversal.StoredNodes (2 * U) (2 * m ^ 2)
      (ChanHe.Preprocessing.arena κ n p.mem).table out a.mem := by
    rw [ham']
    exact hstored
  obtain ⟨y, hy, hyb, hya, _⟩ := exec_calls c out a hw hNV htabV hnumV
    (fun a' => (congrFun ham' a') ▸ hpoly.2 a') haStored haN hak
    (hab.trans ((hqc _).trans hans))
  have heq : 4 * (2 * m ^ 2) = instanceLength κ n := by
    dsimp only [instanceLength, m, U]
    omega
  rw [heq] at hy hya
  have hcount : out.length ≤ instanceBound κ n := by
    have hh := congrArg List.length hout
    simp only [List.length_map] at hh
    rw [hh]
    exact Cslib.Algorithms.ThreeSum.ChanHe.length_instances_le n U _
  refine ⟨y, ?_, hyb, ?_⟩
  · unfold large
    apply (hq.seq (ha.seq hy)).mono
    have hprod := Nat.mul_le_mul_right (Host.callerTime (instanceLength κ n)
      (c.time (Host.sideLength (instanceLength κ n)) (2 * V + 1)) + 12) hcount
    have hpos : 0 < ChanHe.Preprocessing.cost κ n := by
      dsimp only [ChanHe.Preprocessing.cost]
      omega
    dsimp only [cost, V, n] at hprod hpos ⊢
    omega
  · rw [hya]
    have hcorrect := Cslib.Algorithms.ThreeSum.ChanHe.instances_correct n U (by omega)
      (fun i : Fin n => input[i]) (fun i => hvalues _ (List.getElem_mem i.isLt))
    rw [← hout] at hcorrect
    constructor
    · rintro ⟨i, hi⟩
      apply hcorrect.mpr
      refine ⟨out[i.val].2.oneArray (2 * U), List.mem_map.mpr ⟨out[i.val],
        List.getElem_mem i.isLt, rfl⟩, ?_⟩
      simpa only [instanceLength, U, m, n] using hi
    · intro h
      obtain ⟨μ, hμ, hs⟩ := hcorrect.mp h
      obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hμ
      obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hp'
      refine ⟨⟨i, hi⟩, ?_⟩
      rw [heq]
      simpa only [instanceLength, U, m, n] using hs

end Cslib.Algorithms.WordRAM.ThreeSum.Decision
