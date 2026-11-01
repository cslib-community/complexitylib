/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Callee

/-!
# Arbitrary dirty old-word and alias clients

Correct execution imposes no bound on unused preserved words. The caller below deliberately
retains any old K outside three aliased source spans. Prefix-resource results separately use
the original raw-word bound; they never assert that such arbitrary old words fit every width.
-/

namespace ComplexityTests.WordRAMParameterSelectingCaller

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.WordRAM.ExactTriangle
open ParameterSelecting

private def dirty (K : ℕ) : Data 640 :=
  { regs := fun i => if i.val = 0 ∨ i.val = 1 then 1
      else if i.val = 2 ∨ i.val = 3 ∨ i.val = 4 then 2
      else if i.val = 5 then 4 else K
    mem := fun q => if q = 2 then 0 else K }

/-- All three original arrays alias. Unused words may exceed the physical word range;
the same real program still returns the exact verdict and preserves the sentinel. -/
example (K : ℕ) :
    let values : List ℤ := [0, 0, 0]
    let W := executionWidth 1 1 4 2 2 2 values
    ∃ (p : ℕ) (mem : ℕ → ℕ) (y : Data 640),
      ExecWithin W program (dirty K) y (timeBound 1 p values mem) ∧
      y.regs Reg.result = 1 ∧ y.mem 0 = K ∧ y.regs Reg.free = 4 := by
  obtain ⟨p, mem, y, he, hf, hiff, hp, hz, frame, yn, yF, ya, yb, yc, yf⟩ :=
    exec_at (n := 1) (F := 1) (b := 4) (ap := 2) (bp := 2) (cp := 2)
      [0, 0, 0] (by decide) (by decide) (dirty K) rfl rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide)
      (fun q hq => by
        have : q = 0 := by omega
        subst q
        rfl)
      (fun q hq => by
        have : q = 0 := by omega
        subst q
        rfl)
      (fun q hq => by
        have : q = 0 := by omega
        subst q
        rfl) le_rfl
  refine ⟨p, mem, y, he, hiff.mpr ?_, (frame 0 (Or.inl (by decide))).trans rfl, yf⟩
  exact ⟨0, 0, 0, by norm_num [pairIndex]⟩

private def hostData (K : ℕ) : Data 640 :=
  { regs := fun i => if i.val = 0 then 1 else if i.val = 1 then 2
      else if i.val = 2 then 3 else if i.val = 3 then 4
      else if i.val = 4 then 5 else if i.val = 5 then 6 else K
    mem := fun q => if q = 3 ∨ q = 4 then Signed.encode (-1)
      else if q = 5 then Signed.encode 2 else K }

/-- The actual certified callee is callable with original host0–6, proper ordered signed
arrays and arbitrary unused old words. Every width/span/readback premise is discharged. -/
example (K : ℕ) :
    let W := 123357 * Nat.clog 2 (6 + 2 + 1 + 2)
    ∃ (y : Data 640), ExecWithin W callee.code (hostData K) y (callee.time 1 2) ∧
      y.regs 6 = 1 ∧ y.mem 0 = K := by
  let A := fun _ _ : Fin 1 => (-1 : ℤ)
  let C := fun _ _ : Fin 1 => (2 : ℤ)
  have readA (i j : Fin 1) :
      (hostData K).mem (3 + i.val * 1 + j.val) = Signed.encode (A i j) := by
    simp [hostData, A]
  have readB (i j : Fin 1) :
      (hostData K).mem (4 + i.val * 1 + j.val) = Signed.encode (A i j) := by
    simp [hostData, A]
  have readC (i j : Fin 1) :
      (hostData K).mem (5 + i.val * 1 + j.val) = Signed.encode (C i j) := by
    simp [hostData, C]
  obtain ⟨y, he, hf, hiff, frame⟩ := callee.exec
    (123357 * Nat.clog 2 (6 + 2 + 1 + 2)) 1 2 3 4 5 6 (hostData K) A A C
    (by decide) (by decide) (by decide) (by decide) (by decide) le_rfl
    rfl rfl rfl rfl rfl rfl readA readB readC
    (by intro i j; norm_num [A]) (by intro i j; norm_num [A]) (by intro i j; norm_num [C])
  refine ⟨y, he, hiff.mpr ⟨0, 0, 0, by norm_num [A, C]⟩, ?_⟩
  exact (frame 0 (by decide)).trans rfl

end ComplexityTests.WordRAMParameterSelectingCaller
