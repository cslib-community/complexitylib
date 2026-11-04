/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.SourceBounds
import Mathlib.Data.List.GetD

/-!
# Admitted dirty caller with aliased original matrices

The complete solver is called at valid geometry. All three original spans alias, its workspace
contains nonzero dirty words, and the selector bank contains 717. The proof connects the same
actual final state to the prefix, halt, verdict, global scan bound and protected caller frame.
No enormous complete interpreter evaluation or supplied source execution is used.
-/

namespace ComplexityTests.WordRAMCallableFixedPrimeCaller

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.WordRAM.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage

private def base (N : ℕ) : ℕ := N * N + 1024
private def oldBound (N : ℕ) : ℕ := base N + 4096
private def zeros (N : ℕ) : List ℤ := List.replicate (3 * (N * N)) 0
private def caller (N : ℕ) : Data 640 :=
  { regs := fun j =>
      if j.val = 600 then N else if j.val = 601 then 16 else if j.val = 602 then 1
      else if j.val = 603 then 3 else if j.val = 604 then 1 else if j.val = 605 then 1
      else if j.val = 606 then 1 else if j.val = 607 then base N else 717
    mem := fun q => if q < base N then 0 else 99 }
private def width (N : ℕ) : ℕ :=
  CallableFixedPrime.admissionWidth N (D 2) 1 3 (CallableFixedPrime.rawTotal N (zeros N))
    (base N) (oldBound N)

private theorem caller_reg_bound (N : ℕ) (i : Fin 640) : (caller N).regs i ≤ oldBound N := by
  have hn : N ≤ N * N + 1024 := by nlinarith
  dsimp only [caller, oldBound, base]
  split_ifs <;> omega

private theorem caller_mem_bound (N q : ℕ) : (caller N).mem q ≤ oldBound N := by
  change (if q < base N then 0 else 99) ≤ oldBound N
  split <;> dsimp only [oldBound, base] <;> omega

/-- A fully admitted dirty caller; original arrays may alias and low selector registers survive. -/
private theorem dirty_alias (N : ℕ) (hgeo : D 2 ^ 18 ≤ N) :
    ∃ y : Data 640, ∃ t : ℕ,
      Runs (width N) (CallableFixedPrime.program.program CallableFixedPrime.Reg.found)
        ⟨0, caller N⟩ ⟨CallableFixedPrime.program.size, y⟩ t ∧
      Executes (width N) (CallableFixedPrime.program.program CallableFixedPrime.Reg.found)
        ⟨0, caller N⟩ 1 (t + 1) ∧
      y.regs CallableFixedPrime.Reg.found = 1 ∧
      y.regs CallableFixedPrime.Reg.scans ≤ 1 ∧
      y.regs 0 = 717 ∧ y.regs 159 = 717 ∧ y.regs CallableFixedPrime.Reg.ab = 1 ∧
      ∀ q, q < base N ∨
        base N + CallableFixedPrime.windowSize N (D 2) 1 3
          (CallableFixedPrime.rawTotal N (zeros N)) ≤ q → y.mem q = (caller N).mem q := by
  have hp : 3 ∈ Nat.sqrtPrimeWindow (D 2) :=
    Nat.mem_sqrtPrimeWindow_iff_sq.mpr ⟨by decide, by decide, by decide⟩
  have hregs := caller_reg_bound N
  have hmem := caller_mem_bound N
  have hbounded : (caller N).Bounded (width N) :=
    CallableFixedPrime.original_bounded (caller N) hregs hmem le_rfl
  have hfit : Fits (width N) (base N +
      4 * CallableFixedPrime.windowSize N (D 2) 1 3
        (CallableFixedPrime.rawTotal N (zeros N)) + 1024) :=
    (CallableFixedPrime.admission_fits (le_refl (width N))).of_le (by omega)
  have hval0 (q : ℕ) : (zeros N).getD q 0 = 0 :=
    List.getElem?_getD_replicate_default_eq _ _ _
  have hread (q : ℕ) (hq : q < N * N) : (caller N).mem (1 + q) =
      Signed.encode ((zeros N).getD q 0) := by
    have hq' : 1 + q < base N := by dsimp only [base]; omega
    rw [hval0]
    change (if 1 + q < base N then 0 else 99) = Signed.encode 0
    simp only [ite_eq_left hq', Signed.encode, Int.natAbs_zero,
      lt_self_iff_false, ite_eq_right (not_false)]
  have hread' (q : ℕ) (hq : q < N * N) : (caller N).mem (1 + q) =
      Signed.encode ((zeros N).getD (N * N + q) 0) := by
    simpa only [hval0] using hread q hq
  have hread'' (q : ℕ) (hq : q < N * N) : (caller N).mem (1 + q) =
      Signed.encode ((zeros N).getD (2 * (N * N) + q) 0) := by
    simpa only [hval0] using hread q hq
  have hargs : (caller N).regs CallableFixedPrime.Reg.n = N ∧
      (caller N).regs CallableFixedPrime.Reg.dimension = D 2 ∧
      (caller N).regs CallableFixedPrime.Reg.groups = 1 ∧
      (caller N).regs CallableFixedPrime.Reg.prime = 3 ∧
      (caller N).regs CallableFixedPrime.Reg.base = base N ∧
      (caller N).regs CallableFixedPrime.Reg.ab = 1 ∧
      (caller N).regs CallableFixedPrime.Reg.bc = 1 ∧
      (caller N).regs CallableFixedPrime.Reg.ac = 1 := by
    simp +decide [caller, CallableFixedPrime.Reg.n, CallableFixedPrime.Reg.dimension,
      CallableFixedPrime.Reg.groups, CallableFixedPrime.Reg.prime, CallableFixedPrime.Reg.base,
      CallableFixedPrime.Reg.ab, CallableFixedPrime.Reg.bc, CallableFixedPrime.Reg.ac, D]
  obtain ⟨hn, hd, hg, hp', hb, hab, hbc, hac⟩ := hargs
  obtain ⟨a, hout, y, he, yb, yf, ys, yiff, yw, frame, regs⟩ :=
    CallableFixedPrime.exec (m := 2) (zeros N) (by simp only [zeros, List.length_replicate])
      (by decide) (by decide) hp hgeo (caller N) hn hd hg hp' hb
      (by rw [hab]; dsimp only [base]; omega)
      (by rw [hbc]; dsimp only [base]; omega)
      (by rw [hac]; dsimp only [base]; omega)
      (by simpa only [hab] using hread) (by simpa only [hbc] using hread')
      (by simpa only [hac] using hread'') hbounded hfit
  let V := fun q => (zeros N).getD q 0
  have hval (q : ℕ) : V q = 0 := List.getElem?_getD_replicate_default_eq _ _ _
  have hzero : HasZeroTriangle (fun u v : Fin N => V (pairIndex (u, v)))
      (fun b c => V (N * N + pairIndex (b, c)))
      (fun u c => V (2 * (N * N) + pairIndex (u, c))) := by
    let v : Fin N := ⟨0, lt_of_lt_of_le (by decide : 0 < D 2 ^ 18) hgeo⟩
    exact ⟨v, v, v, by simp only [hval, zero_add]⟩
  have hf : y.regs CallableFixedPrime.Reg.found = 1 := yiff.mpr hzero
  have hF : falsePositiveCount (fun u v : Fin N => V (pairIndex (u, v)))
      (fun b c => V (N * N + pairIndex (b, c)))
      (fun u c => V (2 * (N * N) + pairIndex (u, c))) 3 = 0 := by
    simp only [falsePositiveCount, IsFalsePositive, weightSum, hval, zero_add,
      ne_eq, not_true_eq_false, false_and, Finset.filter_false, Finset.card_empty]
  obtain ⟨t, ht, hex⟩ := he
  refine ⟨y, t, ?_, ?_, hf, ?_, ?_, ?_, ?_, frame⟩
  · simpa only [Nat.zero_add] using hex.runs (pc := 0)
      (p := CallableFixedPrime.program.program CallableFixedPrime.Reg.found)
      (Program.Contains.self _).append_left
  · simpa only [hf] using hex.executes CallableFixedPrime.Reg.found
  · have hs : y.regs CallableFixedPrime.Reg.scans ≤
        falsePositiveCount (fun u v : Fin N => V (pairIndex (u, v)))
          (fun b c => V (N * N + pairIndex (b, c)))
          (fun u c => V (2 * (N * N) + pairIndex (u, c))) 3 +
          y.regs CallableFixedPrime.Reg.found := ys
    simpa only [hF, hf, zero_add] using hs
  · exact (regs 0 (Or.inl (by decide))).trans rfl
  · exact (regs 159 (Or.inl (by decide))).trans rfl
  · exact (regs CallableFixedPrime.Reg.ab (Or.inr ⟨by decide, by decide⟩)).trans hab

example : ∃ y : Data 640, ∃ t : ℕ,
    Runs (width (16 ^ 18))
      (CallableFixedPrime.program.program CallableFixedPrime.Reg.found)
      ⟨0, caller (16 ^ 18)⟩ ⟨CallableFixedPrime.program.size, y⟩ t ∧
    Executes (width (16 ^ 18))
      (CallableFixedPrime.program.program CallableFixedPrime.Reg.found)
      ⟨0, caller (16 ^ 18)⟩ 1 (t + 1) := by
  obtain ⟨y, t, hr, he, -⟩ := dirty_alias (16 ^ 18) (by decide)
  exact ⟨y, t, hr, he⟩

end ComplexityTests.WordRAMCallableFixedPrimeCaller
