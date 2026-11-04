/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.SourceBounds
import Mathlib.Data.List.OfFn

/-!
# Original matrix-function clients of the assembled native caller

The existing host supplies three signed arrays and mathematical readback functions. This
rule derives the proof-only row-major list used to index the established resource ledger;
it neither copies that list nor supplies it to the program. Every actual load still uses
the caller's original pointers. Arbitrary unused old words remain unrestricted.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle

private def rowList {n : ℕ} (A : Fin n → Fin n → ℤ) : List ℤ :=
  List.ofFn fun q : Fin (n * n) => A (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2

private theorem rowList_length {n : ℕ} (A : Fin n → Fin n → ℤ) :
    (rowList A).length = n * n := List.length_ofFn

private theorem rowList_get {n q : ℕ} (A : Fin n → Fin n → ℤ) (hq : q < n * n) :
    (rowList A).getD q 0 =
      A (finProdFinEquiv.symm (⟨q, hq⟩ : Fin (n * n))).1
        (finProdFinEquiv.symm (⟨q, hq⟩ : Fin (n * n))).2 := by
  rw [List.getD_eq_getElem _ _ (by simpa only [rowList_length] using hq)]
  simp only [rowList, List.getElem_ofFn]

private theorem rowList_pair {n : ℕ} (A : Fin n → Fin n → ℤ) (i j : Fin n) :
    (rowList A).getD (pairIndex (i, j)) 0 = A i j := by
  have idx : (finProdFinEquiv (i, j)).val = pairIndex (i, j) := by
    simp [finProdFinEquiv, pairIndex, Nat.add_comm, Nat.mul_comm]
  have hi : pairIndex (i, j) < n * n := idx ▸ (finProdFinEquiv (i, j)).isLt
  rw [rowList_get A hi]
  have eqidx : (⟨pairIndex (i, j), hi⟩ : Fin (n * n)) = finProdFinEquiv (i, j) :=
    Fin.ext idx.symm
  simp only [eqidx, Equiv.symm_apply_apply]

/-- Complete native matrix-function caller, using exactly the original host ABI. The
derived list and reference memory index an actual charge, never algorithm arguments. -/
theorem exec_matrices {W n F ap bp cp b : ℕ} (x : Data 640)
    (A B C : Fin n → Fin n → ℤ)
    (xn : x.regs Reg.side = n) (xF : x.regs Reg.bound = F)
    (xap : x.regs Reg.ab = ap) (xbp : x.regs Reg.bc = bp)
    (xcp : x.regs Reg.ac = cp) (xb : x.regs Reg.free = b)
    (hab : ap + n * n ≤ b) (hbc : bp + n * n ≤ b) (hac : cp + n * n ≤ b)
    (vab : ∀ i j, x.mem (ap + i.val * n + j.val) = Signed.encode (A i j))
    (vbc : ∀ i j, x.mem (bp + i.val * n + j.val) = Signed.encode (B i j))
    (vac : ∀ i j, x.mem (cp + i.val * n + j.val) = Signed.encode (C i j))
    (hA : ∀ i j, |A i j| ≤ F) (hB : ∀ i j, |B i j| ≤ F) (hC : ∀ i j, |C i j| ≤ F)
    (hW : 123357 * Nat.clog 2 (b + F + n + 2) ≤ W) :
    ∃ (values : List ℤ) (p : ℕ) (mem : ℕ → ℕ) (y : Data 640),
      values.length = 3 * (n * n) ∧ (∀ z ∈ values, z.natAbs ≤ F) ∧
      (∀ i j, values.getD (pairIndex (i, j)) 0 = A i j) ∧
      (∀ i j, values.getD (n * n + pairIndex (i, j)) 0 = B i j) ∧
      (∀ i j, values.getD (2 * (n * n) + pairIndex (i, j)) 0 = C i j) ∧
      ExecWithin W program x y (timeBound n p values mem) ∧
      (y.regs Reg.result = 0 ∨ y.regs Reg.result = 1) ∧
      (y.regs Reg.result = 1 ↔ HasZeroTriangle A B C) ∧
      (0 < ParameterChoice.blocks n → IsSelectedPrime A B C (ParameterChoice.window n) p) ∧
      (¬0 < ParameterChoice.blocks n → p = 0) ∧
      (∀ q, q < b ∨ workspaceEnd n b values ≤ q → y.mem q = x.mem q) ∧
      y.regs Reg.side = n ∧ y.regs Reg.bound = F ∧ y.regs Reg.ab = ap ∧
      y.regs Reg.bc = bp ∧ y.regs Reg.ac = cp ∧ y.regs Reg.free = b := by
  let values := rowList A ++ (rowList B ++ rowList C)
  have hlen : values.length = 3 * (n * n) := by
    simp only [values, List.length_append, rowList_length]
    omega
  have bounded (M : Fin n → Fin n → ℤ) (hM : ∀ i j, |M i j| ≤ F) :
      ∀ z ∈ rowList M, z.natAbs ≤ F := by
    intro z hz
    obtain ⟨q, hq⟩ := List.mem_ofFn.mp hz
    subst z
    have h := hM (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2
    exact_mod_cast (show ((M (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2).natAbs : ℤ)
      ≤ F by simpa only [Int.natCast_natAbs] using h)
  have hv : ∀ z ∈ values, z.natAbs ≤ F := by
    intro z hz
    rcases List.mem_append.mp hz with h | h
    · exact bounded A hA z h
    · rcases List.mem_append.mp h with h | h
      · exact bounded B hB z h
      · exact bounded C hC z h
  have getA (q : ℕ) (hq : q < n * n) : values.getD q 0 = (rowList A).getD q 0 := by
    exact List.getD_append _ _ _ _ (by simpa only [rowList_length] using hq)
  have getB (q : ℕ) (hq : q < n * n) :
      values.getD (n * n + q) 0 = (rowList B).getD q 0 := by
    dsimp only [values]
    rw [List.getD_append_right _ _ _ _ (by simp only [rowList_length]; omega)]
    simp only [rowList_length, Nat.add_sub_cancel_left]
    exact List.getD_append _ _ _ _ (by simpa only [rowList_length] using hq)
  have getC (q : ℕ) (hq : q < n * n) :
      values.getD (2 * (n * n) + q) 0 = (rowList C).getD q 0 := by
    dsimp only [values]
    rw [List.getD_append_right _ _ _ _ (by simp only [rowList_length]; omega)]
    rw [List.getD_append_right _ _ _ _ (by simp only [rowList_length]; omega)]
    congr 1
    simp only [rowList_length]
    omega
  have pair (q : ℕ) (hq : q < n * n) :
      pairIndex (finProdFinEquiv.symm (⟨q, hq⟩ : Fin (n * n))) = q := by
    have h := congrArg (fun k : Fin (n * n) => k.val)
      (finProdFinEquiv.apply_symm_apply (⟨q, hq⟩ : Fin (n * n)))
    simpa [finProdFinEquiv, pairIndex, Nat.add_comm, Nat.mul_comm] using h
  have word (M : Fin n → Fin n → ℤ) (a : ℕ)
      (read : ∀ i j, x.mem (a + i.val * n + j.val) = Signed.encode (M i j))
      (q : ℕ) (hq : q < n * n) : x.mem (a + q) = Signed.encode ((rowList M).getD q 0) := by
    rw [rowList_get M hq]
    have h := read (finProdFinEquiv.symm (⟨q, hq⟩ : Fin (n * n))).1
      (finProdFinEquiv.symm (⟨q, hq⟩ : Fin (n * n))).2
    have h' : x.mem (a + pairIndex (finProdFinEquiv.symm (⟨q, hq⟩ : Fin (n * n)))) =
        Signed.encode (M (finProdFinEquiv.symm (⟨q, hq⟩ : Fin (n * n))).1
          (finProdFinEquiv.symm (⟨q, hq⟩ : Fin (n * n))).2) := by
      simpa only [pairIndex, Nat.add_assoc] using h
    simpa only [pair q hq] using h'
  obtain ⟨p, mem, y, he, hf, hiff, hp, hz, frame, yn, yf, ya, yb, yc, yfree⟩ :=
    exec_at values hlen hv x xn xF xap xbp xcp xb hab hbc hac
      (fun q hq => by rw [getA q hq]; exact word A ap vab q hq)
      (fun q hq => by rw [getB q hq]; exact word B bp vbc q hq)
      (fun q hq => by rw [getC q hq]; exact word C cp vac q hq)
      ((executionWidth_le_host_log values hlen hv (by omega) (by omega) (by omega)).trans hW)
  have matrixA : (fun i j : Fin n => values.getD (pairIndex (i, j)) 0) = A := by
    funext i j
    rw [getA _ (by simpa only [pairIndex, Fin.coe_mkDivMod, Nat.mul_comm] using
      (Fin.mkDivMod i j).isLt), rowList_pair]
  have matrixB : (fun i j : Fin n => values.getD (n * n + pairIndex (i, j)) 0) = B := by
    funext i j
    rw [getB _ (by simpa only [pairIndex, Fin.coe_mkDivMod, Nat.mul_comm] using
      (Fin.mkDivMod i j).isLt), rowList_pair]
  have matrixC : (fun i j : Fin n => values.getD (2 * (n * n) + pairIndex (i, j)) 0) = C := by
    funext i j
    rw [getC _ (by simpa only [pairIndex, Fin.coe_mkDivMod, Nat.mul_comm] using
      (Fin.mkDivMod i j).isLt), rowList_pair]
  refine ⟨values, p, mem, y, hlen, hv, ?_, ?_, ?_, he, hf, ?_, ?_, hz, frame,
    yn, yf, ya, yb, yc, yfree⟩
  · exact fun i j => congrFun (congrFun matrixA i) j
  · exact fun i j => congrFun (congrFun matrixB i) j
  · exact fun i j => congrFun (congrFun matrixC i) j
  · simpa only [matrixA, matrixB, matrixC] using hiff
  · simpa only [matrixA, matrixB, matrixC] using hp

end Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting
