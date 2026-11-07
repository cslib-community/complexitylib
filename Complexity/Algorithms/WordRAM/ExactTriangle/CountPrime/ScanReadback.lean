/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Scan
public import Complexity.Algorithms.ExactTriangle.CountPrime.Extraction

/-!
# Actual selected-product scan yields the existing modular triangle count

The signed original weights determine the residue keys and the actual seven-product
coefficient array. Nonnegative coefficient bounds justify native unsigned decoding and every
prefix sum. The caller counter constructs these arrays with its proved native stages; they
are not additional algorithm inputs or an assumed multiplication/counting implementation.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Scan actual computed residue/product readback and obtain precisely the existing modular
triangle count, with original row-major coordinates, zero padding and both residue branches. -/
theorem exec_count_coefficients {w n p k : ℕ} (x : Data 128)
    (wAB wBC wAC : Fin n → Fin n → ℤ) (hpositive : 0 < p) (hpadding : n ≤ 2 ^ k)
    (hn : x.regs Reg.side = n) (hp : x.regs Reg.modulus = p)
    (hc : x.regs Reg.cells = n * n)
    (hresidue : ∀ a b : Fin n, x.mem (x.regs Reg.residueAB + a.val * n + b.val) =
      (wAB a b % (p : ℤ)).toNat)
    (hproduct : ∀ i < 4 ^ k * p, x.mem (x.regs Reg.matrixR + i) = encode
      (Cslib.Algorithms.MatrixMultiplication.Strassen.multiply p k
        (Cslib.Algorithms.ExactTriangle.CountPrime.pCoefficients p wAC)
        (Cslib.Algorithms.ExactTriangle.CountPrime.qCoefficients p wBC) i))
    (h0 : x.regs Reg.zero = 0) (h1 : x.regs Reg.one = 1) (h2 : x.regs Reg.two = 2)
    (htable : ∀ j < 2 ^ k, x.mem (x.regs Reg.spread + j) = Nat.Morton.spread j)
    (hw : Fits w (x.regs Reg.spread + x.regs Reg.residueAB + x.regs Reg.matrixR +
      4 ^ k * p + 4 ^ k + 2 ^ k + n * n * n + n * n + p + 16)) :
    ∃ y, ExecWithin w count x y (22 * (n * n) + 4) ∧ y.mem = x.mem ∧
      y.regs Reg.result = Cslib.Algorithms.ExactTriangle.countZeroMod wAB wBC wAC p ∧
      ∀ j, ¬ScanLocal j → y.regs j = x.regs j := by
  let keys (i : ℕ) : ℕ := if h : i < n * n then
    let q := finProdFinEquiv.symm (⟨i, h⟩ : Fin (n * n))
    (wAB q.1 q.2 % (p : ℤ)).toNat else 0
  let values := Cslib.Algorithms.ExactTriangle.CountPrime.rowMajorCoefficient p k wAB wBC wAC
  have keys_at (i : ℕ) (hi : i < n * n) : keys i =
      (wAB (finProdFinEquiv.symm (⟨i, hi⟩ : Fin (n * n))).1
        (finProdFinEquiv.symm (⟨i, hi⟩ : Fin (n * n))).2 % (p : ℤ)).toNat := by
    simp only [keys, dite_eq_left hi]
  have residue (i : ℕ) (hi : i < n * n) :
      x.mem (x.regs Reg.residueAB + i) = keys i := by
    let q := finProdFinEquiv.symm (⟨i, hi⟩ : Fin (n * n))
    have index : q.1.val * n + q.2.val = i := by
      change i / n * n + i % n = i
      simpa only [Nat.mul_comm] using Nat.div_add_mod i n
    rw [keys_at i hi]
    change x.mem (x.regs Reg.residueAB + i) = (wAB q.1 q.2 % (p : ℤ)).toNat
    simpa only [Nat.add_assoc, index] using hresidue q.1 q.2
  have product (i : ℕ) (hi : i < n * n) :
      x.mem (x.regs Reg.matrixR + Nat.Morton.index (i / n) (i % n) * p +
        (if keys i = 0 then 0 else p - keys i)) = encode (values i : ℤ) := by
    let q := finProdFinEquiv.symm (⟨i, hi⟩ : Fin (n * n))
    have qr : q.1.val = i / n := rfl
    have qc : q.2.val = i % n := rfl
    have key : keys i = (wAB q.1 q.2 % (p : ℤ)).toNat := keys_at i hi
    have val : values i = Cslib.Algorithms.ExactTriangle.CountPrime.pairCoefficient
        p k wAB wBC wAC q.1 q.2 := by
      simp only [values, Cslib.Algorithms.ExactTriangle.CountPrime.rowMajorCoefficient,
        dite_eq_left hi]
      rfl
    have hidx := Nat.Morton.index_lt (q.1.isLt.trans_le hpadding) (q.2.isLt.trans_le hpadding)
    have hr : ((-wAB q.1 q.2) % (p : ℤ)).toNat < p := Int.natMod_lt hpositive.ne'
    have hb := Nat.mul_le_mul_right p (Nat.succ_le_of_lt hidx)
    rw [Nat.succ_mul] at hb
    have entry := hproduct (Nat.Morton.index q.1 q.2 * p +
      ((-wAB q.1 q.2) % (p : ℤ)).toNat) ((Nat.add_lt_add_left hr _).trans_le hb)
    rw [← Cslib.Algorithms.ExactTriangle.CountPrime.pairCoefficient_cast
      hpositive.ne' hpadding wAB wBC wAC q.1 q.2] at entry
    simpa only [Nat.add_assoc, qr, qc, val, key, Int.toNat_neg_emod hpositive] using entry
  obtain ⟨y, he, memory, result, regs⟩ := exec_count x keys values hn hp hc hpadding
    (by intro i hi; rw [keys_at i hi]; exact Int.natMod_lt hpositive.ne')
    (fun _ _ => Cslib.Algorithms.ExactTriangle.CountPrime.rowMajorCoefficient_le
      hpositive.ne' hpadding wAB wBC wAC)
    residue product h0 h1 h2 htable hw
  refine ⟨y, he, memory, ?_, regs⟩
  rw [result]
  exact Cslib.Algorithms.ExactTriangle.CountPrime.sum_rowMajorCoefficient
    hpositive.ne' hpadding wAB wBC wAC

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
