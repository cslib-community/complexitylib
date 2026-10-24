/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Multiword.Arithmetic
public import Complexity.Computability.WordRAM.Multiword.Bank
public import Complexity.Computability.WordRAM.Multiword.Transfer

/-!
# Framed arithmetic on multiword register banks

The bank starts at physical register forty-four. Multiplication uses thirty-six scratch
digits in registers eight through forty-three and copies the low eighteen digits into the
destination. Subtraction copies its minuend into a fresh destination and clears that
destination when a final borrow signals underflow. Both wrappers preserve memory and every
other bank entry.

## Main definitions

* `Bank.multiply`: multiplication through a separate full-product scratch area.
* `Bank.subtract`: copying followed by truncating natural-number subtraction.

## Main results

* `Bank.exec_multiply`: a product smaller than six physical words updates a bank entry in
  exactly 2484 instructions.
* `Bank.exec_subtract`: general natural-number subtraction updates a fresh bank entry in
  at most 151 instructions.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009].
-/

@[expose] public section

namespace Cslib.WordRAM.Multiword.Bank

open Workspace
open Schoolbook (registers rowCost)

variable {n : ℕ}

/-- Low eighteen product digits, in physical registers eight through twenty-five. -/
def productLow (n : ℕ) : List (Fin (capacity n + 4)) :=
  registers 4 18 (by dsimp [capacity]; omega)

/-- High eighteen product digits, in physical registers twenty-six through forty-three. -/
def productHigh (n : ℕ) : List (Fin (capacity n + 4)) :=
  registers 22 18 (by dsimp [capacity]; omega)

private theorem length_productLow (n : ℕ) : (productLow n).length = 18 := by
  simp [productLow, registers]

private theorem length_productHigh (n : ℕ) : (productHigh n).length = 18 := by
  simp [productHigh, registers]

private theorem register_bounds {start len r : ℕ} {h : start + len ≤ r}
    {i : Fin (r + 4)} (hi : i ∈ registers start len h) :
    4 + start ≤ i.val ∧ i.val < 4 + start + len := by
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
  dsimp
  omega

private theorem register_nodup (start len r : ℕ) (h : start + len ≤ r) :
    (registers start len h).Nodup := by
  apply List.nodup_ofFn_ofInjective
  intro i j hij
  apply Fin.ext
  have := congrArg Fin.val hij
  dsimp at this
  omega

private theorem product_bounds {i : Fin (capacity n + 4)}
    (hi : i ∈ productLow n ++ productHigh n) : 8 ≤ i.val ∧ i.val < 44 := by
  rcases List.mem_append.mp hi with hi | hi
  · have := register_bounds hi
    omega
  · have := register_bounds hi
    omega

private theorem product_digits : ∀ i ∈ productLow n ++ productHigh n, IsDigit i := by
  intro i hi
  exact le_trans (by decide) (product_bounds hi).1

private theorem product_nodup : (productLow n ++ productHigh n).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨register_nodup _ _ _ _, register_nodup _ _ _ _, ?_⟩
  intro i hl j hh he
  subst j
  have := register_bounds hl
  have := register_bounds hh
  omega

private theorem product_disjoint (j : Fin n) :
    List.Disjoint (productLow n ++ productHigh n) (regs j) := by
  apply List.disjoint_left.mpr
  intro i hs hj
  have := product_bounds hs
  have := mem_regs hj
  omega

/-- Compute the full scratch product, then copy its low eighteen digits to a bank entry.
The destination may coincide with either source. -/
def multiply (a b d : Fin n) : Code .standard (capacity n + 4) :=
  .seq (Schoolbook.program (regs a) (regs b) (productLow n) (productHigh n))
    (Transfer.copy (productLow n) (regs d))

theorem size_multiply (a b d : Fin n) : (multiply a b d).size = 2484 := by
  have hm := Schoolbook.size_program (regs a) (regs b) (productLow n) (productHigh n)
    ((length_regs b).trans (length_productLow n).symm)
    ((length_productHigh n).trans (length_regs a).symm)
  simp only [length_regs, rowCost] at hm
  simp only [multiply, Code.size, hm,
    Transfer.size_copy _ _ ((length_productLow n).trans (length_regs d).symm), length_regs]

/-- Uniform static code-size bound for multiplication. -/
theorem size_multiply_le (a b d : Fin n) : (multiply a b d).size ≤ 4000 := by
  rw [size_multiply]
  omega

/-- A six-word-bounded exact product can be placed in any bank entry, including a source
entry. The full scratch execution precedes the copy, and all other bank registers survive. -/
theorem exec_multiply {w : ℕ} (hw : 2 ≤ w) (a b d : Fin n)
    (x : Data (capacity n + 4)) {v : Fin n → ℕ} (hx : Encodes w x v)
    (hprod : v a * v b < 2 ^ (6 * w)) :
    ∃ y, Exec w (multiply a b d) x y 2484 ∧
      Encodes w y (Function.update v d (v a * v b)) ∧ y.mem = x.mem := by
  have hdis : List.Disjoint (productLow n ++ productHigh n) (regs a ++ regs b) := by
    apply List.disjoint_left.mpr
    intro i hi hj
    rcases List.mem_append.mp hj with hj | hj
    · exact List.disjoint_left.mp (product_disjoint a) hi hj
    · exact List.disjoint_left.mp (product_disjoint b) hi hj
  obtain ⟨z, hez, hz, hzval, hzf⟩ := Schoolbook.exec_eighteen_framed hw
    (regs a) (regs b) (productLow n) (productHigh n)
    (length_regs a) (length_regs b) (length_productLow n) (length_productHigh n)
    (fun i hi => by
      rcases List.mem_append.mp hi with hi | hi
      · exact digit_regs a i hi
      · exact digit_regs b i hi)
    product_digits product_nodup hdis x (hx a).1 (hx b).1
  rw [(hx a).2, (hx b).2] at hzval
  have hlow : value (radix w) z (productLow n) = v a * v b := by
    have hmod := Nat.ofDigits_mod_pow_eq_ofDigits_take 18
      (by have := one_lt_radix hw; omega : 0 < radix w)
      ((productLow n ++ productHigh n).map z.regs) (by
        intro l hl
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
        exact hz i hi)
    have htake : ((productLow n ++ productHigh n).map z.regs).take 18 =
        (productLow n).map z.regs := by
      have hlenmap : ((productLow n).map z.regs).length = 18 := by
        simp [length_productLow]
      rw [List.map_append, ← hlenmap, List.take_left]
    rw [htake] at hmod
    change value (radix w) z (productLow n ++ productHigh n) % radix w ^ 18 =
      value (radix w) z (productLow n) at hmod
    rw [hzval, Nat.mod_eq_of_lt (hprod.trans_le (six_word_capacity hw))] at hmod
    exact hmod.symm
  have hcopydis : List.Disjoint (regs d) (productLow n) := by
    apply List.disjoint_left.mpr
    intro i hd hl
    exact List.disjoint_left.mp (product_disjoint d) (by simp [hl]) hd
  obtain ⟨y, hey, hym, hyf, hyp⟩ := Transfer.exec_copy (w := w) (productLow n) (regs d)
    ((length_productLow n).trans (length_regs d).symm) (nodup_regs d) hcopydis z
  have hy : Bounded (radix w) y (regs d) := Transfer.bounded_copy hym
    (fun i hi => hz i (by simp [hi]))
  have hyval : value (radix w) y (regs d) = v a * v b :=
    (Transfer.value_copy hym).trans hlow
  have hp (i : Fin (capacity n + 4)) (hi : 44 ≤ i.val) (hid : i ∉ regs d) :
      y.regs i = x.regs i := by
    rw [hyp i hid]
    apply hzf.2 i (by omega)
    intro hs
    have := product_bounds hs
    omega
  refine ⟨y, ?_, encodes_update hx d _ hy hyval hp, hyf.1.trans hzf.1⟩
  simpa only [multiply, length_regs] using hez.seq hey

/-- Copy the minuend to a fresh destination, then subtract with underflow cleared to zero. -/
def subtract (w : ℕ) (a b d : Fin n) : Code .standard (capacity n + 4) :=
  .seq (Transfer.copy (regs a) (regs d))
    (Difference.truncatingProgram w (regs b) (regs d))

theorem size_subtract (w : ℕ) (a b d : Fin n) :
    (subtract w a b d).size = 153 := by
  simp only [subtract, Code.size,
    Transfer.size_copy _ _ ((length_regs a).trans (length_regs d).symm),
    Difference.size_truncatingProgram _ _ _ ((length_regs b).trans (length_regs d).symm),
    length_regs]

/-- Uniform static code-size bound for subtraction. -/
theorem size_subtract_le (w : ℕ) (a b d : Fin n) : (subtract w a b d).size ≤ 4000 := by
  rw [size_subtract]
  omega

/-- General subtraction needs no sign hypothesis. Its destination is distinct from the two
sources; those sources may coincide. Every other bank entry and all memory are preserved. -/
theorem exec_subtract {w : ℕ} (hw : 2 ≤ w) (a b d : Fin n)
    (hda : d ≠ a) (hdb : d ≠ b)
    (x : Data (capacity n + 4)) {v : Fin n → ℕ} (hx : Encodes w x v) :
    ∃ y, ExecWithin w (subtract w a b d) x y 151 ∧
      Encodes w y (Function.update v d (v a - v b)) ∧ y.mem = x.mem := by
  obtain ⟨z, hez, hzm, hzf, hzp⟩ := Transfer.exec_copy (w := w) (regs a) (regs d)
    ((length_regs a).trans (length_regs d).symm) (nodup_regs d) (disjoint_regs hda) x
  have hzb (i : Fin (capacity n + 4)) (hi : i ∈ regs b) : z.regs i = x.regs i :=
    hzp i (fun hd => List.disjoint_left.mp (disjoint_regs hdb) hd hi)
  have hzbval : Multiword.value (radix w) z (regs b) = v b := by
    rw [← (hx b).2]
    unfold value
    exact congrArg (Nat.ofDigits (radix w)) (List.map_congr_left hzb)
  have hzdval : Multiword.value (radix w) z (regs d) = v a :=
    (Transfer.value_copy hzm).trans (hx a).2
  obtain ⟨y, hey, hy, hyval, hyf⟩ := Difference.exec_eighteen_truncating hw (regs b) (regs d)
    (length_regs b) (length_regs d) (digit_regs b) (digit_regs d) (nodup_regs d)
    (disjoint_regs (Ne.symm hdb)) z
    (fun i hi => by rw [hzb i hi]; exact (hx b).1 i hi)
    (Transfer.bounded_copy hzm (hx a).1)
  rw [hzdval, hzbval] at hyval
  have hp (i : Fin (capacity n + 4)) (hi : 44 ≤ i.val) (hid : i ∉ regs d) :
      y.regs i = x.regs i :=
    (hyf.2 i (by omega) hid).trans (hzp i hid)
  refine ⟨y, ?_, encodes_update hx d _ hy hyval hp, hyf.1.trans hzf.1⟩
  simpa only [subtract, length_regs] using hez.within.seq hey

end Cslib.WordRAM.Multiword.Bank
