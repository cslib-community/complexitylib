/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Notation
public import Complexity.Foundations.Data.Nat.Bitwise.PackedCount

/-!
# Counting packed flags on the word RAM

Three checked instructions count packed zero-or-one fields, using a replication constant,
middle-field divisor, and radix supplied in registers. Keeping the packed input below half
the physical word width makes the entire multiplication legal. Loading and constructing
these constants is separate from the fragment.

## Main definitions

* `Cslib.WordRAM.PackedCount.flags`, `Cslib.WordRAM.PackedCount.ones`,
  `Cslib.WordRAM.PackedCount.divisor`, `Cslib.WordRAM.PackedCount.base`,
  `Cslib.WordRAM.PackedCount.out`: the five registers of the packed-count fragment.
* `Cslib.WordRAM.PackedCount.code`, `Cslib.WordRAM.PackedCount.result`: the three-instruction
  multiplication, division, and remainder program and its final data state.

## Main results

* `Cslib.WordRAM.PackedCount.exec`: the actual instruction count and exact answer.

## References

* [Fredman and Willard, *Surpassing the information theoretic bound
  with fusion trees*][FredmanWillard1993].
-/

@[expose] public section

namespace Cslib.WordRAM.PackedCount

open Cslib.BitString

/-- Packed input flags. -/
abbrev flags : Fin 5 := 0
/-- The all-ones radix word. -/
abbrev ones : Fin 5 := 1
/-- The power selecting the middle field. -/
abbrev divisor : Fin 5 := 2
/-- Field radix. -/
abbrev base : Fin 5 := 3
/-- Product workspace and final count. -/
abbrev out : Fin 5 := 4

/-- Count packed flags with three standard word operations. -/
def code : Code .standard 5 := ram[
  out ← flags * ones;
  out ← out / divisor;
  out ← out % base ]

/-- The full final data, including the overwritten workspace register. -/
def result (x : Data 5) : Data 5 :=
  let product := x.regs flags * x.regs ones
  ((x.set out product).set out (product / x.regs divisor)).set out
    (product / x.regs divisor % x.regs base)

/-- A fully charged count, preserving memory and all input registers. The width bound covers
the product, and `n < 2^e` prevents carry between fields in the arithmetic identity. -/
theorem exec {w e n : ℕ} (f : ℕ → Bool) (x : Data 5) (hn : 0 < n) (hb : n < 2 ^ e)
    (hw : 2 * e * n ≤ w)
    (hf : x.regs flags = packRadix (2 ^ e) n (fun i => (f i).toNat))
    (ho : x.regs ones = packRadix (2 ^ e) n (fun _ => 1))
    (hd : x.regs divisor = (2 ^ e) ^ (n - 1)) (hbase : x.regs base = 2 ^ e) :
    Exec w code x (result x) 3 ∧
      (result x).regs out = ∑ i ∈ Finset.range n, (f i).toNat ∧
      (result x).mem = x.mem := by
  have hβ : 1 < 2 ^ e := by omega
  have hp : packRadix (2 ^ e) n (fun i => (f i).toNat) < (2 ^ e) ^ n := by
    apply packRadix_lt
    intro i _
    cases f i <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  have hones : packRadix (2 ^ e) n (fun _ => 1) < (2 ^ e) ^ n :=
    packRadix_lt _ (fun _ _ => hβ)
  have hprod : Fits w (x.regs flags * x.regs ones) := by
    rw [hf, ho]
    have hm := Nat.mul_lt_mul_of_lt_of_lt hp hones
    have he : (2 ^ e) ^ n * (2 ^ e) ^ n = 2 ^ (2 * e * n) := by
      rw [← pow_add, ← pow_mul]
      congr 1
      simp only [Nat.mul_add, Nat.two_mul, Nat.add_mul]
    rw [he] at hm
    exact hm.trans_le (Nat.pow_le_pow_right (by decide) hw)
  have hdiv : Fits w (x.regs flags * x.regs ones / x.regs divisor) :=
    hprod.of_le (Nat.div_le_self _ _)
  have hmod : Fits w (x.regs flags * x.regs ones / x.regs divisor % x.regs base) :=
    hdiv.of_le (Nat.mod_le _ _)
  refine ⟨?_, ?_, rfl⟩
  · ram_eval [code, result, hprod, hdiv, hmod]
  · simpa only [result, Data.set_regs, Function.update_self, hf, ho, hd, hbase] using
      countPackedFlags f hn hb

end Cslib.WordRAM.PackedCount
