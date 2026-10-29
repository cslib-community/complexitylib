/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Signed.Arithmetic
public import Complexity.Computability.WordRAM.Copy
import Mathlib.Tactic.NormNum

/-!
# Native Euclidean residue arrays

The input holds signed encodings. The output holds ordinary unsigned residue keys, ready
for histogram construction. In particular a nonnegative encoded integer is explicitly decoded
by division by two before it is used as a histogram index.

## Main definitions

* `Residues.program`: a fixed loop producing Euclidean residue keys.

## Main results

* `Residues.exec`: charged execution preserving the input and all cells outside the output.

## References

* [T. M. Chan and Q. He, *Reducing 3SUM to Convolution-3SUM*][ChanHe2020]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Residues

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Encoded integer input base. -/
abbrev src : Fin 16 := 9
/-- Unsigned residue output base. -/
abbrev dst : Fin 16 := 10
/-- Input length. -/
abbrev len : Fin 16 := 11
/-- Encoded modulus. -/
abbrev modulus : Fin 16 := 12
/-- Loop counter. -/
abbrev idx : Fin 16 := 13
/-- Address scratch. -/
abbrev addr : Fin 16 := 14
/-- Constant one. -/
abbrev one : Fin 16 := 15

/-- The signed remainder block followed by explicit unsigned decoding and a store. -/
def body : Code .standard 16 :=
  .seq (ram[ addr ← src + idx; left ← *addr; right ← modulus ])
    (.seq Signed.modulo (ram[ two ← #2; result ← result / two;
      addr ← dst + idx; *addr ← result; idx ← idx + one ]))

/-- All parameters are supplied at runtime; registers and code are independent
of length and width. -/
def program : Code .standard 16 :=
  .seq (ram[ idx ← #0; one ← #1 ]) (.loop (.lt idx len) body)

/-- Memory after writing a prefix of unsigned residue keys. -/
def memory (mem : ℕ → ℕ) (values : ℕ → ℤ) (M dst k : ℕ) : ℕ → ℕ :=
  fun a => if dst ≤ a ∧ a < dst + k then (values (a - dst) % (M : ℤ)).toNat else mem a

@[simp] theorem memory_zero (mem : ℕ → ℕ) (values : ℕ → ℤ) (M dst : ℕ) :
    memory mem values M dst 0 = mem := by
  funext a
  simp [memory]

private theorem memory_succ (mem : ℕ → ℕ) (values : ℕ → ℤ) (M dst k : ℕ) :
    memory mem values M dst (k + 1) = Function.update (memory mem values M dst k)
      (dst + k) (values k % (M : ℤ)).toNat := by
  funext a
  by_cases ha : a = dst + k
  · subst a
    simp [memory]
  · rw [Function.update_of_ne ha]
    simp only [memory]
    have h : (dst ≤ a ∧ a < dst + (k + 1)) ↔ (dst ≤ a ∧ a < dst + k) := by omega
    simp only [h]

/-- Convert `n` encoded signed integers to unsigned Euclidean residue keys in at most
`23n + 4` native instructions. The modulus is positive and encoded in its parameter register;
addresses are ordinary unsigned words. The final halt is excluded. -/
theorem exec {w M : ℕ} (x : Data 16) (values : ℕ → ℤ) (hM : 0 < M)
    (hmod : GenericRAM.Signed.Fits w (M : ℤ))
    (hmodreg : x.regs modulus = encode (M : ℤ))
    (hfit : ∀ i < x.regs len, GenericRAM.Signed.Fits w (values i))
    (hs : Fits (w + 2) (x.regs src + x.regs len))
    (hd : Fits (w + 2) (x.regs dst + x.regs len))
    (hdisj : x.regs src + x.regs len ≤ x.regs dst)
    (hinput : ∀ i < x.regs len, x.mem (x.regs src + i) = encode (values i)) :
    ∃ y, ExecWithin (w + 2) program x y (23 * x.regs len + 4) ∧
      y.mem = memory x.mem values M (x.regs dst) (x.regs len) ∧
      (∀ i, 9 ≤ i.val ∧ i.val ≤ 12 → y.regs i = x.regs i) := by
  let I (y : Data 16) : Prop :=
    (∀ i, 9 ≤ i.val ∧ i.val ≤ 12 → y.regs i = x.regs i) ∧ y.regs one = 1 ∧
      y.regs idx ≤ x.regs len ∧
      y.mem = memory x.mem values M (x.regs dst) (y.regs idx)
  have hbody (y : Data 16) (hy : I y) (hc : (Cond.lt idx len).Holds y) :
      ∃ z, ExecWithin (w + 2) body y z 21 ∧ I z ∧
        x.regs len - z.regs idx < x.regs len - y.regs idx := by
    obtain ⟨hr, ho, hi, hm⟩ := hy
    have hl := hr len (by decide)
    have hsrc := hr src (by decide)
    have hdst := hr dst (by decide)
    have hmod' := hr modulus (by decide)
    have hlt : y.regs idx < x.regs len := by simpa only [Cond.holds_lt, hl] using hc
    have hread : y.mem (y.regs src + y.regs idx) = encode (values (y.regs idx)) := by
      rw [hm, hsrc]
      simp only [memory, show ¬(x.regs dst ≤ x.regs src + y.regs idx ∧
        x.regs src + y.regs idx < x.regs dst + y.regs idx) from by omega, ↓reduceIte]
      exact hinput _ hlt
    have ha : Fits (w + 2) (y.regs src + y.regs idx) := hs.of_le (by rw [hsrc]; omega)
    let p := ((y.set addr (y.regs src + y.regs idx)).set left
      (encode (values (y.regs idx)))).set right (encode (M : ℤ))
    have hp : ExecWithin (w + 2)
        (ram[ addr ← src + idx; left ← *addr; right ← modulus ]) y p 3 := by
      ram_eval [p, ha, hread, hmod', hmodreg, addr, src, idx, left, right, modulus, Fin.mk.injEq]
    obtain ⟨z, hz, hzval, hzmem, hzreg⟩ := Signed.exec_modulo (hfit _ hlt) hmod p
      (by simp +decide [p, left, right]) (by simp [p])
    have hzr (i : Fin 16) (hi : 9 ≤ i.val) : z.regs i = p.regs i := hzreg i (Or.inr hi)
    have hzi : z.regs idx = y.regs idx := by
      simpa +decide [p, idx, addr, left, right] using hzr idx (by decide)
    have hzo : z.regs one = 1 := by
      simpa +decide [p, one, addr, left, right] using (hzr one (by decide)).trans
        (show p.regs one = 1 by simpa +decide [p, one, addr, left, right] using ho)
    have hzd : z.regs dst = x.regs dst := by
      simpa +decide [p, dst, addr, left, right] using (hzr dst (by decide)).trans
        (show p.regs dst = x.regs dst by simpa +decide [p, dst, addr, left, right] using hdst)
    have hnonneg := Int.emod_nonneg (values (y.regs idx)) (show (M : ℤ) ≠ 0 by omega)
    have hdecode : z.regs result / 2 = (values (y.regs idx) % (M : ℤ)).toNat := by
      rw [hzval, GenericRAM.Signed.Arithmetic.eval, encode_div_two]
      omega
    have hb : Fits (w + 2) (z.regs dst + z.regs idx) := hd.of_le (by rw [hzd, hzi]; omega)
    have hn : Fits (w + 2) (z.regs idx + 1) := hs.of_le (by rw [hzi]; omega)
    have htwo : Fits (w + 2) 2 := (show Fits 2 2 from by decide).mono (by omega)
    have hrem : Fits (w + 2) (z.regs result / 2) := by
      rw [hdecode]
      have hlt' := Int.emod_lt_of_pos (values (y.regs idx)) (show (0 : ℤ) < M by omega)
      exact ((encode_fits hmod).mono (by omega)).of_le (by
        simp only [encode, Int.natAbs_natCast, show ¬(M : ℤ) < 0 from by omega, ↓reduceIte]
        omega)
    refine ⟨?q, ?run, ?inv, ?decrease⟩
    case run =>
      have htail : ExecWithin (w + 2)
          (ram[ two ← #2; result ← result / two; addr ← dst + idx;
            *addr ← result; idx ← idx + one ]) z ?q 5 := by
        ram_eval [htwo, hrem, hb, hn, hzo, two, result, addr, dst, idx, one, Fin.mk.injEq]
      exact (hp.seq (hz.seq htail))
    case inv =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i hi
        have hip : p.regs i = y.regs i := by
          have hia : i ≠ addr := by intro h; subst i; norm_num [addr] at hi
          have hil : i ≠ left := by intro h; subst i; norm_num [left] at hi
          have hir : i ≠ right := by intro h; subst i; norm_num [right] at hi
          simp only [p, Data.set_regs, Function.update_of_ne hia, Function.update_of_ne hil,
            Function.update_of_ne hir]
        have hia : i ≠ addr := by intro h; subst i; norm_num [addr] at hi
        have hii : i ≠ idx := by intro h; subst i; norm_num [idx] at hi
        have hit : i ≠ two := by intro h; subst i; norm_num [two] at hi
        have hir : i ≠ result := by intro h; subst i; norm_num [result] at hi
        simpa only [Data.set_regs, Data.write_regs, Function.update_of_ne hia,
          Function.update_of_ne hii, Function.update_of_ne hit, Function.update_of_ne hir]
          using (hzr i hi.1).trans (hip.trans (hr i hi))
      · simpa +decide [Function.update_apply] using hzo
      · simpa +decide [Function.update_apply, hzi, hzo] using Nat.succ_le_of_lt hlt
      · simp only [Data.set_mem, Data.write_mem, Data.set_regs, Function.update_apply]
        rw [hdecode, hzmem]
        change Function.update y.mem (z.regs dst + z.regs idx)
          (values (y.regs idx) % (M : ℤ)).toNat = _
        rw [hm, hzd, hzi, ← memory_succ]
        rfl
    case decrease =>
      change x.regs len - (z.regs idx + 1) < x.regs len - y.regs idx
      rw [hzi]
      omega
  let x₀ := (x.set idx 0).set one 1
  have hx₀ : I x₀ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      have hio : i ≠ one := by intro h; subst i; norm_num [one] at hi
      have hii : i ≠ idx := by intro h; subst i; norm_num [idx] at hi
      simp only [x₀, Data.set_regs, Function.update_of_ne hio, Function.update_of_ne hii]
    · simp [x₀]
    · simp +decide [x₀, idx, one]
    · simp +decide [x₀, idx, one]
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I
    (fun y => x.regs len - y.regs idx) hbody hx₀
  obtain ⟨hr, ho, hi, hm⟩ := hy
  have hl := hr len (by decide)
  have hend : y.regs idx = x.regs len := by
    simp only [Cond.holds_lt, hl] at hc
    omega
  refine ⟨y, ?_, by simpa only [hend] using hm, hr⟩
  have h1 : Fits (w + 2) 1 := (show Fits 2 1 from by decide).mono (by omega)
  have hinit : ExecWithin (B := .standard) (w + 2) (ram[ idx ← #0; one ← #1 ]) x x₀ 2 := by
    ram_eval [x₀, h1]
  convert hinit.seq he using 1
  · rfl
  · simp +decide only [x₀, Data.set_regs, Function.update_apply, idx, one, ↓reduceIte,
      Nat.sub_zero]
    omega

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Residues
