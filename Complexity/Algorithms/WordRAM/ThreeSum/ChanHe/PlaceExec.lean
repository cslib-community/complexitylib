/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.Place

/-!
# Charged execution of the native Chan–He placement scan

## Main results

* `Place.tagged_encode`: the unsigned sign/magnitude calculation is the exact tagged integer.

## References

The encoding calculation and native proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Place

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- The encoded tagged value can be computed without a signed primitive. The positive tag
dominates the integer magnitude, so unsigned subtraction cannot truncate a negative result. -/
theorem tagged_encode (neg : Bool) (z : ℤ) (t : ℕ) (ht : z.natAbs ≤ t) :
    encode (signedValue neg z + (t : ℤ)) =
      if encode z % 2 = (if neg then 1 else 0) then
        2 * t + (encode z / 2 + encode z / 2)
      else 2 * t - (encode z / 2 + encode z / 2) := by
  cases neg <;> by_cases hz : z < 0
  · have he : (z.natAbs : ℤ) = -z := Int.ofNat_natAbs_of_nonpos (by omega)
    have hnon : 0 ≤ z + (t : ℤ) := by omega
    simp only [signedValue, Bool.false_eq_true, ↓reduceIte, encode_mod_two, hz,
      encode_div_two, Nat.reduceEqDiff]
    unfold encode
    rw [ite_eq_right (by omega)]
    have hm := Int.natAbs_of_nonneg hnon
    omega
  · have he : (z.natAbs : ℤ) = z := (Int.eq_natAbs_of_nonneg (by omega)).symm
    have hnon : 0 ≤ z + (t : ℤ) := by omega
    simp only [signedValue, Bool.false_eq_true, ↓reduceIte, encode_mod_two, hz,
      encode_div_two]
    unfold encode
    rw [ite_eq_right (by omega)]
    have hm := Int.natAbs_of_nonneg hnon
    omega
  · have he : (z.natAbs : ℤ) = -z := Int.ofNat_natAbs_of_nonpos (by omega)
    have hnon : 0 ≤ -z + (t : ℤ) := by omega
    simp only [signedValue, ↓reduceIte, encode_mod_two, hz, encode_div_two]
    unfold encode
    rw [ite_eq_right (by omega)]
    have hm := Int.natAbs_of_nonneg hnon
    omega
  · have he : (z.natAbs : ℤ) = z := (Int.eq_natAbs_of_nonneg (by omega)).symm
    have hnon : 0 ≤ -z + (t : ℤ) := by omega
    simp only [signedValue, ↓reduceIte, encode_mod_two, hz, encode_div_two, Nat.reduceEqDiff]
    unfold encode
    rw [ite_eq_right (by omega)]
    have hm := Int.natAbs_of_nonneg hnon
    omega

/-- A polynomial envelope for every value and address produced by the placement scan.
The caller supplies a fit for this sum; no fit of an uncomputed output is assumed. -/
def budget (x : Data 32) (M N U t : ℕ) : ℕ :=
  x.regs src + x.regs keys + x.regs hist + x.regs heavy + x.regs packed + x.regs len +
    M + 4 * N + 2 * t + 2 * U + 16


/-- One complete scan round, including classification, sign/tag work, both light stores,
heavy count maintenance and the input cursor increment. -/
theorem exec_body {w M N U t : ℕ} (x : Data 32) (values : ℕ → ℤ) (neg : Bool)
    (hM : 0 < M) (hN : 2 * M ≤ N) (hc : x.regs column < 4)
    (hd : x.regs distance ≤ 4 * M) (ht : U ≤ t)
    (hmod : x.regs modulus = M) (htag : x.regs tag = 2 * t)
    (hneg : x.regs negative = if neg then 1 else 0)
    (h1 : x.regs one = 1) (h2 : x.regs two = 2) (h4 : x.regs four = 4)
    (h0 : x.regs zero = 0) (hi : x.regs idx < x.regs len)
    (hcount : x.regs count = (heavyList values (x.regs len) M (x.regs idx)).length)
    (hbdd : (values (x.regs idx)).natAbs ≤ U)
    (hfit : Fits w (budget x M N U t))
    (hinput : x.mem (x.regs src + x.regs idx) = encode (values (x.regs idx)))
    (hkey : x.mem (x.regs keys + x.regs idx) = residueKey M (values (x.regs idx)))
    (hhist : x.mem (x.regs hist + residueKey M (values (x.regs idx))) =
      Histogram.count (fun j => residueKey M (values j)) (x.regs len)
        (residueKey M (values (x.regs idx)))) :
    ∃ y, ExecWithin w body x y 30 ∧
      y.mem = write x.mem values (x.regs len) M (x.regs heavy) (x.regs packed)
        (x.regs column) (x.regs distance) t neg (x.regs idx) ∧
      y.regs count = (heavyList values (x.regs len) M (x.regs idx + 1)).length ∧
      y.regs idx = x.regs idx + 1 ∧
      (∀ i, (9 ≤ i.val ∧ i.val ≤ 19) ∨ i = one ∨ i = two ∨ i = four ∨ i = zero →
        y.regs i = x.regs i) := by
  let k := x.regs idx
  let n := x.regs len
  let r := residueKey M (values k)
  let c := Histogram.count (fun j => residueKey M (values j)) n r
  have hr : r < M := residueKey_lt hM _
  have hr' : targetKey M neg (values k) < M := by
    rw [targetKey_eq hM]
    exact residueKey_lt hM _
  have f (v : ℕ) (hv : v ≤ budget x M N U t) : Fits w v := hfit.of_le hv
  have fone : Fits w 1 := f _ (by dsimp only [budget]; omega)
  have fzero : Fits w 0 := fits_zero _
  have fs : Fits w (x.regs src + k) := f _ (by dsimp only [budget, k]; omega)
  have fk : Fits w (x.regs keys + k) := f _ (by dsimp only [budget, k]; omega)
  have fh : Fits w (x.regs hist + r) := f _ (by dsimp only [budget]; omega)
  have fo : Fits w (x.regs heavy + x.regs count) := f _ (by
    have hl := length_heavyList_le values n M k
    dsimp only [n, k] at hl
    dsimp only [budget]
    omega)
  have fcount : Fits w (x.regs count + 1) := f _ (by
    have hl := length_heavyList_le values n M k
    dsimp only [n, k] at hl
    dsimp only [budget]
    omega)
  have fi : Fits w (k + 1) := f _ (by dsimp only [budget, k]; omega)
  have fm : Fits w (M - r) := f _ (by dsimp only [budget]; omega)
  have fr : Fits w ((M - r) % M) := f _ (by
    have := Nat.mod_lt (M - r) hM
    dsimp only [budget]
    omega)
  have fmag : Fits w (values k).natAbs := f _ (by dsimp only [budget, k]; omega)
  have fmag2 : Fits w ((values k).natAbs + (values k).natAbs) :=
    f _ (by dsimp only [budget, k]; omega)
  have fsign : Fits w (encode (values k) % 2) := f _ (by
    have := Nat.mod_lt (encode (values k)) (by decide : 0 < 2)
    dsimp only [budget]
    omega)
  have fadd : Fits w (2 * t + ((values k).natAbs + (values k).natAbs)) :=
    f _ (by dsimp only [budget, k]; omega)
  have fsub : Fits w (2 * t - ((values k).natAbs + (values k).natAbs)) :=
    f _ (by dsimp only [budget]; omega)
  have fa : Fits w (4 * targetKey M neg (values k)) :=
    f _ (by dsimp only [budget]; omega)
  have fb : Fits w (x.regs packed + 4 * targetKey M neg (values k)) :=
    f _ (by dsimp only [budget]; omega)
  have fc : Fits w (x.regs packed + 4 * targetKey M neg (values k) + x.regs column) :=
    f _ (by dsimp only [budget]; omega)
  have fd : Fits w (x.regs packed + 4 * targetKey M neg (values k) + x.regs column +
      x.regs distance) := f _ (by dsimp only [budget]; omega)
  have hv := tagged_encode neg (values k) t (hbdd.trans ht)
  have hcp : 0 < c := count_residue_pos values n M (show k < n from hi)
  by_cases hh : 1 < c
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left
    · ram_eval [body, heavyCode, src, keys, idx, hist, addr, key, bucketSize, value, one,
        heavy, count, Fin.mk.injEq, h1, hinput, hkey, hhist, hh,
        fs, fk, fh, fo, fcount, fi, k, n, r, c]
    · simp [write, hh, k, n, r, c, hcount]
    · simp +decide [heavyList, hh, k, n, r, c, hcount, count, idx]
    · simp +decide [idx]
    · intro i hi
      fin_cases i <;> norm_num [one, two, four, zero] at hi <;> rfl
  · have hc1 : c = 1 := by omega
    cases neg <;> by_cases hs : values k < 0
    all_goals
      simp only [targetKey, Bool.false_eq_true, ↓reduceIte] at fa fb fc fd
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      rotate_left
      · ram_eval [body, lightCode, src, keys, idx, hist, addr, key, bucketSize, value,
          one, two, four, zero, modulus, negative, tag, magnitude, sign, packed, column,
          distance, Fin.mk.injEq, h1, h2, h4, h0, hmod, htag, hneg, hinput, hkey, hhist,
          hh, hc1, hs, encode_div_two, encode_mod_two, fs, fk, fh, fi, fm, fr, fmag,
          fmag2, fsign, fadd, fsub, fone, fzero, fa, fb, fc, fd, targetKey, k, n, r, c]
      · simp only [write, show ¬1 < Histogram.count (fun i => residueKey M (values i))
          (x.regs len) (residueKey M (values (x.regs idx))) from hh, ↓reduceIte]
        simp only [Data.set_mem, Data.write_mem]
        simp +decide [targetKey, k, hs, encode_div_two, encode_mod_two, hv]
      · simp +decide [heavyList, hh, k, n, r, c, hcount, count, idx]
      · simp +decide [idx]
      · intro i hi
        fin_cases i <;> norm_num [one, two, four, zero] at hi <;> rfl


/-- Complete native placement in at most `32n+8` instructions, excluding halt. All input,
residue and histogram reads are proved from the memory frame, rather than assumed anew at
iterations. The heavy block precedes the packed block, which precedes the counting workspace. -/
theorem exec {w M N U t : ℕ} (x : Data 32) (values : ℕ → ℤ) (neg : Bool)
    (hM : 0 < M) (hN : 2 * M ≤ N) (hc : x.regs column < 4)
    (hd : x.regs distance ≤ 4 * M) (ht : U ≤ t)
    (hmod : x.regs modulus = M) (htag : x.regs tag = 2 * t)
    (hneg : x.regs negative = if neg then 1 else 0)
    (hbdd : ∀ i < x.regs len, (values i).natAbs ≤ U)
    (hfit : Fits w (budget x M N U t))
    (hsh : x.regs src + x.regs len ≤ x.regs heavy)
    (hhp : x.regs heavy + x.regs len ≤ x.regs packed)
    (hpk : x.regs packed + 4 * N ≤ x.regs keys)
    (hkh : x.regs keys + x.regs len ≤ x.regs hist)
    (hinput : ∀ i < x.regs len, x.mem (x.regs src + i) = encode (values i))
    (hkey : ∀ i < x.regs len, x.mem (x.regs keys + i) = residueKey M (values i))
    (hhist : ∀ r < M, x.mem (x.regs hist + r) =
      Histogram.count (fun j => residueKey M (values j)) (x.regs len) r) :
    ∃ y, ExecWithin w program x y (32 * x.regs len + 8) ∧
      y.mem = memory x.mem values (x.regs len) M (x.regs heavy) (x.regs packed)
        (x.regs column) (x.regs distance) t neg (x.regs len) ∧
      y.regs count = (heavyList values (x.regs len) M (x.regs len)).length ∧
      ∀ i, 9 ≤ i.val ∧ i.val ≤ 19 → y.regs i = x.regs i := by
  let P (i : Fin 32) : Prop := 9 ≤ i.val ∧ i.val ≤ 19
  let I (y : Data 32) : Prop :=
    (∀ i, P i → y.regs i = x.regs i) ∧ y.regs one = 1 ∧ y.regs two = 2 ∧
      y.regs four = 4 ∧ y.regs zero = 0 ∧ y.regs idx ≤ x.regs len ∧
      y.regs count = (heavyList values (x.regs len) M (y.regs idx)).length ∧
      y.mem = memory x.mem values (x.regs len) M (x.regs heavy) (x.regs packed)
        (x.regs column) (x.regs distance) t neg (y.regs idx)
  have hbody (y : Data 32) (hy : I y) (hcond : (Cond.lt idx len).Holds y) :
      ∃ z, ExecWithin w body y z 30 ∧ I z ∧
        x.regs len - z.regs idx < x.regs len - y.regs idx := by
    obtain ⟨hr, h1, h2, h4, h0, hi, hcount, hm⟩ := hy
    have hs := hr src (by decide)
    have hk := hr keys (by decide)
    have hl := hr len (by decide)
    have hh := hr hist (by decide)
    have ho := hr heavy (by decide)
    have hp := hr packed (by decide)
    have hcol := hr column (by decide)
    have hdist := hr distance (by decide)
    have hmod' := (hr modulus (by decide)).trans hmod
    have htag' := (hr tag (by decide)).trans htag
    have hneg' := (hr negative (by decide)).trans hneg
    have hlt : y.regs idx < x.regs len := by simpa only [Cond.holds_lt, hl] using hcond
    have hbefore (a : ℕ) (ha : a < x.regs heavy) : y.mem a = x.mem a := by
      rw [hm]
      apply memory_outside _ _ _ _ _ _ _ _ _ N neg hM hN hc hd hi <;> omega
    have hafter (a : ℕ) (ha : x.regs keys ≤ a) : y.mem a = x.mem a := by
      rw [hm]
      apply memory_outside _ _ _ _ _ _ _ _ _ N neg hM hN hc hd hi <;> omega
    obtain ⟨z, he, hzm, hzc, hzi, hzr⟩ := exec_body y values neg hM hN
      (by simpa only [hcol] using hc) (by simpa only [hdist] using hd) ht hmod' htag' hneg'
      h1 h2 h4 h0 (by simpa only [hl] using hlt) (by simpa only [hl] using hcount)
      (hbdd _ hlt)
      (by simpa only [budget, hs, hk, hh, ho, hp, hl] using hfit)
      (by rw [hs, hbefore _ (by omega)]; exact hinput _ hlt)
      (by rw [hk, hafter _ (by omega)]; exact hkey _ hlt)
      (by rw [hh, hl, hafter _ (by omega)]; exact hhist _ (residueKey_lt hM _))
    refine ⟨z, he, ?_, by omega⟩
    refine ⟨fun i hi => (hzr i (Or.inl hi)).trans (hr i hi),
      (hzr one (by simp)).trans h1,
      (hzr two (by simp)).trans h2, (hzr four (by simp)).trans h4,
      (hzr zero (by simp)).trans h0, by omega,
      by simpa only [hl, hzi] using hzc, ?_⟩
    rw [hzm, hl, ho, hp, hcol, hdist, hm, hzi]
    rfl
  let x₀ := (((((x.set idx 0).set count 0).set one 1).set two 2).set four 4).set zero 0
  have hx₀ : I x₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      fin_cases i <;> norm_num [P] at hi <;> rfl
    all_goals simp +decide [x₀, idx, count, one, two, four, zero, heavyList, memory]
  obtain ⟨y, he, hy, hstop⟩ := ExecWithin.loop_invariant I
    (fun y => x.regs len - y.regs idx) hbody hx₀
  obtain ⟨hr, h1, h2, h4, h0, hi, hcount, hm⟩ := hy
  have hend : y.regs idx = x.regs len := by
    have hl := hr len (by decide)
    simp only [Cond.holds_lt, hl] at hstop
    omega
  have f4 : Fits w 4 := hfit.of_le (by dsimp only [budget]; omega)
  have f2 : Fits w 2 := f4.of_le (by decide)
  have f1 : Fits w 1 := f4.of_le (by decide)
  have hinit : ExecWithin (B := .standard) w (ram[
      idx ← #0; count ← #0; one ← #1; two ← #2; four ← #4; zero ← #0 ]) x x₀ 6 := by
    ram_eval [x₀, f1, f2, f4]
  refine ⟨y, ?_, by simpa only [hend] using hm, by simpa only [hend] using hcount, hr⟩
  convert hinit.seq he using 1
  · rfl
  · simp +decide only [x₀, idx, count, one, two, four, zero, Data.set_regs,
      Function.update_apply, ↓reduceIte, Nat.sub_zero]
    omega

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Place
