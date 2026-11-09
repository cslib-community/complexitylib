/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Input
import Complexity.Foundations.Data.Nat.Log

/-!
# Original-input logarithmic width of the callable solver

The computed raw-word sum has a polynomial bound from the original integer weights. Consequently
both the computed virtual modulus and the physical admission have bounds independent of the
physical width. The caller's original placement and raw dirty-word exponent is explicit and may
be different from its integer-weight exponent. These are resource bounds, not algorithm inputs.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime

open Cslib.WordRAM

private theorem scalarSum_le_pow {n d g p A κ : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ A)
    (hd : d ≤ n) (hg : g ≤ n) (hp : p ≤ n) (hA : A ≤ (n + 2) ^ κ) :
    n + d + g + p + rawTotal n values + 4 ≤ (n + 2) ^ (κ + 9) := by
  let B := n + 2
  have hb : 2 ≤ B := by dsimp only [B]; omega
  have hb1 : 1 ≤ B := by omega
  have hnB : n ≤ B := by dsimp only [B]; omega
  have h3 : 3 ≤ B ^ 2 := (by decide : 3 ≤ (2 : ℕ) ^ 2).trans (Nat.pow_le_pow_left hb 2)
  have hA' : A ≤ B ^ κ := hA
  have hκ : 1 ≤ B ^ κ := Nat.one_le_pow _ _ hb1
  have ha : 2 * A + 1 ≤ B ^ (κ + 2) := by
    calc
      _ ≤ 3 * B ^ κ := by omega
      _ ≤ B ^ 2 * B ^ κ := Nat.mul_le_mul_right _ h3
      _ = _ := by ring
  have hn2 : n * n ≤ B ^ 2 := (Nat.mul_le_mul hnB hnB).trans_eq (by ring)
  have ht : rawTotal n values ≤ B ^ (κ + 6) := by
    calc
      _ ≤ 3 * (n * n) * (2 * A + 1) := rawTotal_le values hlen hv
      _ ≤ B ^ 2 * B ^ 2 * B ^ (κ + 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul h3 hn2) ha
      _ = _ := by ring
  have hnE : n ≤ B ^ (κ + 6) := hnB.trans (Nat.le_self_pow (by omega) B)
  have h4 : 4 ≤ B ^ (κ + 6) :=
    (by decide : 4 ≤ (2 : ℕ) ^ 6).trans ((Nat.pow_le_pow_left hb 6).trans
      (Nat.pow_le_pow_right hb1 (by omega)))
  calc
    _ ≤ 6 * B ^ (κ + 6) := by omega
    _ ≤ B ^ 3 * B ^ (κ + 6) := Nat.mul_le_mul_right _
      ((by decide : 6 ≤ (2 : ℕ) ^ 3).trans (Nat.pow_le_pow_left hb 3))
    _ = _ := by ring

/-- Width actually computed by the program, from polynomial original weights and scalar headers. -/
theorem sourceWidth_le_log {n d g p A κ : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ A)
    (hd : d ≤ n) (hg : g ≤ n) (hp : p ≤ n) (hA : A ≤ (n + 2) ^ κ) :
    sourceWidth n d g p (rawTotal n values) ≤
      (6166 * (κ + 9)) * Nat.clog 2 (n + 2) := by
  have he := scalarSum_le_pow values hlen hv hd hg hp hA
  have he' := he.trans (Nat.pow_le_pow_left
    (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) (n + 2)) (κ + 9))
  rw [← Nat.pow_mul] at he'
  have hl := Nat.clog_le_of_le_pow he'
  unfold sourceWidth
  nlinarith only [hl]

/-- The real runtime reservation is polynomial, without any physical-width parameter. -/
theorem windowSize_le_pow {n d g p A κ : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ A)
    (hd : d ≤ n) (hg : g ≤ n) (hp : p ≤ n) (hA : A ≤ (n + 2) ^ κ) :
    windowSize n d g p (rawTotal n values) ≤ (n + 2) ^ (12332 * (κ + 9)) := by
  have hb : 2 ≤ n + 2 := by omega
  have hbase : 2 ^ Nat.clog 2 (n + 2) ≤ (n + 2) ^ 2 :=
    (Nat.pow_clog_le_mul (by decide : 1 < (2 : ℕ)) (by omega : n + 2 ≠ 0)).trans
      (by nlinarith only [hb])
  calc
    _ ≤ 2 ^ ((6166 * (κ + 9)) * Nat.clog 2 (n + 2)) :=
      Nat.pow_le_pow_right (by decide) (sourceWidth_le_log values hlen hv hd hg hp hA)
    _ = (2 ^ Nat.clog 2 (n + 2)) ^ (6166 * (κ + 9)) := by
      rw [← Nat.pow_mul, Nat.mul_comm]
    _ ≤ ((n + 2) ^ 2) ^ (6166 * (κ + 9)) := Nat.pow_le_pow_left hbase _
    _ = _ := by
      rw [← Nat.pow_mul]
      exact congrArg (fun e : ℕ => (n + 2) ^ e)
        (by omega : 2 * (6166 * (κ + 9)) = 12332 * (κ + 9))

private theorem envelope_le_pow {n d g p A κ β b P : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ A)
    (hd : d ≤ n) (hg : g ≤ n) (hp : p ≤ n) (hA : A ≤ (n + 2) ^ κ)
    (hb : b ≤ (n + 2) ^ β) (hP : P ≤ (n + 2) ^ β) :
    b + 4 * windowSize n d g p (rawTotal n values) + P + 1024 ≤
      (n + 2) ^ (12332 * (κ + 9) + β + 13) := by
  let B := n + 2
  let e := 12332 * (κ + 9) + β + 10
  have hb1 : 1 ≤ B := by dsimp only [B]; omega
  have hb2 : 2 ≤ B := by dsimp only [B]; omega
  have hm := (windowSize_le_pow values hlen hv hd hg hp hA).trans
    (Nat.pow_le_pow_right hb1 (show 12332 * (κ + 9) ≤ e by dsimp only [e]; omega))
  have hb' := hb.trans (Nat.pow_le_pow_right hb1 (show β ≤ e by dsimp only [e]; omega))
  have hP' := hP.trans (Nat.pow_le_pow_right hb1 (show β ≤ e by dsimp only [e]; omega))
  have hc : 1024 ≤ B ^ e := (by decide : 1024 ≤ (2 : ℕ) ^ 10).trans
    ((Nat.pow_le_pow_left hb2 10).trans
      (Nat.pow_le_pow_right hb1 (show 10 ≤ e by dsimp only [e]; omega)))
  calc
    _ ≤ 7 * B ^ e := by omega
    _ ≤ B ^ 3 * B ^ e := Nat.mul_le_mul_right _
      ((by decide : 7 ≤ (2 : ℕ) ^ 3).trans (Nat.pow_le_pow_left hb2 3))
    _ = _ := by rw [← pow_add]; congr 1; dsimp only [e]; omega

/-- Positive logarithmic physical threshold. The original caller's placement/dirty-word
exponent β is separate from its original integer-weight exponent κ. -/
theorem admissionWidth_le_log {n d g p A κ β b P : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ A)
    (hd : d ≤ n) (hg : g ≤ n) (hp : p ≤ n) (hA : A ≤ (n + 2) ^ κ)
    (hb : b ≤ (n + 2) ^ β) (hP : P ≤ (n + 2) ^ β) :
    admissionWidth n d g p (rawTotal n values) b P ≤
      (12332 * (κ + 9) + β + 14) * Nat.clog 2 (n + 2) := by
  have he := envelope_le_pow values hlen hv hd hg hp hA hb hP
  have he' := he.trans (Nat.pow_le_pow_left
    (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) (n + 2)) _)
  rw [← Nat.pow_mul] at he'
  have hl := Nat.clog_le_of_le_pow he'
  have hpos : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by decide) (by omega)
  unfold admissionWidth
  nlinarith only [hl, hpos]

/-- All admitted prefixes use a polynomial numerical envelope in the original input size. -/
theorem wordBound_le_pow {n d g p A κ β b P : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ A)
    (hd : d ≤ n) (hg : g ≤ n) (hp : p ≤ n) (hA : A ≤ (n + 2) ^ κ)
    (hb : b ≤ (n + 2) ^ β) (hP : P ≤ (n + 2) ^ β) :
    wordBound n d g p (rawTotal n values) b P ≤
      (n + 2) ^ (12332 * (κ + 9) + β + 15) := by
  have he := envelope_le_pow values hlen hv hd hg hp hA hb hP
  have hc : 4 ≤ (n + 2) ^ 2 :=
    (by decide : 4 ≤ (2 : ℕ) ^ 2).trans (Nat.pow_le_pow_left (by omega : 2 ≤ n + 2) 2)
  calc
    _ ≤ 4 * (n + 2) ^ (12332 * (κ + 9) + β + 13) := Nat.mul_le_mul_left _ he
    _ ≤ (n + 2) ^ 2 * (n + 2) ^ (12332 * (κ + 9) + β + 13) := Nat.mul_le_mul_right _ hc
    _ = _ := by rw [← pow_add]; congr 1; omega

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
