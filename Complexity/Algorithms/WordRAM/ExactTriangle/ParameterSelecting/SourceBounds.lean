/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Prefix
import Complexity.Foundations.Data.Nat.Log

/-!
# Original-input logarithmic admission for the assembled program

One common scalar base bounds the original dimension, weights and placement. The bounds
include the actual maximum candidate counter padding, signed recursion magnitude, computed
callable window, parameter preparation and small-input arithmetic. They concern numerical
admission and prefix support, not a global running-time exponent.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle

private theorem padding_le {n B : ℕ} (hn : n + 2 ≤ B) :
    2 ^ Nat.clog 2 n ≤ B ^ 2 := by
  have hm := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ))
    (Nat.clog_mono_right 2 (by omega : n ≤ n + 1))
  have hp := Nat.pow_clog_le_mul (by decide : 1 < (2 : ℕ)) (by omega : n + 1 ≠ 0)
  exact (hm.trans hp).trans (by nlinarith)

private theorem window_le_pow {n F B κ : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ F)
    (hn : n + 2 ≤ B) (hF : F ≤ B ^ κ) :
    CallableFixedPrime.windowSize n (ParameterChoice.window n) (ParameterChoice.groups n)
      (Nat.sqrt (ParameterChoice.window n)) (CallableFixedPrime.rawTotal n values) ≤
      B ^ (12332 * (κ + 9)) := by
  have hb : 2 ≤ B := by omega
  have hb1 : 1 ≤ B := by omega
  have hκ : 1 ≤ B ^ κ := Nat.one_le_pow _ _ hb1
  have hnB : n ≤ B := by omega
  have hd : ParameterChoice.window n ≤ B := (ParameterChoice.powers_le n).2.trans (by omega)
  have hg : ParameterChoice.groups n ≤ B := (ParameterChoice.powers_le n).1.trans (by omega)
  have hp : Nat.sqrt (ParameterChoice.window n) ≤ B := (Nat.sqrt_le_self _).trans hd
  have h3 : 3 ≤ B ^ 2 := (by decide : 3 ≤ (2 : ℕ) ^ 2).trans (Nat.pow_le_pow_left hb 2)
  have ha : 2 * F + 1 ≤ B ^ (κ + 2) := by
    calc
      _ ≤ 3 * B ^ κ := by omega
      _ ≤ B ^ 2 * B ^ κ := Nat.mul_le_mul_right _ h3
      _ = _ := by ring
  have hn2 : n * n ≤ B ^ 2 := (Nat.mul_le_mul hnB hnB).trans_eq (by ring)
  have ht : CallableFixedPrime.rawTotal n values ≤ B ^ (κ + 6) := by
    calc
      _ ≤ 3 * (n * n) * (2 * F + 1) := CallableFixedPrime.rawTotal_le values hlen hv
      _ ≤ B ^ 2 * B ^ 2 * B ^ (κ + 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul h3 hn2) ha
      _ = _ := by ring
  have hbase : B ≤ B ^ (κ + 6) := Nat.le_self_pow (by omega) B
  have h4 : 4 ≤ B ^ (κ + 6) := (by decide : 4 ≤ (2 : ℕ) ^ 6).trans
    ((Nat.pow_le_pow_left hb 6).trans (Nat.pow_le_pow_right hb1 (by omega)))
  have hs : n + ParameterChoice.window n + ParameterChoice.groups n +
      Nat.sqrt (ParameterChoice.window n) + CallableFixedPrime.rawTotal n values + 4 ≤
      B ^ (κ + 9) := by
    calc
      _ ≤ 6 * B ^ (κ + 6) := by omega
      _ ≤ B ^ 3 * B ^ (κ + 6) := Nat.mul_le_mul_right _
        ((by decide : 6 ≤ (2 : ℕ) ^ 3).trans (Nat.pow_le_pow_left hb 3))
      _ = _ := by ring
  have hs' := hs.trans (Nat.pow_le_pow_left
    (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) B) _)
  rw [← pow_mul] at hs'
  have hc := Nat.clog_le_of_le_pow hs'
  have hpB : 2 ^ Nat.clog 2 B ≤ B ^ 2 :=
    (Nat.pow_clog_le_mul (by decide : 1 < (2 : ℕ)) (by omega : B ≠ 0)).trans
      (by nlinarith)
  unfold CallableFixedPrime.windowSize CallableFixedPrime.sourceWidth
  calc
    _ ≤ 2 ^ (6166 * (Nat.clog 2 B * (κ + 9))) := Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul_left _ hc)
    _ = (2 ^ Nat.clog 2 B) ^ (6166 * (κ + 9)) := by
      rw [← pow_mul]; congr 1; ring
    _ ≤ (B ^ 2) ^ (6166 * (κ + 9)) := Nat.pow_le_pow_left hpB _
    _ = _ := by
      rw [← pow_mul]
      exact congrArg (fun q : ℕ => B ^ q) (by omega : 2 * (6166 * (κ + 9)) = 12332 * (κ + 9))

/-- Polynomial original scalars and placement bound every intermediate numerical admission.
The common base also permits direct use with a host's address-plus-magnitude logarithm. -/
theorem envelope_le_pow {n F b ap bp cp B κ β : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ F)
    (hn : n + 2 ≤ B) (hF : F ≤ B ^ κ) (hb : b ≤ B ^ β)
    (ha : ap ≤ B ^ β) (hc : bp ≤ B ^ β) (hd : cp ≤ B ^ β) :
    envelope n F b ap bp cp values ≤ B ^ (12332 * (κ + 9) + β + 33) := by
  let k := Nat.clog 2 n
  let e := 12332 * (κ + 9) + β + 20
  have hB : 2 ≤ B := by omega
  have hB1 : 1 ≤ B := by omega
  have hnB : n ≤ B := by omega
  have hk : k ≤ n := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)
  have htwo : 2 ^ k ≤ B ^ 2 := padding_le hn
  have hfour : 4 ^ k ≤ B ^ 4 := by
    calc
      _ = (2 ^ k) ^ 2 := by rw [pow_two, ← mul_pow]; rfl
      _ ≤ (B ^ 2) ^ 2 := Nat.pow_le_pow_left htwo _
      _ = _ := by rw [← pow_mul]
  have hsixteen : 16 ^ k ≤ B ^ 8 := by
    change (2 ^ 4) ^ k ≤ B ^ 8
    rw [← pow_mul, Nat.mul_comm 4 k, pow_mul]
    exact (Nat.pow_le_pow_left htwo 4).trans_eq (by rw [← pow_mul])
  have small (q : ℕ) (hq : q ≤ e) : B ^ q ≤ B ^ e := Nat.pow_le_pow_right hB1 hq
  have hnE : n ≤ B ^ e := hnB.trans (Nat.le_self_pow (by dsimp only [e]; omega) B)
  have hkE : k ≤ B ^ e := hk.trans hnE
  have hN2 : n * n ≤ B ^ e :=
    ((Nat.mul_le_mul hnB hnB).trans_eq (by ring : B * B = B ^ 2)).trans
      (small 2 (by dsimp only [e]; omega))
  have hN3 : n * n * n ≤ B ^ e := by
    calc
      _ ≤ B * B * B := Nat.mul_le_mul (Nat.mul_le_mul hnB hnB) hnB
      _ = B ^ 3 := by ring
      _ ≤ B ^ e := small 3 (by dsimp only [e]; omega)
  have hscalar : B ^ β ≤ B ^ e := small β (by dsimp only [e]; omega)
  have hFE := hF.trans (small κ (by dsimp only [e]; omega))
  have hconst : 2048 ≤ B ^ e := (by decide : 2048 ≤ (2 : ℕ) ^ 20).trans
    ((Nat.pow_le_pow_left hB 20).trans (small 20 (by dsimp only [e]; omega)))
  have hcap : Nat.sqrt (ParameterChoice.window n) ≤ B :=
    (Nat.sqrt_le_self _).trans ((ParameterChoice.powers_le n).2.trans (by omega))
  have hcapE : Nat.sqrt (ParameterChoice.window n) ≤ B ^ e :=
    hcap.trans (Nat.le_self_pow (by dsimp only [e]; omega) B)
  have harea : 4 ^ k * Nat.sqrt (ParameterChoice.window n) ≤ B ^ e := by
    calc
      _ ≤ B ^ 4 * B := Nat.mul_le_mul hfour hcap
      _ = B ^ 5 := by ring
      _ ≤ B ^ e := small 5 (by dsimp only [e]; omega)
  have hfourE := hfour.trans (small 4 (by dsimp only [e]; omega))
  have htwoE := htwo.trans (small 2 (by dsimp only [e]; omega))
  have haddress : CountPrime.addressBudget n (Nat.sqrt (ParameterChoice.window n)) k b ap bp cp ≤
      512 * B ^ e := by
    unfold CountPrime.addressBudget
    have hb' := hb.trans hscalar
    have ha' := ha.trans hscalar
    have hc' := hc.trans hscalar
    have hd' := hd.trans hscalar
    omega
  have hmagproduct : 2 * (Nat.sqrt (ParameterChoice.window n) + 4) * 16 ^ k ≤ B ^ e := by
    have hf : 2 * (Nat.sqrt (ParameterChoice.window n) + 4) ≤ 10 * B := by omega
    calc
      _ ≤ 10 * B * B ^ 8 := Nat.mul_le_mul hf hsixteen
      _ = 10 * B ^ 9 := by ring
      _ ≤ B ^ 4 * B ^ 9 := Nat.mul_le_mul_right _
        ((by decide : 10 ≤ (2 : ℕ) ^ 4).trans (Nat.pow_le_pow_left hB 4))
      _ = B ^ 13 := by rw [← pow_add]
      _ ≤ B ^ e := small 13 (by dsimp only [e]; omega)
  have hwindow := (window_le_pow values hlen hv hn hF).trans
    (small (12332 * (κ + 9)) (by dsimp only [e]; omega))
  have hcontrol : 4 * (ParameterChoice.window n + 2) * (ParameterChoice.window n + 2) + 4 ≤
      40 * B ^ e := by
    have hw := (ParameterChoice.powers_le n).2
    have hsq : ParameterChoice.window n + 2 ≤ 3 * B := by omega
    have hprod := Nat.mul_le_mul (Nat.mul_le_mul_left 4 hsq) hsq
    have hB2 := small 2 (by dsimp only [e]; omega)
    nlinarith only [hprod, hB2, hconst]
  have henv : envelope n F b ap bp cp values ≤ 6000 * B ^ e := by
    have hb' := hb.trans hscalar
    dsimp only [k] at haddress hmagproduct
    dsimp only [envelope]
    change b + 4 * _ + 1024 + _ + (F + _ + _ + 1) + _ +
      (1296 + 32 * (n + 1)) + (b + n * (n * n) + 6 * F + 10) + 1 ≤ _
    have hN3' : n * (n * n) ≤ B ^ e := by simpa only [Nat.mul_assoc] using hN3
    omega
  calc
    _ ≤ 6000 * B ^ e := henv
    _ ≤ B ^ 13 * B ^ e := Nat.mul_le_mul_right _
      ((by decide : 6000 ≤ (2 : ℕ) ^ 13).trans (Nat.pow_le_pow_left hB 13))
    _ = _ := by rw [← pow_add]; congr 1; dsimp only [e]; omega

/-- Logarithmic semantic admission from one common original scalar base. -/
theorem executionWidth_le_base_log {n F b ap bp cp B κ β : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ F)
    (hn : n + 2 ≤ B) (hF : F ≤ B ^ κ) (hb : b ≤ B ^ β)
    (ha : ap ≤ B ^ β) (hc : bp ≤ B ^ β) (hd : cp ≤ B ^ β) :
    executionWidth n F b ap bp cp values ≤
      (12332 * (κ + 9) + β + 36) * Nat.clog 2 B := by
  have he := envelope_le_pow values hlen hv hn hF hb ha hc hd
  have he' := he.trans (Nat.pow_le_pow_left
    (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) B) _)
  rw [← pow_mul] at he'
  have hl := Nat.clog_le_of_le_pow he'
  have hp : 1 ≤ Nat.clog 2 B := Nat.clog_pos (by decide) (by omega)
  unfold executionWidth
  nlinarith only [hl, hp]

/-- A fixed coefficient suffices for the host's original address/magnitude logarithm;
no old unused register or memory bound is required for this execution admission. -/
theorem executionWidth_le_host_log {n F b ap bp cp : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ F)
    (ha : ap ≤ b) (hc : bp ≤ b) (hd : cp ≤ b) :
    executionWidth n F b ap bp cp values ≤ 123357 * Nat.clog 2 (b + F + n + 2) := by
  exact executionWidth_le_base_log (B := b + F + n + 2) (κ := 1) (β := 1)
    values hlen hv (by omega) (by simpa only [pow_one] using (by omega : F ≤ b + F + n + 2))
    (by simpa only [pow_one] using (by omega : b ≤ b + F + n + 2))
    (by simpa only [pow_one] using (by omega : ap ≤ b + F + n + 2))
    (by simpa only [pow_one] using (by omega : bp ≤ b + F + n + 2))
    (by simpa only [pow_one] using (by omega : cp ≤ b + F + n + 2))

/-- Positive logarithmic resource admission from polynomial original weights, placement
and raw old words. The old-word exponent is an explicit numerical resource hypothesis. -/
theorem admissionWidth_le_log {n F b ap bp cp P κ β : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ F)
    (hF : F ≤ (n + 2) ^ κ) (hb : b ≤ (n + 2) ^ β)
    (ha : ap ≤ (n + 2) ^ β) (hc : bp ≤ (n + 2) ^ β) (hd : cp ≤ (n + 2) ^ β)
    (hP : P ≤ (n + 2) ^ β) :
    admissionWidth n F b ap bp cp P values ≤
      (12332 * (κ + 9) + β + 38) * Nat.clog 2 (n + 2) := by
  let B := n + 2
  let e := 12332 * (κ + 9) + β + 33
  have hb1 : 1 ≤ B := by dsimp only [B]; omega
  have he : envelope n F b ap bp cp values ≤ B ^ e :=
    envelope_le_pow values hlen hv le_rfl hF hb ha hc hd
  have hP' := hP.trans (Nat.pow_le_pow_right hb1
    (show β ≤ e by dsimp only [e]; omega))
  have hunit : 1 ≤ B ^ e := Nat.one_le_pow _ _ hb1
  have h3 : 3 ≤ B ^ 2 := (by decide : 3 ≤ (2 : ℕ) ^ 2).trans
    (Nat.pow_le_pow_left (show 2 ≤ B by dsimp only [B]; omega) 2)
  have hsum : envelope n F b ap bp cp values + P + 1 ≤ B ^ (e + 2) := by
    calc
      _ ≤ 3 * B ^ e := by omega
      _ ≤ B ^ 2 * B ^ e := Nat.mul_le_mul_right _ h3
      _ = _ := by rw [← pow_add, Nat.add_comm]
  have hpow := hsum.trans (Nat.pow_le_pow_left
    (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) B) _)
  rw [← pow_mul] at hpow
  have hl := Nat.clog_le_of_le_pow hpow
  have hp : 1 ≤ Nat.clog 2 B := Nat.clog_pos (by decide) (by dsimp only [B]; omega)
  dsimp only [admissionWidth]
  dsimp only [e, B] at hl hp
  nlinarith only [hl, hp]

/-- Original polynomial hypotheses give a polynomial word/support envelope, independent of W. -/
theorem wordBound_le_pow {n F b ap bp cp P κ β : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ F)
    (hF : F ≤ (n + 2) ^ κ) (hb : b ≤ (n + 2) ^ β)
    (ha : ap ≤ (n + 2) ^ β) (hc : bp ≤ (n + 2) ^ β) (hd : cp ≤ (n + 2) ^ β)
    (hP : P ≤ (n + 2) ^ β) :
    wordBound n F b ap bp cp P values ≤ (n + 2) ^ (12332 * (κ + 9) + β + 39) := by
  let B := n + 2
  let e := 12332 * (κ + 9) + β + 33
  have hb2 : 2 ≤ B := by dsimp only [B]; omega
  have he : envelope n F b ap bp cp values ≤ B ^ e :=
    envelope_le_pow values hlen hv le_rfl hF hb ha hc hd
  have hP' := hP.trans (Nat.pow_le_pow_right (by omega : 1 ≤ B)
    (show β ≤ e by dsimp only [e]; omega))
  have hunit : 1 ≤ B ^ e := Nat.one_le_pow _ _ (by omega)
  have h48 : 48 ≤ B ^ 6 := (by decide : 48 ≤ (2 : ℕ) ^ 6).trans (Nat.pow_le_pow_left hb2 6)
  calc
    _ ≤ 48 * B ^ e := by dsimp only [wordBound]; omega
    _ ≤ B ^ 6 * B ^ e := Nat.mul_le_mul_right _ h48
    _ = _ := by rw [← pow_add]; congr 1; dsimp only [e]; omega

private theorem initialized_placement (n : ℕ) : 3 + 3 * (n * n) ≤ (n + 2) ^ 4 := by
  nlinarith [sq_nonneg (n * n)]

/-- Complete initialized execution admits a positive logarithmic original-input threshold. -/
theorem inputWidth_le_log {n F κ : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ F)
    (hF : F ≤ (n + 2) ^ κ) :
    inputWidth n F values ≤ (12332 * (κ + 9) + 40) * Nat.clog 2 (n + 2) :=
  executionWidth_le_base_log (β := 4) values hlen hv le_rfl hF (initialized_placement n)
    (by have := initialized_placement n; omega)
    (by have := initialized_placement n; omega) (by have := initialized_placement n; omega)

/-- Every admitted initialized prefix uses polynomial words and address support, with no
dependence on the physical word width. Empty matrices and the whole small branch are included. -/
theorem bounded_reachable_polynomial {W n F κ k : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ F)
    (hF : F ≤ (n + 2) ^ κ)
    (hW : (12332 * (κ + 9) + 40) * Nat.clog 2 (n + 2) ≤ W)
    {s : State 640} (hr : Runs W (entryProgram.program Reg.result)
      (State.init (CountPrime.inputWords n F values)) s k) :
    (∀ i, s.data.regs i < (n + 2) ^ (12332 * (κ + 9) + 41)) ∧
      (∀ q, s.data.mem q < (n + 2) ^ (12332 * (κ + 9) + 41)) ∧
      ∀ q, (n + 2) ^ (12332 * (κ + 9) + 41) ≤ q → s.data.mem q = 0 := by
  obtain ⟨regs, memory, support⟩ := bounded_reachable_input values hlen hv
    ((inputWidth_le_log values hlen hv hF).trans hW) hr
  have he := envelope_le_pow (β := 4) (ap := 3) (bp := 3 + n * n)
    (cp := 3 + 2 * (n * n)) values hlen hv le_rfl hF (initialized_placement n)
    (by have := initialized_placement n; omega)
    (by have := initialized_placement n; omega) (by have := initialized_placement n; omega)
  have hc : 16 ≤ (n + 2) ^ 4 := (by decide : 16 ≤ (2 : ℕ) ^ 4).trans
    (Nat.pow_le_pow_left (by omega : 2 ≤ n + 2) 4)
  have bound : 16 * envelope n F (3 + 3 * (n * n)) 3 (3 + n * n)
      (3 + 2 * (n * n)) values ≤ (n + 2) ^ (12332 * (κ + 9) + 41) := by
    calc
      _ ≤ (n + 2) ^ 4 * (n + 2) ^ (12332 * (κ + 9) + 4 + 33) := Nat.mul_le_mul hc he
      _ = _ := by
        rw [← pow_add]
        exact congrArg (fun q : ℕ => (n + 2) ^ q)
          (by omega : 4 + (12332 * (κ + 9) + 4 + 33) = 12332 * (κ + 9) + 41)
  exact ⟨fun i => (regs i).trans_le bound, fun q => (memory q).trans_le bound,
    fun q hq => support q (bound.trans hq)⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting
