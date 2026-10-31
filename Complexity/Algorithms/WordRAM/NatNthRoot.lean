/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Notation
public import Complexity.Computability.WordRAM.RegisterFrame
public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith

/-!
# A charged native integer `k`-th root

The `k`-th root `Nat.nthRoot k n`, the largest `a` with `a ^ k ≤ n`, is found by binary search on
`[0, n + 1)`. Each probe compares `m ^ k` with `n` by a *capped power*: repeated multiplication
that stops as soon as the partial product exceeds `n`, so every product stays below `n (n + 1)`
and fits a word of about twice the bit length of `n`. The search halves the interval, so it makes
at most `⌈log₂ (n + 1)⌉` probes.

## Main definitions

* `NatNthRoot.CapPow.program`: compare `m ^ k` with a bound `n` by capped multiplication.
* `NatNthRoot.program`: binary search for `Nat.nthRoot k n`.

## Main results

* `NatNthRoot.CapPow.exec`: within `6 k + 5` instructions, the capped power is at most `n`
  exactly when `m ^ k ≤ n`, and then equals `m ^ k`.
* `NatNthRoot.exec`: `Nat.nthRoot k n` within `⌈log₂ (n + 1)⌉ (6 k + 13) + 7` instructions.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.NatNthRoot

open Cslib.WordRAM

namespace CapPow

/-- Base, preserved. -/
abbrev m : Fin 6 := 0
/-- Exponent, preserved. -/
abbrev k : Fin 6 := 1
/-- Bound, preserved. -/
abbrev n : Fin 6 := 2
/-- Capped power, the output. -/
abbrev p : Fin 6 := 3
/-- Counter. -/
abbrev i : Fin 6 := 4
/-- Constant one. -/
abbrev one : Fin 6 := 5

/-- Stop once the partial product exceeds the bound; otherwise multiply once more. -/
def body : Code .standard 6 :=
  ram[ if n < p then [ i ← k ] else [ p ← p * m; i ← i + one ] ]

/-- Capped repeated multiplication. -/
def program : Code .standard 6 :=
  .seq (ram[ p ← #1; i ← #0; one ← #1 ]) (.loop (.lt i k) body)

/-- For a positive base, the capped power is at most the bound exactly when the true power is,
and then the two agree. The products stay below `n m`. -/
theorem exec {w : ℕ} (x : Data 6) (hm : 1 ≤ x.regs m) (h1 : Fits w 1)
    (hk : Fits w (x.regs k)) (hprod : Fits w (x.regs n * x.regs m)) :
    ∃ y, ExecWithin w program x y (6 * x.regs k + 5) ∧
      (y.regs p ≤ x.regs n ↔ x.regs m ^ x.regs k ≤ x.regs n) ∧
      (x.regs m ^ x.regs k ≤ x.regs n → y.regs p = x.regs m ^ x.regs k) ∧
      y.regs m = x.regs m ∧ y.regs k = x.regs k ∧ y.regs n = x.regs n ∧
      y.regs one = 1 ∧ y.mem = x.mem := by
  set b := x.regs m
  set e := x.regs k
  set N := x.regs n
  let I (y : Data 6) : Prop := y.regs m = b ∧ y.regs k = e ∧ y.regs n = N ∧ y.regs one = 1 ∧
    y.regs i ≤ e ∧ (y.regs p = b ^ y.regs i ∨ (N < y.regs p ∧ N < b ^ e)) ∧ y.mem = x.mem
  have hbody (y : Data 6) (hy : I y) (hc : (Cond.lt i k).Holds y) :
      ∃ z, ExecWithin w body y z 4 ∧ I z ∧ e - z.regs i < e - y.regs i := by
    obtain ⟨hym, hyk, hyn, hyo, hyi, hyp, hymem⟩ := hy
    have hlt : y.regs i < e := by simpa only [Cond.holds_lt, hyk] using hc
    by_cases hover : N < y.regs p
    · have hc' : (Cond.lt n p).Holds y := by simpa only [Cond.holds_lt, hyn] using hover
      have hcopy : ExecWithin (B := .standard) w (ram[ i ← k ]) y (y.set i e) 1 := by
        simpa only [hyk] using ExecWithin.copy (B := .standard) (w := w) (d := i) (s := k) (x := y)
      refine ⟨y.set i e, (ExecWithin.branch_pos hc' hcopy).mono (by omega), ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hymem⟩
        · simpa +decide [Function.update_apply] using hym
        · simpa +decide [Function.update_apply] using hyk
        · simpa +decide [Function.update_apply] using hyn
        · simpa +decide [Function.update_apply] using hyo
        · simp
        · refine Or.inr ⟨by simpa +decide [Function.update_apply] using hover, ?_⟩
          rcases hyp with h | h
          · exact hover.trans_le (h ▸ Nat.pow_le_pow_right hm hyi)
          · exact h.2
      · simp only [Data.set_regs, Function.update_self]; omega
    · have hc' : ¬(Cond.lt n p).Holds y := by simpa only [Cond.holds_lt, hyn] using hover
      have hpow : y.regs p = b ^ y.regs i := hyp.resolve_right (fun h => hover h.1)
      have hmul : Fits w (y.regs p * y.regs m) := by
        rw [hym]; exact hprod.of_le (Nat.mul_le_mul_right _ (by omega))
      have hinc : Fits w (y.regs i + 1) := hk.of_le (by omega)
      refine ⟨?z, ?run, ?inv, ?decrease⟩
      case run =>
        refine ExecWithin.branch_neg hc' ?_
        ram_eval [hmul, hinc, hyo]
      case inv =>
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hymem⟩
        · simpa +decide [Function.update_apply] using hym
        · simpa +decide [Function.update_apply] using hyk
        · simpa +decide [Function.update_apply] using hyn
        · simpa +decide [Function.update_apply] using hyo
        · simp +decide only [Data.set_regs, Function.update_apply, ↓reduceIte]; omega
        · left
          simp +decide only [Data.set_regs, Function.update_apply, ↓reduceIte, hpow, hym,
            pow_succ]
      case decrease =>
        simp +decide only [Data.set_regs, Function.update_apply, ↓reduceIte]; omega
  let x₀ := ((x.set p 1).set i 0).set one 1
  have hx₀ : I x₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> simp +decide [x₀, b, e, N]
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I (fun y => e - y.regs i) hbody hx₀
  obtain ⟨hym, hyk, hyn, hyo, hyi, hyp, hymem⟩ := hy
  have hend : y.regs i = e := by simp only [Cond.holds_lt, hyk] at hc; omega
  have hinit : ExecWithin (B := .standard) w (ram[ p ← #1; i ← #0; one ← #1 ]) x x₀ 3 := by
    ram_eval [x₀, h1]
  refine ⟨y, ?_, ?_, ?_, hym, hyk, hyn, hyo, hymem⟩
  · have hi₀ : x₀.regs i = 0 := by simp +decide [x₀]
    exact (hinit.seq he).mono (by rw [hi₀]; omega)
  · rw [hend] at hyp
    rcases hyp with h | h
    · rw [h]
    · exact ⟨fun hle => absurd hle (not_le.mpr h.1), fun hle => absurd hle (not_le.mpr h.2)⟩
  · intro hle
    rw [hend] at hyp
    exact hyp.resolve_right fun h => absurd hle (not_le.mpr h.2)

/-- Run the capped power on any injectively chosen registers. -/
theorem exec_rename {r w : ℕ} (f : Fin 6 → Fin r) (hf : f.Injective) (x : Data r)
    (hm : 1 ≤ x.regs (f m)) (h1 : Fits w 1) (hk : Fits w (x.regs (f k)))
    (hprod : Fits w (x.regs (f n) * x.regs (f m))) :
    ∃ y, ExecWithin w (program.rename f) x y (6 * x.regs (f k) + 5) ∧
      (y.regs (f p) ≤ x.regs (f n) ↔ x.regs (f m) ^ x.regs (f k) ≤ x.regs (f n)) ∧
      (x.regs (f m) ^ x.regs (f k) ≤ x.regs (f n) →
        y.regs (f p) = x.regs (f m) ^ x.regs (f k)) ∧
      y.regs (f m) = x.regs (f m) ∧ y.regs (f k) = x.regs (f k) ∧
      y.regs (f n) = x.regs (f n) ∧ y.regs (f one) = 1 ∧ y.mem = x.mem := by
  obtain ⟨y, hy, hle, heq, hym, hyk, hyn, hyo, hymem⟩ := exec (x.comap f) hm h1 hk hprod
  have hext (j : Fin 6) : (y.extend f x).regs (f j) = y.regs j := hf.extend_apply _ _ j
  refine ⟨y.extend f x, hy.rename hf, ?_, ?_, ?_, ?_, ?_, ?_, hymem⟩ <;>
    simp only [hext] <;> assumption

end CapPow

/-- Bound `n`, preserved. -/
abbrev n : Fin 10 := 0
/-- Root degree `k`, preserved. -/
abbrev k : Fin 10 := 1
/-- Lower end of the search interval, and the output. -/
abbrev lo : Fin 10 := 2
/-- Upper end of the search interval. -/
abbrev hi : Fin 10 := 3
/-- Probe. -/
abbrev mid : Fin 10 := 4
/-- Capped power of the probe. -/
abbrev p : Fin 10 := 5
/-- Counter of the capped power. -/
abbrev i : Fin 10 := 6
/-- Constant one. -/
abbrev one : Fin 10 := 7
/-- Constant two. -/
abbrev two : Fin 10 := 8
/-- `lo + 1`, for the loop test. -/
abbrev t : Fin 10 := 9

/-- The registers of the capped power inside the search. -/
def capMap : Fin 6 → Fin 10 := ![mid, k, n, p, i, one]

theorem capMap_injective : capMap.Injective := by decide

/-- One probe: halve the interval according to the capped power of its midpoint. -/
def body : Code .standard 10 :=
  .seq (ram[ mid ← lo + hi; mid ← mid / two ]) (.seq (CapPow.program.rename capMap)
    (ram[ if n < p then [ hi ← mid ] else [ lo ← mid ]; t ← lo + one ]))

/-- Binary search for the `k`-th root on `[0, n + 1)`. -/
def program : Code .standard 10 :=
  .seq (ram[ lo ← #0; one ← #1; two ← #2; hi ← n + one; t ← lo + one ]) (.loop (.lt t hi) body)

private theorem clog_halve {d : ℕ} (hd : 2 ≤ d) {d' : ℕ} (hd' : d' ≤ (d + 1) / 2) :
    Nat.clog 2 d' < Nat.clog 2 d := by
  rw [Nat.clog_of_two_le one_lt_two hd]
  exact Nat.lt_succ_of_le (Nat.clog_mono_right 2 (by omega))

/-- Compute `Nat.nthRoot k n` for `k ≥ 1` within `⌈log₂ (n + 1)⌉ (6 k + 13) + 7` instructions,
preserving `n`, `k` and memory. Products and search bounds are at most `n² + 2 n + 1`, but the
probe counters run up to `k` whatever `n` is, hence the separate hypothesis `hkfit`. -/
theorem exec {w : ℕ} (x : Data 10) (hk : 1 ≤ x.regs k) (hkfit : Fits w (x.regs k))
    (hfit : Fits w (x.regs n * x.regs n + 2 * x.regs n + 2)) :
    ∃ y, ExecWithin w program x y (Nat.clog 2 (x.regs n + 1) * (6 * x.regs k + 13) + 7) ∧
      y.regs lo = Nat.nthRoot (x.regs k) (x.regs n) ∧ y.regs n = x.regs n ∧
      y.regs k = x.regs k ∧ y.regs one = 1 ∧ y.regs two = 2 ∧ y.mem = x.mem := by
  set N := x.regs n
  set e := x.regs k
  have he0 : e ≠ 0 := by omega
  have h1 : Fits w 1 := hfit.of_le (by omega)
  have h2 : Fits w 2 := hfit.of_le (by omega)
  let I (y : Data 10) : Prop := y.regs n = N ∧ y.regs k = e ∧ y.regs one = 1 ∧ y.regs two = 2 ∧
    y.regs t = y.regs lo + 1 ∧ y.regs lo < y.regs hi ∧ y.regs hi ≤ N + 1 ∧
    y.regs lo ^ e ≤ N ∧ N < y.regs hi ^ e ∧ y.mem = x.mem
  have hbody (y : Data 10) (hy : I y) (hc : (Cond.lt t hi).Holds y) :
      ∃ z, ExecWithin w body y z (6 * e + 11) ∧ I z ∧
        Nat.clog 2 (z.regs hi - z.regs lo) < Nat.clog 2 (y.regs hi - y.regs lo) := by
    obtain ⟨hyn, hyk, hyo, hyt2, hyt, hlohi, hhi, hlo, hhip, hymem⟩ := hy
    obtain ⟨l, hl⟩ : ∃ l, y.regs lo = l := ⟨_, rfl⟩
    obtain ⟨h, hh⟩ : ∃ h, y.regs hi = h := ⟨_, rfl⟩
    simp only [hl, hh] at hlohi hlo hhip hyt hhi
    have hgap : l + 1 < h := by simpa only [Cond.holds_lt, hyt, hh] using hc
    have hmd1 : l < (l + h) / 2 := by omega
    have hmd2 : (l + h) / 2 < h := by omega
    have hsum : Fits w (l + h) := hfit.of_le (by nlinarith)
    have hdiv : Fits w ((l + h) / 2) := hsum.of_le (Nat.div_le_self _ _)
    -- After the two midpoint instructions.
    let y₁ := (y.set mid (l + h)).set mid ((l + h) / 2)
    have hrun₁ : ExecWithin (B := .standard) w (ram[ mid ← lo + hi; mid ← mid / two ]) y y₁ 2 := by
      ram_eval [y₁, hl, hh, hsum, hdiv, hyt2]
    have hy₁ (j : Fin 10) (hj : j ≠ mid) : y₁.regs j = y.regs j := by
      simp [y₁, hj]
    have hy₁m : y₁.regs mid = (l + h) / 2 := by simp [y₁]
    have hmdN : (l + h) / 2 ≤ N := by omega
    have hcm : capMap CapPow.m = mid := rfl
    have hck : capMap CapPow.k = k := rfl
    have hcn : capMap CapPow.n = n := rfl
    have hcp : capMap CapPow.p = p := rfl
    have hco : capMap CapPow.one = one := rfl
    obtain ⟨y₂, hrun₂, hple, -, hy₂m, hy₂k, hy₂n, hy₂o, hy₂mem⟩ :=
      CapPow.exec_rename capMap capMap_injective y₁ (by rw [hcm, hy₁m]; omega) h1
        (by rw [hck, hy₁ k (by decide), hyk]; exact hkfit)
        (by
          rw [hcn, hcm, hy₁m, hy₁ n (by decide), hyn]
          exact hfit.of_le ((Nat.mul_le_mul_left N hmdN).trans (by omega)))
    have hpres (j : Fin 10) (hj : ∀ a, capMap a ≠ j) : y₂.regs j = y₁.regs j :=
      hrun₂.regs_eq (Code.preserves_rename_of_forall_ne _ _ _ hj)
    rw [hcp, hcn, hcm, hck, hy₁m, hy₁ n (by decide), hy₁ k (by decide), hyn, hyk] at hple
    rw [hck, hy₁ k (by decide), hyk] at hy₂k
    rw [hcn, hy₁ n (by decide), hyn] at hy₂n
    rw [hco] at hy₂o
    rw [hcm, hy₁m] at hy₂m
    rw [hck, hy₁ k (by decide), hyk] at hrun₂
    have hy₂lo : y₂.regs lo = l := (hpres lo (by decide)).trans ((hy₁ lo (by decide)).trans hl)
    have hy₂hi : y₂.regs hi = h := (hpres hi (by decide)).trans ((hy₁ hi (by decide)).trans hh)
    have hy₂two : y₂.regs two = 2 :=
      (hpres two (by decide)).trans ((hy₁ two (by decide)).trans hyt2)
    have hy₂mid : y₂.regs mid = (l + h) / 2 := hy₂m
    by_cases hover : N < y₂.regs p
    · -- The probe is too large: `hi ← mid`.
      have hc' : (Cond.lt n p).Holds y₂ := by simpa only [Cond.holds_lt, hy₂n] using hover
      have hpow : N < ((l + h) / 2) ^ e := by
        by_contra hle
        exact absurd (hple.mpr (not_lt.mp hle)) (not_le.mpr hover)
      have hinc : Fits w (l + 1) := hfit.of_le (by nlinarith)
      let z := (y₂.set hi ((l + h) / 2)).set t (l + 1)
      have hrun₃ : ExecWithin (B := .standard) w
          (ram[ if n < p then [ hi ← mid ] else [ lo ← mid ]; t ← lo + one ]) y₂ z 3 := by
        refine ((ExecWithin.branch_pos (T := 1) hc' (ExecWithin.copy (d := hi) (s := mid))).seq
          (T₂ := 1) ?_).mono (by norm_num)
        ram_eval [z, hy₂lo, hy₂o, hy₂mid, hinc]
      refine ⟨z, (hrun₁.seq (hrun₂.seq hrun₃)).mono (by omega), ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hy₂mem.trans hymem⟩ <;>
          simp +decide [z, hy₂n, hy₂k, hy₂o, hy₂two, hy₂lo] <;> omega
      · simp +decide only [z, Data.set_regs, Function.update_apply, ↓reduceIte, hy₂lo, hl, hh]
        exact clog_halve (by omega) (by omega)
    · have hc' : ¬(Cond.lt n p).Holds y₂ := by simpa only [Cond.holds_lt, hy₂n] using hover
      have hpow : ((l + h) / 2) ^ e ≤ N := hple.mp (not_lt.mp hover)
      have hinc : Fits w ((l + h) / 2 + 1) := hfit.of_le (by nlinarith)
      let z := (y₂.set lo ((l + h) / 2)).set t ((l + h) / 2 + 1)
      have hrun₃ : ExecWithin (B := .standard) w
          (ram[ if n < p then [ hi ← mid ] else [ lo ← mid ]; t ← lo + one ]) y₂ z 4 := by
        refine ((ExecWithin.branch_neg (T := 1) hc' (ExecWithin.copy (d := lo) (s := mid))).seq
          (T₂ := 1) ?_).mono (by norm_num)
        ram_eval [z, hy₂o, hy₂mid, hinc]
      refine ⟨z, (hrun₁.seq (hrun₂.seq hrun₃)).mono (by omega), ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hy₂mem.trans hymem⟩ <;>
          simp +decide [z, hy₂n, hy₂k, hy₂o, hy₂two, hy₂hi] <;> omega
      · simp +decide only [z, Data.set_regs, Function.update_apply, ↓reduceIte, hy₂hi, hl, hh]
        exact clog_halve (by omega) (by omega)
  have hn1 : Fits w (x.regs n + 1) := hfit.of_le (by nlinarith)
  let x₀ := ((((x.set lo 0).set one 1).set two 2).set hi (N + 1)).set t 1
  have hx₀ : I x₀ := by
    have hpow : N < (N + 1) ^ e := Nat.lt_of_lt_of_le (Nat.lt_succ_self N) (Nat.le_self_pow he0 _)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
      simp +decide [x₀, N, e, he0, hpow]
  obtain ⟨y, hrun, hy, hc⟩ := ExecWithin.loop_invariant I
    (fun y => Nat.clog 2 (y.regs hi - y.regs lo)) hbody hx₀
  obtain ⟨hyn, hyk, hyo, hytwo, hyt, hlohi, -, hlo, hhip, hymem⟩ := hy
  have hhi : y.regs hi = y.regs lo + 1 := by simp only [Cond.holds_lt, hyt] at hc; omega
  have hinit : ExecWithin (B := .standard) w
      (ram[ lo ← #0; one ← #1; two ← #2; hi ← n + one; t ← lo + one ]) x x₀ 5 := by
    ram_eval [x₀, N, h1, h2, hn1]
  refine ⟨y, ?_, ?_, hyn, hyk, hyo, hytwo, hymem⟩
  · have hμ : Nat.clog 2 (x₀.regs hi - x₀.regs lo) = Nat.clog 2 (N + 1) := by
      simp +decide [x₀]
    refine (hinit.seq hrun).mono ?_
    rw [hμ, show 6 * e + 11 + 2 = 6 * e + 13 by omega]
    omega
  · rw [hhi] at hhip
    exact (Nat.nthRoot_eq_of_le_of_lt hlo hhip).symm

/-- Run the binary search on any injectively chosen registers. -/
theorem exec_rename {r w : ℕ} (f : Fin 10 → Fin r) (hf : f.Injective) (x : Data r)
    (hk : 1 ≤ x.regs (f k)) (hkfit : Fits w (x.regs (f k)))
    (hfit : Fits w (x.regs (f n) * x.regs (f n) + 2 * x.regs (f n) + 2)) :
    ∃ y, ExecWithin w (program.rename f) x y
        (Nat.clog 2 (x.regs (f n) + 1) * (6 * x.regs (f k) + 13) + 7) ∧
      y.regs (f lo) = Nat.nthRoot (x.regs (f k)) (x.regs (f n)) ∧
      y.regs (f n) = x.regs (f n) ∧ y.regs (f k) = x.regs (f k) ∧
      y.regs (f one) = 1 ∧ y.regs (f two) = 2 ∧ y.mem = x.mem := by
  obtain ⟨y, hy, hlo, hyn, hyk, hyo, hyt, hymem⟩ := exec (x.comap f) hk hkfit hfit
  have hext (j : Fin 10) : (y.extend f x).regs (f j) = y.regs j := hf.extend_apply _ _ j
  refine ⟨y.extend f x, hy.rename hf, ?_, ?_, ?_, ?_, ?_, hymem⟩ <;> simp only [hext] <;>
    assumption

end Cslib.Algorithms.WordRAM.NatNthRoot
