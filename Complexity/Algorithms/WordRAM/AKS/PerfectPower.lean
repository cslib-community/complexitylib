/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.NatLog
public import Complexity.Algorithms.WordRAM.NatNthRoot
public import Complexity.Foundations.NumberTheory.AKS.PerfectPower

/-!
# Perfect-power detection on the word RAM

Step 1 of the AKS algorithm [Agrawal, Kayal, Saxena, Section 4][AKS2004] asks whether `n = a ^ b`
for some `b > 1`. For `n ≥ 2` such an `a` is at least `2`, so `b ≤ log₂ n`, and `n` is a `b`-th
power exactly when `Nat.nthRoot b n ^ b = n` (`Cslib.AKS.isPerfectPower_iff_nthRoot`). The program
computes `⌊log₂ n⌋`, and for each `b` from `2` to `⌊log₂ n⌋` takes the `b`-th root by binary search
(`Cslib.Algorithms.WordRAM.NatNthRoot.program`) and compares its capped `b`-th power with `n`.
Every intermediate value is at most `n² + 2n + 1`.

## Main definitions

* `Cslib.Algorithms.WordRAM.AKS.PerfectPower.program`: the perfect-power test.
* `Cslib.Algorithms.WordRAM.AKS.PerfectPower.time`: its instruction bound, `O(log³ n)`.

## Main results

* `Cslib.Algorithms.WordRAM.AKS.PerfectPower.exec`: the program decides `Cslib.AKS.IsPerfectPower`
  for `n ≥ 2` within `time n` instructions.

## References

* [M. Agrawal, N. Kayal, N. Saxena, *PRIMES is in P*][AKS2004]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.AKS.PerfectPower

open Cslib.WordRAM

/-- The candidate `n`, preserved. -/
abbrev n : Fin 14 := 0
/-- The current exponent `b`. -/
abbrev k : Fin 14 := 1
/-- The root found by the search. -/
abbrev lo : Fin 14 := 2
/-- Upper end of the search interval. -/
abbrev hi : Fin 14 := 3
/-- Probe of the search. -/
abbrev mid : Fin 14 := 4
/-- Capped power. -/
abbrev p : Fin 14 := 5
/-- Counter of the capped power. -/
abbrev i : Fin 14 := 6
/-- Constant one. -/
abbrev one : Fin 14 := 7
/-- Constant two. -/
abbrev two : Fin 14 := 8
/-- Loop test of the search. -/
abbrev t : Fin 14 := 9
/-- `⌊log₂ n⌋ + 1`, the end of the exponent loop. -/
abbrev lim : Fin 14 := 10
/-- The answer: `1` for a perfect power. -/
abbrev flag : Fin 14 := 11
/-- Argument of the logarithm, consumed. -/
abbrev larg : Fin 14 := 12
/-- `⌊log₂ n⌋`. -/
abbrev lres : Fin 14 := 13

/-- The root search runs on the first ten registers. -/
def rootMap : Fin 10 → Fin 14 := Fin.castLE (by norm_num)

/-- The final capped power raises the root `lo` to the exponent `k`. -/
def capMap : Fin 6 → Fin 14 := ![lo, k, n, p, i, one]

/-- The logarithm runs on `larg`, `lres` and the shared constants. -/
def logMap : Fin 4 → Fin 14 := ![larg, lres, one, two]

theorem rootMap_injective : rootMap.Injective := Fin.castLE_injective _
theorem capMap_injective : capMap.Injective := by decide
theorem logMap_injective : logMap.Injective := by decide

/-- Test one exponent: take the root, raise it back, and record equality with `n`. -/
def body : Code .standard 14 :=
  .seq (NatNthRoot.program.rename rootMap) (.seq (NatNthRoot.CapPow.program.rename capMap)
    (ram[ if p = n then [ flag ← one ] else [ flag ← flag ]; k ← k + one ]))

/-- Compute `⌊log₂ n⌋`, then test every exponent `2 ≤ b ≤ ⌊log₂ n⌋`. -/
def program : Code .standard 14 :=
  .seq (ram[ larg ← n ]) (.seq (NatLog.program.rename logMap)
    (.seq (ram[ lim ← lres + one; flag ← #0; k ← #2 ]) (.loop (.lt k lim) body)))

/-- The instruction bound of `program`, which is `O(log³ n)`. -/
def time (n : ℕ) : ℕ :=
  (Nat.log 2 n + 1) * (Nat.clog 2 (n + 1) * (6 * Nat.log 2 n + 13) + 6 * Nat.log 2 n + 22) +
    4 * Nat.log 2 n + 11

/-- **The perfect-power test.** For `n ≥ 2` and a word size holding `n² + 2n + 2`, the program
leaves `1` in `flag` if `n` is a perfect power and `0` otherwise, within `time n` instructions,
preserving `n` and memory. -/
theorem exec {w : ℕ} (x : Data 14) (hn : 2 ≤ x.regs n)
    (hfit : Fits w (x.regs n * x.regs n + 2 * x.regs n + 2)) :
    ∃ y, ExecWithin w program x y (time (x.regs n)) ∧
      y.regs flag = (if Cslib.AKS.IsPerfectPower (x.regs n) then 1 else 0) ∧
      y.regs n = x.regs n ∧ y.mem = x.mem := by
  classical
  obtain ⟨N, hN⟩ : ∃ N, x.regs n = N := ⟨_, rfl⟩
  rw [hN] at hn hfit ⊢
  obtain ⟨L, hL⟩ : ∃ L, Nat.log 2 N = L := ⟨_, rfl⟩
  have hLN : L < N := hL ▸ Nat.log_lt_self 2 (by omega)
  have hLpos : 1 ≤ L := hL ▸ Nat.le_log_of_pow_le one_lt_two (by omega)
  have hfitN : Fits w N := hfit.of_le (by nlinarith)
  have h2 : Fits w 2 := hfit.of_le (by nlinarith)
  have h1 : Fits w 1 := hfit.of_le (by nlinarith)
  let Good (b : ℕ) : Prop := ∃ c, 2 ≤ c ∧ c < b ∧ Nat.nthRoot c N ^ c = N
  let I (y : Data 14) : Prop := y.regs n = N ∧ y.regs one = 1 ∧ y.regs two = 2 ∧
    y.regs lim = L + 1 ∧ 2 ≤ y.regs k ∧ y.regs k ≤ L + 1 ∧
    y.regs flag = (if Good (y.regs k) then 1 else 0) ∧ y.mem = x.mem
  set T₀ := Nat.clog 2 (N + 1) * (6 * L + 13) + 6 * L + 18 with hT₀
  have hbody (y : Data 14) (hy : I y) (hc : (Cond.lt k lim).Holds y) :
      ∃ z, ExecWithin w body y z T₀ ∧ I z ∧ L + 1 - z.regs k < L + 1 - y.regs k := by
    obtain ⟨hyn, hyo, hyt, hyl, hk2, hkL, hyf, hym⟩ := hy
    have hkL' : y.regs k ≤ L := by simp only [Cond.holds_lt, hyl] at hc; omega
    obtain ⟨b, hb⟩ : ∃ b, y.regs k = b := ⟨_, rfl⟩
    rw [hb] at hk2 hkL hkL' hyf
    have hbfit : Fits w b := hfitN.of_le (by omega)
    -- The root search.
    have hrn : rootMap NatNthRoot.n = n := rfl
    have hrk : rootMap NatNthRoot.k = k := rfl
    have hrlo : rootMap NatNthRoot.lo = lo := rfl
    have hro : rootMap NatNthRoot.one = one := rfl
    have hrt : rootMap NatNthRoot.two = two := rfl
    obtain ⟨y₁, hrun₁, hy₁lo, hy₁n, hy₁k, hy₁o, hy₁t, hy₁m⟩ :=
      NatNthRoot.exec_rename rootMap rootMap_injective y
        (by rw [hrk, hb]; omega) (by rw [hrk, hb]; exact hbfit)
        (by rw [hrn, hyn]; exact hfit)
    rw [hrn, hyn] at hy₁n hrun₁
    rw [hrk, hb] at hy₁k hrun₁
    rw [hrlo, hrk, hrn, hb, hyn] at hy₁lo
    rw [hro] at hy₁o
    rw [hrt] at hy₁t
    have hpres₁ (j : Fin 14) (hj : ∀ a, rootMap a ≠ j) : y₁.regs j = y.regs j :=
      hrun₁.regs_eq (Code.preserves_rename_of_forall_ne _ _ _ hj)
    set a := Nat.nthRoot b N with ha
    have hb0 : b ≠ 0 := by omega
    have hale : a ^ b ≤ N := (Nat.pow_nthRoot_le_iff).mpr (Or.inl hb0)
    have ha1 : 1 ≤ a := (Nat.le_nthRoot_iff hb0).mpr (by rw [one_pow]; omega)
    have haN : a ≤ N := (Nat.le_self_pow hb0 a).trans hale
    -- The capped power of the root.
    have hcm : capMap NatNthRoot.CapPow.m = lo := rfl
    have hck : capMap NatNthRoot.CapPow.k = k := rfl
    have hcn : capMap NatNthRoot.CapPow.n = n := rfl
    have hcp : capMap NatNthRoot.CapPow.p = p := rfl
    obtain ⟨y₂, hrun₂, -, hpeq, -, hy₂k, hy₂n, hy₂o, hy₂m⟩ :=
      NatNthRoot.CapPow.exec_rename capMap capMap_injective y₁
        (by rw [hcm, hy₁lo]; exact ha1) h1 (by rw [hck, hy₁k]; exact hbfit)
        (by rw [hcn, hcm, hy₁n, hy₁lo]; exact hfit.of_le (by nlinarith))
    rw [hcm, hck, hcn, hcp, hy₁lo, hy₁k, hy₁n] at hpeq
    rw [hck, hy₁k] at hy₂k hrun₂
    rw [hcn, hy₁n] at hy₂n
    have hy₂p : y₂.regs p = a ^ b := hpeq hale
    have hpres₂ (j : Fin 14) (hj : ∀ a, capMap a ≠ j) : y₂.regs j = y₁.regs j :=
      hrun₂.regs_eq (Code.preserves_rename_of_forall_ne _ _ _ hj)
    have hco : capMap NatNthRoot.CapPow.one = one := rfl
    have hy₂o' : y₂.regs one = 1 := by rwa [hco] at hy₂o
    have hy₂f : y₂.regs flag = y.regs flag :=
      (hpres₂ flag (by decide)).trans (hpres₁ flag (by decide))
    -- Record the comparison and advance the exponent.
    have hinc : Fits w (b + 1) := hfitN.of_le (by omega)
    let v := if a ^ b = N then 1 else y.regs flag
    let z := (y₂.set flag v).set k (b + 1)
    have hrun₃ : ExecWithin (B := .standard) w
        (ram[ if p = n then [ flag ← one ] else [ flag ← flag ]; k ← k + one ]) y₂ z 4 := by
      by_cases heq : a ^ b = N
      · have hc' : (Cond.eq p n).Holds y₂ := by
          simp only [Cond.holds_eq, hy₂p, hy₂n, heq]
        refine ((ExecWithin.branch_pos (T := 1) hc' ExecWithin.copy).seq (T₂ := 1) ?_).mono
          (by norm_num)
        ram_eval [z, v, heq, hy₂o', hy₂k, hinc]
      · have hc' : ¬(Cond.eq p n).Holds y₂ := by
          simp only [Cond.holds_eq, hy₂p, hy₂n]; exact heq
        refine ((ExecWithin.branch_neg (T := 1) hc' ExecWithin.copy).seq (T₂ := 1) ?_).mono
          (by norm_num)
        ram_eval [z, v, heq, hy₂o', hy₂k, hy₂f, hinc]
    have hgood : Good (b + 1) ↔ Good b ∨ a ^ b = N := by
      constructor
      · rintro ⟨c, hc2, hcb, hc⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hcb with hcb | rfl
        · exact Or.inl ⟨c, hc2, hcb, hc⟩
        · exact Or.inr hc
      · rintro (⟨c, hc2, hcb, hc⟩ | h)
        · exact ⟨c, hc2, by omega, hc⟩
        · exact ⟨b, hk2, by omega, h⟩
    refine ⟨z, ?_, ?_, ?_⟩
    · refine (hrun₁.seq (hrun₂.seq hrun₃)).mono ?_
      have : Nat.clog 2 (N + 1) * (6 * b + 13) ≤ Nat.clog 2 (N + 1) * (6 * L + 13) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hy₂m.trans (hy₁m.trans hym)⟩
      · simp +decide [z, hy₂n]
      · simp +decide [z, hy₂o']
      · have := (hpres₂ two (by decide)).trans hy₁t
        simp +decide [z, this]
      · have := (hpres₂ lim (by decide)).trans ((hpres₁ lim (by decide)).trans hyl)
        simp +decide [z, this]
      · simp +decide [z]; omega
      · simp +decide [z]; omega
      · simp only [z, v, Data.set_regs, Function.update_self]
        rw [Function.update_of_ne (by decide), Function.update_self, hyf]
        by_cases heq : a ^ b = N
        · simp [heq, hgood]
        · have : Good (b + 1) ↔ Good b := by simp [hgood, heq]
          simp [heq, this]
    · simp [z, hb]; omega
  -- The logarithm and the initialization.
  have hlarg : Fits w N := hfitN
  let x₁ := x.set larg N
  have hrun₀ : ExecWithin (B := .standard) w (ram[ larg ← n ]) x x₁ 1 := by
    simpa [x₁, hN] using ExecWithin.copy (B := .standard) (w := w) (d := larg) (s := n) (x := x)
  have hla : logMap NatLog.arg = larg := rfl
  have hlr : logMap NatLog.result = lres := rfl
  have hlo : logMap NatLog.one = one := rfl
  have hlt : logMap NatLog.two = two := rfl
  obtain ⟨y₁, hrun₁, hy₁r, hy₁m, hy₁o, hy₁t⟩ :=
    NatLog.exec_rename logMap logMap_injective x₁ h2 (by simpa [hla, x₁] using hlarg)
      (by simp only [hla, x₁, Data.set_regs, Function.update_self, hL]
          exact hfitN.of_le (by omega))
  have hx₁ : x₁.regs larg = N := by simp [x₁]
  rw [hla, hx₁, hL] at hrun₁ hy₁r
  rw [hlr] at hy₁r
  rw [hlo] at hy₁o
  rw [hlt] at hy₁t
  have hpres₁ (j : Fin 14) (hj : ∀ a, logMap a ≠ j) : y₁.regs j = x₁.regs j :=
    hrun₁.regs_eq (Code.preserves_rename_of_forall_ne _ _ _ hj)
  have hy₁n : y₁.regs n = N := by
    rw [hpres₁ n (by decide)]; simp +decide [x₁, hN]
  have hL1 : Fits w (L + 1) := hfitN.of_le (by omega)
  let x₂ := ((y₁.set lim (L + 1)).set flag 0).set k 2
  have hrun₂ : ExecWithin (B := .standard) w (ram[ lim ← lres + one; flag ← #0; k ← #2 ])
      y₁ x₂ 3 := by
    ram_eval [x₂, hy₁r, hy₁o, hL1, h2]
  have hx₂ : I x₂ := by
    have hgood : ¬Good 2 := fun ⟨c, hc2, hc, _⟩ => by omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hy₁m⟩ <;>
      simp +decide [x₂, hy₁n, hy₁o, hy₁t, hLpos, hgood]
  obtain ⟨y, hrun₃, hy, hc⟩ := ExecWithin.loop_invariant I (fun y => L + 1 - y.regs k) hbody hx₂
  obtain ⟨hyn, -, -, hyl, hk2, hkL, hyf, hym⟩ := hy
  have hkend : L + 1 ≤ y.regs k := by simp only [Cond.holds_lt, hyl] at hc; omega
  refine ⟨y, ?_, ?_, hyn, hym⟩
  · refine (hrun₀.seq (hrun₁.seq (hrun₂.seq hrun₃))).mono ?_
    have hx₂k : L + 1 - x₂.regs k ≤ L + 1 := by omega
    have := Nat.mul_le_mul_right (T₀ + 2) hx₂k
    simp only [time, hL, hT₀] at this ⊢
    nlinarith
  · have hiff : Good (y.regs k) ↔ Cslib.AKS.IsPerfectPower N := by
      rw [Cslib.AKS.isPerfectPower_iff_nthRoot hn]
      constructor
      · rintro ⟨c, hc2, hck, hc⟩; exact ⟨c, by omega, hc2, hc⟩
      · rintro ⟨c, hcL, hc2, hc⟩; exact ⟨c, hc2, by omega, hc⟩
    rw [hyf]
    exact if_congr hiff rfl rfl

/-- Run the perfect-power test on any injectively chosen registers. -/
theorem exec_rename {r w : ℕ} (f : Fin 14 → Fin r) (hf : f.Injective) (x : Data r)
    (hn : 2 ≤ x.regs (f n)) (hfit : Fits w (x.regs (f n) * x.regs (f n) + 2 * x.regs (f n) + 2)) :
    ∃ y, ExecWithin w (program.rename f) x y (time (x.regs (f n))) ∧
      y.regs (f flag) = (if Cslib.AKS.IsPerfectPower (x.regs (f n)) then 1 else 0) ∧
      y.regs (f n) = x.regs (f n) ∧ y.mem = x.mem := by
  obtain ⟨y, hy, hfl, hyn, hym⟩ := exec (x.comap f) hn hfit
  refine ⟨y.extend f x, hy.rename hf, ?_, ?_, hym⟩
  · exact (hf.extend_apply _ _ flag).trans hfl
  · exact (hf.extend_apply _ _ n).trans hyn

end Cslib.Algorithms.WordRAM.AKS.PerfectPower
