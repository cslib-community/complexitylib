/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.Step
public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.Trace

/-!
# The actual short-circuit query loop

The proof derives its scan trace from the original answer words and the verifier's integer
equation. Runtime execution receives neither trace nor witness function. Variable-cost loop
accounting charges a complete scan exactly when the native controller actually invokes it.
The finite scan bound follows the counting argument of pinned `ScanPairs.lean`;
the native code, ABI and instruction constants are original.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM

private theorem potential_step (active : ℕ → Prop) [DecidablePred active]
    {i Q T : ℕ} (hi : i < Q) :
    (if active i then T + 6 else 6) + 2 +
        (8 * (Q - (i + 1)) + T * (Nat.count active Q - Nat.count active (i + 1))) ≤
      8 * (Q - i) + T * (Nat.count active Q - Nat.count active i) := by
  have hcount : Nat.count active (i + 1) = Nat.count active i +
      (if active i then 1 else 0) := Nat.count_succ active i
  have hle := Nat.count_monotone active (Nat.succ_le_of_lt hi)
  change Nat.count active (i + 1) ≤ Nat.count active Q at hle
  have hindex : Q - i = Q - (i + 1) + 1 := by omega
  by_cases h : active i
  · rw [ite_eq_left h] at hcount ⊢
    rw [hcount] at hle
    have hd : Nat.count active Q - Nat.count active i =
        (Nat.count active Q - Nat.count active (i + 1)) + 1 := by omega
    rw [hindex, hd, Nat.mul_add, Nat.mul_add]
    omega
  · rw [ite_eq_right h] at hcount ⊢
    simp only [Nat.add_zero] at hcount
    rw [hindex, hcount, Nat.mul_add, Nat.mul_one]
    omega

/-- Run the actual answer/query loop. Every query coordinate is read from the protected
interleaved block, and every success is verified against the original three integer arrays.
Only accepted pairs without an original witness contribute to the failure count. -/
theorem exec_queries {w U n first length out queries Q : ℕ}
    (AB BC AC : ℕ → ℕ → ℤ) (a b : ℕ → ℕ) (x : Data 400)
    (hx : Fixed n first length out queries Q x)
    (hi : x.regs Reg.index = 0) (hs : x.regs Reg.scans = 0)
    (hf : x.regs Reg.found = 0)
    (hquery : ∀ i < Q, x.mem (queries + 2 * i) = a i ∧
      x.mem (queries + 2 * i + 1) = b i ∧ a i < n ∧ b i < n)
    (hc : first + length ≤ n)
    (hmem : ∀ u < n, ∀ v < n,
      x.mem (5 + (u * n + v)) = Signed.encode (AB u v) ∧
      x.mem (5 + n * n + (u * n + v)) = Signed.encode (BC u v) ∧
      x.mem (5 + n * n + n * n + (u * n + v)) = Signed.encode (AC u v))
    (hmag : ∀ u < n, ∀ v < n,
      (AB u v).natAbs ≤ U ∧ (BC u v).natAbs ≤ U ∧ (AC u v).natAbs ≤ U)
    (hU : GenericRAM.Signed.Fits w (2 * U : ℕ))
    (hfit : Fits (w + 2)
      (out + queries + 4 * Q + 6 * (n * n) + n + first + length + 64)) :
    ∃ y S, ExecWithin (w + 2) (.loop (.lt Reg.index Reg.count) step) x y
        (8 * Q + (42 * length + 28) * S + 2) ∧
      Fixed n first length out queries Q y ∧ y.mem = x.mem ∧
      y.regs Reg.index = Q ∧ y.regs Reg.scans = S ∧
      S ≤ Nat.count (fun i => x.mem (out + i) ≠ 0 ∧
        ∀ c : Fin length, AB (a i) (b i) + BC (b i) (first + c.val) +
          AC (a i) (first + c.val) ≠ 0) Q + y.regs Reg.found ∧
      (y.regs Reg.found = 0 ∨ y.regs Reg.found = 1) ∧
      (y.regs Reg.found = 1 ↔ ∃ i < Q, x.mem (out + i) ≠ 0 ∧
        ∃ c, first ≤ c ∧ c < first + length ∧ AB (a i) (b i) + BC (b i) c + AC (a i) c = 0) ∧
      (y.regs Reg.found = 1 → ∃ i < Q,
        x.mem (out + i) ≠ 0 ∧ y.regs Reg.witnessA = a i ∧ y.regs Reg.witnessB = b i ∧
        first ≤ y.regs Reg.witnessC ∧ y.regs Reg.witnessC < first + length ∧
        AB (a i) (b i) + BC (b i) (y.regs Reg.witnessC) +
          AC (a i) (y.regs Reg.witnessC) = 0) := by
  let accept (i : ℕ) : Bool := decide (x.mem (out + i) ≠ 0)
  let hit (i : ℕ) : Bool := decide (∃ c : Fin length,
    AB (a i) (b i) + BC (b i) (first + c.val) + AC (a i) (first + c.val) = 0)
  let active (i : ℕ) : Prop := (accept i && !foundBefore accept hit i) = true
  have hit_iff (i : ℕ) : hit i = true ↔ ∃ c, first ≤ c ∧ c < first + length ∧
      AB (a i) (b i) + BC (b i) c + AC (a i) c = 0 := by
    simp only [hit, decide_eq_true_eq]
    constructor
    · rintro ⟨c, hz⟩
      exact ⟨first + c.val, by omega, by have := c.isLt; omega, hz⟩
    · rintro ⟨c, hlo, hhi, hz⟩
      refine ⟨⟨c - first, by omega⟩, ?_⟩
      simpa only [Nat.add_sub_of_le hlo] using hz
  let I (y : Data 400) : Prop :=
    Fixed n first length out queries Q y ∧ y.mem = x.mem ∧ y.regs Reg.index ≤ Q ∧
    y.regs Reg.found = (foundBefore accept hit (y.regs Reg.index)).toNat ∧
    y.regs Reg.scans = Nat.count active (y.regs Reg.index) ∧
    (y.regs Reg.found = 1 → ∃ i < y.regs Reg.index,
      x.mem (out + i) ≠ 0 ∧ y.regs Reg.witnessA = a i ∧ y.regs Reg.witnessB = b i ∧
      first ≤ y.regs Reg.witnessC ∧ y.regs Reg.witnessC < first + length ∧
      AB (a i) (b i) + BC (b i) (y.regs Reg.witnessC) +
        AC (a i) (y.regs Reg.witnessC) = 0)
  let Φ (y : Data 400) := 8 * (Q - y.regs Reg.index) +
    (42 * length + 28) * (Nat.count active Q - Nat.count active (y.regs Reg.index))
  have hstart : I x := by
    refine ⟨hx, rfl, by omega, ?_, ?_, ?_⟩
    · simp only [hi, hf, foundBefore_zero, Bool.toNat_false]
    · simp only [hi, hs, Nat.count_zero]
    · intro h; omega
  have body (y : Data 400) (hy : I y) (hcond : (Cond.lt Reg.index Reg.count).Holds y) :
      ∃ z T, ExecWithin (w + 2) step y z T ∧ I z ∧ T + 2 + Φ z ≤ Φ y := by
    obtain ⟨yFixed, ym, yi, yf, ys, yw⟩ := hy
    let i := y.regs Reg.index
    change y.regs Reg.found = (foundBefore accept hit i).toNat at yf
    have hilt : i < Q := by simpa only [Cond.holds_lt, yFixed.count] using hcond
    have hscans : y.regs Reg.scans ≤ Q := by
      rw [ys]
      exact (Nat.count_le active).trans yi
    have hstepfit : Fits (w + 2)
        (out + queries + 3 * i + y.regs Reg.scans + 6 * (n * n) + n + first + length + 40) :=
      hfit.of_le (by dsimp only [i]; omega)
    by_cases hact : active i
    · have hinfo : accept i = true ∧ foundBefore accept hit i = false := by
        simpa only [active, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false] using hact
      have yzero : y.regs Reg.found = 0 := by rw [yf, hinfo.2]; rfl
      have hanswer : y.mem (out + i) ≠ 0 := by
        rw [ym]
        exact of_decide_eq_true hinfo.1
      obtain ⟨haWord, hbWord, ha, hb⟩ := hquery i hilt
      obtain ⟨z, he, zFixed, zm, zi, zs, zf, zh, zw⟩ := exec_step_scan (i := i) AB BC AC y yFixed
        rfl rfl yzero hanswer (by simpa only [ym] using haWord)
        (by simpa only [ym] using hbWord) ha hb hc (by simpa only [ym] using hmem)
        hmag hU hstepfit
      have zflag : z.regs Reg.found = (hit i).toNat := by
        cases hh : hit i
        · have hn : z.regs Reg.found ≠ 1 := by
            intro h
            have := (hit_iff i).mpr (zh.mp h)
            simp only [hh, Bool.false_eq_true] at this
          rcases zf with hz | hz
          · simpa only [hh, Bool.toNat_false] using hz
          · exact (hn hz).elim
        · simpa only [hh, Bool.toNat_true] using zh.mpr ((hit_iff i).mp hh)
      have zI : I z := by
        refine ⟨zFixed, zm.trans ym, by omega, ?_, ?_, ?_⟩
        · rw [zi, foundBefore_succ, hinfo.1, hinfo.2]
          simpa only [Bool.true_and, Bool.false_or] using zflag
        · rw [zi, Nat.count_succ, ite_eq_left hact, ← ys]
          exact zs
        · intro hz
          obtain ⟨za, zb, zlo, zhi, zeq⟩ := zw hz
          exact ⟨i, by omega, by simpa only [ym] using hanswer, za, zb, zlo, zhi, zeq⟩
      refine ⟨z, 42 * length + 34, he, zI, ?_⟩
      have hp := potential_step active (T := 42 * length + 28) hilt
      simpa only [ite_eq_left hact, Φ, zi, i] using hp
    · have hskip : y.regs Reg.found ≠ 0 ∨ y.mem (out + i) = 0 := by
        by_cases hz : y.regs Reg.found = 0
        · right
          by_contra hn
          apply hact
          have ha : accept i = true := decide_eq_true (by simpa only [ym] using hn)
          have hb : foundBefore accept hit i = false := by
            have hz' : (foundBefore accept hit i).toNat = 0 := yf.symm.trans hz
            cases h : foundBefore accept hit i
            · rfl
            · simp only [h, Bool.toNat_true, Nat.one_ne_zero] at hz'
          simp only [active, ha, hb, Bool.not_false, Bool.true_and]
        · exact Or.inl hz
      obtain ⟨z, he, zFixed, zm, zi, frame⟩ := exec_step_skip (i := i) y yFixed rfl hskip
        (hfit.of_le (by dsimp only [i]; omega))
      have zfound : z.regs Reg.found = y.regs Reg.found :=
        frame _ (by decide) (by decide) (by decide)
      have zscans : z.regs Reg.scans = y.regs Reg.scans :=
        frame _ (by decide) (by decide) (by decide)
      have hnext : foundBefore accept hit (i + 1) = foundBefore accept hit i := by
        rw [foundBefore_succ]
        cases ha : accept i
        · simp only [Bool.false_and, Bool.or_false]
        · cases hb : foundBefore accept hit i
          · exact (hact (by simp [active, ha, hb])).elim
          · simp only [Bool.true_or]
      have zI : I z := by
        refine ⟨zFixed, zm.trans ym, by omega, ?_, ?_, ?_⟩
        · rw [zi, hnext, zfound]
          exact yf
        · rw [zi, Nat.count_succ, ite_eq_right hact, Nat.add_zero, zscans]
          exact ys
        · intro hz
          obtain ⟨j, hj, hm, hwa, hwb, hlo, hhi, hzsum⟩ := yw (zfound.symm.trans hz)
          have za := frame Reg.witnessA (by decide) (by decide) (by decide)
          have zb := frame Reg.witnessB (by decide) (by decide) (by decide)
          have zc := frame Reg.witnessC (by decide) (by decide) (by decide)
          exact ⟨j, by omega, hm, za.trans hwa, zb.trans hwb,
            by simpa only [zc] using hlo, by simpa only [zc] using hhi,
            by simpa only [zc] using hzsum⟩
      refine ⟨z, 6, he, zI, ?_⟩
      have hp := potential_step active (T := 42 * length + 28) hilt
      simpa only [ite_eq_right hact, Φ, zi, i] using hp
  obtain ⟨y, he, hIy, hend⟩ := ExecWithin.loop_potential I Φ body hstart
  obtain ⟨yFixed, ym, yi, yf, ys, yw⟩ := hIy
  have yindex : y.regs Reg.index = Q := by
    have hh : ¬ y.regs Reg.index < Q := by
      simpa only [Cond.holds_lt, yFixed.count] using hend
    omega
  have hcount := scan_count_le accept hit Q
  have hfail : Nat.count (fun i => (accept i && !hit i) = true) Q =
      Nat.count (fun i => x.mem (out + i) ≠ 0 ∧
        ∀ c : Fin length, AB (a i) (b i) + BC (b i) (first + c.val) +
          AC (a i) (first + c.val) ≠ 0) Q := by
    congr 1
    funext i
    simp only [accept, hit, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true_eq_eq_false, decide_eq_false_iff_not, not_exists]
  refine ⟨y, Nat.count active Q, ?_, yFixed, ym, yindex, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Φ, hi, Nat.sub_zero, Nat.count_zero, Nat.mul_zero, Nat.add_zero] using he
  · simpa only [yindex] using ys
  · rw [← hfail, yf, yindex]
    exact hcount
  · rw [yf, yindex]
    cases foundBefore accept hit Q <;> simp
  · rw [yf, yindex]
    simp only [Bool.toNat_eq_one, foundBefore_eq_true, accept, decide_eq_true_eq]
    constructor
    · rintro ⟨i, hi, ha, hh⟩
      exact ⟨i, hi, ha, (hit_iff i).mp hh⟩
    · rintro ⟨i, hi, ha, hh⟩
      exact ⟨i, hi, ha, (hit_iff i).mpr hh⟩
  · simpa only [yindex] using yw

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
