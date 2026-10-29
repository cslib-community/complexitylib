/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Notation
public import Mathlib.Data.Nat.Count

/-!
# Native row-major residue-class queries

The program scans a square residue matrix and writes the row and column of each entry equal to
the runtime query residue. Its output order is the row-major order used by the existing finite
chunk construction. Prefix ranks use Mathlib's `Nat.count`.

This directly adapts the query-class construction in the pinned
[Theorem 17 class builder](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem17/Instances/Classes.lean).
The per-class scan is charged explicitly; composing all residue classes multiplies its bound by
the modulus. No class-membership or query-list table is supplied to the program.

## Main definitions

* `QueryScan.program`: the fixed twelve-register query scan.

## Main results

* `QueryScan.exec`: actual scan execution, exact ranks and the output-prefix frame.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.QueryScan

open Cslib.WordRAM

/-- Square residue input pointer. -/
abbrev src : Fin 12 := 0
/-- Output pointer for consecutive row/column pairs. -/
abbrev dst : Fin 12 := 1
/-- Matrix side. -/
abbrev size : Fin 12 := 2
/-- Selected residue. -/
abbrev residue : Fin 12 := 3
/-- Flat input cursor. -/
abbrev idx : Fin 12 := 4
/-- Input area. -/
abbrev area : Fin 12 := 5
/-- Number of emitted pairs. -/
abbrev count : Fin 12 := 6
/-- Address temporary. -/
abbrev addr : Fin 12 := 7
/-- Loaded residue. -/
abbrev key : Fin 12 := 8
/-- Constant one. -/
abbrev one : Fin 12 := 9
/-- Output row. -/
abbrev row : Fin 12 := 10
/-- Output column. -/
abbrev col : Fin 12 := 11

/-- Every successful match computes both coordinates and stores their two words. -/
def body : Code .standard 12 := ram[
  addr ← src + idx; key ← *addr;
  if key = residue then [
    row ← idx / size; col ← idx % size; addr ← count + count; addr ← addr + dst;
    *addr ← row; addr ← addr + one; *addr ← col; count ← count + one
  ] else [ count ← count ];
  idx ← idx + one ]

/-- Constants, counters and matrix area are initialized by actual instructions. -/
def program : Code .standard 12 :=
  .seq (ram[ one ← #1; idx ← #0; count ← #0; area ← size * size ])
    (.loop (.lt idx area) body)

/-- The query scanner has a fixed instruction graph and no physical-width reads. -/
theorem program_fixed : program.size ≤ 32 ∧ ¬program.ReadsWidth := by decide

private theorem body_preserves : ∀ i : Fin 12,
    (i.val < 4 ∨ i = area ∨ i = one) → body.Preserves i := by decide

private theorem exec_body {w : ℕ} (x : Data 12) (R : ℕ → ℕ)
    (ho : x.regs one = 1) (hq : x.regs idx < x.regs size * x.regs size)
    (hc : x.regs count ≤ x.regs idx)
    (hinput : x.mem (x.regs src + x.regs idx) = R (x.regs idx))
    (hsrc : Fits w (x.regs src + x.regs size * x.regs size))
    (hdst : Fits w (x.regs dst + 2 * (x.regs size * x.regs size))) :
    ∃ y, ExecWithin w body x y 12 ∧ y.regs idx = x.regs idx + 1 ∧
      y.regs count = x.regs count + (if R (x.regs idx) = x.regs residue then 1 else 0) ∧
      y.mem = (if R (x.regs idx) = x.regs residue then
        Function.update (Function.update x.mem (x.regs dst + 2 * x.regs count)
          (x.regs idx / x.regs size)) (x.regs dst + 2 * x.regs count + 1)
            (x.regs idx % x.regs size) else x.mem) := by
  let q := x.regs idx
  let c := x.regs count
  let n := x.regs size
  let d := x.regs dst
  have hread : Fits w (x.regs src + q) := hsrc.of_le (by dsimp [q]; omega)
  have hqfit : Fits w q := hsrc.of_le (by dsimp [q]; omega)
  have hdiv : Fits w (q / n) := hqfit.of_le (Nat.div_le_self ..)
  have hmod : Fits w (q % n) := hqfit.of_le (Nat.mod_le ..)
  have hdouble : Fits w (c + c) := hdst.of_le (by dsimp [c] at *; omega)
  have hdest : Fits w (c + c + d) := hdst.of_le (by dsimp [c, d] at *; omega)
  have hnext : Fits w (c + c + d + 1) := hdst.of_le (by dsimp [c, d] at *; omega)
  have hcount : Fits w (c + 1) := hdst.of_le (by dsimp [c] at *; omega)
  have hidx : Fits w (q + 1) := hsrc.of_le (by dsimp [q]; omega)
  let a := x.set addr (x.regs src + q) |>.set key (R q)
  let b := if R q = x.regs residue then
      a.set row (q / n) |>.set col (q % n) |>.set addr (c + c)
      |>.set addr (c + c + d) |>.write (c + c + d) (q / n)
      |>.set addr (c + c + d + 1) |>.write (c + c + d + 1) (q % n) |>.set count (c + 1)
    else a.set count c
  let y := b.set idx (q + 1)
  refine ⟨y, ?_, ?_, ?_, ?_⟩
  · by_cases h : R q = x.regs residue <;>
      ram_eval [body, a, b, y, q, c, n, d, ho, h, hinput, hread, hdiv, hmod, hdouble,
        hdest, hnext, hcount, hidx, src, dst, size, residue, idx, count, addr, key, one,
        row, col, Fin.mk.injEq]
  · simp [y, q]
  · by_cases h : R q = x.regs residue <;>
      simp +decide [y, b, a, q, c, h, count, idx, addr, key, row, col]
  · by_cases h : R q = x.regs residue
    · change R (x.regs idx) = x.regs residue at h
      simp only [y, b, a, q, n, c, d, h, ↓reduceIte, Data.set_mem, Data.write_mem]
      congr 2 <;> omega
    · change ¬R (x.regs idx) = x.regs residue at h
      simp only [y, b, a, q, h, ↓reduceIte, Data.set_mem]

/-- Scan an actual residue matrix, preserving the input and all cells outside the emitted pair
prefix. Each selected flat position is stored at its exact row-major rank, counted by `Nat.count`.
The final halt is excluded from the `14n²+6` instruction bound. -/
theorem exec {w : ℕ} (x : Data 12) (R : ℕ → ℕ) (h1 : Fits w 1)
    (hinput : ∀ i < x.regs size * x.regs size, x.mem (x.regs src + i) = R i)
    (hsrc : Fits w (x.regs src + x.regs size * x.regs size))
    (hdst : Fits w (x.regs dst + 2 * (x.regs size * x.regs size)))
    (hdisj : x.regs src + x.regs size * x.regs size ≤ x.regs dst) :
    ∃ y, ExecWithin w program x y (14 * (x.regs size * x.regs size) + 6) ∧
      y.regs idx = x.regs size * x.regs size ∧
      y.regs count = Nat.count (fun j => R j = x.regs residue) (x.regs size * x.regs size) ∧
      (∀ i : Fin 12, i.val < 4 → y.regs i = x.regs i) ∧
      (∀ q < x.regs size * x.regs size, R q = x.regs residue →
        y.mem (x.regs dst + 2 * Nat.count (fun j => R j = x.regs residue) q) = q / x.regs size ∧
        y.mem (x.regs dst + 2 * Nat.count (fun j => R j = x.regs residue) q + 1) =
          q % x.regs size) ∧
      (∀ a, ¬(x.regs dst ≤ a ∧ a < x.regs dst + 2 * y.regs count) → y.mem a = x.mem a) := by
  let C := Nat.count (fun j => R j = x.regs residue)
  let n := x.regs size
  let d := x.regs dst
  let I (y : Data 12) : Prop :=
    (∀ i : Fin 12, i.val < 4 → y.regs i = x.regs i) ∧
      y.regs area = n * n ∧ y.regs one = 1 ∧ y.regs idx ≤ n * n ∧
      y.regs count = C (y.regs idx) ∧
      (∀ q < y.regs idx, R q = x.regs residue →
        y.mem (d + 2 * C q) = q / n ∧ y.mem (d + 2 * C q + 1) = q % n) ∧
      (∀ a, ¬(d ≤ a ∧ a < d + 2 * C (y.regs idx)) → y.mem a = x.mem a)
  have hbody (y : Data 12) (hy : I y) (hcond : (Cond.lt idx area).Holds y) :
      ∃ z, ExecWithin w body y z 12 ∧ I z ∧ n * n - z.regs idx < n * n - y.regs idx := by
    obtain ⟨hyr, hya, hyo, hyi, hyc, hycells, hyout⟩ := hy
    have hyn : y.regs size = n := hyr size (by decide)
    have hyd : y.regs dst = d := hyr dst (by decide)
    have hys : y.regs src = x.regs src := hyr src (by decide)
    have hyρ : y.regs residue = x.regs residue := hyr residue (by decide)
    have hlt : y.regs idx < n * n := by simpa only [Cond.holds_lt, hya] using hcond
    have hread : y.mem (y.regs src + y.regs idx) = R (y.regs idx) := by
      rw [hys, hyout _ (by dsimp [d, n] at *; omega)]
      exact hinput _ hlt
    have hcle : y.regs count ≤ y.regs idx := by rw [hyc]; exact Nat.count_le _
    obtain ⟨z, he, hzi, hzc, hzm⟩ := exec_body y R hyo (by simpa only [hyn] using hlt)
      hcle hread (by simpa only [hys, hyn] using hsrc)
      (by simpa only [hyd, hyn] using hdst)
    have hsucc : C (y.regs idx + 1) =
        C (y.regs idx) + if R (y.regs idx) = x.regs residue then 1 else 0 := Nat.count_succ _ _
    have hzc' : z.regs count = C (z.regs idx) := by
      rw [hzi]
      simpa only [hyc, hyρ, hsucc] using hzc
    have hpres (i : Fin 12) (hi : i.val < 4 ∨ i = area ∨ i = one) :
        z.regs i = y.regs i := he.regs_eq (body_preserves i hi)
    simp only [hyd, hyn, hyc, hyρ] at hzm
    refine ⟨z, he, ⟨fun i hi => (hpres i (Or.inl hi)).trans (hyr i hi),
      (hpres area (by simp)).trans hya, (hpres one (by simp)).trans hyo,
      by omega, hzc', ?_, ?_⟩, by omega⟩
    · intro j hj hkey
      by_cases h : R (y.regs idx) = x.regs residue
      · simp only [h, ↓reduceIte] at hzm
        by_cases hji : j = y.regs idx
        · subst j
          rw [hzm]
          constructor
          · rw [Function.update_of_ne (by omega), Function.update_self]
          · exact Function.update_self ..
        · have hjlt : j < y.regs idx := by omega
          have hrank : C j < C (y.regs idx) := Nat.count_strict_mono hkey hjlt
          obtain ⟨hrow, hcol⟩ := hycells j hjlt hkey
          rw [hzm]
          constructor
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hrow
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hcol
      · simp only [h, ↓reduceIte] at hzm
        rw [hzm]
        have hne : j ≠ y.regs idx := by
          intro hj
          exact h (hj ▸ hkey)
        exact hycells j (by omega) hkey
    · intro a ha
      by_cases h : R (y.regs idx) = x.regs residue
      · simp only [h, ↓reduceIte] at hzm
        have hcstep : C (z.regs idx) = C (y.regs idx) + 1 := by
          simp only [hzi, hsucc, h, ↓reduceIte]
        rw [hzm, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hyout a (by omega)
      · simp only [h, ↓reduceIte] at hzm
        have hcstep : C (z.regs idx) = C (y.regs idx) := by
          simp only [hzi, hsucc, h, ↓reduceIte, Nat.add_zero]
        rw [hzm]
        exact hyout a (by omega)
  have harea : Fits w (n * n) := hsrc.of_le (by dsimp [n]; omega)
  let x₀ := x.set one 1 |>.set idx 0 |>.set count 0 |>.set area (n * n)
  have hx₀ : I x₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      have ho : i ≠ one := by intro h; subst i; change 9 < 4 at hi; omega
      have hi' : i ≠ idx := by intro h; subst i; change 4 < 4 at hi; omega
      have hc : i ≠ count := by intro h; subst i; change 6 < 4 at hi; omega
      have ha : i ≠ area := by intro h; subst i; change 5 < 4 at hi; omega
      simp only [x₀, Data.set_regs, Function.update_of_ne ho, Function.update_of_ne hi',
        Function.update_of_ne hc, Function.update_of_ne ha]
    · simp [x₀]
    · simp +decide [x₀, one, idx, count, area]
    · simp +decide [x₀, idx, count, area]
    · simp +decide [x₀, idx, count, area, C]
    · intro j hj
      simp +decide only [x₀, Data.set_regs, Function.update_apply, idx, count, area,
        ↓reduceIte] at hj
      omega
    · intro a _
      rfl
  have hinit : ExecWithin w (ram[ one ← #1; idx ← #0; count ← #0; area ← size * size ])
      x x₀ 4 := by
    ram_eval [x₀, n, h1, harea, one, idx, count, area, size, Fin.mk.injEq]
  obtain ⟨y, hy, hI, hc⟩ := ExecWithin.loop_invariant I
    (fun y => n * n - y.regs idx) hbody hx₀
  obtain ⟨hr, ha, -, hi, hcount, hcells, hout⟩ := hI
  have hend : y.regs idx = n * n := by
    simp only [Cond.holds_lt, ha] at hc
    omega
  refine ⟨y, ?_, hend, by simpa only [hend] using hcount, hr, ?_, ?_⟩
  · convert hinit.seq hy using 1
    · rfl
    · simp +decide only [x₀, Data.set_regs, Function.update_apply, idx, count, area,
        ↓reduceIte]
      dsimp [n]
      omega
  · simpa only [hend] using hcells
  · intro a ha
    apply hout a
    simpa only [← hcount] using ha

end Cslib.Algorithms.WordRAM.ExactTriangle.QueryScan
