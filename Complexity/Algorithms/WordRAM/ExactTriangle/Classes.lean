/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.QueryScan

/-!
# Native residue-class query lists

The fixed program calls `QueryScan.program` for each residue, storing the computed class count
and its row-major coordinate pairs. Each class receives a disjoint block of capacity `2n²`.
The cost of scanning once per residue is included; no class table is supplied as input.

This adapts the class builder in the pinned
[Theorem 17 program](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem17/Instances/Classes.lean).

## Main definitions

* `Classes.program`: fixed twenty-register class enumeration.

## Main results

* `Classes.exec`: actual execution, class counts, coordinate readback and a memory frame.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.Classes

open Cslib.WordRAM

/-- Source residue matrix. -/
abbrev src : Fin 20 := 0
/-- Query-scanner output pointer. -/
abbrev dst : Fin 20 := 1
/-- Matrix side. -/
abbrev size : Fin 20 := 2
/-- Query-scanner selected residue. -/
abbrev residue : Fin 20 := 3
/-- Query-scanner emitted count. -/
abbrev count : Fin 20 := 6
/-- Array of class counts. -/
abbrev counts : Fin 20 := 12
/-- Array of disjoint query blocks. -/
abbrev queries : Fin 20 := 13
/-- Number of residues to enumerate. -/
abbrev modulus : Fin 20 := 14
/-- Current class. -/
abbrev cursor : Fin 20 := 15
/-- Constant one. -/
abbrev one : Fin 20 := 16
/-- Count address. -/
abbrev addr : Fin 20 := 17
/-- Capacity in words of a query block. -/
abbrev stride : Fin 20 := 18

private abbrev scanReg : Fin 12 → Fin 20 := Fin.castLE (by decide)

private theorem scanReg_injective : Function.Injective scanReg := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 20 => k.val) h)

/-- Reuse the certified scanner with a disjoint register bank for the outer loop. -/
def scan : Code .standard 20 := QueryScan.program.rename (Fin.castLE (by decide))

/-- Compute the class's output pointer, scan, record its count, and advance. -/
def body : Code .standard 20 :=
  .seq (ram[ dst ← cursor * stride; dst ← dst + queries; residue ← cursor ])
    (.seq scan (ram[ addr ← counts + cursor; *addr ← count; cursor ← cursor + one ]))

/-- The modulus is runtime data; the program itself is independent of it. -/
def program : Code .standard 20 :=
  .seq (ram[ one ← #1; cursor ← #0; stride ← size * size; stride ← stride + stride ])
    (.loop (.lt cursor modulus) body)

/-- Fixed instruction graph, with no physical-width reads. -/
theorem program_fixed : program.size ≤ 64 ∧ ¬program.ReadsWidth := by decide

private theorem scan_preserves : ∀ i : Fin 20, 12 ≤ i.val → scan.Preserves i := by decide

private theorem body_preserves : ∀ i : Fin 20,
    (i = src ∨ i = size ∨ i = counts ∨ i = queries ∨ i = modulus ∨ i = one ∨ i = stride) →
      body.Preserves i := by decide

/-- Enumerate every residue class into actual count and coordinate arrays. The source matrix,
count array and query capacity blocks must occur in that order. The final halt is excluded. -/
theorem exec {w : ℕ} (x : Data 20) (R : ℕ → ℕ) (h1 : Fits w 1)
    (hinput : ∀ q < x.regs size * x.regs size, x.mem (x.regs src + q) = R q)
    (hsource : x.regs src + x.regs size * x.regs size ≤ x.regs counts)
    (hblocks : x.regs counts + x.regs modulus ≤ x.regs queries)
    (hcount : Fits w (x.regs counts + x.regs modulus))
    (hquery : Fits w (x.regs queries + 2 * (x.regs size * x.regs size) * x.regs modulus))
    (harea : Fits w (2 * (x.regs size * x.regs size))) :
    ∃ y, ExecWithin w program x y
        (x.regs modulus * (14 * (x.regs size * x.regs size) + 14) + 6) ∧
      y.regs cursor = x.regs modulus ∧
      (∀ j < x.regs modulus,
        y.mem (x.regs counts + j) = Nat.count (fun q => R q = j)
          (x.regs size * x.regs size)) ∧
      (∀ j < x.regs modulus, ∀ q < x.regs size * x.regs size, R q = j →
        y.mem (x.regs queries + 2 * (x.regs size * x.regs size) * j +
          2 * Nat.count (fun k => R k = j) q) = q / x.regs size ∧
        y.mem (x.regs queries + 2 * (x.regs size * x.regs size) * j +
          2 * Nat.count (fun k => R k = j) q + 1) = q % x.regs size) ∧
      (∀ a, ¬(x.regs counts ≤ a ∧ a < x.regs counts + x.regs modulus) →
        ¬(x.regs queries ≤ a ∧
          a < x.regs queries + 2 * (x.regs size * x.regs size) * x.regs modulus) →
        y.mem a = x.mem a) := by
  let n := x.regs size
  let p := x.regs modulus
  let b := x.regs counts
  let d := x.regs queries
  let s := 2 * (n * n)
  let C (j q : ℕ) := Nat.count (fun k => R k = j) q
  change x.regs src + n * n ≤ b at hsource
  change b + p ≤ d at hblocks
  change Fits w (b + p) at hcount
  change Fits w (d + s * p) at hquery
  change Fits w s at harea
  let I (y : Data 20) : Prop :=
    (∀ i, i = src ∨ i = size ∨ i = counts ∨ i = queries ∨ i = modulus →
      y.regs i = x.regs i) ∧
      y.regs one = 1 ∧ y.regs stride = s ∧ y.regs cursor ≤ p ∧
      (∀ j < y.regs cursor, y.mem (b + j) = C j (n * n)) ∧
      (∀ j < y.regs cursor, ∀ q < n * n, R q = j →
        y.mem (d + s * j + 2 * C j q) = q / n ∧
        y.mem (d + s * j + 2 * C j q + 1) = q % n) ∧
      (∀ a, ¬(b ≤ a ∧ a < b + y.regs cursor) →
        ¬(d ≤ a ∧ a < d + s * y.regs cursor) → y.mem a = x.mem a)
  have hbody (y : Data 20) (hy : I y) (hc : (Cond.lt cursor modulus).Holds y) :
      ∃ z, ExecWithin w body y z (14 * (n * n) + 12) ∧ I z ∧
        p - z.regs cursor < p - y.regs cursor := by
    obtain ⟨hyr, hyo, hys, hyc, hycounts, hypairs, hyframe⟩ := hy
    have hyn : y.regs size = n := hyr size (by simp)
    have hyp : y.regs modulus = p := hyr modulus (by simp)
    have hyb : y.regs counts = b := hyr counts (by simp)
    have hyd : y.regs queries = d := hyr queries (by simp)
    have hysrc : y.regs src = x.regs src := hyr src (by simp)
    have hlt : y.regs cursor < p := by simpa only [Cond.holds_lt, hyp] using hc
    let j := y.regs cursor
    change j < p at hlt
    have hmul : s * (j + 1) ≤ s * p := Nat.mul_le_mul_left s hlt
    have hstep : s * (j + 1) = s * j + s := Nat.mul_succ s j
    have hsj : Fits w (j * s) := hquery.of_le (by rw [Nat.mul_comm j s]; omega)
    have hdest : Fits w (j * s + d) := hquery.of_le (by rw [Nat.mul_comm j s]; omega)
    let a := y.set dst (j * s) |>.set dst (j * s + d) |>.set residue j
    have hstart : ExecWithin w
        (ram[ dst ← cursor * stride; dst ← dst + queries; residue ← cursor ]) y a 3 := by
      ram_eval [a, j, hys, hyd, hsj, hdest, dst, queries, cursor, residue, stride, Fin.mk.injEq]
    have ha (i : Fin 20) (hi : i ≠ dst ∧ i ≠ residue) : a.regs i = y.regs i := by
      simp only [a, Data.set_regs, Function.update_of_ne hi.1, Function.update_of_ne hi.2]
    have ha_src : (a.comap scanReg).regs QueryScan.src = x.regs src := by
      change a.regs src = _
      rw [ha src (by decide), hysrc]
    have ha_size : (a.comap scanReg).regs QueryScan.size = n := by
      change a.regs size = _
      rw [ha size (by decide), hyn]
    have ha_dst : (a.comap scanReg).regs QueryScan.dst = j * s + d := by
      simp +decide [a, scanReg, QueryScan.dst, dst, residue]
    have ha_residue : (a.comap scanReg).regs QueryScan.residue = j := by
      simp +decide [a, scanReg, QueryScan.residue, residue]
    have hread : ∀ q < n * n, a.mem (x.regs src + q) = R q := by
      intro q hq
      change y.mem (x.regs src + q) = _
      rw [hyframe _ (by dsimp [b, n] at *; omega) (by dsimp [d, b, n] at *; omega)]
      exact hinput q hq
    obtain ⟨v, hv, -, hvc, hvr, hvpairs, hvframe⟩ := QueryScan.exec (a.comap scanReg) R h1
      (by simpa only [ha_src, ha_size, Data.comap_mem] using hread)
      (by rw [ha_src, ha_size]; exact hcount.of_le (by omega))
      (by rw [ha_dst, ha_size]; exact hquery.of_le (by rw [Nat.mul_comm j s]; omega))
      (by rw [ha_src, ha_size, ha_dst, Nat.mul_comm j s]; omega)
    simp only [ha_dst, ha_residue, ha_size] at hvc hvpairs hvframe
    let v' := v.extend scanReg a
    have hv' : ExecWithin w scan a v' (14 * (n * n) + 6) := by
      simpa only [ha_size, scan, v'] using hv.rename scanReg_injective
    have hvreg (i : Fin 20) (hi : 12 ≤ i.val) : v'.regs i = y.regs i :=
      (hv'.regs_eq (scan_preserves i hi)).trans (ha i (by
        constructor <;> intro heq <;> subst i <;> simp_all [dst, residue]))
    have hext (i : Fin 12) : v'.regs (scanReg i) = v.regs i :=
      scanReg_injective.extend_apply _ _ i
    have hvsrc : v'.regs src = y.regs src := by
      change v'.regs (scanReg QueryScan.src) = _
      rw [hext]
      have h := hvr QueryScan.src (by decide)
      change v.regs QueryScan.src = a.regs src at h
      exact h.trans (ha src (by decide))
    have hvsize : v'.regs size = y.regs size := by
      change v'.regs (scanReg QueryScan.size) = _
      rw [hext]
      have h := hvr QueryScan.size (by decide)
      change v.regs QueryScan.size = a.regs size at h
      exact h.trans (ha size (by decide))
    have hvcount : v'.regs count = C j (n * n) := by
      change v'.regs (scanReg QueryScan.count) = _
      rw [hext]
      exact hvc
    have hvj : v'.regs cursor = j := hvreg cursor (by decide)
    have hvone : v'.regs one = 1 := (hvreg one (by decide)).trans hyo
    have hvb : v'.regs counts = b := (hvreg counts (by decide)).trans hyb
    have haddr : Fits w (b + j) := hcount.of_le (by dsimp [b, p] at *; omega)
    have hj : Fits w (j + 1) := hcount.of_le (by dsimp [p] at *; omega)
    let z := v'.set addr (b + j) |>.write (b + j) (C j (n * n)) |>.set cursor (j + 1)
    have hend : ExecWithin w
        (ram[ addr ← counts + cursor; *addr ← count; cursor ← cursor + one ]) v' z 3 := by
      ram_eval [z, hvb, hvj, hvcount, hvone, haddr, hj, addr, counts, cursor, count, one,
        Fin.mk.injEq]
    have hpres (i : Fin 20)
        (hi : i = src ∨ i = size ∨ i = counts ∨ i = queries ∨ i = modulus ∨
          i = one ∨ i = stride) : z.regs i = y.regs i :=
      (hstart.seq (hv'.seq hend)).regs_eq (body_preserves i hi)
    have hzj : z.regs cursor = j + 1 := by simp [z]
    have hmem : z.mem = Function.update v.mem (b + j) (C j (n * n)) := rfl
    have hvframe' : ∀ q, ¬(d + s * j ≤ q ∧ q < d + s * (j + 1)) →
        v.mem q = y.mem q := by
      intro q hq
      apply hvframe q
      rw [hvc, Nat.mul_comm j s, Nat.add_comm (s * j) d]
      have hcle : C j (n * n) ≤ n * n := Nat.count_le _
      change ¬(d + s * j ≤ q ∧ q < d + s * j + 2 * C j (n * n))
      dsimp [s] at *
      omega
    have hcost : ExecWithin w body y z (14 * (n * n) + 12) := by
      convert hstart.seq (hv'.seq hend) using 1 <;> first | rfl | omega
    refine ⟨z, hcost, ⟨?_, ?_, ?_, by omega, ?_, ?_, ?_⟩, by omega⟩
    · intro i hi
      exact (hpres i (by rcases hi with h | h | h | h | h <;> simp [h])).trans (hyr i hi)
    · exact (hpres one (by simp)).trans hyo
    · exact (hpres stride (by simp)).trans hys
    · intro k hk
      rw [hzj] at hk
      rw [hmem]
      by_cases hkj : k = j
      · subst k
        exact Function.update_self ..
      · rw [Function.update_of_ne (by omega), hvframe' _ (by dsimp [b, d, p] at *; omega)]
        exact hycounts k (by omega)
    · intro k hk q hq hkey
      rw [hzj] at hk
      rw [hmem]
      have hrank : C k q < n * n := (Nat.count_le _).trans_lt hq
      have hcountaddr : b + j < d := by dsimp [b, d, p] at *; omega
      constructor
      · rw [Function.update_of_ne (by omega)]
        by_cases hkj : k = j
        · rw [hkj] at hkey ⊢
          simpa only [Nat.mul_comm j s, Nat.add_comm (s * j) d] using (hvpairs q hq hkey).1
        · rw [hvframe' _ (by
            have hmul' : s * (k + 1) ≤ s * j := Nat.mul_le_mul_left s (by omega)
            have hstep' : s * (k + 1) = s * k + s := Nat.mul_succ s k
            dsimp [s] at *; omega)]
          exact (hypairs k (by omega) q hq hkey).1
      · rw [Function.update_of_ne (by omega)]
        by_cases hkj : k = j
        · rw [hkj] at hkey ⊢
          simpa only [Nat.mul_comm j s, Nat.add_comm (s * j) d] using (hvpairs q hq hkey).2
        · rw [hvframe' _ (by
            have hmul' : s * (k + 1) ≤ s * j := Nat.mul_le_mul_left s (by omega)
            have hstep' : s * (k + 1) = s * k + s := Nat.mul_succ s k
            dsimp [s] at *; omega)]
          exact (hypairs k (by omega) q hq hkey).2
    · intro q hqb hqd
      rw [hzj] at hqb hqd
      rw [hmem, Function.update_of_ne (by omega), hvframe' q (by omega)]
      exact hyframe q (by omega) (by
        change ¬(d ≤ q ∧ q < d + s * j)
        have hmul' : s * j ≤ s * (j + 1) := Nat.mul_le_mul_left s (by omega)
        omega)
  let x₀ := x.set one 1 |>.set cursor 0 |>.set stride (n * n) |>.set stride s
  have hx₀ : I x₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;>
        simp +decide [x₀, src, size, counts, queries, modulus, one, cursor, stride]
    · simp +decide [x₀, one, cursor, stride]
    · simp [x₀]
    · simp +decide [x₀, cursor, stride]
    · simp +decide [x₀, cursor, stride]
    · simp +decide [x₀, cursor, stride]
    · intro q _ _
      rfl
  have hinit : ExecWithin w
      (ram[ one ← #1; cursor ← #0; stride ← size * size; stride ← stride + stride ]) x x₀ 4 := by
    have hnfit : Fits w (n * n) := harea.of_le (by change n * n ≤ 2 * (n * n); omega)
    have hdbl : Fits w (n * n + n * n) := by simpa only [s, two_mul] using harea
    dsimp [n] at hnfit hdbl
    ram_eval [x₀, n, s, two_mul, h1, hnfit, hdbl, one, cursor, stride, size, Fin.mk.injEq]
  obtain ⟨y, hy, hI, hc⟩ := ExecWithin.loop_invariant I
    (fun y => p - y.regs cursor) hbody hx₀
  obtain ⟨hyr, -, -, hyc, hycounts, hypairs, hyframe⟩ := hI
  have hyp : y.regs modulus = p := hyr modulus (by simp)
  have hend : y.regs cursor = p := by
    simp only [Cond.holds_lt, hyp] at hc
    omega
  refine ⟨y, ?_, hend, ?_, ?_, ?_⟩
  · convert hinit.seq hy using 1
    · rfl
    · simp +decide only [x₀, Data.set_regs, Function.update_apply, cursor, stride, ↓reduceIte]
      dsimp [n, p]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      omega
  · simpa only [hend] using hycounts
  · simpa only [hend] using hypairs
  · simpa only [hend] using hyframe

end Cslib.Algorithms.WordRAM.ExactTriangle.Classes
