/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Copy
public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.InputSpec

/-!
# Complete original-array adaptation and actual word accumulation

All three real copy calls operate only on original squares. Their sum and memory effects
are composed without a clean destination, a supplied list of words or a layout certificate.
The implementation interfaces here retain numerical fits; the complete caller derives them
from original input bounds and the computed virtual-window threshold.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime

open Cslib.WordRAM

/-- Original raw-word sum computed while copying the three source squares. -/
@[expose] def matrixWordSum (mem : ℕ → ℕ) (n ab bc ac : ℕ) : ℕ :=
  ArrayCopySum.wordSum mem ab (n * n) + ArrayCopySum.wordSum mem bc (n * n) +
    ArrayCopySum.wordSum mem ac (n * n)

/-- Original canonical source words identify the actual native sum with the original list
sum used by source-width admission. No additional matrix traversal is performed. -/
theorem matrixWordSum_eq_rawTotal {n ab bc ac : ℕ} (mem : ℕ → ℕ) (values : List ℤ)
    (vab : ∀ q < n * n, mem (ab + q) = Signed.encode (values.getD q 0))
    (vbc : ∀ q < n * n, mem (bc + q) = Signed.encode (values.getD (n * n + q) 0))
    (vac : ∀ q < n * n, mem (ac + q) = Signed.encode (values.getD (2 * (n * n) + q) 0)) :
    matrixWordSum mem n ab bc ac = rawTotal n values := by
  have ha : ArrayCopySum.wordSum mem ab (n * n) =
      ∑ q ∈ Finset.range (n * n), Signed.encode (values.getD q 0) :=
    Finset.sum_congr rfl (fun q hq => vab q (Finset.mem_range.mp hq))
  have hb : ArrayCopySum.wordSum mem bc (n * n) =
      ∑ q ∈ Finset.range (n * n), Signed.encode (values.getD (n * n + q) 0) :=
    Finset.sum_congr rfl (fun q hq => vbc q (Finset.mem_range.mp hq))
  have hc : ArrayCopySum.wordSum mem ac (n * n) =
      ∑ q ∈ Finset.range (n * n), Signed.encode (values.getD (2 * (n * n) + q) 0) :=
    Finset.sum_congr rfl (fun q hq => vac q (Finset.mem_range.mp hq))
  rw [matrixWordSum, ha, hb, hc, rawTotal_split]

/-- Actual stores/copies and their complete linear charge. The three sources may alias each
other, but precede workspace. Only original source/end/sum quantities occur in the fits. -/
theorem exec_adapt {W : ℕ} (x : Data 640)
    (hab : x.regs Reg.ab + x.regs Reg.n * x.regs Reg.n ≤ x.regs Reg.base)
    (hbc : x.regs Reg.bc + x.regs Reg.n * x.regs Reg.n ≤ x.regs Reg.base)
    (hac : x.regs Reg.ac + x.regs Reg.n * x.regs Reg.n ≤ x.regs Reg.base)
    (hfit : Fits W (x.regs Reg.base + 4 * (x.regs Reg.n * x.regs Reg.n) +
      matrixWordSum x.mem (x.regs Reg.n) (x.regs Reg.ab) (x.regs Reg.bc) (x.regs Reg.ac) +
      1024)) :
    ∃ y, ExecWithin W adapt x y (24 * (x.regs Reg.n * x.regs Reg.n) + 38) ∧
      y.mem = copyMemory x.mem (x.regs Reg.base) (x.regs Reg.n) (x.regs Reg.dimension)
        (x.regs Reg.groups) (x.regs Reg.prime) (x.regs Reg.ab) (x.regs Reg.bc) (x.regs Reg.ac) ∧
      y.regs Reg.total = matrixWordSum x.mem (x.regs Reg.n)
        (x.regs Reg.ab) (x.regs Reg.bc) (x.regs Reg.ac) ∧
      ∀ j : Fin 640, j.val < 608 → y.regs j = x.regs j := by
  let n := x.regs Reg.n
  let N := n * n
  let b := x.regs Reg.base
  let ab := x.regs Reg.ab
  let bc := x.regs Reg.bc
  let ac := x.regs Reg.ac
  let Sa := ArrayCopySum.wordSum x.mem ab N
  let Sb := ArrayCopySum.wordSum x.mem bc N
  let Sc := ArrayCopySum.wordSum x.mem ac N
  let T := Sa + Sb + Sc
  have fit : Fits W (b + 4 * N + T + 1024) := hfit
  have h1 : Fits W 1 := fit.of_le (by omega)
  have sum_eq (mem : ℕ → ℕ) (hmem : ∀ q < b, mem q = x.mem q)
      (src : ℕ) (hsrc : src + N ≤ b) :
      ArrayCopySum.wordSum mem src N = ArrayCopySum.wordSum x.mem src N := by
    apply Finset.sum_congr rfl
    intro q hq
    exact hmem _ (by have := Finset.mem_range.mp hq; omega)
  obtain ⟨h, hh, harea, hconstant, hmem, hregs⟩ := exec_header x (fit.of_le (by
    change b + 4 * N + 1024 ≤ b + 4 * N + T + 1024
    omega))
  have hbelow (q : ℕ) (hq : q < b) : h.mem q = x.mem q := by
    rw [hmem]
    exact headerMemory_below _ _ _ _ _ _ _ hq
  obtain ⟨a, ha, amem, asrc, adst, alen, atotal, aregs⟩ := exec_firstCopy h hconstant
    (by rw [hregs Reg.base (by decide)]; exact fit.of_le (by omega))
  have a_src : a.regs (copyBank 0) = ab := asrc.trans (hregs Reg.ab (by decide))
  have a_dst : a.regs (copyBank 1) = b + 5 := by rw [adst, hregs Reg.base (by decide)]
  have a_len : a.regs (copyBank 2) = N := alen.trans harea
  have a_total : a.regs (copyBank 7) = 0 := atotal
  have a_meta (j : Fin 640) (hj : j.val < 608) : a.regs j = x.regs j :=
    (aregs j (by omega)).trans (hregs j (by omega))
  have a_below (q : ℕ) (hq : q < b) : a.mem q = x.mem q := by rw [amem]; exact hbelow q hq
  have a_sum : ArrayCopySum.wordSum a.mem ab N = Sa := sum_eq a.mem a_below ab hab
  obtain ⟨c₁, hc₁, c₁mem, c₁src, c₁dst, c₁len, c₁total, c₁regs⟩ := exec_copy a h1
    (by rw [a_src, a_len]; exact fit.of_le (by omega))
    (by rw [a_dst, a_len]; exact fit.of_le (by omega))
    (by rw [a_total, a_src, a_len, a_sum]; exact fit.of_le (by omega))
    (by rw [a_src, a_dst, a_len]; omega)
  have hc₁' : ExecWithin W (ArrayCopySum.program.rename copyBank) a c₁ (8 * N + 4) := by
    simpa only [a_len] using hc₁
  have c₁_dst : c₁.regs (copyBank 1) = b + 5 := c₁dst.trans a_dst
  have c₁_len : c₁.regs (copyBank 2) = N := c₁len.trans a_len
  have c₁_total : c₁.regs (copyBank 7) = Sa := by
    simpa only [a_total, a_src, a_len, a_sum, Nat.zero_add] using c₁total
  have c₁_meta (j : Fin 640) (hj : j.val < 608) : c₁.regs j = x.regs j :=
    (c₁regs j (Or.inl (by omega))).trans (a_meta j hj)
  have cm₁ : c₁.mem = ArrayCopy.copyPrefix
      (headerMemory x.mem b n (x.regs Reg.dimension) (x.regs Reg.groups) (x.regs Reg.prime))
      ab (b + 5) N := by rw [c₁mem, a_src, a_dst, a_len, amem, hmem]
  have c₁_below (q : ℕ) (hq : q < b) : c₁.mem q = x.mem q := by
    rw [c₁mem, a_dst, ArrayCopy.copyPrefix_outside (by omega)]
    exact a_below q hq
  obtain ⟨d₂, hd₂, d₂mem, d₂src, d₂dst, d₂len, d₂total, d₂regs⟩ :=
    exec_nextCopy Reg.bc c₁ (by rw [c₁_dst, c₁_len]; exact fit.of_le (by omega))
  have d₂_src : d₂.regs (copyBank 0) = bc := d₂src.trans (c₁_meta Reg.bc (by decide))
  have d₂_dst : d₂.regs (copyBank 1) = b + 5 + N := by rw [d₂dst, c₁_dst, c₁_len]
  have d₂_len : d₂.regs (copyBank 2) = N := d₂len.trans c₁_len
  have d₂_total : d₂.regs (copyBank 7) = Sa := d₂total.trans c₁_total
  have d₂_meta (j : Fin 640) (hj : j.val < 608) : d₂.regs j = x.regs j :=
    (d₂regs j (by omega)).trans (c₁_meta j hj)
  have d₂_below (q : ℕ) (hq : q < b) : d₂.mem q = x.mem q := by
    rw [d₂mem]; exact c₁_below q hq
  have d₂_sum : ArrayCopySum.wordSum d₂.mem bc N = Sb := sum_eq d₂.mem d₂_below bc hbc
  obtain ⟨c₂, hc₂, c₂mem, c₂src, c₂dst, c₂len, c₂total, c₂regs⟩ := exec_copy d₂ h1
    (by rw [d₂_src, d₂_len]; exact fit.of_le (by omega))
    (by rw [d₂_dst, d₂_len]; exact fit.of_le (by omega))
    (by rw [d₂_total, d₂_src, d₂_len, d₂_sum]; exact fit.of_le (by omega))
    (by rw [d₂_src, d₂_dst, d₂_len]; omega)
  have hc₂' : ExecWithin W (ArrayCopySum.program.rename copyBank) d₂ c₂ (8 * N + 4) := by
    simpa only [d₂_len] using hc₂
  have c₂_dst : c₂.regs (copyBank 1) = b + 5 + N := c₂dst.trans d₂_dst
  have c₂_len : c₂.regs (copyBank 2) = N := c₂len.trans d₂_len
  have c₂_total : c₂.regs (copyBank 7) = Sa + Sb := by
    simpa only [d₂_total, d₂_src, d₂_len, d₂_sum] using c₂total
  have c₂_meta (j : Fin 640) (hj : j.val < 608) : c₂.regs j = x.regs j :=
    (c₂regs j (Or.inl (by omega))).trans (d₂_meta j hj)
  have cm₂ : c₂.mem = ArrayCopy.copyPrefix c₁.mem bc (b + 5 + N) N := by
    rw [c₂mem, d₂_src, d₂_dst, d₂_len, d₂mem]
  have c₂_below (q : ℕ) (hq : q < b) : c₂.mem q = x.mem q := by
    rw [c₂mem, d₂_dst, ArrayCopy.copyPrefix_outside (by omega)]
    exact d₂_below q hq
  obtain ⟨d₃, hd₃, d₃mem, d₃src, d₃dst, d₃len, d₃total, d₃regs⟩ :=
    exec_nextCopy Reg.ac c₂ (by rw [c₂_dst, c₂_len]; exact fit.of_le (by omega))
  have d₃_src : d₃.regs (copyBank 0) = ac := d₃src.trans (c₂_meta Reg.ac (by decide))
  have d₃_dst : d₃.regs (copyBank 1) = b + 5 + N + N := by rw [d₃dst, c₂_dst, c₂_len]
  have d₃_len : d₃.regs (copyBank 2) = N := d₃len.trans c₂_len
  have d₃_total : d₃.regs (copyBank 7) = Sa + Sb := d₃total.trans c₂_total
  have d₃_meta (j : Fin 640) (hj : j.val < 608) : d₃.regs j = x.regs j :=
    (d₃regs j (by omega)).trans (c₂_meta j hj)
  have d₃_below (q : ℕ) (hq : q < b) : d₃.mem q = x.mem q := by
    rw [d₃mem]; exact c₂_below q hq
  have d₃_sum : ArrayCopySum.wordSum d₃.mem ac N = Sc := sum_eq d₃.mem d₃_below ac hac
  obtain ⟨c₃, hc₃, c₃mem, c₃src, c₃dst, c₃len, c₃total, c₃regs⟩ := exec_copy d₃ h1
    (by rw [d₃_src, d₃_len]; exact fit.of_le (by omega))
    (by rw [d₃_dst, d₃_len]; exact fit.of_le (by omega))
    (by rw [d₃_total, d₃_src, d₃_len, d₃_sum]; exact fit.of_le (by omega))
    (by rw [d₃_src, d₃_dst, d₃_len]; omega)
  have hc₃' : ExecWithin W (ArrayCopySum.program.rename copyBank) d₃ c₃ (8 * N + 4) := by
    simpa only [d₃_len] using hc₃
  have c₃_total : c₃.regs (copyBank 7) = T := by
    simpa only [d₃_total, d₃_src, d₃_len, d₃_sum] using c₃total
  have c₃_meta (j : Fin 640) (hj : j.val < 608) : c₃.regs j = x.regs j :=
    (c₃regs j (Or.inl (by omega))).trans (d₃_meta j hj)
  have cm₃ : c₃.mem = ArrayCopy.copyPrefix c₂.mem ac (b + 5 + N + N) N := by
    rw [c₃mem, d₃_src, d₃_dst, d₃_len, d₃mem]
  let y := c₃.set Reg.total T
  have hsave : ExecWithin (B := .standard) W (.op (.copy Reg.total (copyBank 7))) c₃ y 1 := by
    simpa only [y, c₃_total] using
      (ExecWithin.copy (B := .standard) (w := W) (d := Reg.total) (s := copyBank 7) (x := c₃))
  refine ⟨y, (hh.seq (ha.seq (hc₁'.seq (hd₂.seq (hc₂'.seq (hd₃.seq (hc₃'.seq hsave))))))).mono
    (by change 17 + (4 + (8 * N + 4 + (2 + (8 * N + 4 + (2 + (8 * N + 4 + 1)))))) ≤
          24 * N + 38
        omega), ?_, ?_, ?_⟩
  · change c₃.mem = _
    rw [cm₃, cm₂, cm₁]
    rfl
  · change (c₃.set Reg.total T).regs Reg.total = T
    exact Function.update_self Reg.total T c₃.regs
  · intro j hj
    have hne : j ≠ Reg.total := by
      intro he
      have hv := congrArg Fin.val he
      change j.val = 608 at hv
      omega
    simpa only [y, Data.set_regs, Function.update_of_ne hne] using c₃_meta j hj

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
