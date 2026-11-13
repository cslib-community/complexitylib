/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Copy
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.InputSpec

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

/-- One copy call of `exec_adapt`: copy the `N` words of a source square `s` below the workspace
base `b` to `D ≥ b`, adding their original sum to the running total `S`. The copy registers other
than the source, the registers below 608 and the memory below `b` are unchanged. -/
private theorem exec_copyStep {W : ℕ} {x c : Data 640} {b s D N S : ℕ} (h1 : Fits W 1)
    (hsrc : c.regs (copyBank 0) = s) (hdst : c.regs (copyBank 1) = D)
    (hlen : c.regs (copyBank 2) = N) (htotal : c.regs (copyBank 7) = S)
    (hmeta : ∀ j : Fin 640, j.val < 608 → c.regs j = x.regs j)
    (hbelow : ∀ q < b, c.mem q = x.mem q) (hs : s + N ≤ b) (hbD : b ≤ D)
    (hfit : Fits W (D + N + S + ArrayCopySum.wordSum x.mem s N)) :
    ∃ c', ExecWithin W (ArrayCopySum.program.rename copyBank) c c' (8 * N + 4) ∧
      c'.regs (copyBank 1) = D ∧ c'.regs (copyBank 2) = N ∧
      c'.regs (copyBank 7) = S + ArrayCopySum.wordSum x.mem s N ∧
      (∀ j : Fin 640, j.val < 608 → c'.regs j = x.regs j) ∧
      c'.mem = ArrayCopy.copyPrefix c.mem s D N ∧ ∀ q < b, c'.mem q = x.mem q := by
  have hsum : ArrayCopySum.wordSum c.mem s N = ArrayCopySum.wordSum x.mem s N :=
    Finset.sum_congr rfl fun q hq => hbelow _ (by have := Finset.mem_range.mp hq; omega)
  obtain ⟨c', hc', post, hregs⟩ := exec_copy c h1
    (by rw [hsrc, hlen]; exact hfit.of_le (by omega))
    (by rw [hdst, hlen]; exact hfit.of_le (by omega))
    (by rw [htotal, hsrc, hlen, hsum]; exact hfit.of_le (by omega))
    (by rw [hsrc, hdst, hlen]; omega)
  refine ⟨c', by simpa only [hlen] using hc', post.dst.trans hdst, post.len.trans hlen, ?_,
    fun j hj => (hregs j (Or.inl (by omega))).trans (hmeta j hj), ?_, fun q hq => ?_⟩
  · simpa only [htotal, hsrc, hlen, hsum] using post.total
  · rw [post.memory, hsrc, hdst, hlen]
  · rw [post.memory, hdst, ArrayCopy.copyPrefix_outside (by omega)]
    exact hbelow q hq

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
  obtain ⟨c₁, hc₁', c₁_dst, c₁_len, c₁_total, c₁_meta, cm₁, c₁_below⟩ :=
    exec_copyStep h1 a_src a_dst a_len a_total a_meta a_below hab (by omega)
      (fit.of_le (by change b + 5 + N + 0 + Sa ≤ _; omega))
  rw [Nat.zero_add] at c₁_total
  rw [amem, hmem] at cm₁
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
  obtain ⟨c₂, hc₂', c₂_dst, c₂_len, c₂_total, c₂_meta, cm₂, c₂_below⟩ :=
    exec_copyStep h1 d₂_src d₂_dst d₂_len d₂_total d₂_meta d₂_below hbc (by omega)
      (fit.of_le (by change b + 5 + N + N + Sa + Sb ≤ _; omega))
  rw [d₂mem] at cm₂
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
  obtain ⟨c₃, hc₃', -, -, c₃_total, c₃_meta, cm₃, -⟩ :=
    exec_copyStep h1 d₃_src d₃_dst d₃_len d₃_total d₃_meta d₃_below hac (by omega)
      (fit.of_le (by change b + 5 + N + N + N + (Sa + Sb) + Sc ≤ _; omega))
  rw [d₃mem] at cm₃
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
