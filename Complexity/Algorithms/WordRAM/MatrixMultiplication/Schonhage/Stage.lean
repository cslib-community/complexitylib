/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Cell

/-!
# Charged shared-coordinate array loop

## Main results

* `Encoding.exec_cells`: all cells in one shared coordinate transform, preserving the input
  and every memory cell outside the destination block.

## References

The forms are from [AlmanWilliams2026, Section 2.4.1]; see `Encoding` for provenance.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- The linear-form value at flat output position `i` of a stage with suffix stride `n`. -/
def stageResult (side : Bool) (n : ℕ) (v : ℕ → Fin 7 → ℤ) (i : ℕ) : ℤ :=
  ∑ a, coefficients side ⟨i / n % 10, Nat.mod_lt _ (by decide)⟩ a * v i a

/-- The complete cell loop has at most `207 * (10 * P * n) + 2` instructions. The seven
source entries for each output are shared values from the previous array, not separately
enumerated original input terms. Disjointness is permitted in either address order. -/
theorem exec_cells {w : ℕ} (hw : 0 < w) (side : Bool) (x : Data 32)
    (P n s d : ℕ) (hP : 0 < P) (hnpos : 0 < n)
    (hsrc : x.regs src = s) (hdst : x.regs dst = d) (hcell : x.regs cell = 0)
    (hn : x.regs stride = n) (hseven : x.regs seven = 7)
    (hten : x.regs ten = 10) (hone : x.regs one = 1)
    (hsize : x.regs stageSize = 10 * P * n)
    (v : ℕ → Fin 7 → ℤ) (B : ℤ) (hB : 0 ≤ B) (hv : ∀ i < 10 * P * n, ∀ a, |v i a| ≤ B)
    (hmem : ∀ i < 10 * P * n, ∀ a,
      x.mem (s + (i / (10 * n) * 7 + a.val) * n + i % n) = encode (v i a))
    (hval : 7 * B < (2 : ℤ) ^ (w - 1))
    (haddr : Fits (w + 2) (s + d + 64 + 64 * P * n))
    (hdisj : s + 7 * P * n ≤ d ∨ d + 10 * P * n ≤ s) :
    ∃ y, ExecWithin (w + 2) (.loop (.lt cell stageSize) (cellBody side)) x y
        (207 * (10 * P * n) + 2) ∧
      (∀ i < 10 * P * n, y.mem (d + i) = encode (stageResult side n v i)) ∧
      (∀ a, ¬(d ≤ a ∧ a < d + 10 * P * n) → y.mem a = x.mem a) ∧
      (∀ a, 9 ≤ a.val → ¬CellLocal a → y.regs a = x.regs a) := by
  let N := 10 * P * n
  let I (y : Data 32) : Prop :=
    (∀ a, 9 ≤ a.val → ¬CellLocal a → y.regs a = x.regs a) ∧ y.regs cell ≤ N ∧
      (∀ i < y.regs cell, y.mem (d + i) = encode (stageResult side n v i)) ∧
      (∀ a, ¬(d ≤ a ∧ a < d + y.regs cell) → y.mem a = x.mem a)
  have hbody (y : Data 32) (hy : I y) (hc : (Cond.lt cell stageSize).Holds y) :
      ∃ z, ExecWithin (w + 2) (cellBody side) y z 205 ∧ I z ∧
        N - z.regs cell < N - y.regs cell := by
    obtain ⟨hr, hiN, hm, hf⟩ := hy
    have hys : y.regs src = s := (hr src (by decide) (by decide)).trans hsrc
    have hyd : y.regs dst = d := (hr dst (by decide) (by decide)).trans hdst
    have hyn : y.regs stride = n := (hr stride (by decide) (by decide)).trans hn
    have hy7 : y.regs seven = 7 := (hr seven (by decide) (by decide)).trans hseven
    have hy10 : y.regs ten = 10 := (hr ten (by decide) (by decide)).trans hten
    have hy1 : y.regs one = 1 := (hr one (by decide) (by decide)).trans hone
    have hysz : y.regs stageSize = N := (hr stageSize (by decide) (by decide)).trans hsize
    have hi : y.regs cell < N := by simpa only [Cond.holds_lt, hysz] using hc
    have hyinput (a : Fin 7) :
        y.mem (s + (y.regs cell / (10 * n) * 7 + a.val) * n + y.regs cell % n) =
          encode (v (y.regs cell) a) := by
      have hp : y.regs cell / (10 * n) < P := by
        apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 10 * n)).mpr
        dsimp only [N] at hi
        nlinarith
      have hmod := Nat.mod_lt (y.regs cell) hnpos
      have hprefix : y.regs cell / (10 * n) * 7 + a.val < P * 7 := by omega
      have hproduct := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hprefix)
      have hoff : (y.regs cell / (10 * n) * 7 + a.val) * n + y.regs cell % n <
          P * 7 * n := by nlinarith only [hproduct, hmod]
      rw [Nat.mul_comm P 7] at hoff
      rw [hf _ ?_]
      · exact hmem _ hi a
      · rcases hdisj with h | h <;> dsimp only [N] at hiN <;> omega
    obtain ⟨z, he, hzmem, hzcell, hzreg⟩ := exec_cell hw side y P n s d (y.regs cell)
      hP hnpos hi hys hyd rfl hyn hy7 hy10 hy1 (v (y.regs cell)) B hB (hv _ hi)
      hyinput hval haddr
    refine ⟨z, he, ?_, by rw [hzcell]; omega⟩
    refine ⟨fun a ha hl => (hzreg a ha hl).trans (hr a ha hl), by omega, ?_, ?_⟩
    · intro i hzi
      rw [hzcell] at hzi
      by_cases hic : i = y.regs cell
      · subst i
        simp only [hzmem, Function.update_self, stageResult]
      · have hin : i < y.regs cell := by omega
        rw [hzmem, Function.update_of_ne (by omega : d + i ≠ d + y.regs cell)]
        exact hm i hin
    · intro a ha
      rw [hzcell] at ha
      have hne : a ≠ d + y.regs cell := by omega
      rw [hzmem, Function.update_of_ne hne]
      exact hf a (by omega)
  have hx : I x := by
    refine ⟨fun _ _ _ => rfl, by simp [hcell, N], ?_, ?_⟩
    · simp only [hcell, Nat.not_lt_zero, false_implies, implies_true]
    · intro a _
      rfl
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I (fun y => N - y.regs cell) hbody hx
  obtain ⟨hr, hi, hm, hf⟩ := hy
  have hysz : y.regs stageSize = N := (hr stageSize (by decide) (by decide)).trans hsize
  have hend : y.regs cell = N := by
    simp only [Cond.holds_lt, hysz] at hc
    omega
  refine ⟨y, ?_, ?_, ?_, hr⟩
  · simpa only [hcell, N, Nat.sub_zero, Nat.add_comm, Nat.mul_comm] using he
  · simpa only [hend] using hm
  · simpa only [hend] using hf

/-- Registers changed by the stage controller or its cell loop. -/
def StageLocal (i : Fin 32) : Prop :=
  CellLocal i ∨ i = stride ∨ i = stageSize ∨ i = src ∨ i = dst ∨ i = prefixes ∨ i = stage

instance (i : Fin 32) : Decidable (StageLocal i) :=
  inferInstanceAs (Decidable (CellLocal i ∨ i = stride ∨ i = stageSize ∨ i = src ∨
    i = dst ∨ i = prefixes ∨ i = stage))

private theorem stage_preserves (side : Bool) (i : Fin 32) :
    9 ≤ i.val → ¬StageLocal i → (stageBody side).Preserves i := by
  decide +kernel +revert

/-- A complete coordinate stage, including stride division, stage-size arithmetic, both
cell-loop control instructions per entry, buffer alternation and the next-stage counters. -/
theorem exec_stageBody {w : ℕ} (hw : 0 < w) (side : Bool) (x : Data 32)
    (P n s d j o q : ℕ) (hP : 0 < P) (hnpos : 0 < n)
    (hsrc : x.regs src = s) (hdst : x.regs dst = d) (hj : x.regs stage = j)
    (hn : x.regs stride = 7 * n) (hp : x.regs prefixes = P)
    (hseven : x.regs seven = 7) (hten : x.regs ten = 10) (hone : x.regs one = 1)
    (hout : x.regs output = o) (hscratch : x.regs scratch = q)
    (v : ℕ → Fin 7 → ℤ) (B : ℤ) (hB : 0 ≤ B) (hv : ∀ i < 10 * P * n, ∀ a, |v i a| ≤ B)
    (hmem : ∀ i < 10 * P * n, ∀ a,
      x.mem (s + (i / (10 * n) * 7 + a.val) * n + i % n) = encode (v i a))
    (hval : 7 * B < (2 : ℤ) ^ (w - 1))
    (haddr : Fits (w + 2) (s + d + 64 + 64 * P * n)) (hjfit : Fits (w + 2) (j + 1))
    (hdisj : s + 7 * P * n ≤ d ∨ d + 10 * P * n ≤ s) :
    ∃ y, ExecWithin (w + 2) (stageBody side) x y (207 * (10 * P * n) + 12) ∧
      (∀ i < 10 * P * n, y.mem (d + i) = encode (stageResult side n v i)) ∧
      (∀ a, ¬(d ≤ a ∧ a < d + 10 * P * n) → y.mem a = x.mem a) ∧
      y.regs src = d ∧ y.regs dst = (if d = o then q else o) ∧
      y.regs stride = n ∧ y.regs prefixes = 10 * P ∧ y.regs stage = j + 1 ∧
      (∀ a, 9 ≤ a.val → ¬StageLocal a → y.regs a = x.regs a) := by
  have hPn : n ≤ P * n := by nlinarith
  have h10P : Fits (w + 2) (P * 10) := haddr.of_le (by nlinarith)
  have hN : Fits (w + 2) (P * 10 * n) := haddr.of_le (by nlinarith)
  have hnfit : Fits (w + 2) n := haddr.of_le (by nlinarith)
  have hdiv : 7 * n / 7 = n := by omega
  let z := (((x.set stride n).set stageSize (P * 10)).set stageSize (P * 10 * n)).set cell 0
  have hz : ExecWithin (w + 2) stageHead x z 4 := by
    ram_eval [stageHead, z, hn, hseven, hp, hten, hdiv, hnfit, h10P, hN,
      stride, prefixes, ten, seven, stageSize, cell, Fin.mk.injEq]
  have hzr (a : Fin 32) (ha : a ≠ stride ∧ a ≠ stageSize ∧ a ≠ cell) :
      z.regs a = x.regs a := by
    simp only [z, Data.set_regs, Function.update_of_ne ha.1, Function.update_of_ne ha.2.1,
      Function.update_of_ne ha.2.2]
  obtain ⟨u, hu, hum, huf, hur⟩ := exec_cells hw side z P n s d hP hnpos
    ((hzr src (by decide)).trans hsrc) ((hzr dst (by decide)).trans hdst)
    (by simp [z]) (by simp [z, stride, stageSize, cell])
    ((hzr seven (by decide)).trans hseven) ((hzr ten (by decide)).trans hten)
    ((hzr one (by decide)).trans hone)
    (by simp [z, stageSize, cell, Nat.mul_comm]) v B hB hv hmem hval haddr hdisj
  have ur (a : Fin 32) (ha : 9 ≤ a.val) (hl : ¬CellLocal a)
      (hzl : a ≠ stride ∧ a ≠ stageSize ∧ a ≠ cell) : u.regs a = x.regs a :=
    (hur a ha hl).trans (hzr a hzl)
  have us : u.regs dst = d := (ur dst (by decide) (by decide) (by decide)).trans hdst
  have uo : u.regs output = o := (ur output (by decide) (by decide) (by decide)).trans hout
  have uq : u.regs scratch = q := (ur scratch (by decide) (by decide) (by decide)).trans hscratch
  have up : u.regs prefixes = P := (ur prefixes (by decide) (by decide) (by decide)).trans hp
  have uj : u.regs stage = j := (ur stage (by decide) (by decide) (by decide)).trans hj
  have ut : u.regs ten = 10 := (ur ten (by decide) (by decide) (by decide)).trans hten
  have u1 : u.regs one = 1 := (ur one (by decide) (by decide) (by decide)).trans hone
  have un : u.regs stride = n := by
    rw [hur stride (by decide) (by decide)]
    simp [z, stride, stageSize, cell]
  let y := (((u.set src d).set dst (if d = o then q else o)).set prefixes (P * 10)).set
    stage (j + 1)
  have hy : ExecWithin (w + 2) stageTail u y 6 := by
    by_cases hdo : d = o
    all_goals ram_eval [stageTail, y, us, uo, uq, up, uj, ut, u1, hdo, h10P, hjfit,
      src, dst, output, scratch, prefixes, stage, ten, one, Fin.mk.injEq]
  have he : ExecWithin (w + 2) (stageBody side) x y (207 * (10 * P * n) + 12) :=
    (hz.seq (hu.seq hy)).mono (by omega)
  refine ⟨y, he, hum, huf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [y, src, dst, prefixes, stage]
  · simp [y, dst, prefixes, stage]
  · simpa [y, src, dst, prefixes, stage, stride] using un
  · simp [y, prefixes, stage, Nat.mul_comm]
  · simp [y]
  · intro a ha hl
    exact he.regs_eq (stage_preserves side a ha hl)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding
