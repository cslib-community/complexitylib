/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Controller
import Mathlib.Tactic.Ring

/-!
# Complete charged execution of the shared encoder

## Main results

* `Encoding.exec_coordinates`: all shared coordinate transforms, with charged loop control.
* `Encoding.exec`: complete initialization, transforms and fixed-output copy with an explicit
  `240 * (L+1) * 10^L` native instruction bound.

The code is directly over the standard unsigned WordRAM. Its signed add/subtract blocks use
two extra target bits and respectively at most fifteen/seventeen actual instructions. There
is no whole-program signed compiler in this construction and no uncharged simulation premise.

## References

The encodings are from [AlmanWilliams2026, Section 2.4.1]; see `Encoding` for provenance.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open CoordinateTransform

/-- Explicit total instruction bound, including header preparation, all index arithmetic,
stage and cell loop control, and the final copy. A final halt costs one additional instruction. -/
def timeBound (L : ℕ) : ℕ := 240 * (L + 1) * 10 ^ L

/-- Every coordinate stage is executed natively. Charging every stage at the maximum buffer
size gives `L * (207 * 10^L + 14) + 2` instructions, including both outer loop controls. -/
theorem exec_coordinates {w L : ℕ} (hw : 0 < w) (side : Bool) (arr : ℕ → ℤ)
    (initial : ℕ → ℕ) (x : Data 32) (hx : Progress side L 0 arr initial x)
    (A : ℤ) (hA : 0 ≤ A) (ha : ∀ i < 7 ^ L, |arr i| ≤ A)
    (hmag : (7 ^ L : ℕ) * A < (2 : ℤ) ^ (w - 1))
    (haddr : Fits (w + 2) (addressBound L)) :
    ∃ y, ExecWithin (w + 2) (.loop (.lt stage depth) (stageBody side)) x y
        (L * (207 * 10 ^ L + 14) + 2) ∧ Progress side L L arr initial y := by
  let I (y : Data 32) : Prop := ∃ j, j ≤ L ∧ Progress side L j arr initial y
  have hbody (y : Data 32) (hy : I y) (hc : (Cond.lt stage depth).Holds y) :
      ∃ z, ExecWithin (w + 2) (stageBody side) y z (207 * 10 ^ L + 12) ∧ I z ∧
        L - z.regs stage < L - y.regs stage := by
    obtain ⟨j, hj, hprogress⟩ := hy
    have hjL : j < L := by simpa only [Cond.holds_lt, hprogress.stage, hprogress.fixed.1] using hc
    obtain ⟨z, he, hz⟩ := progress_step hw hjL side arr initial y hprogress A hA ha hmag haddr
    exact ⟨z, he, ⟨j + 1, by omega, hz⟩, by rw [hprogress.stage, hz.stage]; omega⟩
  obtain ⟨y, he, ⟨j, hj, hy⟩, hc⟩ := ExecWithin.loop_invariant I
    (fun y => L - y.regs stage) hbody ⟨0, Nat.zero_le _, hx⟩
  have hjL : j = L := by
    simp only [Cond.holds_lt, hy.stage, hy.fixed.1] at hc
    omega
  subst j
  refine ⟨y, ?_, hy⟩
  simpa only [hx.stage, Nat.sub_zero, Nat.add_assoc] using he

/-- The encoder runs from a concrete flat memory layout and preserves every cell outside
its output/scratch region. Only the original input magnitude and explicit address bounds are
assumed; every intermediate signed arithmetic fit is derived in the coordinate-stage proof. -/
theorem exec {w L : ℕ} (hw : 0 < w) (side : Bool) (arr : ℕ → ℤ) (x : Data 32)
    (hheader : x.mem 1 = L) (hinput : ∀ i < 7 ^ L, x.mem (2 + i) = encode (arr i))
    (A : ℤ) (hA : 0 ≤ A) (ha : ∀ i < 7 ^ L, |arr i| ≤ A)
    (hmag : (7 ^ L : ℕ) * A < (2 : ℤ) ^ (w - 1))
    (haddr : Fits (w + 2) (addressBound L)) :
    ∃ y, ExecWithin (w + 2) (program side) x y (timeBound L) ∧
      (∀ p < 10 ^ L, y.mem (outputBase L + p) =
        encode (value (table (coefficients side)) L 0 arr p 0)) ∧
      (∀ a, ¬(outputBase L ≤ a ∧ a < scratchBase L + 10 ^ L) → y.mem a = x.mem a) ∧
      y.regs output = outputBase L ∧ y.regs capacity = 10 ^ L := by
  obtain ⟨z, hz, hsetup⟩ := exec_setup L x hheader haddr
  have hzero := progress_zero side L arr x z hsetup hinput
  obtain ⟨u, hu, hp⟩ := exec_coordinates hw side arr x.mem z hzero A hA ha hmag haddr
  have hsource := hp.src
  have hout := hp.fixed.2.2.1
  have hcap := hp.fixed.2.1
  have hcap1 : 1 ≤ 10 ^ L := Nat.one_le_pow L 10 (by decide)
  have hsfit : Fits (w + 2) (u.regs src + u.regs capacity) := by
    rw [hsource, hcap]
    apply haddr.of_le
    have hb := (buffer_address_le L L).1
    unfold addressBound
    omega
  have hdfit : Fits (w + 2) (u.regs output + u.regs capacity) := by
    rw [hout, hcap]
    apply haddr.of_le
    have h7 := Nat.pow_le_pow_left (by decide : 7 ≤ 10) L
    unfold addressBound outputBase
    omega
  have hdisj : u.regs src + u.regs capacity ≤ u.regs output ∨
      u.regs output + u.regs capacity ≤ u.regs src ∨ u.regs src = u.regs output := by
    rw [hsource, hout, hcap]
    by_cases hL : L = 0
    · rcases hL with rfl
      left
      decide
    · rcases source_cases (L := L) (j := L) (by omega) with h | h
      · exact Or.inr (Or.inr h)
      · right
        left
        rw [h]
        rfl
  obtain ⟨y, hy, hymem, hyr⟩ := exec_copyOut u (haddr.of_le (by unfold addressBound; omega))
    hsfit hdfit hdisj
  have he : ExecWithin (w + 2) (program side) x y (timeBound L) := by
    have hwhole := hz.seq (hu.seq hy)
    apply hwhole.mono
    rw [hcap]
    unfold timeBound
    have hLcap : L ≤ L * 10 ^ L := by nlinarith only [Nat.mul_le_mul_left L hcap1]
    nlinarith only [hcap1, hLcap]
  refine ⟨y, he, ?_, ?_, ?_, ?_⟩
  · intro p hpp
    rw [hymem, hsource, hout, hcap, ArrayCopy.copyPrefix_read hpp]
    have h := hp.values p hpp 0 (by simp)
    simpa only [Nat.sub_self, pow_zero, Nat.mul_one, Nat.add_zero] using h
  · intro a haout
    rw [hymem, hsource, hout, hcap, ArrayCopy.copyPrefix_outside ?_]
    · exact hp.frame a haout
    · unfold scratchBase at haout
      omega
  · exact (hyr output (by decide) (by decide) (by decide) (by decide)).trans hout
  · exact (hyr capacity (by decide) (by decide) (by decide) (by decide)).trans hcap

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding
