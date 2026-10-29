/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandEncode

/-!
# Every shared band, computed once

## Main results

* `BandPreparation.exec_encodeBands`: the complete native loop prepares, encodes and collects
  all bands of one matrix side. Catalogue cells retain the existing flat leaf numbering.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

-- Static preservation checks reduce the finite persistent-register set.
set_option maxRecDepth 4096

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Catalogue blocks are ordered by band index, without duplicating them per tile. -/
theorem catalogue_address_lt {L m N β γ p : ℕ} (side : Bool) (hβγ : β < γ)
    (hp : p < 10 ^ L) :
    catalogueAddress L m N side β p < catalogueAddress L m N side γ 0 := by
  have ht : 0 < 10 ^ L := Nat.pow_pos (by decide)
  unfold catalogueAddress
  nlinarith only [hβγ, hp, ht]

/-- The full one-side catalogue interval ends at the block immediately after its last band. -/
theorem catalogue_block_inside {L m N β : ℕ} (side : Bool) (hβ : β < numBands L m N) :
    catalogueAddress L m N side 0 0 ≤ catalogueAddress L m N side β 0 ∧
    catalogueAddress L m N side β 0 + 10 ^ L ≤
      catalogueAddress L m N side (numBands L m N) 0 := by
  have ht : 0 < 10 ^ L := Nat.pow_pos (by decide)
  unfold catalogueAddress
  constructor <;> nlinarith only [hβ, ht, Nat.zero_le β]

/-- All ordinary band counters fit from the original explicit allocation budget. -/
theorem bands_fits {w L m N : ℕ} (hfit : Fits w (wordBudget L m N)) :
    Fits w (numBands L m N) := by
  apply hfit.of_le
  unfold wordBudget
  have ht : 0 < 10 ^ L := Nat.pow_pos (by decide)
  nlinarith only [ht, Nat.zero_le L, Nat.zero_le N, Nat.zero_le (N * D m),
    Nat.zero_le (2 ^ L), Nat.zero_le (numBands L m N)]

/-- The actual native loop calls the complete encoder once for every shared band, charges
all loop control and counter increments, and preserves any outside caller memory. -/
theorem exec_encodeBands {w L m N : ℕ} (hw : 0 < w) (side : Bool) (x : Data 96)
    (hx : BandParameters L m N x)
    (htable : ∀ t < 2 ^ L, x.mem (inverseBase L m N + t) = MaskTable.lookup L m t)
    (matrix : ℕ → ℕ → ℤ)
    (hmat : ∀ r < N, ∀ k < D m,
      x.mem (matrixAddress L m N side r k) = encode (matrix r k))
    (A : ℤ) (hA : 0 ≤ A) (ha : ∀ r < N, ∀ k < D m, |matrix r k| ≤ A)
    (hmag : (7 ^ L : ℕ) * A < (2 : ℤ) ^ (w - 1))
    (hfit : Fits (w + 2) (wordBudget L m N)) :
    ∃ y, ExecWithin (w + 2) (encodeBands side) x y
        (numBands L m N * (bandTime L + 3) + 3) ∧
      BandParameters L m N y ∧
      (∀ β < numBands L m N, ∀ p < 10 ^ L,
        y.mem (catalogueAddress L m N side β p) =
          encode (catalogueValue L m N side matrix β p)) ∧
      (∀ b, ¬(1 ≤ b ∧ b < Encoding.scratchBase L + 10 ^ L) →
        ¬(catalogueAddress L m N side 0 0 ≤ b ∧
          b < catalogueAddress L m N side (numBands L m N) 0) →
        y.mem b = x.mem b) := by
  let start := x.set band 0
  have hs : ExecWithin (B := .standard) (w + 2) (ram[ band ← #0 ]) x start 1 :=
    ExecWithin.const (fits_zero _)
  have hp : BandParameters L m N start := parameters_reframe hx (by
    intro i hi
    have hne : i ≠ band := by
      have hp : ∀ i ∈ parameterRegisters, i ≠ band := by decide
      exact hp i hi
    simp only [start, Data.set_regs, Function.update_of_ne hne])
  let I (y : Data 96) : Prop := BandParameters L m N y ∧
    y.regs band ≤ numBands L m N ∧
    (∀ β < y.regs band, ∀ p < 10 ^ L,
      y.mem (catalogueAddress L m N side β p) =
        encode (catalogueValue L m N side matrix β p)) ∧
    (∀ b, ¬(1 ≤ b ∧ b < Encoding.scratchBase L + 10 ^ L) →
      ¬(catalogueAddress L m N side 0 0 ≤ b ∧
        b < catalogueAddress L m N side (numBands L m N) 0) →
      y.mem b = x.mem b)
  have hstart : I start := by
    refine ⟨hp, ?_, ?_, ?_⟩
    · simp [start]
    · simp [start]
    · intro b _ _; rfl
  have hbody (y : Data 96) (hy : I y) (hc : (Cond.lt band bands).Holds y) :
      ∃ z, ExecWithin (w + 2) (bandBody side) y z (bandTime L + 1) ∧ I z ∧
        numBands L m N - z.regs band < numBands L m N - y.regs band := by
    let β := y.regs band
    have hβ : β < numBands L m N := by simpa only [Cond.holds_lt, hy.1.bands] using hc
    have hlow := workspace_le_snapshot L m N
    have hcat := catalogue_le_address L m N 0 side
    have htable' (t : ℕ) (ht : t < 2 ^ L) :
        y.mem (inverseBase L m N + t) = MaskTable.lookup L m t := by
      rw [hy.2.2.2 _ (by unfold inverseBase; omega) (by
        unfold catalogueBase tableBase at hcat
        omega)]
      exact htable t ht
    have hmat' (r : ℕ) (hr : r < N) (k : ℕ) (hk : k < D m) :
        y.mem (matrixAddress L m N side r k) = encode (matrix r k) := by
      have hbound := matrixAddress_lt_inverse (L := L) side hr hk
      rw [hy.2.2.2 _ (by unfold matrixAddress; omega) (by
        unfold catalogueBase tableBase at hcat
        have := Nat.zero_le (2 ^ L)
        omega)]
      exact hmat r hr k hk
    obtain ⟨t, he, htp, htb, hvalues, hframe⟩ := exec_band hw side β y hy.1 hβ rfl
      htable' matrix hmat' A hA ha hmag hfit
    let z := t.set band (β + 1)
    have hz : ExecWithin (B := .standard) (w + 2) (ram[ band ← band + one ]) t z 1 := by
      ram_eval [z, htb, htp.fixed.one, (bands_fits hfit).of_le (Nat.succ_le_of_lt hβ),
        band, one, Fin.mk.injEq]
    have hzb : z.regs band = β + 1 := by simp [z]
    refine ⟨z, he.seq hz, ?_, ?_⟩
    · refine ⟨parameters_reframe htp ?_, ?_, ?_, ?_⟩
      · intro i hi
        have hp : ∀ i ∈ parameterRegisters, i ≠ band := by decide
        simp only [z, Data.set_regs, Function.update_of_ne (hp i hi)]
      · rw [hzb]; omega
      · intro γ hγ p hp
        rw [hzb] at hγ
        change t.mem _ = _
        by_cases hγβ : γ = β
        · subst γ; exact hvalues p hp
        · have hγlt : γ < β := by omega
          have hprior := catalogue_address_lt (m := m) (N := N) side hγlt hp
          rw [hframe _ ?_ (by omega)]
          · exact hy.2.2.1 γ hγlt p hp
          · have haddr := catalogue_le_address L m N γ side
            unfold catalogueAddress at haddr
            have hsep : Encoding.scratchBase L + 10 ^ L ≤ catalogueBase L m N := by
              unfold catalogueBase tableBase inverseBase
              have := Nat.zero_le (2 ^ L)
              omega
            unfold catalogueAddress
            omega
      · intro b hb hc
        change t.mem b = x.mem b
        have hinside := catalogue_block_inside side hβ
        rw [hframe b hb (by omega)]
        exact hy.2.2.2 b hb hc
    · rw [hzb]; change numBands L m N - (β + 1) < numBands L m N - β; omega
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I
    (fun y => numBands L m N - y.regs band) hbody hstart
  have hb : y.regs band = numBands L m N := by
    simp only [Cond.holds_lt, hy.1.bands] at hc
    have := hy.2.1
    omega
  refine ⟨y, ?_, hy.1, ?_, hy.2.2.2⟩
  · apply (hs.seq he).mono
    have hz : start.regs band = 0 := by simp [start]
    simp only [hz, Nat.sub_zero, Nat.add_assoc, Nat.reduceAdd]
    omega
  · simpa only [hb] using hy.2.2.1

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
