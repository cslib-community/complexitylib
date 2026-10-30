/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime.Indexing
public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.SourceBounds

/-!
# Original-input bounds for the catalogue controller

The controller's counters fit from original scalar dimensions. A coarse polynomial counter
bound is used only for physical admission; charged scan accounting uses the single global
false-positive count instead. No intermediate counter fit is supplied by the caller.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle

/-- A polynomial envelope for ordinal and accumulated scan-counter arithmetic. -/
@[expose] def counterEnvelope (n p : ℕ) : ℕ :=
  (p * n * n * n + 1) * (n * n + 1) + n + 64

/-- Original-input threshold for the unchanged record code and its new controller. -/
@[expose] def admissionWidth (n D g p A : ℕ) : ℕ :=
  max (RecordWitness.admissionWidth n D g p A) (Nat.clog 2 (counterEnvelope n p) + 1)

/-- The original-input physical threshold is positive even before imposing source geometry. -/
theorem admissionWidth_pos (n D g p A : ℕ) : 0 < admissionWidth n D g p A := by
  unfold admissionWidth
  omega

/-- The real occupied count has a polynomial bound without inspecting a workspace. -/
theorem produced_le {n D g p : ℕ} (values : ℕ → ℤ)
    {initial a : Data 64} (h : Instances.Output n D g p values initial a)
    (hD : 16 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g) :
    a.regs Instances.produced ≤ p * n * n * n := by
  let C := fun rho => Nat.count (fun q => (values q % (p : ℤ)).toNat = rho) (n * n)
  have hK : ChunkCatalogue.before C (queryCap n D) p ≤ p * (n * n) :=
    ChunkCatalogue.before_le (one_le_queryCap (by omega) hDn)
      (fun _ _ => Nat.count_le _) (le_refl p)
  have hH : numPieces n D g ≤ n :=
    (Nat.ceilDiv_le_iff (pieceSize_pos hD hg)).mpr
      (Nat.le_mul_of_pos_right n (pieceSize_pos hD hg))
  have hc := h.2.2.2.2.1
  change a.regs Instances.produced = ChunkCatalogue.before C (queryCap n D) p *
    numPieces n D g at hc
  rw [hc]
  exact (Nat.mul_le_mul hK hH).trans_eq (by ring)

/-- All record query-occurrence counts are at most the number of original pairs. -/
theorem recordQueryCount_le (n D p : ℕ) (values : ℕ → ℤ) (idx : InstanceIndex p) :
    RecordProduct.recordQueryCount n D p values idx ≤ n * n := by
  unfold RecordProduct.recordQueryCount
  exact (min_le_right _ _).trans ((Nat.sub_le _ _).trans (Nat.count_le _))

/-- Every larger admitted physical width contains the complete accumulated-counter bound. -/
theorem counter_fits {W n D g p A : ℕ} (hW : admissionWidth n D g p A ≤ W) :
    Fits W (counterEnvelope n p) := by
  have hc : Nat.clog 2 (counterEnvelope n p) < W := by
    unfold admissionWidth at hW
    omega
  exact (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) _).trans_lt
    (Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hc)

/-- The controller threshold retains the original concrete callee admission. -/
theorem record_admitted {W n D g p A : ℕ} (hW : admissionWidth n D g p A ≤ W) :
    RecordWitness.admissionWidth n D g p A ≤ W := (le_max_left _ _).trans hW

/-- Before each actual return, both counters fit solely from original dimensions and the
coarse visited-prefix bounds. This is not the charged false-positive estimate. -/
theorem return_fits {W n D g p A M i S performed : ℕ}
    (hW : admissionWidth n D g p A ≤ W) (hM : M ≤ p * n * n * n)
    (hi : i < M) (hS : S ≤ i * (n * n + 1)) (hp : performed ≤ n * n + 1) :
    Fits W (S + performed) ∧ Fits W (i + 1) := by
  have hsum : S + performed ≤ (i + 1) * (n * n + 1) := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hnext : i + 1 ≤ p * n * n * n + 1 := by omega
  have hprod := Nat.mul_le_mul_right (n * n + 1) hnext
  have hlinear : i + 1 ≤ (p * n * n * n + 1) * (n * n + 1) :=
    hnext.trans (Nat.le_mul_of_pos_right _ (by omega))
  exact ⟨(counter_fits hW).of_le (by unfold counterEnvelope; omega),
    (counter_fits hW).of_le (by unfold counterEnvelope; omega)⟩

/-- The additional counters do not increase the existing original-input logarithmic constant.
All source-regime bounds remain explicit; this is not a bound for arbitrary scalar headers. -/
theorem admissionWidth_le_log {n D g p A κ : ℕ} (hn : 1 ≤ n)
    (hD : D ≤ n) (hg : g ≤ n) (hp : p ≤ n) (hA : A ≤ (n + 2) ^ κ) :
    admissionWidth n D g p A ≤ (257 * κ + 5909) * Nat.clog 2 (n + 2) := by
  let b := n + 2
  have hb : 2 ≤ b := by dsimp only [b]; omega
  have hb1 : 1 ≤ b := by omega
  have hnB : n ≤ b := by dsimp only [b]; omega
  have hfour : p * n * n * n ≤ b ^ 4 := by
    calc
      _ ≤ b * b * b * b := Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul (hp.trans hnB) hnB) hnB) hnB
      _ = b ^ 4 := by ring
  have htwo : n * n ≤ b ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul hnB hnB
  have h4pos : 1 ≤ b ^ 4 := Nat.one_le_pow _ _ hb1
  have h2pos : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ hb1
  have hleft : p * n * n * n + 1 ≤ b ^ 5 := by
    calc
      _ ≤ 2 * b ^ 4 := by omega
      _ ≤ b * b ^ 4 := Nat.mul_le_mul_right _ hb
      _ = b ^ 5 := by ring
  have hright : n * n + 1 ≤ b ^ 3 := by
    calc
      _ ≤ 2 * b ^ 2 := by omega
      _ ≤ b * b ^ 2 := Nat.mul_le_mul_right _ hb
      _ = b ^ 3 := by ring
  have hprod : (p * n * n * n + 1) * (n * n + 1) ≤ b ^ 8 :=
    (Nat.mul_le_mul hleft hright).trans_eq (by ring)
  have hn8 : n ≤ b ^ 8 := hnB.trans (Nat.le_self_pow (by decide) b)
  have hc : 64 ≤ b ^ 8 := (show 64 ≤ (2 : ℕ) ^ 8 by decide).trans
    (Nat.pow_le_pow_left hb 8)
  have he : counterEnvelope n p ≤ b ^ 10 := by
    calc
      _ ≤ 3 * b ^ 8 := by unfold counterEnvelope; omega
      _ ≤ b ^ 2 * b ^ 8 := Nat.mul_le_mul_right _
        ((show 3 ≤ (2 : ℕ) ^ 2 by decide).trans (Nat.pow_le_pow_left hb 2))
      _ = b ^ 10 := by ring
  have hlogBound := he.trans (Nat.pow_le_pow_left
    (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) b) 10)
  rw [← Nat.pow_mul] at hlogBound
  have hlog := Nat.clog_le_of_le_pow hlogBound
  have hpos : 1 ≤ Nat.clog 2 b := Nat.clog_pos (by decide) (by omega : 1 < b)
  have hcounter : Nat.clog 2 (counterEnvelope n p) + 1 ≤
      (257 * κ + 5909) * Nat.clog 2 b := by
    nlinarith only [hlog, hpos, Nat.zero_le (κ * Nat.clog 2 b)]
  exact max_le (RecordWitness.admissionWidth_le_log hn hD hg hp hA) hcounter

end Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime
