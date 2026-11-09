/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.BoundedDegreePartitionVolumes
public import CslibFrontier.Computability.Complexity.FineGrained.TwoBoundaryFrontend
import all CslibFrontier.Computability.PolyTime.CNF.SparseCNFLeafCounter

/-!
# Actual sharp counting for input-bounded labeled degree matrices

The actual original-matrix constructor is composed with the proved unrestricted-density counter.
Every threshold and padded gate is derived uniquely. Only the fixed class count/cutoff/matrix
parameterize the algorithm; graph and binary class bounds vary at runtime.
Source: [ChenJiangZhu2027], Theorem 7.3 / Appendix C.2 (PDF pp.25,32).
## Main results

* `exists_count_sharp_certificate`: original-input count, rounded sharp clock and global space.
* `exists_count_realEta_certificate`: the real source exponent after actual dimension rescaling.
* `exists_count_finiteCofinite_certificate`: every fixed finite/cofinite matrix with varying bounds.

-/

public section

namespace Cslib.Logic.PL.DegreePartition.Bounded.BinaryFrontend

open Turing.MultiTapeTM Cslib.GenericRAM Cslib.Complexity

open Classical in
/-- Complete actual general-rule counter, including actual writing and ordinary labeled counts. -/
theorem exists_count_sharp_certificate (q D : ℕ) (hD : 1 ≤ D)
    (M : Fin q → Fin q → SimpleGraph.DegreeRule D) :
    ∃ count : Input → ℕ,
      ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : Fin q → ℕ),
        count (ofGraph G lo hi) = Fintype.card {S : Fin q → Set (Fin n) //
          G.IsDegreePartition (fun i j => (M i j).counts) S ∧
          SimpleGraph.InClassBounds lo hi S} ∧
        cs.time (ofGraph G lo hi) ≤ C *
          ((encInput (ofGraph G lo hi)).length + 1) ^ e *
          2 ^ (A * Nat.logLogSqrtLogScale n) := by
  obtain ⟨counter, cp, pC, f, A, hs, h⟩ :=
    TwoBoundary.BinaryFrontend.exists_count_sharp_certificate (max q (max (D + 1) 3)) D
  let cc := NativeCertificate.ofPolyTime (build_polytime M)
  have hcc := NativeCertificate.ofPolyTime_isPolynomial (build_polytime M)
  let cs := cp.comp cc
  have hcpS : PolyBounded
      (fun x => (TwoBoundary.BinaryFrontend.encInput x).length) cp.space :=
    PolyBounded.of_forall_le pC f hs
  have hcsS := SparseCNFLeafCounter.polyBounded_comp_space cp cc hcpS hcc.2
  let W (x : Input) := cc.time x +
    pC * ((TwoBoundary.BinaryFrontend.encInput (build M x)).length + 1) ^ f + cs.space x
  have hW : PolyBounded (fun x => (encInput x).length) W :=
    (hcc.1.add ((PolyBounded.const pC).mul
      (((build_polytime M).polyBounded_length.add (.const 1)).pow f))).add hcsS
  let cScale := q * (2 * D + 1) + 1904 * q + 4
  let H := max 4 cScale
  let T := cScale * (H + 1) + 952 * q
  let K := 2 ^ (A * (5 * Nat.logLogSqrtLogScale T))
  obtain ⟨C, e, hCe⟩ := ((PolyBounded.const K).mul hW).exists_le
  have hK : 0 < K := Nat.two_pow_pos _
  refine ⟨counter ∘ build M, cs, C, e, (20 * cScale) * A, fun x => ?_, ?_⟩
  · exact (show cs.space x ≤ W x from Nat.le_add_left _ _).trans
      ((Nat.le_mul_of_pos_left _ hK).trans (hCe x))
  intro n G _ lo hi
  obtain ⟨B, P, hbuild, hb, hp, hplen, hcount⟩ := representation G hD M lo hi
  obtain ⟨hc, ht⟩ := h B P hb hp
  let a := q * PaddedCardinality.capacity n
  have ha : a ≤ 952 * q * (n + 1) := by dsimp only [a, PaddedCardinality.capacity]; nlinarith
  have htime : cp.time (build M (ofGraph G lo hi)) ≤
      pC * ((TwoBoundary.BinaryFrontend.encInput
        (build M (ofGraph G lo hi))).length + 1) ^ f *
        2 ^ (A * Nat.logLogSqrtLogScale (q * (2 * D + 1) * n + a)) := by
    rw [← hbuild, hplen] at ht
    have hh : q * (n + PaddedCardinality.capacity n + D * n) + q * (D * n) =
        q * (2 * D + 1) * n + a := by dsimp only [a]; ring
    simpa only [hh] using ht
  have hscale : Nat.logLogSqrtLogScale (q * (2 * D + 1) * n + a) ≤
      20 * cScale * Nat.logLogSqrtLogScale n + 5 * Nat.logLogSqrtLogScale T := by
    by_cases hn : H ≤ n
    · have hn1 : 1 ≤ n := (by have := le_max_left 4 cScale; omega : 1 ≤ H).trans hn
      have hdim : q * (2 * D + 1) * n + a ≤ cScale * n := by
        dsimp only [cScale]; nlinarith
      have hcn : 4 ≤ cScale * n := by
        have hc : 4 ≤ cScale := by dsimp only [cScale]; omega
        nlinarith
      have hm := Nat.logLogSqrtLogScale_le_of_le hdim hcn
      have hl := Nat.logLogSqrtLogScale_mul_le cScale hn
      nlinarith
    · have hnH : n ≤ H := by omega
      have hx : q * (2 * D + 1) * n + a ≤ cScale * n + 952 * q := by
        dsimp only [cScale]; nlinarith
      have hy := Nat.mul_le_mul_left cScale hnH
      have hdim : q * (2 * D + 1) * n + a ≤ T := by dsimp only [T]; nlinarith
      have hT : 4 ≤ T := by
        have hc : 4 ≤ cScale := by dsimp only [cScale]; omega
        have hm := Nat.le_mul_of_pos_right cScale (Nat.succ_pos H)
        change cScale ≤ cScale * (H + 1) at hm
        dsimp only [T]
        omega
      have hm := Nat.logLogSqrtLogScale_le_of_le hdim hT
      omega
  let E := 2 ^ (((20 * cScale) * A) * Nat.logLogSqrtLogScale n)
  have hE : 0 < E := Nat.two_pow_pos _
  have hpow : 2 ^ (A * Nat.logLogSqrtLogScale (q * (2 * D + 1) * n + a)) ≤ K * E := by
    calc _ ≤ 2 ^ (A * (20 * cScale * Nat.logLogSqrtLogScale n +
        5 * Nat.logLogSqrtLogScale T)) :=
          Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left A hscale)
      _ = _ := by dsimp only [K, E]; rw [Nat.mul_add, pow_add, mul_comm]; congr 1; ring
  constructor
  · change counter (build M (ofGraph G lo hi)) = _
    rw [hbuild, hc, hcount]
  · change cc.time (ofGraph G lo hi) +
      cp.time (build M (ofGraph G lo hi)) ≤ _
    calc
      _ ≤ (cc.time (ofGraph G lo hi) +
          pC * ((TwoBoundary.BinaryFrontend.encInput
            (build M (ofGraph G lo hi))).length + 1) ^ f) *
            (K * E) := by
        rw [Nat.add_mul]
        exact Nat.add_le_add
          (Nat.le_mul_of_pos_right _ (Nat.mul_pos hK hE))
          (htime.trans (Nat.mul_le_mul_left _ hpow))
      _ ≤ K * W (ofGraph G lo hi) * E := by
        have hm := Nat.mul_le_mul_right (K * E)
          (show cc.time (ofGraph G lo hi) + pC *
            ((TwoBoundary.BinaryFrontend.encInput
              (build M (ofGraph G lo hi))).length + 1) ^ f ≤
              W (ofGraph G lo hi) from Nat.le_add_right _ _)
        nlinarith
      _ ≤ _ := Nat.mul_le_mul_right E (hCe _)

open Classical in
/-- The actual counter has the real single-loglog source exponent; rounded bounds cover all small
and empty instances, and workspace is polynomial on all raw frames. -/
theorem exists_count_realEta_certificate (q D : ℕ) (hD : 1 ≤ D)
    (M : Fin q → Fin q → SimpleGraph.DegreeRule D) :
    ∃ count : Input → ℕ,
      ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : Fin q → ℕ),
        count (ofGraph G lo hi) = Fintype.card {S : Fin q → Set (Fin n) //
          G.IsDegreePartition (fun i j => (M i j).counts) S ∧
          SimpleGraph.InClassBounds lo hi S} ∧
        (16 ≤ n → (cs.time (ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
          ((encInput
            (ofGraph G lo hi)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨count, cs, C, e, A, hs, h⟩ := exists_count_sharp_certificate q D hD M
  refine ⟨count, cs, C, e, 6 * A, hs, ?_⟩
  intro n G _ lo hi
  refine ⟨(h G lo hi).1, fun hn => ?_⟩
  have ht : (cs.time (ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
      ((encInput
            (ofGraph G lo hi)).length + 1 : ℕ) ^ e *
        (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast (h G lo hi).2
  exact ht.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A hn) (by positivity))


open Classical in
/-- Every fixed finite/cofinite source matrix admits the actual input-bounded sharp counter. -/
theorem exists_count_finiteCofinite_certificate {q : ℕ} (M : Fin q → Fin q → Set ℕ)
    (hM : ∀ i j, (M i j).Finite ∨ (M i j)ᶜ.Finite) :
    ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : Fin q → ℕ),
        count (ofGraph G lo hi) = Fintype.card {S : Fin q → Set (Fin n) //
          G.IsDegreePartition M S ∧ SimpleGraph.InClassBounds lo hi S} ∧
        (16 ≤ n → (cs.time (ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
          ((encInput (ofGraph G lo hi)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨D, hD, R, hR⟩ := SimpleGraph.exists_degreeMatrixRules M hM
  obtain ⟨count, cs, C, e, A, hs, h⟩ := exists_count_realEta_certificate q D hD R
  refine ⟨count, cs, C, e, A, hs, ?_⟩
  intro n G _ lo hi
  simpa only [hR] using h G lo hi

end Cslib.Logic.PL.DegreePartition.Bounded.BinaryFrontend
