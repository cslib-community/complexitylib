/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CNF.SigmaRhoInput
public import Complexity.Computability.Complexity.FineGrained.TwoBoundaryFrontend
import all Complexity.Computability.PolyTime.CNF.SparseCNFLeafCounter

/-!
# Actual sharp counting for general fixed finite/cofinite degree rules

The actual original-input constructor is composed with the proved unrestricted-density counter.
Every threshold and optional gate value is derived uniquely. Only the fixed cutoff/rule tables
and size-test choice parameterize the algorithm; the graph and binary bounds vary at runtime.
Source: [ChenJiangZhu2027], Corollary 7.2 / Appendix C.2 (PDF pp.24–25,31–32).
-/

public section

namespace Cslib.Logic.PL.SigmaRho.BinaryFrontend

open Turing.MultiTapeTM Cslib.GenericRAM Cslib.Complexity

open Classical in
/-- Complete actual general-rule counter, including binary bounds, writing and original counts. -/
theorem exists_count_sharp_certificate (D : ℕ) (hD : 1 ≤ D)
    (σ ρ : SimpleGraph.DegreeRule D) (active : Bool) :
    ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℕ),
        count (ofGraph G lo hi) = Fintype.card {S : Set (Fin n) //
          G.IsSigmaRhoSet σ.counts ρ.counts S ∧ InBounds active lo hi (Nat.card S)} ∧
        cs.time (ofGraph G lo hi) ≤ C * ((encInput (ofGraph G lo hi)).length + 1) ^ e *
          2 ^ (A * Nat.logLogSqrtLogScale n) := by
  obtain ⟨counter, cp, pC, f, A, hs, h⟩ :=
    TwoBoundary.BinaryFrontend.exists_count_sharp_certificate (max (D + 1) 3) D
  let cc := NativeCertificate.ofPolyTime (build_polytime D σ ρ active)
  have hcc := NativeCertificate.ofPolyTime_isPolynomial (build_polytime D σ ρ active)
  let cs := cp.comp cc
  have hcpS : PolyBounded
      (fun x => (TwoBoundary.BinaryFrontend.encInput x).length) cp.space :=
    PolyBounded.of_forall_le pC f hs
  have hcsS := SparseCNFLeafCounter.polyBounded_comp_space cp cc hcpS hcc.2
  let W (x : Input) := cc.time x +
    pC * ((TwoBoundary.BinaryFrontend.encInput (build D σ ρ active x)).length + 1) ^ f + cs.space x
  have hW : PolyBounded (fun x => (encInput x).length) W :=
    (hcc.1.add ((PolyBounded.const pC).mul
      (((build_polytime D σ ρ active).polyBounded_length.add (.const 1)).pow f))).add hcsS
  let cScale := 2 * D + 1905
  let H := max 4 cScale
  let T := cScale * (H + 1) + 952
  let K := 2 ^ (A * (5 * Nat.logLogSqrtLogScale T))
  obtain ⟨C, e, hCe⟩ := ((PolyBounded.const K).mul hW).exists_le
  have hK : 0 < K := Nat.two_pow_pos _
  refine ⟨counter ∘ build D σ ρ active, cs, C, e, (20 * cScale) * A, fun x => ?_, ?_⟩
  · exact (show cs.space x ≤ W x from Nat.le_add_left _ _).trans
      ((Nat.le_mul_of_pos_left _ hK).trans (hCe x))
  intro n G _ lo hi
  obtain ⟨B, P, hbuild, hb, hp, hplen, hcount⟩ := representation G D hD σ ρ active lo hi
  obtain ⟨hc, ht⟩ := h B P hb hp
  let a := auxiliary active (ofGraph G lo hi)
  have ha : a ≤ 952 * (n + 1) := auxiliary_bound G active lo hi
  have htime : cp.time (build D σ ρ active (ofGraph G lo hi)) ≤
      pC * ((TwoBoundary.BinaryFrontend.encInput
        (build D σ ρ active (ofGraph G lo hi))).length + 1) ^ f *
        2 ^ (A * Nat.logLogSqrtLogScale ((2 * D + 1) * n + a)) := by
    rw [← hbuild, hplen] at ht
    have hh : (n + auxiliary active (ofGraph G lo hi) + D * n) + D * n =
        (2 * D + 1) * n + a := by dsimp only [a]; ring
    simpa only [hh] using ht
  have hscale : Nat.logLogSqrtLogScale ((2 * D + 1) * n + a) ≤
      20 * cScale * Nat.logLogSqrtLogScale n + 5 * Nat.logLogSqrtLogScale T := by
    by_cases hn : H ≤ n
    · have hn1 : 1 ≤ n := (by have := le_max_left 4 cScale; omega : 1 ≤ H).trans hn
      have hdim : (2 * D + 1) * n + a ≤ cScale * n := by
        dsimp only [cScale]; nlinarith
      have hcn : 4 ≤ cScale * n := by
        have hc : 4 ≤ cScale := by dsimp only [cScale]; omega
        nlinarith
      have hm := Nat.logLogSqrtLogScale_le_of_le hdim hcn
      have hl := Nat.logLogSqrtLogScale_mul_le cScale hn
      nlinarith
    · have hnH : n ≤ H := by omega
      have hx : (2 * D + 1) * n + a ≤ cScale * n + 952 := by
        dsimp only [cScale]; nlinarith
      have hy := Nat.mul_le_mul_left cScale hnH
      have hdim : (2 * D + 1) * n + a ≤ T := by dsimp only [T]; nlinarith
      have hm := Nat.logLogSqrtLogScale_le_of_le hdim (by dsimp only [T]; omega : 4 ≤ T)
      omega
  let E := 2 ^ (((20 * cScale) * A) * Nat.logLogSqrtLogScale n)
  have hE : 0 < E := Nat.two_pow_pos _
  have hpow : 2 ^ (A * Nat.logLogSqrtLogScale ((2 * D + 1) * n + a)) ≤ K * E := by
    calc _ ≤ 2 ^ (A * (20 * cScale * Nat.logLogSqrtLogScale n +
        5 * Nat.logLogSqrtLogScale T)) :=
          Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left A hscale)
      _ = _ := by dsimp only [K, E]; rw [Nat.mul_add, pow_add, mul_comm]; congr 1; ring
  constructor
  · change counter (build D σ ρ active (ofGraph G lo hi)) = _
    rw [hbuild, hc, hcount]
  · change cc.time (ofGraph G lo hi) + cp.time (build D σ ρ active (ofGraph G lo hi)) ≤ _
    calc
      _ ≤ (cc.time (ofGraph G lo hi) +
          pC * ((TwoBoundary.BinaryFrontend.encInput
            (build D σ ρ active (ofGraph G lo hi))).length + 1) ^ f) *
            (K * E) := by
        rw [Nat.add_mul]
        exact Nat.add_le_add
          (Nat.le_mul_of_pos_right _ (Nat.mul_pos hK hE))
          (htime.trans (Nat.mul_le_mul_left _ hpow))
      _ ≤ K * W (ofGraph G lo hi) * E := by
        have hm := Nat.mul_le_mul_right (K * E)
          (show cc.time (ofGraph G lo hi) + pC *
            ((TwoBoundary.BinaryFrontend.encInput
              (build D σ ρ active (ofGraph G lo hi))).length + 1) ^ f ≤
              W (ofGraph G lo hi) from Nat.le_add_right _ _)
        nlinarith
      _ ≤ _ := Nat.mul_le_mul_right E (hCe _)

open Classical in
/-- The actual counter has the real single-loglog source exponent; rounded bounds cover all small
and empty instances, and workspace is polynomial on all raw frames. -/
theorem exists_count_realEta_certificate (D : ℕ) (hD : 1 ≤ D)
    (σ ρ : SimpleGraph.DegreeRule D) (active : Bool) :
    ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℕ),
        count (ofGraph G lo hi) = Fintype.card {S : Set (Fin n) //
          G.IsSigmaRhoSet σ.counts ρ.counts S ∧ InBounds active lo hi (Nat.card S)} ∧
        (16 ≤ n → (cs.time (ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
          ((encInput (ofGraph G lo hi)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨count, cs, C, e, A, hs, h⟩ := exists_count_sharp_certificate D hD σ ρ active
  refine ⟨count, cs, C, e, 6 * A, hs, ?_⟩
  intro n G _ lo hi
  refine ⟨(h G lo hi).1, fun hn => ?_⟩
  have ht : (cs.time (ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
      ((encInput (ofGraph G lo hi)).length + 1 : ℕ) ^ e *
        (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast (h G lo hi).2
  exact ht.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A hn) (by positivity))

open Classical in
/-- Every fixed finite/cofinite source rule pair has an actual sharp counter. Rule compilation is
fixed problem data, not instance-dependent advice or an assumed reduction/runtime contract. -/
theorem exists_count_finiteCofinite_certificate (σ ρ : Set ℕ)
    (hσ : σ.Finite ∨ σᶜ.Finite) (hρ : ρ.Finite ∨ ρᶜ.Finite) (active : Bool) :
    ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℕ),
        count (ofGraph G lo hi) = Fintype.card {S : Set (Fin n) //
          G.IsSigmaRhoSet σ ρ S ∧ InBounds active lo hi (Nat.card S)} ∧
        (16 ≤ n → (cs.time (ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
          ((encInput (ofGraph G lo hi)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨D, hD, s, r, hs, hr⟩ := SimpleGraph.exists_degreeRules σ ρ hσ hρ
  obtain ⟨count, cs, C, e, A, hspace, h⟩ := exists_count_realEta_certificate D hD s r active
  refine ⟨count, cs, C, e, A, hspace, ?_⟩
  intro n G _ lo hi
  simpa only [hs, hr] using h G lo hi

end Cslib.Logic.PL.SigmaRho.BinaryFrontend
