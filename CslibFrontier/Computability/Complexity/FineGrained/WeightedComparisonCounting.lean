/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.WeightedComparisonConstruction
public import CslibFrontier.Computability.Complexity.FineGrained.TwoBoundaryFrontend
import all CslibFrontier.Computability.PolyTime.CNF.SparseCNFLeafCounter

/-!
# Actual sharp counting with correlated polynomial-weight tests

Compose the proved original-input generator, unrestricted-density counter, actual query
reconstruction and output. The parameter is original variables plus original predicates;
functional gates are absorbed by a fixed-linear rescaling, retaining one loglog factor.
Source: [ChenJiangZhu2027], Corollary A.2, PDF p.29.

## Main results

* `exists_count_sharp_certificate`: original weighted counts, complete native time and workspace.
-/

public section

namespace Cslib.Circuits.Boolean.WeightedSum.WithBase

open Turing.MultiTapeTM Cslib.GenericRAM Cslib.Complexity Logic.PL

open Classical in
/-- One actual augmented-instance counter, original correlated counts, sharp native time and
polynomial peak workspace on all raw frames; no encoder/counter/runtime advice is supplied. -/
theorem exists_count_sharp_certificate {r : ℕ} (op : Fin r → Comparison) (b d c : ℕ) :
    ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (B : CNF (Fin n)) (P : List (DNF (Fin n)))
        (weights : Fin r → Fin n → ℕ) (positive : Fin r → Fin n → Bool) (target : Fin r → ℤ)
        (_hw : ∀ j i, weights j i ≤ n ^ c)
        (_hb : ∀ clause ∈ B, clause.length ≤ b) (_hp : ∀ p ∈ P, ∀ t ∈ p, t.length ≤ d),
        count (ofData B P weights positive target) =
          Fintype.card {x : Fin n → Bool //
            (∀ j, (op j).Holds (value (weights j) (positive j) x) (target j)) ∧
              B.eval x = true ∧ ∀ p ∈ P, DNF.eval x p = true} ∧
        cs.time (ofData B P weights positive target) ≤
          C * ((encInput (ofData B P weights positive target)).length + 1) ^ e *
            2 ^ (A * Nat.logLogSqrtLogScale (n + P.length)) := by
  obtain ⟨counter, cp, pC, f, A, hs, h⟩ :=
    TwoBoundary.BinaryFrontend.exists_count_sharp_certificate (max b 3) d
  let cc := NativeCertificate.ofPolyTime (build_polytime op c)
  have hcc := NativeCertificate.ofPolyTime_isPolynomial (build_polytime op c)
  let cs := cp.comp cc
  have hcpS : PolyBounded
      (fun x => (TwoBoundary.BinaryFrontend.encInput x).length) cp.space :=
    PolyBounded.of_forall_le pC f hs
  have hcsS := SparseCNFLeafCounter.polyBounded_comp_space cp cc hcpS hcc.2
  let W (x : Input) := cc.time x +
    pC * ((TwoBoundary.BinaryFrontend.encInput (build op c x)).length + 1) ^ f + cs.space x
  have hW : PolyBounded (fun x => (encInput x).length) W :=
    (hcc.1.add ((PolyBounded.const pC).mul
      (((build_polytime op c).polyBounded_length.add (.const 1)).pow f))).add hcsS
  let R := r * comparisonBudget c
  let cScale := 2 * R + 5
  let H := max 4 cScale
  let T := cScale * (H + 1) + R
  let K := 2 ^ (A * (5 * Nat.logLogSqrtLogScale T))
  obtain ⟨C, e, hCe⟩ := ((PolyBounded.const K).mul hW).exists_le
  have hK : 0 < K := Nat.two_pow_pos _
  refine ⟨counter ∘ build op c, cs, C, e, (20 * cScale) * A, fun x => ?_, ?_⟩
  · exact (show cs.space x ≤ W x from Nat.le_add_left _ _).trans
      ((Nat.le_mul_of_pos_left _ hK).trans (hCe x))
  intro n B P weights positive target hw hb hp
  let x := ofData B P weights positive target
  obtain ⟨BF, PF, hbuild, hbf, hpf, hplen, hcount⟩ :=
    representation op c B P weights positive target hw hb hp
  obtain ⟨hc, ht⟩ := h BF PF hbf hpf
  let a := (joint op c weights positive target).size
  let z := n + P.length
  have ha : a ≤ R * (n + 1) := (joint_bounds op c weights positive target).1
  have htime : cp.time (build op c x) ≤ pC *
      ((Logic.PL.TwoBoundary.BinaryFrontend.encInput (build op c x)).length + 1) ^ f *
        2 ^ (A * Nat.logLogSqrtLogScale (z + a)) := by
    rw [← hbuild, hplen] at ht
    simpa only [x, z, a, Nat.add_right_comm] using ht
  have hscale : Nat.logLogSqrtLogScale (z + a) ≤
      20 * cScale * Nat.logLogSqrtLogScale z + 5 * Nat.logLogSqrtLogScale T := by
    by_cases hn : H ≤ z
    · have hn1 : 1 ≤ z := (by have := le_max_left 4 cScale; omega : 1 ≤ H).trans hn
      have hnz : n ≤ z := Nat.le_add_right _ _
      have hdim : z + a ≤ cScale * z := by
        dsimp only [cScale]; nlinarith
      have hcn : 4 ≤ cScale * z := by
        have hc : 4 ≤ cScale := by dsimp only [cScale]; omega
        nlinarith
      have hm := Nat.logLogSqrtLogScale_le_of_le hdim hcn
      have hl := Nat.logLogSqrtLogScale_mul_le cScale hn
      nlinarith
    · have hnH : z ≤ H := by omega
      have hnz : n ≤ z := Nat.le_add_right _ _
      have hx : z + a ≤ cScale * z + R := by
        dsimp only [cScale]; nlinarith
      have hy := Nat.mul_le_mul_left cScale hnH
      have hdim : z + a ≤ T := by dsimp only [T]; nlinarith
      have hT : 4 ≤ T := by
        have hc : 4 ≤ cScale := by dsimp only [cScale]; omega
        have hm := Nat.le_mul_of_pos_right cScale (Nat.succ_pos H)
        change cScale ≤ cScale * (H + 1) at hm
        dsimp only [T]
        omega
      have hm := Nat.logLogSqrtLogScale_le_of_le hdim hT
      omega
  let E := 2 ^ (((20 * cScale) * A) * Nat.logLogSqrtLogScale z)
  have hE : 0 < E := Nat.two_pow_pos _
  have hpow : 2 ^ (A * Nat.logLogSqrtLogScale (z + a)) ≤ K * E := by
    calc _ ≤ 2 ^ (A * (20 * cScale * Nat.logLogSqrtLogScale z +
        5 * Nat.logLogSqrtLogScale T)) :=
          Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left A hscale)
      _ = _ := by dsimp only [K, E]; rw [Nat.mul_add, pow_add, mul_comm]; congr 1; ring
  constructor
  · change counter (build op c x) = _
    rw [hbuild, hc, hcount]
  · change cc.time x +
      cp.time (build op c x) ≤ _
    calc
      _ ≤ (cc.time x +
          pC * ((TwoBoundary.BinaryFrontend.encInput
            (build op c x)).length + 1) ^ f) *
            (K * E) := by
        rw [Nat.add_mul]
        exact Nat.add_le_add
          (Nat.le_mul_of_pos_right _ (Nat.mul_pos hK hE))
          (htime.trans (Nat.mul_le_mul_left _ hpow))
      _ ≤ K * W x * E := by
        have hm := Nat.mul_le_mul_right (K * E)
          (show cc.time x + pC *
            ((TwoBoundary.BinaryFrontend.encInput
              (build op c x)).length + 1) ^ f ≤
              W x from Nat.le_add_right _ _)
        nlinarith
      _ ≤ _ := Nat.mul_le_mul_right E (hCe _)

end Cslib.Circuits.Boolean.WeightedSum.WithBase
