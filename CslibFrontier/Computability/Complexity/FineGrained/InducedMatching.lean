/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.InducedMatching
public import CslibFrontier.Computability.Complexity.FineGrained.TwoBoundaryFrontend
import all CslibFrontier.Computability.PolyTime.CNF.SparseCNFLeafCounter

/-!
# Sharp total induced matching counting without size-test gates

Compose the actual no-size-test constructor with the approved unrestricted-density native counter.
This is the total-count clause of [ChenJiangZhu2027], Corollary 7.5 / Appendix D.1 (PDF pp. 26, 34).
Every matching is a conventional Mathlib subgraph, counted once, without isolated marks.

## Main results

* `exists_count_sharp_certificate`: exact total count, sharp native time and global polynomial
  space.
* `exists_count_realEta_certificate`: the real single-loglog source bound on that actual algorithm.
-/

public section

namespace Cslib.Logic.PL.InducedMatching

open Turing.MultiTapeTM Cslib.Complexity Cslib.GenericRAM IndependentDomination
open DominatingInducedMatching

open Classical in
/-- One actual adjacency-matrix counter counts actual induced matchings exactly
with global polynomial space and sharp rounded time in the original vertex count. -/
theorem exists_count_sharp_certificate :
    ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        count (ofGraph G) =
          Fintype.card {M : G.Subgraph // M.IsMatching ∧ M.IsInduced} ∧
        cs.time (ofGraph G) ≤ C * ((encInput (ofGraph G)).length + 1) ^ e *
          2 ^ (A * Nat.logLogSqrtLogScale n) := by
  obtain ⟨counter, cp, D, f, A, hs, h⟩ :=
    TwoBoundary.BinaryFrontend.exists_count_sharp_certificate 3 1
  let cc := NativeCertificate.ofPolyTime build_polytime
  have hcc := NativeCertificate.ofPolyTime_isPolynomial build_polytime
  let cs := cp.comp cc
  have hcpS : PolyBounded
      (fun x => (TwoBoundary.BinaryFrontend.encInput x).length) cp.space :=
    PolyBounded.of_forall_le D f hs
  have hcsS := SparseCNFLeafCounter.polyBounded_comp_space cp cc hcpS hcc.2
  let W (x : Input) := cc.time x +
    D * ((TwoBoundary.BinaryFrontend.encInput (build x)).length + 1) ^ f + cs.space x
  have hW : PolyBounded (fun x => (encInput x).length) W :=
    (hcc.1.add ((PolyBounded.const D).mul
      ((build_polytime.polyBounded_length.add (.const 1)).pow f))).add hcsS
  let K := 2 ^ (A * (5 * Nat.logLogSqrtLogScale 32))
  obtain ⟨C, e, hCe⟩ := ((PolyBounded.const K).mul hW).exists_le
  have hK : 0 < K := Nat.two_pow_pos _
  refine ⟨counter ∘ build, cs, C, e, 8 * A, fun x => ?_, ?_⟩
  · exact (show cs.space x ≤ W x from Nat.le_add_left _ _).trans
      ((Nat.le_mul_of_pos_left _ hK).trans (hCe x))
  intro n G _
  obtain ⟨hb, hp⟩ := widths G
  obtain ⟨hc, ht⟩ := h ((finiteUpper G)) (finiteConditions G) hb hp
  have htime : cp.time (build (ofGraph G)) ≤
      D * ((TwoBoundary.BinaryFrontend.encInput (build (ofGraph G))).length + 1) ^ f *
        2 ^ (A * Nat.logLogSqrtLogScale (2 * n)) := by
    simpa only [build_ofGraph, finiteConditions_length, two_mul] using ht
  have hscale : Nat.logLogSqrtLogScale (2 * n) ≤
      8 * Nat.logLogSqrtLogScale n + 5 * Nat.logLogSqrtLogScale 32 := by
    by_cases hn : 4 ≤ n
    · have hm := Nat.logLogSqrtLogScale_mul_le 2 hn
      omega
    · have hm := Nat.logLogSqrtLogScale_le_of_le
        (by omega : 2 * n ≤ 32) (by decide : 4 ≤ 32)
      omega
  let E := 2 ^ ((8 * A) * Nat.logLogSqrtLogScale n)
  have hE : 0 < E := Nat.two_pow_pos _
  have hpow : 2 ^ (A * Nat.logLogSqrtLogScale (2 * n)) ≤ K * E := by
    calc _ ≤ 2 ^ (A * (8 * Nat.logLogSqrtLogScale n + 5 * Nat.logLogSqrtLogScale 32)) :=
          Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left A hscale)
      _ = _ := by dsimp only [K, E]; rw [Nat.mul_add, pow_add, mul_comm]; congr 1; ring
  constructor
  · change counter (build (ofGraph G)) = _
    rw [build_ofGraph, hc]
    have hsource := plan_count G
    rw [build_ofGraph, TwoBoundary.BinaryFrontend.compile_count] at hsource
    simpa only [← Nat.card_eq_fintype_card] using hsource
  · change cc.time (ofGraph G) + cp.time (build (ofGraph G)) ≤ _
    calc
      _ ≤ (cc.time (ofGraph G) +
          D * ((TwoBoundary.BinaryFrontend.encInput (build (ofGraph G))).length + 1) ^ f) *
            (K * E) := by
        rw [Nat.add_mul]
        exact Nat.add_le_add
          (Nat.le_mul_of_pos_right _ (Nat.mul_pos hK hE))
          (htime.trans (Nat.mul_le_mul_left _ hpow))
      _ ≤ K * W (ofGraph G) * E := by
        have hm := Nat.mul_le_mul_right (K * E)
          (show cc.time (ofGraph G) + D *
            ((TwoBoundary.BinaryFrontend.encInput (build (ofGraph G))).length + 1) ^ f ≤
              W (ofGraph G) from Nat.le_add_right _ _)
        nlinarith
      _ ≤ _ := Nat.mul_le_mul_right E (hCe _)

open Classical in
/-- The source real single-log-log exponent in original graph vertices, on the same actual
algorithm and explicit matrix encoding. The rounded theorem includes every smaller graph. -/
theorem exists_count_realEta_certificate :
    ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        count (ofGraph G) =
          Fintype.card {M : G.Subgraph // M.IsMatching ∧ M.IsInduced} ∧
        (16 ≤ n → (cs.time (ofGraph G) : ℝ) ≤ (C : ℝ) *
          ((encInput (ofGraph G)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨count, cs, C, e, A, hs, h⟩ := exists_count_sharp_certificate
  refine ⟨count, cs, C, e, 6 * A, hs, ?_⟩
  intro n G _
  refine ⟨(h G).1, fun hn => ?_⟩
  have ht : (cs.time (ofGraph G) : ℝ) ≤ (C : ℝ) *
      ((encInput (ofGraph G)).length + 1 : ℕ) ^ e *
        (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast (h G).2
  exact ht.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A hn) (by positivity))

end Cslib.Logic.PL.InducedMatching
