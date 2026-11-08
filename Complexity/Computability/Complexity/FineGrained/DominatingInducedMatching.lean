/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CNF.DominatingInducedMatching
public import Complexity.Computability.Complexity.FineGrained.TwoBoundaryFrontend
import all Complexity.Computability.PolyTime.CNF.SparseCNFLeafCounter

/-!
# Sharp counting and decision for actual dominating induced matchings

Compose the actual original-matrix reduction, proved endpoint-set/matching bijection and the
unrestricted-density native DNF counter. Counts are conventional Mathlib matching subgraphs whose
edges dominate each original edge exactly once. This is [ChenJiangZhu2027], Corollary D.4
(PDF p. 36) and its Corollary 7.4 decision/time/space specialization (p. 26).

## Main results

* `exists_count_sharp_certificate`: exact matching counts and complete native sharp time/global
  polynomial workspace, including empty and edgeless graphs.
* `exists_count_realEta_certificate`: the real source exponent for that same actual counter.
* `exists_decide_realEta_certificate`: complete actual decision including binary positivity.
-/

public section

namespace Cslib.Logic.PL.DominatingInducedMatching

open Turing.MultiTapeTM Cslib.Complexity Cslib.GenericRAM IndependentDomination

open Classical in
/-- One actual adjacency-matrix counter counts actual dominating induced matchings exactly
with global polynomial space and sharp rounded time in the original vertex count. -/
theorem exists_count_sharp_certificate :
    ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        count (ofGraph G) =
          Fintype.card {M : G.Subgraph // M.IsDominatingInducedMatching} ∧
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
  obtain ⟨hc, ht⟩ := h ((finiteUpper G ++ finiteCover G)) (finiteConditions G) hb hp
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
          Fintype.card {M : G.Subgraph // M.IsDominatingInducedMatching} ∧
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

open Classical in
/-- The actual matching decider has global polynomial workspace and the sharp source clock.
The binary positivity test is charged from the count certificate's output/space bound. -/
theorem exists_decide_sharp_certificate :
    ∃ decideMatching : Input → Bool, ∃ cs : NativeCertificate decideMatching encInput encBool,
      ∃ C e A : ℕ, (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        (decideMatching (ofGraph G) = true ↔ ∃ M : G.Subgraph, M.IsDominatingInducedMatching) ∧
        cs.time (ofGraph G) ≤ C * ((encInput (ofGraph G)).length + 1) ^ e *
          2 ^ (A * Nat.logLogSqrtLogScale n) := by
  obtain ⟨count, cp, C, e, A, hs, h⟩ := exists_count_sharp_certificate
  have hpos : ComputableInPolyTime (fun z : ℕ => decide (0 < z)) encNat encBool := by fun_prop
  let post := NativeCertificate.ofPolyTime hpos
  have hp := NativeCertificate.ofPolyTime_isPolynomial hpos
  let cs : NativeCertificate ((fun x => decide (0 < count x))) encInput encBool :=
    (post.comp cp).congr fun _ => rfl
  have hspace : PolyBounded (fun x => (encInput x).length) cp.space :=
    PolyBounded.of_forall_le C e hs
  obtain ⟨k, _, hlen⟩ := cp.computes
  have hlength : PolyBounded (fun x => (encInput x).length)
      (fun x => (encNat (count x)).length) :=
    ((PolyBounded.const k).mul (hspace.add (.const 1))).mono hlen
  have hpostT := hp.1.comp hlength
  have hpostS := hp.2.comp hlength
  have hcsS : PolyBounded (fun x => (encInput x).length) cs.space := hspace.add hpostS
  let W (x : Input) := C * ((encInput x).length + 1) ^ e + post.time (count x) + cs.space x
  have hW : PolyBounded (fun x => (encInput x).length) W :=
    (((PolyBounded.const C).mul ((PolyBounded.self.add (.const 1)).pow e)).add hpostT).add hcsS
  obtain ⟨D, f, hDf⟩ := hW.exists_le
  refine ⟨(fun x => decide (0 < count x)), cs, D, f, A,
    fun x => (Nat.le_add_left _ _).trans (hDf x), ?_⟩
  intro n G _
  obtain ⟨hc, ht⟩ := h G
  constructor
  · simp only [hc, decide_eq_true_eq, Fintype.card_pos_iff, nonempty_subtype]
  · let E := 2 ^ (A * Nat.logLogSqrtLogScale n)
    have hE : 0 < E := Nat.two_pow_pos _
    change cp.time (ofGraph G) + post.time (count (ofGraph G)) ≤ _
    calc
      _ ≤ (C * ((encInput (ofGraph G)).length + 1) ^ e +
          post.time (count (ofGraph G))) * E := by
        rw [Nat.add_mul]
        exact Nat.add_le_add ht (Nat.le_mul_of_pos_right _ hE)
      _ ≤ W (ofGraph G) * E := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
      _ ≤ _ := Nat.mul_le_mul_right _ (hDf _)

open Classical in
/-- Complete actual efficient-edge-domination decision has the real source eta bound. -/
theorem exists_decide_realEta_certificate :
    ∃ decideMatching : Input → Bool, ∃ cs : NativeCertificate decideMatching encInput encBool,
      ∃ C e A : ℕ, (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        (decideMatching (ofGraph G) = true ↔ ∃ M : G.Subgraph, M.IsDominatingInducedMatching) ∧
        (16 ≤ n → (cs.time (ofGraph G) : ℝ) ≤ (C : ℝ) *
          ((encInput (ofGraph G)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨decideMatching, cs, C, e, A, hs, h⟩ := exists_decide_sharp_certificate
  refine ⟨decideMatching, cs, C, e, 6 * A, hs, ?_⟩
  intro n G _
  refine ⟨(h G).1, fun hn => ?_⟩
  have ht : (cs.time (ofGraph G) : ℝ) ≤ (C : ℝ) *
      ((encInput (ofGraph G)).length + 1 : ℕ) ^ e *
        (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast (h G).2
  exact ht.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A hn) (by positivity))

end Cslib.Logic.PL.DominatingInducedMatching
