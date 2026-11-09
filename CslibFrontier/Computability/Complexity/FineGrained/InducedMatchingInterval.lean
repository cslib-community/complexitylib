/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.InducedMatchingInterval
public import CslibFrontier.Computability.Complexity.FineGrained.TwoBoundaryFrontend
import all CslibFrontier.Computability.PolyTime.CNF.SparseCNFLeafCounter

/-!
# Sharp induced matching counts with binary input size bounds

Compose actual degree-one constraints and functional endpoint-size tests with the unrestricted-
density native DNF counter. Every matching has one support and every support one circuit trace.
The interval frame and functional cardinality construction are shared with independent domination;
their graph predicate is replaced by matching. No edge-cover constraint is imposed. This
  implements the
counting reduction of [ChenJiangZhu2027], Proposition D.1 (PDF pp. 33–34), with actual binary
construction, sequential query counting and reconstruction costs. Full Corollary 7.5 distribution
iteration and witness/optimum extraction are separate endpoints.

## Main results

* `exists_count_sharp_certificate`: complete natural endpoint-interval counter resources.
* `exists_count_realEta_certificate`: original support correctness, single-loglog source time
  and global polynomial workspace.
* `Maximum.exists_count_realEta_certificate`: actual matching-object counts with varying signed
  binary edge thresholds, sharp original-vertex time and global polynomial workspace.
* `Maximum.exists_decide_realEta_certificate`: actual threshold decision including binary
  positivity.
-/

public section

namespace Cslib.Logic.PL.InducedMatchingInterval

open Turing.MultiTapeTM Cslib.Complexity Cslib.GenericRAM IndependentDominationInterval

open Classical in
/-- One actual endpoint-interval induced matching counter has global polynomial workspace and sharp
rounded time in original vertices, uniformly over both binary size bounds. -/
theorem exists_count_sharp_certificate :
    ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℕ),
        count (ofGraph G lo hi) =
          Fintype.card {x : Fin n → Bool // ((⊤ : G.Subgraph).induce {u | x u = true}).IsMatching ∧
            lo ≤ Cslib.BitString.weight x ∧ Cslib.BitString.weight x ≤ hi} ∧
        cs.time (ofGraph G lo hi) ≤ C * ((encInput (ofGraph G lo hi)).length + 1) ^ e *
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
  let K := 2 ^ (A * (5 * Nat.logLogSqrtLogScale 2097152))
  obtain ⟨C, e, hCe⟩ := ((PolyBounded.const K).mul hW).exists_le
  have hK : 0 < K := Nat.two_pow_pos _
  refine ⟨counter ∘ build, cs, C, e, 38120 * A, fun x => ?_, ?_⟩
  · exact (show cs.space x ≤ W x from Nat.le_add_left _ _).trans
      ((Nat.le_mul_of_pos_left _ hK).trans (hCe x))
  intro n G _ lo hi
  obtain ⟨B, P, hbuild, hb, hp, hplen, hcount⟩ := representation G lo hi
  obtain ⟨hc, ht⟩ := h B P hb hp
  let a := (CardinalityInterval.circuit n lo hi).size
  have ha : a ≤ 952 * (n + 1) := CardinalityInterval.size_circuit n lo hi
  have htime : cp.time (build (ofGraph G lo hi)) ≤
      D * ((TwoBoundary.BinaryFrontend.encInput (build (ofGraph G lo hi))).length + 1) ^ f *
        2 ^ (A * Nat.logLogSqrtLogScale (2 * n + a)) := by
    simpa only [hbuild, hplen, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
  have hscale : Nat.logLogSqrtLogScale (2 * n + a) ≤
      38120 * Nat.logLogSqrtLogScale n + 5 * Nat.logLogSqrtLogScale 2097152 := by
    by_cases hn : 1906 ≤ n
    · have hdim : 2 * n + a ≤ 1906 * n := by omega
      have hm := Nat.logLogSqrtLogScale_le_of_le hdim (by omega : 4 ≤ 1906 * n)
      have hl := Nat.logLogSqrtLogScale_mul_le 1906 (by omega : max 4 1906 ≤ n)
      omega
    · have hm := Nat.logLogSqrtLogScale_le_of_le
        (by omega : 2 * n + a ≤ 2097152) (by decide : 4 ≤ 2097152)
      omega
  let E := 2 ^ ((38120 * A) * Nat.logLogSqrtLogScale n)
  have hE : 0 < E := Nat.two_pow_pos _
  have hpow : 2 ^ (A * Nat.logLogSqrtLogScale (2 * n + a)) ≤ K * E := by
    calc _ ≤ 2 ^ (A * (38120 * Nat.logLogSqrtLogScale n +
        5 * Nat.logLogSqrtLogScale 2097152)) :=
          Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left A hscale)
      _ = _ := by dsimp only [K, E]; rw [Nat.mul_add, pow_add, mul_comm]; congr 1; ring
  constructor
  · change counter (build (ofGraph G lo hi)) = _
    rw [hbuild, hc, hcount]
  · change cc.time (ofGraph G lo hi) + cp.time (build (ofGraph G lo hi)) ≤ _
    calc
      _ ≤ (cc.time (ofGraph G lo hi) +
          D * ((TwoBoundary.BinaryFrontend.encInput (build (ofGraph G lo hi))).length + 1) ^ f) *
            (K * E) := by
        rw [Nat.add_mul]
        exact Nat.add_le_add
          (Nat.le_mul_of_pos_right _ (Nat.mul_pos hK hE))
          (htime.trans (Nat.mul_le_mul_left _ hpow))
      _ ≤ K * W (ofGraph G lo hi) * E := by
        have hm := Nat.mul_le_mul_right (K * E)
          (show cc.time (ofGraph G lo hi) + D *
            ((TwoBoundary.BinaryFrontend.encInput (build (ofGraph G lo hi))).length + 1) ^ f ≤
              W (ofGraph G lo hi) from Nat.le_add_right _ _)
        nlinarith
      _ ≤ _ := Nat.mul_le_mul_right E (hCe _)

open Classical in
/-- The real single-log-log source exponent, including actual binary-bound construction and
count reconstruction. Rounded bounds cover all smaller graphs and degenerate intervals. -/
theorem exists_count_realEta_certificate :
    ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℕ),
        count (ofGraph G lo hi) =
          Fintype.card {x : Fin n → Bool // ((⊤ : G.Subgraph).induce {u | x u = true}).IsMatching ∧
            lo ≤ Cslib.BitString.weight x ∧ Cslib.BitString.weight x ≤ hi} ∧
        (16 ≤ n → (cs.time (ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
          ((encInput (ofGraph G lo hi)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨count, cs, C, e, A, hs, h⟩ := exists_count_sharp_certificate
  refine ⟨count, cs, C, e, 6 * A, hs, ?_⟩
  intro n G _ lo hi
  refine ⟨(h G lo hi).1, fun hn => ?_⟩
  have ht : (cs.time (ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
      ((encInput (ofGraph G lo hi)).length + 1 : ℕ) ^ e *
        (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast (h G lo hi).2
  exact ht.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A hn) (by positivity))

namespace Maximum

open Classical in
/-- Complete original-matrix counter for induced matchings with at least the varying signed
binary threshold of edges. The actual size generator caps before unary work. Empty graphs and
negative or impossible thresholds use the same proved algorithm, with no supplied answer. -/
theorem exists_count_sharp_certificate :
    ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℤ),
        count (ofGraph G k) =
          Nat.card {M : G.Subgraph // M.IsMatching ∧ M.IsInduced ∧
            k ≤ (Nat.card M.edgeSet : ℤ)} ∧
        cs.time (ofGraph G k) ≤ C * ((encInput (ofGraph G k)).length + 1) ^ e *
          2 ^ (A * Nat.logLogSqrtLogScale n) := by
  obtain ⟨counter, cp, D, f, A, hs, h⟩ :=
    InducedMatchingInterval.exists_count_sharp_certificate
  let norm := NativeCertificate.ofPolyTime prepare_polytime
  have hnorm := NativeCertificate.ofPolyTime_isPolynomial prepare_polytime
  let cs := cp.comp norm
  have hcpS : PolyBounded (fun x => (IndependentDominationInterval.encInput x).length) cp.space :=
    PolyBounded.of_forall_le D f hs
  have hcsS := SparseCNFLeafCounter.polyBounded_comp_space cp norm hcpS hnorm.2
  let W (x : Input) := norm.time x +
    D * ((IndependentDominationInterval.encInput (prepare x)).length + 1) ^ f + cs.space x
  have hW : PolyBounded (fun x => (encInput x).length) W :=
    (hnorm.1.add ((PolyBounded.const D).mul
      ((prepare_polytime.polyBounded_length.add (.const 1)).pow f))).add hcsS
  obtain ⟨C, e, hCe⟩ := hW.exists_le
  refine ⟨counter ∘ prepare, cs, C, e, A,
    fun x => (Nat.le_add_left _ _).trans (hCe x), ?_⟩
  intro n G _ k
  have hinput : prepare (ofGraph G k) =
      IndependentDominationInterval.ofGraph G (2 * k).toNat n := rfl
  obtain ⟨hc, ht⟩ := h G (2 * k).toNat n
  constructor
  · change counter (prepare (ofGraph G k)) = _
    rw [hinput, hc]
    exact count_correspondence G k
  · let E := 2 ^ (A * Nat.logLogSqrtLogScale n)
    have hE : 0 < E := Nat.two_pow_pos _
    have htime : cp.time (prepare (ofGraph G k)) ≤
        D * ((IndependentDominationInterval.encInput (prepare (ofGraph G k))).length + 1) ^ f *
          E := by simpa only [hinput] using ht
    change norm.time (ofGraph G k) + cp.time (prepare (ofGraph G k)) ≤ _
    calc
      _ ≤ (norm.time (ofGraph G k) + D *
          ((IndependentDominationInterval.encInput (prepare (ofGraph G k))).length + 1) ^ f) *
            E := by
        rw [Nat.add_mul]
        exact Nat.add_le_add (Nat.le_mul_of_pos_right _ hE) htime
      _ ≤ W (ofGraph G k) * E := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
      _ ≤ _ := Nat.mul_le_mul_right _ (hCe _)

open Classical in
/-- Proposition D.1 / Corollary 7.4 counting with the real source exponent, uniformly over signed
binary thresholds. Polynomial space holds on every raw frame, independent of graph validity. -/
theorem exists_count_realEta_certificate :
    ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℤ),
        count (ofGraph G k) =
          Nat.card {M : G.Subgraph // M.IsMatching ∧ M.IsInduced ∧
            k ≤ (Nat.card M.edgeSet : ℤ)} ∧
        (16 ≤ n → (cs.time (ofGraph G k) : ℝ) ≤ (C : ℝ) *
          ((encInput (ofGraph G k)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨count, cs, C, e, A, hs, h⟩ := exists_count_sharp_certificate
  refine ⟨count, cs, C, e, 6 * A, hs, ?_⟩
  intro n G _ k
  refine ⟨(h G k).1, fun hn => ?_⟩
  have ht : (cs.time (ofGraph G k) : ℝ) ≤ (C : ℝ) *
      ((encInput (ofGraph G k)).length + 1 : ℕ) ^ e *
        (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast (h G k).2
  exact ht.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A hn) (by positivity))

open Classical in
/-- The actual matching decider has global polynomial workspace and the sharp source clock.
The binary positivity test is charged from the count certificate's output/space bound. -/
theorem exists_decide_sharp_certificate :
    ∃ decideMatching : Input → Bool, ∃ cs : NativeCertificate decideMatching encInput encBool,
      ∃ C e A : ℕ, (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℤ),
        (decideMatching (ofGraph G k) = true ↔ ∃ M : G.Subgraph, M.IsMatching ∧ M.IsInduced ∧ k ≤
          (Nat.card M.edgeSet : ℤ)) ∧
        cs.time (ofGraph G k) ≤ C * ((encInput (ofGraph G k)).length + 1) ^ e *
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
  intro n G _ k
  obtain ⟨hc, ht⟩ := h G k
  constructor
  · simp only [hc, Nat.card_eq_fintype_card, decide_eq_true_eq, Fintype.card_pos_iff,
      nonempty_subtype]
  · let E := 2 ^ (A * Nat.logLogSqrtLogScale n)
    have hE : 0 < E := Nat.two_pow_pos _
    change cp.time (ofGraph G k) + post.time (count (ofGraph G k)) ≤ _
    calc
      _ ≤ (C * ((encInput (ofGraph G k)).length + 1) ^ e +
          post.time (count (ofGraph G k))) * E := by
        rw [Nat.add_mul]
        exact Nat.add_le_add ht (Nat.le_mul_of_pos_right _ hE)
      _ ≤ W (ofGraph G k) * E := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
      _ ≤ _ := Nat.mul_le_mul_right _ (hDf _)

open Classical in
/-- Complete actual maximum-induced-matching decision has the real source eta bound. -/
theorem exists_decide_realEta_certificate :
    ∃ decideMatching : Input → Bool, ∃ cs : NativeCertificate decideMatching encInput encBool,
      ∃ C e A : ℕ, (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℤ),
        (decideMatching (ofGraph G k) = true ↔ ∃ M : G.Subgraph, M.IsMatching ∧ M.IsInduced ∧ k ≤
          (Nat.card M.edgeSet : ℤ)) ∧
        (16 ≤ n → (cs.time (ofGraph G k) : ℝ) ≤ (C : ℝ) *
          ((encInput (ofGraph G k)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨decideMatching, cs, C, e, A, hs, h⟩ := exists_decide_sharp_certificate
  refine ⟨decideMatching, cs, C, e, 6 * A, hs, ?_⟩
  intro n G _ k
  refine ⟨(h G k).1, fun hn => ?_⟩
  have ht : (cs.time (ofGraph G k) : ℝ) ≤ (C : ℝ) *
      ((encInput (ofGraph G k)).length + 1 : ℕ) ^ e *
        (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast (h G k).2
  exact ht.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A hn) (by positivity))

end Maximum

end Cslib.Logic.PL.InducedMatchingInterval
