/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.PerfectMatchingCut
public import CslibFrontier.Computability.Complexity.FineGrained.TwoBoundaryFrontend
import all CslibFrontier.Computability.PolyTime.CNF.SparseCNFLeafCounter

/-!
# Complete sharp perfect-matching-cut counting and decision

Actual original-matrix construction, direct empty rejection, sequential counting and binary
reconstruction are composed. Counts are of labeled cuts, with no extra matching certificates.
This is [ChenJiangZhu2027], Proposition D.2 (PDF p. 34) and the Perfect Matching Cut decision
specialization of Corollary 7.4 (p. 26), on explicit simple-undirected adjacency matrices.

## Main results

* `exists_count_sharp_certificate`: exact labeled-cut count, global polynomial workspace and
  rounded sharp time in original vertices, including the empty graph.
* `exists_count_realEta_certificate`: the same actual algorithm with the real source exponent.
* `exists_decide_realEta_certificate`: complete actual decision, including binary positivity.
-/

public section

namespace Cslib.Logic.PL.PerfectMatchingCut

open Turing.MultiTapeTM Cslib.Complexity Cslib.GenericRAM IndependentDomination

open Classical in
/-- Actual labeled-cut counting with direct empty rejection and sharp native resources.
Global workspace includes all query/reconstruction outputs, not just stage diagnostics. -/
theorem exists_count_sharp_certificate :
    ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        count (ofGraph G) = Fintype.card {side : Fin n → Bool // G.IsPerfectMatchingCut side} ∧
        cs.time (ofGraph G) ≤ C * ((encInput (ofGraph G)).length + 1) ^ e *
          2 ^ (A * Nat.logLogSqrtLogScale n) := by
  obtain ⟨counter, cp, D, f, A, hs, h⟩ :=
    TwoBoundary.BinaryFrontend.exists_count_sharp_certificate 3 1
  let cc := NativeCertificate.ofPolyTime build_polytime
  have hcc := NativeCertificate.ofPolyTime_isPolynomial build_polytime
  let raw := cp.comp cc
  have hcpS : PolyBounded
      (fun x => (TwoBoundary.BinaryFrontend.encInput x).length) cp.space :=
    PolyBounded.of_forall_le D f hs
  have hrawS := SparseCNFLeafCounter.polyBounded_comp_space cp cc hcpS hcc.2
  let tag := NativeCertificate.ofPolyTime isEmpty_polytime
  have htag := NativeCertificate.ofPolyTime_isPolynomial isEmpty_polytime
  have hzero : ComputableInPolyTime (fun _ : Input => 0) encInput encNat := .const 0
  let zero := NativeCertificate.ofPolyTime hzero
  have hzeroP := NativeCertificate.ofPolyTime_isPolynomial hzero
  let cs : NativeCertificate (run counter) encInput encNat :=
    (NativeCertificate.branch tag zero raw).congr fun _ => rfl
  have hcsS : PolyBounded (fun x => (encInput x).length) cs.space :=
    ((htag.2.add hzeroP.2).add hrawS).mono fun x => by
      change tag.space x + (if isEmpty x then zero.space x else raw.space x) ≤
        tag.space x + zero.space x + raw.space x
      split_ifs <;> omega
  let T (x : Input) := tag.time x + zero.time x + cc.time x
  have hT : PolyBounded (fun x => (encInput x).length) T := (htag.1.add hzeroP.1).add hcc.1
  let W (x : Input) := T x +
    D * ((TwoBoundary.BinaryFrontend.encInput (build x)).length + 1) ^ f + cs.space x
  have hW : PolyBounded (fun x => (encInput x).length) W :=
    (hT.add ((PolyBounded.const D).mul
      ((build_polytime.polyBounded_length.add (.const 1)).pow f))).add hcsS
  let K := 2 ^ (A * (5 * Nat.logLogSqrtLogScale 32))
  obtain ⟨C, e, hCe⟩ := ((PolyBounded.const K).mul hW).exists_le
  have hK : 0 < K := Nat.two_pow_pos _
  refine ⟨run counter, cs, C, e, 12 * A, fun x => ?_, ?_⟩
  · exact (show cs.space x ≤ W x from Nat.le_add_left _ _).trans
      ((Nat.le_mul_of_pos_left _ hK).trans (hCe x))
  intro n G _
  obtain ⟨hb, hp⟩ := widths G
  obtain ⟨hc, ht⟩ := h (finiteUpper G) (finiteConditions G) hb hp
  have htime : cp.time (build (ofGraph G)) ≤
      D * ((TwoBoundary.BinaryFrontend.encInput (build (ofGraph G))).length + 1) ^ f *
        2 ^ (A * Nat.logLogSqrtLogScale (3 * n)) := by
    simpa only [build_ofGraph, finiteConditions_length, show n + 2 * n = 3 * n by omega] using ht
  have hscale : Nat.logLogSqrtLogScale (3 * n) ≤
      12 * Nat.logLogSqrtLogScale n + 5 * Nat.logLogSqrtLogScale 32 := by
    by_cases hn : 4 ≤ n
    · have hm := Nat.logLogSqrtLogScale_mul_le 3 hn
      omega
    · have hm := Nat.logLogSqrtLogScale_le_of_le
        (by omega : 3 * n ≤ 32) (by decide : 4 ≤ 32)
      omega
  let E := 2 ^ ((12 * A) * Nat.logLogSqrtLogScale n)
  have hE : 0 < E := Nat.two_pow_pos _
  have hpow : 2 ^ (A * Nat.logLogSqrtLogScale (3 * n)) ≤ K * E := by
    calc _ ≤ 2 ^ (A * (12 * Nat.logLogSqrtLogScale n + 5 * Nat.logLogSqrtLogScale 32)) :=
          Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left A hscale)
      _ = _ := by dsimp only [K, E]; rw [Nat.mul_add, pow_add, mul_comm]; congr 1; ring
  constructor
  · by_cases hn : n = 0
    · subst n
      have hz : Fintype.card {side : Fin 0 → Bool // G.IsPerfectMatchingCut side} = 0 := by
        apply Fintype.card_eq_zero_iff.mpr
        refine ⟨fun z => ?_⟩
        obtain ⟨u, _⟩ := z.property.1
        exact Fin.elim0 u
      simp only [run, isEmpty, ofGraph, order, decide_true, ↓reduceIte, hz]
    · have hn' : 0 < n := Nat.pos_of_ne_zero hn
      have hcount : counter (build (ofGraph G)) =
          Fintype.card {side : Fin n → Bool // G.IsPerfectMatchingCut side} := by
        rw [build_ofGraph, hc]
        exact Fintype.card_congr (Equiv.subtypeEquivRight (finite_semantics G hn'))
      simpa only [run, isEmpty, ofGraph, order, hn, decide_false, Bool.false_eq_true,
        ↓reduceIte] using hcount
  · change tag.time (ofGraph G) + (if isEmpty (ofGraph G) then zero.time (ofGraph G) else
      cc.time (ofGraph G) + cp.time (build (ofGraph G))) ≤ _
    calc
      _ ≤ T (ofGraph G) + cp.time (build (ofGraph G)) := by
        dsimp only [T]
        split_ifs <;> omega
      _ ≤ (T (ofGraph G) +
          D * ((TwoBoundary.BinaryFrontend.encInput (build (ofGraph G))).length + 1) ^ f) *
            (K * E) := by
        rw [Nat.add_mul]
        exact Nat.add_le_add (Nat.le_mul_of_pos_right _ (Nat.mul_pos hK hE))
          (htime.trans (Nat.mul_le_mul_left _ hpow))
      _ ≤ K * W (ofGraph G) * E := by
        have hm := Nat.mul_le_mul_right (K * E)
          (show T (ofGraph G) + D *
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
          Fintype.card {side : Fin n → Bool // G.IsPerfectMatchingCut side} ∧
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
/-- The actual cut decider has global polynomial workspace and the sharp source clock.
The binary positivity test is charged from the count certificate's output/space bound. -/
theorem exists_decide_sharp_certificate :
    ∃ decideCut : Input → Bool, ∃ cs : NativeCertificate decideCut encInput encBool,
      ∃ C e A : ℕ, (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        (decideCut (ofGraph G) = true ↔ ∃ side : Fin n → Bool, G.IsPerfectMatchingCut side) ∧
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
/-- Complete actual perfect-matching-cut decision has the real source eta bound. -/
theorem exists_decide_realEta_certificate :
    ∃ decideCut : Input → Bool, ∃ cs : NativeCertificate decideCut encInput encBool,
      ∃ C e A : ℕ, (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        (decideCut (ofGraph G) = true ↔ ∃ side : Fin n → Bool, G.IsPerfectMatchingCut side) ∧
        (16 ≤ n → (cs.time (ofGraph G) : ℝ) ≤ (C : ℝ) *
          ((encInput (ofGraph G)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨decideCut, cs, C, e, A, hs, h⟩ := exists_decide_sharp_certificate
  refine ⟨decideCut, cs, C, e, 6 * A, hs, ?_⟩
  intro n G _
  refine ⟨(h G).1, fun hn => ?_⟩
  have ht : (cs.time (ofGraph G) : ℝ) ≤ (C : ℝ) *
      ((encInput (ofGraph G)).length + 1 : ℕ) ^ e *
        (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast (h G).2
  exact ht.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A hn) (by positivity))

end Cslib.Logic.PL.PerfectMatchingCut
