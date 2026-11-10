/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.RegularInducedInterval
public import CslibFrontier.Computability.Complexity.FineGrained.TwoBoundaryFrontend
import all CslibFrontier.Computability.PolyTime.CNF.SparseCNFLeafCounter

/-!
# Sharp compact regular induced-subgraph counting by size

The complete actual fixed-degree constructor of [ChenJiangZhu2027], Proposition C.2 (PDF pp.32–33),
is composed with the native bounded-width counter. Both size bounds vary in signed binary;
normalization, size gates, query writing, counting and binary reconstruction are charged.

## Main results

* `exists_count_sharp_certificate`: natural binary intervals and sharp native resources.
* `Signed.exists_count_sharp_certificate`: signed intervals with direct empty-graph handling.
* `Signed.exists_count_realEta_certificate`: the source single-log-log clock and global workspace.
* `Signed.exists_decide_realEta_certificate`: actual binary positivity decision with the same rate.
-/

public section

namespace Cslib.Logic.PL.RegularInducedInterval

open Turing.MultiTapeTM Cslib.Complexity Cslib.GenericRAM

section

open IndependentDominationInterval

open Classical in
/-- One actual interval-constrained graph counter has global polynomial workspace and sharp
rounded time in original vertices, uniformly over both binary size bounds. -/
theorem exists_count_sharp_certificate (d : ℕ) (hd : 1 ≤ d) :
    ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℕ),
        count (ofGraph G lo hi) =
          Fintype.card {x : Fin n → Bool // G.IsSigmaRhoSet {d} Set.univ {u | x u = true} ∧
            lo ≤ Cslib.BitString.weight x ∧ Cslib.BitString.weight x ≤ hi} ∧
        cs.time (ofGraph G lo hi) ≤ C * ((encInput (ofGraph G lo hi)).length + 1) ^ e *
          2 ^ (A * Nat.logLogSqrtLogScale n) := by
  obtain ⟨counter, cp, D, f, A, hs, h⟩ :=
    TwoBoundary.BinaryFrontend.exists_count_sharp_certificate (d + 2) d
  let cc := NativeCertificate.ofPolyTime (build_polytime d)
  have hcc := NativeCertificate.ofPolyTime_isPolynomial (build_polytime d)
  let cs := cp.comp cc
  have hcpS : PolyBounded
      (fun x => (TwoBoundary.BinaryFrontend.encInput x).length) cp.space :=
    PolyBounded.of_forall_le D f hs
  have hcsS := SparseCNFLeafCounter.polyBounded_comp_space cp cc hcpS hcc.2
  let W (x : Input) := cc.time x +
    D * ((TwoBoundary.BinaryFrontend.encInput ((build d) x)).length + 1) ^ f + cs.space x
  have hW : PolyBounded (fun x => (encInput x).length) W :=
    (hcc.1.add ((PolyBounded.const D).mul
      (((build_polytime d).polyBounded_length.add (.const 1)).pow f))).add hcsS
  let K := 2 ^ (A * (5 * Nat.logLogSqrtLogScale 2097152))
  obtain ⟨C, e, hCe⟩ := ((PolyBounded.const K).mul hW).exists_le
  have hK : 0 < K := Nat.two_pow_pos _
  refine ⟨counter ∘ (build d), cs, C, e, 38120 * A, fun x => ?_, ?_⟩
  · exact (show cs.space x ≤ W x from Nat.le_add_left _ _).trans
      ((Nat.le_mul_of_pos_left _ hK).trans (hCe x))
  intro n G _ lo hi
  obtain ⟨B, P, hbuild, hb, hp, hplen, hcount⟩ := representation d hd G lo hi
  obtain ⟨hc, ht⟩ := h B P hb hp
  let a := (CardinalityInterval.circuit n lo hi).size
  have ha : a ≤ 952 * (n + 1) := CardinalityInterval.size_circuit n lo hi
  have htime : cp.time ((build d) (ofGraph G lo hi)) ≤
      D * ((TwoBoundary.BinaryFrontend.encInput ((build d) (ofGraph G lo hi))).length + 1) ^ f *
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
  · change counter ((build d) (ofGraph G lo hi)) = _
    rw [hbuild, hc, hcount]
  · change cc.time (ofGraph G lo hi) + cp.time ((build d) (ofGraph G lo hi)) ≤ _
    calc
      _ ≤ (cc.time (ofGraph G lo hi) +
          D * ((TwoBoundary.BinaryFrontend.encInput
            ((build d) (ofGraph G lo hi))).length + 1) ^ f) *
            (K * E) := by
        rw [Nat.add_mul]
        exact Nat.add_le_add
          (Nat.le_mul_of_pos_right _ (Nat.mul_pos hK hE))
          (htime.trans (Nat.mul_le_mul_left _ hpow))
      _ ≤ K * W (ofGraph G lo hi) * E := by
        have hm := Nat.mul_le_mul_right (K * E)
          (show cc.time (ofGraph G lo hi) + D *
            ((TwoBoundary.BinaryFrontend.encInput ((build d) (ofGraph G lo hi))).length + 1) ^ f ≤
              W (ofGraph G lo hi) from Nat.le_add_right _ _)
        nlinarith
      _ ≤ _ := Nat.mul_le_mul_right E (hCe _)

open Classical in
/-- The real single-log-log source exponent, including actual binary-bound construction and
count reconstruction. Rounded bounds cover all smaller graphs and degenerate intervals. -/
theorem exists_count_realEta_certificate (d : ℕ) (hd : 1 ≤ d) :
    ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℕ),
        count (ofGraph G lo hi) =
          Fintype.card {x : Fin n → Bool // G.IsSigmaRhoSet {d} Set.univ {u | x u = true} ∧
            lo ≤ Cslib.BitString.weight x ∧ Cslib.BitString.weight x ≤ hi} ∧
        (16 ≤ n → (cs.time (ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
          ((encInput (ofGraph G lo hi)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨count, cs, C, e, A, hs, h⟩ := exists_count_sharp_certificate d hd
  refine ⟨count, cs, C, e, 6 * A, hs, ?_⟩
  intro n G _ lo hi
  refine ⟨(h G lo hi).1, fun hn => ?_⟩
  have ht : (cs.time (ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
      ((encInput (ofGraph G lo hi)).length + 1 : ℕ) ^ e *
        (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast (h G lo hi).2
  exact ht.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A hn) (by positivity))

end

namespace Signed

open IndependentDominationInterval.Signed

open Classical in
/-- Complete signed-binary interval counting, with direct empty-graph dispatch and actual
normalization/circuit/query/count/reconstruction costs. Both signed bounds vary with the input. -/
theorem exists_count_sharp_certificate (d : ℕ) (hd : 1 ≤ d) :
    ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℤ),
        count (ofGraph G lo hi) =
          Fintype.card {x : Fin n → Bool // G.IsSigmaRhoSet {d} Set.univ {u | x u = true} ∧
            lo ≤ (Cslib.BitString.weight x : ℤ) ∧ (Cslib.BitString.weight x : ℤ) ≤ hi} ∧
        cs.time (ofGraph G lo hi) ≤ C * ((encInput (ofGraph G lo hi)).length + 1) ^ e *
          2 ^ (A * Nat.logLogSqrtLogScale n) := by
  obtain ⟨counter, cp, D, f, A, hs, h⟩ :=
    RegularInducedInterval.exists_count_sharp_certificate d hd
  let norm := NativeCertificate.ofPolyTime normalize_polytime
  have hnorm := NativeCertificate.ofPolyTime_isPolynomial normalize_polytime
  let cn := cp.comp norm
  have hcpS : PolyBounded (fun x => (IndependentDominationInterval.encInput x).length) cp.space :=
    PolyBounded.of_forall_le D f hs
  have hcnS := SparseCNFLeafCounter.polyBounded_comp_space cp norm hcpS hnorm.2
  let tag := NativeCertificate.ofPolyTime isEmpty_polytime
  let direct := NativeCertificate.ofPolyTime emptyAnswer_polytime
  have htag := NativeCertificate.ofPolyTime_isPolynomial isEmpty_polytime
  have hdirect := NativeCertificate.ofPolyTime_isPolynomial emptyAnswer_polytime
  let cs : NativeCertificate (run counter) encInput encNat :=
    (NativeCertificate.branch tag direct cn).congr fun _ => rfl
  have hcsS : PolyBounded (fun x => (encInput x).length) cs.space :=
    ((htag.2.add hdirect.2).add hcnS).mono fun x => by
      change tag.space x + (if isEmpty x then direct.space x else cn.space x) ≤
        tag.space x + direct.space x + cn.space x
      split_ifs <;> omega
  let W (x : Input) := tag.time x + direct.time x + norm.time x +
    D * ((IndependentDominationInterval.encInput (normalize x)).length + 1) ^ f + cs.space x
  have hW : PolyBounded (fun x => (encInput x).length) W :=
    (((htag.1.add hdirect.1).add hnorm.1).add ((PolyBounded.const D).mul
      ((normalize_polytime.polyBounded_length.add (.const 1)).pow f))).add hcsS
  obtain ⟨C, e, hCe⟩ := hW.exists_le
  refine ⟨run counter, cs, C, e, A, fun x => (Nat.le_add_left _ _).trans (hCe x), ?_⟩
  intro n G _ lo hi
  let x := ofGraph G lo hi
  have hinput : normalize x = IndependentDominationInterval.ofGraph G
      (lowerNat lo hi) (upperNat hi) := rfl
  obtain ⟨hc, ht⟩ := h G (lowerNat lo hi) (upperNat hi)
  have htime : cp.time (normalize x) ≤
      D * ((IndependentDominationInterval.encInput (normalize x)).length + 1) ^ f *
        2 ^ (A * Nat.logLogSqrtLogScale n) := by simpa only [hinput] using ht
  constructor
  · change run counter x = _
    by_cases hn : n = 0
    · subst n
      simp only [x, run, isEmpty, ofGraph, graph, IndependentDomination.ofGraph,
        IndependentDomination.order, decide_true, ↓reduceIte, emptyAnswer, lower, upper]
      rw [zero_count d]
      rfl
    · have hnon : isEmpty x = false := by simp [x, isEmpty, ofGraph, graph,
        IndependentDomination.ofGraph, IndependentDomination.order, hn]
      simp only [run, hnon, Bool.false_eq_true, ↓reduceIte, hinput, hc]
      apply Fintype.card_congr
      apply Equiv.subtypeEquivRight
      intro z
      rw [bounds_iff]
  · let E := 2 ^ (A * Nat.logLogSqrtLogScale n)
    have hE : 0 < E := Nat.two_pow_pos _
    change tag.time x + (if isEmpty x then direct.time x else
      norm.time x + cp.time (normalize x)) ≤ _
    calc
      _ ≤ tag.time x + direct.time x + norm.time x + cp.time (normalize x) := by
        split_ifs <;> omega
      _ ≤ (tag.time x + direct.time x + norm.time x +
          D * ((IndependentDominationInterval.encInput (normalize x)).length + 1) ^ f) * E := by
        rw [Nat.add_mul]
        exact Nat.add_le_add (Nat.le_mul_of_pos_right _ hE) htime
      _ ≤ W x * E := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
      _ ≤ _ := Nat.mul_le_mul_right _ (hCe x)

open Classical in
/-- Real source eta for the same actual signed-bound algorithm; small and empty graphs retain
rounded bounds. Upper, lower and equality tests use variable signed binary inputs. -/
theorem exists_count_realEta_certificate (d : ℕ) (hd : 1 ≤ d) :
    ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℤ),
        count (ofGraph G lo hi) =
          Fintype.card {x : Fin n → Bool // G.IsSigmaRhoSet {d} Set.univ {u | x u = true} ∧
            lo ≤ (Cslib.BitString.weight x : ℤ) ∧ (Cslib.BitString.weight x : ℤ) ≤ hi} ∧
        (16 ≤ n → (cs.time (ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
          ((encInput (ofGraph G lo hi)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨count, cs, C, e, A, hs, h⟩ := exists_count_sharp_certificate d hd
  refine ⟨count, cs, C, e, 6 * A, hs, ?_⟩
  intro n G _ lo hi
  refine ⟨(h G lo hi).1, fun hn => ?_⟩
  have ht : (cs.time (ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
      ((encInput (ofGraph G lo hi)).length + 1 : ℕ) ^ e *
        (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast (h G lo hi).2
  exact ht.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A hn) (by positivity))


open Classical in
/-- Actual yes/no interval decision is a charged binary positivity test of the exact count. -/
theorem exists_decide_sharp_certificate (d : ℕ) (hd : 1 ≤ d) :
    ∃ yes : Input → Bool, ∃ cs : NativeCertificate yes encInput encBool, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℤ),
        (yes (ofGraph G lo hi) = true ↔ ∃ x : Fin n → Bool,
          G.IsSigmaRhoSet {d} Set.univ {u | x u = true} ∧
            lo ≤ (Cslib.BitString.weight x : ℤ) ∧ (Cslib.BitString.weight x : ℤ) ≤ hi) ∧
        cs.time (ofGraph G lo hi) ≤ C * ((encInput (ofGraph G lo hi)).length + 1) ^ e *
          2 ^ (A * Nat.logLogSqrtLogScale n) := by
  obtain ⟨count, cp, C, e, A, hs, h⟩ := exists_count_sharp_certificate d hd
  have hpos : ComputableInPolyTime (fun z : ℕ => decide (0 < z)) encNat encBool := by fun_prop
  let post := NativeCertificate.ofPolyTime hpos
  have hp := NativeCertificate.ofPolyTime_isPolynomial hpos
  let cs := post.comp cp
  have hspace := PolyBounded.of_forall_le C e hs
  have hlength := SparseCNFLeafCounter.polyBounded_output_of_space cp hspace
  have hpostT := hp.1.comp hlength
  have hcsS := SparseCNFLeafCounter.polyBounded_comp_space post cp hp.2 hspace
  let W (x : Input) := C * ((encInput x).length + 1) ^ e + post.time (count x) + cs.space x
  have hW : PolyBounded (fun x => (encInput x).length) W :=
    (((PolyBounded.const C).mul ((PolyBounded.self.add (.const 1)).pow e)).add hpostT).add hcsS
  obtain ⟨D, f, hDf⟩ := hW.exists_le
  refine ⟨(fun x => decide (0 < count x)), cs, D, f, A,
    fun x => (Nat.le_add_left _ _).trans (hDf x), ?_⟩
  intro n G _ lo hi
  obtain ⟨hc, ht⟩ := h G lo hi
  constructor
  · simp only [hc, decide_eq_true_eq, Fintype.card_pos_iff, nonempty_subtype]
  · let E := 2 ^ (A * Nat.logLogSqrtLogScale n)
    have hE : 0 < E := Nat.two_pow_pos _
    change cp.time (ofGraph G lo hi) + post.time (count (ofGraph G lo hi)) ≤ _
    calc _ ≤ (C * ((encInput (ofGraph G lo hi)).length + 1) ^ e +
        post.time (count (ofGraph G lo hi))) * E := by
          rw [Nat.add_mul]
          exact Nat.add_le_add ht (Nat.le_mul_of_pos_right _ hE)
      _ ≤ W (ofGraph G lo hi) * E := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
      _ ≤ _ := Nat.mul_le_mul_right _ (hDf _)

open Classical in
/-- The signed interval decider has the source single-log-log real clock and global workspace. -/
theorem exists_decide_realEta_certificate (d : ℕ) (hd : 1 ≤ d) :
    ∃ yes : Input → Bool, ∃ cs : NativeCertificate yes encInput encBool, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℤ),
        (yes (ofGraph G lo hi) = true ↔ ∃ x : Fin n → Bool,
          G.IsSigmaRhoSet {d} Set.univ {u | x u = true} ∧
            lo ≤ (Cslib.BitString.weight x : ℤ) ∧ (Cslib.BitString.weight x : ℤ) ≤ hi) ∧
        (16 ≤ n → (cs.time (ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
          ((encInput (ofGraph G lo hi)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨yes, cs, C, e, A, hs, h⟩ := exists_decide_sharp_certificate d hd
  refine ⟨yes, cs, C, e, 6 * A, hs, ?_⟩
  intro n G _ lo hi
  refine ⟨(h G lo hi).1, fun hn => ?_⟩
  have ht : (cs.time (ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
      ((encInput (ofGraph G lo hi)).length + 1 : ℕ) ^ e *
        (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast (h G lo hi).2
  exact ht.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A hn) (by positivity))


end Signed

end Cslib.Logic.PL.RegularInducedInterval
