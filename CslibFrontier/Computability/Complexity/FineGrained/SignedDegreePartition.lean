/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.BoundedDegreePartitionCountingResources
public import CslibFrontier.Computability.PolyTime.CNF.SignedClassBounds
import CslibFrontier.Computability.PolyTime.CNF.SparseCNFLeafCounter

/-!
# Native labeled-partition counting with signed binary bounds

Compose actual signed normalization with the native general degree-matrix counter of
[ChenJiangZhu2027], Theorem 7.3 (PDF p.25). Every input class interval varies, including
negative and contradictory bounds. Labels, empty classes and original graph bits are retained.

## Main results

* `normalize_polytime`: complete original-input binary transformation.
* `exists_count_sharp_certificate`: actual composed counter with rounded sharp resources.
* `exists_count_finiteCofinite_certificate`: all fixed finite/cofinite matrices and the real clock.
-/

public section
namespace Cslib.Logic.PL.DegreePartition.Signed
open Turing.MultiTapeTM Cslib.GenericRAM Cslib.Complexity

/-- Explicit graph with unary declaration and ordered signed binary class intervals. -/
abbrev Input := IndependentDomination.Input × List (ℤ × ℤ)
/-- Graph framed before the framed list of signed binary lower/upper pairs. -/
abbrev encInput : Input ↪ List Bool :=
  encPair IndependentDomination.encInput SignedClassBounds.encInput
/-- Actual original graph and normalized interval list, without relabeling or unary expansion. -/
@[expose] def normalize (x : Input) : Bounded.BinaryFrontend.Input :=
  (x.1, SignedClassBounds.normalize x.2)
/-- Canonical explicitly represented graph and signed bounds for every original label. -/
@[expose] def ofGraph {n q : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lo hi : Fin q → ℤ) : Input := (IndependentDomination.ofGraph G,
      List.ofFn fun i => (lo i, hi i))

/-- Binary normalization includes graph copying, interval traversal and all framed output writes. -/
theorem normalize_polytime : ComputableInPolyTime normalize encInput
    Bounded.BinaryFrontend.encInput :=
  (ComputableInPolyTime.fst _ _).prod
    (SignedClassBounds.normalize_polytime.comp (ComputableInPolyTime.snd _ _))

private theorem normalize_ofGraph {n q : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lo hi : Fin q → ℤ) : normalize (ofGraph G lo hi) = Bounded.BinaryFrontend.ofGraph G
      (fun i => (SignedClassBounds.pair (lo i, hi i)).1)
      (fun i => (SignedClassBounds.pair (lo i, hi i)).2) := by
  simp only [normalize, ofGraph, Bounded.BinaryFrontend.ofGraph,
    SignedClassBounds.normalize_ofFn, SignedClassBounds.pair]

open Classical in
/-- The complete actual signed counter, with no supplied runtime or normalization contract. -/
theorem exists_count_sharp_certificate (q D : ℕ) (hD : 1 ≤ D)
    (M : Fin q → Fin q → SimpleGraph.DegreeRule D) :
    ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : Fin q → ℤ),
        count (ofGraph G lo hi) = Fintype.card {S : Fin q → Set (Fin n) //
          G.IsDegreePartition (fun i j => (M i j).counts) S ∧
            ∀ i, lo i ≤ (Nat.card (S i) : ℤ) ∧ (Nat.card (S i) : ℤ) ≤ hi i} ∧
        cs.time (ofGraph G lo hi) ≤ C * ((encInput (ofGraph G lo hi)).length + 1) ^ e *
          2 ^ (A * Nat.logLogSqrtLogScale n) := by
  obtain ⟨counter, cp, C, e, A, hs, h⟩ :=
    Bounded.BinaryFrontend.exists_count_sharp_certificate q D hD M
  let pre := NativeCertificate.ofPolyTime normalize_polytime
  have hp := NativeCertificate.ofPolyTime_isPolynomial normalize_polytime
  let cs := cp.comp pre
  have hcsS := SparseCNFLeafCounter.polyBounded_comp_space cp pre
    (PolyBounded.of_forall_le C e hs) hp.2
  let W (x : Input) := pre.time x +
    C * ((Bounded.BinaryFrontend.encInput (normalize x)).length + 1) ^ e + cs.space x
  have hW : PolyBounded (fun x => (encInput x).length) W :=
    (hp.1.add ((PolyBounded.const C).mul
      ((normalize_polytime.polyBounded_length.add (.const 1)).pow e))).add hcsS
  obtain ⟨B, f, hBf⟩ := hW.exists_le
  refine ⟨counter ∘ normalize, cs, B, f, A,
    fun x => (Nat.le_add_left _ _).trans (hBf x), ?_⟩
  intro n G _ lo hi
  obtain ⟨hc, ht⟩ := h G (fun i => (SignedClassBounds.pair (lo i, hi i)).1)
    (fun i => (SignedClassBounds.pair (lo i, hi i)).2)
  rw [← normalize_ofGraph] at hc ht
  constructor
  · change counter (normalize (ofGraph G lo hi)) = _
    rw [hc]
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro S
    exact and_congr_right fun _ => SignedClassBounds.bounds_iff lo hi (fun i => Nat.card (S i))
  · let x := ofGraph G lo hi
    let E := 2 ^ (A * Nat.logLogSqrtLogScale n)
    have hE : 0 < E := Nat.two_pow_pos _
    have ht' : cp.time (normalize x) ≤
        C * ((Bounded.BinaryFrontend.encInput (normalize x)).length + 1) ^ e * E := ht
    change pre.time x + cp.time (normalize x) ≤ _
    calc _ ≤ (pre.time x +
        C * ((Bounded.BinaryFrontend.encInput (normalize x)).length + 1) ^ e) * E := by
          have := Nat.le_mul_of_pos_right (pre.time x) hE
          nlinarith only [ht', this]
      _ ≤ W x * E := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
      _ ≤ _ := Nat.mul_le_mul_right _ (hBf x)

open Classical in
/-- Fixed finite/cofinite rules, arbitrary signed input intervals, exact original counts and
source real eta time with global polynomial workspace. Empty graphs are included. -/
theorem exists_count_finiteCofinite_certificate {q : ℕ} (M : Fin q → Fin q → Set ℕ)
    (hM : ∀ i j, (M i j).Finite ∨ (M i j)ᶜ.Finite) :
    ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : Fin q → ℤ),
        count (ofGraph G lo hi) = Fintype.card {S : Fin q → Set (Fin n) //
          G.IsDegreePartition M S ∧
            ∀ i, lo i ≤ (Nat.card (S i) : ℤ) ∧ (Nat.card (S i) : ℤ) ≤ hi i} ∧
        (16 ≤ n → (cs.time (ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
          ((encInput (ofGraph G lo hi)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨D, hD, R, hR⟩ := SimpleGraph.exists_degreeMatrixRules M hM
  obtain ⟨count, cs, C, e, A, hs, h⟩ := exists_count_sharp_certificate q D hD R
  refine ⟨count, cs, C, e, 6 * A, hs, ?_⟩
  intro n G _ lo hi
  refine ⟨by simpa only [hR] using (h G lo hi).1, fun hn => ?_⟩
  have ht : (cs.time (ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
      ((encInput (ofGraph G lo hi)).length + 1 : ℕ) ^ e *
        (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast (h G lo hi).2
  exact ht.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A hn) (by positivity))

end Cslib.Logic.PL.DegreePartition.Signed
