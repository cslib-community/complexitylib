/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.SigmaRhoOptimum
public import CslibFrontier.Computability.Complexity.FineGrained.SigmaRhoCountingResources
import CslibFrontier.Computability.PolyTime.CNF.SparseCNFLeafCounter

/-!
# Native degree-rule counting and extrema with signed binary bounds

Compose the actual signed normalizer with the approved general finite/cofinite rule algorithms.
The graph is unchanged, so the sharp exponent remains in original vertices. Every original bit,
normalization step, output tag and returned binary value is charged by the composed certificate.

## Main results

* `optimal_iff`: signed feasibility, attainment and global optimality transport.
* `exists_count_sharp_certificate`: exact signed set counts and native resources.
* `exists_count_finiteCofinite_certificate`: source real clock for fixed finite/cofinite rules.
* `exists_optimal_sharp_certificate`, `exists_optimal_realEta_certificate`: attained extrema.

## References

[ChenJiangZhu2027], Corollary 7.2 and Theorem 7.3 (PDF pp.24–25).
-/

public section
namespace Cslib.Logic.PL.SigmaRho.Signed
open Turing.MultiTapeTM Cslib.GenericRAM Cslib.Complexity
open IndependentDominationInterval.Signed

/-- Original selected-set feasibility, retaining both input cardinality bounds. -/
@[expose] def Feasible {n : ℕ} (G : SimpleGraph (Fin n)) (σ ρ : Set ℕ) (lo hi : ℤ)
    (S : Set (Fin n)) : Prop := G.IsSigmaRhoSet σ ρ S ∧ lo ≤ (Nat.card S : ℤ) ∧
    (Nat.card S : ℤ) ≤ hi

/-- Both returned optional values are attained/global extrema; absence means infeasibility. -/
@[expose] def Optimal {n : ℕ} (G : SimpleGraph (Fin n)) (σ ρ : Set ℕ) (lo hi : ℤ)
    (r : SigmaRho.Optimum.Result) : Prop :=
  (r.1 = none ↔ ¬ ∃ S, Feasible G σ ρ lo hi S) ∧
  (r.2 = none ↔ ¬ ∃ S, Feasible G σ ρ lo hi S) ∧
  (∀ k ∈ r.1, ∃ S, Feasible G σ ρ lo hi S ∧ Nat.card S = k ∧
    ∀ T, Feasible G σ ρ lo hi T → k ≤ Nat.card T) ∧
  (∀ k ∈ r.2, ∃ S, Feasible G σ ρ lo hi S ∧ Nat.card S = k ∧
    ∀ T, Feasible G σ ρ lo hi T → Nat.card T ≤ k)

/-- Normalizing a scalar interval preserves all absence, attainment and optimality clauses. -/
theorem optimal_iff {n : ℕ} (G : SimpleGraph (Fin n)) (σ ρ : Set ℕ) (lo hi : ℤ)
    (r : SigmaRho.Optimum.Result) :
    SigmaRho.Optimum.Optimal G σ ρ (lowerNat lo hi) (upperNat hi) r ↔
      Optimal G σ ρ lo hi r := by
  have hf (S : Set (Fin n)) : SigmaRho.Optimum.Feasible G σ ρ
      (lowerNat lo hi) (upperNat hi) S ↔ Feasible G σ ρ lo hi S :=
    and_congr_right fun _ => bounds_iff lo hi (Nat.card S)
  simp only [SigmaRho.Optimum.Optimal, Optimal, hf]

open Classical in
/-- The complete actual signed counter, with no supplied runtime or normalization contract. -/
theorem exists_count_sharp_certificate (D : ℕ) (hD : 1 ≤ D)
    (σ ρ : SimpleGraph.DegreeRule D) :
    ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℤ),
        count (ofGraph G lo hi) = Fintype.card {S : Set (Fin n) //
          G.IsSigmaRhoSet σ.counts ρ.counts S ∧
            lo ≤ (Nat.card S : ℤ) ∧ (Nat.card S : ℤ) ≤ hi} ∧
        cs.time (ofGraph G lo hi) ≤ C * ((encInput (ofGraph G lo hi)).length + 1) ^ e *
          2 ^ (A * Nat.logLogSqrtLogScale n) := by
  obtain ⟨counter, cp, C, e, A, hs, h⟩ :=
    SigmaRho.BinaryFrontend.exists_count_sharp_certificate D hD σ ρ true
  let pre := NativeCertificate.ofPolyTime normalize_polytime
  have hp := NativeCertificate.ofPolyTime_isPolynomial normalize_polytime
  let cs := cp.comp pre
  have hcsS := SparseCNFLeafCounter.polyBounded_comp_space cp pre
    (PolyBounded.of_forall_le C e hs) hp.2
  let W (x : Input) := pre.time x +
    C * ((SigmaRho.BinaryFrontend.encInput (normalize x)).length + 1) ^ e + cs.space x
  have hW : PolyBounded (fun x => (encInput x).length) W :=
    (hp.1.add ((PolyBounded.const C).mul
      ((normalize_polytime.polyBounded_length.add (.const 1)).pow e))).add hcsS
  obtain ⟨B, f, hBf⟩ := hW.exists_le
  refine ⟨counter ∘ normalize, cs, B, f, A,
    fun x => (Nat.le_add_left _ _).trans (hBf x), ?_⟩
  intro n G _ lo hi
  obtain ⟨hc, ht⟩ := h G (lowerNat lo hi) (upperNat hi)
  change counter (normalize (ofGraph G lo hi)) = _ at hc
  change cp.time (normalize (ofGraph G lo hi)) ≤ _ at ht
  constructor
  · change counter (normalize (ofGraph G lo hi)) = _
    rw [hc]
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro S
    exact and_congr_right fun _ => by
      simpa only [SigmaRho.BinaryFrontend.InBounds, forall_const] using
        bounds_iff lo hi (Nat.card S)
  · let x := ofGraph G lo hi
    let E := 2 ^ (A * Nat.logLogSqrtLogScale n)
    have hE : 0 < E := Nat.two_pow_pos _
    have ht' : cp.time (normalize x) ≤
        C * ((SigmaRho.BinaryFrontend.encInput (normalize x)).length + 1) ^ e * E := ht
    change pre.time x + cp.time (normalize x) ≤ _
    calc _ ≤ (pre.time x +
        C * ((SigmaRho.BinaryFrontend.encInput (normalize x)).length + 1) ^ e) * E := by
          have := Nat.le_mul_of_pos_right (pre.time x) hE
          nlinarith only [ht', this]
      _ ≤ W x * E := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
      _ ≤ _ := Nat.mul_le_mul_right _ (hBf x)

open Classical in
/-- Every fixed finite/cofinite rule pair has exact signed counts, source time and global space. -/
theorem exists_count_finiteCofinite_certificate (σ ρ : Set ℕ)
    (hσ : σ.Finite ∨ σᶜ.Finite) (hρ : ρ.Finite ∨ ρᶜ.Finite) :
    ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℤ),
        count (ofGraph G lo hi) = Fintype.card {S : Set (Fin n) //
          G.IsSigmaRhoSet σ ρ S ∧ lo ≤ (Nat.card S : ℤ) ∧ (Nat.card S : ℤ) ≤ hi} ∧
        (16 ≤ n → (cs.time (ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
          ((encInput (ofGraph G lo hi)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨D, hD, s, r, hs, hr⟩ := SimpleGraph.exists_degreeRules σ ρ hσ hρ
  obtain ⟨count, cs, C, e, A, hspace, h⟩ := exists_count_sharp_certificate D hD s r
  refine ⟨count, cs, C, e, 6 * A, hspace, ?_⟩
  intro n G _ lo hi
  refine ⟨by simpa only [hs, hr] using (h G lo hi).1, fun hn => ?_⟩
  have ht : (cs.time (ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
      ((encInput (ofGraph G lo hi)).length + 1 : ℕ) ^ e *
        (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast (h G lo hi).2
  exact ht.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A hn) (by positivity))

open Classical in
/-- The complete actual signed optimizer, with no supplied runtime or normalization contract. -/
theorem exists_optimal_sharp_certificate (σ ρ : Set ℕ)
    (hσ : σ.Finite ∨ σᶜ.Finite) (hρ : ρ.Finite ∨ ρᶜ.Finite) :
    ∃ optimal : Input → SigmaRho.Optimum.Result,
      ∃ cs : NativeCertificate optimal encInput SigmaRho.Optimum.encResult, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℤ),
        Optimal G σ ρ lo hi (optimal (ofGraph G lo hi)) ∧
        cs.time (ofGraph G lo hi) ≤ C * ((encInput (ofGraph G lo hi)).length + 1) ^ e *
          2 ^ (A * Nat.logLogSqrtLogScale n) := by
  obtain ⟨counter, cp, C, e, A, hs, h⟩ :=
    SigmaRho.Optimum.exists_optimal_sharp_certificate σ ρ hσ hρ
  let pre := NativeCertificate.ofPolyTime normalize_polytime
  have hp := NativeCertificate.ofPolyTime_isPolynomial normalize_polytime
  let cs := cp.comp pre
  have hcsS := SparseCNFLeafCounter.polyBounded_comp_space cp pre
    (PolyBounded.of_forall_le C e hs) hp.2
  let W (x : Input) := pre.time x +
    C * ((SigmaRho.BinaryFrontend.encInput (normalize x)).length + 1) ^ e + cs.space x
  have hW : PolyBounded (fun x => (encInput x).length) W :=
    (hp.1.add ((PolyBounded.const C).mul
      ((normalize_polytime.polyBounded_length.add (.const 1)).pow e))).add hcsS
  obtain ⟨B, f, hBf⟩ := hW.exists_le
  refine ⟨counter ∘ normalize, cs, B, f, A,
    fun x => (Nat.le_add_left _ _).trans (hBf x), ?_⟩
  intro n G _ lo hi
  obtain ⟨hc, ht⟩ := h G (lowerNat lo hi) (upperNat hi)
  change SigmaRho.Optimum.Optimal G σ ρ (lowerNat lo hi) (upperNat hi)
    (counter (normalize (ofGraph G lo hi))) at hc
  change cp.time (normalize (ofGraph G lo hi)) ≤ _ at ht
  constructor
  · exact (optimal_iff G σ ρ lo hi _).mp hc
  · let x := ofGraph G lo hi
    let E := 2 ^ (A * Nat.logLogSqrtLogScale n)
    have hE : 0 < E := Nat.two_pow_pos _
    have ht' : cp.time (normalize x) ≤
        C * ((SigmaRho.BinaryFrontend.encInput (normalize x)).length + 1) ^ e * E := ht
    change pre.time x + cp.time (normalize x) ≤ _
    calc _ ≤ (pre.time x +
        C * ((SigmaRho.BinaryFrontend.encInput (normalize x)).length + 1) ^ e) * E := by
          have := Nat.le_mul_of_pos_right (pre.time x) hE
          nlinarith only [ht', this]
      _ ≤ W x * E := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
      _ ≤ _ := Nat.mul_le_mul_right _ (hBf x)

open Classical in
/-- The actual original-set extrema have the source single-log-log clock and polynomial space. -/
theorem exists_optimal_realEta_certificate (σ ρ : Set ℕ)
    (hσ : σ.Finite ∨ σᶜ.Finite) (hρ : ρ.Finite ∨ ρᶜ.Finite) :
    ∃ optimal : Input → SigmaRho.Optimum.Result,
      ∃ cs : NativeCertificate optimal encInput SigmaRho.Optimum.encResult,
      ∃ C e A : ℕ,
        (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
        ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℤ),
          Optimal G σ ρ lo hi (optimal (ofGraph G lo hi)) ∧
          (16 ≤ n → (cs.time (ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
            ((encInput (ofGraph G lo hi)).length + 1 : ℕ) ^ e *
              (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨opt, cs, C, e, A, hs, h⟩ := exists_optimal_sharp_certificate σ ρ hσ hρ
  refine ⟨opt, cs, C, e, 6 * A, hs, ?_⟩
  intro n G _ lo hi
  refine ⟨(h G lo hi).1, fun hn => ?_⟩
  have ht : (cs.time (ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
      ((encInput (ofGraph G lo hi)).length + 1 : ℕ) ^ e *
        (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast (h G lo hi).2
  exact ht.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A hn) (by positivity))

end Cslib.Logic.PL.SigmaRho.Signed
