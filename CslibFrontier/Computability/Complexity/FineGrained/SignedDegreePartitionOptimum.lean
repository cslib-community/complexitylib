/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.SignedDegreePartition
public import CslibFrontier.Computability.Complexity.FineGrained.DegreePartitionOptimum
import CslibFrontier.Computability.PolyTime.CNF.SparseCNFLeafCounter

/-!
# Attained degree-partition extrema under signed binary intervals

Reuse the actual unsigned distribution and scans after binary signed normalization. Both extrema
retain the original vector, its count, attainment and comparison with every feasible partition.

## Main results

* `optimal_iff`: transport all attainment, absence and global optimality clauses.
* `exists_optimal_sharp_certificate`: composed native optimizer, sharp time and polynomial space.
* `exists_optimal_finiteCofinite_certificate`: fixed finite/cofinite rules with the real clock.

## References

[ChenJiangZhu2027], Theorem 7.3 and its optimization remark (PDF p.25).
-/

public section
namespace Cslib.Logic.PL.DegreePartition.Signed.Optimum
open Turing.MultiTapeTM Cslib.GenericRAM Cslib.Complexity

/-- Feasibility uses the original signed intervals, including negative or contradictory bounds. -/
@[expose] def Feasible {n q : ℕ} (G : SimpleGraph (Fin n))
    (M : Fin q → Fin q → Set ℕ) (lo hi : Fin q → ℤ) (S : Fin q → Set (Fin n)) : Prop :=
  G.IsDegreePartition M S ∧ ∀ j, lo j ≤ (Nat.card (S j) : ℤ) ∧ (Nat.card (S j) : ℤ) ≤ hi j

/-- A returned vector has its original multiplicity and an actual signed-feasible partition. -/
@[expose] def Attained {n q : ℕ} (G : SimpleGraph (Fin n))
    (M : Fin q → Fin q → Set ℕ) (lo hi : Fin q → ℤ) (e : Distribution.Entry) : Prop :=
  e.1.length = q ∧ e.2 = Distribution.countForVector G M e.1 ∧
    ∃ S, Feasible G M lo hi S ∧ ∀ j, Nat.card (S j) = e.1.getD j.val 0

/-- Absence is infeasibility; present entries attain global minimum and maximum class size. -/
@[expose] def Optimal {n q : ℕ} (G : SimpleGraph (Fin n))
    (M : Fin q → Fin q → Set ℕ) (lo hi : Fin q → ℤ) (i : Fin q)
    (r : DegreePartition.Optimum.Result) : Prop :=
  (r.1 = none ↔ ¬ ∃ S, Feasible G M lo hi S) ∧
  (r.2 = none ↔ ¬ ∃ S, Feasible G M lo hi S) ∧
  (∀ e ∈ r.1, Attained G M lo hi e ∧ ∀ S, Feasible G M lo hi S →
    DegreePartition.Optimum.coordinate i.val e ≤ Nat.card (S i)) ∧
  (∀ e ∈ r.2, Attained G M lo hi e ∧ ∀ S, Feasible G M lo hi S →
    Nat.card (S i) ≤ DegreePartition.Optimum.coordinate i.val e)

/-- Normalization transports attainment, optimality and empty/infeasible cases. -/
theorem optimal_iff {n q : ℕ} (G : SimpleGraph (Fin n)) (M : Fin q → Fin q → Set ℕ)
    (lo hi : Fin q → ℤ) (i : Fin q) (r : DegreePartition.Optimum.Result) :
    DegreePartition.Optimum.Optimal G M
      (fun j => (SignedClassBounds.pair (lo j, hi j)).1)
      (fun j => (SignedClassBounds.pair (lo j, hi j)).2) i r ↔ Optimal G M lo hi i r := by
  have hf (S : Fin q → Set (Fin n)) :
      DegreePartition.Optimum.Feasible G M
        (fun j => (SignedClassBounds.pair (lo j, hi j)).1)
        (fun j => (SignedClassBounds.pair (lo j, hi j)).2) S ↔ Feasible G M lo hi S :=
    and_congr_right fun _ => SignedClassBounds.bounds_iff lo hi (fun j => Nat.card (S j))
  simp only [DegreePartition.Optimum.Optimal, Optimal, DegreePartition.Optimum.Attained,
    Attained, hf]

open Classical in
/-- The complete actual signed optimizer, with no supplied runtime or normalization contract. -/
theorem exists_optimal_sharp_certificate (q D : ℕ) (hD : 1 ≤ D)
    (M : Fin q → Fin q → SimpleGraph.DegreeRule D) (i : Fin q) :
    ∃ optimal : Input → DegreePartition.Optimum.Result,
      ∃ cs : NativeCertificate optimal encInput DegreePartition.Optimum.encResult, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : Fin q → ℤ),
        Optimal G (fun j k => (M j k).counts) lo hi i (optimal (ofGraph G lo hi)) ∧
        cs.time (ofGraph G lo hi) ≤ C * ((encInput (ofGraph G lo hi)).length + 1) ^ e *
          2 ^ (A * Nat.logLogSqrtLogScale n) := by
  obtain ⟨counter, cp, C, e, A, hs, h⟩ :=
    DegreePartition.Optimum.exists_optimal_sharp_certificate q D hD M i
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
  · exact (optimal_iff G _ lo hi i _).mp hc
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
/-- Fixed finite/cofinite rules, arbitrary signed input intervals, attained original extrema and
source real eta time with global polynomial workspace. Empty graphs are included. -/
theorem exists_optimal_finiteCofinite_certificate {q : ℕ} (M : Fin q → Fin q → Set ℕ)
    (hM : ∀ i j, (M i j).Finite ∨ (M i j)ᶜ.Finite) (i : Fin q) :
    ∃ optimal : Input → DegreePartition.Optimum.Result,
      ∃ cs : NativeCertificate optimal encInput DegreePartition.Optimum.encResult, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : Fin q → ℤ),
        Optimal G M lo hi i (optimal (ofGraph G lo hi)) ∧
        (16 ≤ n → (cs.time (ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
          ((encInput (ofGraph G lo hi)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨D, hD, R, hR⟩ := SimpleGraph.exists_degreeMatrixRules M hM
  obtain ⟨optimal, cs, C, e, A, hs, h⟩ := exists_optimal_sharp_certificate q D hD R i
  refine ⟨optimal, cs, C, e, 6 * A, hs, ?_⟩
  intro n G _ lo hi
  refine ⟨by simpa only [hR] using (h G lo hi).1, fun hn => ?_⟩
  have ht : (cs.time (ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
      ((encInput (ofGraph G lo hi)).length + 1 : ℕ) ^ e *
        (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast (h G lo hi).2
  exact ht.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A hn) (by positivity))

end Cslib.Logic.PL.DegreePartition.Signed.Optimum
