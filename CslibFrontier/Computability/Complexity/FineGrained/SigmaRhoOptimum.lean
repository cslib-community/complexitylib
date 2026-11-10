/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.DegreePartitionOptimum
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.SigmaRhoPartition
public import CslibFrontier.Computability.PolyTime.CNF.SigmaRhoInput
import CslibFrontier.Computability.PolyTime.CNF.SparseCNFLeafCounter

/-!
# Native extrema for general finite/cofinite degree-rule sets

Selected class zero and its complementary class one realize the general degree-rule problem as
an actual fixed two-label matrix. Input bounds on the selected cardinality remain binary; the
complementary class receives the computed interval zero through the original declaration.
The native labeled-partition extrema are followed by actual optional scalar reconstruction.
Source: [ChenJiangZhu2027], Corollary 7.2 and the optimization clause after Theorem 7.3 (PDF p.25).

## Main definitions

* `prepare`: actual bounded two-class instance, sharing the original vertices.
* `values`: reconstruct optional minimum and maximum vertex cardinalities.
* `Optimal`: attained global optimum values and precise infeasibility tags.

## Main results

* `prepare_polytime`, `values_polytime`: actual binary input/output transformations.
* `transport_optimal`: partition extrema are exactly original-set extrema.
* `exists_optimal_sharp_certificate`, `exists_optimal_realEta_certificate`: complete native
  sharp time and global polynomial workspace for all fixed finite/cofinite rules.
-/

public section

namespace Cslib.Logic.PL.SigmaRho.Optimum

open Turing.MultiTapeTM Cslib.GenericRAM Cslib.Complexity BinaryFrontend

/-- Optional minimum vertex cardinality followed by optional maximum cardinality. -/
abbrev Result := Option ℕ × Option ℕ
/-- Both optional binary values retain independent absence tags, the first option is framed. -/
abbrev encResult : Result ↪ List Bool := encPair (encOption encNat) (encOption encNat)
/-- Actual original graph and selected interval, with computed unrestricted complement bounds. -/
@[expose] def prepare (x : Input) : DegreePartition.Bounded.BinaryFrontend.Input :=
  (original x, [(lower x, upper x), (0, IndependentDomination.order (original x))])
/-- Drop vector/count metadata only after computing both attained native extrema. -/
@[expose] def values (r : DegreePartition.Optimum.Result) : Result :=
  (r.1.map (DegreePartition.Optimum.coordinate 0),
    r.2.map (DegreePartition.Optimum.coordinate 0))

/-- The computed complement interval charges the unary declaration's binary conversion. -/
theorem prepare_polytime : ComputableInPolyTime prepare encInput
    DegreePartition.Bounded.BinaryFrontend.encInput := by
  have hg : ComputableInPolyTime original encInput IndependentDomination.encInput := by
    unfold original encInput IndependentDominationInterval.graph
      IndependentDominationInterval.encInput
    fun_prop
  have hn : ComputableInPolyTime (fun x => IndependentDomination.order (original x))
      encInput encUnary := by
    have ho : ComputableInPolyTime IndependentDomination.order
        IndependentDomination.encInput encUnary := by
      unfold IndependentDomination.order IndependentDomination.encInput
      fun_prop
    exact ho.comp hg
  have hl : ComputableInPolyTime lower encInput encNat := by
    unfold lower encInput IndependentDominationInterval.lower IndependentDominationInterval.encInput
    fun_prop
  have hh : ComputableInPolyTime upper encInput encNat := by
    unfold upper encInput IndependentDominationInterval.upper IndependentDominationInterval.encInput
    fun_prop
  exact hg.prod (ComputableInPolyTime.cons' (hl.prod hh)
    (ComputableInPolyTime.cons' ((ComputableInPolyTime.const 0).prod
      (ComputableInPolyTime.unary_to_binary.comp hn)) (.const [])))

/-- Both option tags and binary values are written by the actual reconstruction machine. -/
theorem values_polytime : ComputableInPolyTime values DegreePartition.Optimum.encResult
    encResult := by
  have hc : ComputableInPolyTime (DegreePartition.Optimum.coordinate 0)
      DegreePartition.Distribution.encEntry encNat := by
    unfold DegreePartition.Optimum.coordinate DegreePartition.Distribution.encEntry
    fun_prop
  exact (ComputableInPolyTime.optionMapWithInput (ComputableInPolyTime.fst _ _)
    (hc.comp (ComputableInPolyTime.snd _ _))).prod
      (ComputableInPolyTime.optionMapWithInput (ComputableInPolyTime.snd _ _)
        (hc.comp (ComputableInPolyTime.snd _ _)))

/-- Only the selected class receives the input lower bound. -/
@[expose] def classLower (lo : ℕ) (i : Fin 2) : ℕ := if i = 0 then lo else 0
/-- The complementary class is bounded by the original vertex declaration. -/
@[expose] def classUpper (n hi : ℕ) (i : Fin 2) : ℕ := if i = 0 then hi else n

private theorem prepare_ofGraph {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (lo hi : ℕ) : prepare (ofGraph G lo hi) = DegreePartition.Bounded.BinaryFrontend.ofGraph G
      (classLower lo) (classUpper n hi) := rfl

/-- Original selected-set feasibility, retaining both input cardinality bounds. -/
@[expose] def Feasible {n : ℕ} (G : SimpleGraph (Fin n)) (σ ρ : Set ℕ) (lo hi : ℕ)
    (S : Set (Fin n)) : Prop := G.IsSigmaRhoSet σ ρ S ∧ lo ≤ Nat.card S ∧ Nat.card S ≤ hi

/-- Both returned optional values are attained/global extrema; absence means infeasibility. -/
@[expose] def Optimal {n : ℕ} (G : SimpleGraph (Fin n)) (σ ρ : Set ℕ) (lo hi : ℕ)
    (r : Result) : Prop :=
  (r.1 = none ↔ ¬ ∃ S, Feasible G σ ρ lo hi S) ∧
  (r.2 = none ↔ ¬ ∃ S, Feasible G σ ρ lo hi S) ∧
  (∀ k ∈ r.1, ∃ S, Feasible G σ ρ lo hi S ∧ Nat.card S = k ∧
    ∀ T, Feasible G σ ρ lo hi T → k ≤ Nat.card T) ∧
  (∀ k ∈ r.2, ∃ S, Feasible G σ ρ lo hi S ∧ Nat.card S = k ∧
    ∀ T, Feasible G σ ρ lo hi T → Nat.card T ≤ k)

private theorem project_feasible {n : ℕ} {G : SimpleGraph (Fin n)} {σ ρ : Set ℕ}
    {lo hi : ℕ} {S : Fin 2 → Set (Fin n)}
    (h : DegreePartition.Optimum.Feasible G (SimpleGraph.sigmaRhoMatrix σ ρ)
      (classLower lo) (classUpper n hi) S) : Feasible G σ ρ lo hi (S 0) :=
  ⟨h.1.isSigmaRhoSet, (h.2 0).1, (h.2 0).2⟩

open Classical in
private theorem lift_feasible {n : ℕ} {G : SimpleGraph (Fin n)} {σ ρ : Set ℕ}
    {lo hi : ℕ} {S : Set (Fin n)} (h : Feasible G σ ρ lo hi S) :
    DegreePartition.Optimum.Feasible G (SimpleGraph.sigmaRhoMatrix σ ρ)
      (classLower lo) (classUpper n hi) (SimpleGraph.selectedPartition S) := by
  refine ⟨G.isDegreePartition_selectedPartition σ ρ S h.1, ?_⟩
  intro i
  fin_cases i
  · exact h.2
  · have hc : Nat.card (Sᶜ : Set (Fin n)) ≤ n := by
      rw [Nat.card_eq_fintype_card]
      exact (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin n)
    exact ⟨Nat.zero_le _, hc⟩

open Classical in
/-- Every returned scalar is the attained original-set extremum, with no partition advice. -/
theorem transport_optimal {n : ℕ} (G : SimpleGraph (Fin n)) (σ ρ : Set ℕ) (lo hi : ℕ)
    (r : DegreePartition.Optimum.Result)
    (h : DegreePartition.Optimum.Optimal G (SimpleGraph.sigmaRhoMatrix σ ρ)
      (classLower lo) (classUpper n hi) 0 r) : Optimal G σ ρ lo hi (values r) := by
  have hf : (∃ S, DegreePartition.Optimum.Feasible G (SimpleGraph.sigmaRhoMatrix σ ρ)
      (classLower lo) (classUpper n hi) S) ↔ ∃ S, Feasible G σ ρ lo hi S :=
    ⟨fun ⟨S, hS⟩ => ⟨S 0, project_feasible hS⟩,
      fun ⟨S, hS⟩ => ⟨SimpleGraph.selectedPartition S, lift_feasible hS⟩⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [values, Option.map_eq_none_iff, hf] using h.1
  · simpa only [values, Option.map_eq_none_iff, hf] using h.2.1
  · intro k hk
    obtain ⟨e, he, rfl⟩ := Option.mem_map.mp hk
    obtain ⟨⟨_, _, S, hS, hsize⟩, hmin⟩ := h.2.2.1 e he
    refine ⟨S 0, project_feasible hS, hsize 0, ?_⟩
    intro T hT
    exact hmin _ (lift_feasible hT)
  · intro k hk
    obtain ⟨e, he, rfl⟩ := Option.mem_map.mp hk
    obtain ⟨⟨_, _, S, hS, hsize⟩, hmax⟩ := h.2.2.2 e he
    refine ⟨S 0, project_feasible hS, hsize 0, ?_⟩
    intro T hT
    exact hmax _ (lift_feasible hT)

open Classical in
/-- General finite/cofinite rules admit an actual attained minimum/maximum value machine,
including both input binary bounds, the sharp rounded clock and global polynomial workspace. -/
theorem exists_optimal_sharp_certificate (σ ρ : Set ℕ)
    (hσ : σ.Finite ∨ σᶜ.Finite) (hρ : ρ.Finite ∨ ρᶜ.Finite) :
    ∃ optimal : Input → Result, ∃ cs : NativeCertificate optimal encInput encResult,
      ∃ C e A : ℕ,
        (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
        ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℕ),
          Optimal G σ ρ lo hi (optimal (ofGraph G lo hi)) ∧
          cs.time (ofGraph G lo hi) ≤ C * ((encInput (ofGraph G lo hi)).length + 1) ^ e *
            2 ^ (A * Nat.logLogSqrtLogScale n) := by
  have hm : ∀ i j, (SimpleGraph.sigmaRhoMatrix σ ρ i j).Finite ∨
      (SimpleGraph.sigmaRhoMatrix σ ρ i j)ᶜ.Finite := by
    intro i j
    by_cases hj : j = 0
    · by_cases hi : i = 0
      · simpa only [SimpleGraph.sigmaRhoMatrix, hj, hi, ↓reduceIte] using hσ
      · simpa only [SimpleGraph.sigmaRhoMatrix, hj, hi, ↓reduceIte] using hρ
    · simp [SimpleGraph.sigmaRhoMatrix, hj]
  obtain ⟨D, hD, M, hM⟩ := SimpleGraph.exists_degreeMatrixRules _ hm
  obtain ⟨opt, cp, C, e, A, hs, h⟩ :=
    DegreePartition.Optimum.exists_optimal_sharp_certificate 2 D hD M 0
  let pre := NativeCertificate.ofPolyTime prepare_polytime
  have hp := NativeCertificate.ofPolyTime_isPolynomial prepare_polytime
  let base := cp.comp pre
  have hbS := SparseCNFLeafCounter.polyBounded_comp_space cp pre
    (PolyBounded.of_forall_le C e hs) hp.2
  have hlen := SparseCNFLeafCounter.polyBounded_output_of_space base hbS
  let post := NativeCertificate.ofPolyTime values_polytime
  have hpost := NativeCertificate.ofPolyTime_isPolynomial values_polytime
  let cs := post.comp base
  have hcsS := SparseCNFLeafCounter.polyBounded_comp_space post base hpost.2 hbS
  let W (x : Input) := pre.time x +
    C * ((DegreePartition.Bounded.BinaryFrontend.encInput (prepare x)).length + 1) ^ e +
    post.time (opt (prepare x)) + cs.space x
  have hW : PolyBounded (fun x => (encInput x).length) W :=
    ((hp.1.add ((PolyBounded.const C).mul
      ((prepare_polytime.polyBounded_length.add (.const 1)).pow e))).add
        (hpost.1.comp hlen)).add hcsS
  obtain ⟨B, f, hBf⟩ := hW.exists_le
  refine ⟨(fun x => values (opt (prepare x))), cs, B, f, A,
    fun x => (show cs.space x ≤ W x from Nat.le_add_left _ _).trans (hBf x), ?_⟩
  intro n G _ lo hi
  obtain ⟨hc, ht⟩ := h G (classLower lo) (classUpper n hi)
  rw [← prepare_ofGraph] at hc ht
  constructor
  · apply transport_optimal
    simpa only [hM] using hc
  · let x := ofGraph G lo hi
    let E := 2 ^ (A * Nat.logLogSqrtLogScale n)
    have hE : 0 < E := Nat.two_pow_pos _
    have ht' : cp.time (prepare x) ≤
        C * ((DegreePartition.Bounded.BinaryFrontend.encInput (prepare x)).length + 1) ^ e * E := ht
    have hrest := Nat.le_mul_of_pos_right
      (pre.time x + post.time (opt (prepare x))) hE
    change pre.time x + cp.time (prepare x) + post.time (opt (prepare x)) ≤ _
    calc _ ≤ (pre.time x +
        C * ((DegreePartition.Bounded.BinaryFrontend.encInput (prepare x)).length + 1) ^ e +
          post.time (opt (prepare x))) * E := by nlinarith only [ht', hrest]
      _ ≤ W x * E := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
      _ ≤ _ := Nat.mul_le_mul_right _ (hBf x)

open Classical in
/-- The actual original-set extrema have the source single-log-log clock and polynomial space. -/
theorem exists_optimal_realEta_certificate (σ ρ : Set ℕ)
    (hσ : σ.Finite ∨ σᶜ.Finite) (hρ : ρ.Finite ∨ ρᶜ.Finite) :
    ∃ optimal : Input → Result, ∃ cs : NativeCertificate optimal encInput encResult,
      ∃ C e A : ℕ,
        (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
        ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℕ),
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

end Cslib.Logic.PL.SigmaRho.Optimum
