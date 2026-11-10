/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.BoundedDegreePartitionCountingResources
public import CslibFrontier.Computability.PolyTime.CNF.PartitionSizeVectors
import all CslibFrontier.Computability.PolyTime.CNF.SparseCNFLeafCounter
import Mathlib.Data.List.GetD

/-!
# Complete labeled-partition size-vector output

The executable fixed-q grid has (v+1)^q entries. Each output explicitly contains its ordered
class-size vector and the original labeled-partition count. Sequential counter calls, repeated
grid lookup, accumulation, reversal and all binary output writes are charged. Source:
[ChenJiangZhu2027], Theorem 7.3 / Appendix C.2, PDF pp.25,32.
## Main results

* `exists_distribution_finiteCofinite_certificate`: tagged output and complete native resources.
* `output_encoding_bound`: independent explicit framed output length, including every vector tag.
* `rounds_le_input_power`: the fixed-label-count polynomial number of actual coefficient calls.

-/

public section

namespace Cslib.Logic.PL.DegreePartition.Distribution

open Turing.MultiTapeTM Cslib.GenericRAM Cslib.Complexity

/-- Original graph and unary position within the fixed-q polynomial grid. -/
abbrev Case := IndependentDomination.Input × ℕ
/-- Retained original graph of one vector request. -/
@[expose] def graph (p : Case) : IndependentDomination.Input := p.1
/-- Actual grid index, with no supplied output vector. -/
@[expose] def index (p : Case) : ℕ := p.2
/-- Binary coefficient requests retain a unary bounded traversal index internally. -/
@[expose] def encCase : Case ↪ List Bool := encPair IndependentDomination.encInput encUnary
/-- Compute the actual grid and select its vector; raw out-of-range requests fall back to zeros. -/
@[expose] def vectorAt (q : ℕ) (p : Case) : List ℕ :=
  (SizeVectors.vectors q (IndependentDomination.order (graph p))).getD
    (index p) (List.replicate q 0)
/-- Runtime equality tests for all original class sizes. -/
@[expose] def caseInput (q : ℕ) (p : Case) : Bounded.BinaryFrontend.Input :=
  (graph p, (vectorAt q p).map fun k => (k, k))
/-- An output entry includes every original class label's size, followed by its binary count. -/
abbrev Entry := List ℕ × ℕ
/-- Full framing of an explicit size vector and coefficient. -/
@[expose] def encEntry : Entry ↪ List Bool := encPair (encList encNat) encNat
/-- Actually construct the vector tag, rather than merely promising a coefficient order. -/
@[expose] def attach (q : ℕ) (p : Case × ℕ) : Entry := (vectorAt q p.1, p.2)
/-- Actual complete coefficient request/output, using the original-input bounded counter. -/
@[expose] def coefficient (q : ℕ) (counter : Bounded.BinaryFrontend.Input → ℕ) (p : Case) : Entry :=
  attach q (p, counter (caseInput q p))

private theorem vectorAt_polytime (q : ℕ) : ComputableInPolyTime (vectorAt q) encCase
    (encList encNat) := by
  have hn : ComputableInPolyTime (fun p : Case => IndependentDomination.order (graph p))
      encCase encUnary := by
    unfold graph encCase IndependentDomination.order IndependentDomination.encInput
    fun_prop
  exact ComputableInPolyTime.listGetDWithInput ((SizeVectors.vectors_polytime q).comp hn)
    (by unfold index encCase; fun_prop) (List.replicate q 0)

private theorem caseInput_polytime (q : ℕ) : ComputableInPolyTime (caseInput q) encCase
    Bounded.BinaryFrontend.encInput := by
  have hv := vectorAt_polytime q
  have hg : ComputableInPolyTime graph encCase IndependentDomination.encInput := by
    unfold graph encCase; fun_prop
  unfold caseInput Bounded.BinaryFrontend.encInput
  exact hg.prod ((ComputableInPolyTime.map (show ComputableInPolyTime
    (fun k : ℕ => (k, k)) encNat (encPair encNat encNat) from by fun_prop)).comp hv)

private theorem attach_polytime (q : ℕ) : ComputableInPolyTime (attach q) (encPair encCase encNat)
    encEntry := by
  unfold attach encEntry
  exact ((vectorAt_polytime q).comp (ComputableInPolyTime.fst _ _)).prod
    (ComputableInPolyTime.snd _ _)

/-- Every actual or fallback vector has exactly the source class count and bounded coordinates. -/
theorem vectorAt_mem (q : ℕ) (p : Case) :
    vectorAt q p ∈ SizeVectors.vectors q (IndependentDomination.order (graph p)) := by
  unfold vectorAt
  by_cases h : index p < (SizeVectors.vectors q (IndependentDomination.order (graph p))).length
  · rw [List.getD_eq_getElem _ _ h]
    exact List.getElem_mem _
  · rw [List.getD_eq_default _ _ (by omega)]
    apply (SizeVectors.mem_vectors _ _ _).mpr
    simp

private theorem ofFn_getD {q : ℕ} (v : List ℕ) (hv : v.length = q) :
    List.ofFn (fun i : Fin q => v.getD i.val 0) = v := by
  subst q
  have h : (fun i : Fin v.length => v.getD i.val 0) = (fun i : Fin v.length => v[i.val]) := by
    funext i
    exact List.getD_eq_getElem v 0 i.isLt
  rw [h]
  exact List.ofFn_getElem

/-- The requested binary interval list is exactly the canonical original-input equality vector. -/
theorem caseInput_ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (q j : ℕ) :
    caseInput q (IndependentDomination.ofGraph G, j) = Bounded.BinaryFrontend.ofGraph G
      (fun i : Fin q => (vectorAt q (IndependentDomination.ofGraph G, j)).getD i.val 0)
      (fun i : Fin q => (vectorAt q (IndependentDomination.ofGraph G, j)).getD i.val 0) := by
  have hv := ((SizeVectors.mem_vectors _ _ _).mp
    (vectorAt_mem q (IndependentDomination.ofGraph G, j))).1
  simp only [caseInput, graph, Bounded.BinaryFrontend.ofGraph]
  congr 1
  calc
    _ = (List.ofFn (fun i : Fin q =>
        (vectorAt q (IndependentDomination.ofGraph G, j)).getD i.val 0)).map
          (fun k => (k, k)) :=
      congrArg (List.map (fun k => (k, k))) (ofFn_getD _ hv).symm
    _ = _ := by simp only [List.map_ofFn, Function.comp_def]

/-- Conventional coefficient of an explicitly labeled original size vector. -/
@[expose] noncomputable def countForVector {n q : ℕ} (G : SimpleGraph (Fin n))
    (M : Fin q → Fin q → Set ℕ) (v : List ℕ) : ℕ :=
  Nat.card {S : Fin q → Set (Fin n) // G.IsDegreePartition M S ∧
    ∀ i, Nat.card (S i) = v.getD i.val 0}

open Classical in
/-- Equality intervals impose exactly the intended original size vector, including zeros. -/
theorem coefficient_count {n q D : ℕ} (G : SimpleGraph (Fin n))
    (M : Fin q → Fin q → SimpleGraph.DegreeRule D) (v : List ℕ) :
    Fintype.card {S : Fin q → Set (Fin n) // G.IsDegreePartition (fun i j => (M i j).counts) S ∧
      SimpleGraph.InClassBounds (fun i => v.getD i.val 0) (fun i => v.getD i.val 0) S} =
      countForVector G (fun i j => (M i j).counts) v := by
  rw [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro S
  apply and_congr Iff.rfl
  apply forall_congr'
  intro i
  change (v.getD i.val 0 ≤ Nat.card (S i) ∧ Nat.card (S i) ≤ v.getD i.val 0) ↔ _
  omega

open Classical in
/-- A coefficient counts at most all class-membership arrays, a linear-bit bound for fixed q. -/
theorem coefficient_le_two_pow {n q : ℕ} (G : SimpleGraph (Fin n))
    (M : Fin q → Fin q → Set ℕ) (v : List ℕ) : countForVector G M v ≤ 2 ^ (n * q) := by
  unfold countForVector
  rw [Nat.card_eq_fintype_card]
  calc
    _ ≤ Fintype.card (Fin q → Set (Fin n)) := Fintype.card_subtype_le _
    _ = _ := by simp [← pow_mul]

/-- Actual framed vector bits are polynomial in v, even though every label is retained. -/
theorem vector_bits_le {q n : ℕ} (v : List ℕ) (hv : v ∈ SizeVectors.vectors q n) :
    ((encList encNat) v).length ≤ q * (2 * (n + 1) + 1) := by
  obtain ⟨hl, hb⟩ := (SizeVectors.mem_vectors q n v).mp hv
  have h := length_encList_le encNat v (b := n + 1) (by
    intro k hk
    rw [encNat_apply, Nat.size_eq_bits_len]
    exact (Nat.size_le_self k).trans (by have := hb k hk; omega))
  simpa only [hl] using h

/-- Complete output-entry bit bound, separate from its actual runtime proof. -/
theorem entry_bits_le {n q : ℕ} (G : SimpleGraph (Fin n))
    (M : Fin q → Fin q → Set ℕ) (v : List ℕ) (hv : v ∈ SizeVectors.vectors q n) :
    (encEntry (v, countForVector G M v)).length ≤
      2 * q * (2 * (n + 1) + 1) + n * q + 2 := by
  have hb : (encNat (countForVector G M v)).length ≤ n * q + 1 := by
    have h := Nat.size_le_size (coefficient_le_two_pow G M v)
    simpa only [encNat_apply, Nat.size_eq_bits_len, Nat.size_pow] using h
  have hvB := vector_bits_le v hv
  simp only [encEntry, length_encPair]
  nlinarith

/-- Original matrix, unary next index and reverse-ordered explicit output entries. -/
abbrev State := IndependentDomination.Input × ℕ × List Entry
/-- Retained original graph. -/
@[expose] def original (s : State) : IndependentDomination.Input := s.1
/-- Next grid position. -/
@[expose] def next : State → ℕ | (_, j, _) => j
/-- All accumulated vector tags and binary coefficients, newest first. -/
@[expose] def stored : State → List Entry | (_, _, xs) => xs
/-- Full live-state framing includes the actual output vector tags. -/
@[expose] def encState : State ↪ List Bool :=
  encPair IndependentDomination.encInput (encPair encUnary (encList encEntry))
/-- One original-input coefficient request, excluding the accumulated output. -/
@[expose] def request (s : State) : Case := (original s, next s)
/-- Retain the actual vector/count pair and advance. -/
@[expose] def finish (p : State × Entry) : State :=
  (original p.1, next p.1 + 1, p.2 :: stored p.1)
/-- One actual original-input count and explicit tagged output append. -/
@[expose] def step (q : ℕ) (counter : Bounded.BinaryFrontend.Input → ℕ) (s : State) : State :=
  finish (s, coefficient q counter (request s))
/-- Initial original input and empty output. -/
@[expose] def initial (g : IndependentDomination.Input) : State := (g, 0, [])
/-- Exactly the computed grid length; q is fixed, never part of the runtime input. -/
@[expose] def rounds (q : ℕ) (g : IndependentDomination.Input) : ℕ :=
  (SizeVectors.vectors q (IndependentDomination.order g)).length
/-- Emit the accumulated tagged counts in the exact grid order. -/
@[expose] def output (s : State) : List Entry := (stored s).reverse
/-- Complete actual size-vector distribution algorithm. -/
@[expose] def run (q : ℕ) (counter : Bounded.BinaryFrontend.Input → ℕ)
    (g : IndependentDomination.Input) : List Entry :=
  output ((step q counter)^[rounds q g] (initial g))

private theorem trajectory (q : ℕ) (counter : Bounded.BinaryFrontend.Input → ℕ)
    (g : IndependentDomination.Input) (j : ℕ) :
    (step q counter)^[j] (initial g) =
      (g, j, ((List.range j).map fun k => coefficient q counter (g, k)).reverse) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [step, finish, request, original, next, stored, List.range_succ]

/-- Every emitted position contains its actual computed vector and count in traversal order. -/
theorem run_eq_map (q : ℕ) (counter : Bounded.BinaryFrontend.Input → ℕ)
    (g : IndependentDomination.Input) : run q counter g =
      (List.range (rounds q g)).map fun k => coefficient q counter (g, k) := by
  rw [run, trajectory]
  exact List.reverse_reverse _

private theorem request_polytime : ComputableInPolyTime request encState encCase := by
  unfold request original next encState encCase; fun_prop

private theorem finish_polytime : ComputableInPolyTime finish (encPair encState encEntry)
    encState := by unfold finish original next stored encState; fun_prop

private theorem initial_polytime : ComputableInPolyTime initial IndependentDomination.encInput
    encState := by unfold initial encState; fun_prop

private theorem rounds_unary_polytime (q : ℕ) : ComputableInPolyTime (rounds q)
    IndependentDomination.encInput encUnary := by
  have hn : ComputableInPolyTime IndependentDomination.order IndependentDomination.encInput
      encUnary := by unfold IndependentDomination.order IndependentDomination.encInput; fun_prop
  exact (ComputableInPolyTime.length_list (encList encNat)).comp
    ((SizeVectors.vectors_polytime q).comp hn)

private theorem rounds_polytime (q : ℕ) : ComputableInPolyTime (rounds q)
    IndependentDomination.encInput encNat :=
  ComputableInPolyTime.unary_to_binary.comp (rounds_unary_polytime q)

private theorem output_polytime : ComputableInPolyTime output encState (encList encEntry) := by
  have hs : ComputableInPolyTime stored encState (encList encEntry) := by
    unfold stored encState; fun_prop
  exact .of_tidy ((ComputableTidilyInPolyTime.listReverse encEntry).comp hs.tidy)

private theorem case_length_le (q : ℕ) (g : IndependentDomination.Input) {j : ℕ}
    (hj : j ≤ rounds q g) : (encCase (g, j)).length ≤
      2 * (IndependentDomination.encInput g).length + rounds q g + 1 := by
  simp only [encCase, length_encPair, encUnary_apply, List.length_replicate]
  omega

private theorem trajectory_length (q : ℕ) (counter : Bounded.BinaryFrontend.Input → ℕ)
    (g : IndependentDomination.Input) {j V : ℕ} (hj : j ≤ rounds q g)
    (hV : ∀ k ≤ rounds q g, (encEntry (coefficient q counter (g, k))).length ≤ V) :
    (encState ((step q counter)^[j] (initial g))).length ≤
      2 * (IndependentDomination.encInput g).length + 2 * rounds q g + 2 +
        rounds q g * (2 * V + 1) := by
  rw [trajectory]
  simp only [encState, length_encPair, encUnary_apply, List.length_replicate,
    length_encList_reverse]
  have hl := length_encList_le encEntry
    ((List.range j).map fun k => coefficient q counter (g, k)) (b := V) (by
      intro c hc
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
      exact hV k (by have := List.mem_range.mp hk; omega))
  simp only [List.length_map, List.length_range] at hl
  have hm := Nat.mul_le_mul_right (2 * V + 1) hj
  omega

/-- The actual round count exposes its dependence on the fixed label count. -/
theorem rounds_eq (q : ℕ) (g : IndependentDomination.Input) :
    rounds q g = (IndependentDomination.order g + 1) ^ q := SizeVectors.length_vectors _ _

/-- All and only the generated vectors are visited, in their exact declared class order. -/
theorem map_vectorAt_range (q : ℕ) (g : IndependentDomination.Input) :
    (List.range (rounds q g)).map (fun j => vectorAt q (g, j)) =
      SizeVectors.vectors q (IndependentDomination.order g) := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, rounds]
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range, vectorAt, graph, index]
    exact List.getD_eq_getElem _ _ hj

open Classical in
/-- The complete actual ordered size distribution has sharp original-vertex time and global
polynomial workspace. All sequential count calls, accumulation, reversal, intermediate integer
encodings and output writes are charged. No counter contract or output/runtime advice is input. -/
theorem exists_distribution_sharp_certificate (q D : ℕ) (hD : 1 ≤ D)
    (M : Fin q → Fin q → SimpleGraph.DegreeRule D) :
    ∃ distribution : IndependentDomination.Input → List Entry,
      ∃ cs : NativeCertificate distribution IndependentDomination.encInput (encList encEntry),
        ∃ C e A : ℕ,
          (∀ g, cs.space g ≤ C * ((IndependentDomination.encInput g).length + 1) ^ e) ∧
          ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
            distribution (IndependentDomination.ofGraph G) =
              (SizeVectors.vectors q n).map (fun v =>
                (v, countForVector G (fun i j => (M i j).counts) v)) ∧
            cs.time (IndependentDomination.ofGraph G) ≤ C *
              ((IndependentDomination.encInput (IndependentDomination.ofGraph G)).length + 1) ^ e *
                2 ^ (A * Nat.logLogSqrtLogScale n) := by
  obtain ⟨counter, cp, pC, f, A, hs, ht⟩ :=
    Bounded.BinaryFrontend.exists_count_sharp_certificate q D hD M
  let cq := NativeCertificate.ofPolyTime (caseInput_polytime q)
  have hq := NativeCertificate.ofPolyTime_isPolynomial (caseInput_polytime q)
  let ccount := cp.comp cq
  have hcountS := SparseCNFLeafCounter.polyBounded_comp_space cp cq
    (PolyBounded.of_forall_le pC f hs) hq.2
  let caseId : NativeCertificate (fun p : Case => p) encCase encCase :=
    NativeCertificate.linear (ComputableInO.of_eq fun _ => rfl)
  let casePair := caseId.prod ccount
  have hcasePairS : PolyBounded (fun p => (encCase p).length) casePair.space :=
    PolyBounded.self.add hcountS
  have hcasePairL := SparseCNFLeafCounter.polyBounded_output_of_space casePair hcasePairS
  let tag := NativeCertificate.ofPolyTime (attach_polytime q)
  have htag := NativeCertificate.ofPolyTime_isPolynomial (attach_polytime q)
  let cc : NativeCertificate (coefficient q counter) encCase encEntry :=
    (tag.comp casePair).congr fun _ => rfl
  have hccS := SparseCNFLeafCounter.polyBounded_comp_space tag casePair htag.2 hcasePairS
  have hccL := SparseCNFLeafCounter.polyBounded_output_of_space cc hccS
  have hN : PolyBounded (fun g => (IndependentDomination.encInput g).length) (rounds q) := by
    simpa only [encUnary_apply, List.length_replicate] using
      (rounds_unary_polytime q).polyBounded_length
  obtain ⟨cL, eL, hL⟩ := hccL.exists_le
  let J (g : IndependentDomination.Input) :=
    2 * (IndependentDomination.encInput g).length + rounds q g + 1
  let V (g : IndependentDomination.Input) := cL * (J g + 1) ^ eL
  have hJ : PolyBounded (fun g => (IndependentDomination.encInput g).length) J :=
    ((PolyBounded.const 2).mul PolyBounded.self).add hN |>.add (.const 1)
  have hVP : PolyBounded (fun g => (IndependentDomination.encInput g).length) V :=
    (PolyBounded.const cL).mul ((hJ.add (.const 1)).pow eL)
  have hV (g : IndependentDomination.Input) (j : ℕ) (hj : j ≤ rounds q g) :
      (encEntry (coefficient q counter (g, j))).length ≤ V g :=
    (hL _).trans (Nat.mul_le_mul_left cL
      (Nat.pow_le_pow_left (Nat.add_le_add_right (case_length_le q g hj) 1) eL))
  let cproj := NativeCertificate.ofPolyTime request_polytime
  have hproj := NativeCertificate.ofPolyTime_isPolynomial request_polytime
  let cf := cc.comp cproj
  have hcfS := SparseCNFLeafCounter.polyBounded_comp_space cc cproj hccS hproj.2
  let cid : NativeCertificate (fun s : State => s) encState encState :=
    NativeCertificate.linear (ComputableInO.of_eq fun _ => rfl)
  let pair := cid.prod cf
  have hpairS : PolyBounded (fun s => (encState s).length) pair.space :=
    PolyBounded.self.add hcfS
  have hpairL := SparseCNFLeafCounter.polyBounded_output_of_space pair hpairS
  let finishC := NativeCertificate.ofPolyTime finish_polytime
  have hfinish := NativeCertificate.ofPolyTime_isPolynomial finish_polytime
  let cb : NativeCertificate (step q counter) encState encState :=
    (finishC.comp pair).congr fun _ => rfl
  have hcbS := SparseCNFLeafCounter.polyBounded_comp_space finishC pair hfinish.2 hpairS
  let H (s : State) := (encState s).length + cproj.time s +
    finishC.time (s, coefficient q counter (request s))
  have hH : PolyBounded (fun s => (encState s).length) H :=
    (PolyBounded.self.add hproj.1).add (hfinish.1.comp hpairL)
  obtain ⟨cH, eH, hHbound⟩ := hH.exists_le
  let U (p : Case) := (encCase p).length + cq.time p +
    tag.time (p, counter (caseInput q p))
  have hU : PolyBounded (fun p => (encCase p).length) U :=
    (PolyBounded.self.add hq.1).add (htag.1.comp hcasePairL)
  let F (p : Case) := U p +
    pC * ((Bounded.BinaryFrontend.encInput (caseInput q p)).length + 1) ^ f
  have hF : PolyBounded (fun p => (encCase p).length) F :=
    hU.add ((PolyBounded.const pC).mul
      (((caseInput_polytime q).polyBounded_length.add (.const 1)).pow f))
  obtain ⟨cF, eF, hFbound⟩ := hF.exists_le
  let cn := NativeCertificate.ofPolyTime (rounds_polytime q)
  let ci := NativeCertificate.ofPolyTime initial_polytime
  have hn := NativeCertificate.ofPolyTime_isPolynomial (rounds_polytime q)
  have hi := NativeCertificate.ofPolyTime_isPolynomial initial_polytime
  let B (g : IndependentDomination.Input) := 2 * (IndependentDomination.encInput g).length +
    2 * rounds q g + 2 + rounds q g * (2 * V g + 1)
  have hB : PolyBounded (fun g => (IndependentDomination.encInput g).length) B :=
    ((((PolyBounded.const 2).mul PolyBounded.self).add
      ((PolyBounded.const 2).mul hN)).add (.const 2)).add
      (hN.mul (((PolyBounded.const 2).mul hVP).add (.const 1)))
  have hstate (g : IndependentDomination.Input) (j : ℕ) (hj : j ≤ rounds q g) :
      (encState ((step q counter)^[j] (initial g))).length ≤ B g :=
    trajectory_length q counter g hj (hV g)
  let R (g : IndependentDomination.Input) := cH * (B g + 1) ^ eH + cF * (J g + 1) ^ eF
  have hRP : PolyBounded (fun g => (IndependentDomination.encInput g).length) R :=
    ((PolyBounded.const cH).mul ((hB.add (.const 1)).pow eH)).add
      ((PolyBounded.const cF).mul ((hJ.add (.const 1)).pow eF))
  obtain ⟨cS, eS, hS⟩ := hcbS.exists_le
  let Q (g : IndependentDomination.Input) := cS * (B g + 1) ^ eS
  have hQP : PolyBounded (fun g => (IndependentDomination.encInput g).length) Q :=
    (PolyBounded.const cS).mul ((hB.add (.const 1)).pow eS)
  let loop := NativeCertificate.iterate cn ci cb
  have hLN := (rounds_polytime q).polyBounded_length
  have hmaxB (g : IndependentDomination.Input) :
      NativeCertificate.maxStateLength encState (step q counter) (rounds q g) (initial g) ≤ B g :=
    NativeCertificate.maxStateLength_le _ _ _ _ (hstate g)
  have hmaxQ (g : IndependentDomination.Input) :
      NativeCertificate.maxRoundSpace cb (rounds q g) (initial g) ≤ Q g :=
    NativeCertificate.maxRoundSpace_le _ _ _ fun j hj =>
      (hS _).trans (Nat.mul_le_mul_left cS
        (Nat.pow_le_pow_left (Nat.add_le_add_right (hstate g j hj) 1) eS))
  have hloopS : PolyBounded (fun g => (IndependentDomination.encInput g).length) loop.space :=
    ((((hn.2.add hi.2).add hQP).add hB).add hLN).mono fun g => by
      change cn.space g + ci.space g +
        NativeCertificate.maxRoundSpace cb (rounds q g) (initial g) +
        NativeCertificate.maxStateLength encState (step q counter) (rounds q g) (initial g) +
        (encNat (rounds q g)).length ≤
          cn.space g + ci.space g + Q g + B g + (encNat (rounds q g)).length
      have := hmaxQ g
      have := hmaxB g
      omega
  have hfinalL : PolyBounded (fun g => (IndependentDomination.encInput g).length)
      (fun g => (encState ((step q counter)^[rounds q g] (initial g))).length) :=
    hB.mono fun g => hstate g _ (Nat.le_refl _)
  let post := NativeCertificate.ofPolyTime output_polytime
  have hp := NativeCertificate.ofPolyTime_isPolynomial output_polytime
  have hpostT := hp.1.comp hfinalL
  have hpostS := hp.2.comp hfinalL
  let cs : NativeCertificate (run q counter) IndependentDomination.encInput (encList encEntry) :=
    (post.comp loop).congr fun _ => rfl
  have hcsS : PolyBounded (fun g => (IndependentDomination.encInput g).length) cs.space :=
    hloopS.add hpostS
  let W (g : IndependentDomination.Input) := cn.time g + ci.time g +
    (rounds q g + 1) * (R g + B g + ((encNat (rounds q g)).length + 1) ^ 2) +
    post.time ((step q counter)^[rounds q g] (initial g)) + cs.space g
  have hW : PolyBounded (fun g => (IndependentDomination.encInput g).length) W :=
    (((hn.1.add hi.1).add ((hN.add (.const 1)).mul
      ((hRP.add hB).add ((hLN.add (.const 1)).pow 2)))).add hpostT).add hcsS
  obtain ⟨C, e, hCe⟩ := hW.exists_le
  refine ⟨run q counter, cs, C, e, A, fun g => (Nat.le_add_left _ _).trans (hCe g), ?_⟩
  intro n G _
  constructor
  · rw [run_eq_map]
    have hc (j : ℕ) : coefficient q counter (IndependentDomination.ofGraph G, j) =
        (vectorAt q (IndependentDomination.ofGraph G, j), countForVector G
          (fun i j => (M i j).counts) (vectorAt q (IndependentDomination.ofGraph G, j))) := by
      let v := vectorAt q (IndependentDomination.ofGraph G, j)
      have h := ht G (fun i => v.getD i.val 0) (fun i => v.getD i.val 0)
      rw [← caseInput_ofGraph G q j] at h
      exact Prod.ext rfl (h.1.trans (coefficient_count G M v))
    calc
      _ = (List.range (rounds q (IndependentDomination.ofGraph G))).map (fun j =>
          (vectorAt q (IndependentDomination.ofGraph G, j), countForVector G
            (fun i j => (M i j).counts) (vectorAt q (IndependentDomination.ofGraph G, j)))) :=
        List.map_congr_left fun j _ => hc j
      _ = ((List.range (rounds q (IndependentDomination.ofGraph G))).map
          (fun j => vectorAt q (IndependentDomination.ofGraph G, j))).map
            (fun v => (v, countForVector G (fun i j => (M i j).counts) v)) := by
        simp only [List.map_map, Function.comp_def]
      _ = _ := congrArg (List.map (fun v =>
        (v, countForVector G (fun i j => (M i j).counts) v))) (map_vectorAt_range q _)
  · let g := IndependentDomination.ofGraph G
    let E := 2 ^ (A * Nat.logLogSqrtLogScale n)
    have hE : 0 < E := Nat.two_pow_pos _
    have hmaxT : NativeCertificate.maxRoundTime cb (rounds q g) (initial g) ≤ R g * E := by
      apply NativeCertificate.maxRoundTime_le
      intro j hj
      let s := (step q counter)^[j] (initial g)
      have hrequest : request s = (g, j) := by
        dsimp only [s]
        rw [trajectory q counter]
        rfl
      let v := vectorAt q (g, j)
      have htime := (ht G (fun i => v.getD i.val 0) (fun i => v.getD i.val 0)).2
      rw [← caseInput_ofGraph G q j] at htime
      change cp.time (caseInput q (g, j)) ≤ pC *
        ((Bounded.BinaryFrontend.encInput (caseInput q (g, j))).length + 1) ^ f * E at htime
      have hcountT : cc.time (g, j) ≤ F (g, j) * E := by
        change (encCase (g, j)).length +
          (cq.time (g, j) + cp.time (caseInput q (g, j))) +
          tag.time ((g, j), counter (caseInput q (g, j))) ≤ _
        have hm := Nat.le_mul_of_pos_right (U (g, j)) hE
        dsimp only [F, U] at hm ⊢
        rw [Nat.add_mul]
        nlinarith
      have hbody : cb.time s ≤ (H s + F (g, j)) * E := by
        change (encState s).length + (cproj.time s + cc.time (request s)) +
          finishC.time (s, coefficient q counter (request s)) ≤ _
        rw [hrequest]
        have hm := Nat.le_mul_of_pos_right (H s) hE
        dsimp only [H] at hm
        dsimp only [H]
        rw [hrequest] at hm ⊢
        rw [Nat.add_mul]
        omega
      have hupper : H s + F (g, j) ≤ R g := Nat.add_le_add
        ((hHbound s).trans (Nat.mul_le_mul_left cH
          (Nat.pow_le_pow_left (Nat.add_le_add_right (hstate g j hj) 1) eH)))
        ((hFbound (g, j)).trans (Nat.mul_le_mul_left cF
          (Nat.pow_le_pow_left (Nat.add_le_add_right (case_length_le q g hj) 1) eF)))
      exact hbody.trans (Nat.mul_le_mul_right E hupper)
    have hmb := hmaxB g
    have ht0 := Nat.le_mul_of_pos_right
      (cn.time g + ci.time g + post.time ((step q counter)^[rounds q g] (initial g))) hE
    have ht1 := Nat.le_mul_of_pos_right
      (B g + ((encNat (rounds q g)).length + 1) ^ 2) hE
    have ht2 := Nat.mul_le_mul_left (rounds q g + 1) (Nat.add_le_add hmaxT ht1)
    have hm := Nat.mul_le_mul_left (rounds q g + 1) (Nat.add_le_add_right
      (Nat.add_le_add_left hmb (NativeCertificate.maxRoundTime cb (rounds q g) (initial g)))
      (((encNat (rounds q g)).length + 1) ^ 2))
    have htime : cs.time g ≤ W g * E := by
      change cn.time g + ci.time g + (rounds q g + 1) *
        (NativeCertificate.maxRoundTime cb (rounds q g) (initial g) +
          NativeCertificate.maxStateLength encState (step q counter) (rounds q g) (initial g) +
          ((encNat (rounds q g)).length + 1) ^ 2) +
        post.time ((step q counter)^[rounds q g] (initial g)) ≤ _
      dsimp only [W]
      nlinarith
    exact htime.trans (Nat.mul_le_mul_right E (hCe g))



/-- Explicit framed output length of the entire grid, including vector tags and zero coefficients.
This bound does not substitute for the actual clock/resource proof. -/
theorem output_encoding_bound {n q : ℕ} (G : SimpleGraph (Fin n))
    (M : Fin q → Fin q → Set ℕ) :
    ((encList encEntry) ((SizeVectors.vectors q n).map fun v =>
      (v, countForVector G M v))).length ≤
      (n + 1) ^ q * (2 * (2 * q * (2 * (n + 1) + 1) + n * q + 2) + 1) := by
  have h := length_encList_le encEntry ((SizeVectors.vectors q n).map fun v =>
    (v, countForVector G M v)) (b := 2 * q * (2 * (n + 1) + 1) + n * q + 2) (by
      intro e he
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp he
      exact entry_bits_le G M v hv)
  simpa only [List.length_map, SizeVectors.length_vectors] using h

/-- The number of calls is polynomial in actual encoded input length for fixed q, explicitly. -/
theorem rounds_le_input_power (q : ℕ) (g : IndependentDomination.Input) :
    rounds q g ≤ ((IndependentDomination.encInput g).length + 1) ^ q := by
  rw [rounds_eq]
  apply Nat.pow_le_pow_left
  rcases g with ⟨n, rows⟩
  simp only [IndependentDomination.order, IndependentDomination.encInput,
    length_encPair, encUnary_apply, List.length_replicate]
  omega

open Classical in
/-- The complete actual tagged distribution has exact original counts, the real source exponent,
explicit polynomial output length and global polynomial peak workspace. -/
theorem exists_distribution_realEta_certificate (q D : ℕ) (hD : 1 ≤ D)
    (M : Fin q → Fin q → SimpleGraph.DegreeRule D) :
    ∃ distribution : IndependentDomination.Input → List Entry,
      ∃ cs : NativeCertificate distribution IndependentDomination.encInput (encList encEntry),
        ∃ C e A : ℕ,
          (∀ g, cs.space g ≤ C * ((IndependentDomination.encInput g).length + 1) ^ e) ∧
          ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
            distribution (IndependentDomination.ofGraph G) =
              (SizeVectors.vectors q n).map (fun v =>
                (v, countForVector G (fun i j => (M i j).counts) v)) ∧
            ((encList encEntry) (distribution (IndependentDomination.ofGraph G))).length ≤
              (n + 1) ^ q * (2 * (2 * q * (2 * (n + 1) + 1) + n * q + 2) + 1) ∧
            (16 ≤ n → (cs.time (IndependentDomination.ofGraph G) : ℝ) ≤ (C : ℝ) *
              ((IndependentDomination.encInput (IndependentDomination.ofGraph G)).length + 1 : ℕ) ^
                e * (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨dist, cs, C, e, A, hs, h⟩ := exists_distribution_sharp_certificate q D hD M
  refine ⟨dist, cs, C, e, 6 * A, hs, ?_⟩
  intro n G _
  refine ⟨(h G).1, ?_, fun hn => ?_⟩
  · rw [(h G).1]
    exact output_encoding_bound G _
  · have ht : (cs.time (IndependentDomination.ofGraph G) : ℝ) ≤ (C : ℝ) *
        ((IndependentDomination.encInput (IndependentDomination.ofGraph G)).length + 1 : ℕ) ^ e *
          (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast (h G).2
    exact ht.trans (mul_le_mul_of_nonneg_left
      (Nat.two_pow_mul_logLogSqrtLogScale_le A hn) (by positivity))

open Classical in
/-- Full source quantification over every fixed finite/cofinite labeled degree matrix. The
algorithm computes all vector tags/counts; it accepts no distribution or runtime contract. -/
theorem exists_distribution_finiteCofinite_certificate {q : ℕ} (M : Fin q → Fin q → Set ℕ)
    (hM : ∀ i j, (M i j).Finite ∨ (M i j)ᶜ.Finite) :
    ∃ distribution : IndependentDomination.Input → List Entry,
      ∃ cs : NativeCertificate distribution IndependentDomination.encInput (encList encEntry),
        ∃ C e A : ℕ,
          (∀ g, cs.space g ≤ C * ((IndependentDomination.encInput g).length + 1) ^ e) ∧
          ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
            distribution (IndependentDomination.ofGraph G) =
              (SizeVectors.vectors q n).map (fun v => (v, countForVector G M v)) ∧
            ((encList encEntry) (distribution (IndependentDomination.ofGraph G))).length ≤
              (n + 1) ^ q * (2 * (2 * q * (2 * (n + 1) + 1) + n * q + 2) + 1) ∧
            (16 ≤ n → (cs.time (IndependentDomination.ofGraph G) : ℝ) ≤ (C : ℝ) *
              ((IndependentDomination.encInput (IndependentDomination.ofGraph G)).length + 1 : ℕ) ^
                e * (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨D, hD, R, hR⟩ := SimpleGraph.exists_degreeMatrixRules M hM
  obtain ⟨dist, cs, C, e, A, hs, h⟩ := exists_distribution_realEta_certificate q D hD R
  refine ⟨dist, cs, C, e, A, hs, ?_⟩
  intro n G _
  simpa only [hR] using h G

end Cslib.Logic.PL.DegreePartition.Distribution
