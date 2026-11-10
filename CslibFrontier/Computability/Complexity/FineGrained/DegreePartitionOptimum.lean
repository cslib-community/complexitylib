/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.DegreePartitionDistribution
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List.ArgOpt
-- Reuse the private polyBounded_output_of_space and polyBounded_comp_space resource lemmas.
import all CslibFrontier.Computability.PolyTime.CNF.SparseCNFLeafCounter

/-!
# Native extrema for labeled degree partitions

For each fixed label, scan the actual complete distribution, retaining positive coefficients
inside every input binary class interval. The returned optional minimum and maximum include an
attained size vector and its exact original-partition multiplicity. Empty feasible families
return two absent results. This is the optimization clause following [ChenJiangZhu2027],
Theorem 7.3 (PDF p.25); it requires no monotonicity under inclusion.

## Main definitions

* `select`: actual bounded positive-support scan and attained extrema.
* `encResult`: both optional full vector/count outputs, with their tags and framing.

## Main results

* `select_polytime`: traversal, comparisons, retained vectors and output are charged.
* `select_optimal`: each returned size is attained and globally optimal, or feasibility fails.
* `exists_optimal_sharp_certificate`, `exists_optimal_realEta_certificate`: complete native bounds.
* `exists_optimal_finiteCofinite_certificate`: all fixed finite/cofinite matrices
  and varying bounds.
-/

public section

namespace Cslib.Logic.PL.DegreePartition.Optimum

open Turing.MultiTapeTM Cslib.GenericRAM Cslib.Complexity
open Distribution Bounded.BinaryFrontend

/-- Optional minimum entry followed by optional maximum entry, retaining original label tags. -/
abbrev Result := Option Entry × Option Entry
/-- Framed pair of optional vector/count pairs; each option has its own tag, all numbers binary. -/
abbrev encResult : Result ↪ List Bool := encPair (encOption encEntry) (encOption encEntry)
/-- A postprocessing request retains the complete bounded original input and tagged distribution. -/
abbrev Request := Input × List Entry
/-- The bounded graph/binary intervals are framed before the complete framed tagged-entry list. -/
abbrev encRequest : Request ↪ List Bool := encPair encInput (encList encEntry)

/-- Check every original class interval, preserving empty classes and contradictory bounds. -/
@[expose] def within (q : ℕ) (x : Input) (v : List ℕ) : Bool :=
  (List.finRange q).all fun i => decide (lower i.val x ≤ v.getD i.val 0 ∧
    v.getD i.val 0 ≤ upper i.val x)
/-- Original class-size objective of one tagged coefficient. -/
@[expose] def coordinate (i : ℕ) (e : Entry) : ℕ := e.1.getD i 0
/-- Only actual positive original-partition counts satisfying all input intervals survive. -/
@[expose] def candidates (q : ℕ) (x : Input) (ys : List Entry) : List Entry :=
  ys.filter fun e => decide (0 < e.2) && within q x e.1
/-- Actual first-tie scans return complete attained entries, not just a threshold predicate. -/
@[expose] def select (q i : ℕ) (p : Request) : Result :=
  let ys := candidates q p.1 p.2
  (ys.argmin (coordinate i), ys.argmax (coordinate i))

private theorem within_polytime (q : ℕ) : ComputableInPolyTime
    (fun p : Input × List ℕ => within q p.1 p.2) (encPair encInput (encList encNat)) encBool := by
  unfold within
  apply ComputableInPolyTime.allConst
  intro i _
  have he : ComputableInPolyTime (fun p : Input × List ℕ => entry i.val p.1)
      (encPair encInput (encList encNat)) (encPair encNat encNat) := by
    unfold entry intervals encInput
    fun_prop
  have hv : ComputableInPolyTime (fun p : Input × List ℕ => p.2.getD i.val 0)
      (encPair encInput (encList encNat)) encNat := by fun_prop
  unfold lower upper
  fun_prop

/-- The actual support filtering and two attained scans have polynomial binary time and space. -/
theorem select_polytime (q i : ℕ) : ComputableInPolyTime (select q i) encRequest encResult := by
  have htest : ComputableInPolyTime (fun p : Request × Entry =>
      decide (0 < p.2.2) && within q p.1.1 p.2.1) (encPair encRequest encEntry) encBool := by
    have he := ComputableInPolyTime.snd encRequest encEntry
    have hx := ComputableInPolyTime.fst encRequest encEntry
    have hw := (within_polytime q).comp (hx.fst'.prod he.fst')
    exact (ComputableInPolyTime.binary_lt' (.const 0) he.snd').bool_and' hw
  have hy : ComputableInPolyTime (fun p : Request => candidates q p.1 p.2)
      encRequest (encList encEntry) :=
    ComputableInPolyTime.filterWithInput (ComputableInPolyTime.snd _ _) htest
  have hc : ComputableInPolyTime (coordinate i) encEntry encNat := by
    unfold coordinate encEntry
    fun_prop
  have ht : ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.1 < p.2))
      (encPair encNat encNat) encBool := by fun_prop
  exact ((ComputableInPolyTime.argmin hc ht).comp hy).prod
    ((ComputableInPolyTime.argmax hc ht).comp hy)

private theorem within_ofGraph {n q : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lo hi : Fin q → ℕ) (v : List ℕ) :
    within q (ofGraph G lo hi) v = true ↔ ∀ i, lo i ≤ v.getD i.val 0 ∧
      v.getD i.val 0 ≤ hi i := by
  have he (i : Fin q) : entry i.val (ofGraph G lo hi) = (lo i, hi i) := by
    simp [entry, intervals, ofGraph]
  simp [within, lower, upper, he]

/-- Conventional feasibility includes all varying input class bounds. -/
@[expose] def Feasible {n q : ℕ} (G : SimpleGraph (Fin n))
    (M : Fin q → Fin q → Set ℕ) (lo hi : Fin q → ℕ) (S : Fin q → Set (Fin n)) : Prop :=
  G.IsDegreePartition M S ∧ SimpleGraph.InClassBounds lo hi S

/-- A returned entry records an actual feasible vector and its original labeled multiplicity. -/
@[expose] def Attained {n q : ℕ} (G : SimpleGraph (Fin n))
    (M : Fin q → Fin q → Set ℕ) (lo hi : Fin q → ℕ) (e : Entry) : Prop :=
  e.1.length = q ∧ e.2 = countForVector G M e.1 ∧ ∃ S, Feasible G M lo hi S ∧
    ∀ i, Nat.card (S i) = e.1.getD i.val 0

/-- Both returned optima are attained and dominate every feasible original partition's objective;
both absence tags are equivalent to infeasibility, not to a zero size. -/
@[expose] def Optimal {n q : ℕ} (G : SimpleGraph (Fin n))
    (M : Fin q → Fin q → Set ℕ) (lo hi : Fin q → ℕ) (i : Fin q) (r : Result) : Prop :=
  (r.1 = none ↔ ¬ ∃ S, Feasible G M lo hi S) ∧
  (r.2 = none ↔ ¬ ∃ S, Feasible G M lo hi S) ∧
  (∀ e ∈ r.1, Attained G M lo hi e ∧ ∀ S, Feasible G M lo hi S →
    coordinate i.val e ≤ Nat.card (S i)) ∧
  (∀ e ∈ r.2, Attained G M lo hi e ∧ ∀ S, Feasible G M lo hi S →
    Nat.card (S i) ≤ coordinate i.val e)

open Classical in
private theorem candidates_mem {n q : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (M : Fin q → Fin q → Set ℕ) (lo hi : Fin q → ℕ) (e : Entry) :
    e ∈ candidates q (ofGraph G lo hi)
      ((SizeVectors.vectors q n).map fun v => (v, countForVector G M v)) ↔
      e.1 ∈ SizeVectors.vectors q n ∧ Attained G M lo hi e := by
  have hpos (v : List ℕ) : 0 < countForVector G M v ↔
      ∃ S, G.IsDegreePartition M S ∧ ∀ i, Nat.card (S i) = v.getD i.val 0 := by
    simp only [countForVector, Nat.card_eq_fintype_card, Fintype.card_pos_iff, nonempty_subtype]
  constructor
  · intro h
    obtain ⟨hm, ht⟩ := List.mem_filter.mp h
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hm
    obtain ⟨hp, hb⟩ := Bool.and_eq_true_iff.mp ht
    obtain ⟨S, hS, hsize⟩ := (hpos v).mp (of_decide_eq_true hp)
    have hbounds := (within_ofGraph G lo hi v).mp hb
    refine ⟨hv, ((SizeVectors.mem_vectors q n v).mp hv).1, rfl, S, ⟨hS, ?_⟩, hsize⟩
    intro i
    simpa only [hsize i] using hbounds i
  · rintro ⟨hv, _, he, S, ⟨hS, hb⟩, hsize⟩
    apply List.mem_filter.mpr
    refine ⟨List.mem_map.mpr ⟨e.1, hv, Prod.ext rfl he.symm⟩, ?_⟩
    apply Bool.and_eq_true_iff.mpr
    refine ⟨?_, ?_⟩
    · apply decide_eq_true
      rw [he]
      exact (hpos e.1).mpr ⟨S, hS, hsize⟩
    · apply (within_ofGraph G lo hi e.1).mpr
      intro i
      simpa only [← hsize i] using hb i

open Classical in
private theorem feasible_entry {n q : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (M : Fin q → Fin q → Set ℕ) (lo hi : Fin q → ℕ) (S : Fin q → Set (Fin n))
    (hS : Feasible G M lo hi S) :
    ∃ e ∈ candidates q (ofGraph G lo hi)
      ((SizeVectors.vectors q n).map fun v => (v, countForVector G M v)),
        ∀ i, coordinate i.val e = Nat.card (S i) := by
  let v := List.ofFn fun i : Fin q => Nat.card (S i)
  have hv : v ∈ SizeVectors.vectors q n := by
    apply (SizeVectors.mem_vectors q n v).mpr
    refine ⟨by simp [v], ?_⟩
    intro k hk
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin n)
  have heq (i : Fin q) : v.getD i.val 0 = Nat.card (S i) := by
    simp [v]
  refine ⟨(v, countForVector G M v), (candidates_mem G M lo hi _).mpr
    ⟨hv, ((SizeVectors.mem_vectors q n v).mp hv).1, rfl, S, hS,
      fun i => (heq i).symm⟩, ?_⟩
  exact heq

open Classical in
/-- The actual scans attain both extrema over all original labeled partitions
within the input bounds. -/
theorem select_optimal {n q : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (M : Fin q → Fin q → Set ℕ) (lo hi : Fin q → ℕ) (i : Fin q) :
    Optimal G M lo hi i (select q i.val (ofGraph G lo hi,
      (SizeVectors.vectors q n).map fun v => (v, countForVector G M v))) := by
  let ys := candidates q (ofGraph G lo hi)
    ((SizeVectors.vectors q n).map fun v => (v, countForVector G M v))
  have hempty : ys = [] ↔ ¬ ∃ S, Feasible G M lo hi S := by
    rw [List.eq_nil_iff_forall_not_mem]
    constructor
    · intro h ⟨S, hS⟩
      obtain ⟨e, he, _⟩ := feasible_entry G M lo hi S hS
      exact h e he
    · intro h e he
      obtain ⟨_, _, _, S, hS, _⟩ := (candidates_mem G M lo hi e).mp he
      exact h ⟨S, hS⟩
  refine ⟨(List.argmin_eq_none).trans hempty, (List.argmax_eq_none).trans hempty, ?_, ?_⟩
  · intro e he
    refine ⟨((candidates_mem G M lo hi e).mp (List.argmin_mem he)).2, ?_⟩
    intro S hS
    obtain ⟨t, ht, hsize⟩ := feasible_entry G M lo hi S hS
    exact (List.le_of_mem_argmin ht he).trans_eq (hsize i)
  · intro e he
    refine ⟨((candidates_mem G M lo hi e).mp (List.argmax_mem he)).2, ?_⟩
    intro S hS
    obtain ⟨t, ht, hsize⟩ := feasible_entry G M lo hi S hS
    exact (hsize i).symm.trans_le (List.le_of_mem_argmax ht he)

open Classical in
/-- The actual bounded distribution followed by the two scans has sharp rounded time in original
vertices and polynomial workspace globally, uniformly over every input binary class bound. -/
theorem exists_optimal_sharp_certificate (q D : ℕ) (hD : 1 ≤ D)
    (M : Fin q → Fin q → SimpleGraph.DegreeRule D) (i : Fin q) :
    ∃ optimal : Input → Result, ∃ cs : NativeCertificate optimal encInput encResult,
      ∃ C e A : ℕ,
        (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
        ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : Fin q → ℕ),
          Optimal G (fun j k => (M j k).counts) lo hi i (optimal (ofGraph G lo hi)) ∧
          cs.time (ofGraph G lo hi) ≤ C * ((encInput (ofGraph G lo hi)).length + 1) ^ e *
            2 ^ (A * Nat.logLogSqrtLogScale n) := by
  obtain ⟨dist, cp, C, e, A, hs, h⟩ := Distribution.exists_distribution_sharp_certificate q D hD M
  have ho : ComputableInPolyTime Bounded.BinaryFrontend.original encInput
      IndependentDomination.encInput := by
    unfold Bounded.BinaryFrontend.original encInput
    fun_prop
  let pre := NativeCertificate.ofPolyTime ho
  have hp := NativeCertificate.ofPolyTime_isPolynomial ho
  let ident := NativeCertificate.ofPolyTime (ComputableInPolyTime.id' (encIn := encInput))
  have hid := NativeCertificate.ofPolyTime_isPolynomial
    (ComputableInPolyTime.id' (encIn := encInput))
  let retained := ident.prod (cp.comp pre)
  have hcpS := PolyBounded.of_forall_le C e hs
  have hrS : PolyBounded (fun x => (encInput x).length) retained.space :=
    hid.2.add (SparseCNFLeafCounter.polyBounded_comp_space cp pre hcpS hp.2)
  have hlen := SparseCNFLeafCounter.polyBounded_output_of_space retained hrS
  let post := NativeCertificate.ofPolyTime (select_polytime q i.val)
  have hpost := NativeCertificate.ofPolyTime_isPolynomial (select_polytime q i.val)
  let cs := post.comp retained
  have hcsS := SparseCNFLeafCounter.polyBounded_comp_space post retained hpost.2 hrS
  let W (x : Input) := ident.time x + pre.time x +
    C * ((IndependentDomination.encInput (Bounded.BinaryFrontend.original x)).length + 1) ^ e +
    post.time (x, dist (Bounded.BinaryFrontend.original x)) + cs.space x
  have hW : PolyBounded (fun x => (encInput x).length) W :=
    ((((hid.1.add hp.1).add ((PolyBounded.const C).mul
      ((ho.polyBounded_length.add (.const 1)).pow e))).add
      (hpost.1.comp hlen))).add hcsS
  obtain ⟨B, f, hBf⟩ := hW.exists_le
  refine ⟨(fun x => select q i.val (x, dist (Bounded.BinaryFrontend.original x))),
    cs, B, f, A, ?_, ?_⟩
  · intro x
    exact (show cs.space x ≤ W x from Nat.le_add_left _ _).trans (hBf x)
  intro n G _ lo hi
  constructor
  · change Optimal G _ lo hi i (select q i.val (ofGraph G lo hi,
      dist (IndependentDomination.ofGraph G)))
    rw [(h G).1]
    exact select_optimal G _ lo hi i
  · let x := ofGraph G lo hi
    let E := 2 ^ (A * Nat.logLogSqrtLogScale n)
    have hE : 0 < E := Nat.two_pow_pos _
    have ht : cp.time (Bounded.BinaryFrontend.original x) ≤
        C * ((IndependentDomination.encInput (Bounded.BinaryFrontend.original x)).length + 1) ^ e *
          E :=
      (h G).2
    have hrest := Nat.le_mul_of_pos_right
      (ident.time x + pre.time x + post.time (x, dist (Bounded.BinaryFrontend.original x))) hE
    change ident.time x + (pre.time x + cp.time (Bounded.BinaryFrontend.original x)) +
      post.time (x, dist (Bounded.BinaryFrontend.original x)) ≤ _
    calc _ ≤ (ident.time x + pre.time x +
        C * ((IndependentDomination.encInput (Bounded.BinaryFrontend.original x)).length + 1) ^ e +
          post.time (x, dist (Bounded.BinaryFrontend.original x))) * E := by nlinarith
      _ ≤ W x * E := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
      _ ≤ _ := Nat.mul_le_mul_right _ (hBf x)

open Classical in
/-- Attained extrema use the source single-log-log real clock, without an extra loglog factor. -/
theorem exists_optimal_realEta_certificate (q D : ℕ) (hD : 1 ≤ D)
    (M : Fin q → Fin q → SimpleGraph.DegreeRule D) (i : Fin q) :
    ∃ optimal : Input → Result, ∃ cs : NativeCertificate optimal encInput encResult,
      ∃ C e A : ℕ,
        (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
        ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : Fin q → ℕ),
          Optimal G (fun j k => (M j k).counts) lo hi i (optimal (ofGraph G lo hi)) ∧
          (16 ≤ n → (cs.time (ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
            ((encInput (ofGraph G lo hi)).length + 1 : ℕ) ^ e *
              (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨opt, cs, C, e, A, hs, h⟩ := exists_optimal_sharp_certificate q D hD M i
  refine ⟨opt, cs, C, e, 6 * A, hs, ?_⟩
  intro n G _ lo hi
  refine ⟨(h G lo hi).1, fun hn => ?_⟩
  have ht : (cs.time (ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
      ((encInput (ofGraph G lo hi)).length + 1 : ℕ) ^ e *
        (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast (h G lo hi).2
  exact ht.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A hn) (by positivity))

open Classical in
/-- Full fixed finite/cofinite matrix quantifiers: no supplied distribution, optimum or runtime.
Both original input class bounds vary; the chosen label and matrix are fixed source parameters. -/
theorem exists_optimal_finiteCofinite_certificate {q : ℕ} (M : Fin q → Fin q → Set ℕ)
    (hM : ∀ j k, (M j k).Finite ∨ (M j k)ᶜ.Finite) (i : Fin q) :
    ∃ optimal : Input → Result, ∃ cs : NativeCertificate optimal encInput encResult,
      ∃ C e A : ℕ,
        (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
        ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : Fin q → ℕ),
          Optimal G M lo hi i (optimal (ofGraph G lo hi)) ∧
          (16 ≤ n → (cs.time (ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
            ((encInput (ofGraph G lo hi)).length + 1 : ℕ) ^ e *
              (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨D, hD, R, hR⟩ := SimpleGraph.exists_degreeMatrixRules M hM
  obtain ⟨opt, cs, C, e, A, hs, h⟩ := exists_optimal_realEta_certificate q D hD R i
  refine ⟨opt, cs, C, e, A, hs, ?_⟩
  intro n G _ lo hi
  simpa only [hR] using h G lo hi

end Cslib.Logic.PL.DegreePartition.Optimum
