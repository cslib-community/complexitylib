/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.SetCover.Greedy
public import CslibFrontier.Computability.Complexity.Classes.NP.Witness
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.GetD

/-!
# Set Cover

Finite set systems (`Cslib.Complexity.SetSystem`) and weighted set systems
(`Cslib.Complexity.WeightedSetSystem`) over natural-number elements, encoded with binary
element labels and frame delimiters (`encSetSystem`, `encWeightedSetSystem`).

An unweighted instance `(S, k)` belongs to `Cslib.Complexity.SetCover` when at most `k` sets from
`S.sets` (selected by index `Fin S.sets.length`) cover every element of `S.ground`. A weighted
instance `(W, k)` belongs to `Cslib.Complexity.WeightedSetCover` when a covering selection of sets
has total weight at most `k`. Both problems lie in `NP` (`SetCover_mem_NP`,
`WeightedSetCover_mem_NP`) via subset witnesses (`Cslib.Complexity.mem_NP_of_subsetWitness`), and
connect directly to the library's greedy algorithm (`Cslib.Algorithms.Lean.SetCover.greedy`).

This set-system encoding is designed to be shared with related problems (`HittingSet` and
Karp's set-system problems).

## Main definitions

* `Cslib.Complexity.SetSystem`, `Cslib.Complexity.encSetSystem`: finite set systems and their
  binary-labeled encoding.
* `Cslib.Complexity.SetSystem.IsCover`, `Cslib.Complexity.SetSystem.optCoverSize`: covering
  predicates and minimum cover cardinality on coverable set systems.
* `Cslib.Complexity.SetCover`, `Cslib.Complexity.encSetCover`: the unweighted Set Cover decision
  problem and its encoding.
* `Cslib.Complexity.WeightedSet`, `Cslib.Complexity.WeightedSetSystem`,
  `Cslib.Complexity.encWeightedSetSystem`, `Cslib.Complexity.WeightedSetCover`: weighted set
  systems, minimum cover weight (`optCoverWeight`), and the weighted Set Cover decision problem.

## Main results

* `Cslib.Complexity.SetCover_mem_NP`, `Cslib.Complexity.WeightedSetCover_mem_NP`: membership in
  `NP`.
* `Cslib.Complexity.SetSystem.greedyIndices_isCover`,
  `Cslib.Complexity.SetSystem.greedyIndices_length_le_one_add_log`,
  `Cslib.Complexity.WeightedSetSystem.greedyIndices_isCover`,
  `Cslib.Complexity.WeightedSetSystem.greedyWeight_le_one_add_log`: bridge to the greedy algorithm.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

/-! ### Unweighted set systems -/

/-- A finite set system over natural-number elements: a ground list `ground` together with a list
of candidate subsets `sets`. Duplicates in `ground` or a candidate set are harmless, while distinct
indices in `S.sets` are kept distinct. -/
structure SetSystem where
  /-- Elements of the ground set that must be covered. -/
  ground : List ℕ
  /-- Candidate subsets available for covering `ground`. -/
  sets : List (List ℕ)
  deriving DecidableEq, Repr

/-- Framed binary encoding of a list of natural-number subsets. -/
abbrev encNatSetList : List (List ℕ) ↪ List Bool := encList (encList encNat)

/-- Framed encoding of a `SetSystem` with binary element labels. -/
enc_structure encSetSystem : SetSystem where
  ground : (encList encNat),
  sets : encNatSetList

/-- Framed pair of a `SetSystem` and a binary target bound `k`. -/
abbrev encSetCover : SetSystem × ℕ ↪ List Bool := encPair encSetSystem encNat

@[fun_prop] theorem computableInPolyTime_setSystemGround :
    ComputableInPolyTime SetSystem.ground encSetSystem (encList encNat) :=
  encSetSystem_ground_deg.computableInPolyTime

@[fun_prop] theorem computableInPolyTime_setSystemSets :
    ComputableInPolyTime SetSystem.sets encSetSystem encNatSetList :=
  encSetSystem_sets_deg.computableInPolyTime

@[fun_prop] theorem computableInPolyTime_setSystemMk {γ : Type} {enc : γ ↪ List Bool}
    {u : γ → List ℕ} {s : γ → List (List ℕ)}
    (hu : ComputableInPolyTime u enc (encList encNat))
    (hs : ComputableInPolyTime s enc encNatSetList) :
    ComputableInPolyTime (fun x => SetSystem.mk (u x) (s x)) enc encSetSystem :=
  encSetSystem_mk_deg.computableInPolyTime.comp (hu.prod hs)

namespace SetSystem

/-- A selection of indices `C` covers `S` when every element of `S.ground` belongs to `S.sets[i]`
for some `i ∈ C`. -/
@[expose] def IsCover (S : SetSystem) (C : Finset (Fin S.sets.length)) : Prop :=
  ∀ u ∈ S.ground, ∃ i ∈ C, u ∈ S.sets[i]

/-- A set system is coverable when some finite index selection covers its ground set. -/
@[expose] def Coverable (S : SetSystem) : Prop :=
  ∃ C : Finset (Fin S.sets.length), S.IsCover C

/-- Boolean test for whether every element of `S.ground` appears in at least one candidate set. -/
@[expose] def coverableBool (S : SetSystem) : Bool :=
  S.ground.all fun u => S.sets.any fun A => decide (u ∈ A)

theorem coverableBool_eq_true_iff (S : SetSystem) : S.coverableBool = true ↔ S.Coverable := by
  simp only [coverableBool, List.all_eq_true, List.any_eq_true, decide_eq_true_eq, Coverable,
    IsCover]
  constructor
  · intro h
    refine ⟨Finset.univ, fun u hu => ?_⟩
    obtain ⟨A, hA, huA⟩ := h u hu
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hA
    exact ⟨⟨i, hi⟩, Finset.mem_univ _, huA⟩
  · rintro ⟨C, hC⟩ u hu
    obtain ⟨i, -, hui⟩ := hC u hu
    exact ⟨S.sets[i], List.getElem_mem i.isLt, hui⟩

@[fun_prop] theorem computableInPolyTime_coverableBool :
    ComputableInPolyTime coverableBool encSetSystem encBool := by
  unfold coverableBool
  apply ComputableInPolyTime.allWithInput (by fun_prop)
  apply ComputableInPolyTime.anyWithInput (by fun_prop)
  fun_prop

/-- Boolean check that a list `I` of natural-number indices specifies a valid cover of `S`. -/
@[expose] def isCoverList (S : SetSystem) (I : List ℕ) : Bool :=
  I.all (fun i => decide (i < S.sets.length)) &&
    S.ground.all fun u => I.any fun i => decide (u ∈ S.sets.getD i [])

theorem isCoverList_eq_true_iff (S : SetSystem) (I : List ℕ) :
    S.isCoverList I = true ↔
      (∀ i ∈ I, i < S.sets.length) ∧
        ∀ u ∈ S.ground, ∃ i ∈ I, ∃ hi : i < S.sets.length, u ∈ S.sets[i]'hi := by
  simp only [isCoverList, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨hbound, hcov⟩
    refine ⟨hbound, fun u hu => ?_⟩
    obtain ⟨i, hiI, hui⟩ := hcov u hu
    have hi := hbound i hiI
    rw [List.getD_eq_getElem _ _ hi] at hui
    exact ⟨i, hiI, hi, hui⟩
  · rintro ⟨hbound, hcov⟩
    refine ⟨hbound, fun u hu => ?_⟩
    obtain ⟨i, hiI, hi, hui⟩ := hcov u hu
    exact ⟨i, hiI, by rwa [List.getD_eq_getElem _ _ hi]⟩

private theorem isCoverList_toFinset_iff (S : SetSystem) {I : List ℕ}
    (hI : ∀ i ∈ I, i < S.sets.length) :
    S.isCoverList I = true ↔
      S.IsCover (Finset.univ.filter fun i : Fin S.sets.length => (i : ℕ) ∈ I.toFinset) := by
  rw [isCoverList_eq_true_iff]
  refine ⟨fun ⟨_, hcov⟩ u hu => ?_, fun hcov => ⟨hI, fun u hu => ?_⟩⟩
  · obtain ⟨i, hiI, hi, hui⟩ := hcov u hu
    exact ⟨⟨i, hi⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, List.mem_toFinset.2 hiI⟩, hui⟩
  · obtain ⟨i, hiC, hui⟩ := hcov u hu
    exact ⟨i, List.mem_toFinset.1 (Finset.mem_filter.1 hiC).2, i.isLt, hui⟩

@[fun_prop] theorem computableInPolyTime_isCoverList :
    ComputableInPolyTime (fun p : SetSystem × List ℕ => p.1.isCoverList p.2)
      (encPair encSetSystem (encList encUnary)) encBool := by
  unfold isCoverList
  have hlen : ComputableInPolyTime (fun p : (SetSystem × List ℕ) × ℕ => p.1.1.sets.length)
      (encPair (encPair encSetSystem (encList encUnary)) encUnary) encUnary := by fun_prop
  have hbound : ComputableInPolyTime
      (fun p : SetSystem × List ℕ => p.2.all fun i => decide (i < p.1.sets.length))
      (encPair encSetSystem (encList encUnary)) encBool := by
    apply ComputableInPolyTime.allWithInput (by fun_prop)
    exact ComputableInPolyTime.unary_lt' (ComputableInPolyTime.snd _ _) hlen
  have hcov : ComputableInPolyTime
      (fun p : SetSystem × List ℕ =>
        p.1.ground.all fun u => p.2.any fun i => decide (u ∈ p.1.sets.getD i []))
      (encPair encSetSystem (encList encUnary)) encBool := by
    apply ComputableInPolyTime.allWithInput (by fun_prop)
    apply ComputableInPolyTime.anyWithInput (by fun_prop)
    have hset : ComputableInPolyTime
        (fun q : ((SetSystem × List ℕ) × ℕ) × ℕ => q.1.1.1.sets.getD q.2 [])
        (encPair (encPair (encPair encSetSystem (encList encUnary)) encNat) encUnary)
        (encList encNat) :=
      ComputableInPolyTime.listGetDWithInput (by fun_prop) (by fun_prop) []
    fun_prop
  fun_prop

/-- The minimum number of sets needed to cover `S` when `S.Coverable` holds (and `0` otherwise). -/
noncomputable def optCoverSize (S : SetSystem) : ℕ :=
  open Classical in
  if h : S.Coverable then
    Nat.find (⟨S.sets.length, h.choose, h.choose_spec,
      (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)⟩ :
      ∃ n : ℕ, ∃ C : Finset (Fin S.sets.length), S.IsCover C ∧ C.card ≤ n)
  else 0

theorem optCoverSize_le {S : SetSystem} {C : Finset (Fin S.sets.length)} (hC : S.IsCover C) :
    S.optCoverSize ≤ C.card := by
  classical
  have hS : S.Coverable := ⟨C, hC⟩
  rw [optCoverSize]
  split_ifs
  exact Nat.find_min' _ ⟨C, hC, le_rfl⟩

theorem optCoverSize_eq_zero_of_not_coverable {S : SetSystem} (hS : ¬ S.Coverable) :
    S.optCoverSize = 0 := by
  classical
  rw [optCoverSize]
  split_ifs
  rfl

theorem exists_isCover_optCoverSize {S : SetSystem} (hS : S.Coverable) :
    ∃ C : Finset (Fin S.sets.length), S.IsCover C ∧ C.card = S.optCoverSize := by
  classical
  rw [optCoverSize]
  split_ifs
  obtain ⟨C, hC, hcard⟩ := Nat.find_spec (⟨S.sets.length, hS.choose, hS.choose_spec,
    (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)⟩ :
    ∃ n : ℕ, ∃ C : Finset (Fin S.sets.length), S.IsCover C ∧ C.card ≤ n)
  have hmin : Nat.find (⟨S.sets.length, hS.choose, hS.choose_spec,
      (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)⟩ :
      ∃ n : ℕ, ∃ C : Finset (Fin S.sets.length), S.IsCover C ∧ C.card ≤ n) ≤ C.card :=
    Nat.find_min' _ ⟨C, hC, le_rfl⟩
  exact ⟨C, hC, le_antisymm hcard hmin⟩

theorem optCoverSize_le_iff {S : SetSystem} (hS : S.Coverable) {k : ℕ} :
    S.optCoverSize ≤ k ↔ ∃ C : Finset (Fin S.sets.length), S.IsCover C ∧ C.card ≤ k := by
  refine ⟨fun h => ?_, fun ⟨C, hC, hk⟩ => (optCoverSize_le hC).trans hk⟩
  obtain ⟨C, hC, hcard⟩ := exists_isCover_optCoverSize hS
  exact ⟨C, hC, hcard ▸ h⟩

theorem le_optCoverSize_iff {S : SetSystem} (hS : S.Coverable) {k : ℕ} :
    k ≤ S.optCoverSize ↔ ∀ C : Finset (Fin S.sets.length), S.IsCover C → k ≤ C.card := by
  refine ⟨fun hk C hC => hk.trans (optCoverSize_le hC), fun h => ?_⟩
  obtain ⟨C, hC, hcard⟩ := exists_isCover_optCoverSize hS
  rw [← hcard]
  exact h C hC

/-- Indices chosen by `Cslib.Algorithms.Lean.SetCover.greedy` on `S` with unit weights. -/
@[expose] noncomputable def greedyIndices (S : SetSystem) : List (Fin S.sets.length) :=
  Cslib.Algorithms.Lean.SetCover.greedy (fun i : Fin S.sets.length => S.sets[i].toFinset)
    (fun _ => (1 : ℝ)) (List.finRange S.sets.length) S.ground.toFinset

theorem greedyIndices_isCover {S : SetSystem} (hS : S.Coverable) :
    S.IsCover S.greedyIndices.toFinset := by
  intro u hu
  have hcov := Cslib.Algorithms.Lean.SetCover.greedy_covers
    (S := fun i : Fin S.sets.length => S.sets[i].toFinset)
    (w := fun _ => (1 : ℝ)) (J := List.finRange S.sets.length) (U := S.ground.toFinset)
    (fun a ha => by
      obtain ⟨C, hC⟩ := hS
      obtain ⟨i, -, hui⟩ := hC a (List.mem_toFinset.1 ha)
      exact ⟨i, List.mem_finRange i, List.mem_toFinset.2 hui⟩)
    u (List.mem_toFinset.2 hu)
  obtain ⟨i, hi, hui⟩ := hcov
  exact ⟨i, List.mem_toFinset.2 hi, List.mem_toFinset.1 hui⟩

theorem greedyIndices_length_le_one_add_log {S : SetSystem} (hS : S.Coverable) :
    (S.greedyIndices.length : ℝ) ≤ (1 + Real.log S.ground.toFinset.card) * S.optCoverSize := by
  obtain ⟨C, hC, hcard⟩ := exists_isCover_optCoverSize hS
  have h := Cslib.Algorithms.Lean.SetCover.sum_greedy_le_one_add_log_mul
    (S := fun i : Fin S.sets.length => S.sets[i].toFinset) (w := fun _ => (1 : ℝ))
    (J := List.finRange S.sets.length) (U := S.ground.toFinset) (C := C)
    (d := S.ground.toFinset.card) (fun _ _ => zero_le_one) (fun j _ => List.mem_finRange j)
    (fun a ha => by
      obtain ⟨i, hi, hai⟩ := hC a (List.mem_toFinset.1 ha)
      exact ⟨i, hi, List.mem_toFinset.2 hai⟩)
    (fun j _ => Finset.card_le_card Finset.inter_subset_right)
  simpa only [greedyIndices, List.map_const', List.sum_replicate, nsmul_eq_mul, mul_one,
    Finset.sum_const, ← hcard] using h

end SetSystem

/-- **Unweighted Set Cover**: pairs `(S, k)` such that at most `k` candidate sets in `S` cover
`S.ground`. -/
@[expose] def SetCover : Set (SetSystem × ℕ) :=
  {p | ∃ C : Finset (Fin p.1.sets.length), p.1.IsCover C ∧ C.card ≤ p.2}

theorem mem_SetCover_iff {S : SetSystem} {k : ℕ} :
    (S, k) ∈ SetCover ↔ ∃ C : Finset (Fin S.sets.length), S.IsCover C ∧ C.card ≤ k :=
  Iff.rfl

theorem mem_SetCover_iff_optCoverSize {S : SetSystem} {k : ℕ} :
    (S, k) ∈ SetCover ↔ S.Coverable ∧ S.optCoverSize ≤ k := by
  refine ⟨fun ⟨C, hC, hk⟩ => ⟨⟨C, hC⟩, (SetSystem.optCoverSize_le hC).trans hk⟩,
    fun ⟨hS, hk⟩ => (SetSystem.optCoverSize_le_iff hS).1 hk⟩

theorem card_filter_mem_le_card {n : ℕ} (I : Finset ℕ) :
    (Finset.univ.filter fun i : Fin n => (i : ℕ) ∈ I).card ≤ I.card :=
  Finset.card_le_card_of_injOn Fin.val
    (fun _ hi => (Finset.mem_filter.1 hi).2) (fun _ _ _ _ h => Fin.ext h)

private theorem filter_image_val_eq {n : ℕ} (C : Finset (Fin n)) :
    Finset.univ.filter (fun i : Fin n => (i : ℕ) ∈ C.image Fin.val) = C := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_image, true_and]
  exact ⟨fun ⟨j, hj, hij⟩ => Fin.ext hij ▸ hj, fun hi => ⟨i, hi, rfl⟩⟩

private theorem exists_fin_witness_iff {n : ℕ} {C_pred : Finset (Fin n) → Prop}
    {I_pred : Finset ℕ → Prop}
    (h_fwd : ∀ C, C_pred C → I_pred (C.image Fin.val))
    (h_bwd : ∀ I, (∀ v ∈ I, v ∈ List.range n) → I_pred I →
      C_pred (Finset.univ.filter fun i : Fin n => (i : ℕ) ∈ I)) :
    (∃ C, C_pred C) ↔
      ∃ I : Finset ℕ, (∀ v ∈ I, v ∈ List.range n) ∧ I_pred I := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C.image Fin.val, fun x hx => ?_, h_fwd C hC⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact List.mem_range.2 i.isLt
  · rintro ⟨I, hmem, hI⟩
    exact ⟨_, h_bwd I hmem hI⟩

/-- Unweighted Set Cover is in `NP` via subset witnesses over `List.range S.sets.length`. -/
theorem SetCover_mem_NP : SetCover ∈ NP encSetCover := by
  let vs : SetSystem × ℕ → List ℕ := fun p => List.range p.1.sets.length
  let check : (SetSystem × ℕ) × List ℕ → Bool := fun q =>
    decide (q.2.length ≤ q.1.2) && q.1.1.isCoverList q.2
  have hvs : ComputableInPolyTime vs encSetCover (encList encUnary) := by
    refine ComputableInPolyTime.range.comp ?_
    exact (ComputableInPolyTime.length_list (encList encNat)).comp
      (computableInPolyTime_setSystemSets.comp (fst encSetSystem encNat))
  have hcheck : ComputableInPolyTime check
      (encPair encSetCover (encList encUnary)) encBool := by
    have hlen : ComputableInPolyTime (fun q : (SetSystem × ℕ) × List ℕ => q.2.length)
        (encPair encSetCover (encList encUnary)) encNat :=
      ComputableInPolyTime.unary_to_binary.comp
        ((ComputableInPolyTime.length_list encUnary).comp (snd encSetCover (encList encUnary)))
    have hk : ComputableInPolyTime (fun q : (SetSystem × ℕ) × List ℕ => q.1.2)
        (encPair encSetCover (encList encUnary)) encNat :=
      (snd encSetSystem encNat).comp (fst encSetCover (encList encUnary))
    have hble : ComputableInPolyTime
        (fun q : (SetSystem × ℕ) × List ℕ => decide (q.2.length ≤ q.1.2))
        (encPair encSetCover (encList encUnary)) encBool :=
      ComputableInPolyTime.binary_le' hlen hk
    have hcov : ComputableInPolyTime (fun q : (SetSystem × ℕ) × List ℕ => q.1.1.isCoverList q.2)
        (encPair encSetCover (encList encUnary)) encBool :=
      SetSystem.computableInPolyTime_isCoverList.comp
        (((fst encSetSystem encNat).comp (fst encSetCover (encList encUnary))).prod
          (snd encSetCover (encList encUnary)))
    exact ComputableInPolyTime.bool_and' hble hcov
  let P : (SetSystem × ℕ) → Finset ℕ → Prop := fun p I =>
    p.1.IsCover (Finset.univ.filter fun i : Fin p.1.sets.length => (i : ℕ) ∈ I) ∧ I.card ≤ p.2
  have hP : ∀ (p : SetSystem × ℕ) (l : List ℕ), l.Nodup → (∀ i ∈ l, i ∈ vs p) →
      (check (p, l) = true ↔ P p l.toFinset) := by
    intro p l hnd hmem
    have hlt : ∀ i ∈ l, i < p.1.sets.length := fun i hi => List.mem_range.1 (hmem i hi)
    simp only [check, P, Bool.and_eq_true, decide_eq_true_eq,
      SetSystem.isCoverList_toFinset_iff p.1 hlt, List.toFinset_card_of_nodup hnd, and_comm]
  have hmem := mem_NP_of_subsetWitness (encγ := encUnary) (P := P) hvs hcheck hP
  have hEq : SetCover = {p | ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ vs p) ∧ P p S} := by
    ext ⟨S, k⟩
    exact exists_fin_witness_iff
      (fun C ⟨hcov, hcard⟩ => ⟨by rwa [filter_image_val_eq], Finset.card_image_le.trans hcard⟩)
      (fun I _ ⟨hcov, hcard⟩ => ⟨hcov, (card_filter_mem_le_card I).trans hcard⟩)
  rwa [hEq]

/-! ### Weighted set systems -/

/-- A candidate subset together with its nonnegative integer weight. -/
structure WeightedSet where
  /-- Elements contained in this candidate subset. -/
  elements : List ℕ
  /-- Weight incurred when selecting this subset. -/
  weight : ℕ
  deriving DecidableEq, Repr

/-- Framed encoding of a `WeightedSet` with binary elements and binary weight. -/
enc_structure encWeightedSet : WeightedSet where
  elements : (encList encNat),
  weight : encNat

@[fun_prop] theorem computableInPolyTime_weightedSetElements :
    ComputableInPolyTime WeightedSet.elements encWeightedSet (encList encNat) :=
  encWeightedSet_elements_deg.computableInPolyTime

@[fun_prop] theorem computableInPolyTime_weightedSetWeight :
    ComputableInPolyTime WeightedSet.weight encWeightedSet encNat :=
  encWeightedSet_weight_deg.computableInPolyTime

@[fun_prop] theorem computableInPolyTime_weightedSetMk {γ : Type} {enc : γ ↪ List Bool}
    {e : γ → List ℕ} {w : γ → ℕ}
    (he : ComputableInPolyTime e enc (encList encNat))
    (hw : ComputableInPolyTime w enc encNat) :
    ComputableInPolyTime (fun x => WeightedSet.mk (e x) (w x)) enc encWeightedSet :=
  encWeightedSet_mk_deg.computableInPolyTime.comp (he.prod hw)

/-- A finite weighted set system over natural-number elements. -/
structure WeightedSetSystem where
  /-- Elements of the ground set that must be covered. -/
  ground : List ℕ
  /-- Weighted candidate subsets available for covering `ground`. -/
  sets : List WeightedSet
  deriving DecidableEq, Repr

/-- Framed encoding of a `WeightedSetSystem`. -/
enc_structure encWeightedSetSystem : WeightedSetSystem where
  ground : (encList encNat),
  sets : (encList encWeightedSet)

/-- Framed pair of a `WeightedSetSystem` and a binary target weight bound `k`. -/
abbrev encWeightedSetCover : WeightedSetSystem × ℕ ↪ List Bool :=
  encPair encWeightedSetSystem encNat

@[fun_prop] theorem computableInPolyTime_weightedSetSystemGround :
    ComputableInPolyTime WeightedSetSystem.ground encWeightedSetSystem (encList encNat) :=
  encWeightedSetSystem_ground_deg.computableInPolyTime

@[fun_prop] theorem computableInPolyTime_weightedSetSystemSets :
    ComputableInPolyTime WeightedSetSystem.sets encWeightedSetSystem (encList encWeightedSet) :=
  encWeightedSetSystem_sets_deg.computableInPolyTime

@[fun_prop] theorem computableInPolyTime_weightedSetSystemMk {γ : Type} {enc : γ ↪ List Bool}
    {u : γ → List ℕ} {s : γ → List WeightedSet}
    (hu : ComputableInPolyTime u enc (encList encNat))
    (hs : ComputableInPolyTime s enc (encList encWeightedSet)) :
    ComputableInPolyTime (fun x => WeightedSetSystem.mk (u x) (s x)) enc encWeightedSetSystem :=
  encWeightedSetSystem_mk_deg.computableInPolyTime.comp (hu.prod hs)

namespace WeightedSetSystem

/-- Forget the weights of a `WeightedSetSystem` to obtain an unweighted `SetSystem`. -/
@[expose] def toSetSystem (W : WeightedSetSystem) : SetSystem :=
  ⟨W.ground, W.sets.map WeightedSet.elements⟩

@[fun_prop] theorem computableInPolyTime_toSetSystem :
    ComputableInPolyTime toSetSystem encWeightedSetSystem encSetSystem := by
  unfold toSetSystem
  apply computableInPolyTime_setSystemMk (by fun_prop)
  exact (ComputableInPolyTime.map computableInPolyTime_weightedSetElements).comp (by fun_prop)

/-- A selection of indices `C` covers `W` when every element of `W.ground` belongs to
`W.sets[i].elements` for some `i ∈ C`. -/
@[expose] def IsCover (W : WeightedSetSystem) (C : Finset (Fin W.sets.length)) : Prop :=
  ∀ u ∈ W.ground, ∃ i ∈ C, u ∈ W.sets[i].elements

/-- A weighted set system is coverable when some finite index selection covers its ground set. -/
@[expose] def Coverable (W : WeightedSetSystem) : Prop :=
  ∃ C : Finset (Fin W.sets.length), W.IsCover C

/-- Total weight of a selection `C` of sets in `W`. -/
@[expose] def coverWeight (W : WeightedSetSystem) (C : Finset (Fin W.sets.length)) : ℕ :=
  ∑ i ∈ C, W.sets[i].weight

theorem isCover_toSetSystem_iff (W : WeightedSetSystem) (C : Finset (Fin W.sets.length)) :
    W.toSetSystem.IsCover (C.map ⟨fun i : Fin W.sets.length =>
        (⟨i.1, by simp [toSetSystem]⟩ : Fin W.toSetSystem.sets.length),
      fun _ _ h => Fin.ext (congrArg (Fin.val : Fin W.toSetSystem.sets.length → ℕ) h)⟩) ↔
      W.IsCover C := by
  constructor
  · intro h u hu
    obtain ⟨j, hj, huj⟩ := h u hu
    obtain ⟨i, hi, hij⟩ := Finset.mem_map.1 hj
    have huv : u ∈ W.toSetSystem.sets[(j : ℕ)]'j.isLt := huj
    simp only [toSetSystem, List.getElem_map] at huv
    have hij' : (i : ℕ) = (j : ℕ) := congrArg Fin.val hij
    refine ⟨i, hi, ?_⟩
    simpa [hij'] using huv
  · intro h u hu
    obtain ⟨i, hi, hui⟩ := h u hu
    refine ⟨⟨i.1, by simp [toSetSystem]⟩, Finset.mem_map.2 ⟨i, hi, rfl⟩, ?_⟩
    simpa [toSetSystem] using hui

theorem coverable_iff_toSetSystem (W : WeightedSetSystem) :
    W.Coverable ↔ W.toSetSystem.Coverable := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨_, (isCover_toSetSystem_iff W C).2 hC⟩
  · rintro ⟨C, hC⟩
    refine ⟨Finset.univ.filter (fun i : Fin W.sets.length =>
      (⟨i.1, by simp [toSetSystem]⟩ : Fin W.toSetSystem.sets.length) ∈ C), fun u hu => ?_⟩
    obtain ⟨j, hjC, huj⟩ := hC u hu
    have hj : j.1 < W.sets.length := by simpa [toSetSystem] using j.isLt
    have h0 : u ∈ (W.sets.map WeightedSet.elements)[j.1]'(by simpa [toSetSystem] using j.isLt) :=
      huj
    rw [List.getElem_map] at h0
    exact ⟨⟨j.1, hj⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hjC⟩, h0⟩

/-- Boolean test for whether `W` is coverable. -/
@[expose] def coverableBool (W : WeightedSetSystem) : Bool :=
  W.toSetSystem.coverableBool

theorem coverableBool_eq_true_iff (W : WeightedSetSystem) :
    W.coverableBool = true ↔ W.Coverable := by
  rw [coverableBool, SetSystem.coverableBool_eq_true_iff, ← coverable_iff_toSetSystem]

@[fun_prop] theorem computableInPolyTime_coverableBool :
    ComputableInPolyTime coverableBool encWeightedSetSystem encBool :=
  SetSystem.computableInPolyTime_coverableBool.comp computableInPolyTime_toSetSystem

/-- Minimum weight of a cover of `W` when `W.Coverable` holds (and `0` otherwise). -/
noncomputable def optCoverWeight (W : WeightedSetSystem) : ℕ :=
  open Classical in
  if h : W.Coverable then
    Nat.find (⟨W.coverWeight h.choose, h.choose, h.choose_spec, le_rfl⟩ :
      ∃ w : ℕ, ∃ C : Finset (Fin W.sets.length), W.IsCover C ∧ W.coverWeight C ≤ w)
  else 0

theorem optCoverWeight_le {W : WeightedSetSystem} {C : Finset (Fin W.sets.length)}
    (hC : W.IsCover C) : W.optCoverWeight ≤ W.coverWeight C := by
  classical
  have hW : W.Coverable := ⟨C, hC⟩
  rw [optCoverWeight]
  split_ifs
  exact Nat.find_min' _ ⟨C, hC, le_rfl⟩

theorem optCoverWeight_eq_zero_of_not_coverable {W : WeightedSetSystem} (hW : ¬ W.Coverable) :
    W.optCoverWeight = 0 := by
  classical
  rw [optCoverWeight]
  split_ifs
  rfl

theorem exists_isCover_optCoverWeight {W : WeightedSetSystem} (hW : W.Coverable) :
    ∃ C : Finset (Fin W.sets.length), W.IsCover C ∧ W.coverWeight C = W.optCoverWeight := by
  classical
  rw [optCoverWeight]
  split_ifs
  obtain ⟨C, hC, hwt⟩ := Nat.find_spec
    (⟨W.coverWeight hW.choose, hW.choose, hW.choose_spec, le_rfl⟩ :
      ∃ w : ℕ, ∃ C : Finset (Fin W.sets.length), W.IsCover C ∧ W.coverWeight C ≤ w)
  have hmin : Nat.find (⟨W.coverWeight hW.choose, hW.choose, hW.choose_spec, le_rfl⟩ :
      ∃ w : ℕ, ∃ C : Finset (Fin W.sets.length), W.IsCover C ∧ W.coverWeight C ≤ w) ≤
      W.coverWeight C := Nat.find_min' _ ⟨C, hC, le_rfl⟩
  exact ⟨C, hC, le_antisymm hwt hmin⟩

theorem optCoverWeight_le_iff {W : WeightedSetSystem} (hW : W.Coverable) {k : ℕ} :
    W.optCoverWeight ≤ k ↔
      ∃ C : Finset (Fin W.sets.length), W.IsCover C ∧ W.coverWeight C ≤ k := by
  refine ⟨fun h => ?_, fun ⟨C, hC, hk⟩ => (optCoverWeight_le hC).trans hk⟩
  obtain ⟨C, hC, hwt⟩ := exists_isCover_optCoverWeight hW
  exact ⟨C, hC, hwt ▸ h⟩

theorem le_optCoverWeight_iff {W : WeightedSetSystem} (hW : W.Coverable) {k : ℕ} :
    k ≤ W.optCoverWeight ↔
      ∀ C : Finset (Fin W.sets.length), W.IsCover C → k ≤ W.coverWeight C := by
  refine ⟨fun hk C hC => hk.trans (optCoverWeight_le hC), fun h => ?_⟩
  obtain ⟨C, hC, hwt⟩ := exists_isCover_optCoverWeight hW
  rw [← hwt]
  exact h C hC

/-- Indices chosen by `Cslib.Algorithms.Lean.SetCover.greedy` on `W`. -/
@[expose] noncomputable def greedyIndices (W : WeightedSetSystem) : List (Fin W.sets.length) :=
  Cslib.Algorithms.Lean.SetCover.greedy (fun i : Fin W.sets.length => W.sets[i].elements.toFinset)
    (fun i => (W.sets[i].weight : ℝ)) (List.finRange W.sets.length) W.ground.toFinset

theorem greedyIndices_isCover {W : WeightedSetSystem} (hW : W.Coverable) :
    W.IsCover W.greedyIndices.toFinset := by
  intro u hu
  have hcov := Cslib.Algorithms.Lean.SetCover.greedy_covers
    (S := fun i : Fin W.sets.length => W.sets[i].elements.toFinset)
    (w := fun i => (W.sets[i].weight : ℝ)) (J := List.finRange W.sets.length)
    (U := W.ground.toFinset)
    (fun a ha => by
      obtain ⟨C, hC⟩ := hW
      obtain ⟨i, -, hui⟩ := hC a (List.mem_toFinset.1 ha)
      exact ⟨i, List.mem_finRange i, List.mem_toFinset.2 hui⟩)
    u (List.mem_toFinset.2 hu)
  obtain ⟨i, hi, hui⟩ := hcov
  exact ⟨i, List.mem_toFinset.2 hi, List.mem_toFinset.1 hui⟩

theorem greedyWeight_le_one_add_log {W : WeightedSetSystem} (hW : W.Coverable) :
    (W.coverWeight W.greedyIndices.toFinset : ℝ) ≤
      (1 + Real.log W.ground.toFinset.card) * W.optCoverWeight := by
  obtain ⟨C, hC, hwt⟩ := exists_isCover_optCoverWeight hW
  have h := Cslib.Algorithms.Lean.SetCover.sum_greedy_le_one_add_log_mul
    (S := fun i : Fin W.sets.length => W.sets[i].elements.toFinset)
    (w := fun i => (W.sets[i].weight : ℝ))
    (J := List.finRange W.sets.length) (U := W.ground.toFinset) (C := C)
    (d := W.ground.toFinset.card) (fun i _ => Nat.cast_nonneg _)
    (fun j _ => List.mem_finRange j)
    (fun a ha => by
      obtain ⟨i, hi, hai⟩ := hC a (List.mem_toFinset.1 ha)
      exact ⟨i, hi, List.mem_toFinset.2 hai⟩)
    (fun j _ => Finset.card_le_card Finset.inter_subset_right)
  have hnd : W.greedyIndices.Nodup := Cslib.Algorithms.Lean.SetCover.nodup_greedy
  have hsum : (W.greedyIndices.map fun i => (W.sets[i].weight : ℝ)).sum =
      (W.coverWeight W.greedyIndices.toFinset : ℝ) := by
    rw [coverWeight, Nat.cast_sum, ← List.sum_toFinset _ hnd]
  change (W.greedyIndices.map fun i => (W.sets[i].weight : ℝ)).sum ≤ _ at h
  rw [← hsum]
  refine h.trans (le_of_eq ?_)
  rw [← hwt, coverWeight, Nat.cast_sum]

end WeightedSetSystem

/-- **Weighted Set Cover**: pairs `(W, k)` admitting a cover of `W.ground` of total weight at
most `k`. -/
@[expose] def WeightedSetCover : Set (WeightedSetSystem × ℕ) :=
  {p | ∃ C : Finset (Fin p.1.sets.length), p.1.IsCover C ∧ p.1.coverWeight C ≤ p.2}

theorem mem_WeightedSetCover_iff {W : WeightedSetSystem} {k : ℕ} :
    (W, k) ∈ WeightedSetCover ↔
      ∃ C : Finset (Fin W.sets.length), W.IsCover C ∧ W.coverWeight C ≤ k :=
  Iff.rfl

theorem mem_WeightedSetCover_iff_optCoverWeight {W : WeightedSetSystem} {k : ℕ} :
    (W, k) ∈ WeightedSetCover ↔ W.Coverable ∧ W.optCoverWeight ≤ k := by
  refine ⟨fun ⟨C, hC, hk⟩ => ⟨⟨C, hC⟩, (WeightedSetSystem.optCoverWeight_le hC).trans hk⟩,
    fun ⟨hW, hk⟩ => (WeightedSetSystem.optCoverWeight_le_iff hW).1 hk⟩

private theorem sum_weight_eq_coverWeight (W : WeightedSetSystem) {l : List ℕ} (hnd : l.Nodup)
    (hlt : ∀ i ∈ l, i < W.sets.length) :
    (l.map fun i => (W.sets.getD i ⟨[], 0⟩).weight).sum =
      W.coverWeight (Finset.univ.filter fun i : Fin W.sets.length => (i : ℕ) ∈ l.toFinset) := by
  rw [WeightedSetSystem.coverWeight, ← List.sum_toFinset _ hnd]
  symm
  refine Finset.sum_bij (fun i _ => (i : ℕ))
    (fun i hi => by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi)
    (fun i _ j _ hij => Fin.ext hij)
    (fun x hx => by
      have hx' := List.mem_toFinset.1 hx
      exact ⟨⟨x, hlt x hx'⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩, rfl⟩)
    (fun i _ => by
      simp only [List.getD_eq_getElem _ _ i.isLt]
      rfl)

private theorem toSetSystem_isCover_filter_iff (W : WeightedSetSystem) (I : Finset ℕ) :
    W.toSetSystem.IsCover (Finset.univ.filter fun i : Fin W.toSetSystem.sets.length =>
      (i : ℕ) ∈ I) ↔
      W.IsCover (Finset.univ.filter fun i : Fin W.sets.length => (i : ℕ) ∈ I) := by
  constructor
  · intro h u hu
    obtain ⟨i, hi, hui⟩ := h u hu
    have hiI : (i : ℕ) ∈ I := (Finset.mem_filter.1 hi).2
    have hi' : i.1 < W.sets.length := by simpa [WeightedSetSystem.toSetSystem] using i.isLt
    have h0 : u ∈ (W.sets.map WeightedSet.elements)[i.1]'(by
        simpa [WeightedSetSystem.toSetSystem] using i.isLt) := hui
    rw [List.getElem_map] at h0
    exact ⟨⟨i.1, hi'⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hiI⟩, h0⟩
  · intro h u hu
    obtain ⟨i, hi, hui⟩ := h u hu
    have hiI : (i : ℕ) ∈ I := (Finset.mem_filter.1 hi).2
    refine ⟨⟨i.1, by simp [WeightedSetSystem.toSetSystem, i.isLt]⟩,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hiI⟩, ?_⟩
    simpa [WeightedSetSystem.toSetSystem] using hui

/-- Weighted Set Cover is in `NP` via subset witnesses over `List.range W.sets.length`. -/
theorem WeightedSetCover_mem_NP : WeightedSetCover ∈ NP encWeightedSetCover := by
  let vs : WeightedSetSystem × ℕ → List ℕ := fun p => List.range p.1.sets.length
  let check : (WeightedSetSystem × ℕ) × List ℕ → Bool := fun q =>
    decide ((q.2.map fun i => (q.1.1.sets.getD i ⟨[], 0⟩).weight).sum ≤ q.1.2) &&
      q.1.1.toSetSystem.isCoverList q.2
  have hvs : ComputableInPolyTime vs encWeightedSetCover (encList encUnary) := by
    refine ComputableInPolyTime.range.comp ?_
    exact (ComputableInPolyTime.length_list encWeightedSet).comp
      (computableInPolyTime_weightedSetSystemSets.comp (fst encWeightedSetSystem encNat))
  have hcheck : ComputableInPolyTime check
      (encPair encWeightedSetCover (encList encUnary)) encBool := by
    have hws : ComputableInPolyTime
        (fun q : (WeightedSetSystem × ℕ) × List ℕ =>
          q.2.map fun i => (q.1.1.sets.getD i ⟨[], 0⟩).weight)
        (encPair encWeightedSetCover (encList encUnary)) (encList encNat) := by
      apply ComputableInPolyTime.mapWithInput (by fun_prop)
      have hlist : ComputableInPolyTime
          (fun r : ((WeightedSetSystem × ℕ) × List ℕ) × ℕ => r.1.1.1.sets)
          (encPair (encPair encWeightedSetCover (encList encUnary)) encUnary)
          (encList encWeightedSet) := by fun_prop
      have hidx : ComputableInPolyTime
          (fun r : ((WeightedSetSystem × ℕ) × List ℕ) × ℕ => r.2)
          (encPair (encPair encWeightedSetCover (encList encUnary)) encUnary) encUnary := by
        fun_prop
      have hset : ComputableInPolyTime
          (fun r : ((WeightedSetSystem × ℕ) × List ℕ) × ℕ =>
            r.1.1.1.sets.getD r.2 ⟨[], 0⟩)
          (encPair (encPair encWeightedSetCover (encList encUnary)) encUnary)
          encWeightedSet :=
        ComputableInPolyTime.listGetDWithInput hlist hidx ⟨[], 0⟩
      exact computableInPolyTime_weightedSetWeight.comp hset
    have hsum : ComputableInPolyTime
        (fun q : (WeightedSetSystem × ℕ) × List ℕ =>
          (q.2.map fun i => (q.1.1.sets.getD i ⟨[], 0⟩).weight).sum)
        (encPair encWeightedSetCover (encList encUnary)) encNat :=
      (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.binary_sum).comp hws
    have hk : ComputableInPolyTime (fun q : (WeightedSetSystem × ℕ) × List ℕ => q.1.2)
        (encPair encWeightedSetCover (encList encUnary)) encNat :=
      (snd encWeightedSetSystem encNat).comp (fst encWeightedSetCover (encList encUnary))
    have hble : ComputableInPolyTime
        (fun q : (WeightedSetSystem × ℕ) × List ℕ =>
          decide ((q.2.map fun i => (q.1.1.sets.getD i ⟨[], 0⟩).weight).sum ≤ q.1.2))
        (encPair encWeightedSetCover (encList encUnary)) encBool :=
      ComputableInPolyTime.binary_le' hsum hk
    have hcov : ComputableInPolyTime
        (fun q : (WeightedSetSystem × ℕ) × List ℕ => q.1.1.toSetSystem.isCoverList q.2)
        (encPair encWeightedSetCover (encList encUnary)) encBool :=
      SetSystem.computableInPolyTime_isCoverList.comp
        ((WeightedSetSystem.computableInPolyTime_toSetSystem.comp
            ((fst encWeightedSetSystem encNat).comp
              (fst encWeightedSetCover (encList encUnary)))).prod
          (snd encWeightedSetCover (encList encUnary)))
    exact ComputableInPolyTime.bool_and' hble hcov
  let P : (WeightedSetSystem × ℕ) → Finset ℕ → Prop := fun p I =>
    p.1.IsCover (Finset.univ.filter fun i : Fin p.1.sets.length => (i : ℕ) ∈ I) ∧
      p.1.coverWeight (Finset.univ.filter fun i : Fin p.1.sets.length => (i : ℕ) ∈ I) ≤ p.2
  have hP : ∀ (p : WeightedSetSystem × ℕ) (l : List ℕ), l.Nodup → (∀ i ∈ l, i ∈ vs p) →
      (check (p, l) = true ↔ P p l.toFinset) := by
    intro p l hnd hmem
    have hlt : ∀ i ∈ l, i < p.1.sets.length := fun i hi => List.mem_range.1 (hmem i hi)
    have hlt' : ∀ i ∈ l, i < p.1.toSetSystem.sets.length := fun i hi => by
      simpa [WeightedSetSystem.toSetSystem] using hlt i hi
    simp only [check, P, Bool.and_eq_true, decide_eq_true_eq,
      SetSystem.isCoverList_toFinset_iff p.1.toSetSystem hlt',
      sum_weight_eq_coverWeight p.1 hnd hlt]
    rw [and_comm]
    exact and_congr (toSetSystem_isCover_filter_iff p.1 l.toFinset) Iff.rfl
  have hmem := mem_NP_of_subsetWitness (encγ := encUnary) (P := P) hvs hcheck hP
  have hEq : WeightedSetCover = {p | ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ vs p) ∧ P p S} := by
    ext ⟨W, k⟩
    exact exists_fin_witness_iff
      (fun C ⟨hcov, hwt⟩ => ⟨by rwa [filter_image_val_eq], by rwa [filter_image_val_eq]⟩)
      (fun _ _ h => h)
  rwa [hEq]

end Cslib.Complexity
