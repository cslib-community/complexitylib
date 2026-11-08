/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceEntry
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sigma

/-!
# Distinct incidences in the executable selection procedure

The block decoder selects sublists of its actual incidence lists. Row blocks partition incidences
by variable group, and each variable occurs once in a test scope. Thus selections of constructed
rows have no duplicates, without a canonical-input or valid-index premise. This supplies the
structural hypothesis for coefficient extraction in [OpenAI2026ETH], Lemma D.2 (pp. 55–56).

## Main results

* `Cslib.Circuits.Frontier.IncidenceNetwork.selected_sublist`: block decoding only removes
  occurrences from the actual concatenated incidence list.
* `Cslib.Circuits.Frontier.IncidenceNetwork.nodup_selected_rowBlocks`: constructed-row
  selections have no duplicates, on valid and invalid indices alike.
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open Cslib.Complexity

/-- Selecting positions of a word preserves incidence order and introduces no new occurrence. -/
theorem chosenBy_sublist (sel : List (ℕ × ℕ)) (w : List Bool) :
    List.Sublist (chosenBy sel w) sel := by
  induction sel generalizing w with
  | nil => simp [chosenBy]
  | cons a sel ih =>
    cases w with
    | nil => simp [chosenBy]
    | cons b w =>
      cases b
      · simpa [chosenBy] using (ih w).cons a
      · simpa [chosenBy] using (ih w).cons_cons a

/-- Block unranking and selection only remove entries of the actual block. -/
theorem selectBlock_sublist (b : Block) (i : ℕ) : List.Sublist (selectBlock b i) b.1 :=
  chosenBy_sublist b.1 (Cslib.BitString.unrankCombination b.1.length b.2 i)

/-- Multi-block selection is a sublist of the concatenation, including truncated index lists. -/
theorem selected_sublist (blocks : List Block) (idx : List ℕ) :
    List.Sublist (selected blocks idx) (blocks.flatMap Prod.fst) := by
  induction blocks generalizing idx with
  | nil => simp [selected]
  | cons b blocks ih =>
    cases idx with
    | nil => simp [selected]
    | cons i idx =>
      simp only [selected, List.zip_cons_cons, List.flatMap_cons]
      exact (selectBlock_sublist b i).append (ih idx)

/-- A pair of groups has no repeated incidence: scope deduplication and local test positions
separate the entries, even when the original test list has repeated rows or variables. -/
theorem nodup_pairInc (J : ℕ) (sys : List (List (List ℕ))) (g h : ℕ) :
    (pairInc J sys g h).Nodup := by
  unfold pairInc
  apply List.nodup_flatMap.mpr
  constructor
  · intro p hp
    apply List.Nodup.map (fun a b hab => congrArg Prod.snd hab)
    exact (nodup_sortDedup _).filter _
  · have hs := List.nodup_zipIdx_map_snd (List.residueClass J sys.length g)
    change ((List.residueClass J sys.length g).zipIdx.map Prod.snd).Pairwise (· ≠ ·) at hs
    have hs' := List.pairwise_map.mp hs
    apply hs'.imp
    intro p q hpq
    change List.Disjoint _ _
    rw [List.disjoint_left]
    intro v hv hw
    obtain ⟨a, _, ha⟩ := List.mem_map.mp hv
    obtain ⟨b, _, hb⟩ := List.mem_map.mp hw
    exact hpq (congrArg Prod.fst (ha.trans hb.symm))

/-- Membership in a group pair determines the variable's group. -/
theorem mod_eq_of_mem_pairInc {J g h : ℕ} {sys : List (List (List ℕ))}
    {p : ℕ × ℕ} (hp : p ∈ pairInc J sys g h) : p.2 % J = h := by
  obtain ⟨q, _, hq⟩ := List.mem_flatMap.mp hp
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hq
  exact of_decide_eq_true (List.mem_filter.mp hv).2

/-- All blocks of a constructed row together have no repeated incidence. -/
theorem nodup_rowBlocks (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ) (g : ℕ) :
    ((rowBlocks J sys d g).flatMap Prod.fst).Nodup := by
  simp only [rowBlocks, List.flatMap_map]
  apply List.nodup_flatMap.mpr
  refine ⟨fun h _ => nodup_pairInc J sys g h, ?_⟩
  apply (show (List.range J).Pairwise (· ≠ ·) from List.nodup_range).imp
  intro h h' hne
  change List.Disjoint _ _
  rw [List.disjoint_left]
  intro p hp hp'
  exact hne ((mod_eq_of_mem_pairInc hp).symm.trans (mod_eq_of_mem_pairInc hp'))

/-- Distinctness of the actually selected incidences of a constructed row requires no advice. -/
theorem nodup_selected_rowBlocks (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ)
    (g : ℕ) (idx : List ℕ) : (selected (rowBlocks J sys d g) idx).Nodup :=
  (nodup_rowBlocks J sys d g).sublist (selected_sublist _ _)

end Cslib.Circuits.Frontier.IncidenceNetwork
