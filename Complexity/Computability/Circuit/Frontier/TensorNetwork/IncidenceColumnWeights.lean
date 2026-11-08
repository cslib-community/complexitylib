/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceEntryCorrectness
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceWireDecoding
import Complexity.Foundations.Data.List.Blocks
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Actual column entries give the global free-variable weight

The residue classes partition all declared variables. Incidences selected by one constructed
column belong to its variable class. Thus a variable is unselected by that column exactly when
it is unselected globally. Multiplying actual column entries gives two for each globally free
variable, including variables outside all scopes ([OpenAI2026ETH], Lemma D.2, PDF p.56).

## Main definitions

* `Cslib.Circuits.Frontier.IncidenceNetwork.columnSelected`: the actual decoded column selection.
* `Cslib.Circuits.Frontier.IncidenceNetwork.allColumnSelected`: all those selections together.
* `Cslib.Circuits.Frontier.IncidenceNetwork.allRowSelected`: the corresponding actual row choices.

## Main results

* `Cslib.Circuits.Frontier.IncidenceNetwork.mem_allColumnSelected_iff_rows`: row and column
  selections agree on membership by actual common-wire decoding.
* `Cslib.Circuits.Frontier.IncidenceNetwork.sum_unselected_columns`: every free variable is
  counted in exactly one column.
* `Cslib.Circuits.Frontier.IncidenceNetwork.val_colVertices_prod`: actual column entries multiply
  to the global free-variable weight in the truncated ring.

## References

* [OpenAI2026ETH], Appendix D.3, Lemma D.2, PDF p.56.
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open DescribedNetwork GaloisRingArith

/-- The actual selection read by column `h` from the shared physical wire assignment. -/
@[expose] def columnSelected (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ)
    (word : List Bool) (h : ℕ) : List (ℕ × ℕ) :=
  selected (colBlocks J sys d h)
    (blockIndices (colBlocks J sys d h) (wordBits word (colPorts J sys d h)))

/-- All selected column incidences. Their second coordinates determine which variables are free. -/
@[expose] def allColumnSelected (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ)
    (word : List Bool) : List (ℕ × ℕ) :=
  (List.range J).flatMap (columnSelected J sys d word)

/-- The actual selected incidences at a test-group endpoint. -/
@[expose] def rowSelected (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ)
    (word : List Bool) (g : ℕ) : List (ℕ × ℕ) :=
  selected (rowBlocks J sys d g)
    (blockIndices (rowBlocks J sys d g) (wordBits word (rowPorts J sys d g)))

/-- All actual row selections, whose test coefficients occur in the global product. -/
@[expose] def allRowSelected (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ)
    (word : List Bool) : List (ℕ × ℕ) :=
  (List.range J).flatMap (rowSelected J sys d word)

/-- Both endpoints select the same incidence at every group pair, even on invalid ranks.
Only order changes when all row groups and all column groups are concatenated. -/
theorem mem_allColumnSelected_iff_rows (J : ℕ) (sys : List (List (List ℕ)))
    (d : List ℕ) (word : List Bool) (p : ℕ × ℕ) :
    p ∈ allColumnSelected J sys d word ↔ p ∈ allRowSelected J sys d word := by
  constructor
  · intro hp
    obtain ⟨h, hh, hp⟩ := List.mem_flatMap.mp hp
    unfold columnSelected at hp
    rw [blockIndices_colPorts J sys d word h (List.mem_range.mp hh), colBlocks, selected,
      List.zip_map', List.flatMap_map] at hp
    obtain ⟨g, hg, hp⟩ := List.mem_flatMap.mp hp
    apply List.mem_flatMap.mpr
    refine ⟨g, hg, ?_⟩
    unfold rowSelected
    rw [blockIndices_rowPorts, rowBlocks, selected, List.zip_map', List.flatMap_map]
    exact List.mem_flatMap.mpr ⟨h, hh, hp⟩
  · intro hp
    obtain ⟨g, hg, hp⟩ := List.mem_flatMap.mp hp
    unfold rowSelected at hp
    rw [blockIndices_rowPorts, rowBlocks, selected, List.zip_map', List.flatMap_map] at hp
    obtain ⟨h, hh, hp⟩ := List.mem_flatMap.mp hp
    apply List.mem_flatMap.mpr
    refine ⟨h, hh, ?_⟩
    unfold columnSelected
    rw [blockIndices_colPorts J sys d word h (List.mem_range.mp hh), colBlocks, selected,
      List.zip_map', List.flatMap_map]
    exact List.mem_flatMap.mpr ⟨g, hg, hp⟩

private theorem unselectedCount_eq_rows (J : ℕ) (sys : List (List (List ℕ)))
    (d : List ℕ) (word : List Bool) (vars : List ℕ) :
    unselectedCount vars (allColumnSelected J sys d word) =
      unselectedCount vars (allRowSelected J sys d word) := by
  simp only [unselectedCount, List.mem_map, mem_allColumnSelected_iff_rows]

private theorem mod_columnSelected {J h : ℕ} {sys : List (List (List ℕ))} {d : List ℕ}
    {word : List Bool} {p : ℕ × ℕ} (hp : p ∈ columnSelected J sys d word h) : p.2 % J = h := by
  have hs := (selected_sublist (colBlocks J sys d h) _).subset hp
  obtain ⟨b, hb, hp⟩ := List.mem_flatMap.mp hs
  obtain ⟨g, _, rfl⟩ := List.mem_map.mp hb
  exact mod_eq_of_mem_pairInc hp

private theorem mem_allColumnSelected_iff {J h v : ℕ} {sys : List (List (List ℕ))}
    {d : List ℕ} {word : List Bool} (hh : h < J) (hv : v % J = h) :
    v ∈ (allColumnSelected J sys d word).map Prod.snd ↔
      v ∈ (columnSelected J sys d word h).map Prod.snd := by
  constructor
  · intro hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
    obtain ⟨g, _, hp⟩ := List.mem_flatMap.mp hp
    have hg : g = h := (mod_columnSelected hp).symm.trans hv
    subst g
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  · intro hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
    exact List.mem_map.mpr ⟨p, List.mem_flatMap.mpr ⟨h, List.mem_range.mpr hh, hp⟩, rfl⟩

private theorem unselectedCount_eq_sum (vars : List ℕ) (sel : List (ℕ × ℕ)) :
    unselectedCount vars sel = (vars.map fun v => if v ∉ sel.map Prod.snd then 1 else 0).sum := by
  rw [unselectedCount, List.countP_eq_length_filter, List.length_filter_eq_sum]
  simp only [decide_eq_true_eq]

/-- The actual columns count each globally unselected declared variable exactly once. -/
theorem sum_unselected_columns (J n : ℕ) (hJ : 0 < J) (sys : List (List (List ℕ)))
    (d : List ℕ) (word : List Bool) :
    (∑ h ∈ Finset.range J, unselectedCount (List.residueClass J n h)
      (columnSelected J sys d word h)) =
        unselectedCount (List.range n) (allColumnSelected J sys d word) := by
  simp only [unselectedCount_eq_sum]
  calc
    _ = ∑ h ∈ Finset.range J,
        ((List.residueClass J n h).map fun v =>
          if v ∉ (allColumnSelected J sys d word).map Prod.snd then 1 else 0).sum := by
      apply Finset.sum_congr rfl
      intro h hh
      apply congrArg List.sum
      apply List.map_congr_left
      intro v hv
      have hm := of_decide_eq_true (List.mem_filter.mp hv).2
      simp only [mem_allColumnSelected_iff (List.mem_range.mp hh) hm]
    _ = _ := List.sum_residueClass hJ n _

/-- The product of actual column entries is the exact global free-variable weight, represented
in the same truncated ring as the row coefficients. No supplied selection correspondence is used. -/
theorem val_colVertices_prod (P ℓ J n : ℕ) (hJ : 0 < J)
    (sys : List (List (List ℕ))) (d : List ℕ) (word : List Bool) :
    (∏ h ∈ Finset.range J, val P (truncFl ℓ)
      (incEntry (colVertex P J n sys d h).2 (wordBits word (colPorts J sys d h)))) =
        (2 : Ring P (truncFl ℓ)) ^ unselectedCount (List.range n)
          (allRowSelected J sys d word) := by
  simp only [colVertex, incEntry_inr_inl, val_colEntry]
  rw [Finset.prod_pow_eq_pow_sum]
  exact congrArg (fun a : ℕ => (2 : Ring P (truncFl ℓ)) ^ a)
    ((sum_unselected_columns J n hJ sys d word).trans
      (unselectedCount_eq_rows J sys d word (List.range n)))

end Cslib.Circuits.Frontier.IncidenceNetwork
