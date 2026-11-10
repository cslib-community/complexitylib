/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/Ramsey.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Ramsey.Basic
import CslibFrontier.Foundations.Combinatorics.SetFamily.Oddtown
import Mathlib.Data.Fintype.Powerset

/-!
# Nagy's explicit Ramsey graph

Nagy's graph on a finite type `α` has the `3`-element subsets of `α` as vertices, two of them
adjacent when they meet in exactly one point. With `t = |α|`:

* a clique is a family of `3`-sets pairwise meeting in exactly one point, so it has at most `t`
  members by the uniform Fisher inequality;
* an independent set is a family of `3`-sets whose distinct members meet in `0` or `2` points (they
  cannot meet in `3`), an oddtown family, so it has at most `t` members.

So the graph has `C(t, 3)` vertices and neither a clique nor an independent set of size `t + 1`,
whence `C(t, 3) < R(t + 1, t + 1)` [Nagy1972] [Jukna2011, §13.7]. This beats the easy explicit
construction, `t` disjoint cliques of size `t`, which gives only `t ^ 2 < R(t + 1, t + 1)`.
Erdős's bound gives `2 ^ ((t + 1) / 2) < R(t + 1, t + 1)`
(`SimpleGraph.two_rpow_half_lt_ramseyNumber`) but no graph.

## Main definitions

* `SimpleGraph.nagyGraph α`: Nagy's graph on the `3`-subsets of `α`.

## Main results

* `SimpleGraph.cliqueFree_nagyGraph`: no clique of size `|α| + 1`.
* `SimpleGraph.indepSetFree_nagyGraph`: no independent set of size `|α| + 1`.
* `SimpleGraph.choose_three_lt_ramseyNumber`: `C(t, 3) < R(t + 1, t + 1)`.

## References

* [S. Jukna, *Extremal Combinatorics*][Jukna2011]
* [Zs. Nagy, *A constructive estimation of the Ramsey numbers*][Nagy1972]
-/

public section

open Finset

namespace SimpleGraph

/-- **Nagy's graph**: the `3`-element subsets of `α`, two of them adjacent when they meet in
exactly one point [Nagy1972] [Jukna2011, §13.7]. -/
def nagyGraph (α : Type*) [DecidableEq α] : SimpleGraph {s : Finset α // #s = 3} where
  Adj s s' := #(s.1 ∩ s'.1) = 1
  symm := ⟨fun s s' h => by rwa [inter_comm]⟩
  loopless := ⟨fun s h => by rw [inter_self, s.2] at h; omega⟩

variable {α : Type*} [DecidableEq α]

theorem nagyGraph_adj {s s' : {s : Finset α // #s = 3}} :
    (nagyGraph α).Adj s s' ↔ #(s.1 ∩ s'.1) = 1 := Iff.rfl

variable [Fintype α]

/-- Nagy's graph has no clique of size `|α| + 1`, by the uniform Fisher inequality. -/
theorem cliqueFree_nagyGraph : (nagyGraph α).CliqueFree (Fintype.card α + 1) := by
  intro t ht
  have h := Fintype.card_le_of_card_eq_of_card_inter_eq (ι := t) (fun s => s.1.1)
    (d := 3) (c := 1) (by omega) (fun s => s.1.2) (fun i j hij => ?_)
  · rw [Fintype.card_coe, ht.2] at h
    omega
  · exact ht.1 i.2 j.2 (fun h => hij (Subtype.ext h))

/-- Nagy's graph has no independent set of size `|α| + 1`, by the oddtown theorem. -/
theorem indepSetFree_nagyGraph : (nagyGraph α).IndepSetFree (Fintype.card α + 1) := by
  intro t ht
  have h := Fintype.card_le_of_odd_card_of_even_card_inter (ι := t) (fun s => s.1.1)
    (fun s => by rw [s.1.2]; decide) (fun i j hij => ?_)
  · rw [Fintype.card_coe, ht.2] at h
    omega
  · have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    have hna : #(i.1.1 ∩ j.1.1) ≠ 1 := ht.1 i.2 j.2 hne
    have hle : #(i.1.1 ∩ j.1.1) ≤ 3 := (card_le_card inter_subset_left).trans_eq i.1.2
    have hne3 : #(i.1.1 ∩ j.1.1) ≠ 3 := by
      intro h3
      have hsub : i.1.1 ⊆ j.1.1 :=
        inter_eq_left.1 (eq_of_subset_of_card_le inter_subset_left (by rw [h3, i.1.2]))
      exact hne (Subtype.ext (eq_of_subset_of_card_le hsub (by rw [i.1.2, j.1.2])))
    rcases (by omega : #(i.1.1 ∩ j.1.1) = 0 ∨ #(i.1.1 ∩ j.1.1) = 2) with h0 | h2
    · rw [h0]; exact Even.zero
    · rw [h2]; exact even_two

/-- **Nagy's bound**: `C(t, 3) < R(t + 1, t + 1)`, witnessed by `SimpleGraph.nagyGraph (Fin t)`
[Nagy1972] [Jukna2011, §13.7]. -/
theorem choose_three_lt_ramseyNumber (t : ℕ) : t.choose 3 < ramseyNumber (t + 1) (t + 1) := by
  have h := card_lt_ramseyNumber_iff (k := t + 1) (l := t + 1)
    (V := {s : Finset (Fin t) // #s = 3})
  rw [Fintype.card_finset_len, Fintype.card_fin] at h
  refine h.2 ⟨nagyGraph (Fin t), ?_, ?_⟩
  · simpa only [Fintype.card_fin] using cliqueFree_nagyGraph (α := Fin t)
  · simpa only [Fintype.card_fin] using indepSetFree_nagyGraph (α := Fin t)

end SimpleGraph

end
