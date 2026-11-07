/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Sunflower.Implication
public import Cslib.Foundations.Relation.RelatesInSteps

/-!
# Closure under implication inside an ambient family

Fix an ambient family `P` of sets. A family `F` is *`r`-closed* in `P` when it contains every member
of `P` implied by `r` of its members (`Cslib.ImplicationClosure.IsClosed`, with implication
`Cslib.ImpliedBy`). This is Razborov's closure as presented by Jukna
[Jukna, Section 9.10.1][Jukna2012]: the approximators of the method of approximations are the
closed subfamilies of a family of small sets, such as the matchings with at most `s` edges for the
perfect matching function.

Closed families are closed under intersection (`Cslib.ImplicationClosure.IsClosed.inter`). The
closure of a family is reached by adding derived sets one at a time
(`Cslib.ImplicationClosure.Step`), so it takes at most `#P` steps
(`Cslib.ImplicationClosure.relatesInSteps_closure`). When `P` is closed under subsets, the minimal
members of a closed subfamily of `P` form an implication-minimal family, so a closed family of sets
of at most `s` elements has at most `(r - 1) ^ s` minimal members
(`Cslib.ImplicationClosure.card_minimals_le`), by the Alon–Boppana family bound
(`Cslib.card_le_pow_of_isImplicationMinimal`).

## Main definitions

* `Cslib.ImplicationClosure.Derives`, `Cslib.ImplicationClosure.IsClosed`: derived sets and closed
  families.
* `Cslib.ImplicationClosure.Step`, `Cslib.ImplicationClosure.closure`: closure steps and the
  closure.
* `Cslib.ImplicationClosure.minimals`: the minimal members of a family.

## Main results

* `Cslib.ImplicationClosure.relatesInSteps_closure`: the closure is reached in at most `#P` steps.
* `Cslib.ImplicationClosure.card_minimals_le`: a closed family of sets of at most `s` elements has
  at most `(r - 1) ^ s` minimal members.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Section 9.10][Jukna2012]
* [N. Alon, R. B. Boppana, *The monotone circuit complexity of Boolean functions*][AlonBoppana1987]
-/

@[expose] public section

namespace Cslib.ImplicationClosure

open Finset Relation

variable {α : Type*} [DecidableEq α] {r : ℕ} {P F G : Finset (Finset α)}

/-! ### Closed families -/

/-- `W` is *derived* from `F` inside `P`: it belongs to `P` and is implied by `r` members of `F`. -/
def Derives (r : ℕ) (P F : Finset (Finset α)) (W : Finset α) : Prop :=
  W ∈ P ∧ ImpliedBy r F W

/-- A family is *closed* in `P` when it contains every set derived from it inside `P`. -/
def IsClosed (r : ℕ) (P F : Finset (Finset α)) : Prop :=
  ∀ W, Derives r P F W → W ∈ F

/-- A closed family contains every member of `P` containing one of its members. -/
theorem IsClosed.mem_of_subset (hF : IsClosed r P F) {V W : Finset α} (hV : V ∈ F) (hVW : V ⊆ W)
    (hW : W ∈ P) : W ∈ F :=
  hF W ⟨hW, impliedBy_of_subset hV hVW⟩

/-- The intersection of closed families is closed. -/
theorem IsClosed.inter (hF : IsClosed r P F) (hG : IsClosed r P G) : IsClosed r P (F ∩ G) :=
  fun W ⟨hW, h⟩ =>
    mem_inter.2 ⟨hF W ⟨hW, h.mono inter_subset_left⟩, hG W ⟨hW, h.mono inter_subset_right⟩⟩

/-- The ambient family is closed. -/
theorem isClosed_self : IsClosed r P P :=
  fun _ h => h.1

/-- For `r ≥ 1`, the empty family is closed: no set is implied by members of it. -/
theorem isClosed_empty (hr : 1 ≤ r) : IsClosed r P ∅ :=
  fun _ ⟨_, _, hV, _⟩ => absurd (hV ⟨0, hr⟩) (notMem_empty _)

/-- A closure step: add one derived set. -/
def Step (r : ℕ) (P F G : Finset (Finset α)) : Prop :=
  ∃ W, W ∉ F ∧ Derives r P F W ∧ G = insert W F

/-- A closure step adds a member of `P`, so it lowers the number of members of `P` missing. -/
theorem Step.card_lt (h : Step r P F G) : (P \ G).card < (P \ F).card := by
  obtain ⟨W, hWF, hW, rfl⟩ := h
  refine card_lt_card ⟨sdiff_subset_sdiff subset_rfl (subset_insert _ _), fun hsub => ?_⟩
  exact (mem_sdiff.1 (hsub (mem_sdiff.2 ⟨hW.1, hWF⟩))).2 (mem_insert_self _ _)

/-- A family can be closed in at most as many steps as it misses members of `P`. -/
theorem exists_relatesInSteps_isClosed (r : ℕ) (P F : Finset (Finset α)) :
    ∃ G m, m ≤ (P \ F).card ∧ RelatesInSteps (Step r P) F G m ∧ IsClosed r P G := by
  induction F using (measure fun F => (P \ F).card).wf.induction with
  | h F ih =>
    by_cases hF : IsClosed r P F
    · exact ⟨F, 0, Nat.zero_le _, RelatesInSteps.refl F, hF⟩
    · simp only [IsClosed, not_forall] at hF
      obtain ⟨W, hW, hWF⟩ := hF
      have hstep : Step r P F (insert W F) := ⟨W, hWF, hW, rfl⟩
      obtain ⟨G, m, hm, hG, hclosed⟩ := ih _ hstep.card_lt
      exact ⟨G, m + 1, by have := hstep.card_lt; omega,
        RelatesInSteps.head _ _ _ _ hstep hG, hclosed⟩

/-- The closure of a family: a closed family reached from it by closure steps. -/
noncomputable def closure (r : ℕ) (P F : Finset (Finset α)) : Finset (Finset α) :=
  (exists_relatesInSteps_isClosed r P F).choose

/-- The closure is closed. -/
theorem isClosed_closure (F : Finset (Finset α)) : IsClosed r P (closure r P F) :=
  (exists_relatesInSteps_isClosed r P F).choose_spec.choose_spec.2.2

/-- The closure is reached in at most `#P` steps. -/
theorem relatesInSteps_closure (F : Finset (Finset α)) :
    ∃ m ≤ P.card, RelatesInSteps (Step r P) F (closure r P F) m := by
  obtain ⟨m, hm, h, -⟩ := (exists_relatesInSteps_isClosed r P F).choose_spec
  exact ⟨m, hm.trans (card_le_card sdiff_subset), h⟩

/-- Closure steps only add sets. -/
theorem subset_of_relatesInSteps {m : ℕ} (h : RelatesInSteps (Step r P) F G m) : F ⊆ G := by
  induction h with
  | refl => exact subset_rfl
  | tail _ _ _ _ h ih =>
    obtain ⟨W, -, -, rfl⟩ := h
    exact ih.trans (subset_insert _ _)

/-- Closure steps only add members of `P`. -/
theorem subset_of_relatesInSteps_of_subset {m : ℕ} (h : RelatesInSteps (Step r P) F G m)
    (hF : F ⊆ P) : G ⊆ P := by
  induction h with
  | refl => exact hF
  | tail _ _ _ _ h ih =>
    obtain ⟨W, -, hW, rfl⟩ := h
    exact insert_subset hW.1 ih

/-- A family is contained in its closure. -/
theorem subset_closure (F : Finset (Finset α)) : F ⊆ closure r P F :=
  let ⟨_, _, h⟩ := relatesInSteps_closure (r := r) (P := P) F
  subset_of_relatesInSteps h

/-- The closure of a subfamily of `P` is a subfamily of `P`. -/
theorem closure_subset (hF : F ⊆ P) : closure r P F ⊆ P :=
  let ⟨_, _, h⟩ := relatesInSteps_closure (r := r) (P := P) F
  subset_of_relatesInSteps_of_subset h hF

/-! ### Minimal members -/

/-- The minimal members of a family. -/
def minimals (F : Finset (Finset α)) : Finset (Finset α) :=
  F.filter fun W => ∀ U ∈ F, U ⊆ W → U = W

/-- The minimal members of a family belong to it. -/
theorem minimals_subset (F : Finset (Finset α)) : minimals F ⊆ F :=
  filter_subset _ _

/-- Every member of a family contains a minimal member of the family. -/
theorem exists_mem_minimals_subset {W : Finset α} (hW : W ∈ F) : ∃ X ∈ minimals F, X ⊆ W := by
  obtain ⟨X, hX, hmin⟩ := (F.filter (· ⊆ W)).exists_minimal ⟨W, mem_filter.2 ⟨hW, subset_rfl⟩⟩
  obtain ⟨hXF, hXW⟩ := mem_filter.1 hX
  refine ⟨X, mem_filter.2 ⟨hXF, fun U hU hUX => ?_⟩, hXW⟩
  exact subset_antisymm hUX (hmin (mem_filter.2 ⟨hU, hUX.trans hXW⟩) hUX)

/-- **Minimal members of a closed family.** If `P` is closed under subsets and `r ≥ 2`, a closed
subfamily of `P` whose members have at most `s` elements has at most `(r - 1) ^ s` minimal members:
they form an implication-minimal family, to which the Alon–Boppana family bound
(`Cslib.card_le_pow_of_isImplicationMinimal`) [AlonBoppana1987] applies. -/
theorem card_minimals_le (hr : 2 ≤ r) (hP : ∀ W ∈ P, ∀ U ⊆ W, U ∈ P) (hFP : F ⊆ P)
    (hF : IsClosed r P F) {s : ℕ} (hs : ∀ W ∈ F, W.card ≤ s) : (minimals F).card ≤ (r - 1) ^ s := by
  refine card_le_pow_of_isImplicationMinimal hr (fun W hW => hs W (minimals_subset F hW)) ?_
  intro W hW U hUW hU
  obtain ⟨hWF, hmin⟩ := mem_filter.1 hW
  have hUF : U ∈ F := hF U ⟨hP W (hFP hWF) U hUW.subset, hU.mono (minimals_subset F)⟩
  exact hUW.ne (hmin U hUF hUW.subset)

end Cslib.ImplicationClosure
