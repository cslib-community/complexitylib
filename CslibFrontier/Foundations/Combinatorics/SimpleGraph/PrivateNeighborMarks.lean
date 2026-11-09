/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, canonical private-neighbor markings)

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.DominatingSet
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Unique private-neighbor markings of minimal dominating sets

Mark every vertex whose closed neighborhood contains exactly one selected vertex. The augmented
formulation of [ChenJiangZhu2027], Proposition 7.6 / Appendix D.3 (PDF pp.27,35), forces exactly
these marks, so its counts are of original sets rather than set–marking pairs.

## Main results

* `completePrivateMarking_iff`: the augmented predicate forces precisely the canonical marks.
* `card_completePrivateMarking`: forgetting marks preserves the original-set count.
-/

public section

namespace SimpleGraph

variable {V : Type*}

/-- Mark all private closed neighbors, without choosing or labeling an owner. -/
@[expose] def privateMarks (G : SimpleGraph V) (S : Set V) : Set V :=
  {w | ∃ u, G.IsPrivateNeighbor S w u}

/-- A valid private marking is complete when every unmarked vertex has two distinct selected
closed neighbors. Together with domination this forces marks exactly at count one. -/
@[expose] def IsCompletePrivateMarking (G : SimpleGraph V) (S W : Set V) : Prop :=
  G.IsPrivateMarking S W ∧ ∀ w, w ∈ W ∨
    ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ G.ClosedAdj w u ∧ G.ClosedAdj w v

open Classical in
/-- The augmented marking predicate is a functional extension of ordinary minimal domination. -/
theorem completePrivateMarking_iff (G : SimpleGraph V) (S W : Set V) :
    G.IsCompletePrivateMarking S W ↔ Minimal G.IsDominatingSet S ∧ W = G.privateMarks S := by
  constructor
  · rintro ⟨hm, hc⟩
    refine ⟨(G.exists_privateMarking_iff S).mp ⟨W, hm⟩, ?_⟩
    ext w
    constructor
    · intro hw
      obtain ⟨u, hu, hwu⟩ := hm.1 w
      exact ⟨u, hu, hwu, fun v hv hwv => (hm.2.1 w hw u hu v hv hwu hwv).symm⟩
    · rintro ⟨u, hu, hwu, huniq⟩
      rcases hc w with hw | ⟨v, hv, t, ht, hne, hwv, hwt⟩
      · exact hw
      · exact False.elim (hne ((huniq v hv hwv).trans (huniq t ht hwt).symm))
  · rintro ⟨hmin, rfl⟩
    obtain ⟨hd, hp⟩ := (G.minimal_dominatingSet_iff S).mp hmin
    refine ⟨⟨hd, ?_, ?_⟩, ?_⟩
    · rintro w ⟨owner, _, _, huniq⟩ u hu v hv hwu hwv
      exact (huniq u hu hwu).trans (huniq v hv hwv).symm
    · intro u hu
      obtain ⟨w, hw⟩ := hp u hu
      exact ⟨w, ⟨u, hw⟩, hw.2.1.symm⟩
    · intro w
      by_cases hw : w ∈ G.privateMarks S
      · exact Or.inl hw
      · obtain ⟨u, hu, hwu⟩ := hd w
        have hv : ∃ v ∈ S, G.ClosedAdj w v ∧ v ≠ u := by
          by_contra hn
          apply hw
          refine ⟨u, hu, hwu, ?_⟩
          intro v hv hwv
          by_contra hne
          exact hn ⟨v, hv, hwv, hne⟩
        obtain ⟨v, hv, hwv, hne⟩ := hv
        exact Or.inr ⟨u, hu, v, hv, Ne.symm hne, hwu, hwv⟩

open Classical in
/-- Exactly one augmented marking for each original minimal dominating set, retaining any
predicate on that set. This follows from a bijection, even without finiteness. -/
theorem card_completePrivateMarking (G : SimpleGraph V) (Q : Set V → Prop) :
    Nat.card {p : Set V × Set V // G.IsCompletePrivateMarking p.1 p.2 ∧ Q p.1} =
      Nat.card {S : Set V // Minimal G.IsDominatingSet S ∧ Q S} := by
  apply Nat.card_congr
  exact
    { toFun := fun p => ⟨p.val.1, ((G.completePrivateMarking_iff _ _).mp p.property.1).1,
        p.property.2⟩
      invFun := fun S => ⟨(S.val, G.privateMarks S.val),
        (G.completePrivateMarking_iff _ _).mpr ⟨S.property.1, rfl⟩, S.property.2⟩
      left_inv := fun p => by
        apply Subtype.ext
        change (p.val.1, G.privateMarks p.val.1) = p.val
        apply Prod.ext
        · rfl
        · exact ((G.completePrivateMarking_iff _ _).mp p.property.1).2.symm
      right_inv := fun _ => rfl }

end SimpleGraph
