/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Basic
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Layouts of disconnected graphs

The layout hypothesis `Cslib.Circuits.Frontier.LayoutBound` is stated for connected graphs. A
disconnected graph is laid out one connected component after another, each component by the
layout hypothesis (`LayoutBound.exists_layout_componentwise`). Every frontier of the result lies
among the edges of a single component, and is bounded in terms of the cycle rank of that
component alone (`Cslib.Circuits.Frontier.Multigraph.cycleRankOn`): the components before it are
closed, so they do not change its edge cuts.

## Main results

* `Cslib.Circuits.Frontier.LayoutBound.exists_layout_componentwise`: under the layout hypothesis,
  every loopless graph of maximum degree `d`, connected or not, has a layout whose frontiers at
  each step lie among the edges of the component of the vertex processed and are at most
  `(A + η) β₁ + η |V| + C`, for the cycle rank `β₁` of that component.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set

/-- **Layouts of disconnected graphs.** Under the layout hypothesis for maximum degree `d`, every
loopless graph of maximum degree `d`, connected or not, has a layout such that at every step `t`,
with `W` the component of the vertex processed, the frontiers at times `t` and `t + 1` lie among
the edges of `W` and have at most `(A + η) β₁(W) + η |V| + C` edges.

The components are laid out one after another, each by the layout hypothesis. -/
theorem LayoutBound.exists_layout_componentwise {d : ℕ} {A : ℝ} (h : LayoutBound d A) {η : ℝ}
    (hη : 0 < η) :
    ∃ C : ℝ, ∀ (V E : Type) [Finite V] [Finite E] (G : Multigraph V E),
      G.Loopless → G.MaxDegreeLE d →
        ∃ π : Layout V, ∀ t (ht : t < Nat.card V), ∀ s, t ≤ s → s ≤ t + 1 →
          G.frontier π s ⊆ G.touching (G.component (π.symm ⟨t, ht⟩)) ∧
          ((G.frontier π s).ncard : ℝ) ≤
            (A + η) * G.cycleRankOn (G.component (π.symm ⟨t, ht⟩)) + η * Nat.card V + C := by
  obtain ⟨C, hC⟩ := h η hη
  refine ⟨C, fun V E _ _ G hG hd => ?_⟩
  set Γ := G.toSimpleGraph
  -- Lay out each component by the layout hypothesis.
  have hlay (K : Γ.ConnectedComponent) : ∃ ρ : Layout K.supp, ∀ s,
      (((G.induce K.supp).frontier ρ s).ncard : ℝ) ≤
        (A + η) * G.cycleRankOn K.supp + η * Nat.card V + C := by
    obtain ⟨v, rfl⟩ := K.nonempty_supp
    obtain ⟨ρ, hρ⟩ := hC _ _ (G.induce (G.component v)) (G.connected_induce_component v)
      (hG.induce _) (hd.induce _)
    refine ⟨ρ, fun s =>
      ((Nat.cast_le.2 ((G.induce _).ncard_frontier_le_width ρ s)).trans hρ).trans ?_⟩
    rw [G.cycleRank_induce (G.edgeCut_component v)]
    have : (Nat.card (G.component v) : ℝ) ≤ Nat.card V := by
      exact_mod_cast Finite.card_subtype_le _
    change _ ≤ (A + η) * G.cycleRankOn (G.component v) + η * Nat.card V + C
    gcongr
  choose ρ hρ using hlay
  -- Order the vertices by their component, then by their place in its layout.
  set num := Finite.equivFin Γ.ConnectedComponent
  set key : V → ℕ ×ₗ ℕ := fun v =>
    toLex ((num (Γ.connectedComponentMk v) : ℕ),
      (ρ (Γ.connectedComponentMk v) ⟨v, rfl⟩ : ℕ)) with hkey
  have hpos (v : V) (K : Γ.ConnectedComponent) (hv : v ∈ K.supp) :
      (ρ (Γ.connectedComponentMk v) ⟨v, rfl⟩ : ℕ) = ρ K ⟨v, hv⟩ := by
    obtain rfl : Γ.connectedComponentMk v = K := hv
    rfl
  have hinj : key.Injective := by
    intro v w hvw
    simp only [hkey, toLex_inj, Prod.mk.injEq] at hvw
    have hK := num.injective (Fin.ext hvw.1)
    rw [hpos w _ hK.symm] at hvw
    exact congrArg Subtype.val ((ρ _).injective (Fin.ext hvw.2))
  obtain ⟨π, hπ⟩ := Layout.exists_lt_iff hinj
  refine ⟨π, fun t ht => ?_⟩
  -- The vertex processed at step `t`, its component `K`, and its place `p` in the layout of `K`.
  set v := π.symm ⟨t, ht⟩
  set K := Γ.connectedComponentMk v
  set p : ℕ := (ρ K ⟨v, rfl⟩ : ℕ)
  have hp : p < Nat.card K.supp := (ρ K ⟨v, rfl⟩).isLt
  have hK : G.edgeCut K.supp = ∅ := G.edgeCut_setOf_connectedComponentMk (· = K)
  -- The components before `K`.
  set B : Set V := {u | num (Γ.connectedComponentMk u) < num K}
  have hB : G.edgeCut B = ∅ := G.edgeCut_setOf_connectedComponentMk (num · < num K)
  have hBK (S : Set K.supp) : Disjoint B (Subtype.val '' S) := by
    refine disjoint_left.2 fun u hu ⟨u', _, hu'⟩ => ?_
    have hu : num (Γ.connectedComponentMk u) < num K := hu
    rw [← hu', u'.2] at hu
    exact lt_irrefl _ hu
  -- The first `t` vertices are the components before `K` and the first `p` vertices of `K`.
  have hinit : π.initial t = B ∪ Subtype.val '' (ρ K).initial p := by
    ext u
    rw [Layout.initial_eq_of_lt_iff hπ ht, mem_ofPred_eq, hkey, Prod.Lex.toLex_lt_toLex]
    simp only [Fin.val_fin_lt, Fin.val_inj, B, mem_union, mem_ofPred_eq, mem_image,
      Layout.mem_initial]
    refine or_congr_right ⟨fun ⟨hu, hlt⟩ => ?_, fun ⟨u', hu', hu'u⟩ => ?_⟩
    · obtain hu := num.injective hu
      exact ⟨⟨u, hu⟩, by rwa [← hpos u K hu], rfl⟩
    · subst hu'u
      refine ⟨congrArg num u'.2, ?_⟩
      rwa [hpos _ K u'.2]
  have hinit' : π.initial (t + 1) = B ∪ Subtype.val '' (ρ K).initial (p + 1) := by
    rw [π.initial_succ ht, hinit, (ρ K).initial_succ hp, image_insert_eq, union_insert]
    congr 1
    change v = ((ρ K).symm (ρ K ⟨v, rfl⟩) : V)
    rw [Equiv.symm_apply_apply]
  -- Both frontiers are frontiers of the layout of `K`.
  have hfront (q : ℕ) : G.edgeCut (B ∪ Subtype.val '' (ρ K).initial q) =
      Subtype.val '' (G.induce K.supp).frontier (ρ K) q := by
    rw [G.edgeCut_union_of_edgeCut_eq_empty hB (hBK _), G.edgeCut_image_val hK]
    rfl
  intro s hts hst
  obtain ⟨q, hq⟩ : ∃ q, G.frontier π s = Subtype.val '' (G.induce K.supp).frontier (ρ K) q := by
    rcases (show s = t ∨ s = t + 1 by omega) with rfl | rfl
    · exact ⟨p, by rw [Multigraph.frontier, hinit, hfront]⟩
    · exact ⟨p + 1, by rw [Multigraph.frontier, hinit', hfront]⟩
  rw [hq, ncard_image_of_injective _ Subtype.val_injective]
  exact ⟨fun _ ⟨e, _, he⟩ => he ▸ Or.inl e.2.1, hρ K q⟩

end Cslib.Circuits.Frontier
