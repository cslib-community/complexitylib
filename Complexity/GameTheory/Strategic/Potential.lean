/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.GameTheory.Strategic.Basic
public import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.WellFounded
import Mathlib.Tactic.Linarith

/-!
# Potential games and the finite improvement property

Potential functions for strategic games in cost-minimization form, following Monderer and
Shapley [MondererShapley1996], Section 2, with costs in place of payoffs (all inequalities are
reversed). For a game `G` and `Φ : (∀ i, S i) → ℝ`:

* `Φ` is an **exact potential** if every unilateral deviation changes the deviator's cost by
  exactly the change in `Φ`;
* `Φ` is an **ordinal potential** if a unilateral deviation strictly lowers the deviator's cost
  if and only if it strictly lowers `Φ`;
* `Φ` is a **generalized ordinal potential** if every strict improvement of the deviator
  strictly lowers `Φ`.

A game has the **finite improvement property** (FIP) if it has no infinite improvement path
`γ 0, γ 1, …`, where each `γ (k + 1)` arises from `γ k` by a unilateral deviation that strictly
lowers the deviator's cost.

## Main definitions

* `Cslib.GameTheory.CostGame.IsExactPotential`, `Cslib.GameTheory.CostGame.IsOrdinalPotential`,
  `Cslib.GameTheory.CostGame.IsGeneralizedOrdinalPotential`: the three notions of potential.
* `Cslib.GameTheory.CostGame.HasFIP`: the finite improvement property.

## Main results

* `Cslib.GameTheory.CostGame.IsOrdinalPotential.isPureNash_iff` ([MondererShapley1996],
  Lemma 2.1): for an ordinal potential, the pure Nash equilibria are the profiles at which no
  unilateral deviation lowers the potential.
* `Cslib.GameTheory.CostGame.IsGeneralizedOrdinalPotential.isPureNash_of_forall_le`: a global
  minimizer of a generalized ordinal potential is a pure Nash equilibrium.
* `Cslib.GameTheory.CostGame.IsGeneralizedOrdinalPotential.hasFIP` ([MondererShapley1996],
  Lemma 2.3, for generalized ordinal potentials): a game with finitely many profiles and a
  generalized ordinal potential has the FIP.
* `Cslib.GameTheory.CostGame.IsGeneralizedOrdinalPotential.exists_isPureNash`
  ([MondererShapley1996], Corollary 2.2, for generalized ordinal potentials): such a game has a
  pure Nash equilibrium.
* `Cslib.GameTheory.CostGame.hasFIP_iff_exists_isGeneralizedOrdinalPotential`
  ([MondererShapley1996], Lemma 2.5): a game with finitely many profiles has the FIP if and only
  if it has a generalized ordinal potential.
* `Cslib.GameTheory.CostGame.HasFIP.exists_reflTransGen_isPureNash`: under the FIP,
  better-response dynamics started from any profile reach a pure Nash equilibrium.
* `Cslib.GameTheory.CostGame.IsGeneralizedOrdinalPotential.le_of_reflTransGen`: a generalized
  ordinal potential does not increase along improvement paths.
* `Cslib.GameTheory.CostGame.IsExactPotential.sub_eq_sub` ([MondererShapley1996], Lemma 2.7):
  with finitely many players, two exact potentials differ by a constant.

## References

* [MondererShapley1996]
-/

public section

namespace Cslib.GameTheory.CostGame

variable {ι : Type*} {S : ι → Type*} [DecidableEq ι] (G : CostGame ι S)

/-- `Φ` is an **exact potential** for `G`: for every profile `s`, player `i` and strategy `a`,
`cost i (update s i a) - cost i s = Φ (update s i a) - Φ s` ([MondererShapley1996], Section 2,
with `w i = 1` in (2.2)). -/
@[expose] def IsExactPotential (Φ : (∀ i, S i) → ℝ) : Prop :=
  ∀ s i (a : S i),
    G.cost i (Function.update s i a) - G.cost i s = Φ (Function.update s i a) - Φ s

/-- `Φ` is an **ordinal potential** for `G`: a unilateral deviation strictly lowers the deviator's
cost if and only if it strictly lowers `Φ` ([MondererShapley1996], (2.1), for costs). -/
@[expose] def IsOrdinalPotential (Φ : (∀ i, S i) → ℝ) : Prop :=
  ∀ s i (a : S i),
    G.cost i (Function.update s i a) < G.cost i s ↔ Φ (Function.update s i a) < Φ s

/-- `Φ` is a **generalized ordinal potential** for `G`: every unilateral deviation that strictly
lowers the deviator's cost strictly lowers `Φ` ([MondererShapley1996], (2.3), for costs). -/
@[expose] def IsGeneralizedOrdinalPotential (Φ : (∀ i, S i) → ℝ) : Prop :=
  ∀ s i (a : S i),
    G.cost i (Function.update s i a) < G.cost i s → Φ (Function.update s i a) < Φ s

/-- The **finite improvement property**: there is no infinite improvement path, that is, no
sequence of profiles `γ` with `G.Improves (γ (k + 1)) (γ k)` for every `k`
([MondererShapley1996], Section 2). -/
@[expose] def HasFIP : Prop :=
  ∀ γ : ℕ → ∀ i, S i, ¬ ∀ k, G.Improves (γ (k + 1)) (γ k)

variable {G}

/-- The finite improvement property is well-foundedness of the improvement relation. -/
theorem hasFIP_iff_wellFounded : G.HasFIP ↔ WellFounded G.Improves := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  exact ⟨fun h => ⟨fun ⟨γ, hγ⟩ => h γ hγ⟩, fun h γ hγ => h.false ⟨γ, hγ⟩⟩

theorem IsExactPotential.isOrdinalPotential {Φ : (∀ i, S i) → ℝ} (h : G.IsExactPotential Φ) :
    G.IsOrdinalPotential Φ := by
  intro s i a
  have := h s i a
  constructor <;> intro hlt <;> linarith

theorem IsOrdinalPotential.isGeneralizedOrdinalPotential {Φ : (∀ i, S i) → ℝ}
    (h : G.IsOrdinalPotential Φ) : G.IsGeneralizedOrdinalPotential Φ :=
  fun s i a => (h s i a).1

theorem IsExactPotential.isGeneralizedOrdinalPotential {Φ : (∀ i, S i) → ℝ}
    (h : G.IsExactPotential Φ) : G.IsGeneralizedOrdinalPotential Φ :=
  h.isOrdinalPotential.isGeneralizedOrdinalPotential

/-- [MondererShapley1996], Lemma 2.1, for costs: if `Φ` is an ordinal potential, then `s` is a
pure Nash equilibrium of `G` if and only if no unilateral deviation strictly lowers `Φ`, that is,
if and only if `s` is a pure Nash equilibrium of the game in which every player's cost is `Φ`. -/
theorem IsOrdinalPotential.isPureNash_iff {Φ : (∀ i, S i) → ℝ} (h : G.IsOrdinalPotential Φ)
    {s : ∀ i, S i} : G.IsPureNash s ↔ ∀ i (a : S i), Φ s ≤ Φ (Function.update s i a) := by
  refine forall₂_congr fun i a => ?_
  rw [← not_lt, ← not_lt, h s i a]

/-- If no unilateral deviation strictly lowers a generalized ordinal potential, the profile is a
pure Nash equilibrium. -/
theorem IsGeneralizedOrdinalPotential.isPureNash_of_forall_update_le {Φ : (∀ i, S i) → ℝ}
    (h : G.IsGeneralizedOrdinalPotential Φ) {s : ∀ i, S i}
    (hs : ∀ i (a : S i), Φ s ≤ Φ (Function.update s i a)) : G.IsPureNash s := by
  intro i a
  by_contra hlt
  exact (hs i a).not_gt (h s i a (lt_of_not_ge hlt))

/-- A global minimizer of a generalized ordinal potential is a pure Nash equilibrium. -/
theorem IsGeneralizedOrdinalPotential.isPureNash_of_forall_le {Φ : (∀ i, S i) → ℝ}
    (h : G.IsGeneralizedOrdinalPotential Φ) {s : ∀ i, S i} (hs : ∀ t, Φ s ≤ Φ t) :
    G.IsPureNash s :=
  h.isPureNash_of_forall_update_le fun _ _ => hs _

/-- With finitely many profiles, a generalized ordinal potential makes the improvement relation
well-founded. -/
theorem IsGeneralizedOrdinalPotential.wellFounded [Finite (∀ i, S i)] {Φ : (∀ i, S i) → ℝ}
    (h : G.IsGeneralizedOrdinalPotential Φ) : WellFounded G.Improves := by
  have hsub : Subrelation G.Improves (fun t s => Φ t < Φ s) := by
    rintro t s ⟨i, a, rfl, hlt⟩
    exact h s i a hlt
  exact hsub.wf (Finite.wellFounded_of_trans_of_irrefl _)

/-- [MondererShapley1996], Lemma 2.3, in the generality of the "if" direction of Lemma 2.5: a game
with finitely many profiles and a generalized ordinal potential has the finite improvement
property. -/
theorem IsGeneralizedOrdinalPotential.hasFIP [Finite (∀ i, S i)] {Φ : (∀ i, S i) → ℝ}
    (h : G.IsGeneralizedOrdinalPotential Φ) : G.HasFIP :=
  hasFIP_iff_wellFounded.2 h.wellFounded

/-- A game with the finite improvement property and some profile has a pure Nash equilibrium. -/
theorem HasFIP.exists_isPureNash [Nonempty (∀ i, S i)] (h : G.HasFIP) :
    ∃ s, G.IsPureNash s := by
  obtain ⟨s, -, hs⟩ := (hasFIP_iff_wellFounded.1 h).has_min Set.univ Set.univ_nonempty
  exact ⟨s, G.isPureNash_iff_forall_not_improves.2 fun t ht => hs t trivial ht⟩

/-- **Better-response dynamics converge** under the finite improvement property: from every
profile `s`, a finite sequence of improvement steps reaches a pure Nash equilibrium `t`
([MondererShapley1996], Section 2, after Lemma 2.3). -/
theorem HasFIP.exists_reflTransGen_isPureNash (h : G.HasFIP) (s : ∀ i, S i) :
    ∃ t, Relation.ReflTransGen (flip G.Improves) s t ∧ G.IsPureNash t := by
  induction s using (hasFIP_iff_wellFounded.1 h).induction with
  | _ s ih =>
    by_cases hs : G.IsPureNash s
    · exact ⟨s, .refl, hs⟩
    · rw [G.isPureNash_iff_forall_not_improves] at hs
      push Not at hs
      obtain ⟨t, ht⟩ := hs
      obtain ⟨u, htu, hu⟩ := ih t ht
      exact ⟨u, Relation.ReflTransGen.head ht htu, hu⟩

/-- A generalized ordinal potential does not increase along an improvement path: if better-response
dynamics lead from `s` to `t`, then `Φ t ≤ Φ s`. -/
theorem IsGeneralizedOrdinalPotential.le_of_reflTransGen {Φ : (∀ i, S i) → ℝ}
    (h : G.IsGeneralizedOrdinalPotential Φ) {s t : ∀ i, S i}
    (hst : Relation.ReflTransGen (flip G.Improves) s t) : Φ t ≤ Φ s := by
  induction hst with
  | refl => exact le_rfl
  | tail _ hbc ih =>
    obtain ⟨i, a, rfl, hlt⟩ := hbc
    exact (h _ i a hlt).le.trans ih

/-- [MondererShapley1996], Corollary 2.2, for generalized ordinal potentials: a game with finitely
many (and at least one) profiles and a generalized ordinal potential has a pure Nash equilibrium.
-/
theorem IsGeneralizedOrdinalPotential.exists_isPureNash [Finite (∀ i, S i)]
    [Nonempty (∀ i, S i)] {Φ : (∀ i, S i) → ℝ} (h : G.IsGeneralizedOrdinalPotential Φ) :
    ∃ s, G.IsPureNash s :=
  h.hasFIP.exists_isPureNash

/-- [MondererShapley1996], Lemma 2.5: a game with finitely many profiles has the finite
improvement property if and only if it has a generalized ordinal potential.

For the "only if" direction we use, in cost form, the construction of Milchtaich cited in
[MondererShapley1996], footnote 12: `Φ s` is the number of profiles reachable from `s` by a
nonempty improvement path. -/
theorem hasFIP_iff_exists_isGeneralizedOrdinalPotential [Finite (∀ i, S i)] :
    G.HasFIP ↔ ∃ Φ, G.IsGeneralizedOrdinalPotential Φ := by
  refine ⟨fun h => ?_, fun ⟨Φ, hΦ⟩ => hΦ.hasFIP⟩
  classical
  have : Fintype (∀ i, S i) := Fintype.ofFinite _
  have hwf := (hasFIP_iff_wellFounded.1 h).transGen
  let D : (∀ i, S i) → Finset (∀ i, S i) := fun s =>
    Finset.univ.filter fun z => Relation.TransGen G.Improves z s
  refine ⟨fun s => ((D s).card : ℝ), fun s i a hlt => ?_⟩
  have hstep : G.Improves (Function.update s i a) s := ⟨i, a, rfl, hlt⟩
  have hss : D (Function.update s i a) ⊂ D s := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨Function.update s i a, ?_, ?_⟩
      · simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
        exact .single hstep
      · simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
        intro hself
        exact @WellFounded.asymmetric _ _ hwf _ _ hself hself
    · intro z
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun hz => .tail hz hstep
  change ((D (Function.update s i a)).card : ℝ) < (D s).card
  exact_mod_cast Finset.card_lt_card hss

/-- [MondererShapley1996], Lemma 2.7: with finitely many players, two exact potentials of the same
game differ by a constant. -/
theorem IsExactPotential.sub_eq_sub [Finite ι] {Φ Ψ : (∀ i, S i) → ℝ}
    (hΦ : G.IsExactPotential Φ) (hΨ : G.IsExactPotential Ψ) (s t : ∀ i, S i) :
    Φ s - Ψ s = Φ t - Ψ t := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hupd : ∀ (u : ∀ i, S i) i (a : S i),
      Φ (Function.update u i a) - Ψ (Function.update u i a) = Φ u - Ψ u := by
    intro u i a
    have h1 := hΦ u i a
    have h2 := hΨ u i a
    linarith
  -- Replace the coordinates of `t` by those of `s` one player at a time.
  have key : ∀ F : Finset ι,
      Φ (fun j => if j ∈ F then s j else t j) - Ψ (fun j => if j ∈ F then s j else t j)
        = Φ t - Ψ t := by
    intro F
    induction F using Finset.induction_on with
    | empty => simp only [Finset.notMem_empty, ite_false]
    | insert k F hk ih =>
      have : (fun j => if j ∈ insert k F then s j else t j)
          = Function.update (fun j => if j ∈ F then s j else t j) k (s k) := by
        funext j
        by_cases hj : j = k
        · subst hj
          simp only [Finset.mem_insert, true_or, ite_true, Function.update_self]
        · simp only [Finset.mem_insert, hj, false_or, Function.update_of_ne hj]
      rw [this, hupd, ih]
  simpa only [Finset.mem_univ, ite_true] using key Finset.univ

end Cslib.GameTheory.CostGame
