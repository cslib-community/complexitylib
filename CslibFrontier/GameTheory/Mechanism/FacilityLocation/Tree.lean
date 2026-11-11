/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Tree
public import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Interval
import Mathlib.Tactic.Linarith

/-!
# Strategyproof facility location on tree metric graphs

This module formalizes the tree characterization theorem of [SchummerVohra2002] (Theorem 1,
p. 15 of the January 2001 author preprint): on a finite tree metric graph `MetricGraph W`
(`W.graph.IsTree`), a deterministic facility-location mechanism is strategyproof and surjective
if and only if it is the evaluation map of an extended median voter scheme (`TreeEMVS`).

`TreeEMVS` adapts the source's definition. The source builds an extended median voter scheme from
a consistent family of generalized median voter schemes on leaf-to-leaf paths (Section 3,
pp. 9–15); `TreeEMVS` instead records, at every point and in every direction, which coalitions
win. The `TreeEMVS` docstring describes the correspondence.

The module also proves that every such mechanism is strongly group strategyproof. This
strengthening is not stated in the source, whose Theorem 1 concerns individual strategyproofness.

## Main definitions

* `Cslib.GameTheory.FacilityLocation.TreeEMVS`: an extended median voter scheme on a tree metric
  graph, specified by monotone branch-winning coalition families `win y q : Finset ι → Prop`
  satisfying branch invariance, nesting, duality, disjoint-branch exclusivity, and interior
  openness.
* `Cslib.GameTheory.FacilityLocation.TreeEMVS.IsEquilibrium`: equilibrium condition asserting that
  at `y`, no branch contains a winning coalition of reported agent locations.
* `Cslib.GameTheory.FacilityLocation.TreeEMVS.eval`: the unique equilibrium outcome of a `TreeEMVS`.

## Main results

* `Cslib.GameTheory.FacilityLocation.TreeEMVS.existsUnique_equilibrium`: every `TreeEMVS` admits a
  unique equilibrium outcome for every profile.
* `Cslib.GameTheory.FacilityLocation.TreeEMVS.eval_isGroupStrategyProof`: every `TreeEMVS`
  evaluates to a strongly group-strategyproof mechanism.
* `Cslib.GameTheory.FacilityLocation.isStrategyProof_and_surjective_iff_exists_treeEMVS`:
  Schummer–Vohra's characterization on trees: deterministic onto strategyproof mechanisms on
  `MetricGraph W` coincide with `TreeEMVS.eval`.
* `Cslib.GameTheory.FacilityLocation.isGroupStrategyProof_of_isStrategyProof_of_surjective_tree`:
  every deterministic onto strategyproof mechanism on a tree metric graph is strongly group
  strategyproof.

## References

* [SchummerVohra2002] J. Schummer and R. V. Vohra, "Strategy-proof Location on a Network",
  Journal of Economic Theory 104(2) (2002), 405–428.
-/

public section

open SimpleGraph SimpleGraph.MetricGraph

namespace Cslib.GameTheory.FacilityLocation

section GeodesicInterval

private lemma exists_isometry_interval {V : Type*} [Finite V] {W : WeightedGraph V}
    (hT : W.graph.IsTree) (a b : MetricGraph W) :
    ∃ φ : Set.Icc (0 : ℝ) (dist a b) → MetricGraph W,
      Isometry φ ∧
      φ ⟨0, le_rfl, dist_nonneg⟩ = a ∧
      φ ⟨dist a b, dist_nonneg, le_rfl⟩ = b ∧
      Set.range φ = interval a b := by
  obtain ⟨γ, hγ⟩ := exists_isGeodesic a b
  refine ⟨fun t => γ t.1, hγ.isometry, hγ.map_zero, hγ.map_dist, Set.ext fun z => ?_⟩
  constructor
  · rintro ⟨t, rfl⟩
    exact hγ.mem_interval t.2
  · intro hz
    obtain ⟨γ', hγ', hgz⟩ := exists_isGeodesic_through_of_mem_interval hz
    have hmem : dist a z ∈ Set.Icc 0 (dist a b) :=
      ⟨dist_nonneg, by linarith [mem_interval_iff.mp hz, dist_nonneg (x := z) (y := b)]⟩
    exact ⟨⟨dist a z, hmem⟩, (hγ'.eq_on hT hγ hmem).symm.trans hgz⟩

private lemma branch_disjoint_of_ne {V : Type*} [Finite V] {W : WeightedGraph V}
    (hT : W.graph.IsTree) {y p q : MetricGraph W}
    (hpq : branch y p ≠ branch y q) : Disjoint (branch y p) (branch y q) := by
  rw [Set.disjoint_left]
  intro w hwp hwq
  exact hpq ((branch_eq_of_mem hT hwp).symm.trans (branch_eq_of_mem hT hwq))

private lemma branch_subset_of_mem_interval {V : Type*} [Finite V] {W : WeightedGraph V}
    {y p q w : MetricGraph W} (hp : p ∈ interval y q) (_hpy : p ≠ y)
    (hw : w ∈ branch p q) : w ∈ branch y q := by
  by_contra hnot
  simp only [branch, Set.mem_ofPred_eq, Classical.not_not] at hnot hw
  have h1 := mem_interval_iff.mp hp
  have h2 := mem_interval_iff.mp hnot
  have hqpw : dist q p + dist p w ≤ dist q w := by
    have htri := dist_triangle p y w
    linarith [dist_comm q p, dist_comm q y, dist_comm q w, dist_comm p y, dist_comm y w]
  exact hw (mem_interval_iff.mpr (le_antisymm hqpw (dist_triangle q p w)))

private lemma interval_subset_branch {V : Type*} [Finite V] {W : WeightedGraph V}
    (hT : W.graph.IsTree) {y b q z : MetricGraph W}
    (hb : b ∈ branch y q) (hz : z ∈ interval y b) (hzy : z ≠ y) : z ∈ branch y q := by
  rw [← branch_eq_of_mem hT hb]
  simp only [branch, Set.mem_ofPred_eq]
  intro hmem
  have h1 := mem_interval_iff.mp hz
  have h2 := mem_interval_iff.mp hmem
  have hd : dist y z = 0 := by
    linarith [dist_comm b y, dist_comm b z, dist_comm y z, dist_comm z b]
  exact hzy (dist_eq_zero.mp hd).symm

private lemma interval_subset_notMem_branch {V : Type*} [Finite V] {W : WeightedGraph V}
    (hT : W.graph.IsTree) {y q a b z : MetricGraph W}
    (ha : a ∉ branch y q) (hb : b ∉ branch y q) (hz : z ∈ interval a b) :
    z ∉ branch y q := by
  intro hz_mem
  have hba := branch_eq_of_mem hT hz_mem
  rw [← hba] at ha hb
  simp only [branch, Set.mem_ofPred_eq, Classical.not_not] at ha hb
  have h1 := mem_interval_iff.mp hz
  have h2 := mem_interval_iff.mp ha
  have h3 := mem_interval_iff.mp hb
  have hd : dist y z = 0 := by
    linarith [dist_triangle a y b, dist_comm a y, dist_comm a z, dist_comm y z,
      dist_comm y a, dist_comm y b, dist_comm z b, dist_nonneg (x := y) (y := z)]
  exact (notMem_branch_self y q) ((dist_eq_zero.mp hd).symm ▸ hz_mem)

private lemma mem_branch_proj_interval_iff {V : Type*} [Finite V] {W : WeightedGraph V}
    (hT : W.graph.IsTree) {a b p q z : MetricGraph W}
    (hp : p ∈ interval a b) (hq : q ∈ interval a b) :
    z ∈ branch p q ↔ treeMedian hT a b z ∈ branch p q := by
  have hzp := dist_add_dist_eq_treeMedian hT (z := z) hp
  have hzq := dist_add_dist_eq_treeMedian hT (z := z) hq
  simp only [branch, Set.mem_ofPred_eq, mem_interval_iff]
  constructor <;> intro h heq <;> apply h <;>
    linarith [hzp, hzq, dist_comm z p, dist_comm z q, dist_comm p (treeMedian hT a b z),
      dist_comm q (treeMedian hT a b z)]

end GeodesicInterval

section TreeEMVS

/-- An **extended median voter scheme** (`TreeEMVS`) on a finite tree metric graph `MetricGraph W`
for agents `ι`, represented by a monotone family of winning coalitions `win y q` for each
direction `branch y q` (`q ≠ y`) satisfying branch invariance, nesting, pairwise duality,
disjoint-branch exclusivity, and interior openness.

This adapts the definition of [SchummerVohra2002] (January 2001 author preprint, Section 3,
pp. 9–15), which uses a consistent family of generalized median voter schemes, one on each path
`[x, z]` between leaves. Such a scheme has a point `α_S` on `[x, z]` for each coalition `S`, and
its outcome is the point at distance `max_S min (min_{i ∈ S} d(p_i, x), d(α_S, x))` from `x`.
The outcome thus lies strictly beyond a point `y` towards `z` exactly when some coalition `S`
with `α_S` strictly beyond `y` has all its reports strictly beyond `y`. Reading `win y z S` as
"`α_S` lies strictly beyond `y` towards `z`":

* the equilibrium `IsEquilibrium`, where no branch at `y` holds a winning coalition of reports,
  is the source's outcome, its unique critical point;
* `duality` relates the parameters read from the two ends of a path, where complementary
  coalitions exchange roles;
* `branch_eq` and `nesting` express the source's consistency condition between overlapping paths
  (p. 12), and `exclusive` rules out complementary coalitions pulling into different branches;
* `open_interior` reflects the strict inequality in "strictly beyond".

This correspondence is explanatory. The library does not prove an equivalence with the
path-based definition; `isStrategyProof_and_surjective_iff_exists_treeEMVS` characterizes
strategyproof onto rules directly in terms of `TreeEMVS`. -/
structure TreeEMVS {V : Type*} (W : WeightedGraph V) [Finite V]
    (ι : Type*) [Fintype ι] [Nonempty ι] [DecidableEq ι] where
  /-- Winning coalition predicate `win y q S` for direction `branch y q`. -/
  win : MetricGraph W → MetricGraph W → Finset ι → Prop
  /-- Winning coalitions depend only on the branch `branch y q`. -/
  branch_eq : ∀ {y q₁ q₂ : MetricGraph W},
    q₁ ≠ y → q₂ ≠ y → branch y q₁ = branch y q₂ → win y q₁ = win y q₂
  /-- The empty coalition never wins in any direction. -/
  empty_false : ∀ {y q : MetricGraph W}, q ≠ y → ¬ win y q ∅
  /-- The grand coalition always wins in every direction. -/
  univ_true : ∀ {y q : MetricGraph W}, q ≠ y → win y q Finset.univ
  /-- Winning coalitions are upward closed under subset inclusion. -/
  mono : ∀ {y q : MetricGraph W} {S T : Finset ι},
    q ≠ y → S ⊆ T → win y q S → win y q T
  /-- Winning in a smaller branch implies winning in any containing branch. -/
  nesting : ∀ {y₁ q₁ y₂ q₂ : MetricGraph W} {S : Finset ι},
    q₁ ≠ y₁ → q₂ ≠ y₂ → branch y₂ q₂ ⊆ branch y₁ q₁ → win y₂ q₂ S → win y₁ q₁ S
  /-- Duality between opposite directions along the geodesic `interval y₁ y₂`. -/
  duality : ∀ {y₁ y₂ : MetricGraph W} {S : Finset ι},
    y₁ ≠ y₂ → ¬ win y₁ y₂ S → win y₂ y₁ Sᶜ
  /-- Complementary coalitions cannot simultaneously win along distinct branches at `y`. -/
  exclusive : ∀ {y q₁ q₂ : MetricGraph W} {S : Finset ι},
    q₁ ≠ y → q₂ ≠ y → branch y q₁ ≠ branch y q₂ → ¬ (win y q₁ S ∧ win y q₂ Sᶜ)
  /-- Openness: a winning coalition at `(y, q)` remains winning at some strictly interior point
  on `interval y q`. -/
  open_interior : ∀ {y q : MetricGraph W} {S : Finset ι},
    q ≠ y → win y q S → ∃ p ∈ interval y q, p ≠ y ∧ p ≠ q ∧ win p q S

namespace TreeEMVS

variable {V : Type*} [Finite V] {W : WeightedGraph V}
variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- `y` is an equilibrium of `E` at profile `x` if no branch at `y` contains a winning
coalition of reported locations. -/
@[expose] def IsEquilibrium (E : TreeEMVS W ι) (x : ι → MetricGraph W)
    (y : MetricGraph W) : Prop :=
  ∀ q : MetricGraph W, q ≠ y →
    ∀ S : Finset ι, (∀ i, i ∈ S ↔ x i ∈ branch y q) → ¬ E.win y q S

private lemma equilibrium_unique (E : TreeEMVS W ι) {x : ι → MetricGraph W}
    {y₁ y₂ : MetricGraph W} (h₁ : E.IsEquilibrium x y₁) (h₂ : E.IsEquilibrium x y₂) :
    y₁ = y₂ := by
  classical
  by_contra hne
  let S₁ : Finset ι := Finset.univ.filter fun i => x i ∈ branch y₁ y₂
  let S₂ : Finset ι := Finset.univ.filter fun i => x i ∈ branch y₂ y₁
  have hS₁ : ∀ i, i ∈ S₁ ↔ x i ∈ branch y₁ y₂ := fun i => by simp [S₁]
  have hS₂ : ∀ i, i ∈ S₂ ↔ x i ∈ branch y₂ y₁ := fun i => by simp [S₂]
  have hnot : ¬ E.win y₁ y₂ S₁ := h₁ y₂ (Ne.symm hne) S₁ hS₁
  have hdual : E.win y₂ y₁ S₁ᶜ := E.duality hne hnot
  have hsub : S₁ᶜ ⊆ S₂ := by
    intro i hi
    rw [Finset.mem_compl, hS₁] at hi
    rw [hS₂]
    exact branch_symm hne hi
  exact h₂ y₁ hne S₂ hS₂ (E.mono hne hsub hdual)

private lemma tree_helly (hT : W.graph.IsTree) {ι' : Type*}
    (K : ι' → Set (MetricGraph W))
    (hconv : ∀ j, ∀ ⦃a b⦄, a ∈ K j → b ∈ K j → interval a b ⊆ K j)
    (hpair : ∀ j₁ j₂, (K j₁ ∩ K j₂).Nonempty)
    (F : Finset ι') (hF : F.Nonempty) : (⋂ j ∈ F, K j).Nonempty := by
  classical
  induction F using Finset.induction with
  | empty => exact absurd hF Finset.not_nonempty_empty
  | @insert j₀ F' hj₀ ih =>
    by_cases hF' : F' = ∅
    · subst hF'
      obtain ⟨z, hz, _⟩ := hpair j₀ j₀
      exact ⟨z, by simpa using hz⟩
    · have hF'_ne : F'.Nonempty := Finset.nonempty_iff_ne_empty.mpr hF'
      obtain ⟨p₁, hp₁⟩ := ih hF'_ne
      simp only [Set.mem_iInter] at hp₁
      by_cases hp₁j : p₁ ∈ K j₀
      · refine ⟨p₁, Set.mem_iInter₂.mpr fun j hj => ?_⟩
        rcases Finset.mem_insert.mp hj with rfl | hj'
        · exact hp₁j
        · exact hp₁ j hj'
      · have hstep : ∀ T : Finset ι', T ⊆ F' → T.Nonempty → (K j₀ ∩ ⋂ j ∈ T, K j).Nonempty := by
          intro T hTF' hTne
          induction T using Finset.induction with
          | empty => exact absurd hTne Finset.not_nonempty_empty
          | @insert j₁ T' hj₁ ihT =>
            by_cases hT' : T' = ∅
            · subst hT'
              obtain ⟨z, hz0, hz1⟩ := hpair j₀ j₁
              exact ⟨z, hz0, by simpa using hz1⟩
            · have hT'ne : T'.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT'
              obtain ⟨x₀, hx0_j₀, hx0_T⟩ :=
                ihT (Finset.Subset.trans (Finset.subset_insert _ _) hTF') hT'ne
              simp only [Set.mem_iInter] at hx0_T
              obtain ⟨x₁, hx1_j₀, hx1_j₁⟩ := hpair j₀ j₁
              have hT_sub : ∀ j ∈ insert j₁ T', j ∈ F' := fun j hj => hTF' hj
              let m := treeMedian hT p₁ x₀ x₁
              refine ⟨m, hconv j₀ hx0_j₀ hx1_j₀ (treeMedian_mem_yz hT p₁ x₀ x₁),
                Set.mem_iInter₂.mpr fun j hj => ?_⟩
              rcases Finset.mem_insert.mp hj with rfl | hjT'
              · exact hconv j (hp₁ j (hTF' (Finset.mem_insert_self j T'))) hx1_j₁
                  (interval_comm x₁ p₁ ▸ treeMedian_mem_zx hT p₁ x₀ x₁)
              · exact hconv j (hp₁ j (hTF' (Finset.mem_insert_of_mem hjT'))) (hx0_T j hjT')
                  (treeMedian_mem_xy hT p₁ x₀ x₁)
        obtain ⟨z, hz0, hzF'⟩ := hstep F' Finset.Subset.rfl hF'_ne
        simp only [Set.mem_iInter] at hzF'
        refine ⟨z, Set.mem_iInter₂.mpr fun j hj => ?_⟩
        rcases Finset.mem_insert.mp hj with rfl | hj'
        · exact hz0
        · exact hzF' j hj'

private lemma exists_equilibrium [Nonempty V] (hT : W.graph.IsTree) (E : TreeEMVS W ι)
    (x : ι → MetricGraph W) : ∃ y, E.IsEquilibrium x y := by
  classical
  by_contra hnone
  let S (y q : MetricGraph W) : Finset ι := Finset.univ.filter fun i => x i ∈ branch y q
  have hS_spec : ∀ y q i, i ∈ S y q ↔ x i ∈ branch y q := fun y q i => by simp [S]
  have hwin_ex : ∀ y : MetricGraph W, ∃ q : MetricGraph W, q ≠ y ∧ E.win y q (S y q) := by
    intro y
    by_contra hy
    push Not at hy
    apply hnone
    refine ⟨y, fun q hqy S' hS' hwin => ?_⟩
    have hEq : S' = S y q := Finset.ext fun i => (hS' i).trans (hS_spec y q i).symm
    exact hy q hqy (hEq ▸ hwin)
  let qy : MetricGraph W → MetricGraph W := fun y => (hwin_ex y).choose
  have hqy_ne : ∀ y, qy y ≠ y := fun y => (hwin_ex y).choose_spec.1
  have hqy_win : ∀ y, E.win y (qy y) (S y (qy y)) := fun y => (hwin_ex y).choose_spec.2
  have hwin_unique : ∀ {y q₁ q₂}, q₁ ≠ y → q₂ ≠ y →
      E.win y q₁ (S y q₁) → E.win y q₂ (S y q₂) → branch y q₁ = branch y q₂ := by
    intro y q₁ q₂ hq1 hq2 hw1 hw2
    by_contra hne
    have hdisj := branch_disjoint_of_ne hT hne
    have hsub : S y q₂ ⊆ (S y q₁)ᶜ := by
      intro i hi
      rw [Finset.mem_compl, hS_spec]
      rw [hS_spec] at hi
      exact Set.disjoint_right.mp hdisj hi
    exact E.exclusive hq1 hq2 hne ⟨hw1, E.mono hq2 hsub hw2⟩
  let M (y : MetricGraph W) : Set (MetricGraph W) := { w | w = y ∨ w ∈ branch y (qy y) }
  have hM_closed : ∀ y, IsClosed (M y) := by
    intro y
    rw [← isOpen_compl_iff, Metric.isOpen_iff]
    intro w₀ hw₀
    have hw₀_ne : w₀ ≠ y := fun heq => hw₀ (Or.inl heq)
    have hw₀_nb : w₀ ∉ branch y (qy y) := fun hmem => hw₀ (Or.inr hmem)
    refine ⟨dist y w₀, dist_pos.mpr hw₀_ne.symm, fun w hw_lt => ?_⟩
    rw [Set.mem_compl_iff]
    rw [Metric.mem_ball] at hw_lt
    rintro (rfl | hw_mem)
    · exact lt_irrefl _ hw_lt
    · have heq := branch_eq_of_mem hT hw_mem
      rw [← heq] at hw₀_nb
      simp only [branch, Set.mem_ofPred_eq, Classical.not_not, mem_interval_iff] at hw₀_nb
      have htri := dist_nonneg (x := w) (y := y)
      linarith [dist_comm w w₀]
  have hM_conv : ∀ y, ∀ ⦃a b⦄, a ∈ M y → b ∈ M y → interval a b ⊆ M y := by
    intro y a b ha hb z hz
    rcases ha with ha_eq | ha_b
    · rw [ha_eq] at hz
      rcases hb with hb_eq | hb_b
      · rw [hb_eq, interval_eq_singleton_self] at hz
        exact Or.inl hz
      · by_cases hzy : z = y
        · exact Or.inl hzy
        · exact Or.inr (interval_subset_branch hT hb_b hz hzy)
    · rcases hb with hb_eq | hb_b
      · rw [hb_eq] at hz
        by_cases hzy : z = y
        · exact Or.inl hzy
        · exact Or.inr (interval_subset_branch hT ha_b (interval_comm a y ▸ hz) hzy)
      · by_cases hzy : z = y
        · exact Or.inl hzy
        · refine Or.inr ?_
          by_contra hz_not
          have ha_not : y ∈ interval a z := by
            have := branch_eq_of_mem hT ha_b
            rw [← this] at hz_not
            simpa only [branch, Set.mem_ofPred_eq, Classical.not_not] using hz_not
          have hb_not : y ∈ interval b z := by
            have := branch_eq_of_mem hT hb_b
            rw [← this] at hz_not
            simpa only [branch, Set.mem_ofPred_eq, Classical.not_not] using hz_not
          have e1 := mem_interval_iff.mp hz
          have e2 := mem_interval_iff.mp ha_not
          have e3 := mem_interval_iff.mp hb_not
          have hd : dist y z = 0 := by
            linarith [dist_triangle a y b, dist_comm y z, dist_comm z b, dist_comm b z,
              dist_comm b y, dist_nonneg (x := y) (y := z)]
          exact hzy (dist_eq_zero.mp hd).symm
  have hM_pair : ∀ y₁ y₂, (M y₁ ∩ M y₂).Nonempty := by
    intro y₁ y₂
    by_cases h12 : y₁ = y₂
    · subst h12
      exact ⟨y₁, Or.inl rfl, Or.inl rfl⟩
    · by_cases hb1 : branch y₁ (qy y₁) = branch y₁ y₂
      · by_cases hb2 : branch y₂ (qy y₂) = branch y₂ y₁
        · exact ⟨y₂, Or.inr (hb1 ▸ mem_branch_self (Ne.symm h12)), Or.inl rfl⟩
        · have hnot : ¬ E.win y₂ y₁ (S y₂ y₁) := fun hw =>
            hb2 (hwin_unique (hqy_ne y₂) h12 (hqy_win y₂) hw)
          have hdual := E.duality (Ne.symm h12) hnot
          have hsub : (S y₂ y₁)ᶜ ⊆ S y₁ y₂ := by
            intro i hi
            rw [Finset.mem_compl, hS_spec] at hi
            rw [hS_spec]
            exact branch_symm (Ne.symm h12) hi
          have hw1 : E.win y₁ y₂ (S y₁ y₂) := E.mono (Ne.symm h12) hsub hdual
          have hb1' : branch y₁ (qy y₁) = branch y₁ y₂ :=
            hwin_unique (hqy_ne y₁) (Ne.symm h12) (hqy_win y₁) hw1
          exact ⟨y₂, Or.inr (hb1' ▸ mem_branch_self (Ne.symm h12)), Or.inl rfl⟩
      · have hnot : ¬ E.win y₁ y₂ (S y₁ y₂) := fun hw =>
          hb1 (hwin_unique (hqy_ne y₁) (Ne.symm h12) (hqy_win y₁) hw)
        have hdual := E.duality h12 hnot
        have hsub : (S y₁ y₂)ᶜ ⊆ S y₂ y₁ := by
          intro i hi
          rw [Finset.mem_compl, hS_spec] at hi
          rw [hS_spec]
          exact branch_symm h12 hi
        have hw2 : E.win y₂ y₁ (S y₂ y₁) := E.mono h12 hsub hdual
        have hb2 : branch y₂ (qy y₂) = branch y₂ y₁ :=
          hwin_unique (hqy_ne y₂) h12 (hqy_win y₂) hw2
        exact ⟨y₁, Or.inl rfl, Or.inr (hb2 ▸ mem_branch_self h12)⟩
  have hfin : ∀ F : Finset (MetricGraph W), (⋂ y ∈ F, M y).Nonempty := by
    intro F
    by_cases hF : F = ∅
    · subst hF
      obtain ⟨v₀⟩ := ‹Nonempty V›
      exact ⟨vertex v₀, by simp⟩
    · exact tree_helly hT M hM_conv hM_pair F (Finset.nonempty_iff_ne_empty.mpr hF)
  have hnonempty_iInter : (⋂ y : MetricGraph W, M y).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hcov : (Set.univ : Set (MetricGraph W)) ⊆ ⋃ y : MetricGraph W, (M y)ᶜ := by
      intro z _
      by_contra hnot
      rw [Set.mem_iUnion] at hnot
      push Not at hnot
      have hz : z ∈ ⋂ y : MetricGraph W, M y := Set.mem_iInter.mpr fun y => by
        simpa only [Set.mem_compl_iff, Classical.not_not] using hnot y
      rw [hemp] at hz
      exact hz
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (M y)ᶜ)
      (fun y => (hM_closed y).isOpen_compl) hcov
    obtain ⟨z, hz⟩ := hfin t
    have hz' : z ∈ ⋃ y ∈ t, (M y)ᶜ := ht (Set.mem_univ z)
    simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_compl_iff] at hz hz'
    obtain ⟨y, hy, hny⟩ := hz'
    exact hny (hz y hy)
  obtain ⟨yStar, hyStar⟩ := hnonempty_iInter
  rw [Set.mem_iInter] at hyStar
  let qStar := qy yStar
  have hqStar_ne : qStar ≠ yStar := hqy_ne yStar
  obtain ⟨v₀, hv₀_mem, hv₀_pos, _, hstem_sub, r₀, hr₀_pos, _, _⟩ :=
    exists_stem_segment hT hqStar_ne
  have hv₀_ne : v₀ ≠ yStar := fun h => by
    rw [h, _root_.dist_self] at hv₀_pos
    exact lt_irrefl (0 : ℝ) hv₀_pos
  have hbr_eq : branch yStar v₀ = branch yStar qStar := branch_eq_of_mem hT hv₀_mem
  have hS_eq : S yStar v₀ = S yStar qStar := Finset.ext fun i => by
    rw [hS_spec, hS_spec, hbr_eq]
  have hwin_v0 : E.win yStar v₀ (S yStar qStar) := by
    rw [← hS_eq, E.branch_eq hv₀_ne hqStar_ne hbr_eq, hS_eq]
    exact hqy_win yStar
  obtain ⟨p₀, hp₀_mem, hp₀_ne_y, hp₀_ne_v, hp₀_win⟩ := E.open_interior hv₀_ne hwin_v0
  have hdist_pos : ∀ i ∈ S yStar qStar, 0 < dist yStar (x i) := fun i hi => by
    rw [hS_spec] at hi
    exact dist_pos.mpr fun heq => (notMem_branch_self yStar qStar) (heq ▸ hi)
  let δ : ℝ := if hne : (S yStar qStar).Nonempty then
    ((S yStar qStar).attach.image fun i => dist yStar (x i.1)).min'
      (by simpa using hne) else 1
  have hδ_pos : 0 < δ := by
    dsimp only [δ]
    split_ifs with hne
    · rw [Finset.lt_min'_iff]
      intro d hd
      rw [Finset.mem_image] at hd
      obtain ⟨⟨i, hi⟩, _, rfl⟩ := hd
      exact hdist_pos i hi
    · exact zero_lt_one
  let r : ℝ := min (min r₀ δ) (dist yStar p₀) / 2
  have hr_pos : 0 < r := by
    have : 0 < dist yStar p₀ := dist_pos.mpr hp₀_ne_y.symm
    positivity
  have hr_le : r ≤ dist yStar p₀ := by
    have : r ≤ dist yStar p₀ / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    linarith
  obtain ⟨p, hp_mem_p0, hp_dist, _⟩ := exists_mem_interval_dist_eq yStar p₀ ⟨hr_pos.le, hr_le⟩
  have hp_ne_y : p ≠ yStar := fun heq => by
    rw [heq, _root_.dist_self] at hp_dist
    linarith
  have hp_mem_v0 : p ∈ interval yStar v₀ :=
    interval_subset_of_mem hT (left_mem_interval yStar v₀) hp₀_mem hp_mem_p0
  have hp_ne_v0 : p ≠ v₀ := fun heq => by
    have hp_lt_p0 : dist yStar p < dist yStar p₀ := by
      have : r ≤ dist yStar p₀ / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      linarith
    have h2 : dist yStar p₀ ≤ dist yStar v₀ := by
      have e1 := mem_interval_iff.mp hp₀_mem
      linarith [dist_nonneg (x := p₀) (y := v₀)]
    have h3 : dist yStar v₀ < dist yStar v₀ := by
      calc dist yStar v₀ = dist yStar p := heq ▸ rfl
        _ < dist yStar p₀ := hp_lt_p0
        _ ≤ dist yStar v₀ := h2
    exact lt_irrefl _ h3
  have hp_in_b : p ∈ branch yStar qStar :=
    (branch_eq_of_mem hT hv₀_mem).symm ▸
      interval_subset_branch hT (mem_branch_self hv₀_ne) hp_mem_v0 hp_ne_y
  have hp_sub : branch p₀ v₀ ⊆ branch p v₀ := by
    have hp0_p_v0 : p₀ ∈ interval p v₀ := by
      have e1 := mem_interval_iff.mp hp₀_mem
      have e2 := mem_interval_iff.mp hp_mem_p0
      have e3 := mem_interval_iff.mp hp_mem_v0
      rw [mem_interval_iff]
      linarith
    intro z hz
    exact branch_subset_of_mem_interval hp0_p_v0 (fun heq => by
      have hpr : dist yStar p₀ = r := heq ▸ hp_dist
      have : r ≤ dist yStar p₀ / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      have : 0 < dist yStar p₀ := dist_pos.mpr hp₀_ne_y.symm
      linarith) hz
  have hp_win_v0 : E.win p v₀ (S yStar qStar) :=
    E.nesting hp_ne_v0.symm hp₀_ne_v.symm hp_sub hp₀_win
  have hS_p_y : S p yStar = (S yStar qStar)ᶜ := by
    ext i
    rw [Finset.mem_compl, hS_spec, hS_spec]
    constructor
    · intro hi_py hi_yq
      have hδ_le : δ ≤ dist yStar (x i) := by
        dsimp only [δ]
        have hne : (S yStar qStar).Nonempty := ⟨i, (hS_spec _ _ _).mpr hi_yq⟩
        simp only [hne, ↓reduceDIte]
        refine Finset.min'_le _ _ ?_
        rw [Finset.mem_image]
        exact ⟨⟨i, (hS_spec _ _ _).mpr hi_yq⟩, Finset.mem_attach _ _, rfl⟩
      have hp_le_xi : dist yStar p ≤ dist yStar (x i) := by
        have h1 : r ≤ min r₀ δ / 2 :=
          div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
        have h2 : min r₀ δ ≤ δ := min_le_right _ _
        linarith
      have hp_in_xi : p ∈ interval yStar (x i) := hstem_sub (x i) hi_yq p hp_mem_v0 hp_le_xi
      exact hi_py hp_in_xi
    · intro hi_not
      have hp_not_qy : p ∈ branch yStar qStar := hp_in_b
      rw [← branch_eq_of_mem hT hp_not_qy] at hi_not
      exact branch_symm hp_ne_y.symm hi_not
  have hbr_p_ne : branch p v₀ ≠ branch p yStar := by
    intro heq
    have hv0_in : v₀ ∈ branch p v₀ := mem_branch_self hp_ne_v0.symm
    rw [heq] at hv0_in
    have hp_in : p ∈ interval yStar v₀ := hp_mem_v0
    exact hv0_in hp_in
  have hnot_py : ¬ E.win p yStar (S p yStar) := by
    rw [hS_p_y]
    intro hwin_py
    exact E.exclusive hp_ne_v0.symm hp_ne_y.symm hbr_p_ne ⟨hp_win_v0, hwin_py⟩
  have hy_in_Mp := hyStar p
  rcases hy_in_Mp with rfl | hy_br
  · exact hp_ne_y rfl
  · have hb_eq : branch p (qy p) = branch p yStar :=
      (branch_eq_of_mem hT hy_br).symm
    have hS_eq' : S p (qy p) = S p yStar := Finset.ext fun i => by
      rw [hS_spec, hS_spec, hb_eq]
    have hw_py : E.win p yStar (S p yStar) := by
      rw [← hS_eq', ← E.branch_eq (hqy_ne p) hp_ne_y.symm hb_eq]
      exact hqy_win p
    exact hnot_py hw_py

/-- Every `TreeEMVS` admits a unique equilibrium for every agent profile. -/
theorem existsUnique_equilibrium [Nonempty V] (hT : W.graph.IsTree) (E : TreeEMVS W ι)
    (x : ι → MetricGraph W) : ∃! y, E.IsEquilibrium x y := by
  obtain ⟨y, hy⟩ := E.exists_equilibrium hT x
  exact ⟨y, hy, fun y' hy' => E.equilibrium_unique hy' hy⟩

/-- Evaluates a `TreeEMVS` on profile `x` by returning its unique equilibrium location. -/
noncomputable def eval [Nonempty V] (hT : W.graph.IsTree) (E : TreeEMVS W ι)
    (x : ι → MetricGraph W) : MetricGraph W :=
  (E.existsUnique_equilibrium hT x).choose

theorem eval_eq_iff [Nonempty V] (hT : W.graph.IsTree) (E : TreeEMVS W ι)
    (x : ι → MetricGraph W) (y : MetricGraph W) :
    E.eval hT x = y ↔ E.IsEquilibrium x y := by
  have hspec := (E.existsUnique_equilibrium hT x).choose_spec
  constructor
  · rintro rfl
    exact hspec.1
  · intro hy
    exact (hspec.2 y hy).symm

theorem eval_const [Nonempty V] (hT : W.graph.IsTree) (E : TreeEMVS W ι)
    (y : MetricGraph W) : E.eval hT (fun _ => y) = y := by
  rw [E.eval_eq_iff hT]
  intro q hq S hS
  have hS_emp : S = ∅ := Finset.eq_empty_of_forall_notMem fun i hi => by
    rw [hS i] at hi
    exact (notMem_branch_self y q) hi
  rw [hS_emp]
  exact E.empty_false hq

theorem eval_surjective [Nonempty V] (hT : W.graph.IsTree) (E : TreeEMVS W ι) :
    Function.Surjective (E.eval hT) :=
  fun y => ⟨fun _ => y, E.eval_const hT y⟩

/-- Every `TreeEMVS` evaluates to a strongly group-strategyproof mechanism. -/
theorem eval_isGroupStrategyProof [Nonempty V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) (E : TreeEMVS W ι) :
    (Mechanism.deterministic (E.eval hT)).IsGroupStrategyProof := by
  classical
  rw [Mechanism.isGroupStrategyProof_deterministic_iff]
  rintro x z A ⟨hle, i₀, hi₀, hlt⟩
  let y := E.eval hT x
  let y' := E.eval hT (A.piecewise z x)
  have hne : y ≠ y' := by
    intro heq
    have : dist (x i₀) y' = dist (x i₀) y := by simp [y, y', heq]
    exact hlt.ne this
  have hA_sub : ∀ i ∈ A, x i ∈ branch y y' := by
    intro i hi
    by_contra hnot
    simp only [branch, Set.mem_ofPred_eq, Classical.not_not, mem_interval_iff] at hnot
    have hle_i := hle i hi
    have hpos : 0 < dist y y' := dist_pos.mpr hne
    linarith [hpos, dist_comm y y', dist_comm (x i) y, dist_comm (x i) y']
  let S : Finset ι := Finset.univ.filter fun i => x i ∈ branch y y'
  have hS : ∀ i, i ∈ S ↔ x i ∈ branch y y' := fun i => by simp [S]
  have heq_y : E.IsEquilibrium x y := (E.eval_eq_iff hT x y).mp rfl
  have hnot : ¬ E.win y y' S := heq_y y' hne.symm S hS
  have hdual : E.win y' y Sᶜ := E.duality hne hnot
  let S' : Finset ι := Finset.univ.filter fun i => A.piecewise z x i ∈ branch y' y
  have hS' : ∀ i, i ∈ S' ↔ A.piecewise z x i ∈ branch y' y := fun i => by simp [S']
  have hsub : Sᶜ ⊆ S' := by
    intro i hi
    rw [Finset.mem_compl, hS] at hi
    have hiA : i ∉ A := fun hmem => hi (hA_sub i hmem)
    rw [hS', Finset.piecewise_eq_of_notMem _ _ _ hiA]
    exact branch_symm hne hi
  have heq_y' : E.IsEquilibrium (A.piecewise z x) y' := (E.eval_eq_iff hT _ y').mp rfl
  exact heq_y' y hne S' hS' (E.mono hne hsub hdual)

theorem eval_isStrategyProof [Nonempty V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) (E : TreeEMVS W ι) :
    (Mechanism.deterministic (E.eval hT)).IsStrategyProof :=
  (E.eval_isGroupStrategyProof hT).isStrategyProof

end TreeEMVS

end TreeEMVS

section Subtrees

variable {V : Type*} [Finite V] {W : WeightedGraph V}
variable {ι : Type*} [Finite ι] [DecidableEq ι]

private lemma pareto_branch [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_onto : Function.Surjective f)
    (x : ι → MetricGraph W) {q : MetricGraph W} (hq : q ≠ f x) :
    ¬ ∀ i, x i ∈ branch (f x) q := by
  classical
  let _ := Fintype.ofFinite ι
  intro hall
  let y := f x
  have hq' : q ≠ y := hq
  obtain ⟨v₀, hv₀_mem, _, _, hstem_sub, r₀, hr₀_pos, hr₀_le, hball⟩ :=
    exists_stem_segment hT hq'
  have hall_pos : ∀ i : ι, 0 < dist y (x i) := fun i =>
    dist_pos.mpr fun heq => by
      have hi := hall i
      change x i ∈ branch y q at hi
      rw [← heq] at hi
      exact notMem_branch_self y q hi
  let dmin : ℝ := if hne : (Finset.univ : Finset ι).Nonempty then
    (Finset.univ.image fun i => dist y (x i)).min' (Finset.image_nonempty.mpr hne) else 1
  have hdmin_pos : 0 < dmin := by
    dsimp only [dmin]
    split_ifs with hne
    · rw [Finset.lt_min'_iff]
      intro d hd
      rw [Finset.mem_image] at hd
      obtain ⟨i, _, rfl⟩ := hd
      exact hall_pos i
    · exact zero_lt_one
  let r : ℝ := min r₀ (dmin / 3)
  have hr_pos : 0 < r := lt_min hr₀_pos (by positivity)
  have hr_le_r0 : r ≤ r₀ := min_le_left _ _
  have hr_le_v0 : r ≤ dist y v₀ := hr_le_r0.trans hr₀_le
  obtain ⟨p, hp_mem, hp_dist, _⟩ := exists_mem_interval_dist_eq y v₀ ⟨hr_pos.le, hr_le_v0⟩
  have hp_ne_y : p ≠ y := fun heq => by
    rw [heq, _root_.dist_self] at hp_dist
    linarith
  have hsp : ∀ (z : ι → MetricGraph W) (i : ι) (w : MetricGraph W),
      dist (f z) (z i) ≤ dist (f (Function.update z i w)) (z i) := fun z i w => by
    simpa only [_root_.dist_comm] using
      (Mechanism.isStrategyProof_deterministic_iff f).mp hf_sp z i w
  have hconst : ∀ (n : ℕ) (z : ι → MetricGraph W),
      (Finset.univ.filter fun i => z i ≠ p).card = n →
      (∀ i, z i = p ∨ z i = x i) → f z = y → f (fun _ => p) = y := by
    intro n
    induction n with
    | zero =>
      intro z hcard _ hfz
      have hemp : (Finset.univ.filter fun i => z i ≠ p) = ∅ := Finset.card_eq_zero.mp hcard
      have heq : z = fun _ => p := by
        funext i
        by_contra hne
        have hi : i ∈ Finset.univ.filter fun i => z i ≠ p := by simp [hne]
        rw [hemp] at hi
        exact Finset.notMem_empty i hi
      simpa [heq] using hfz
    | succ k ih =>
      intro z hcard hz_cases hfz
      have hne : (Finset.univ.filter fun i => z i ≠ p).Nonempty :=
        Finset.card_pos.mp (hcard ▸ Nat.succ_pos k)
      obtain ⟨i₀, hi₀⟩ := hne
      have hi₀_ne : z i₀ ≠ p := (Finset.mem_filter.mp hi₀).2
      have hi₀_eq : z i₀ = x i₀ := (hz_cases i₀).resolve_left hi₀_ne
      let z' := Function.update z i₀ p
      have hball_z' : f z' ∈ interval y v₀ ∧ dist y (f z') ≤ 2 * dist y p := by
        refine hball p hp_mem (hp_dist.symm ▸ hr_pos) (hp_dist.symm ▸ hr_le_r0) (f z') ?_
        have := hsp z' i₀ (z i₀)
        have hupd : Function.update z' i₀ (z i₀) = z := by
          funext j
          by_cases hj : j = i₀
          · subst hj; simp [z']
          · simp [z', hj]
        rw [hupd, hfz] at this
        simpa only [z', Function.update_self, _root_.dist_comm] using this
      have hxi_mem : p ∈ interval y (x i₀) := by
        have hxi_le : dist y p ≤ dist y (x i₀) := by
          have hmem_univ : (Finset.univ : Finset ι).Nonempty := ⟨i₀, Finset.mem_univ i₀⟩
          have hd : dmin ≤ dist y (x i₀) := by
            dsimp only [dmin]
            simp only [hmem_univ, ↓reduceDIte]
            exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i₀, Finset.mem_univ i₀, rfl⟩)
          have : r ≤ dmin / 3 := min_le_right _ _
          linarith
        exact hstem_sub (x i₀) (hall i₀) p hp_mem hxi_le
      have hfzp_mem : f z' ∈ interval y (x i₀) := by
        have hfz_le_xi : dist y (f z') ≤ dist y (x i₀) := by
          have hmem_univ : (Finset.univ : Finset ι).Nonempty := ⟨i₀, Finset.mem_univ i₀⟩
          have hd : dmin ≤ dist y (x i₀) := by
            dsimp only [dmin]
            simp only [hmem_univ, ↓reduceDIte]
            exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i₀, Finset.mem_univ i₀, rfl⟩)
          have : r ≤ dmin / 3 := min_le_right _ _
          linarith [hball_z'.2]
        by_cases hfz_y : f z' = y
        · rw [hfz_y]
          exact left_mem_interval y (x i₀)
        · have hfz_br : f z' ∈ branch y q := by
            have := (branch_eq_of_mem hT hv₀_mem)
            rw [← this]
            exact interval_subset_branch hT (mem_branch_self (fun heq => by
              rw [heq] at hv₀_mem; exact notMem_branch_self y q hv₀_mem)) hball_z'.1 hfz_y
          exact hstem_sub (x i₀) (hall i₀) (f z') hball_z'.1 hfz_le_xi
      have hfz_sp := hsp z i₀ p
      rw [hfz, hi₀_eq] at hfz_sp
      change dist y (x i₀) ≤ dist (f z') (x i₀) at hfz_sp
      have he1 := mem_interval_iff.mp hfzp_mem
      have hd0 : dist y (f z') = 0 := by
        linarith [_root_.dist_comm (x i₀) y, _root_.dist_comm (x i₀) (f z'),
          _root_.dist_comm y (f z'), _root_.dist_comm (f z') (x i₀),
          dist_nonneg (x := y) (y := f z')]
      have hfz'_eq : f z' = y := (dist_eq_zero.mp hd0).symm
      have hsub : Finset.univ.filter (fun i => z' i ≠ p) =
          (Finset.univ.filter fun i => z i ≠ p).erase i₀ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, z']
        by_cases hj : j = i₀
        · subst hj; simp
        · simp [hj]
      have hcard' : (Finset.univ.filter fun i => z' i ≠ p).card = k := by
        rw [hsub, Finset.card_erase_of_mem hi₀, hcard]
        simp
      have hz'_cases : ∀ i, z' i = p ∨ z' i = x i := fun i => by
        by_cases hi : i = i₀
        · subst hi; simp [z']
        · simpa [z', hi] using hz_cases i
      exact ih z' hcard' hz'_cases hfz'_eq
  have hfp : f (fun _ => p) = y := hconst _ x rfl (fun i => Or.inr rfl) rfl
  have hunan : f (fun _ => p) = p := unanimous_of_surjective_isStrategyProof hf_sp hf_onto p
  exact hp_ne_y (hunan.symm.trans hfp)

private def ConvexSet (W : WeightedGraph V) (K : Set (MetricGraph W)) : Prop :=
  K.Nonempty ∧ IsClosed K ∧ ∀ ⦃a b⦄, a ∈ K → b ∈ K → interval a b ⊆ K

private lemma exists_proj_convex (hT : W.graph.IsTree) {K : Set (MetricGraph W)}
    (hK : ConvexSet W K) (y : MetricGraph W) :
    ∃ p ∈ K, ∀ z ∈ K, p ∈ interval y z := by
  have hKc : IsCompact K := hK.2.1.isCompact
  obtain ⟨p, hpK, hp_min⟩ :=
    hKc.exists_isMinOn hK.1 (continuous_const.dist continuous_id).continuousOn
  refine ⟨p, hpK, fun z hz => ?_⟩
  by_contra hnot
  let m := treeMedian hT y p z
  have hmK : m ∈ K := hK.2.2 hpK hz (treeMedian_mem_yz hT y p z)
  have hmp : m ≠ p := fun heq => hnot (heq ▸
    (interval_comm z y ▸ treeMedian_mem_zx hT y p z))
  have hle : dist y p ≤ dist y m := hp_min hmK
  have h1 := mem_interval_iff.mp (treeMedian_mem_xy hT y p z)
  have hpos : 0 < dist m p := dist_pos.mpr hmp
  linarith

private noncomputable def projConvex (hT : W.graph.IsTree) {K : Set (MetricGraph W)}
    (hK : ConvexSet W K) (y : MetricGraph W) : MetricGraph W :=
  (exists_proj_convex hT hK y).choose

private lemma projConvex_mem (hT : W.graph.IsTree) {K : Set (MetricGraph W)}
    (hK : ConvexSet W K) (y : MetricGraph W) : projConvex hT hK y ∈ K :=
  (exists_proj_convex hT hK y).choose_spec.1

private lemma mem_interval_projConvex (hT : W.graph.IsTree) {K : Set (MetricGraph W)}
    (hK : ConvexSet W K) (y : MetricGraph W) {z : MetricGraph W} (hz : z ∈ K) :
    projConvex hT hK y ∈ interval y z :=
  (exists_proj_convex hT hK y).choose_spec.2 z hz

private lemma projConvex_eq_self (hT : W.graph.IsTree) {K : Set (MetricGraph W)}
    (hK : ConvexSet W K) {y : MetricGraph W} (hy : y ∈ K) :
    projConvex hT hK y = y := by
  have h := mem_interval_projConvex hT hK y hy
  rw [interval_eq_singleton_self] at h
  exact h

private lemma mem_branch_projConvex_iff (hT : W.graph.IsTree) {K : Set (MetricGraph W)}
    (hK : ConvexSet W K) {p q : MetricGraph W} (hp : p ∈ K) (hq : q ∈ K)
    (z : MetricGraph W) :
    z ∈ branch p q ↔ projConvex hT hK z ∈ branch p q := by
  let π := projConvex hT hK z
  have hzp := mem_interval_iff.mp (mem_interval_projConvex hT hK z hp)
  have hzq := mem_interval_iff.mp (mem_interval_projConvex hT hK z hq)
  simp only [branch, Set.mem_ofPred_eq, mem_interval_iff]
  constructor <;> intro h heq <;> apply h <;>
    linarith [hzp, hzq, dist_comm z p, dist_comm z q, dist_comm p π, dist_comm q π]

private lemma range_of_convex
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_onto : Function.Surjective f)
    {K : Set (MetricGraph W)} (hK : ConvexSet W K)
    {x : ι → MetricGraph W} (hx : ∀ i, x i ∈ K) : f x ∈ K := by
  by_contra hnot
  let y := f x
  let p := projConvex hT hK y
  have hp_ne : p ≠ y := fun heq => hnot (by
    change y ∈ K
    rw [← heq]
    exact projConvex_mem hT hK y)
  apply pareto_branch hT hf_sp hf_onto x hp_ne
  intro i
  have hm := mem_interval_projConvex hT hK y (hx i)
  simp only [branch, Set.mem_ofPred_eq]
  intro hmem
  have e1 := mem_interval_iff.mp hm
  have e2 := mem_interval_iff.mp hmem
  have hd : dist p y = 0 := by linarith [dist_comm p (x i), dist_comm p y, dist_comm y (x i)]
  exact hp_ne (dist_eq_zero.mp hd)

private def ConvexVertices (W : WeightedGraph V) (S : Finset V) : Prop :=
  S.Nonempty ∧ ∀ u ∈ S, ∀ v ∈ S, ∀ (p : W.graph.Walk u v), p.IsPath → ∀ w ∈ p.support, w ∈ S

private def subtree (W : WeightedGraph V) (S : Finset V) : Set (MetricGraph W) :=
  { z | ∃ u ∈ S, ∃ v ∈ S, z ∈ interval (vertex u) (vertex v) }

private lemma vertex_mem_subtree (W : WeightedGraph V) {S : Finset V} {u : V} (hu : u ∈ S) :
    vertex u ∈ subtree W S :=
  ⟨u, hu, u, hu, left_mem_interval (vertex u) (vertex u)⟩

omit [Finite V] in
private lemma exists_cut_dart_of_notMem (hT : W.graph.IsTree) {S : Finset V}
    (hS : ConvexVertices W S) {v : V} (hv : v ∉ S) :
    ∃ d : W.graph.Dart,
      edgeProj hT d (vertex v) = W.weight d.edge ∧
      ∀ u ∈ S, edgeProj hT d (vertex u) = 0 := by
  obtain ⟨u₀, hu₀⟩ := hS.1
  obtain ⟨q, hq⟩ := (W.connected v u₀).exists_isPath
  have hstep : ∀ {a b : V} (p : W.graph.Walk a b), a ∉ S → b ∈ S →
      ∃ d : W.graph.Dart, d.snd ∉ S ∧ d.fst ∈ S ∧
        (W.graph.deleteEdges {d.edge}).Reachable a d.snd := by
    intro a b p
    induction p with
    | nil => intro ha hb; exact absurd hb ha
    | @cons x y z hadj q' ih =>
      intro hx hz
      by_cases hy : y ∈ S
      · refine ⟨⟨(y, x), hadj.symm⟩, hx, hy, .refl x⟩
      · obtain ⟨d, hd_snd, hd_fst, hreach⟩ := ih hy hz
        refine ⟨d, hd_snd, hd_fst, ?_⟩
        have hne_e : s(x, y) ≠ d.edge := fun he => by
          rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hx hd_fst
          · exact hy hd_fst
        have hne_adj : (W.graph.deleteEdges {d.edge}).Adj x y := by
          rw [deleteEdges_adj]
          exact ⟨hadj, fun h => hne_e (Set.mem_singleton_iff.mp h)⟩
        exact hne_adj.reachable.trans hreach
  obtain ⟨d, hd_snd, hd_fst, hreach⟩ := hstep q hv hu₀
  refine ⟨d, ?_, ?_⟩
  · rw [edgeProj_vertex_eq_weight_iff]
    intro hrev
    exact (isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic d.adj))
      (by simpa only [Dart.edge] using hrev.symm.trans hreach)
  · intro u hu
    rw [edgeProj_vertex_eq_zero_iff]
    by_contra hnot
    obtain ⟨p, hp⟩ := (W.connected d.fst u).exists_isPath
    have hsplit : d.snd ∈ p.support := by
      by_contra hsnd
      have hne : ∀ e ∈ p.edges, e ≠ d.edge := fun e he hed => by
        rw [hed] at he
        have hed' : s(d.fst, d.snd) ∈ p.edges := he
        exact hsnd (p.snd_mem_support_of_mem_edges hed')
      have hr : (W.graph.deleteEdges {d.edge}).Reachable d.fst u :=
        ⟨p.toDeleteEdges {d.edge} (fun e he hmem => by
          rw [Set.mem_singleton_iff] at hmem
          exact hne e he hmem)⟩
      exact hnot hr.symm
    exact hd_snd (hS.2 d.fst hd_fst u hu p hp d.snd hsplit)

private lemma edgeProj_eq_zero_of_mem_interval (hT : W.graph.IsTree) {d : W.graph.Dart}
    {p q z : MetricGraph W} (hp : edgeProj hT d p = 0) (hq : edgeProj hT d q = 0)
    (hz : z ∈ interval p q) : edgeProj hT d z = 0 := by
  by_contra hne
  have hpos : 0 < edgeProj hT d z := lt_of_le_of_ne (edgeProj_nonneg hT d z) (Ne.symm hne)
  have hm₁ := mem_interval_iff.mp (vertex_fst_mem_interval_of_edgeProj hT d hp hpos)
  have hm₂ := mem_interval_iff.mp (vertex_fst_mem_interval_of_edgeProj hT d hq hpos)
  have hz_mem := mem_interval_iff.mp hz
  have hd_pos : 0 < dist (vertex d.fst : MetricGraph W) z := by
    by_contra hle
    push Not at hle
    have heq : (vertex d.fst : MetricGraph W) = z := dist_eq_zero.mp (le_antisymm hle dist_nonneg)
    have h0 : edgeProj hT d (vertex d.fst) = 0 :=
      (edgeProj_vertex_eq_zero_iff hT d d.fst).mpr (.refl _)
    rw [heq] at h0
    linarith
  linarith [dist_triangle p (vertex d.fst) q, dist_comm (vertex d.fst : MetricGraph W) z,
    dist_comm q z, dist_comm q (vertex d.fst)]

private lemma vertex_mem_subtree_iff (hT : W.graph.IsTree) {S : Finset V}
    (hS : ConvexVertices W S) (v : V) :
    vertex v ∈ subtree W S ↔ v ∈ S := by
  constructor
  · rintro ⟨u₁, hu₁, u₂, hu₂, hv⟩
    by_contra hv_not
    obtain ⟨d, hdv, hdu⟩ := exists_cut_dart_of_notMem hT hS hv_not
    have h0 := edgeProj_eq_zero_of_mem_interval hT (hdu u₁ hu₁) (hdu u₂ hu₂) hv
    linarith [W.dart_weight_pos d]
  · exact vertex_mem_subtree W

private lemma edgePoint_mem_subtree_iff (hT : W.graph.IsTree) {S : Finset V}
    (hS : ConvexVertices W S) {d : W.graph.Dart} {t : unitInterval}
    (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    edgePoint d t ∈ subtree W S ↔ d.fst ∈ S ∧ d.snd ∈ S := by
  constructor
  · rintro ⟨u₁, hu₁, u₂, hu₂, hz⟩
    constructor
    · by_contra hfst
      obtain ⟨d₀, hd₀_snd, hd₀_u⟩ := exists_cut_dart_of_notMem hT hS hfst
      have hpos : 0 < edgeProj hT d₀ (edgePoint d t) := by
        by_cases he : d.edge = d₀.edge
        · rcases (dart_edge_eq_iff d d₀).mp he with rfl | hsym
          · rw [edgeProj_edgePoint_self]
            exact mul_pos ht0 (W.dart_weight_pos d)
          · rw [hsym, edgeProj_edgePoint_symm]
            exact mul_pos (sub_pos.mpr ht1) (W.dart_weight_pos d₀)
        · rw [edgeProj_edgePoint_of_edge_ne hT he, hd₀_snd]
          exact W.dart_weight_pos d₀
      exact hpos.ne' (edgeProj_eq_zero_of_mem_interval hT (hd₀_u u₁ hu₁) (hd₀_u u₂ hu₂) hz)
    · by_contra hsnd
      obtain ⟨d₀, hd₀_snd, hd₀_u⟩ := exists_cut_dart_of_notMem hT hS hsnd
      have hpos : 0 < edgeProj hT d₀ (edgePoint d t) := by
        by_cases he : d.edge = d₀.edge
        · rcases (dart_edge_eq_iff d d₀).mp he with rfl | hsym
          · rw [edgeProj_edgePoint_self]
            exact mul_pos ht0 (W.dart_weight_pos d)
          · rw [hsym, edgeProj_edgePoint_symm]
            exact mul_pos (sub_pos.mpr ht1) (W.dart_weight_pos d₀)
        · rw [edgeProj_edgePoint_of_edge_ne hT he]
          have hd_adj : (W.graph.deleteEdges {d₀.edge}).Adj d.fst d.snd :=
            ⟨d.adj, fun h => he (Set.mem_singleton_iff.mp h.1)⟩
          have hd_fst : edgeProj hT d₀ (vertex d.fst) = W.weight d₀.edge := by
            rw [edgeProj_vertex_eq_weight_iff]
            intro hr
            have hs : ¬ (W.graph.deleteEdges {d₀.edge}).Reachable d.snd d₀.fst := by
              rw [← edgeProj_vertex_eq_weight_iff hT d₀ d.snd]
              exact hd₀_snd
            exact hs (hd_adj.symm.reachable.trans hr)
          rw [hd_fst]
          exact W.dart_weight_pos d₀
      exact hpos.ne' (edgeProj_eq_zero_of_mem_interval hT (hd₀_u u₁ hu₁) (hd₀_u u₂ hu₂) hz)
  · rintro ⟨hfst, hsnd⟩
    refine ⟨d.fst, hfst, d.snd, hsnd, ?_⟩
    rw [mem_interval_iff, ← edgePoint_zero d, ← edgePoint_one d,
      dist_edgePoint_edgePoint_same_eq hT d 0 t,
      dist_edgePoint_edgePoint_same_eq hT d t 1,
      dist_edgePoint_edgePoint_same_eq hT d 0 1]
    have ht0' : (0 : ℝ) ≤ t := t.2.1
    have ht1' : (t : ℝ) ≤ 1 := t.2.2
    rw [Set.Icc.coe_zero, Set.Icc.coe_one, zero_sub, abs_neg, abs_of_nonneg ht0',
      abs_of_neg (by linarith), abs_of_neg (by linarith)]
    ring

private lemma convexSet_subtree (hT : W.graph.IsTree) {S : Finset V}
    (hS : ConvexVertices W S) : ConvexSet W (subtree W S) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨u, hu⟩ := hS.1
    exact ⟨vertex u, vertex_mem_subtree W hu⟩
  · have heq : subtree W S = ⋃ u ∈ S, ⋃ v ∈ S, interval (vertex u) (vertex v) := by
      ext z
      simp [subtree]
    rw [heq]
    exact isClosed_biUnion_finset fun u _ => isClosed_biUnion_finset fun v _ =>
      isClosed_interval (vertex u) (vertex v)
  · intro a b ⟨u₁, hu₁, v₁, hv₁, ha⟩ ⟨u₂, hu₂, v₂, hv₂, hb⟩ z hz
    induction z using ind with
    | vertex w =>
      rw [vertex_mem_subtree_iff hT hS]
      by_contra hw
      obtain ⟨d, hdw, hdu⟩ := exists_cut_dart_of_notMem hT hS hw
      have hw_pos : 0 < edgeProj hT d (vertex w) := by
        rw [hdw]
        exact W.dart_weight_pos d
      have ha0 := edgeProj_eq_zero_of_mem_interval hT (hdu u₁ hu₁) (hdu v₁ hv₁) ha
      have hb0 := edgeProj_eq_zero_of_mem_interval hT (hdu u₂ hu₂) (hdu v₂ hv₂) hb
      exact hw_pos.ne' (edgeProj_eq_zero_of_mem_interval hT ha0 hb0 hz)
    | edgePoint d' t ht0 ht1 =>
      rw [edgePoint_mem_subtree_iff hT hS ht0 ht1]
      by_contra hnot
      have hcut : ∃ d₀ : W.graph.Dart,
          0 < edgeProj hT d₀ (edgePoint d' t) ∧ ∀ u ∈ S, edgeProj hT d₀ (vertex u) = 0 := by
        by_cases hfst : d'.fst ∈ S
        · have hsnd : d'.snd ∉ S := fun h => hnot ⟨hfst, h⟩
          obtain ⟨d₀, hd₀_snd, hd₀_u⟩ := exists_cut_dart_of_notMem hT hS hsnd
          refine ⟨d₀, ?_, hd₀_u⟩
          by_cases he : d'.edge = d₀.edge
          · rcases (dart_edge_eq_iff d' d₀).mp he with rfl | hsym
            · rw [edgeProj_edgePoint_self]
              exact mul_pos ht0 (W.dart_weight_pos d')
            · rw [hsym, edgeProj_edgePoint_symm]
              exact mul_pos (sub_pos.mpr ht1) (W.dart_weight_pos d₀)
          · rw [edgeProj_edgePoint_of_edge_ne hT he]
            have hd_adj : (W.graph.deleteEdges {d₀.edge}).Adj d'.fst d'.snd :=
              ⟨d'.adj, fun h => he (Set.mem_singleton_iff.mp h.1)⟩
            have hd_fst : edgeProj hT d₀ (vertex d'.fst) = W.weight d₀.edge := by
              rw [edgeProj_vertex_eq_weight_iff]
              intro hr
              have hs : ¬ (W.graph.deleteEdges {d₀.edge}).Reachable d'.snd d₀.fst := by
                rw [← edgeProj_vertex_eq_weight_iff hT d₀ d'.snd]
                exact hd₀_snd
              exact hs (hd_adj.symm.reachable.trans hr)
            rw [hd_fst]
            exact W.dart_weight_pos d₀
        · obtain ⟨d₀, hd₀_snd, hd₀_u⟩ := exists_cut_dart_of_notMem hT hS hfst
          refine ⟨d₀, ?_, hd₀_u⟩
          by_cases he : d'.edge = d₀.edge
          · rcases (dart_edge_eq_iff d' d₀).mp he with rfl | hsym
            · rw [edgeProj_edgePoint_self]
              exact mul_pos ht0 (W.dart_weight_pos d')
            · rw [hsym, edgeProj_edgePoint_symm]
              exact mul_pos (sub_pos.mpr ht1) (W.dart_weight_pos d₀)
          · rw [edgeProj_edgePoint_of_edge_ne hT he, hd₀_snd]
            exact W.dart_weight_pos d₀
      obtain ⟨d₀, hpos, hd₀_u⟩ := hcut
      have ha0 := edgeProj_eq_zero_of_mem_interval hT (hd₀_u u₁ hu₁) (hd₀_u v₁ hv₁) ha
      have hb0 := edgeProj_eq_zero_of_mem_interval hT (hd₀_u u₂ hu₂) (hd₀_u v₂ hv₂) hb
      exact hpos.ne' (edgeProj_eq_zero_of_mem_interval hT ha0 hb0 hz)

omit [Finite V] in
private lemma convexVertices_univ [Fintype V] [Nonempty V] (W : WeightedGraph V) :
    ConvexVertices W (Finset.univ : Finset V) :=
  ⟨Finset.univ_nonempty, fun _ _ _ _ _ _ w _ => Finset.mem_univ w⟩

private lemma subtree_univ [Fintype V] [Nonempty V] (hT : W.graph.IsTree) :
    subtree W (Finset.univ : Finset V) = Set.univ := by
  ext z
  simp only [Set.mem_univ, iff_true]
  induction z using ind with
  | vertex v => exact vertex_mem_subtree W (Finset.mem_univ v)
  | edgePoint d t ht0 ht1 =>
    rw [edgePoint_mem_subtree_iff hT (convexVertices_univ W) ht0 ht1]
    exact ⟨Finset.mem_univ _, Finset.mem_univ _⟩

private lemma walkLength_eq_vertexDist_of_isPath (hT : W.graph.IsTree) {a b : V}
    (p : W.graph.Walk a b) (hp : p.IsPath) :
    walkLength W.weight p = vertexDist W.graph W.weight a b := by
  obtain ⟨q, hqp, hq⟩ := exists_isPath_walkLength_eq_vertexDist W.weight_nonneg (W.connected a b)
  have heq : (⟨p, hp⟩ : W.graph.Path a b) = ⟨q, hqp⟩ :=
    (hT.isAcyclic.subsingleton_path a b).elim _ _
  exact (congrArg (fun x => walkLength W.weight x.1) heq).trans hq

private lemma vertex_mem_interval_of_mem_isPath (hT : W.graph.IsTree) {a b w : V}
    {p : W.graph.Walk a b} (hp : p.IsPath) (hw : w ∈ p.support) :
    (vertex w : MetricGraph W) ∈ interval (vertex a) (vertex b) := by
  classical
  let p₁ := p.takeUntil w hw
  let p₂ := p.dropUntil w hw
  have hp_app : p₁.append p₂ = p := Walk.take_spec p hw
  have hlen : walkLength W.weight p₁ + walkLength W.weight p₂ = walkLength W.weight p := by
    rw [← walkLength_append, hp_app]
  have hp1_isPath : p₁.IsPath := hp.takeUntil hw
  have hp2_isPath : p₂.IsPath := hp.dropUntil hw
  rw [mem_interval_iff, dist_vertex, dist_vertex, dist_vertex,
    ← walkLength_eq_vertexDist_of_isPath hT p₁ hp1_isPath,
    ← walkLength_eq_vertexDist_of_isPath hT p₂ hp2_isPath,
    ← walkLength_eq_vertexDist_of_isPath hT p hp, hlen]

private lemma path_subtree_eq_interval (hT : W.graph.IsTree) {S : Finset V}
    (hS : ConvexVertices W S)
    (hdeg : ∀ v ∈ S, ∀ T : Finset V, (∀ u ∈ T, u ∈ S ∧ W.graph.Adj v u) → T.card ≤ 2) :
    ∃ a ∈ S, ∃ b ∈ S, subtree W S = interval (vertex a) (vertex b) := by
  classical
  let lengths : Finset ℕ :=
    (Finset.range (S.card + 1)).filter fun n =>
      ∃ a ∈ S, ∃ b ∈ S, ∃ p : W.graph.Walk a b, p.IsPath ∧ p.length = n
  have hne_len : lengths.Nonempty := by
    obtain ⟨u₀, hu₀⟩ := hS.1
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.zero_lt_succ _),
      u₀, hu₀, u₀, hu₀, Walk.nil, Walk.IsPath.nil, rfl⟩⟩
  let L := lengths.max' hne_len
  have hL_mem : L ∈ lengths := Finset.max'_mem lengths hne_len
  obtain ⟨a, ha, b, hb, p, hp, hp_len⟩ := (Finset.mem_filter.mp hL_mem).2
  have hp_in_S : ∀ w ∈ p.support, w ∈ S := fun w hw => hS.2 a ha b hb p hp w hw
  have hall_mem : ∀ u ∈ S, u ∈ p.support := by
    intro u hu
    obtain ⟨q, hq⟩ := (W.connected u a).exists_isPath
    have hstep : ∀ {x y : V} (r : W.graph.Walk x y), r.IsPath → x ∈ S → y ∈ p.support →
        x ∉ p.support → ∃ u' ∈ S, ∃ v' ∈ p.support, u' ∉ p.support ∧ W.graph.Adj u' v' := by
      intro x y r
      induction r with
      | nil => intro _ _ hy hx; exact absurd hy hx
      | @cons x₁ z₁ w₁ hadj r' ih =>
        intro hr hx₁ hw₁ hnx₁
        have hz₁_S : z₁ ∈ S :=
          hS.2 x₁ hx₁ w₁ (hp_in_S w₁ hw₁) (Walk.cons hadj r') hr z₁ (by simp)
        by_cases hz₁ : z₁ ∈ p.support
        · exact ⟨x₁, hx₁, z₁, hz₁, hnx₁, hadj⟩
        · exact ih hr.of_cons hz₁_S hw₁ hz₁
    by_contra hu_not
    obtain ⟨u', hu'S, v', hv'p, hu'not, hadj⟩ :=
      hstep q hq hu (Walk.start_mem_support p) hu_not
    by_cases hva : v' = a
    · subst hva
      let p' : W.graph.Walk u' b := Walk.cons hadj p
      have hp' : p'.IsPath := Walk.IsPath.cons hp hu'not
      have hlen' : p'.length = L + 1 := by simp [p', hp_len]
      have hbd : p'.length + 1 ≤ S.card := by
        have hsub : p'.support.toFinset ⊆ S := by
          intro w hw
          rw [List.mem_toFinset] at hw
          exact hS.2 u' hu'S b hb p' hp' w hw
        have hc := Finset.card_le_card hsub
        rw [List.toFinset_card_of_nodup hp'.support_nodup, Walk.length_support] at hc
        exact hc
      have hL1_mem : L + 1 ∈ lengths := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), u', hu'S, b, hb, p', hp', hlen'⟩
      have hle := Finset.le_max' lengths (L + 1) hL1_mem
      omega
    · by_cases hvb : v' = b
      · subst hvb
        let p' : W.graph.Walk a u' := p.concat hadj.symm
        have hp' : p'.IsPath := by
          rw [← Walk.isPath_reverse_iff, Walk.reverse_concat]
          exact Walk.IsPath.cons hp.reverse (by simpa [Walk.support_reverse] using hu'not)
        have hlen' : p'.length = L + 1 := by simp [p', hp_len]
        have hbd : p'.length + 1 ≤ S.card := by
          have hsub : p'.support.toFinset ⊆ S := by
            intro w hw
            rw [List.mem_toFinset] at hw
            exact hS.2 a ha u' hu'S p' hp' w hw
          have hc := Finset.card_le_card hsub
          rw [List.toFinset_card_of_nodup hp'.support_nodup, Walk.length_support] at hc
          exact hc
        have hL1_mem : L + 1 ∈ lengths := Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega), a, ha, u', hu'S, p', hp', hlen'⟩
        have hle := Finset.le_max' lengths (L + 1) hL1_mem
        omega
      · have hv'_S : v' ∈ S := hp_in_S v' hv'p
        let p₁ := p.takeUntil v' hv'p
        let p₂ := p.dropUntil v' hv'p
        have hp1_rev_ne : ¬ p₁.reverse.Nil := Walk.not_nil_of_ne hva
        have hp2_ne : ¬ p₂.Nil := Walk.not_nil_of_ne hvb
        let d₁ := p₁.reverse.firstDart hp1_rev_ne
        let d₂ := p₂.firstDart hp2_ne
        have hp_spec : p₁.append p₂ = p := Walk.take_spec p hv'p
        have h1_mem : d₁.snd ∈ p.support := by
          have hd1_supp : d₁.snd ∈ p₁.support := by
            have hrev_mem : d₁.snd ∈ p₁.reverse.support := by
              cases hrev : p₁.reverse with
              | nil => exact absurd (hrev ▸ .nil) hp1_rev_ne
              | cons _ _ => simp [d₁, hrev, Walk.firstDart]
            rw [Walk.support_reverse, List.mem_reverse] at hrev_mem
            exact hrev_mem
          rw [← hp_spec]
          exact Walk.support_subset_support_append_left _ _ hd1_supp
        have h2_mem : d₂.snd ∈ p.support := by
          have hd2_supp : d₂.snd ∈ p₂.support := by
            cases hp2 : p₂ with
            | nil => exact absurd (hp2 ▸ .nil) hp2_ne
            | cons _ _ => simp [d₂, hp2, Walk.firstDart]
          rw [← hp_spec]
          exact Walk.support_subset_support_append_right _ _ hd2_supp
        have h1_adj : W.graph.Adj v' d₁.snd := d₁.adj
        have h2_adj : W.graph.Adj v' d₂.snd := d₂.adj
        have h1_ne_u : d₁.snd ≠ u' := fun heq => hu'not (heq ▸ h1_mem)
        have h2_ne_u : d₂.snd ≠ u' := fun heq => hu'not (heq ▸ h2_mem)
        have h1_ne_2 : d₁.snd ≠ d₂.snd := by
          intro heq
          have he1 : d₁.edge ∈ p₁.edges := by
            have hd1 : d₁.edge ∈ p₁.reverse.edges := by
              cases hrev : p₁.reverse with
              | nil => exact absurd (hrev ▸ .nil) hp1_rev_ne
              | cons _ _ => simp [d₁, hrev, Walk.firstDart]
            simpa [Walk.edges_reverse] using hd1
          have he2 : d₂.edge ∈ p₂.edges := by
            cases hp2 : p₂ with
            | nil => exact absurd (hp2 ▸ .nil) hp2_ne
            | cons _ _ => simp [d₂, hp2, Walk.firstDart]
          have he_eq : d₁.edge = d₂.edge := by
            change s(d₁.fst, d₁.snd) = s(d₂.fst, d₂.snd)
            rw [show d₁.fst = v' from rfl, show d₂.fst = v' from rfl, heq]
          have hnodup : p.edges.Nodup := hp.isTrail.edges_nodup
          rw [← Walk.take_spec p hv'p, Walk.edges_append, List.nodup_append] at hnodup
          exact hnodup.2.2 d₁.edge he1 d₂.edge he2 he_eq
        have hcard3 : ({u', d₁.snd, d₂.snd} : Finset V).card ≤ 2 := by
          refine hdeg v' hv'_S {u', d₁.snd, d₂.snd} fun x hx => ?_
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · exact ⟨hu'S, hadj.symm⟩
          · exact ⟨hp_in_S _ h1_mem, h1_adj⟩
          · exact ⟨hp_in_S _ h2_mem, h2_adj⟩
        have hc3 : ({u', d₁.snd, d₂.snd} : Finset V).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
          · exact fun h => h1_ne_2 (Finset.mem_singleton.mp h)
          · simp [h1_ne_u.symm, h2_ne_u.symm]
        omega
  refine ⟨a, ha, b, hb, Set.Subset.antisymm ?_ ?_⟩
  · intro z hz
    induction z using ind with
    | vertex w =>
      rw [vertex_mem_subtree_iff hT hS] at hz
      exact vertex_mem_interval_of_mem_isPath hT hp (hall_mem w hz)
    | edgePoint d t ht0 ht1 =>
      rw [edgePoint_mem_subtree_iff hT hS ht0 ht1] at hz
      have hfst := vertex_mem_interval_of_mem_isPath hT hp (hall_mem d.fst hz.1)
      have hsnd := vertex_mem_interval_of_mem_isPath hT hp (hall_mem d.snd hz.2)
      exact interval_subset_of_mem hT hfst hsnd (by
        rw [mem_interval_iff, ← edgePoint_zero d, ← edgePoint_one d,
          dist_edgePoint_edgePoint_same_eq hT d 0 t,
          dist_edgePoint_edgePoint_same_eq hT d t 1,
          dist_edgePoint_edgePoint_same_eq hT d 0 1]
        have ht0' : (0 : ℝ) ≤ t := t.2.1
        have ht1' : (t : ℝ) ≤ 1 := t.2.2
        rw [Set.Icc.coe_zero, Set.Icc.coe_one, zero_sub, abs_neg, abs_of_nonneg ht0',
          abs_of_neg (by linarith), abs_of_neg (by linarith)]
        ring)
  · intro z hz
    exact ⟨a, ha, b, hb, hz⟩

private lemma branch_adj_disjoint (hT : W.graph.IsTree) {c w₁ w₂ : V}
    (hadj₁ : W.graph.Adj c w₁) (hadj₂ : W.graph.Adj c w₂) (hne : w₁ ≠ w₂) :
    Disjoint (branch (vertex c : MetricGraph W) (vertex w₁))
      (branch (vertex c : MetricGraph W) (vertex w₂)) := by
  refine branch_disjoint_of_ne hT fun heq => ?_
  have hw1_in : (vertex w₁ : MetricGraph W) ∈ branch (vertex c) (vertex w₂) := by
    rw [← heq]
    exact mem_branch_self fun h => hadj₁.ne (vertex_injective (W := W) h.symm)
  have hd₂ : edgeProj hT ⟨(c, w₂), hadj₂⟩ (vertex w₁) = 0 := by
    rw [edgeProj_vertex_eq_zero_iff]
    refine SimpleGraph.Adj.reachable ⟨hadj₁.symm, fun h => ?_⟩
    rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp h.1) with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hadj₁.ne h1.symm
    · exact hne h1
  have hw2_proj : 0 < edgeProj hT ⟨(c, w₂), hadj₂⟩ (vertex w₂) := by
    let d₂ : W.graph.Dart := ⟨(c, w₂), hadj₂⟩
    have hweq : edgeProj hT d₂ (vertex d₂.snd) = W.weight d₂.edge := by
      rw [edgeProj_vertex_eq_weight_iff]
      exact fun hr => (isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp
        hT.isAcyclic hadj₂)) hr.symm
    change 0 < edgeProj hT d₂ (vertex d₂.snd)
    rw [hweq]
    exact W.dart_weight_pos d₂
  have hmem := mem_interval_iff.mp (vertex_fst_mem_interval_of_edgeProj hT ⟨(c, w₂), hadj₂⟩ hd₂
    (z := (vertex w₂ : MetricGraph W)) hw2_proj)
  exact hw1_in (interval_comm (vertex w₁) (vertex w₂) ▸ mem_interval_iff.mpr hmem)

private lemma mem_branch_adj_iff_edgeProj_pos (hT : W.graph.IsTree) {c w : V}
    (hadj : W.graph.Adj c w) (z : MetricGraph W) :
    z ∈ branch (vertex c) (vertex w) ↔ 0 < edgeProj hT ⟨(c, w), hadj⟩ z := by
  let d : W.graph.Dart := ⟨(c, w), hadj⟩
  change z ∈ branch (vertex d.fst) (vertex d.snd) ↔ 0 < edgeProj hT d z
  have hw_pos := W.dart_weight_pos d
  have hc0 : edgeProj hT d (vertex d.fst) = 0 :=
    (edgeProj_vertex_eq_zero_iff hT d d.fst).mpr (.refl _)
  have hw_proj : edgeProj hT d (vertex d.snd) = W.weight d.edge := by
    rw [edgeProj_vertex_eq_weight_iff]
    exact fun hr => (isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic d.adj))
      hr.symm
  constructor
  · intro hz
    by_contra hle
    have h0 : edgeProj hT d z = 0 := le_antisymm (not_lt.mp hle) (edgeProj_nonneg hT d z)
    have hmem := vertex_fst_mem_interval_of_edgeProj hT d h0 (by rw [hw_proj]; exact hw_pos)
    exact hz (interval_comm z (vertex d.snd) ▸ hmem)
  · intro hpos
    simp only [branch, Set.mem_ofPred_eq]
    intro hmem
    have hmem' := mem_interval_iff.mp hmem
    have hdist_pos : 0 < dist (vertex d.fst : MetricGraph W) z := by
      by_contra hle
      have heq : (vertex d.fst : MetricGraph W) = z :=
        dist_eq_zero.mp (le_antisymm (not_lt.mp hle) dist_nonneg)
      rw [← heq, hc0] at hpos
      exact lt_irrefl 0 hpos
    have hsym_lt : edgeProj hT d.symm z < W.weight d.edge := by
      rw [edgeProj_symm]
      linarith
    rcases lt_or_ge (edgeProj hT d z) (W.weight d.edge) with hlt | hge
    · obtain ⟨t, ht0, ht1, rfl⟩ : ∃ t : unitInterval, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧
          z = edgePoint d t := by
        rcases edgeProj_cases hT d z with h0 | hw | ⟨t, ht0, ht1, hzeq⟩
        · linarith
        · linarith
        · exact ⟨t, ht0, ht1, hzeq⟩
      have h1 := dist_edgePoint_edgePoint_same_eq hT d 0 t
      have h2 := dist_edgePoint_edgePoint_same_eq hT d t 1
      have h3 := dist_edgePoint_edgePoint_same_eq hT d 0 1
      simp only [edgePoint_zero, edgePoint_one, Set.Icc.coe_zero, Set.Icc.coe_one, zero_sub,
        abs_neg, abs_one, one_mul] at h1 h2 h3
      rw [abs_of_nonneg ht0.le] at h1
      rw [abs_of_neg (sub_neg.mpr ht1)] at h2
      linarith [_root_.dist_comm (vertex d.snd : MetricGraph W) (vertex d.fst),
        _root_.dist_comm (vertex d.snd : MetricGraph W) (edgePoint d t)]
    · have hw_eq : edgeProj hT d z = W.weight d.edge := le_antisymm (edgeProj_le_weight hT d z) hge
      have h0 : edgeProj hT d.symm z = 0 := by rw [edgeProj_symm, hw_eq, sub_self]
      have hpos' : 0 < edgeProj hT d.symm (vertex d.fst) := by
        rw [edgeProj_symm, hc0, sub_zero]
        exact hw_pos
      have hm := mem_interval_iff.mp (vertex_fst_mem_interval_of_edgeProj hT d.symm h0 hpos')
      rw [Dart.fst_symm d] at hm
      have hcd_pos : 0 < dist (vertex d.snd : MetricGraph W) (vertex d.fst) :=
        dist_pos.mpr fun h => d.fst_ne_snd (vertex_injective (W := W) h.symm)
      linarith [_root_.dist_comm (vertex d.snd : MetricGraph W) (vertex d.fst),
        _root_.dist_comm (vertex d.snd : MetricGraph W) z,
        _root_.dist_comm z (vertex d.fst)]

private noncomputable def removeBranch (hT : W.graph.IsTree) (S : Finset V) (c w : V) : Finset V :=
  have _ := hT
  @Finset.filter V (fun u => vertex u ∉ branch (vertex c : MetricGraph W) (vertex w))
    (Classical.decPred _) S

private lemma mem_removeBranch_iff (hT : W.graph.IsTree) {S : Finset V} {c w u : V}
    (hadj : W.graph.Adj c w) :
    u ∈ removeBranch hT S c w ↔
      u ∈ S ∧ (W.graph.deleteEdges {s(c, w)}).Reachable u c := by
  let d : W.graph.Dart := ⟨(c, w), hadj⟩
  simp only [removeBranch, Finset.mem_filter]
  refine and_congr_right fun _ => ?_
  rw [mem_branch_adj_iff_edgeProj_pos hT hadj]
  constructor
  · intro hnot
    have h0 : edgeProj hT d (vertex u) = 0 := le_antisymm (not_lt.mp hnot) (edgeProj_nonneg hT d _)
    exact (edgeProj_vertex_eq_zero_iff hT d u).mp h0
  · intro hr
    have h0 : edgeProj hT d (vertex u) = 0 := (edgeProj_vertex_eq_zero_iff hT d u).mpr hr
    linarith

private lemma convexVertices_removeBranch (hT : W.graph.IsTree) {S : Finset V}
    (hS : ConvexVertices W S) {c w : V} (hc : c ∈ S) (hadj : W.graph.Adj c w) :
    ConvexVertices W (removeBranch hT S c w) := by
  classical
  refine ⟨⟨c, (mem_removeBranch_iff hT hadj).mpr ⟨hc, .refl c⟩⟩, fun u hu v hv p hp x hx => ?_⟩
  rw [mem_removeBranch_iff hT hadj] at hu hv ⊢
  refine ⟨hS.2 u hu.1 v hv.1 p hp x hx, ?_⟩
  obtain ⟨q, hq⟩ := (hu.2.trans hv.2.symm).exists_isPath
  let q' := q.map (SimpleGraph.Hom.ofLE (W.graph.deleteEdges_le {s(c, w)}))
  have hq' : q'.IsPath := hq.map (fun _ _ h => h)
  have hpath : (⟨p, hp⟩ : W.graph.Path u v) = ⟨q', hq'⟩ :=
    (hT.isAcyclic.subsingleton_path u v).elim _ _
  have hpq : p = q' := congrArg Subtype.val hpath
  rw [hpq] at hx
  have hx' : x ∈ q.support := by simpa [q', Walk.support_map] using hx
  have hrx : (W.graph.deleteEdges {s(c, w)}).Reachable x u := ⟨(q.takeUntil x hx').reverse⟩
  exact hrx.trans hu.2

private lemma card_removeBranch_lt (hT : W.graph.IsTree) {S : Finset V}
    {c w : V} (hw : w ∈ S) (hadj : W.graph.Adj c w) :
    (removeBranch hT S c w).card < S.card := by
  classical
  refine Finset.card_lt_card ⟨@Finset.filter_subset V _ (Classical.decPred _) S, fun hsub => ?_⟩
  have hw_rem := hsub hw
  rw [mem_removeBranch_iff hT hadj] at hw_rem
  let d : W.graph.Dart := ⟨(c, w), hadj⟩
  exact (isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic d.adj)) hw_rem.2.symm

private lemma subtree_removeBranch (hT : W.graph.IsTree) {S : Finset V}
    (hS : ConvexVertices W S) {c w : V} (hc : c ∈ S) (hadj : W.graph.Adj c w) :
    subtree W (removeBranch hT S c w) =
      subtree W S ∩ (branch (vertex c) (vertex w))ᶜ := by
  have hS_rem := convexVertices_removeBranch hT hS hc hadj
  let d : W.graph.Dart := ⟨(c, w), hadj⟩
  ext z
  simp only [Set.mem_inter_iff, Set.mem_compl_iff]
  induction z using ind with
  | vertex u =>
    rw [vertex_mem_subtree_iff hT hS_rem, vertex_mem_subtree_iff hT hS,
      mem_removeBranch_iff hT hadj, mem_branch_adj_iff_edgeProj_pos hT hadj]
    constructor
    · rintro ⟨huS, hr⟩
      refine ⟨huS, fun hpos => ?_⟩
      have h0 := (edgeProj_vertex_eq_zero_iff hT d u).mpr hr
      linarith
    · rintro ⟨huS, hnot⟩
      have h0 : edgeProj hT d (vertex u) = 0 :=
        le_antisymm (not_lt.mp hnot) (edgeProj_nonneg hT d _)
      exact ⟨huS, (edgeProj_vertex_eq_zero_iff hT d u).mp h0⟩
  | edgePoint d' t ht0 ht1 =>
    rw [edgePoint_mem_subtree_iff hT hS_rem ht0 ht1, edgePoint_mem_subtree_iff hT hS ht0 ht1,
      mem_branch_adj_iff_edgeProj_pos hT hadj]
    rw [mem_removeBranch_iff hT hadj, mem_removeBranch_iff hT hadj]
    by_cases he : d'.edge = d.edge
    · constructor
      · rintro ⟨⟨_, hr1⟩, ⟨_, hr2⟩⟩
        rcases (dart_edge_eq_iff d' d).mp he with rfl | hsym
        · exact absurd hr2 (fun hr =>
            (isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic d.adj)) hr.symm)
        · rw [hsym] at hr1
          exact absurd hr1 (fun hr =>
            (isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic d.adj)) hr.symm)
      · rintro ⟨_, hnot⟩
        exfalso
        apply hnot
        rcases (dart_edge_eq_iff d' d).mp he with rfl | hsym
        · rw [edgeProj_edgePoint_self]
          exact mul_pos ht0 (W.dart_weight_pos d)
        · rw [hsym, edgeProj_edgePoint_symm]
          exact mul_pos (sub_pos.mpr ht1) (W.dart_weight_pos d)
    · have hadj_del : (W.graph.deleteEdges {d.edge}).Adj d'.fst d'.snd :=
        ⟨d'.adj, fun h => he (Set.mem_singleton_iff.mp h.1)⟩
      rw [edgeProj_edgePoint_of_edge_ne hT he, not_lt]
      constructor
      · rintro ⟨⟨hfS, hfr⟩, ⟨hsS, _⟩⟩
        refine ⟨⟨hfS, hsS⟩, ?_⟩
        change (W.graph.deleteEdges {d.edge}).Reachable d'.fst d.fst at hfr
        exact ((edgeProj_vertex_eq_zero_iff hT d d'.fst).mpr hfr).le
      · rintro ⟨⟨hfS, hsS⟩, hle⟩
        have h0 : edgeProj hT d (vertex d'.fst) = 0 :=
          le_antisymm hle (edgeProj_nonneg hT d _)
        have hfr : (W.graph.deleteEdges {s(c, w)}).Reachable d'.fst c :=
          (edgeProj_vertex_eq_zero_iff hT d d'.fst).mp h0
        exact ⟨⟨hfS, hfr⟩, ⟨hsS, hadj_del.symm.reachable.trans hfr⟩⟩

private lemma projConvex_removeBranch_mem (hT : W.graph.IsTree) {S : Finset V}
    (hS : ConvexVertices W S) {c w : V} (hc : c ∈ S) (hadj : W.graph.Adj c w)
    {z : MetricGraph W} (hbr : z ∈ branch (vertex c) (vertex w)) :
    projConvex hT (convexSet_subtree hT (convexVertices_removeBranch hT hS hc hadj)) z =
      vertex c := by
  have hS_rem := convexVertices_removeBranch hT hS hc hadj
  have hsub := subtree_removeBranch hT hS hc hadj
  let p := projConvex hT (convexSet_subtree hT hS_rem) z
  have hp_mem : p ∈ subtree W (removeBranch hT S c w) :=
    projConvex_mem hT (convexSet_subtree hT hS_rem) z
  rw [hsub, Set.mem_inter_iff, Set.mem_compl_iff] at hp_mem
  have hc_mem : (vertex c : MetricGraph W) ∈ subtree W (removeBranch hT S c w) :=
    vertex_mem_subtree W ((mem_removeBranch_iff hT hadj).mpr ⟨hc, .refl c⟩)
  have h1 := mem_interval_iff.mp
    (mem_interval_projConvex hT (convexSet_subtree hT hS_rem) z hc_mem)
  have hp_not : p ∉ branch (vertex c) z := by
    rw [branch_eq_of_mem hT hbr]
    exact hp_mem.2
  simp only [branch, Set.mem_ofPred_eq, Classical.not_not, mem_interval_iff] at hp_not
  have hd : dist p (vertex c) = 0 := by
    linarith [_root_.dist_comm p z, _root_.dist_comm z (vertex c), _root_.dist_comm p (vertex c)]
  exact dist_eq_zero.mp hd

private lemma projConvex_removeBranch_notMem (hT : W.graph.IsTree) {S : Finset V}
    (hS : ConvexVertices W S) {c w : V} (hc : c ∈ S) (hadj : W.graph.Adj c w)
    {z : MetricGraph W} (hz : z ∈ subtree W S) (hbr : z ∉ branch (vertex c) (vertex w)) :
    projConvex hT (convexSet_subtree hT (convexVertices_removeBranch hT hS hc hadj)) z = z := by
  have hS_rem := convexVertices_removeBranch hT hS hc hadj
  have hz_rem : z ∈ subtree W (removeBranch hT S c w) := by
    rw [subtree_removeBranch hT hS hc hadj]
    exact ⟨hz, hbr⟩
  exact projConvex_eq_self hT (convexSet_subtree hT hS_rem) hz_rem

end Subtrees

section Characterization

variable {V : Type*} [Finite V] {W : WeightedGraph V}
variable {ι : Type*} [Finite ι] [Nonempty ι] [DecidableEq ι]

private def BranchInvOn (W : WeightedGraph V) (f : (ι → MetricGraph W) → MetricGraph W)
    (S : Finset V) : Prop :=
  ∀ ⦃y q : MetricGraph W⦄, y ∈ subtree W S → q ∈ subtree W S → q ≠ y →
    ∀ ⦃x₁ x₂ : ι → MetricGraph W⦄,
      (∀ i, x₁ i ∈ subtree W S) → (∀ i, x₂ i ∈ subtree W S) →
      (∀ i, x₁ i ∈ branch y q ↔ x₂ i ∈ branch y q) →
      (f x₁ ∈ branch y q ↔ f x₂ ∈ branch y q)

private lemma branchInvOn_of_interval
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_onto : Function.Surjective f)
    {S : Finset V} (hS : ConvexVertices W S)
    {a b : V} (_ha : a ∈ S) (_hb : b ∈ S)
    (hsub : subtree W S = interval (vertex a) (vertex b)) :
    BranchInvOn W f S := by
  classical
  let _ := Fintype.ofFinite ι
  have hf_unan : ∀ c : MetricGraph W, f (fun _ => c) = c :=
    unanimous_of_surjective_isStrategyProof hf_sp hf_onto
  obtain ⟨φ, hφ, _, _, hrange⟩ := exists_isometry_interval hT (vertex a) (vertex b)
  let d := dist (vertex a : MetricGraph W) (vertex b)
  have hd : 0 ≤ d := dist_nonneg
  have hrange_S : Set.range φ = subtree W S := hrange.trans hsub.symm
  have hf_range : ∀ x : ι → MetricGraph W, (∀ i, x i ∈ Set.range φ) → f x ∈ Set.range φ := by
    intro x hx
    rw [hrange_S]
    exact range_of_convex hT hf_sp hf_onto (convexSet_subtree hT hS) fun i => by
      simpa [hrange_S] using hx i
  have hf_onto_I : ∀ y ∈ Set.range φ, ∃ x : ι → MetricGraph W, (∀ i, x i ∈ Set.range φ) ∧ f x = y :=
    fun y hy => ⟨fun _ => y, fun _ => hy, hf_unan y⟩
  obtain ⟨E, hE⟩ := moulinScheme_of_isometry hd φ hφ hf_sp hf_range hf_onto_I
  have hcoord : ∀ {u : MetricGraph W}, u ∈ subtree W S →
      ∃ t : Set.Icc 0 d, φ t = u := fun {u} hu => by
    rw [← hrange_S] at hu
    exact hu
  have hbranch_Icc : ∀ {y₀ q₀ w₀ : Set.Icc 0 d}, q₀ ≠ y₀ →
      (φ w₀ ∈ branch (φ y₀) (φ q₀) ↔
        if (y₀ : ℝ) < q₀ then (y₀ : ℝ) < w₀ else (w₀ : ℝ) < y₀) := by
    intro y₀ q₀ w₀ hne
    have hneq_real : (q₀ : ℝ) ≠ y₀ := fun h => hne (Subtype.ext h)
    simp only [branch, Set.mem_ofPred_eq, mem_interval_iff, hφ.dist_eq, Subtype.dist_eq,
      Real.dist_eq]
    split_ifs with hyq
    · constructor
      · intro hnot
        by_contra hle
        apply hnot
        have h1 : |((q₀ : ℝ) - y₀)| = (q₀ : ℝ) - y₀ := abs_of_pos (sub_pos.mpr hyq)
        have h2 : |((y₀ : ℝ) - w₀)| = (y₀ : ℝ) - w₀ :=
          abs_of_nonneg (sub_nonneg.mpr (not_lt.mp hle))
        have h3 : |((q₀ : ℝ) - w₀)| = (q₀ : ℝ) - w₀ := abs_of_nonneg (by linarith [not_lt.mp hle])
        rw [h1, h2, h3]
        ring
      · intro hlt heq
        have h1 := abs_of_pos (sub_pos.mpr hyq)
        have h2 := abs_of_neg (sub_neg.mpr hlt)
        rcases le_total (q₀ : ℝ) w₀ with hqw | hwq
        · have h3 := abs_of_nonneg (sub_nonneg.mpr hqw)
          rw [abs_sub_comm (q₀ : ℝ) w₀] at heq
          linarith
        · have h3 := abs_of_nonneg (sub_nonneg.mpr hwq)
          linarith
    · have hqy : (q₀ : ℝ) < y₀ := lt_of_le_of_ne (not_lt.mp hyq) hneq_real
      constructor
      · intro hnot
        by_contra hle
        apply hnot
        have h1 : |((q₀ : ℝ) - y₀)| = (y₀ : ℝ) - q₀ := by
          rw [abs_sub_comm]; exact abs_of_pos (sub_pos.mpr hqy)
        have h2 : |((y₀ : ℝ) - w₀)| = (w₀ : ℝ) - y₀ := by
          rw [abs_sub_comm]; exact abs_of_nonneg (sub_nonneg.mpr (not_lt.mp hle))
        have h3 : |((q₀ : ℝ) - w₀)| = (w₀ : ℝ) - q₀ := by
          rw [abs_sub_comm]; exact abs_of_nonneg (by linarith [not_lt.mp hle])
        rw [h1, h2, h3]
        ring
      · intro hlt heq
        have h1 := abs_of_neg (sub_neg.mpr hqy)
        have h2 := abs_of_pos (sub_pos.mpr hlt)
        rcases le_total (q₀ : ℝ) w₀ with hqw | hwq
        · have h3 := abs_of_nonneg (sub_nonneg.mpr hqw)
          rw [abs_sub_comm (q₀ : ℝ) w₀] at heq
          linarith
        · have h3 := abs_of_nonneg (sub_nonneg.mpr hwq)
          linarith
  intro y q hy hq hqy x₁ x₂ hx₁ hx₂ hiff
  obtain ⟨y₀, rfl⟩ := hcoord hy
  obtain ⟨q₀, rfl⟩ := hcoord hq
  have hq0_ne : q₀ ≠ y₀ := fun h => hqy (h ▸ rfl)
  let c₁ : ι → Set.Icc 0 d := fun i => Classical.choose (hcoord (hx₁ i))
  let c₂ : ι → Set.Icc 0 d := fun i => Classical.choose (hcoord (hx₂ i))
  have hc₁ : ∀ i, φ (c₁ i) = x₁ i := fun i => Classical.choose_spec (hcoord (hx₁ i))
  have hc₂ : ∀ i, φ (c₂ i) = x₂ i := fun i => Classical.choose_spec (hcoord (hx₂ i))
  have hx₁_eq : x₁ = fun i => φ (c₁ i) := funext fun i => (hc₁ i).symm
  have hx₂_eq : x₂ = fun i => φ (c₂ i) := funext fun i => (hc₂ i).symm
  rw [hx₁_eq, hx₂_eq, hE c₁, hE c₂, hbranch_Icc hq0_ne, hbranch_Icc hq0_ne]
  have hiff_c : ∀ i, (φ (c₁ i) ∈ branch (φ y₀) (φ q₀)) ↔ (φ (c₂ i) ∈ branch (φ y₀) (φ q₀)) :=
    fun i => by rw [hc₁ i, hc₂ i]; exact hiff i
  split_ifs with hyq
  · have hS_eq : (Finset.univ.filter fun i => (c₁ i : ℝ) ≤ y₀) =
        Finset.univ.filter fun i => (c₂ i : ℝ) ≤ y₀ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 := hbranch_Icc (w₀ := c₁ i) hq0_ne
      have h2 := hbranch_Icc (w₀ := c₂ i) hq0_ne
      simp only [hyq, ↓reduceIte] at h1 h2
      rw [← not_lt (a := (y₀ : ℝ)) (b := (c₁ i : ℝ)),
        ← not_lt (a := (y₀ : ℝ)) (b := (c₂ i : ℝ))]
      exact not_congr (h1.symm.trans ((hiff_c i).trans h2))
    rw [E.lt_eval_iff c₁ y₀, E.lt_eval_iff c₂ y₀, hS_eq]
  · have hS_eq : (Finset.univ.filter fun i => (c₁ i : ℝ) < y₀) =
        Finset.univ.filter fun i => (c₂ i : ℝ) < y₀ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 := hbranch_Icc (w₀ := c₁ i) hq0_ne
      have h2 := hbranch_Icc (w₀ := c₂ i) hq0_ne
      simp only [hyq, ↓reduceIte] at h1 h2
      exact h1.symm.trans ((hiff_c i).trans h2)
    rw [E.eval_lt_iff c₁ y₀, E.eval_lt_iff c₂ y₀, hS_eq]

omit [Nonempty ι] in
private lemma proj_interval_of_branchInvOn
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_onto : Function.Surjective f)
    {S : Finset V} (hS : ConvexVertices W S) (hinv : BranchInvOn W f S)
    {a b : MetricGraph W} (ha : a ∈ subtree W S) (hb : b ∈ subtree W S)
    {x : ι → MetricGraph W} (hx : ∀ i, x i ∈ subtree W S) :
    treeMedian hT a b (f x) = f (fun i => treeMedian hT a b (x i)) := by
  by_contra hne
  let p₁ := treeMedian hT a b (f x)
  let p₂ := f (fun i => treeMedian hT a b (x i))
  have hp₁_ab : p₁ ∈ interval a b := treeMedian_mem_xy hT a b (f x)
  have hp₁_S : p₁ ∈ subtree W S := (convexSet_subtree hT hS).2.2 ha hb hp₁_ab
  have hπx_S : ∀ i, treeMedian hT a b (x i) ∈ subtree W S := fun i =>
    (convexSet_subtree hT hS).2.2 ha hb (treeMedian_mem_xy hT a b (x i))
  have hp₂_S : p₂ ∈ subtree W S := range_of_convex hT hf_sp hf_onto (convexSet_subtree hT hS) hπx_S
  have hfx_S : f x ∈ subtree W S := range_of_convex hT hf_sp hf_onto (convexSet_subtree hT hS) hx
  have hp₂_ab : p₂ ∈ interval a b := by
    have hconv_ab : ConvexSet W (interval a b) :=
      ⟨⟨a, left_mem_interval a b⟩, isClosed_interval a b, fun _ _ hu hv =>
        interval_subset_of_mem hT hu hv⟩
    exact range_of_convex hT hf_sp hf_onto hconv_ab fun i => treeMedian_mem_xy hT a b (x i)
  have hiff : ∀ i, x i ∈ branch p₁ p₂ ↔ treeMedian hT a b (x i) ∈ branch p₁ p₂ := fun i =>
    mem_branch_proj_interval_iff hT hp₁_ab hp₂_ab
  have hres := hinv hp₁_S hp₂_S (Ne.symm hne) hx hπx_S hiff
  have hp₁_eq : f x ∈ branch p₁ p₂ ↔ p₁ ∈ branch p₁ p₂ :=
    mem_branch_proj_interval_iff hT hp₁_ab hp₂_ab
  rw [hp₁_eq] at hres
  exact (notMem_branch_self p₁ p₂) (hres.mpr (mem_branch_self (Ne.symm hne)))

private lemma exists_adj_of_mem_subtree_ne (hT : W.graph.IsTree) {S : Finset V}
    (hS : ConvexVertices W S) {c : V} (hc : c ∈ S) {y : MetricGraph W}
    (hy_S : y ∈ subtree W S) (hy_ne : y ≠ vertex c) :
    ∃ w ∈ S, W.graph.Adj c w ∧ y ∈ branch (vertex c) (vertex w) := by
  classical
  have hne_univ : (Set.univ : Set W.graph.Dart).Nonempty := by
    obtain ⟨u, _, v, _, hy_uv⟩ := hy_S
    by_cases huv : u = v
    · subst huv
      rw [interval_eq_singleton_self] at hy_uv
      have huc : u ≠ c := fun h => hy_ne (hy_uv.trans (h ▸ rfl))
      obtain ⟨p⟩ := W.connected u c
      exact ⟨p.firstDart (Walk.not_nil_of_ne huc), Set.mem_univ _⟩
    · obtain ⟨p⟩ := W.connected u v
      exact ⟨p.firstDart (Walk.not_nil_of_ne huv), Set.mem_univ _⟩
  obtain ⟨d₀⟩ := hne_univ
  obtain ⟨wmin, hwmin_pos, hwmin_le⟩ := exists_min_dart_weight (W := W) d₀
  have hdy : 0 < dist (vertex c : MetricGraph W) y := dist_pos.mpr hy_ne.symm
  let r := min wmin (dist (vertex c : MetricGraph W) y) / 2
  have hr_pos : 0 < r := by positivity
  have hr_lt_w : ∀ d : W.graph.Dart, r < W.weight d.edge := fun d => by
    have hd : wmin ≤ W.weight d.edge := hwmin_le d
    have : r ≤ wmin / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    linarith
  have hr_le_dy : r ≤ dist (vertex c : MetricGraph W) y := by
    have : r ≤ dist (vertex c : MetricGraph W) y / 2 :=
      div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    linarith
  obtain ⟨p, hp_mem, hp_dist, _⟩ :=
    exists_mem_interval_dist_eq (vertex c) y ⟨hr_pos.le, hr_le_dy⟩
  obtain ⟨d, t, hd_fst, ht0, ht1, rfl, _⟩ :=
    dist_vertex_mem_step_dart hr_pos hp_dist hr_lt_w
  have hp_S : edgePoint d t ∈ subtree W S :=
    (convexSet_subtree hT hS).2.2 (vertex_mem_subtree W hc) hy_S hp_mem
  have hd_S := (edgePoint_mem_subtree_iff hT hS ht0 ht1).mp hp_S
  have hadj : W.graph.Adj c d.snd := hd_fst ▸ d.adj
  have hp_br : edgePoint d t ∈ branch (vertex c) (vertex d.snd) := by
    rw [mem_branch_adj_iff_edgeProj_pos hT hadj]
    have hd_eq : (⟨(c, d.snd), hadj⟩ : W.graph.Dart) = d := by
      ext <;> simp [hd_fst]
    rw [hd_eq, edgeProj_edgePoint_self]
    exact mul_pos ht0 (W.dart_weight_pos d)
  have hp_ne : edgePoint d t ≠ vertex c := fun heq => by
    rw [heq, _root_.dist_self] at hp_dist
    linarith
  have hp_bry : edgePoint d t ∈ branch (vertex c) y :=
    interval_subset_branch hT (mem_branch_self hy_ne) hp_mem hp_ne
  refine ⟨d.snd, hd_S.2, hadj, ?_⟩
  rw [← branch_eq_of_mem hT hp_br, branch_eq_of_mem hT hp_bry]
  exact mem_branch_self hy_ne

private lemma proj_removeBranch_of_branchInvOn
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_onto : Function.Surjective f)
    {S : Finset V} (hS : ConvexVertices W S)
    {c w₁ : V} (hc : c ∈ S) (hw₁ : w₁ ∈ S) (hadj₁ : W.graph.Adj c w₁)
    (hdeg3 : ∃ T : Finset V, 3 ≤ T.card ∧ ∀ u ∈ T, u ∈ S ∧ W.graph.Adj c u)
    (hinv_rem : ∀ w ∈ S, W.graph.Adj c w → BranchInvOn W f (removeBranch hT S c w))
    {x : ι → MetricGraph W} (hx : ∀ i, x i ∈ subtree W S) :
    let hS₁ := convexVertices_removeBranch hT hS hc hadj₁
    let π₁ := projConvex hT (convexSet_subtree hT hS₁)
    π₁ (f x) = f (fun i => π₁ (x i)) := by
  classical
  let _ := Fintype.ofFinite ι
  have hS₁ := convexVertices_removeBranch hT hS hc hadj₁
  let π₁ := projConvex hT (convexSet_subtree hT hS₁)
  let C₁ := branch (vertex c : MetricGraph W) (vertex w₁)
  have hc₁ : (vertex c : MetricGraph W) ∈ subtree W (removeBranch hT S c w₁) :=
    vertex_mem_subtree W ((mem_removeBranch_iff hT hadj₁).mpr ⟨hc, .refl c⟩)
  have hsp : ∀ (z : ι → MetricGraph W) (i : ι) (w : MetricGraph W),
      dist (f z) (z i) ≤ dist (f (Function.update z i w)) (z i) := fun z i w => by
    simpa only [_root_.dist_comm] using
      (Mechanism.isStrategyProof_deterministic_iff f).mp hf_sp z i w
  suffices h : ∀ (m : ℕ) (z : ι → MetricGraph W),
      (∀ i, z i ∈ subtree W S) →
      (Finset.univ.filter fun i => z i ∈ C₁).card = m →
      π₁ (f z) = f (fun i => π₁ (z i)) from h _ x hx rfl
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro z hz hcard
    by_cases hm : m = 0
    · subst hm
      have hemp : (Finset.univ.filter fun i => z i ∈ C₁) = ∅ := Finset.card_eq_zero.mp hcard
      have hz₁ : ∀ i, z i ∈ subtree W (removeBranch hT S c w₁) := fun i => by
        rw [subtree_removeBranch hT hS hc hadj₁]
        refine ⟨hz i, fun hmem => ?_⟩
        have hi : i ∈ Finset.univ.filter fun i => z i ∈ C₁ := by simp [C₁, hmem]
        rw [hemp] at hi
        exact Finset.notMem_empty i hi
      have hfz : f z ∈ subtree W (removeBranch hT S c w₁) :=
        range_of_convex hT hf_sp hf_onto (convexSet_subtree hT hS₁) hz₁
      have hπz : (fun i => π₁ (z i)) = z := funext fun i =>
        projConvex_eq_self hT (convexSet_subtree hT hS₁) (hz₁ i)
      rw [hπz]
      exact projConvex_eq_self hT (convexSet_subtree hT hS₁) hfz
    · have hne : (Finset.univ.filter fun i => z i ∈ C₁).Nonempty :=
        Finset.card_pos.mp (hcard ▸ Nat.pos_of_ne_zero hm)
      obtain ⟨j, hj⟩ := hne
      have hj_C1 : z j ∈ C₁ := (Finset.mem_filter.mp hj).2
      let z' := Function.update z j (vertex c)
      have hz'_S : ∀ i, z' i ∈ subtree W S := fun i => by
        by_cases hi : i = j
        · subst hi; simp [z', vertex_mem_subtree W hc]
        · simpa [z', hi] using hz i
      have hsub' : Finset.univ.filter (fun i => z' i ∈ C₁) =
          (Finset.univ.filter fun i => z i ∈ C₁).erase j := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, z']
        by_cases hi : i = j
        · subst hi; simp [C₁]
        · simp [hi]
      have hcard' : (Finset.univ.filter fun i => z' i ∈ C₁).card = m - 1 := by
        rw [hsub', Finset.card_erase_of_mem hj, hcard]
      have hπ_upd : (fun i => π₁ (z' i)) = fun i => π₁ (z i) := by
        funext i
        by_cases hi : i = j
        · subst hi
          simp only [z', Function.update_self]
          dsimp only [π₁]
          rw [projConvex_eq_self hT (convexSet_subtree hT hS₁) hc₁,
            projConvex_removeBranch_mem hT hS hc hadj₁ hj_C1]
        · simp [z', hi]
      have hih' : π₁ (f z') = f (fun i => π₁ (z i)) := by
        rw [← hπ_upd]
        exact ih (m - 1) (Nat.sub_lt (Nat.pos_of_ne_zero hm) zero_lt_one) z' hz'_S hcard'
      by_contra hne_res
      rw [← hih'] at hne_res
      let y := f z
      let y' := f z'
      have hy_S : y ∈ subtree W S := range_of_convex hT hf_sp hf_onto (convexSet_subtree hT hS) hz
      have hy'_S : y' ∈ subtree W S :=
        range_of_convex hT hf_sp hf_onto (convexSet_subtree hT hS) hz'_S
      by_cases hy_sub : y ∈ subtree W (removeBranch hT S c w₁)
      · have hy_π : π₁ y = y := projConvex_eq_self hT (convexSet_subtree hT hS₁) hy_sub
        have hy'_sub : y' ∈ subtree W (removeBranch hT S c w₁) := by
          by_contra hy'_not
          have hy'_C1 : y' ∈ C₁ := by
            rw [subtree_removeBranch hT hS hc hadj₁] at hy'_not
            simpa [C₁, hy'_S] using hy'_not
          have hbr_eq_zj : branch (vertex c) (z j) = C₁ := branch_eq_of_mem hT hj_C1
          have hbr_eq_y' : branch (vertex c) y' = C₁ := branch_eq_of_mem hT hy'_C1
          let b := treeMedian hT (vertex c) (z j) y'
          have hb_ne : b ≠ vertex c := by
            intro heq
            have hc_int : (vertex c : MetricGraph W) ∈ interval (z j) y' :=
              heq ▸ treeMedian_mem_yz hT (vertex c) (z j) y'
            have hdisj := branch_disjoint_of_mem_interval hT hc_int
            rw [hbr_eq_zj, hbr_eq_y'] at hdisj
            exact Set.disjoint_left.mp hdisj hj_C1 hj_C1
          have hb_pos : 0 < dist (vertex c : MetricGraph W) b := dist_pos.mpr hb_ne.symm
          have e_cb_zj := mem_interval_iff.mp (treeMedian_mem_xy hT (vertex c) (z j) y')
          have e_cb_y' := mem_interval_iff.mp (interval_comm y' (vertex c) ▸
            treeMedian_mem_zx hT (vertex c) (z j) y')
          have e_zj_y' := mem_interval_iff.mp (treeMedian_mem_yz hT (vertex c) (z j) y')
          have hsp_j := hsp z j (vertex c)
          have hsp_c := hsp z' j (z j)
          have hz'_upd : Function.update z' j (z j) = z := by
            funext i
            by_cases hi : i = j
            · subst hi; simp [z']
            · simp [z', hi]
          rw [hz'_upd] at hsp_c
          simp only [z', Function.update_self] at hsp_c
          change dist y (z j) ≤ dist y' (z j) at hsp_j
          change dist y' (vertex c) ≤ dist y (vertex c) at hsp_c
          have hy_not_C1 : y ∉ C₁ := by
            rw [subtree_removeBranch hT hS hc hadj₁] at hy_sub
            exact hy_sub.2
          have hc_int_zj_y : (vertex c : MetricGraph W) ∈ interval (z j) y := by
            rw [← hbr_eq_zj] at hy_not_C1
            simpa only [branch, Set.mem_ofPred_eq, Classical.not_not] using hy_not_C1
          have e_c_zjy := mem_interval_iff.mp hc_int_zj_y
          linarith [_root_.dist_comm (z j) b, _root_.dist_comm b (vertex c),
            _root_.dist_comm (vertex c) (z j), _root_.dist_comm y (z j),
            _root_.dist_comm y' (z j), _root_.dist_comm y' (vertex c),
            _root_.dist_comm y (vertex c)]
        have hy'_π : π₁ y' = y' := projConvex_eq_self hT (convexSet_subtree hT hS₁) hy'_sub
        rw [hy_π, hy'_π] at hne_res
        have hsp_c := hsp z' j (z j)
        have hz'_upd : Function.update z' j (z j) = z := by
          funext i
          by_cases hi : i = j
          · subst hi; simp [z']
          · simp [z', hi]
        rw [hz'_upd] at hsp_c
        have hsp_j := hsp z j (vertex c)
        simp only [z', Function.update_self] at hsp_c
        change dist y' (vertex c) ≤ dist y (vertex c) at hsp_c
        change dist y (z j) ≤ dist y' (z j) at hsp_j
        have hy_not_C1 : y ∉ C₁ := by
          rw [subtree_removeBranch hT hS hc hadj₁] at hy_sub
          exact hy_sub.2
        have hbr_zj : branch (vertex c) (z j) = C₁ := branch_eq_of_mem hT hj_C1
        have hc_int : (vertex c : MetricGraph W) ∈ interval (z j) y := by
          rw [← hbr_zj] at hy_not_C1
          simpa only [branch, Set.mem_ofPred_eq, Classical.not_not] using hy_not_C1
        have e_int := mem_interval_iff.mp hc_int
        have hd_eq : dist (vertex c : MetricGraph W) y = dist (vertex c : MetricGraph W) y' := by
          have htri := dist_triangle (z j) (vertex c) y'
          linarith [hsp_j, hsp_c, _root_.dist_comm y (z j), _root_.dist_comm y' (z j),
            _root_.dist_comm y (vertex c), _root_.dist_comm y' (vertex c),
            _root_.dist_comm (z j) (vertex c)]
        have hy'_ne_c : y' ≠ vertex c := by
          intro heq
          rw [heq, _root_.dist_self] at hd_eq
          have : y = vertex c := (dist_eq_zero.mp hd_eq).symm
          exact hne_res (this.trans heq.symm)
        let z_y := Function.update z j y
        have hz_y_S : ∀ i, z_y i ∈ subtree W S := fun i => by
          by_cases hi : i = j
          · subst hi; simpa [z_y] using hy_S
          · simpa [z_y, hi] using hz i
        have hsub_y : Finset.univ.filter (fun i => z_y i ∈ C₁) =
            (Finset.univ.filter fun i => z i ∈ C₁).erase j := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, z_y]
          by_cases hi : i = j
          · subst hi; simp [hy_not_C1]
          · simp [hi]
        have hcard_y : (Finset.univ.filter fun i => z_y i ∈ C₁).card = m - 1 := by
          rw [hsub_y, Finset.card_erase_of_mem hj, hcard]
        have hf_zy : f z_y = y := by
          have h1 := hsp z_y j (z j)
          have hupd : Function.update z_y j (z j) = z := by
            funext i
            by_cases hi : i = j
            · subst hi; simp [z_y]
            · simp [z_y, hi]
          rw [hupd] at h1
          simp only [z_y, Function.update_self] at h1
          change dist (f z_y) y ≤ dist y y at h1
          rw [_root_.dist_self, _root_.dist_comm] at h1
          exact (dist_eq_zero.mp (le_antisymm h1 dist_nonneg)).symm
        have hih_y : π₁ (f z_y) = f (fun i => π₁ (z_y i)) :=
          ih (m - 1) (Nat.sub_lt (Nat.pos_of_ne_zero hm) zero_lt_one) z_y hz_y_S hcard_y
        rw [hf_zy, hy_π] at hih_y
        have hπ_zy_S : ∀ i, π₁ (z_y i) ∈ subtree W (removeBranch hT S c w₁) := fun i =>
          projConvex_mem hT (convexSet_subtree hT hS₁) (z_y i)
        have hπ_z'_S : ∀ i, π₁ (z' i) ∈ subtree W (removeBranch hT S c w₁) := fun i =>
          projConvex_mem hT (convexSet_subtree hT hS₁) (z' i)
        have hinv1 := hinv_rem w₁ hw₁ hadj₁
        have hy_in_br : y ∈ branch (vertex c) y' := by
          by_contra hy_nbr
          have hiff : ∀ i, π₁ (z_y i) ∈ branch (vertex c) y' ↔
              π₁ (z' i) ∈ branch (vertex c) y' := fun i => by
            by_cases hi : i = j
            · subst hi
              simp only [z_y, z', Function.update_self]
              rw [hy_π]
              dsimp only [π₁]
              rw [projConvex_eq_self hT (convexSet_subtree hT hS₁) hc₁]
              simp [hy_nbr]
            · simp [z_y, z', hi]
          have hres := hinv1 hc₁ hy'_sub hy'_ne_c hπ_zy_S hπ_z'_S hiff
          rw [← hih_y, hπ_upd, ← hih', hy'_π] at hres
          exact hy_nbr (hres.mpr (mem_branch_self hy'_ne_c))
        have hP_proj : ∀ {u : ι → MetricGraph W},
            (∀ i, u i ∈ subtree W (removeBranch hT S c w₁)) →
            treeMedian hT (vertex c) y' (f u) =
              f (fun i => treeMedian hT (vertex c) y' (u i)) := fun hu =>
          proj_interval_of_branchInvOn hT hf_sp hf_onto hS₁ hinv1 hc₁ hy'_sub hu
        let m_pt := treeMedian hT (vertex c) y' y
        have hm_ab : m_pt ∈ interval (vertex c) y' := treeMedian_mem_xy hT (vertex c) y' y
        have hm_ne_c : m_pt ≠ vertex c := fun heq =>
          hy_in_br (heq ▸ treeMedian_mem_yz hT (vertex c) y' y)
        have hm_ne_y' : m_pt ≠ y' := by
          intro heq
          have hy'_int : y' ∈ interval (vertex c) y := by
            rw [← heq]
            exact interval_comm y (vertex c) ▸ treeMedian_mem_zx hT (vertex c) y' y
          have e1 := mem_interval_iff.mp hy'_int
          have hd0 : dist y' y = 0 := by linarith
          exact hne_res (dist_eq_zero.mp hd0).symm
        obtain ⟨φ, hφ, hφ0, hφd, hrange⟩ := exists_isometry_interval hT (vertex c) y'
        let d := dist (vertex c : MetricGraph W) y'
        have hd_pos : 0 < d := dist_pos.mpr hy'_ne_c.symm
        have hm_mem_range : m_pt ∈ Set.range φ := hrange.symm ▸ hm_ab
        obtain ⟨m₀, hm₀_eq⟩ := hm_mem_range
        have hm₀_gt : 0 < (m₀ : ℝ) := by
          by_contra hle
          have hm₀0 : (m₀ : ℝ) = 0 := le_antisymm (not_lt.mp hle) m₀.2.1
          have : m_pt = vertex c := by
            rw [← hm₀_eq, show m₀ = ⟨0, le_rfl, hd_pos.le⟩ from Subtype.ext hm₀0, hφ0]
          exact hm_ne_c this
        have hm₀_lt : (m₀ : ℝ) < d := by
          by_contra hle
          have hm₀d : (m₀ : ℝ) = d := le_antisymm m₀.2.2 (not_lt.mp hle)
          have : m_pt = y' := by
            rw [← hm₀_eq, show m₀ = ⟨d, hd_pos.le, le_rfl⟩ from Subtype.ext hm₀d, hφd]
          exact hm_ne_y' this
        have hf_range_P : ∀ u : ι → MetricGraph W,
            (∀ i, u i ∈ Set.range φ) → f u ∈ Set.range φ := fun u hu => by
          rw [hrange]
          exact range_of_convex hT hf_sp hf_onto
            ⟨⟨vertex c, left_mem_interval _ _⟩, isClosed_interval _ _,
              fun _ _ h1 h2 => interval_subset_of_mem hT h1 h2⟩
            (fun i => hrange ▸ hu i)
        have hf_onto_P : ∀ u ∈ Set.range φ,
            ∃ q : ι → MetricGraph W, (∀ i, q i ∈ Set.range φ) ∧ f q = u :=
          fun u hu => ⟨fun _ => u, fun _ => hu,
            unanimous_of_surjective_isStrategyProof hf_sp hf_onto u⟩
        obtain ⟨E_P, hE_P⟩ := moulinScheme_of_isometry hd_pos.le φ hφ hf_sp hf_range_P hf_onto_P
        let b_base : ι → Set.Icc 0 d := fun i =>
          Classical.choose (hrange.symm ▸ treeMedian_mem_xy hT (vertex c) y' (π₁ (z' i)))
        have hb_base : ∀ i, φ (b_base i) = treeMedian hT (vertex c) y' (π₁ (z' i)) := fun i =>
          Classical.choose_spec (hrange.symm ▸ treeMedian_mem_xy hT (vertex c) y' (π₁ (z' i)))
        have hc_eq_P : (fun i => φ (Function.update b_base j ⟨0, le_rfl, hd_pos.le⟩ i)) =
            fun i => treeMedian hT (vertex c) y' (π₁ (z' i)) := by
          funext i
          by_cases hi : i = j
          · subst hi
            simp only [Function.update_self, hφ0, z']
            dsimp only [π₁]
            rw [projConvex_eq_self hT (convexSet_subtree hT hS₁) hc₁]
            exact eq_treeMedian_of_mem hT (left_mem_interval (vertex c) y')
              (right_mem_interval y' (vertex c)) (left_mem_interval (vertex c) (vertex c))
          · simp [hi, hb_base i]
        have hm_eq_P : (fun i => φ (Function.update b_base j m₀ i)) =
            fun i => treeMedian hT (vertex c) y' (π₁ (z_y i)) := by
          funext i
          by_cases hi : i = j
          · subst hi
            simp only [Function.update_self, hm₀_eq, z_y, hy_π]
            rfl
          · simp [hi, hb_base i, z_y, z']
        have h0_eval := hP_proj hπ_z'_S
        rw [hπ_upd, ← hih', hy'_π] at h0_eval
        have h0_med : treeMedian hT (vertex c) y' y' = y' :=
          (eq_treeMedian_of_mem hT (right_mem_interval _ _) (left_mem_interval _ _)
            (left_mem_interval _ _)).symm
        rw [h0_med, ← hc_eq_P, hE_P] at h0_eval
        have hm_eval := hP_proj hπ_zy_S
        rw [← hih_y, ← hm_eq_P, hE_P] at hm_eval
        have hm_self : treeMedian hT (vertex c) y' y = m_pt := rfl
        rw [hm_self, ← hm₀_eq] at hm_eval
        have h0_eq_d : (E_P.eval (Function.update b_base j ⟨0, le_rfl, hd_pos.le⟩) : ℝ) = d := by
          have heq' : φ (E_P.eval (Function.update b_base j ⟨0, le_rfl, hd_pos.le⟩)) =
              φ ⟨d, hd_pos.le, le_rfl⟩ := h0_eval.symm.trans hφd.symm
          exact congrArg Subtype.val (hφ.injective heq')
        have hm_eq_m0 : (E_P.eval (Function.update b_base j m₀) : ℝ) = m₀ :=
          congrArg Subtype.val (hφ.injective hm_eval.symm)
        have hmono := E_P.eval_mono (x := Function.update b_base j ⟨0, le_rfl, hd_pos.le⟩)
          (z := Function.update b_base j m₀) fun i => by
          by_cases hi : i = j
          · subst hi; simp [hm₀_gt.le]
          · simp [hi]
        linarith
      · have hy_C1 : y ∈ C₁ := by
          rw [subtree_removeBranch hT hS hc hadj₁] at hy_sub
          simpa [C₁, hy_S] using hy_sub
        have hπ_y : π₁ y = vertex c :=
          projConvex_removeBranch_mem hT hS hc hadj₁ hy_C1
        rw [hπ_y] at hne_res
        have hy'_ne_c : π₁ y' ≠ vertex c := Ne.symm hne_res
        have hy'_S1 : π₁ y' ∈ subtree W (removeBranch hT S c w₁) :=
          projConvex_mem hT (convexSet_subtree hT hS₁) y'
        have hy'_in_S : π₁ y' ∈ subtree W S := by
          rw [subtree_removeBranch hT hS hc hadj₁] at hy'_S1
          exact hy'_S1.1
        obtain ⟨w₂, hw₂, hadj₂, hπy'_br⟩ :=
          exists_adj_of_mem_subtree_ne hT hS hc hy'_in_S hy'_ne_c
        have hw₁_ne_w₂ : w₁ ≠ w₂ := fun heq => by
          subst heq
          rw [subtree_removeBranch hT hS hc hadj₁] at hy'_S1
          exact hy'_S1.2 hπy'_br
        obtain ⟨T, hT3, hT_mem⟩ := hdeg3
        have hnb_sub : ∃ w₃ ∈ T, w₃ ≠ w₁ ∧ w₃ ≠ w₂ := by
          by_contra hnot
          push Not at hnot
          have hsub2 : T ⊆ {w₁, w₂} := fun w hw => by
            by_cases h1 : w = w₁
            · simp [h1]
            · have := hnot w hw h1
              simp [this]
          have hcard2 : T.card ≤ 2 :=
            (Finset.card_le_card hsub2).trans ((Finset.card_insert_le _ _).trans (by simp))
          linarith
        obtain ⟨w₃, hw₃_T, hw₃_ne1, hw₃_ne2⟩ := hnb_sub
        obtain ⟨hw₃, hadj₃⟩ := hT_mem w₃ hw₃_T
        let C₂ := branch (vertex c : MetricGraph W) (vertex w₂)
        let S₃ := removeBranch hT S c w₃
        have hS₃ := convexVertices_removeBranch hT hS hc hadj₃
        have hC₁_sub3 : ∀ u ∈ subtree W S, u ∈ C₁ → u ∈ subtree W S₃ := by
          intro u huS huC1
          rw [subtree_removeBranch hT hS hc hadj₃]
          refine ⟨huS, fun huC3 => ?_⟩
          exact Set.disjoint_left.mp (branch_adj_disjoint hT hadj₁ hadj₃ hw₃_ne1.symm) huC1 huC3
        have hC₂_sub3 : ∀ u ∈ subtree W S, u ∈ C₂ → u ∈ subtree W S₃ := by
          intro u huS huC2
          rw [subtree_removeBranch hT hS hc hadj₃]
          refine ⟨huS, fun huC3 => ?_⟩
          exact Set.disjoint_left.mp (branch_adj_disjoint hT hadj₂ hadj₃ hw₃_ne2.symm) huC2 huC3
        let S₁ := removeBranch hT S c w₁
        have hc_sub3 : (vertex c : MetricGraph W) ∈ subtree W S₃ :=
          vertex_mem_subtree W ((mem_removeBranch_iff hT hadj₃).mpr ⟨hc, .refl c⟩)
        have hloop : ∀ (kopp : ℕ) (Y : Finset ι) (u : ι → MetricGraph W),
            Y.Nonempty → (∀ i ∈ Y, u i = y) →
            (∀ i, u i ∈ subtree W S) →
            f u = y →
            (let u_v := fun i => if i ∈ Y then vertex c else u i
            (Finset.univ.filter fun i => u_v i ∈ C₁).card < m ∧
            f (fun i => π₁ (u_v i)) ∈ C₂) →
            (Finset.univ.filter fun i => i ∉ Y ∧ u i ∈ subtree W S₁ \ C₂).card = kopp →
            False := by
          intro kopp
          induction kopp with
          | zero =>
            intro Y u hY_ne hYu hu_S hfu ⟨huv_card, hπuv_C2⟩ hk0
            have hemp : (Finset.univ.filter fun i => i ∉ Y ∧ u i ∈ subtree W S₁ \ C₂) = ∅ :=
              Finset.card_eq_zero.mp hk0
            let u_v : ι → MetricGraph W := fun i => if i ∈ Y then vertex c else u i
            have huv_S : ∀ i, u_v i ∈ subtree W S := fun i => by
              dsimp only [u_v]
              split_ifs
              · exact vertex_mem_subtree W hc
              · exact hu_S i
            have hfuv_π : π₁ (f u_v) = f (fun i => π₁ (u_v i)) :=
              ih _ huv_card u_v huv_S rfl
            have hfuv_C2 : f u_v ∈ C₂ := by
              rw [← hfuv_π] at hπuv_C2
              have hnot_C1 : f u_v ∉ C₁ := by
                intro hmem
                have hπc : π₁ (f u_v) = vertex c :=
                  projConvex_removeBranch_mem hT hS hc hadj₁ hmem
                rw [hπc] at hπuv_C2
                exact (notMem_branch_self (vertex c) (vertex w₂)) hπuv_C2
              have hS_fuv : f u_v ∈ subtree W S :=
                range_of_convex hT hf_sp hf_onto (convexSet_subtree hT hS) huv_S
              have hπself : π₁ (f u_v) = f u_v :=
                projConvex_removeBranch_notMem hT hS hc hadj₁ hS_fuv hnot_C1
              rwa [hπself] at hπuv_C2
            have hu_S3 : ∀ i, u i ∈ subtree W S₃ := fun i => by
              by_cases hiY : i ∈ Y
              · rw [hYu i hiY]
                exact hC₁_sub3 y hy_S hy_C1
              · by_cases hiC1 : u i ∈ C₁
                · exact hC₁_sub3 (u i) (hu_S i) hiC1
                · have hi_S1 : u i ∈ subtree W S₁ := by
                    rw [subtree_removeBranch hT hS hc hadj₁]
                    exact ⟨hu_S i, hiC1⟩
                  have hi_C2 : u i ∈ C₂ := by
                    by_contra hi_nC2
                    have hmem : i ∈ Finset.univ.filter fun i => i ∉ Y ∧ u i ∈ subtree W S₁ \ C₂ :=
                      Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiY, hi_S1, hi_nC2⟩
                    rw [hemp] at hmem
                    exact Finset.notMem_empty i hmem
                  exact hC₂_sub3 (u i) (hu_S i) hi_C2
            have huv_S3 : ∀ i, u_v i ∈ subtree W S₃ := fun i => by
              dsimp only [u_v]
              split_ifs
              · exact hc_sub3
              · exact hu_S3 i
            have hw2_S3 : (vertex w₂ : MetricGraph W) ∈ subtree W S₃ :=
              hC₂_sub3 (vertex w₂) (vertex_mem_subtree W hw₂)
                (mem_branch_self (fun h => hadj₂.ne (vertex_injective (W := W) h.symm)))
            have hinv3 := hinv_rem w₃ hw₃ hadj₃
            have hy_not_C2 : y ∉ C₂ := Set.disjoint_left.mp
              (branch_adj_disjoint hT hadj₁ hadj₂ hw₁_ne_w₂) hy_C1
            have hiff3 : ∀ i, u i ∈ C₂ ↔ u_v i ∈ C₂ := fun i => by
              dsimp only [u_v]
              split_ifs with hiY
              · rw [hYu i hiY]
                simp [C₂, hy_not_C2]
              · rfl
            have heq_C2 := hinv3 hc_sub3 hw2_S3
              (fun h => hadj₂.ne (vertex_injective (W := W) h.symm)) hu_S3 huv_S3 hiff3
            rw [hfu] at heq_C2
            exact hy_not_C2 (heq_C2.mpr hfuv_C2)
          | succ k ihk =>
            intro Y u hY_ne hYu hu_S hfu ⟨huv_card, hπuv_C2⟩ hk_succ
            have hne_opp : (Finset.univ.filter fun i => i ∉ Y ∧ u i ∈ subtree W S₁ \ C₂).Nonempty :=
              Finset.card_pos.mp (hk_succ ▸ Nat.succ_pos k)
            obtain ⟨i₀, hi₀⟩ := hne_opp
            have hi₀_prop := (Finset.mem_filter.mp hi₀).2
            have hi₀_notY : i₀ ∉ Y := hi₀_prop.1
            have hi₀_S1 : u i₀ ∈ subtree W S₁ := hi₀_prop.2.1
            have hi₀_notC2 : u i₀ ∉ C₂ := hi₀_prop.2.2
            let Y' := insert i₀ Y
            let u' := Function.update u i₀ y
            have hfu' : f u' = y := by
              have h1 := hsp u' i₀ (u i₀)
              have hupd : Function.update u' i₀ (u i₀) = u := by
                funext i
                by_cases hi : i = i₀
                · subst hi; simp [u']
                · simp [u', hi]
              rw [hupd, hfu] at h1
              simp only [u', Function.update_self] at h1
              change dist (f u') y ≤ dist y y at h1
              rw [_root_.dist_self, _root_.dist_comm] at h1
              exact (dist_eq_zero.mp (le_antisymm h1 dist_nonneg)).symm
            let u_v : ι → MetricGraph W := fun i => if i ∈ Y then vertex c else u i
            let u'_v : ι → MetricGraph W := fun i => if i ∈ Y' then vertex c else u' i
            have hu'_v_eq : u'_v = Function.update u_v i₀ (vertex c) := by
              funext i
              by_cases hi : i = i₀
              · subst hi; simp [u'_v, Y']
              · have : (i ∈ Y') ↔ (i ∈ Y) := Finset.mem_insert.trans (or_iff_right hi)
                simp [u'_v, u_v, u', hi, this]
            have huv_card' : (Finset.univ.filter fun i => u'_v i ∈ C₁).card < m := by
              have hsub_C1 : (Finset.univ.filter fun i => u'_v i ∈ C₁) =
                  Finset.univ.filter fun i => u_v i ∈ C₁ := by
                ext i
                rw [hu'_v_eq]
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                by_cases hi : i = i₀
                · rw [hi, Function.update_self]
                  have hui0 : u_v i₀ = u i₀ := by simp [u_v, hi₀_notY]
                  have hi0_notC1 : u i₀ ∉ C₁ := by
                    rw [subtree_removeBranch hT hS hc hadj₁] at hi₀_S1
                    exact hi₀_S1.2
                  rw [hui0]
                  simp [C₁, hi0_notC1]
                · simp [hi]
              rw [hsub_C1]
              exact huv_card
            have hπ_uv_S1 : ∀ i, π₁ (u_v i) ∈ subtree W S₁ := fun i =>
              projConvex_mem hT (convexSet_subtree hT hS₁) (u_v i)
            have hπ_u'v_S1 : ∀ i, π₁ (u'_v i) ∈ subtree W S₁ := fun i =>
              projConvex_mem hT (convexSet_subtree hT hS₁) (u'_v i)
            have hw2_S1 : (vertex w₂ : MetricGraph W) ∈ subtree W S₁ := by
              rw [subtree_removeBranch hT hS hc hadj₁]
              refine ⟨vertex_mem_subtree W hw₂, fun hw2_C1 => ?_⟩
              exact Set.disjoint_left.mp (branch_adj_disjoint hT hadj₁ hadj₂ hw₁_ne_w₂)
                hw2_C1 (mem_branch_self (fun h => hadj₂.ne (vertex_injective (W := W) h.symm)))
            have hinv1 := hinv_rem w₁ hw₁ hadj₁
            have hiff1 : ∀ i, π₁ (u_v i) ∈ C₂ ↔ π₁ (u'_v i) ∈ C₂ := fun i => by
              by_cases hi : i = i₀
              · rw [hi, hu'_v_eq, Function.update_self]
                have hui0 : u_v i₀ = u i₀ := by simp [u_v, hi₀_notY]
                rw [hui0]
                dsimp only [π₁]
                rw [projConvex_eq_self hT (convexSet_subtree hT hS₁) hc₁,
                  projConvex_eq_self hT (convexSet_subtree hT hS₁) hi₀_S1]
                simp [C₂, hi₀_notC2]
              · simp [hu'_v_eq, hi]
            have hπu'v_C2 : f (fun i => π₁ (u'_v i)) ∈ C₂ :=
              (hinv1 hc₁ hw2_S1 (fun h => hadj₂.ne (vertex_injective (W := W) h.symm))
                hπ_uv_S1 hπ_u'v_S1 hiff1).mp hπuv_C2
            have hsub_opp : (Finset.univ.filter fun i => i ∉ Y' ∧ u' i ∈ subtree W S₁ \ C₂) =
                (Finset.univ.filter fun i => i ∉ Y ∧ u i ∈ subtree W S₁ \ C₂).erase i₀ := by
              ext i
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, Y', u']
              by_cases hi : i = i₀
              · subst hi; simp
              · simp [hi]
            have hcard_opp' : (Finset.univ.filter fun i =>
                i ∉ Y' ∧ u' i ∈ subtree W S₁ \ C₂).card = k := by
              rw [hsub_opp, Finset.card_erase_of_mem hi₀, hk_succ]
              simp
            exact ihk Y' u' (Finset.insert_nonempty i₀ Y) (fun i hi => by
              rcases Finset.mem_insert.mp hi with rfl | hiY
              · simp [u']
              · have hine : i ≠ i₀ := fun heq => hi₀_notY (heq ▸ hiY)
                simpa [u', hine] using hYu i hiY)
              (fun i => by
                by_cases hi : i = i₀
                · subst hi; simpa [u'] using hy_S
                · simpa [u', hi] using hu_S i)
              hfu' ⟨huv_card', hπu'v_C2⟩ hcard_opp'
        let z_y := Function.update z j y
        have hfz_y : f z_y = y := by
          have h1 := hsp z_y j (z j)
          have hupd : Function.update z_y j (z j) = z := by
            funext i
            by_cases hi : i = j
            · subst hi; simp [z_y]
            · simp [z_y, hi]
          rw [hupd] at h1
          simp only [z_y, Function.update_self] at h1
          change dist (f z_y) y ≤ dist y y at h1
          rw [_root_.dist_self, _root_.dist_comm] at h1
          exact (dist_eq_zero.mp (le_antisymm h1 dist_nonneg)).symm
        have hz_y_S : ∀ i, z_y i ∈ subtree W S := fun i => by
          by_cases hi : i = j
          · subst hi; simpa [z_y] using hy_S
          · simpa [z_y, hi] using hz i
        let u_v : ι → MetricGraph W := fun i => if i ∈ ({j} : Finset ι) then vertex c else z_y i
        have hu_v_eq : u_v = z' := by
          funext i
          by_cases hi : i = j
          · subst hi; simp [u_v, z']
          · simp [u_v, z', z_y, hi]
        have huv_card : (Finset.univ.filter fun i => u_v i ∈ C₁).card < m := by
          rw [hu_v_eq, hcard']
          exact Nat.sub_lt (Nat.pos_of_ne_zero hm) zero_lt_one
        have hπuv_C2 : f (fun i => π₁ (u_v i)) ∈ C₂ := by
          rw [hu_v_eq, hπ_upd, ← hih']
          exact hπy'_br
        exact hloop _ {j} z_y (Finset.singleton_nonempty j)
          (fun i hi => by rw [Finset.mem_singleton.mp hi]; simp [z_y])
          hz_y_S hfz_y ⟨huv_card, hπuv_C2⟩ rfl

private lemma branchInvOn_all
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_onto : Function.Surjective f)
    (S : Finset V) (hS : ConvexVertices W S) :
    BranchInvOn W f S := by
  classical
  induction hcard : S.card using Nat.strong_induction_on generalizing S with
  | ind n ih =>
    by_cases hdeg : ∀ v ∈ S, (S.filter fun u => W.graph.Adj v u).card ≤ 2
    · have hdeg' : ∀ v ∈ S, ∀ T : Finset V,
          (∀ u ∈ T, u ∈ S ∧ W.graph.Adj v u) → T.card ≤ 2 := fun v hv T hT_mem => by
        have hsub : T ⊆ S.filter fun u => W.graph.Adj v u := fun u hu =>
          Finset.mem_filter.mpr (hT_mem u hu)
        exact (Finset.card_le_card hsub).trans (hdeg v hv)
      obtain ⟨a, ha, b, hb, hsub⟩ := path_subtree_eq_interval hT hS hdeg'
      exact branchInvOn_of_interval hT hf_sp hf_onto hS ha hb hsub
    · push Not at hdeg
      obtain ⟨c, hc, hdeg3⟩ := hdeg
      have hdeg3' : ∃ T : Finset V, 3 ≤ T.card ∧ ∀ u ∈ T, u ∈ S ∧ W.graph.Adj c u :=
        ⟨S.filter fun u => W.graph.Adj c u, hdeg3, fun u hu => Finset.mem_filter.mp hu⟩
      have hinv_rem : ∀ w ∈ S, W.graph.Adj c w → BranchInvOn W f (removeBranch hT S c w) :=
        fun w hw hadj => ih (removeBranch hT S c w).card
          (hcard ▸ card_removeBranch_lt hT hw hadj)
          (removeBranch hT S c w) (convexVertices_removeBranch hT hS hc hadj) rfl
      have hproj : ∀ w ∈ S, ∀ (hadj : W.graph.Adj c w) (x : ι → MetricGraph W),
          (∀ i, x i ∈ subtree W S) →
          let π := projConvex hT (convexSet_subtree hT (convexVertices_removeBranch hT hS hc hadj))
          π (f x) = f (fun i => π (x i)) := fun w hw hadj x hx =>
        proj_removeBranch_of_branchInvOn hT hf_sp hf_onto hS hc hw hadj hdeg3' hinv_rem hx
      intro y q hy hq hqy x₁ x₂ hx₁ hx₂ hiff
      let nb := S.filter fun w => W.graph.Adj c w
      have hnb_ex : ∃ w ∈ nb, y ∉ branch (vertex c) (vertex w) ∧
          q ∉ branch (vertex c) (vertex w) := by
        by_contra hnot
        push Not at hnot
        have hsub : nb ⊆ (nb.filter fun w => y ∈ branch (vertex c) (vertex w)) ∪
            (nb.filter fun w => q ∈ branch (vertex c) (vertex w)) := fun w hw => by
          simp only [Finset.mem_union, Finset.mem_filter]
          rcases em (y ∈ branch (vertex c) (vertex w)) with hyw | hyw
          · exact Or.inl ⟨hw, hyw⟩
          · exact Or.inr ⟨hw, hnot w hw hyw⟩
        have hc1 : (nb.filter fun w => y ∈ branch (vertex c) (vertex w)).card ≤ 1 := by
          rw [Finset.card_le_one]
          intro w₁ hw₁ w₂ hw₂
          rw [Finset.mem_filter] at hw₁ hw₂
          by_contra hne
          have hadj1 := (Finset.mem_filter.mp hw₁.1).2
          have hadj2 := (Finset.mem_filter.mp hw₂.1).2
          exact Set.disjoint_left.mp (branch_adj_disjoint hT hadj1 hadj2 hne) hw₁.2 hw₂.2
        have hc2 : (nb.filter fun w => q ∈ branch (vertex c) (vertex w)).card ≤ 1 := by
          rw [Finset.card_le_one]
          intro w₁ hw₁ w₂ hw₂
          rw [Finset.mem_filter] at hw₁ hw₂
          by_contra hne
          have hadj1 := (Finset.mem_filter.mp hw₁.1).2
          have hadj2 := (Finset.mem_filter.mp hw₂.1).2
          exact Set.disjoint_left.mp (branch_adj_disjoint hT hadj1 hadj2 hne) hw₁.2 hw₂.2
        have hsum := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        linarith
      obtain ⟨w, hw_nb, hy_not, hq_not⟩ := hnb_ex
      rw [Finset.mem_filter] at hw_nb
      obtain ⟨hw, hadj⟩ := hw_nb
      let Sw := removeBranch hT S c w
      have hSw := convexVertices_removeBranch hT hS hc hadj
      let π := projConvex hT (convexSet_subtree hT hSw)
      have hy_Sw : y ∈ subtree W Sw := by
        rw [subtree_removeBranch hT hS hc hadj]
        exact ⟨hy, hy_not⟩
      have hq_Sw : q ∈ subtree W Sw := by
        rw [subtree_removeBranch hT hS hc hadj]
        exact ⟨hq, hq_not⟩
      have hπ1_Sw : ∀ i, π (x₁ i) ∈ subtree W Sw := fun i =>
        projConvex_mem hT (convexSet_subtree hT hSw) (x₁ i)
      have hπ2_Sw : ∀ i, π (x₂ i) ∈ subtree W Sw := fun i =>
        projConvex_mem hT (convexSet_subtree hT hSw) (x₂ i)
      have hiff' : ∀ i, π (x₁ i) ∈ branch y q ↔ π (x₂ i) ∈ branch y q := fun i => by
        rw [← mem_branch_projConvex_iff hT (convexSet_subtree hT hSw) hy_Sw hq_Sw (x₁ i),
          ← mem_branch_projConvex_iff hT (convexSet_subtree hT hSw) hy_Sw hq_Sw (x₂ i)]
        exact hiff i
      have hinv_w := hinv_rem w hw hadj hy_Sw hq_Sw hqy hπ1_Sw hπ2_Sw hiff'
      rw [← hproj w hw hadj x₁ hx₁, ← hproj w hw hadj x₂ hx₂] at hinv_w
      rw [mem_branch_projConvex_iff hT (convexSet_subtree hT hSw) hy_Sw hq_Sw (f x₁),
        mem_branch_projConvex_iff hT (convexSet_subtree hT hSw) hy_Sw hq_Sw (f x₂)]
      exact hinv_w

omit [Finite ι] in
/-- Schummer–Vohra characterization on tree metric graphs ([SchummerVohra2002], Theorem 1, with
`TreeEMVS` in place of the source's path-based definition): a deterministic mechanism on a finite
tree metric graph is strategyproof and surjective if and only if it is the evaluation map of a
`TreeEMVS`. -/
theorem isStrategyProof_and_surjective_iff_exists_treeEMVS [Fintype ι]
    [Nonempty V] [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) (f : (ι → MetricGraph W) → MetricGraph W) :
    ((Mechanism.deterministic f).IsStrategyProof ∧ Function.Surjective f) ↔
      ∃ E : TreeEMVS W ι, f = E.eval hT := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  constructor
  · rintro ⟨hf_sp, hf_onto⟩
    have hf_unan : ∀ y : MetricGraph W, f (fun _ => y) = y :=
      unanimous_of_surjective_isStrategyProof hf_sp hf_onto
    have hinv_univ := branchInvOn_all hT hf_sp hf_onto Finset.univ (convexVertices_univ W)
    have hinv : ∀ {y q : MetricGraph W}, q ≠ y →
        ∀ {x₁ x₂ : ι → MetricGraph W},
          (∀ i, x₁ i ∈ branch y q ↔ x₂ i ∈ branch y q) →
          (f x₁ ∈ branch y q ↔ f x₂ ∈ branch y q) := fun {y q} hqy {x₁ x₂} hiff =>
      hinv_univ (subtree_univ hT ▸ Set.mem_univ y) (subtree_univ hT ▸ Set.mem_univ q) hqy
        (fun _ => subtree_univ hT ▸ Set.mem_univ _) (fun _ => subtree_univ hT ▸ Set.mem_univ _) hiff
    let win : MetricGraph W → MetricGraph W → Finset ι → Prop :=
      fun y q S => f (fun i => if i ∈ S then q else y) ∈ branch y q
    have hwin_eq_profile : ∀ {y q : MetricGraph W} (hq : q ≠ y) {S : Finset ι}
        {x : ι → MetricGraph W}, (∀ i, x i ∈ branch y q ↔ i ∈ S) →
        (f x ∈ branch y q ↔ win y q S) := by
      intro y q hq S x hS
      refine hinv hq fun i => ?_
      rw [hS i]
      by_cases hi : i ∈ S
      · simp [hi, mem_branch_self hq]
      · simp [hi]
    let E : TreeEMVS W ι :=
      { win := win
        branch_eq := fun {y q₁ q₂} hq1 hq2 hbr => by
          ext S
          dsimp only [win]
          have hx : ∀ i, (if i ∈ S then q₁ else y) ∈ branch y q₂ ↔ i ∈ S := fun i => by
            rw [← hbr]
            by_cases hi : i ∈ S <;> simp [hi, mem_branch_self hq1]
          rw [show (f (fun i => if i ∈ S then q₁ else y) ∈ branch y q₁) ↔
            (f (fun i => if i ∈ S then q₁ else y) ∈ branch y q₂) by rw [hbr]]
          exact hwin_eq_profile hq2 hx
        empty_false := fun {y q} _ => by
          simp only [win, Finset.notMem_empty, ↓reduceIte, hf_unan, notMem_branch_self,
            not_false_eq_true]
        univ_true := fun {y q} hq => by
          simp only [win, Finset.mem_univ, ↓reduceIte, hf_unan, mem_branch_self hq]
        mono := fun {y q S T} hq hST hwinS => by
          let x₁ : ι → MetricGraph W := fun i => if i ∈ S then q else y
          let x₂ : ι → MetricGraph W := fun i => if i ∈ T then q else y
          obtain ⟨φ, hφ, hφ0, hφd, hrange⟩ := exists_isometry_interval hT y q
          have hconv : ConvexSet W (interval y q) :=
            ⟨⟨y, left_mem_interval _ _⟩, isClosed_interval _ _,
              fun _ _ h1 h2 => interval_subset_of_mem hT h1 h2⟩
          have hf_range : ∀ u : ι → MetricGraph W, (∀ i, u i ∈ Set.range φ) → f u ∈ Set.range φ :=
            fun u hu => hrange.symm ▸ range_of_convex hT hf_sp hf_onto hconv fun i =>
              hrange ▸ hu i
          have hf_onto_I : ∀ u ∈ Set.range φ,
              ∃ x : ι → MetricGraph W, (∀ i, x i ∈ Set.range φ) ∧ f x = u :=
            fun u hu => ⟨fun _ => u, fun _ => hu, hf_unan u⟩
          obtain ⟨E_I, hE_I⟩ := moulinScheme_of_isometry dist_nonneg φ hφ hf_sp hf_range hf_onto_I
          let d := dist y q
          have hd_nn : 0 ≤ d := dist_nonneg
          let c₁ : ι → Set.Icc 0 d := fun i =>
            if i ∈ S then ⟨d, hd_nn, le_rfl⟩ else ⟨0, le_rfl, hd_nn⟩
          let c₂ : ι → Set.Icc 0 d := fun i =>
            if i ∈ T then ⟨d, hd_nn, le_rfl⟩ else ⟨0, le_rfl, hd_nn⟩
          have hx₁_eq : (fun i => φ (c₁ i)) = x₁ := funext fun i => by
            dsimp only [c₁, x₁]
            split_ifs with hi
            · exact hφd
            · exact hφ0
          have hx₂_eq : (fun i => φ (c₂ i)) = x₂ := funext fun i => by
            dsimp only [c₂, x₂]
            split_ifs with hi
            · exact hφd
            · exact hφ0
          have hle : ∀ i, (c₁ i : ℝ) ≤ c₂ i := fun i => by
            by_cases h1 : i ∈ S <;> by_cases h2 : i ∈ T
            · simp [c₁, c₂, h1, h2]
            · exact absurd (hST h1) h2
            · simp [c₁, c₂, h1, h2, hd_nn]
            · simp [c₁, c₂, h1, h2]
          have hmono := E_I.eval_mono hle
          have hf₁_eq : f x₁ = φ (E_I.eval c₁) := by rw [← hx₁_eq, hE_I c₁]
          have hf₂_eq : f x₂ = φ (E_I.eval c₂) := by rw [← hx₂_eq, hE_I c₂]
          have hne_01 : (0 : ℝ) < E_I.eval c₁ := by
            by_contra hle0
            have h0 : (E_I.eval c₁ : ℝ) = 0 := le_antisymm (not_lt.mp hle0) (E_I.eval c₁).2.1
            have hfx1_y : f x₁ = y := by
              rw [hf₁_eq, show E_I.eval c₁ = ⟨0, le_rfl, hd_nn⟩ from Subtype.ext h0, hφ0]
            have hw1 : f x₁ ∈ branch y q := hwinS
            rw [hfx1_y] at hw1
            exact notMem_branch_self y q hw1
          have hne_02 : (0 : ℝ) < E_I.eval c₂ := hne_01.trans_le hmono
          have hf₂_ne : f x₂ ≠ y := fun heq => by
            have heq' : φ (E_I.eval c₂) = φ ⟨0, le_rfl, hd_nn⟩ :=
              (hf₂_eq.symm.trans heq).trans hφ0.symm
            have : (E_I.eval c₂ : ℝ) = 0 := congrArg Subtype.val (hφ.injective heq')
            linarith
          have hf₂_mem : f x₂ ∈ interval y q := hrange ▸ hf₂_eq ▸ ⟨E_I.eval c₂, rfl⟩
          exact interval_subset_branch hT (mem_branch_self hq) hf₂_mem hf₂_ne
        nesting := fun {y₁ q₁ y₂ q₂ S} hq1 hq2 hsub hwin2 => by
          let x : ι → MetricGraph W := fun i => if i ∈ S then q₂ else y₁
          have hy1_n : y₁ ∉ branch y₂ q₂ := fun hmem => (notMem_branch_self y₁ q₁) (hsub hmem)
          have hx_2 : ∀ i, x i ∈ branch y₂ q₂ ↔ i ∈ S := fun i => by
            by_cases hi : i ∈ S <;> simp [x, hi, mem_branch_self hq2, hy1_n]
          have hx_1 : ∀ i, x i ∈ branch y₁ q₁ ↔ i ∈ S := fun i => by
            by_cases hi : i ∈ S
            · simp [x, hi, hsub (mem_branch_self hq2)]
            · simp [x, hi]
          have hfx_2 : f x ∈ branch y₂ q₂ := (hwin_eq_profile hq2 hx_2).mpr hwin2
          have hfx_1 : f x ∈ branch y₁ q₁ := hsub hfx_2
          exact (hwin_eq_profile hq1 hx_1).mp hfx_1
        duality := fun {y₁ y₂ S} h12 hnot => by
          let x : ι → MetricGraph W := fun i => if i ∈ S then y₂ else y₁
          have hx_12 : ∀ i, x i ∈ branch y₁ y₂ ↔ i ∈ S := fun i => by
            by_cases hi : i ∈ S <;> simp [x, hi, mem_branch_self h12.symm]
          have hfx_not : f x ∉ branch y₁ y₂ := fun h => hnot ((hwin_eq_profile h12.symm hx_12).mp h)
          have hfx_21 : f x ∈ branch y₂ y₁ := branch_symm h12 hfx_not
          have hx_21 : ∀ i, x i ∈ branch y₂ y₁ ↔ i ∈ Sᶜ := fun i => by
            by_cases hi : i ∈ S <;> simp [x, hi, mem_branch_self h12]
          exact (hwin_eq_profile h12 hx_21).mp hfx_21
        exclusive := fun {y q₁ q₂ S} hq1 hq2 hbr ⟨hw1, hw2⟩ => by
          have hdisj := branch_disjoint_of_ne hT hbr
          let x : ι → MetricGraph W := fun i => if i ∈ S then q₁ else q₂
          have hx1 : ∀ i, x i ∈ branch y q₁ ↔ i ∈ S := fun i => by
            by_cases hi : i ∈ S
            · simp [x, hi, mem_branch_self hq1]
            · simp [x, hi, Set.disjoint_right.mp hdisj (mem_branch_self hq2)]
          have hx2 : ∀ i, x i ∈ branch y q₂ ↔ i ∈ Sᶜ := fun i => by
            by_cases hi : i ∈ S
            · simp [x, hi, Set.disjoint_left.mp hdisj (mem_branch_self hq1)]
            · simp [x, hi, mem_branch_self hq2]
          exact Set.disjoint_left.mp hdisj
            ((hwin_eq_profile hq1 hx1).mpr hw1) ((hwin_eq_profile hq2 hx2).mpr hw2)
        open_interior := fun {y q S} hq hwin => by
          let x : ι → MetricGraph W := fun i => if i ∈ S then q else y
          have hx_int : ∀ i, x i ∈ interval y q := fun i => by
            by_cases hi : i ∈ S <;> simp [x, hi]
          have hconv : ConvexSet W (interval y q) :=
            ⟨⟨y, left_mem_interval _ _⟩, isClosed_interval _ _,
              fun _ _ h1 h2 => interval_subset_of_mem hT h1 h2⟩
          have hz_int : f x ∈ interval y q := range_of_convex hT hf_sp hf_onto hconv hx_int
          have hz_br : f x ∈ branch y q := hwin
          have hz_ne_y : f x ≠ y := fun heq => (notMem_branch_self y q) (heq ▸ hz_br)
          have hdz_pos : 0 < dist y (f x) := dist_pos.mpr hz_ne_y.symm
          obtain ⟨p, hp_z, hp_dist, _⟩ :=
            exists_mem_interval_dist_eq y (f x) ⟨(half_pos hdz_pos).le, half_le_self hdz_pos.le⟩
          have hp_q : p ∈ interval y q :=
            interval_subset_of_mem hT (left_mem_interval y q) hz_int hp_z
          have hp_ne_y : p ≠ y := fun heq => by rw [heq, _root_.dist_self] at hp_dist; linarith
          have hp_ne_q : p ≠ q := fun heq => by
            have h1 := mem_interval_iff.mp hz_int
            have h2 := dist_nonneg (x := f x) (y := q)
            rw [← heq, hp_dist] at h1
            rw [← heq] at h2
            linarith
          have hy_nbr : y ∉ branch p q := by
            simp only [branch, Set.mem_ofPred_eq, Classical.not_not]
            exact interval_comm y q ▸ hp_q
          have hq_br : q ∈ branch p q := mem_branch_self hp_ne_q.symm
          have hfz_br : f x ∈ branch p q := by
            simp only [branch, Set.mem_ofPred_eq]
            intro hmem
            have e1 := mem_interval_iff.mp hmem
            have e2 := mem_interval_iff.mp hp_q
            have e3 := mem_interval_iff.mp hp_z
            have e4 := mem_interval_iff.mp hz_int
            have hd : dist p (f x) = 0 := by
              linarith [_root_.dist_comm q p, _root_.dist_comm q (f x),
                _root_.dist_comm p (f x)]
            have : f x = p := (dist_eq_zero.mp hd).symm
            rw [this, hp_dist] at hdz_pos
            linarith
          have hx_p : ∀ i, x i ∈ branch p q ↔ i ∈ S := fun i => by
            by_cases hi : i ∈ S <;> simp [x, hi, hq_br, hy_nbr]
          exact ⟨p, hp_q, hp_ne_y, hp_ne_q, (hwin_eq_profile hp_ne_q.symm hx_p).mp hfz_br⟩ }
    refine ⟨E, funext fun x => ?_⟩
    symm
    rw [E.eval_eq_iff hT]
    intro q hq S hS hwin
    have hfx_br : f x ∈ branch (f x) q := (hwin_eq_profile hq fun i => (hS i).symm).mpr hwin
    exact (notMem_branch_self (f x) q) hfx_br
  · rintro ⟨E, rfl⟩
    exact ⟨E.eval_isStrategyProof hT, E.eval_surjective hT⟩

/-- Every deterministic, surjective, strategyproof facility-location mechanism on a finite tree
metric graph is strongly group strategyproof. This strengthens Theorem 1 of [SchummerVohra2002],
which states only individual strategyproofness; the strengthening is not stated in the source. -/
theorem isGroupStrategyProof_of_isStrategyProof_of_surjective_tree
    [Nonempty V] [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_onto : Function.Surjective f) :
    (Mechanism.deterministic f).IsGroupStrategyProof := by
  let _ := Fintype.ofFinite ι
  obtain ⟨E, rfl⟩ :=
    (isStrategyProof_and_surjective_iff_exists_treeEMVS hT f).mp ⟨hf_sp, hf_onto⟩
  exact E.eval_isGroupStrategyProof hT

end Characterization

end Cslib.GameTheory.FacilityLocation
