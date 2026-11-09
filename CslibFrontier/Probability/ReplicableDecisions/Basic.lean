/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import CslibFrontier.Probability.PMF.Event
public import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Tactic

/-!
# Binary selectors on finite graphs

Selectors, closed-neighborhood correctness and graph distance for the finite minimax problem
of [Chen2026Replicable], Section 2 and Theorem 3.2
(PDF pages 11, 13–14, printed pages 9, 11–12).
The disjoint forced sets encode nonempty acceptable subsets of `Bool`: membership in `A₀`
forces `false`, membership in `A₁` forces `true`, and every other vertex accepts both.

## Main results

* `Cslib.ReplicableDecisions.Problem.finite_profiles`: all finite-distance profile equations.
* `Cslib.ReplicableDecisions.Problem.neighborhoodProfile_eq_top`: infeasibility at distance ≤ 2.
* `Cslib.ReplicableDecisions.Problem.infinite_profiles`: all zero profiles for disconnected classes.

## Source correspondence and scope

The source is the immutable `papers-2/1425.pdf` release, Theorem 3.2, PDF pages 13–14
(printed 11–12); the selector definitions are on PDF page 11 (printed 9).
`ofAcceptableSets` uses exactly the source's singleton acceptable sets, and
`ofAcceptableSets_accepts_iff` proves equivalence for nonempty acceptable sets. `Boundary`
uses open neighbors because a vertex cannot disagree with itself; `NeighborhoodCorrect`
includes the vertex itself. One `PMF (V → Bool)` is shared by all vertices. For finite `V`,
these are precisely the source's arbitrary selector laws. `classDistance` uses Mathlib's
extended shortest-walk distance, including infinity for an empty class. Natural arithmetic
`(D + 1) / 2` is the ceiling of `D / 2`. `IsOptimum` additionally certifies attainment and
lower bounds against every admissible law; `profile` is the infimum of the worst-vertex
probabilities, with infinity for an empty feasible family.

The proofs also work on infinite graphs at finite class distance; the disconnected zero result
requires a nonempty vertex type to express an attained maximum. No BFS running time,
random-bit cost, statistical estimation or sample-complexity theorem is claimed. The finite
uniform mixtures specify semantic probability laws, without a machine realization theorem.

## References

* [Chen2026Replicable], Section 2 and Theorem 3.2.
-/

public section

open scoped ENNReal

namespace Cslib.ReplicableDecisions

variable {V : Type*}

/-- An arbitrary undirected graph and its two disjoint forced classes. -/
structure Problem (V : Type*) where
  /-- Adjacency specifies which inputs must have replicable decisions. -/
  graph : SimpleGraph V
  /-- Inputs on which correctness forces the decision `false`. -/
  forcedZero : Set V
  /-- Inputs on which correctness forces the decision `true`. -/
  forcedOne : Set V
  disjoint : Disjoint forcedZero forcedOne

namespace Problem

variable (P : Problem V)

/-- Construct the forced classes literally from the paper's acceptable sets. -/
@[expose] def ofAcceptableSets (G : SimpleGraph V) (Γ : V → Set Bool) : Problem V where
  graph := G
  forcedZero := {v | Γ v = {false}}
  forcedOne := {v | Γ v = {true}}
  disjoint := by
    rw [Set.disjoint_left]
    intro v hv0 hv1
    have heq : ({false} : Set Bool) = {true} := hv0.symm.trans hv1
    have hmem : false ∈ ({true} : Set Bool) := heq ▸ Set.mem_singleton false
    simp only [Set.mem_singleton_iff, Bool.false_eq_true] at hmem

/-- The paper's nonempty acceptable set, represented as a predicate on binary outputs. -/
@[expose] def Accepts (v : V) (b : Bool) : Prop :=
  (v ∈ P.forcedZero → b = false) ∧ (v ∈ P.forcedOne → b = true)

/-- Every nonempty binary acceptable set is represented exactly by its forced classes.
In particular, an indifference vertex accepts both labels. -/
theorem ofAcceptableSets_accepts_iff (G : SimpleGraph V) (Γ : V → Set Bool)
    (hΓ : ∀ v, (Γ v).Nonempty) (v : V) (b : Bool) :
    (ofAcceptableSets G Γ).Accepts v b ↔ b ∈ Γ v := by
  constructor
  · intro hc
    by_contra hb
    obtain ⟨c, hcΓ⟩ := hΓ v
    have heq : Γ v = {!b} := by
      ext x
      cases b <;> cases c <;> cases x <;> simp_all
    cases b with
    | false => exact Bool.false_ne_true (hc.2 heq)
    | true => exact Bool.false_ne_true (hc.1 heq).symm
  · intro hb
    constructor
    · intro hv
      change Γ v = {false} at hv
      simpa only [hv, Set.mem_singleton_iff] using hb
    · intro hv
      change Γ v = {true} at hv
      simpa only [hv, Set.mem_singleton_iff] using hb

/-- Both endpoints of every edge across which the label changes are boundary vertices. -/
@[expose] def Boundary (f : V → Bool) (v : V) : Prop :=
  ∃ w, P.graph.Adj v w ∧ f w ≠ f v

/-- A bad vertex is on the boundary or has an unacceptable output. -/
@[expose] def Bad (f : V → Bool) (v : V) : Prop :=
  P.Boundary f v ∨ ¬P.Accepts v (f v)

/-- Everywhere-correct selectors. -/
@[expose] def Correct (f : V → Bool) : Prop := ∀ v, P.Accepts v (f v)

/-- Correct at every model even when evaluated at any vertex in its closed neighborhood. -/
@[expose] def NeighborhoodCorrect (f : V → Bool) : Prop :=
  ∀ v w, (v = w ∨ P.graph.Adj v w) → P.Accepts v (f w)

/-- Multi-source extended graph distance, with infinity in components missing the source set. -/
@[expose] noncomputable def distanceFrom (A : Set V) (v : V) : ℕ∞ :=
  ⨅ a : A, P.graph.edist a v

/-- Shortest distance between forced classes; infinity also covers an empty class. -/
@[expose] noncomputable def classDistance : ℕ∞ :=
  ⨅ b : P.forcedOne, P.distanceFrom P.forcedZero b

/-- Breadth-first threshold labeling, including the value `true` at infinite distance. -/
@[expose] noncomputable def threshold (t : ℕ) (v : V) : Bool :=
  decide ((t : ℕ∞) < P.distanceFrom P.forcedZero v)

variable {P}

/-- Every vertex accepts some output; the two forced classes cannot conflict. -/
theorem accepts_nonempty (v : V) : ∃ b, P.Accepts v b := by
  classical
  by_cases h : v ∈ P.forcedZero
  · exact ⟨false, fun _ => rfl, fun h' => (Set.disjoint_left.mp P.disjoint h h').elim⟩
  · exact ⟨true, fun h' => (h h').elim, fun _ => rfl⟩

/-- Expanded correctness implies pointwise correctness because neighborhoods are closed. -/
theorem NeighborhoodCorrect.correct {f : V → Bool} (h : P.NeighborhoodCorrect f) :
    P.Correct f := fun v => h v v (Or.inl rfl)

/-- Source vertices have multi-source distance zero. -/
theorem distanceFrom_eq_zero {A : Set V} {v : V} (hv : v ∈ A) :
    P.distanceFrom A v = 0 := by
  apply le_antisymm _ zero_le
  exact (iInf_le (fun a : A => P.graph.edist a v) ⟨v, hv⟩).trans (by simp)

/-- The multi-source distance changes by at most one along an edge. -/
theorem distanceFrom_le_add_one {A : Set V} {v w : V} (h : P.graph.Adj v w) :
    P.distanceFrom A v ≤ P.distanceFrom A w + 1 := by
  simp only [distanceFrom, ENat.iInf_add]
  apply le_iInf
  intro a
  calc
    P.distanceFrom A v ≤ P.graph.edist a w + P.graph.edist w v :=
      (iInf_le _ a).trans P.graph.edist_triangle
    _ = P.graph.edist a w + 1 := by rw [SimpleGraph.edist_eq_one_iff_adj.mpr h.symm]

/-- A threshold can change only between its two neighboring breadth-first layers. -/
theorem boundary_threshold {t : ℕ} {v : V} (h : P.Boundary (P.threshold t) v) :
    P.distanceFrom P.forcedZero v = t ∨ P.distanceFrom P.forcedZero v = (t + 1 : ℕ) := by
  classical
  obtain ⟨w, hvw, hne⟩ := h
  have hvw' := P.distanceFrom_le_add_one (A := P.forcedZero) hvw
  have hwv' := P.distanceFrom_le_add_one (A := P.forcedZero) hvw.symm
  by_cases hv : P.distanceFrom P.forcedZero v ≤ t
  · have hw : (t : ℕ∞) < P.distanceFrom P.forcedZero w := by
      by_contra hh
      simp [threshold, not_lt.mpr hv, hh] at hne
    left
    obtain ⟨n, hn, hnt⟩ := ENat.le_natCast_iff.mp hv
    rw [hn] at hwv'
    have ht : (t + 1 : ℕ∞) ≤ P.distanceFrom P.forcedZero w := by
      exact (ENat.natCast_add_one_le_iff).mpr hw
    have htn : (t : ℕ) + 1 ≤ n + 1 := by exact_mod_cast ht.trans hwv'
    rw [hn]
    exact_mod_cast (by omega : n = t)
  · have hw : P.distanceFrom P.forcedZero w ≤ t := by
      by_contra hh
      simp [threshold, lt_of_not_ge hv, lt_of_not_ge hh] at hne
    right
    have hvbound : P.distanceFrom P.forcedZero v ≤ ((t + 1 : ℕ) : ℕ∞) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hvw'.trans (add_le_add hw le_rfl)
    obtain ⟨n, hn, hnt⟩ := ENat.le_natCast_iff.mp hvbound
    rw [hn] at hv
    have htn : t < n := by exact_mod_cast (lt_of_not_ge hv)
    rw [hn]
    exact_mod_cast (by omega : n = t + 1)

/-- Every threshold strictly below the class distance is everywhere correct. -/
theorem threshold_correct {t : ℕ} (ht : (t : ℕ∞) < P.classDistance) :
    P.Correct (P.threshold t) := by
  intro v
  constructor
  · intro hv
    simp [threshold, P.distanceFrom_eq_zero hv]
  · intro hv
    have hd : P.classDistance ≤ P.distanceFrom P.forcedZero v :=
      iInf_le (fun b : P.forcedOne => P.distanceFrom P.forcedZero b) ⟨v, hv⟩
    simp [threshold, ht.trans_le hd]

/-- A threshold with one full layer of slack at each forced class is neighborhood correct. -/
theorem threshold_neighborhoodCorrect {t : ℕ} (ht : 1 ≤ t)
    (hD : ((t + 1 : ℕ) : ℕ∞) < P.classDistance) :
    P.NeighborhoodCorrect (P.threshold t) := by
  intro v w hvw
  rcases hvw with rfl | hvw
  · exact P.threshold_correct (lt_of_le_of_lt (by exact_mod_cast (Nat.le_succ t)) hD) v
  constructor
  · intro hv
    have hw := P.distanceFrom_le_add_one (A := P.forcedZero) hvw.symm
    rw [P.distanceFrom_eq_zero hv, zero_add] at hw
    have : P.distanceFrom P.forcedZero w ≤ t := hw.trans (by exact_mod_cast ht)
    simp [threshold, not_lt.mpr this]
  · intro hv
    have hd : P.classDistance ≤ P.distanceFrom P.forcedZero v :=
      iInf_le (fun b : P.forcedOne => P.distanceFrom P.forcedZero b) ⟨v, hv⟩
    have hw := P.distanceFrom_le_add_one (A := P.forcedZero) hvw
    have htw : (t : ℕ∞) < P.distanceFrom P.forcedZero w := by
      by_contra hh
      have hle : P.distanceFrom P.forcedZero w ≤ t := le_of_not_gt hh
      have : P.classDistance ≤ ((t + 1 : ℕ) : ℕ∞) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hd.trans (hw.trans (add_le_add hle le_rfl))
      exact (not_le_of_gt hD) this
    simp [threshold, htw]

/-- When the opposite classes are disconnected, one constant label per component suffices. -/
theorem exists_neighborhoodCorrect_boundary_empty (hD : P.classDistance = ⊤) :
    ∃ f, P.NeighborhoodCorrect f ∧ ∀ v, ¬P.Boundary f v := by
  classical
  let f : V → Bool := fun v => decide (P.distanceFrom P.forcedZero v = ⊤)
  have hedge {v w : V} (h : P.graph.Adj v w) : f v = f w := by
    have hvw := P.distanceFrom_le_add_one (A := P.forcedZero) h
    have hwv := P.distanceFrom_le_add_one (A := P.forcedZero) h.symm
    have hi : P.distanceFrom P.forcedZero v = ⊤ ↔ P.distanceFrom P.forcedZero w = ⊤ := by
      constructor
      · intro hv
        rw [hv] at hvw
        simpa using hvw
      · intro hw
        rw [hw] at hwv
        simpa using hwv
    simp only [f, hi]
  have hc : P.Correct f := by
    intro v
    constructor
    · intro hv
      simp [f, P.distanceFrom_eq_zero hv]
    · intro hv
      have hd : P.classDistance ≤ P.distanceFrom P.forcedZero v :=
      iInf_le (fun b : P.forcedOne => P.distanceFrom P.forcedZero b) ⟨v, hv⟩
      have : P.distanceFrom P.forcedZero v = ⊤ := top_le_iff.mp (hD ▸ hd)
      simp [f, this]
  refine ⟨f, ?_, ?_⟩
  · intro v w hvw
    rcases hvw with rfl | hvw
    · exact hc v
    · rw [← hedge hvw]
      exact hc v
  · rintro v ⟨w, hvw, hne⟩
    exact hne (hedge hvw).symm

/-- A finite class distance is attained by an actual walk between forced vertices. -/
theorem exists_walk_of_classDistance {D : ℕ} (hD : P.classDistance = D) :
    ∃ (a b : V) (_ : a ∈ P.forcedZero) (_ : b ∈ P.forcedOne)
      (p : P.graph.Walk a b), p.length = D := by
  classical
  have h1 : Nonempty P.forcedOne := by
    by_contra h
    have : P.classDistance = ⊤ := by simp [classDistance, not_nonempty_iff.mp h]
    rw [hD] at this
    exact ENat.natCast_ne_top D this
  obtain ⟨b, hb⟩ := ENat.exists_eq_iInf
    (fun b : P.forcedOne => P.distanceFrom P.forcedZero b)
  have hbD : P.distanceFrom P.forcedZero b = D := hb.trans hD
  have h0 : Nonempty P.forcedZero := by
    by_contra h
    have : P.distanceFrom P.forcedZero b = ⊤ := by
      simp [distanceFrom, not_nonempty_iff.mp h]
    rw [hbD] at this
    exact ENat.natCast_ne_top D this
  obtain ⟨a, ha⟩ := ENat.exists_eq_iInf
    (fun a : P.forcedZero => P.graph.edist a b)
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_eq_coe (ha.trans hbD)
  exact ⟨a, b, a.property, b.property, p, hp⟩

/-- Disjoint forced classes have positive finite distance. -/
theorem classDistance_pos {D : ℕ} (hD : P.classDistance = D) : 0 < D := by
  obtain ⟨a, b, ha, hb, p, hp⟩ := P.exists_walk_of_classDistance hD
  by_contra h
  have hz : p.length = 0 := by omega
  have hab := SimpleGraph.Walk.eq_of_length_eq_zero hz
  exact Set.disjoint_left.mp P.disjoint ha (hab ▸ hb)

/-- A walk of at most two edges between opposite forced vertices obstructs neighborhood
correctness. This includes the closed-neighborhood endpoint constraints. -/
theorem not_neighborhoodCorrect_of_classDistance_le_two {D : ℕ}
    (hD : P.classDistance = D) (hsmall : D ≤ 2) :
    ¬ ∃ f, P.NeighborhoodCorrect f := by
  obtain ⟨a, b, ha, hb, p, hp⟩ := P.exists_walk_of_classDistance hD
  rintro ⟨f, hf⟩
  cases p with
  | nil => exact Set.disjoint_left.mp P.disjoint ha hb
  | @cons a c b hac q =>
    have hfc : f c = false := (hf a c (Or.inr hac)).1 ha
    cases q with
    | nil =>
      have hfc' := (hf b b (Or.inl rfl)).2 hb
      simp_all
    | @cons c d b hcd r =>
      have hr : r.length = 0 := by simp only [SimpleGraph.Walk.length_cons] at hp; omega
      have hdb := SimpleGraph.Walk.eq_of_length_eq_zero hr
      have hfc' := (hf b c (Or.inr (hdb ▸ hcd.symm))).2 hb
      simp_all

end Problem

private theorem exists_change {D : ℕ} (x : ℕ → V) (f : V → Bool)
    (hne : f (x 0) ≠ f (x D)) : ∃ i, i < D ∧ f (x i) ≠ f (x (i + 1)) := by
  by_contra! h
  have hall : ∀ i, i ≤ D → f (x i) = f (x 0) := by
    intro i
    induction i with
    | zero => exact fun _ => rfl
    | succ i ih =>
      intro hi
      exact (h i (by omega)).symm.trans (ih (by omega))
  exact hne (hall D le_rfl).symm

/-- Odd vertices cover every edge of a chain, for both parities of its length. -/
theorem alternating_boundary_cover (P : Problem V) {D k : ℕ}
    (hD : D ≤ 2 * k) (x : ℕ → V)
    (hadj : ∀ i, i < D → P.graph.Adj (x i) (x (i + 1)))
    (f : V → Bool) (hne : f (x 0) ≠ f (x D)) :
    ∃ j : Fin k, P.Boundary f (x (2 * j.val + 1)) := by
  obtain ⟨i, hi, hchange⟩ := exists_change x f hne
  have hj : i / 2 < k := by omega
  refine ⟨⟨i / 2, hj⟩, ?_⟩
  by_cases heven : i % 2 = 0
  · have heq : 2 * (i / 2) + 1 = i + 1 := by omega
    rw [heq]
    exact ⟨x i, (hadj i hi).symm, hchange⟩
  · have heq : 2 * (i / 2) + 1 = i := by omega
    rw [heq]
    exact ⟨x (i + 1), hadj i hi, hchange.symm⟩

/-- Endpoints together with the interior even vertices cover every bad selector on a chain
between opposite forced classes. The endpoint at an odd distance is included explicitly. -/
theorem alternating_bad_cover (P : Problem V) {D k : ℕ}
    (hD : D ≤ 2 * k) (x : ℕ → V)
    (hadj : ∀ i, i < D → P.graph.Adj (x i) (x (i + 1)))
    (hzero : x 0 ∈ P.forcedZero) (hone : x D ∈ P.forcedOne) (f : V → Bool) :
    ∃ j : Fin (k + 1), P.Bad f (x (min (2 * j.val) D)) := by
  have hlast : min (2 * k) D = D := by omega
  by_cases hz : f (x 0) = false
  · by_cases ho : f (x D) = true
    · have hne : f (x 0) ≠ f (x D) := by simp [hz, ho]
      obtain ⟨i, hi, hchange⟩ := exists_change x f hne
      by_cases heven : i % 2 = 0
      · have hj : i / 2 < k + 1 := by omega
        refine ⟨⟨i / 2, hj⟩, Or.inl ?_⟩
        have heq : min (2 * (i / 2)) D = i := by omega
        rw [heq]
        exact ⟨x (i + 1), hadj i hi, hchange.symm⟩
      · have hj : (i + 1) / 2 < k + 1 := by omega
        refine ⟨⟨(i + 1) / 2, hj⟩, Or.inl ?_⟩
        have heq : min (2 * ((i + 1) / 2)) D = i + 1 := by omega
        rw [heq]
        exact ⟨x i, (hadj i hi).symm, hchange⟩
    · refine ⟨⟨k, by omega⟩, ?_⟩
      simp only [hlast]
      exact Or.inr (fun hc => ho (hc.2 hone))
  · refine ⟨⟨0, by omega⟩, ?_⟩
    simp only [mul_zero, Nat.zero_min]
    exact Or.inr (fun hc => hz (hc.1 hzero))

/-- The probability of a selector event under one common random labeling law. -/
@[expose] noncomputable def eventProbability (μ : PMF (V → Bool))
    (E : (V → Bool) → V → Prop) (v : V) : ℝ :=
  (μ.toOuterMeasure {f | E f v}).toReal

/-- A law is admissible when every labeling in its support satisfies the constraint. -/
@[expose] def Admissible (C : (V → Bool) → Prop) (μ : PMF (V → Bool)) : Prop :=
  ∀ f ∈ μ.support, C f

/-- An attained exact optimum: one admissible law attains the uniform upper bound, and
no admissible law has a smaller worst-vertex event probability. -/
@[expose] def IsOptimum (C : (V → Bool) → Prop) (E : (V → Bool) → V → Prop)
    (r : ℝ) : Prop :=
  (∃ μ : PMF (V → Bool), Admissible C μ ∧ ∀ v, eventProbability μ E v ≤ r) ∧
    ∀ μ : PMF (V → Bool), Admissible C μ → ∃ v, r ≤ eventProbability μ E v

/-- The minimax event profile. The infimum ranges over actual probability laws satisfying
`C` on their support; the supremum ranges over all vertices. An infeasible constraint has
profile infinity. On a nonempty finite vertex type this is the paper's minimum of maxima. -/
@[expose] noncomputable def profile (C : (V → Bool) → Prop)
    (E : (V → Bool) → V → Prop) : ℝ≥0∞ :=
  ⨅ μ : {μ : PMF (V → Bool) // Admissible C μ},
    ⨆ v, ENNReal.ofReal (eventProbability μ.val E v)

/-- An attained matching upper and lower bound evaluates the minimax profile exactly. -/
theorem IsOptimum.profile_eq {C : (V → Bool) → Prop}
    {E : (V → Bool) → V → Prop} {r : ℝ} (h : IsOptimum C E r) :
    profile C E = ENNReal.ofReal r := by
  apply le_antisymm
  · obtain ⟨μ, hμ, hu⟩ := h.1
    exact iInf_le_of_le ⟨μ, hμ⟩ (iSup_le fun v => ENNReal.ofReal_le_ofReal (hu v))
  · apply le_iInf
    intro μ
    obtain ⟨v, hv⟩ := h.2 μ.val μ.property
    exact (ENNReal.ofReal_le_ofReal hv).trans
      (le_iSup (fun v : V => ENNReal.ofReal (eventProbability μ.val E v)) v)

/-- A finite cover of every supported labeling yields the alternating-cover lower bound.
Repeated vertices are allowed, so this lemma does not require a simple path. -/
theorem cover_probability_lower {n : ℕ} (hn : 0 < n) (μ : PMF (V → Bool))
    (E : (V → Bool) → V → Prop) (w : Fin n → V)
    (hcover : ∀ f ∈ μ.support, ∃ i, E f (w i)) :
    ∃ i, 1 / (n : ℝ) ≤ eventProbability μ E (w i) := by
  classical
  have hfull : μ.toOuterMeasure (⋃ i, {f | E f (w i)}) = 1 := by
    apply (μ.toOuterMeasure_apply_eq_one_iff _).mpr
    intro f hf
    obtain ⟨i, hi⟩ := hcover f hf
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have hsum : (1 : ℝ≥0∞) ≤ ∑ i, μ.toOuterMeasure {f | E f (w i)} := by
    rw [← hfull]
    simpa only [tsum_fintype] using
      (MeasureTheory.measure_iUnion_le (μ := μ.toOuterMeasure) (fun i => {f | E f (w i)}))
  have hsumR : (1 : ℝ) ≤ ∑ i, eventProbability μ E (w i) := by
    have := ENNReal.toReal_mono
      (ENNReal.sum_ne_top.mpr fun i _ => Probability.PMF.toOuterMeasure_ne_top μ _) hsum
    simpa only [eventProbability, ENNReal.toReal_one,
      ENNReal.toReal_sum (fun i _ => Probability.PMF.toOuterMeasure_ne_top μ _)] using this
  by_contra! h
  have hlt : (∑ i, eventProbability μ E (w i)) < ∑ _i : Fin n, 1 / (n : ℝ) :=
    Finset.sum_lt_sum_of_nonempty ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i _ => h i)
  have hcount : (∑ _i : Fin n, 1 / (n : ℝ)) = 1 := by
    simp [hn.ne']
  linarith

/-- Uniformly choose one of the listed deterministic selectors, using the same choice at
all vertices. This is the semantic law of the finite threshold sampler. -/
@[expose] noncomputable def uniformMixture {n : ℕ} (hn : 0 < n)
    (f : Fin n → V → Bool) : PMF (V → Bool) :=
  letI : NeZero n := ⟨hn.ne'⟩
  (Probability.PMF.uniformOfFintype (Fin n)).map f

/-- Every supported selector of a uniform mixture is one of its listed selectors. -/
theorem admissible_uniformMixture {n : ℕ} (hn : 0 < n)
    (f : Fin n → V → Bool) (C : (V → Bool) → Prop) (hC : ∀ i, C (f i)) :
    Admissible C (uniformMixture hn f) := by
  intro g hg
  obtain ⟨i, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hg
  exact hC i

/-- Pairwise disjoint event sets in a uniform list give event probability at most `1/n`. -/
theorem uniformMixture_probability_le {n : ℕ} (hn : 0 < n)
    (f : Fin n → V → Bool) (E : (V → Bool) → V → Prop)
    (hdis : ∀ v i j, E (f i) v → E (f j) v → i = j) (v : V) :
    eventProbability (uniformMixture hn f) E v ≤ 1 / (n : ℝ) := by
  classical
  have : NeZero n := ⟨hn.ne'⟩
  have hc : (Finset.univ.filter (fun i => E (f i) v)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact hdis v i j (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  simp only [eventProbability, uniformMixture, PMF.toOuterMeasure_map_apply]
  rw [Probability.PMF.toOuterMeasure_uniformOfFintype_toReal]
  simp only [Fintype.card_fin]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)

namespace Problem

variable (P : Problem V)

/-- The exact everywhere-correct lower bound applies to every common random labeling law. -/
theorem correct_lower {D : ℕ} (hD : P.classDistance = D) (μ : PMF (V → Bool))
    (hμ : Admissible P.Correct μ) :
    ∃ v, 1 / (((D + 1) / 2 : ℕ) : ℝ) ≤ eventProbability μ P.Boundary v := by
  let k := (D + 1) / 2
  have hk : 0 < k := by have := P.classDistance_pos hD; dsimp [k]; omega
  obtain ⟨a, b, ha, hb, p, hp⟩ := P.exists_walk_of_classDistance hD
  have h0 : p.getVert 0 = a := p.getVert_zero
  have hlast : p.getVert D = b := by rw [← hp]; exact p.getVert_length
  have hadj : ∀ i, i < D → P.graph.Adj (p.getVert i) (p.getVert (i + 1)) :=
    fun i hi => p.adj_getVert_succ (hp ▸ hi)
  obtain ⟨j, hj⟩ := cover_probability_lower hk μ P.Boundary
    (fun j : Fin k => p.getVert (2 * j.val + 1)) (by
      intro f hf
      have hcorrect := hμ f hf
      have hz := (hcorrect a).1 ha
      have ho := (hcorrect b).2 hb
      exact alternating_boundary_cover P (by dsimp [k]; omega) p.getVert hadj f
        (by simpa only [h0, hlast, hz, ho] using Bool.false_ne_true))
  exact ⟨_, hj⟩

/-- The exact joint-defect lower bound, with no correctness restriction on the law. -/
theorem joint_lower {D : ℕ} (hD : P.classDistance = D) (μ : PMF (V → Bool)) :
    ∃ v, 1 / ((((D + 1) / 2 + 1 : ℕ)) : ℝ) ≤ eventProbability μ P.Bad v := by
  let k := (D + 1) / 2
  obtain ⟨a, b, ha, hb, p, hp⟩ := P.exists_walk_of_classDistance hD
  obtain ⟨j, hj⟩ := cover_probability_lower (Nat.zero_lt_succ k) μ P.Bad
    (fun j : Fin (k + 1) => p.getVert (min (2 * j.val) D)) (by
      intro f _
      apply alternating_bad_cover P (by dsimp [k]; omega) p.getVert
        (fun i hi => p.adj_getVert_succ (hp ▸ hi)) _ _ f
      · simpa only [p.getVert_zero] using ha
      · simpa only [← hp, p.getVert_length] using hb)
  exact ⟨_, hj⟩

/-- The exact lower bound under neighborhood correctness uses the interior chain, whose
endpoints are forced by the closed neighborhoods of the original endpoints. -/
theorem neighborhood_lower {D : ℕ} (hD : P.classDistance = D) (hlarge : 3 ≤ D)
    (μ : PMF (V → Bool)) (hμ : Admissible P.NeighborhoodCorrect μ) :
    ∃ v, 1 / ((((D + 1) / 2 - 1 : ℕ)) : ℝ) ≤ eventProbability μ P.Boundary v := by
  let k := (D + 1) / 2 - 1
  have hk : 0 < k := by dsimp [k]; omega
  obtain ⟨a, b, ha, hb, p, hp⟩ := P.exists_walk_of_classDistance hD
  have h0 : p.getVert 0 = a := p.getVert_zero
  have hlast : p.getVert D = b := by rw [← hp]; exact p.getVert_length
  have hadj : ∀ i, i < D → P.graph.Adj (p.getVert i) (p.getVert (i + 1)) :=
    fun i hi => p.adj_getVert_succ (hp ▸ hi)
  obtain ⟨j, hj⟩ := cover_probability_lower hk μ P.Boundary
    (fun j : Fin k => p.getVert (2 * j.val + 1 + 1)) (by
      intro f hf
      have hc := hμ f hf
      have hz : f (p.getVert 1) = false :=
        (hc a (p.getVert 1) (Or.inr (by simpa only [h0, zero_add] using hadj 0 (by omega)))).1 ha
      have ho : f (p.getVert (D - 1)) = true := by
        have hedge := hadj (D - 1) (by omega)
        rw [show D - 1 + 1 = D by omega, hlast] at hedge
        exact (hc b (p.getVert (D - 1)) (Or.inr hedge.symm)).2 hb
      have hcvr := alternating_boundary_cover P (D := D - 2) (k := k)
        (by dsimp [k]; omega) (fun i => p.getVert (i + 1))
        (fun i hi => hadj (i + 1) (by omega)) f
        (by simpa only [zero_add, show D - 2 + 1 = D - 1 by omega, hz, ho]
          using Bool.false_ne_true)
      exact hcvr)
  exact ⟨_, hj⟩

/-- The even breadth-first thresholds attain the everywhere-correct upper bound. -/
theorem correct_upper {D : ℕ} (hD : P.classDistance = D) :
    ∃ μ : PMF (V → Bool), Admissible P.Correct μ ∧
      ∀ v, eventProbability μ P.Boundary v ≤ 1 / (((D + 1) / 2 : ℕ) : ℝ) := by
  let k := (D + 1) / 2
  have hk : 0 < k := by have := P.classDistance_pos hD; dsimp [k]; omega
  let f : Fin k → V → Bool := fun i => P.threshold (2 * i.val)
  refine ⟨uniformMixture hk f, admissible_uniformMixture hk f P.Correct ?_, ?_⟩
  · intro i
    apply P.threshold_correct
    rw [hD]
    exact_mod_cast (show 2 * i.val < D by have := i.isLt; dsimp [k] at *; omega)
  · apply uniformMixture_probability_le hk f P.Boundary
    intro v i j hi hj
    have hi' := P.boundary_threshold hi
    have hj' := P.boundary_threshold hj
    apply Fin.ext
    rcases hi' with hi' | hi' <;> rcases hj' with hj' | hj'
    all_goals
      have heq := hi'.symm.trans hj'
      have heq' := ENat.natCast_inj.mp heq
      omega

/-- The interior odd thresholds attain the neighborhood-correct upper bound. -/
theorem neighborhood_upper {D : ℕ} (hD : P.classDistance = D) (hlarge : 3 ≤ D) :
    ∃ μ : PMF (V → Bool), Admissible P.NeighborhoodCorrect μ ∧
      ∀ v, eventProbability μ P.Boundary v ≤ 1 / (((D + 1) / 2 - 1 : ℕ) : ℝ) := by
  let k := (D + 1) / 2 - 1
  have hk : 0 < k := by dsimp [k]; omega
  let f : Fin k → V → Bool := fun i => P.threshold (2 * i.val + 1)
  refine ⟨uniformMixture hk f,
    admissible_uniformMixture hk f P.NeighborhoodCorrect ?_, ?_⟩
  · intro i
    apply P.threshold_neighborhoodCorrect (by omega)
    rw [hD]
    exact_mod_cast (show 2 * i.val + 1 + 1 < D by
      have := i.isLt; dsimp [k] at *; omega)
  · apply uniformMixture_probability_le hk f P.Boundary
    intro v i j hi hj
    have hi' := P.boundary_threshold hi
    have hj' := P.boundary_threshold hj
    apply Fin.ext
    rcases hi' with hi' | hi' <;> rcases hj' with hj' | hj'
    all_goals
      have heq := hi'.symm.trans hj'
      have heq' := ENat.natCast_inj.mp heq
      omega

variable {P} in
/-- Neighborhood correctness prevents boundary at either forced class. -/
theorem NeighborhoodCorrect.not_boundary_of_forced {f : V → Bool}
    (hc : P.NeighborhoodCorrect f) {v : V}
    (hv : v ∈ P.forcedZero ∨ v ∈ P.forcedOne) : ¬P.Boundary f v := by
  rintro ⟨w, hadj, hne⟩
  have hself := hc v v (Or.inl rfl)
  have hneighbor := hc v w (Or.inr hadj)
  rcases hv with hv | hv
  · exact hne ((hneighbor.1 hv).trans (hself.1 hv).symm)
  · exact hne ((hneighbor.2 hv).trans (hself.2 hv).symm)

/-- The constant-zero selector is bad exactly at forced-one vertices. -/
@[simp] theorem bad_const_false (v : V) : P.Bad (fun _ => false) v ↔ v ∈ P.forcedOne := by
  simp [Bad, Boundary, Accepts]

/-- The constant-one selector is bad exactly at forced-zero vertices. -/
@[simp] theorem bad_const_true (v : V) : P.Bad (fun _ => true) v ↔ v ∈ P.forcedZero := by
  simp [Bad, Boundary, Accepts]

variable {P} in
/-- For a correct selector the joint bad set equals its boundary. -/
theorem Correct.bad_iff_boundary {f : V → Bool} (hc : P.Correct f) (v : V) :
    P.Bad f v ↔ P.Boundary f v :=
  ⟨fun h => h.elim id (fun hn => (hn (hc v)).elim), Or.inl⟩

/-- The two constants together with the interior odd thresholds attain the joint upper bound. -/
theorem joint_upper {D : ℕ} (hD : P.classDistance = D) :
    ∃ μ : PMF (V → Bool), ∀ v,
      eventProbability μ P.Bad v ≤ 1 / (((D + 1) / 2 + 1 : ℕ) : ℝ) := by
  let k := (D + 1) / 2
  let f : Fin (k + 1) → V → Bool := fun i =>
    if i.val = 0 then fun _ => false else
      if i.val = 1 then fun _ => true else P.threshold (2 * (i.val - 2) + 1)
  have hnc (i : Fin (k + 1)) (hi : 2 ≤ i.val) :
      P.NeighborhoodCorrect (P.threshold (2 * (i.val - 2) + 1)) := by
    apply P.threshold_neighborhoodCorrect (by omega)
    rw [hD]
    exact_mod_cast (show 2 * (i.val - 2) + 1 + 1 < D by
      have := i.isLt; dsimp [k] at *; omega)
  have hbad (i : Fin (k + 1)) (hi : 2 ≤ i.val) {v : V} (hb : P.Bad (f i) v) :
      P.Boundary (P.threshold (2 * (i.val - 2) + 1)) v := by
    have hf : f i = P.threshold (2 * (i.val - 2) + 1) := by
      simp only [f, ite_eq_right (show i.val ≠ 0 by omega), ite_eq_right (show i.val ≠ 1 by omega)]
    rw [hf] at hb
    exact ((hnc i hi).correct.bad_iff_boundary v).mp hb
  refine ⟨uniformMixture (Nat.zero_lt_succ k) f,
    uniformMixture_probability_le (Nat.zero_lt_succ k) f P.Bad ?_⟩
  intro v i j hi hj
  by_cases hi0 : i.val = 0
  · have hv1 : v ∈ P.forcedOne := by simpa only [f, ite_eq_left hi0, bad_const_false] using hi
    by_cases hj0 : j.val = 0
    · exact Fin.ext (hi0.trans hj0.symm)
    · by_cases hj1 : j.val = 1
      · have hv0 : v ∈ P.forcedZero := by
          simpa only [f, ite_eq_right hj0, ite_eq_left hj1, bad_const_true] using hj
        exact (Set.disjoint_left.mp P.disjoint hv0 hv1).elim
      · exact ((hnc j (by omega)).not_boundary_of_forced (Or.inr hv1)
          (hbad j (by omega) hj)).elim
  · by_cases hi1 : i.val = 1
    · have hv0 : v ∈ P.forcedZero := by
        simpa only [f, ite_eq_right hi0, ite_eq_left hi1, bad_const_true] using hi
      by_cases hj0 : j.val = 0
      · have hv1 : v ∈ P.forcedOne := by
          simpa only [f, ite_eq_left hj0, bad_const_false] using hj
        exact (Set.disjoint_left.mp P.disjoint hv0 hv1).elim
      · by_cases hj1 : j.val = 1
        · exact Fin.ext (hi1.trans hj1.symm)
        · exact ((hnc j (by omega)).not_boundary_of_forced (Or.inl hv0)
            (hbad j (by omega) hj)).elim
    · have hib := hbad i (by omega) hi
      by_cases hj0 : j.val = 0
      · have hv1 : v ∈ P.forcedOne := by
          simpa only [f, ite_eq_left hj0, bad_const_false] using hj
        exact ((hnc i (by omega)).not_boundary_of_forced (Or.inr hv1) hib).elim
      · by_cases hj1 : j.val = 1
        · have hv0 : v ∈ P.forcedZero := by
            simpa only [f, ite_eq_right hj0, ite_eq_left hj1, bad_const_true] using hj
          exact ((hnc i (by omega)).not_boundary_of_forced (Or.inl hv0) hib).elim
        · have hjb := hbad j (by omega) hj
          have hi' := P.boundary_threshold hib
          have hj' := P.boundary_threshold hjb
          apply Fin.ext
          rcases hi' with hi' | hi' <;> rcases hj' with hj' | hj'
          all_goals
            have heq' := ENat.natCast_inj.mp (hi'.symm.trans hj')
            omega

/-- Theorem 3.2: the exact joint defect is `1/(ceil(D/2)+1)`. The attained law is a
uniform mixture of the two constants and the interior odd breadth-first thresholds. -/
theorem joint_optimum {D : ℕ} (hD : P.classDistance = D) :
    IsOptimum (fun _ => True) P.Bad (1 / (((D + 1) / 2 + 1 : ℕ) : ℝ)) := by
  obtain ⟨μ, hμ⟩ := P.joint_upper hD
  exact ⟨⟨μ, fun _ _ => trivial, hμ⟩, fun ν _ => P.joint_lower hD ν⟩

/-- Theorem 3.2: the exact boundary optimum over everywhere-correct laws is `1/ceil(D/2)`.
The attained law uniformly mixes the even breadth-first thresholds. -/
theorem correct_optimum {D : ℕ} (hD : P.classDistance = D) :
    IsOptimum P.Correct P.Boundary (1 / (((D + 1) / 2 : ℕ) : ℝ)) :=
  ⟨P.correct_upper hD, fun μ hμ => P.correct_lower hD μ hμ⟩

/-- Theorem 3.2: for `D ≥ 3`, the exact neighborhood-correct optimum is `1/(ceil(D/2)-1)`.
The attained law uniformly mixes the interior odd breadth-first thresholds. -/
theorem neighborhood_optimum {D : ℕ} (hD : P.classDistance = D) (hlarge : 3 ≤ D) :
    IsOptimum P.NeighborhoodCorrect P.Boundary (1 / (((D + 1) / 2 - 1 : ℕ) : ℝ)) :=
  ⟨P.neighborhood_upper hD hlarge, fun μ hμ => P.neighborhood_lower hD hlarge μ hμ⟩

/-- A boundary-free neighborhood-correct selector gives all three zero optima, including
when one forced class is empty. A nonempty vertex type makes the maximum well-defined. -/
theorem disconnected_optima [Nonempty V] (hD : P.classDistance = ⊤) :
    IsOptimum (fun _ => True) P.Bad 0 ∧
      IsOptimum P.Correct P.Boundary 0 ∧
      IsOptimum P.NeighborhoodCorrect P.Boundary 0 := by
  obtain ⟨f, hnc, hboundary⟩ := P.exists_neighborhoodCorrect_boundary_empty hD
  have hbad : ∀ v, ¬P.Bad f v := by
    intro v h
    exact h.elim (hboundary v) (fun hn => hn (hnc.correct v))
  have hzero (E : (V → Bool) → V → Prop) (he : ∀ v, ¬E f v) :
      ∀ v, eventProbability (PMF.pure f) E v = 0 := by
    intro v
    simp [eventProbability, PMF.toOuterMeasure_pure_apply, he v]
  have hopt (C : (V → Bool) → Prop) (hc : C f) (E : (V → Bool) → V → Prop)
      (he : ∀ v, ¬E f v) : IsOptimum C E 0 := by
    refine ⟨⟨PMF.pure f, ?_, fun v => (hzero E he v).le⟩, ?_⟩
    · intro g hg
      have : g = f := (PMF.mem_support_pure_iff _ _).mp hg
      exact this ▸ hc
    · intro μ _
      exact ⟨Classical.choice inferInstance, ENNReal.toReal_nonneg⟩
  exact ⟨hopt _ trivial _ hbad, hopt _ hnc.correct _ hboundary, hopt _ hnc _ hboundary⟩

/-- The joint profile `Φ` from Section 2 of the source. -/
@[expose] noncomputable def jointProfile : ℝ≥0∞ := profile (fun _ => True) P.Bad

/-- The everywhere-correct boundary profile `Ψ` from Section 2 of the source. -/
@[expose] noncomputable def correctProfile : ℝ≥0∞ := profile P.Correct P.Boundary

/-- The neighborhood-correct boundary profile `Λ`, with infinity for infeasibility. -/
@[expose] noncomputable def neighborhoodProfile : ℝ≥0∞ :=
  profile P.NeighborhoodCorrect P.Boundary

/-- The complete finite-distance minimax profile equations of Theorem 3.2. -/
theorem finite_profiles {D : ℕ} (hD : P.classDistance = D) :
    P.jointProfile = ENNReal.ofReal (1 / (((D + 1) / 2 + 1 : ℕ) : ℝ)) ∧
      P.correctProfile = ENNReal.ofReal (1 / (((D + 1) / 2 : ℕ) : ℝ)) ∧
      (3 ≤ D → P.neighborhoodProfile =
        ENNReal.ofReal (1 / (((D + 1) / 2 - 1 : ℕ) : ℝ))) :=
  ⟨(P.joint_optimum hD).profile_eq, (P.correct_optimum hD).profile_eq,
    fun hlarge => (P.neighborhood_optimum hD hlarge).profile_eq⟩

/-- The infeasible branch of Theorem 3.2 has profile infinity and no admissible random law. -/
theorem neighborhoodProfile_eq_top {D : ℕ} (hD : P.classDistance = D) (hsmall : D ≤ 2) :
    P.neighborhoodProfile = ⊤ := by
  have he : IsEmpty {μ : PMF (V → Bool) // Admissible P.NeighborhoodCorrect μ} := by
    refine ⟨fun μ => ?_⟩
    obtain ⟨f, hf⟩ := μ.val.support_nonempty
    exact P.not_neighborhoodCorrect_of_classDistance_le_two hD hsmall
      ⟨f, μ.property f hf⟩
  simp only [neighborhoodProfile, profile, iInf_of_isEmpty, sInf_empty]

/-- The disconnected branch of Theorem 3.2, including empty forced classes. -/
theorem infinite_profiles [Nonempty V] (hD : P.classDistance = ⊤) :
    P.jointProfile = 0 ∧ P.correctProfile = 0 ∧ P.neighborhoodProfile = 0 := by
  obtain ⟨hj, hc, hn⟩ := P.disconnected_optima hD
  exact ⟨by simpa only [ENNReal.ofReal_zero, jointProfile] using hj.profile_eq,
    by simpa only [ENNReal.ofReal_zero, correctProfile] using hc.profile_eq,
    by simpa only [ENNReal.ofReal_zero, neighborhoodProfile] using hn.profile_eq⟩

end Problem
end Cslib.ReplicableDecisions
