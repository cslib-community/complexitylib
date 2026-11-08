/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.Edge.Walk
public import Complexity.Foundations.Relation.Acyclic

/-!
# Timestamped incidence DAGs for edge CSPs

This is Definition 32 of [KazdaKolmogorovRolinek2018], arXiv:1602.03124v6,
printed pp. 15–16. Constraint nodes are original **positions** paired with timestamps;
relation symbols never identify nodes. Arcs retain actual ordered occurrences.
Separate finite node supports retain isolated variables, including forest roots.

`DAG.IsFDAG` contains all six conditions of the definition. Actual incidence is built into
`DAG.Arc`; `supported` checks its endpoints. `unique` prohibits reuse of an original incidence
at any orientation or time. `indegree` bounds variable indegree. `ordered` requires distinct
constraint timestamps and a compatible finite topological numbering. Numberings may tie at
unrelated nodes: on the finite support these ties can be broken to obtain the source's total
order. Conversely a finite total order can be numbered. `orderRelation` explicitly adds the
timestamp comparisons, and `ordered_iff_acyclic` relates the numbering to the existing acyclic
relation API. Local feasibility and the full same-original-constraint no-shortcut condition
are `feasible` and `noShortcut`.

Condition 5 flips two singleton coordinates successively. Equal ports therefore cancel, as
in the paper; they do not become a one-coordinate set flip. Since the base labeling is valid
and both ports belong to the same constraint, global validity of this move is equivalent to
feasibility of that constraint's tuple.

## Main results

* `DAG.IsFDAG.subgraph`: Observation 33, including isolated nodes.
* `DAG.IsFDAG.acyclic`: the directed incidence graph is acyclic.
* `DAG.Ordered.exists_injective_numbering`: a checked finite tie-breaking justification of
  the source's total-order formulation, including isolated nodes.

No construction of Algorithm 1's forest, improving comparison labeling, or solver is assumed.
-/

public section

namespace Cslib.Logic.PL.CSP

open BitString Finset

variable {Rel V : Type*} {F : CSP Rel V}

namespace DAG

/-- An original constraint position paired with its copy's timestamp. -/
abbrev Copy (F : CSP Rel V) := Fin F.length × ℕ

/-- Variable nodes and timestamped copies of positional constraints. -/
abbrev Node (F : CSP Rel V) := V ⊕ Copy F

/-- An indexed incidence, its timestamp, and its orientation (`true` means variable to copy). -/
structure Arc (F : CSP Rel V) where
  /-- Original constraint and ordered argument position of this incidence. -/
  occurrence : Occurrence F
  /-- Timestamp identifying the copied constraint endpoint. -/
  time : ℕ
  /-- `true` orients the incidence from its variable toward its constraint copy. -/
  incoming : Bool

instance : DecidableEq (Arc F) := fun ⟨o, t, i⟩ ⟨p, s, j⟩ =>
  decidable_of_iff (o = p ∧ t = s ∧ i = j) (by simp only [Arc.mk.injEq])

namespace Arc

/-- The constraint-copy endpoint of an arc. -/
@[expose] def copy (a : Arc F) : Copy F := (a.occurrence.1, a.time)

/-- Source node of an oriented incidence. -/
@[expose] def source (a : Arc F) : Node F :=
  if a.incoming then .inl a.occurrence.var else .inr a.copy

/-- Target node of an oriented incidence. -/
@[expose] def target (a : Arc F) : Node F :=
  if a.incoming then .inr a.copy else .inl a.occurrence.var

end Arc

/-- Two individual flips, with cancellation when the occurrences are equal. -/
@[expose] def pairFlip (f : OccurrenceLabeling F Bool) (o p : Occurrence F) :
    OccurrenceLabeling F Bool := flipOn {p} (flipOn {o} f)

@[simp] theorem pairFlip_self (f : OccurrenceLabeling F Bool) (o : Occurrence F) :
    pairFlip f o o = f := by
  simp [pairFlip]

/-- For distinct occurrences the cancelling pair operation is the usual set flip. -/
theorem pairFlip_eq (f : OccurrenceLabeling F Bool) {o p : Occurrence F} (h : o ≠ p) :
    pairFlip f o p = flipOn {o, p} f := by
  funext q
  by_cases ho : q = o <;> by_cases hp : q = p <;> simp_all [pairFlip, flipOn_apply]

end DAG

/-- A finite directed incidence graph with explicit support for isolated nodes. -/
structure DAG (F : CSP Rel V) where
  /-- Supported actual variables, retaining isolated roots. -/
  vars : Finset V
  /-- Supported positional constraint copies, retaining isolated copies. -/
  copies : Finset (DAG.Copy F)
  /-- Used original incidences with their timestamps and orientations. -/
  arcs : Finset (DAG.Arc F)

namespace DAG

/-- All explicitly supported nodes, including isolated roots and constraint copies. -/
@[expose] def nodes (T : DAG F) : Finset (Node F) :=
  T.vars.disjSum T.copies

/-- The directed incidence relation, without the auxiliary timestamp comparisons. -/
@[expose] def edge (T : DAG F) (x y : Node F) : Prop :=
  ∃ a ∈ T.arcs, a.source = x ∧ a.target = y

/-- Arcs together with all forward timestamp comparisons between supported constraint copies. -/
@[expose] def orderRelation (T : DAG F) (x y : Node F) : Prop :=
  T.edge x y ∨ ∃ c ∈ T.copies, ∃ d ∈ T.copies,
    c.2 < d.2 ∧ x = .inr c ∧ y = .inr d

/-- Every arc has its actual variable and copy in the declared node supports. -/
@[expose] def Supported (T : DAG F) : Prop :=
  ∀ a ∈ T.arcs, a.occurrence.var ∈ T.vars ∧ a.copy ∈ T.copies

/-- Timestamp-compatible topological order, encoded by a finite rank witness. -/
@[expose] def Ordered (T : DAG F) : Prop :=
  (∀ c ∈ T.copies, ∀ d ∈ T.copies, c.2 = d.2 → c = d) ∧
  ∃ rank : Node F → ℕ, ∀ x y, T.orderRelation x y → rank x < rank y

/-- All six invariant conditions in KKR Definition 32, with base validity explicit. -/
structure IsFDAG (sem : Rel → List Bool → Bool) (f : OccurrenceLabeling F Bool)
    (T : DAG F) : Prop where
  /-- The reference labeling satisfies every original positional constraint. -/
  valid : ValidLabeling sem f
  /-- Condition 1: every indexed arc has both endpoints in the support. -/
  supported : T.Supported
  /-- Condition 2: an original incidence is used at most once, in one orientation and copy. -/
  unique : ∀ a ∈ T.arcs, ∀ b ∈ T.arcs, a.occurrence = b.occurrence → a = b
  /-- Condition 3: a variable has at most one incoming arc. -/
  indegree : ∀ a ∈ T.arcs, ∀ b ∈ T.arcs,
    a.incoming = false → b.incoming = false → a.occurrence.var = b.occurrence.var → a = b
  /-- Condition 4: timestamps are globally distinct and extend to a topological order. -/
  ordered : T.Ordered
  /-- Condition 5: an incoming port exchanges feasibly with any port at its copy. -/
  feasible : ∀ a ∈ T.arcs, ∀ b ∈ T.arcs,
    a.incoming = true → a.copy = b.copy → ValidLabeling sem (pairFlip f a.occurrence b.occurrence)
  /-- Condition 6: an old incoming port cannot exchange with a later-used port of the same
  original constraint. -/
  noShortcut : ∀ a ∈ T.arcs, ∀ b ∈ T.arcs, a.incoming = true →
    a.occurrence.1 = b.occurrence.1 → a.time < b.time →
    ¬ ValidLabeling sem (pairFlip f a.occurrence b.occurrence)

/-- Subgraph inclusion permits deletion of isolated nodes as well as arcs. -/
@[expose] def Subgraph (S T : DAG F) : Prop :=
  S.vars ⊆ T.vars ∧ S.copies ⊆ T.copies ∧ S.arcs ⊆ T.arcs

/-- Observation 33: every supported subgraph inherits all six conditions. -/
theorem IsFDAG.subgraph {sem : Rel → List Bool → Bool} {f : OccurrenceLabeling F Bool}
    {S T : DAG F} (h : T.IsFDAG sem f) (hst : S.Subgraph T) (hs : S.Supported) :
    S.IsFDAG sem f where
  valid := h.valid
  supported := hs
  unique a ha b hb := h.unique a (hst.2.2 ha) b (hst.2.2 hb)
  indegree a ha b hb := h.indegree a (hst.2.2 ha) b (hst.2.2 hb)
  ordered := ⟨fun c hc d hd => h.ordered.1 c (hst.2.1 hc) d (hst.2.1 hd), by
    obtain ⟨rank, hr⟩ := h.ordered.2
    refine ⟨rank, fun x y hxy => hr x y ?_⟩
    rcases hxy with ⟨a, ha, hx, hy⟩ | ⟨c, hc, d, hd, hcd, hx, hy⟩
    · exact Or.inl ⟨a, hst.2.2 ha, hx, hy⟩
    · exact Or.inr ⟨c, hst.2.1 hc, d, hst.2.1 hd, hcd, hx, hy⟩⟩
  feasible a ha b hb := h.feasible a (hst.2.2 ha) b (hst.2.2 hb)
  noShortcut a ha b hb := h.noShortcut a (hst.2.2 ha) b (hst.2.2 hb)

section Restrict

variable [DecidableEq V]

/-- Restrict to selected variable and copy supports, retaining precisely the arcs between them. -/
@[expose] def restrict (T : DAG F) (vs : Finset V) (cs : Finset (Copy F)) : DAG F where
  vars := T.vars ∩ vs
  copies := T.copies ∩ cs
  arcs := T.arcs.filter fun a => a.occurrence.var ∈ vs ∧ a.copy ∈ cs

/-- Restriction deletes nodes and arcs. -/
theorem restrict_subgraph (T : DAG F) (vs : Finset V) (cs : Finset (Copy F)) :
    (T.restrict vs cs).Subgraph T :=
  ⟨inter_subset_left, inter_subset_left, filter_subset _ _⟩

/-- Restriction retains the endpoint-support condition. -/
theorem Supported.restrict {T : DAG F} (h : T.Supported)
    (vs : Finset V) (cs : Finset (Copy F)) : (T.restrict vs cs).Supported := by
  intro a ha
  obtain ⟨ha, hv, hc⟩ := mem_filter.mp ha
  exact ⟨mem_inter.mpr ⟨(h a ha).1, hv⟩, mem_inter.mpr ⟨(h a ha).2, hc⟩⟩

/-- Observation 33 specialized to an executable induced restriction. -/
theorem IsFDAG.restrict {sem : Rel → List Bool → Bool} {f : OccurrenceLabeling F Bool}
    {T : DAG F} (h : T.IsFDAG sem f) (vs : Finset V) (cs : Finset (Copy F)) :
    (T.restrict vs cs).IsFDAG sem f :=
  h.subgraph (T.restrict_subgraph vs cs) (h.supported.restrict vs cs)

end Restrict

/-- The empty graph (with no nodes) is an f-DAG for every valid labeling. -/
theorem isFDAG_empty {sem : Rel → List Bool → Bool} {f : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) : (⟨∅, ∅, ∅⟩ : DAG F).IsFDAG sem f where
  valid := hf
  supported := by simp [Supported]
  unique := by simp
  indegree := by simp
  ordered := ⟨by simp, ⟨fun _ => 0, by simp [orderRelation, edge]⟩⟩
  feasible := by simp
  noShortcut := by simp

/-- A compatible rank excludes all directed cycles. -/
theorem IsFDAG.acyclic {sem : Rel → List Bool → Bool} {f : OccurrenceLabeling F Bool}
    {T : DAG F} (h : T.IsFDAG sem f) : Relation.Acyclic T.edge := by
  obtain ⟨rank, hr⟩ := h.ordered.2
  exact Relation.acyclic_of_rank fun x y hxy => hr x y (Or.inl hxy)

/-- Supported arcs and timestamp comparisons remain inside the finite node support. -/
theorem Supported.orderRelation {T : DAG F} (h : T.Supported) {x y : Node F}
    (hxy : T.orderRelation x y) : x ∈ T.nodes ∧ y ∈ T.nodes := by
  rcases hxy with ⟨a, ha, rfl, rfl⟩ | ⟨c, hc, d, hd, _, rfl, rfl⟩
  · obtain ⟨hv, hc⟩ := h a ha
    cases hi : a.incoming <;> simp [nodes, Arc.source, Arc.target, hi, hv, hc]
  · simp [nodes, hc, hd]

/-- The rank formulation is equivalent to acyclicity after adding the timestamp order.
This uses the existing finite topological-numbering theorem rather than a separate DAG API. -/
theorem ordered_iff_acyclic {T : DAG F} (h : T.Supported) : T.Ordered ↔
    (∀ c ∈ T.copies, ∀ d ∈ T.copies, c.2 = d.2 → c = d) ∧
      Relation.Acyclic T.orderRelation := by
  constructor
  · rintro ⟨ht, rank, hr⟩
    exact ⟨ht, Relation.acyclic_of_rank hr⟩
  · rintro ⟨ht, ha⟩
    obtain ⟨rank, _, hr⟩ := ha.exists_rank T.nodes (fun _ _ => h.orderRelation)
    exact ⟨ht, rank, hr⟩

/-- Break rank ties on the finite support without changing any required strict comparison.
The resulting injective natural numbering induces the source's strict total order on supported
nodes. This also accounts for isolated nodes, whose original ranks may all have been equal. -/
theorem Ordered.exists_injective_numbering {T : DAG F} (h : T.Ordered) :
    ∃ number : {x : Node F // x ∈ T.nodes} ↪ ℕ,
      ∀ x y, T.orderRelation x.val y.val → number x < number y := by
  classical
  obtain ⟨rank, hr⟩ := h.2
  let S := {x : Node F // x ∈ T.nodes}
  let enum := Fintype.equivFin S
  let width := Fintype.card S + 1
  let number : S → ℕ := fun x => rank x.val * width + (enum x).val
  have hen : ∀ x, (enum x).val < width := fun x =>
    Nat.lt_trans (enum x).isLt (Nat.lt_succ_self _)
  have hinj : Function.Injective number := by
    intro x y he
    have hm := congrArg (fun n => n % width) he
    have hmod : ∀ z, number z % width = (enum z).val := by
      intro z
      simp [number, Nat.add_mod, Nat.mod_eq_of_lt (hen z)]
    rw [hmod, hmod] at hm
    exact enum.injective (Fin.ext hm)
  refine ⟨⟨number, hinj⟩, ?_⟩
  intro x y hxy
  have hlt := hr x.val y.val hxy
  have hmul := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hlt)
  have hx := hen x
  change rank x.val * width + (enum x).val < rank y.val * width + (enum y).val
  rw [Nat.succ_mul] at hmul
  omega

end DAG

end Cslib.Logic.PL.CSP
