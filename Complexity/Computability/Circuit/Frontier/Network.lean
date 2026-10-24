/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.BranchingProgram
public import Complexity.Computability.Circuit.Frontier.Multigraph
import Complexity.Foundations.Data.Nat.IntermediateValue
import Complexity.Foundations.Data.Set.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Constraint networks and their branching programs

A *constraint network* is a multigraph whose edges carry values in an alphabet `U` and whose
vertices impose *local constraints*: the constraint at `v` sees only the values on the edges at
`v` and the inputs read at `v`. Each input is read at no more than one vertex. An input is
*accepted* when some assignment of values to the edges satisfies every constraint.

Networks are a semantics-free form of computation. Nothing in them is directed: a gate
`z = g(x, y)` becomes the relation `{(x, y, z) | z = g(x, y)}` between three edge values, and
the network never needs to invert `g`.

**The separator lemma** (`Network.Satisfies.splice`). Cut the vertices into a set `L` and its
complement. If two satisfying assignments, for inputs `x` and `y`, agree on the edge cut of `L`,
then taking the first assignment near `L` and the second away from it satisfies the network for
the input that reads like `x` at `L` and like `y` elsewhere. Once the values on the cut are
fixed, the two sides of the network are independent.

**The branching program of a layout** (`Network.branchingProgram`). Process the vertices in the
order of a layout. Layer `t` of the program is the *frontier* after the first `t` vertices, the
edge cut between them and the rest, and its states are the values on the frontier. Step `t`
processes the vertex `v` numbered `t` and reads the inputs read at `v`; its edges join the values
of an assignment on the frontier before `v` to its values on the frontier after `v` when the
constraint at `v` holds. One last step reads the inputs that the network does not read, so the
program reads every input exactly once.

**Exactness** (`Network.accepted_branchingProgram`). The frontier values of a satisfying
assignment form an accepting path. Conversely, along an accepting path the value on an edge
persists while the edge stays on the frontier, so the assignments witnessing the steps agree on
every edge and glue into a satisfying assignment (`Network.exists_satisfies_of_isAcceptingPath`).
If satisfying assignments are unique, the program is unambiguous.

**Counting edges.** An edge of the program at step `t` is determined by the values on two
consecutive frontiers and the inputs read at the vertex processed in between. So a layout of
width `w` in a network of degree at most `d`, reading at most `m` inputs per vertex, gives a
program with at most `|U| ^ (w + d + m)` edges at each of its first `|V|` steps. Its final step
has at most `|U| ^ #(unread inputs)` edges (`Network.size_branchingProgram_le`), and the rectangle
bound for read-once programs bounds the accepted set (`Network.ncard_accepted_le`); peeling bounds
the bias of a set on it (`Network.abs_signedCount_accepted_le`).

**Sweeps with extra messages** (`Network.frontierSweep`). Any values `val x` on the edges, not
necessarily satisfying, together with an *extra* message at each time, form a sweep as soon as
the inputs sending the same messages splice. This is how a global register, such as a ledger,
travels along a layout next to the values on the frontier.

## Main definitions

* `Cslib.Circuits.Frontier.Network U ι V E`: a constraint network.
* `Cslib.Circuits.Frontier.Network.accepted`: its accepted inputs.
* `Cslib.Circuits.Frontier.Network.branchingProgram`: the read-once branching program of a
  layout.
* `Cslib.Circuits.Frontier.Network.frontierSweep`: frontier values and extra messages along a
  layout, as a sweep.

## Main results

* `Cslib.Circuits.Frontier.Network.Satisfies.splice`: the separator lemma.
* `Cslib.Circuits.Frontier.Network.dependsOn_read`: acceptance depends only on the inputs read.
* `Cslib.Circuits.Frontier.Network.readIn_insert_subset`: inserting one vertex adds only its reads.
* `Cslib.Circuits.Frontier.Network.exists_ncard_readIn_initial_eq`: read counts reach every
  intermediate value when each vertex reads at most one input.
* `Cslib.Circuits.Frontier.Network.ncard_image_path_le`: states at a layer are bounded by the
  number of assignments on its frontier.
* `Cslib.Circuits.Frontier.Network.accepted_branchingProgram`: the branching program of a layout
  accepts exactly the accepted inputs.
* `Cslib.Circuits.Frontier.Network.unambiguous_branchingProgram`: it is unambiguous when
  satisfying assignments are unique.
* `Cslib.Circuits.Frontier.Network.size_branchingProgram_le`: its size, by the width.
* `Cslib.Circuits.Frontier.Network.ncard_accepted_le`: the frontier counting lemma for networks.
* `Cslib.Circuits.Frontier.Network.abs_signedCount_accepted_le`: its peeling form, for biased
  sets.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set

/-- A *constraint network* over the alphabet `U` with inputs indexed by `ι`: a multigraph on
vertices `V` and edges `E`, the vertex at which each input is read (if any), and a constraint at
each vertex that sees only the values on the edges at that vertex and the inputs read there. -/
structure Network (U ι V E : Type*) extends Multigraph V E where
  /-- The vertex at which each input is read, if it is read at all. -/
  site : ι → Option V
  /-- The constraint at a vertex, on the input and the values on the edges. -/
  Constraint : V → (ι → U) → (E → U) → Prop
  /-- Constraints are local: the constraint at `v` sees only the inputs read at `v` and the
  values on the edges incident to `v`. -/
  constraint_congr : ∀ v x x' α α', (∀ i, site i = some v → x i = x' i) →
    (∀ e, src e = v ∨ tgt e = v → α e = α' e) → Constraint v x α → Constraint v x' α'

namespace Network

variable {U ι V E : Type*} (N : Network U ι V E)

/-- An assignment of values to the edges satisfies every constraint on the input `x`. -/
def Satisfies (x : ι → U) (α : E → U) : Prop :=
  ∀ v, N.Constraint v x α

/-- The *accepted* inputs: those with a satisfying assignment. -/
def accepted : Set (ι → U) :=
  {x | ∃ α, N.Satisfies x α}

/-- The inputs read at a vertex. -/
def readAt (v : V) : Set ι :=
  {i | N.site i = some v}

/-- The inputs read at the vertices of `L`. -/
def readIn (L : Set V) : Set ι :=
  {i | ∃ v ∈ L, N.site i = some v}

/-- The inputs read by the network. -/
def read : Set ι :=
  N.readIn univ

@[simp] theorem readIn_empty : N.readIn ∅ = ∅ := by
  ext i; simp [readIn]

/-- The inputs read by a set with one more vertex. -/
theorem readIn_insert_subset (v : V) (L : Set V) :
    N.readIn (insert v L) ⊆ N.readIn L ∪ N.readAt v := by
  rintro i ⟨u, hu, hi⟩
  rcases hu with rfl | hu
  · exact Or.inr hi
  · exact Or.inl ⟨u, hu, hi⟩

/-- **The separator lemma.** Let `α` satisfy the network on the input `x` and `β` on the input
`y`, and suppose that they agree on the edge cut of `L`. Then the network is satisfied on any
input `z` that agrees with `x` on the inputs read in `L` and with `y` on the others, by an
assignment that agrees with `α` on the edges touching `L` and with `β` on the remaining edges. -/
theorem Satisfies.splice {N : Network U ι V E} {L : Set V} {x y z : ι → U} {α β : E → U}
    (hx : N.Satisfies x α) (hy : N.Satisfies y β) (hcut : EqOn α β (N.edgeCut L))
    (hzx : EqOn z x (N.readIn L)) (hzy : EqOn z y (N.readIn L)ᶜ) :
    ∃ γ, N.Satisfies z γ ∧ EqOn γ α (N.touching L) ∧ EqOn γ β (N.touching L)ᶜ := by
  classical
  refine ⟨(N.touching L).piecewise α β, fun v => ?_, piecewise_eqOn _ _ _,
    piecewise_eqOn_compl _ _ _⟩
  by_cases hv : v ∈ L
  · -- Near `L`, the spliced assignment is `α` and the input reads like `x`.
    refine N.constraint_congr v x z α _ (fun i hi => (hzx ⟨v, hv, hi⟩).symm) (fun e he => ?_)
      (hx v)
    have : e ∈ N.touching L := by rcases he with h | h <;> [left; right] <;> rw [h] <;> exact hv
    exact (piecewise_eq_of_mem _ _ _ this).symm
  · -- Away from `L`, it is `β` and the input reads like `y`; the two agree on the cut.
    have hinputs : ∀ i, N.site i = some v → y i = z i := by
      intro i hi
      refine (hzy fun hiL => ?_).symm
      obtain ⟨u, hu, hiu⟩ := hiL
      exact hv (Option.some_injective _ (hiu.symm.trans hi) ▸ hu)
    have hedges : ∀ e, N.src e = v ∨ N.tgt e = v → β e = (N.touching L).piecewise α β e := by
      intro e he
      by_cases ht : e ∈ N.touching L
      · rw [piecewise_eq_of_mem _ _ _ ht]
        refine (hcut ?_).symm
        rcases he with h | h <;> rcases ht with h' | h' <;>
          simp_all [Multigraph.mem_edgeCut]
      · exact (piecewise_eq_of_notMem _ _ _ ht).symm
    exact N.constraint_congr v y z β _ hinputs hedges (hy v)

/-- Acceptance depends only on the inputs that the network reads. -/
theorem dependsOn_read : DependsOn (· ∈ N.accepted) N.read := by
  have key : ∀ x y : ι → U, (∀ i ∈ N.read, x i = y i) → x ∈ N.accepted → y ∈ N.accepted :=
    fun x y hxy ⟨α, hα⟩ => ⟨α, fun v => N.constraint_congr v x y α α
      (fun i hi => hxy i ⟨v, mem_univ v, hi⟩) (fun _ _ => rfl) (hα v)⟩
  exact fun x y hxy => propext ⟨key x y hxy, key y x fun i hi => (hxy i hi).symm⟩

/-! ### Frontier values and revealed inputs along a layout -/

section Layout

variable (π : Layout V)

open Classical in
/-- The values of an assignment on the frontier at time `t`, and nothing elsewhere. -/
noncomputable def frontierValues (t : ℕ) (α : E → U) : E → Option U := fun e =>
  if e ∈ N.frontier π t then some (α e) else none

theorem frontierValues_of_mem {t : ℕ} {α : E → U} {e : E} (he : e ∈ N.frontier π t) :
    N.frontierValues π t α e = some (α e) := by
  simp [frontierValues, he]

private theorem frontierValues_of_notMem {t : ℕ} {α : E → U} {e : E} (he : e ∉ N.frontier π t) :
    N.frontierValues π t α e = none := by
  simp [frontierValues, he]

theorem frontierValues_eq_iff {t : ℕ} {α β : E → U} :
    N.frontierValues π t α = N.frontierValues π t β ↔ EqOn α β (N.frontier π t) := by
  refine ⟨fun h e he => ?_, fun h => funext fun e => ?_⟩
  · simpa [frontierValues, he] using congrFun h e
  · by_cases he : e ∈ N.frontier π t
    · simp [frontierValues, he, h he]
    · simp [frontierValues, he]

/-- The inputs revealed by time `t`: those read by the first `t` vertices, and after the last
vertex, all inputs, including those the network does not read. -/
noncomputable def revealedBy (t : ℕ) : Set ι :=
  if t ≤ Nat.card V then N.readIn (π.initial t) else univ

theorem revealedBy_mono : Monotone (N.revealedBy π) := by
  intro s t hst
  unfold revealedBy
  split_ifs with hs ht ht
  · rintro i ⟨v, hv, hi⟩
    exact ⟨v, lt_of_lt_of_le hv hst, hi⟩
  · exact subset_univ _
  · exact absurd (hst.trans ht) hs
  · exact le_rfl

/-- The inputs revealed while processing the vertex numbered `t` are those read at that
vertex. -/
private theorem revealedBy_succ_diff {t : ℕ} (ht : t < Nat.card V) :
    N.revealedBy π (t + 1) \ N.revealedBy π t = N.readAt (π.symm ⟨t, ht⟩) := by
  ext i
  simp only [revealedBy, show t + 1 ≤ Nat.card V by omega, ht.le, ite_true, mem_sdiff, readIn,
    readAt, mem_ofPred_eq, Layout.mem_initial]
  constructor
  · rintro ⟨⟨u, hu, hiu⟩, hi'⟩
    have hut : (π u : ℕ) = t := by
      by_contra hne
      exact hi' ⟨u, by omega, hiu⟩
    rw [hiu, Option.some.injEq]
    exact (π.symm_apply_eq.mpr (Fin.ext hut.symm)).symm
  · intro hi
    refine ⟨⟨_, by simp, hi⟩, ?_⟩
    rintro ⟨u, hu, hiu⟩
    rw [hi, Option.some.injEq] at hiu
    subst hiu
    simp at hu

/-- The inputs revealed while processing the vertex numbered `t` are read at that vertex. -/
theorem revealedBy_succ_diff_subset {t : ℕ} (ht : t < Nat.card V) :
    N.revealedBy π (t + 1) \ N.revealedBy π t ⊆ N.readAt (π.symm ⟨t, ht⟩) :=
  (N.revealedBy_succ_diff π ht).subset

/-- After the last vertex, the inputs revealed are those the network does not read. -/
private theorem revealedBy_card_succ_diff :
    N.revealedBy π (Nat.card V + 1) \ N.revealedBy π (Nat.card V) = N.readᶜ := by
  simp [revealedBy, read, π.initial_of_card_le le_rfl, compl_eq_univ_sdiff]

end Layout

/-- **Reads grow one at a time.** If each vertex reads at most one input, then along every layout,
for every `k` up to the number of inputs read, the first `t` vertices read exactly `k` inputs for
some `t`, by the discrete intermediate value theorem. -/
theorem exists_ncard_readIn_initial_eq [Finite ι] (π : Layout V)
    (hm : ∀ v, (N.readAt v).ncard ≤ 1) {k : ℕ} (hk : k ≤ N.read.ncard) :
    ∃ t ≤ Nat.card V, (N.readIn (π.initial t)).ncard = k := by
  refine Nat.exists_eq_of_forall_le_add_one
    (a := fun t => (N.readIn (π.initial t)).ncard) (by simp)
    (by rwa [π.initial_of_card_le le_rfl]) fun t ht => ?_
  rw [π.initial_succ ht]
  calc (N.readIn (insert (π.symm ⟨t, ht⟩) (π.initial t))).ncard
      ≤ (N.readIn (π.initial t) ∪ N.readAt (π.symm ⟨t, ht⟩)).ncard :=
        ncard_le_ncard (N.readIn_insert_subset _ _) (toFinite _)
    _ ≤ (N.readIn (π.initial t)).ncard + (N.readAt (π.symm ⟨t, ht⟩)).ncard := ncard_union_le _ _
    _ ≤ (N.readIn (π.initial t)).ncard + 1 := Nat.add_le_add_left (hm _) _

/-! ### The branching program of a layout -/

section BranchingProgram

variable (π : Layout V)

/-- **The branching program of a layout.** Its layers are the frontiers of the layout, and its
states are the values on a frontier. Step `t < |V|` processes the vertex `v` numbered `t` and
reads the inputs read at `v`: an edge joins the values of an assignment `α` on the frontier
before `v` to its values on the frontier after `v` when the constraint at `v` holds for `α`.
The last step reads the inputs that the network does not read. -/
noncomputable def branchingProgram : ReadOnceNBP ι U (E → Option U) where
  length := Nat.card V + 1
  revealed := N.revealedBy π
  revealed_zero := by simp [revealedBy]
  revealed_length := by simp [revealedBy]
  revealed_mono := N.revealedBy_mono π
  start := fun _ => none
  accept := fun _ => none
  Edge t m a m' := ∃ (α : E → U) (x : ι → U), m = N.frontierValues π t α ∧
    m' = N.frontierValues π (t + 1) α ∧
    (N.revealedBy π (t + 1) \ N.revealedBy π t).domRestrict x = a ∧
    ∀ ht : t < Nat.card V, N.Constraint (π.symm ⟨t, ht⟩) x α

theorem branchingProgram_edge_iff {t : ℕ} {m m' : E → Option U}
    {a : ↥(N.revealedBy π (t + 1) \ N.revealedBy π t) → U} :
    (N.branchingProgram π).Edge t m a m' ↔ ∃ (α : E → U) (x : ι → U),
      m = N.frontierValues π t α ∧ m' = N.frontierValues π (t + 1) α ∧
      (N.revealedBy π (t + 1) \ N.revealedBy π t).domRestrict x = a ∧
      ∀ ht : t < Nat.card V, N.Constraint (π.symm ⟨t, ht⟩) x α :=
  Iff.rfl

/-- The step processing the vertex numbered `t` reads the inputs read at that vertex. -/
private theorem newly_branchingProgram {t : ℕ} (ht : t < Nat.card V) :
    (N.branchingProgram π).newly t = N.readAt (π.symm ⟨t, ht⟩) :=
  N.revealedBy_succ_diff π ht

/-- The last step reads the inputs that the network does not read. -/
private theorem newly_branchingProgram_card :
    (N.branchingProgram π).newly (Nat.card V) = N.readᶜ :=
  N.revealedBy_card_succ_diff π

/-! #### Exactness -/

/-- The frontier values of a satisfying assignment form an accepting path. -/
private theorem isAcceptingPath_frontierValues {x : ι → U} {α : E → U} (hα : N.Satisfies x α) :
    (N.branchingProgram π).IsAcceptingPath x fun t => N.frontierValues π t α where
  start := funext fun _ => N.frontierValues_of_notMem π (by simp)
  accept := funext fun _ => N.frontierValues_of_notMem π <| by
    rw [Multigraph.frontier_of_card_le _ _ (show Nat.card V ≤ (N.branchingProgram π).length from
      Nat.le_succ _)]
    exact notMem_empty _
  edge _ _ := (N.branchingProgram_edge_iff π).mpr ⟨α, x, rfl, rfl, rfl, fun _ => hα _⟩

/-- **Gluing.** An accepting path of the branching program lists the frontier values of a
satisfying assignment. An edge is on the frontier strictly after its earlier end and up to its
later end, and along the path it keeps the value given to it by the step that processes its
earlier end. Reading each edge off that step gives an assignment that agrees with the witness of
every step on the edges at its vertex, so it satisfies every constraint. -/
theorem exists_satisfies_of_isAcceptingPath {x : ι → U} {γ : ℕ → E → Option U}
    (hγ : (N.branchingProgram π).IsAcceptingPath x γ) :
    ∃ α, N.Satisfies x α ∧ ∀ t ≤ Nat.card V + 1, γ t = N.frontierValues π t α := by
  have hedge : ∀ t < Nat.card V + 1, ∃ (α : E → U) (y : ι → U),
      γ t = N.frontierValues π t α ∧ γ (t + 1) = N.frontierValues π (t + 1) α ∧
      (N.revealedBy π (t + 1) \ N.revealedBy π t).domRestrict y =
        (N.revealedBy π (t + 1) \ N.revealedBy π t).domRestrict x ∧
      ∀ ht : t < Nat.card V, N.Constraint (π.symm ⟨t, ht⟩) y α :=
    fun t ht => (N.branchingProgram_edge_iff π).mp (hγ.edge t ht)
  have : Nonempty (E → U) := ⟨(hedge 0 (by omega)).choose⟩
  have : Nonempty (ι → U) := ⟨x⟩
  choose! αs ys hfv hfv' hys hcheck using hedge
  -- The positions of the earlier and the later end of each edge.
  obtain ⟨lo, hlo⟩ : ∃ lo : E → ℕ, ∀ e, lo e = min (π (N.src e) : ℕ) (π (N.tgt e)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨hi, hhi⟩ : ∃ hi : E → ℕ, ∀ e, hi e = max (π (N.src e) : ℕ) (π (N.tgt e)) :=
    ⟨_, fun _ => rfl⟩
  have hmem (e : E) (t : ℕ) : e ∈ N.frontier π t ↔ lo e < t ∧ t ≤ hi e := by
    rw [Multigraph.mem_frontier, hlo, hhi]
    omega
  have hhiV (e : E) : hi e < Nat.card V := by
    rw [hhi]
    exact max_lt (π _).isLt (π _).isLt
  -- While an edge is on the frontier, the path carries the value given to it by the step that
  -- processes its earlier end.
  have hpersist (e : E) (t : ℕ) (h₁ : lo e + 1 ≤ t) (h₂ : t ≤ hi e) :
      γ t e = some (αs (lo e) e) := by
    have := hhiV e
    induction t, h₁ using Nat.le_induction with
    | base => rw [hfv' _ (by omega), N.frontierValues_of_mem π ((hmem e _).mpr ⟨by omega, h₂⟩)]
    | succ t ht ih =>
      rw [← ih (by omega), hfv t (by omega), hfv' t (by omega),
        N.frontierValues_of_mem π ((hmem e t).mpr ⟨by omega, by omega⟩),
        N.frontierValues_of_mem π ((hmem e (t + 1)).mpr ⟨by omega, h₂⟩)]
  refine ⟨fun e => αs (lo e) e, fun v => ?_, fun t ht => funext fun e => ?_⟩
  · obtain ⟨t, ht, rfl⟩ : ∃ t, ∃ ht : t < Nat.card V, v = π.symm ⟨t, ht⟩ :=
      ⟨π v, (π v).isLt, by simp⟩
    have hπt : (π (π.symm ⟨t, ht⟩) : ℕ) = t := by simp
    refine N.constraint_congr _ (ys t) x (αs t) _ (fun i hread => ?_) (fun e he => ?_)
      (hcheck t (by omega) ht)
    · -- The inputs read at the vertex are read during its step.
      have hi' : i ∈ (N.branchingProgram π).newly t := by
        rw [N.newly_branchingProgram π ht]
        exact hread
      exact congrFun (hys t (by omega)) ⟨i, hi'⟩
    · -- The vertex is the earlier end of the edge, or the edge is on the frontier before it.
      have hend : lo e = t ∨ lo e < t ∧ t ≤ hi e := by
        have : (π (N.src e) : ℕ) = t ∨ (π (N.tgt e) : ℕ) = t :=
          he.imp (fun h => by rw [h, hπt]) (fun h => by rw [h, hπt])
        rw [hlo, hhi]
        omega
      rcases hend with h | ⟨h₁, h₂⟩
      · rw [h]
      · have h := hpersist e t h₁ h₂
        rw [hfv t (by omega), N.frontierValues_of_mem π ((hmem e t).mpr ⟨h₁, h₂⟩)] at h
        exact Option.some_injective _ h
  · by_cases he : e ∈ N.frontier π t
    · rw [N.frontierValues_of_mem π he]
      exact hpersist e t ((hmem e t).mp he).1 ((hmem e t).mp he).2
    · rw [N.frontierValues_of_notMem π he]
      rcases ht.lt_or_eq with ht | rfl
      · rw [hfv t ht, N.frontierValues_of_notMem π he]
      · exact congrFun hγ.accept e

/-- **Exactness.** The branching program of a layout accepts exactly the accepted inputs of the
network. -/
theorem accepted_branchingProgram : (N.branchingProgram π).accepted = N.accepted := by
  ext x
  constructor
  · rintro ⟨γ, hγ⟩
    obtain ⟨α, hα, -⟩ := N.exists_satisfies_of_isAcceptingPath π hγ
    exact ⟨α, hα⟩
  · rintro ⟨α, hα⟩
    exact ⟨_, N.isAcceptingPath_frontierValues π hα⟩

/-- If every input has at most one satisfying assignment, the branching program of every layout
is unambiguous: an accepting path lists the frontier values of a satisfying assignment. -/
theorem unambiguous_branchingProgram
    (h : ∀ x α β, N.Satisfies x α → N.Satisfies x β → α = β) :
    (N.branchingProgram π).Unambiguous := by
  intro x γ δ hγ hδ t ht
  obtain ⟨α, hα, hγα⟩ := N.exists_satisfies_of_isAcceptingPath π hγ
  obtain ⟨β, hβ, hδβ⟩ := N.exists_satisfies_of_isAcceptingPath π hδ
  rw [hγα t ht, hδβ t ht, h x α β hα hβ]

/-! #### Counting edges -/

/-- **Edges by width.** At a step that processes a vertex, an edge of the program is determined
by the values of an assignment on the two frontiers and the inputs read at the vertex. -/
private theorem ncard_edges_le [Finite ι] [Finite U] [Finite E] {t : ℕ} (ht : t < Nat.card V) :
    ((N.branchingProgram π).edges t).ncard ≤
      Nat.card U ^ ((N.frontier π t ∪ N.frontier π (t + 1)).ncard +
        (N.readAt (π.symm ⟨t, ht⟩)).ncard) := by
  classical
  set C := N.frontier π t ∪ N.frontier π (t + 1)
  let g : (C → U) × ((N.branchingProgram π).newly t → U) →
      (E → Option U) × ((N.branchingProgram π).newly t → U) × (E → Option U) := fun ca =>
    (fun e => if h : e ∈ N.frontier π t then some (ca.1 ⟨e, Or.inl h⟩) else none, ca.2,
      fun e => if h : e ∈ N.frontier π (t + 1) then some (ca.1 ⟨e, Or.inr h⟩) else none)
  have hsub : (N.branchingProgram π).edges t ⊆ range g := by
    rintro ⟨m, a, m'⟩ he
    obtain ⟨α, x, rfl, rfl, rfl, -⟩ := (N.branchingProgram_edge_iff π).mp he
    refine ⟨(C.domRestrict α, _), Prod.ext ?_ (Prod.ext rfl ?_)⟩ <;> funext e <;>
      simp only [g, frontierValues] <;> split_ifs <;> rfl
  calc ((N.branchingProgram π).edges t).ncard
      ≤ (range g).ncard := ncard_le_ncard hsub (toFinite _)
    _ ≤ Nat.card ((C → U) × ((N.branchingProgram π).newly t → U)) := by
        rw [← image_univ]
        exact (ncard_image_le (toFinite _)).trans (ncard_univ _).le
    _ = Nat.card U ^ (C.ncard + (N.readAt (π.symm ⟨t, ht⟩)).ncard) := by
        rw [Nat.card_prod, Nat.card_fun, Nat.card_fun, Nat.card_coe_set_eq,
          Nat.card_coe_set_eq, N.newly_branchingProgram π ht, pow_add]

/-- At the last step both frontiers are empty, so an edge of the program is determined by the
unread inputs. -/
private theorem ncard_edges_last_le [Finite ι] [Finite U] :
    ((N.branchingProgram π).edges (Nat.card V)).ncard ≤ Nat.card U ^ N.readᶜ.ncard := by
  have hempty (s : ℕ) (hs : Nat.card V ≤ s) (α : E → U) :
      N.frontierValues π s α = fun _ => none := by
    funext e
    refine N.frontierValues_of_notMem π ?_
    rw [Multigraph.frontier_of_card_le _ _ hs]
    exact notMem_empty _
  have hsub : (N.branchingProgram π).edges (Nat.card V) ⊆
      range fun a : (N.branchingProgram π).newly (Nat.card V) → U =>
        ((fun _ => none : E → Option U), a, (fun _ => none : E → Option U)) := by
    rintro ⟨m, a, m'⟩ he
    obtain ⟨α, x, rfl, rfl, rfl, -⟩ := (N.branchingProgram_edge_iff π).mp he
    exact ⟨(N.revealedBy π (Nat.card V + 1) \ N.revealedBy π (Nat.card V)).domRestrict x,
      by rw [hempty _ le_rfl, hempty _ (Nat.le_succ _)]⟩
  calc ((N.branchingProgram π).edges (Nat.card V)).ncard
      ≤ (range fun a : (N.branchingProgram π).newly (Nat.card V) → U =>
          ((fun _ => none : E → Option U), a, (fun _ => none : E → Option U))).ncard :=
        ncard_le_ncard hsub (toFinite _)
    _ ≤ Nat.card ((N.branchingProgram π).newly (Nat.card V) → U) := by
        rw [← image_univ]
        exact (ncard_image_le (toFinite _)).trans (ncard_univ _).le
    _ = Nat.card U ^ N.readᶜ.ncard := by
        rw [Nat.card_fun, Nat.card_coe_set_eq, N.newly_branchingProgram_card π]

/-- **The states of the branching program of a layout.** At a layer `t ≤ |V|`, the chosen
accepting paths of the accepted inputs pass through at most `|U| ^ |frontier t|` states: each is
the list of the values of a satisfying assignment on the frontier. -/
theorem ncard_image_path_le [Finite U] [Finite E] (π : Layout V) {t : ℕ}
    (ht : t ≤ Nat.card V) :
    ((fun x => (N.branchingProgram π).path x t) '' N.accepted).ncard ≤
      Nat.card U ^ (N.frontier π t).ncard := by
  classical
  set F := N.frontier π t
  let φ : (F → U) → E → Option U := fun a e => if h : e ∈ F then some (a ⟨e, h⟩) else none
  have hsub : (fun x => (N.branchingProgram π).path x t) '' N.accepted ⊆ range φ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← N.accepted_branchingProgram π] at hx
    obtain ⟨α, -, hα⟩ :=
      N.exists_satisfies_of_isAcceptingPath π ((N.branchingProgram π).isAcceptingPath_path hx)
    refine ⟨F.domRestrict α, funext fun e => ?_⟩
    dsimp only
    rw [hα t (by omega)]
    simp only [φ, frontierValues, Set.domRestrict_apply]
    split_ifs <;> rfl
  calc _ ≤ (range φ).ncard := ncard_le_ncard hsub (toFinite _)
    _ ≤ Nat.card (F → U) := by
        rw [← image_univ]
        exact (ncard_image_le (toFinite _)).trans (ncard_univ _).le
    _ = Nat.card U ^ F.ncard := by rw [Nat.card_fun, Nat.card_coe_set_eq]

/-- **The size of the program.** If a layout has width at most `w`, and every vertex has degree
at most `d` and reads at most `m` inputs, then the branching program has at most
`|V| · |U| ^ (w + d + m) + |U| ^ #(unread inputs)` edges. -/
theorem size_branchingProgram_le [Finite ι] [Finite U] [Nonempty U] [Finite E]
    {w d m : ℕ} (hw : N.width π ≤ w) (hd : N.MaxDegreeLE d)
    (hm : ∀ v, (N.readAt v).ncard ≤ m) :
    (N.branchingProgram π).size ≤
      Nat.card V * Nat.card U ^ (w + d + m) + Nat.card U ^ N.readᶜ.ncard := by
  have hq : 1 ≤ Nat.card U := Nat.card_pos
  rw [ReadOnceNBP.size, show (N.branchingProgram π).length = Nat.card V + 1 from rfl,
    Finset.sum_range_succ]
  refine add_le_add ?_ (N.ncard_edges_last_le π)
  calc ∑ t ∈ Finset.range (Nat.card V), ((N.branchingProgram π).edges t).ncard
      ≤ ∑ _t ∈ Finset.range (Nat.card V), Nat.card U ^ (w + d + m) := by
        refine Finset.sum_le_sum fun t ht => ?_
        have ht : t < Nat.card V := Finset.mem_range.mp ht
        refine (N.ncard_edges_le π ht).trans (Nat.pow_le_pow_right hq ?_)
        -- Both frontiers lie in the first one and the edges at the vertex processed.
        have hC : (N.frontier π t ∪ N.frontier π (t + 1)).ncard ≤ w + d :=
          calc (N.frontier π t ∪ N.frontier π (t + 1)).ncard
              ≤ (N.frontier π t ∪ N.incidenceSet (π.symm ⟨t, ht⟩)).ncard :=
                ncard_le_ncard (union_subset subset_union_left (N.frontier_succ_subset π ht))
                  (toFinite _)
            _ ≤ (N.frontier π t).ncard + (N.incidenceSet (π.symm ⟨t, ht⟩)).ncard :=
                ncard_union_le _ _
            _ ≤ w + d := add_le_add ((N.ncard_frontier_le_width π t).trans hw) (hd _)
        have := hm (π.symm ⟨t, ht⟩)
        omega
    _ = Nat.card V * Nat.card U ^ (w + d + m) := by simp

/-- **The frontier counting lemma for networks.** Let the accepted inputs of a network be
`K`-rectangle-free. If a layout has width at most `w`, and every vertex has degree at most `d`
and reads at most `m` inputs, then

`|accepted| ≤ (K - 1) ^ 2 · (|V| · |U| ^ (w + d + m) + |U| ^ #(unread inputs))`.

This is the rectangle bound for the branching program of the layout. -/
theorem ncard_accepted_le [Finite ι] [Finite U] [Nonempty U] [Finite E] {K : ℕ}
    (hfree : RectangleFree N.accepted K) {w d m : ℕ} (hw : N.width π ≤ w)
    (hd : N.MaxDegreeLE d) (hm : ∀ v, (N.readAt v).ncard ≤ m) :
    N.accepted.ncard ≤
      (K - 1) ^ 2 * (Nat.card V * Nat.card U ^ (w + d + m) + Nat.card U ^ N.readᶜ.ncard) := by
  have h := (N.branchingProgram π).ncard_accepted_le (Nat.succ_pos _) (K := K)
    (by rwa [accepted_branchingProgram])
  rw [accepted_branchingProgram] at h
  exact h.trans (Nat.mul_le_mul_left _ (N.size_branchingProgram_le π hw hd hm))

/-- **Peeling for networks.** Let `S` have bias at most `b ≥ 0` on rectangles with both sides
of size at least `K`, and let every input have at most one satisfying assignment. If a layout
has width at most `w`, and every vertex has degree at most `d` and reads at most `m` inputs, then
the accepted inputs in `S` and those outside `S` differ in number by at most

`2 b |accepted| + (K - 1) ^ 2 · (|V| · |U| ^ (w + d + m) + |U| ^ #(unread inputs))`. -/
theorem abs_signedCount_accepted_le [Finite ι] [Finite U] [Nonempty U] [Finite E]
    (hunique : ∀ x α β, N.Satisfies x α → N.Satisfies x β → α = β)
    {S : Set (ι → U)} {K : ℕ} {b : ℝ} (hb : 0 ≤ b) (hS : RectangleBias S K b)
    {w d m : ℕ} (hw : N.width π ≤ w) (hd : N.MaxDegreeLE d)
    (hm : ∀ v, (N.readAt v).ncard ≤ m) :
    |signedCount S N.accepted| ≤ 2 * b * N.accepted.ncard +
      ((K - 1) ^ 2 * (Nat.card V * Nat.card U ^ (w + d + m) + Nat.card U ^ N.readᶜ.ncard) : ℕ) := by
  have h := (N.branchingProgram π).abs_signedCount_accepted_le
    (N.unambiguous_branchingProgram π hunique) (Nat.succ_pos _) hb hS
  rw [accepted_branchingProgram] at h
  refine h.trans (add_le_add le_rfl ?_)
  exact_mod_cast Nat.mul_le_mul_left _ (N.size_branchingProgram_le π hw hd hm)

end BranchingProgram

/-! ### Sweeps with extra messages -/

section Sweep

variable (π : Layout V) {S : Set (ι → U)} {R : Type*}

/-- **Sweeping along a layout with extra messages.** Fix values `val x` on the edges for every
input `x`, and an extra message `extra t x` at every time. The messages
`(extra t x, val x on the frontier at time t)` form a sweep of `S` as soon as inputs of `S` with
the same messages splice, and the last extra message is the same for all inputs of `S`. -/
noncomputable def frontierSweep (val : (ι → U) → E → U) (extra : ℕ → (ι → U) → R)
    (hlast : ∀ x ∈ S, ∀ y ∈ S, extra (Nat.card V + 1) x = extra (Nat.card V + 1) y)
    (hsplice : ∀ t ≤ Nat.card V, ∀ x ∈ S, ∀ y ∈ S, extra t x = extra t y →
      EqOn (val x) (val y) (N.frontier π t) →
      ∀ z, EqOn z x (N.readIn (π.initial t)) → EqOn z y (N.readIn (π.initial t))ᶜ → z ∈ S) :
    Sweep S (R × (E → Option U)) where
  length := Nat.card V + 1
  revealed := N.revealedBy π
  revealed_zero := by simp [revealedBy]
  revealed_length := by simp [revealedBy]
  message t x := (extra t x, N.frontierValues π t (val x))
  message_length x hx y hy := by
    rw [Prod.mk.injEq, frontierValues_eq_iff, Multigraph.frontier_of_card_le _ _ (by omega)]
    exact ⟨hlast x hx y hy, eqOn_empty _ _⟩
  splice t x hx y hy hxy z hzx hzy := by
    rw [Prod.mk.injEq, frontierValues_eq_iff] at hxy
    unfold revealedBy at hzx hzy
    split_ifs at hzx hzy with ht
    · exact hsplice t ht x hx y hy hxy.1 hxy.2 z hzx hzy
    · rwa [show z = x from funext fun i => hzx (mem_univ i)]

variable {π} {val : (ι → U) → E → U} {extra : ℕ → (ι → U) → R}
  {hlast : ∀ x ∈ S, ∀ y ∈ S, extra (Nat.card V + 1) x = extra (Nat.card V + 1) y}
  {hsplice : ∀ t ≤ Nat.card V, ∀ x ∈ S, ∀ y ∈ S, extra t x = extra t y →
      EqOn (val x) (val y) (N.frontier π t) →
      ∀ z, EqOn z x (N.readIn (π.initial t)) → EqOn z y (N.readIn (π.initial t))ᶜ → z ∈ S}

/-- **Transitions by width.** At a step that processes a vertex, the transition is determined by
the extra messages, the values on the two frontiers, and the inputs read at the vertex. -/
theorem ncard_transition_le [Finite ι] [Finite U] [Finite E] {t : ℕ} (ht : t < Nat.card V) :
    ((N.frontierSweep π val extra hlast hsplice).transition t '' S).ncard ≤
      ((fun x => (extra t x, extra (t + 1) x)) '' S).ncard *
        Nat.card U ^ ((N.frontier π t ∪ N.frontier π (t + 1)).ncard +
          (N.readAt (π.symm ⟨t, ht⟩)).ncard) := by
  set C := N.frontier π t ∪ N.frontier π (t + 1)
  set Q := N.readAt (π.symm ⟨t, ht⟩)
  have h := (N.frontierSweep π val extra hlast hsplice).ncard_transition_le_of_factorsThrough
    (t := t) (D := (C → U) × (Q → U)) (fun x => (extra t x, extra (t + 1) x))
    (fun x => (C.domRestrict (val x), Q.domRestrict x)) fun x _ y _ h₀ hg => by
      simp only [Prod.mk.injEq, domRestrict_eq_domRestrict_iff] at h₀ hg
      simp only [Sweep.transition, frontierSweep, Prod.mk.injEq, frontierValues_eq_iff,
        domRestrict_eq_domRestrict_iff]
      exact ⟨⟨h₀.1, hg.1.mono subset_union_left⟩, ⟨h₀.2, hg.1.mono subset_union_right⟩,
        hg.2.mono (N.revealedBy_succ_diff_subset π ht)⟩
  rwa [Nat.card_prod, Nat.card_fun, Nat.card_fun, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
    ← pow_add] at h

/-- At the last step nothing is left on the frontier, and the transition is determined by the
extra messages and the inputs that the network does not read. -/
theorem ncard_transition_last_le [Finite ι] [Finite U] :
    ((N.frontierSweep π val extra hlast hsplice).transition (Nat.card V) '' S).ncard ≤
      ((fun x => (extra (Nat.card V) x, extra (Nat.card V + 1) x)) '' S).ncard *
        Nat.card U ^ N.readᶜ.ncard := by
  have h := (N.frontierSweep π val extra hlast hsplice).ncard_transition_le_of_factorsThrough
    (t := Nat.card V) (D := ↥N.readᶜ → U)
    (fun x => (extra (Nat.card V) x, extra (Nat.card V + 1) x))
    (fun x => N.readᶜ.domRestrict x) fun x _ y _ h₀ hg => by
      simp only [Prod.mk.injEq] at h₀
      rw [domRestrict_eq_domRestrict_iff, ← N.revealedBy_card_succ_diff π] at hg
      simp only [Sweep.transition, frontierSweep, Prod.mk.injEq, frontierValues_eq_iff,
        domRestrict_eq_domRestrict_iff, Multigraph.frontier_of_card_le _ _ le_rfl,
        Multigraph.frontier_of_card_le _ _ (Nat.le_succ _), eqOn_empty, and_true]
      exact ⟨h₀.1, h₀.2, hg⟩
  rwa [Nat.card_fun, Nat.card_coe_set_eq] at h

end Sweep

end Network

end Cslib.Circuits.Frontier
