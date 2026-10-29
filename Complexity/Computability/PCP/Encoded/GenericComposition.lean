/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Encoded.Constraints
public import Complexity.Computability.PCP.GenericComposition
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
import Complexity.Tactic.PolyTime
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases

/-!
# Executable composition from a realized assignment tester

An `AssignmentTester.Implementation` supplies executable queries and acceptance for runtime Boolean
constraints. `Implementation.Realizes` certifies their exact mathematical interpretation. One
generator enumerates the coin-to-query edges for any such realization. The fixed finite types,
numbering, and coin/query lists are independent of the runtime graph. Its certificates charge
graph enumeration, all tables, copies, and output storage; they do not give alphabet-uniform or
practical bounds.

## Main definitions

* `Cslib.PCP.AssignmentTester.Implementation`: executable data interpreting a mathematical tester.
* `Cslib.PCP.AssignmentTester.Implementation.compose`: the numbered gadget graph.
* `Cslib.PCP.AssignmentTester.Implementation.composeTabulated`: its tabulated constraints.

## Main results

* `Cslib.PCP.AssignmentTester.Implementation.toGraph_compose`: exact interpretation.
* `Cslib.PCP.AssignmentTester.Implementation.isPolyTime_composeTabulated`: construction certificate.
* `Cslib.PCP.AssignmentTester.Implementation.unsatVal_composeTabulated_eq`: exact value transfer.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
-/

@[expose] public section

namespace Cslib.PCP

open Turing.MultiTapeTM Encoded Encoded.Graph

namespace AssignmentTester

/-- The local input, auxiliary, and coin slots in a numbered gadget block. -/
abbrev ComposeSlot (I P R : Type) : Type := I ⊕ P ⊕ R

/-- Executable queries and decisions for runtime Boolean constraints. Correctness relative to a
mathematical tester is the separate proposition `Implementation.Realizes`. -/
structure Implementation (α I P R Q Γ : Type) where
  /-- Compute one queried input or auxiliary position. -/
  query : (α → α → Bool) → R → Q → ((Fin 2 × I) ⊕ P)
  /-- Decide acceptance from the supplied query answers. -/
  accepts : (α → α → Bool) → R → (Q → Γ) → Bool

namespace Implementation

variable {α I P R Q Γ Input : Type} (impl : Implementation α I P R Q Γ)
  {T : AssignmentTester α I P R Q Γ} {input : Input ↪ List Bool} {width : ℕ}

/-- Exact agreement with a mathematical tester, kept separate from executable data so that
noncomputable mathematical definitions are absent from compiled generator arguments. -/
structure Realizes (T : AssignmentTester α I P R Q Γ) : Prop where
  /-- Computed positions agree with the mathematical tester. -/
  query_eq (constraint : α → α → Bool) (coins : R) (i : Q) :
    impl.query constraint coins i = (T.test (fun a b => constraint a b = true)).query coins i
  /-- Computed decisions agree with the mathematical acceptance predicate. -/
  accepts_eq_true (constraint : α → α → Bool) (coins : R) (answers : Q → Γ) :
    impl.accepts constraint coins answers = true ↔
      (T.test (fun a b => constraint a b = true)).Accepts coins answers

/-- Number a queried proof position using a supplied finite slot numbering. -/
def composePosition (number : ComposeSlot I P R ≃ Fin width) (edge src dst : ℕ) :
    (Fin 2 × I) ⊕ P → ℕ :=
  Sum.elim (fun p => (if p.1 = 0 then src else dst) * width + (number (.inl p.2)).val)
    fun p => edge * width + (number (.inr (.inl p))).val

/-- Build the edge from one coin vertex to one of the queried proof positions. -/
def composeEdge (number : ComposeSlot I P R ≃ Fin width) (edge : Edge (α → α → Bool))
    (index : ℕ) (coins : R) (i : Q) : Edge ((α → α → Bool) × R × Q) :=
  ⟨index * width + (number (.inr (.inr coins))).val,
    composePosition number index edge.src edge.dst
      (impl.query edge.constraint coins i),
    (edge.constraint, coins, i)⟩

/-- Verify the claimed answers and their agreement with the queried proof symbol. -/
def composeEval [BEq Γ] (descriptor : (α → α → Bool) × R × Q)
    (a b : Γ × (Q → Γ)) : Bool :=
  impl.accepts descriptor.1 descriptor.2.1 a.2 &&
    (a.2 descriptor.2.2 == b.1)

/-- Enumerate all supplied random strings and queries for every original edge, in list order. -/
def composeDarts (coins : List R) (queries : List Q)
    (g : Graph (α → α → Bool)) : List ((ℕ × R) × Q) :=
  ((List.range g.edges.length).product coins).product queries

/-- Compose an encoded graph with a specified list of coins and queries.
Full alphabet reduction requires each of those lists to enumerate its type exactly once. -/
def compose (number : ComposeSlot I P R ≃ Fin width) (coins : List R)
    (queries : List Q) (g : Graph (α → α → Bool)) :
    Graph ((α → α → Bool) × R × Q) :=
  ⟨(g.vertices + g.edges.length) * width,
    (composeDarts coins queries g).map fun p =>
      composeEdge impl number (g.edgeAt (fun _ _ => false) p.1.1) p.1.1 p.1.2 p.2⟩

/-- Position numbering charges all runtime indices; finite dispatch only concerns the fixed
alphabet's local proof position. -/
@[fun_prop]
theorem isPolyTime_composePosition [Finite I] [Finite P] (number : ComposeSlot I P R ≃ Fin width)
    {edge src dst : Input → ℕ} {position : Input → ((Fin 2 × I) ⊕ P)}
    {positionEncoding : ((Fin 2 × I) ⊕ P) ↪ List Bool}
    (hedge : ComputableInPolyTime edge input encUnary)
    (hsrc : ComputableInPolyTime src input encUnary)
    (hdst : ComputableInPolyTime dst input encUnary)
    (hposition : ComputableInPolyTime position input positionEncoding) :
    ComputableInPolyTime
      (fun x => composePosition number (edge x) (src x) (dst x) (position x)) input encUnary := by
  apply ComputableInPolyTime.finite_cases
    (branch := fun p x => composePosition number (edge x) (src x) (dst x) p) hposition
  rintro (⟨b, r⟩ | p)
  · dsimp only [composePosition, Sum.elim_inl]
    split_ifs <;> fun_prop
  · dsimp only [composePosition, Sum.elim_inr]
    fun_prop

/-- A gadget edge is computed uniformly in the original edge, its index, coins, and query. -/
@[fun_prop]
theorem isPolyTime_composeEdge [Fintype α] [Finite I] [Finite P] [Finite R] [Finite Q]
    (number : ComposeSlot I P R ≃ Fin width)
    {edge : Input → Edge (α → α → Bool)} {index : Input → ℕ}
    {coins : Input → R} {query : Input → Q}
    {coinsEncoding : R ↪ List Bool} {queryEncoding : Q ↪ List Bool}
    (hedge : ComputableInPolyTime edge input (Edge.encoding (encPi (encPi encBool))))
    (hindex : ComputableInPolyTime index input encUnary)
    (hcoins : ComputableInPolyTime coins input coinsEncoding)
    (hquery : ComputableInPolyTime query input queryEncoding) :
    ComputableInPolyTime
      (fun x => composeEdge impl number (edge x) (index x) (coins x) (query x))
      input (Edge.encoding (encPair (encPi (encPi encBool))
        (encPair coinsEncoding queryEncoding))) := by
  have hnumber : ComputableInPolyTime (fun ω => (number (.inr (.inr ω))).val)
      coinsEncoding encUnary := .of_finite _
  have hposition : ComputableInPolyTime
      (fun p : (α → α → Bool) × R × Q => impl.query p.1 p.2.1 p.2.2)
      (encPair (encPi (encPi encBool)) (encPair coinsEncoding queryEncoding))
      (encFinite ((Fin 2 × I) ⊕ P)) := .of_finite _
  have hposition' := hposition.comp
    ((Edge.isPolyTime_constraint hedge).prod (hcoins.prod hquery))
  have hdst' := isPolyTime_composePosition number hindex (Edge.isPolyTime_src hedge)
    (Edge.isPolyTime_dst hedge) hposition'
  exact Edge.isPolyTime_mk
    (ComputableInPolyTime.unary_add.comp
      ((ComputableInPolyTime.unary_mul.comp (hindex.prod (.const width))).prod
        (hnumber.comp hcoins))) hdst'
    ((Edge.isPolyTime_constraint hedge).prod (hcoins.prod hquery))

/-- The verifier's edge predicate charges all supplied finite tables and query answers. -/
@[fun_prop]
theorem isPolyTime_composeEval [Fintype α] [Fintype Q] [Finite R] [Finite Γ] [BEq Γ]
    (symbolEncoding : Γ ↪ List Bool) (coinsEncoding : R ↪ List Bool)
    (queryEncoding : Q ↪ List Bool) :
    ComputableInPolyTime
      (fun p : ((α → α → Bool) × R × Q) ×
          (Γ × (Q → Γ)) × (Γ × (Q → Γ)) => composeEval impl p.1 p.2.1 p.2.2)
      (encPair (encPair (encPi (encPi encBool)) (encPair coinsEncoding queryEncoding))
        (encPair (encPair symbolEncoding (encPi symbolEncoding))
          (encPair symbolEncoding (encPi symbolEncoding)))) encBool :=
  .of_finite _

/-- The full construction charges the old graph, enumeration, each tester call, copying,
and the complete output graph. The finite alphabet and supplied lists are fixed. -/
@[fun_prop]
theorem isPolyTime_compose [Fintype α] [Finite I] [Finite P] [Finite R] [Finite Q]
    (number : ComposeSlot I P R ≃ Fin width) (coins : List R)
    (queries : List Q) (coinsEncoding : R ↪ List Bool)
    (queryEncoding : Q ↪ List Bool) :
    ComputableInPolyTime (compose impl number coins queries)
      (encoding (encPi (encPi encBool)))
      (encoding (encPair (encPi (encPi encBool)) (encPair coinsEncoding queryEncoding))) := by
  have hdarts : ComputableInPolyTime (composeDarts (α := α) coins queries)
      (encoding (encPi (encPi encBool)))
      (encList (encPair (encPair encUnary coinsEncoding) queryEncoding)) := by
    unfold composeDarts List.product
    fun_prop
  unfold compose
  fun_prop

/-- Return composition to the fixed Boolean-table descriptor type over its answer alphabet. -/
def composeTabulated [BEq Γ] (number : ComposeSlot I P R ≃ Fin width) (coins : List R)
    (queries : List Q) (g : Graph (α → α → Bool)) :
    Graph ((Γ × (Q → Γ)) → (Γ × (Q → Γ)) → Bool) :=
  (compose impl number coins queries g).mapConstraints (composeEval impl)

/-- Tabulated composition fixes its internal finite encodings, so clients only certify the
input graph in their own input representation. Every output constraint table is charged. -/
@[fun_prop]
theorem isPolyTime_composeTabulated [Fintype α] [Finite I] [Finite P] [Finite R]
    [Fintype Q] [DecidableEq Q] [Fintype Γ] [BEq Γ] {graph : Input → Graph (α → α → Bool)}
    (hgraph : ComputableInPolyTime graph input (encoding (encPi (encPi encBool))))
    (number : ComposeSlot I P R ≃ Fin width) (coins : List R) (queries : List Q) :
    ComputableInPolyTime (fun x => composeTabulated impl number coins queries (graph x))
      input (encoding (encPi (encPi encBool))) :=
  (isPolyTime_tabulateConstraints
    (isPolyTime_composeEval impl (encFinite Γ) (encFinite R) (encFinite Q))).comp
      ((isPolyTime_compose impl number coins queries (encFinite R) (encFinite Q)).comp hgraph)

/-- Each original edge produces one edge for every supplied pair of coins and query. -/
@[simp]
theorem length_edges_compose (number : ComposeSlot I P R ≃ Fin width)
    (coins : List R) (queries : List Q) (g : Graph (α → α → Bool)) :
    (compose impl number coins queries g).edges.length =
      g.edges.length * coins.length * queries.length := by
  simp only [compose, List.length_map, composeDarts]
  change (((List.range g.edges.length) ×ˢ coins) ×ˢ queries).length = _
  simp only [List.length_product, List.length_range]

/-- The declared vertex count grows by a fixed factor in the old vertices and edges. -/
@[simp]
theorem vertices_compose (number : ComposeSlot I P R ≃ Fin width)
    (coins : List R) (queries : List Q) (g : Graph (α → α → Bool)) :
    (compose impl number coins queries g).vertices = (g.vertices + g.edges.length) * width := rfl

/-- Split a mathematical composed vertex into its owner index and local slot. -/
def composeOwner {E : Type} (index : E → ℕ) :
    AssignmentTester.ComposePos ℕ E I P ⊕ E × R → ℕ × ComposeSlot I P R :=
  Sum.elim
    (Sum.elim (fun p => (p.1, .inl p.2)) (fun p => (index p.1, .inr (.inl p.2))))
    (fun p => (index p.1, .inr (.inr p.2)))

/-- The same explicit numbering on all mathematical proof positions and coin vertices. -/
def composeVertex {E : Type} (number : ComposeSlot I P R ≃ Fin width) (index : E → ℕ)
    (vertex : AssignmentTester.ComposePos ℕ E I P ⊕ E × R) : ℕ :=
  (composeOwner index vertex).1 * width + (number (composeOwner index vertex).2).val

/-- Distinct table positions and coin vertices retain distinct identifiers. -/
theorem composeVertex_injective [Nonempty R] {E : Type} (number : ComposeSlot I P R ≃ Fin width)
    {index : E → ℕ} (hindex : Function.Injective index) :
    Function.Injective (composeVertex number index) := by
  have howner : Function.Injective (composeOwner (I := I) (P := P) (R := R) index) := by
    rintro ((⟨v, r⟩ | ⟨e, p⟩) | ⟨e, ω⟩) ((⟨v', r'⟩ | ⟨e', p'⟩) | ⟨e', ω'⟩) h <;>
      simp only [composeOwner, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq, Sum.inl.injEq,
        Sum.inr.injEq, reduceCtorEq, and_false] at h
    · rcases h with ⟨rfl, rfl⟩
      rfl
    · rcases h with ⟨h, rfl⟩
      cases hindex h
      rfl
    · rcases h with ⟨h, rfl⟩
      cases hindex h
      rfl
  let : NeZero width := (number (.inr (.inr (Classical.arbitrary R)))).neZero
  exact (Nat.divModEquiv width).symm.injective.comp
    ((Equiv.prodCongr (Equiv.refl ℕ) number).injective.comp howner)

/-- The explicit endpoint selection agrees with `ConstraintGraph.testerPos`. -/
theorem composePosition_eq (number : ComposeSlot I P R ≃ Fin width)
    (g : Graph (α → α → Bool)) (e : Fin g.edges.length) (p : ((Fin 2 × I) ⊕ P)) :
    composePosition number e.val (g.edges.get e).src (g.edges.get e).dst p =
      composeVertex number Fin.val (.inl (AssignmentTester.testerPos (g.toGraph id) e p)) := by
  rcases p with ⟨b, r⟩ | p
  · fin_cases b <;> rfl
  · rfl

/-- The dart enumeration includes exactly the valid old indices and listed coins/queries. -/
@[simp]
theorem mem_composeDarts_iff (coins : List R) (queries : List Q)
    (g : Graph (α → α → Bool)) (p : (ℕ × R) × Q) :
    p ∈ composeDarts coins queries g ↔
      p.1.1 < g.edges.length ∧ p.1.2 ∈ coins ∧ p.2 ∈ queries := by
  rcases p with ⟨⟨e, ω⟩, i⟩
  change ((e, ω), i) ∈ ((List.range g.edges.length ×ˢ coins) ×ˢ queries) ↔ _
  simp only [List.mem_product, List.mem_range, and_assoc]

/-- Valid old endpoints give valid output endpoints, even for empty or incomplete coin lists. -/
theorem wellFormed_compose (number : ComposeSlot I P R ≃ Fin width)
    (coins : List R) (queries : List Q) {g : Graph (α → α → Bool)}
    (hg : g.WellFormed) : (compose impl number coins queries g).WellFormed := by
  have hnumber {owner bound : ℕ} (howner : owner < bound) (slot : ComposeSlot I P R) :
      owner * width + (number slot).val < bound * width :=
    (Nat.add_lt_add_left (number slot).isLt _).trans_le
      (by simpa only [Nat.succ_mul] using Nat.mul_le_mul_right width howner)
  intro edge hedge
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hedge
  have hp := (mem_composeDarts_iff coins queries g p).mp hp
  have heq : g.edgeAt (fun _ _ => false) p.1.1 = g.edges[p.1.1] :=
    List.getD_eq_getElem _ _ hp.1
  have he := hg _ (List.getElem_mem hp.1)
  have hi : p.1.1 < g.vertices + g.edges.length := hp.1.trans_le (Nat.le_add_left ..)
  have hsrc : (g.edges[p.1.1]).src < g.vertices + g.edges.length :=
    he.1.trans_le (Nat.le_add_right ..)
  have hdst : (g.edges[p.1.1]).dst < g.vertices + g.edges.length :=
    he.2.trans_le (Nat.le_add_right ..)
  constructor
  · exact hnumber hi _
  · change composePosition number p.1.1 _ _ _ < _
    rw [heq]
    rcases impl.query (g.edges[p.1.1]).constraint p.1.2 p.2 with
      ⟨b, r⟩ | q
    · dsimp only [composePosition, Sum.elim_inl]
      split_ifs
      · exact hnumber hsrc _
      · exact hnumber hdst _
    · exact hnumber hi _

/-- Listing each coin and query once lists each composed dart once. -/
theorem nodup_composeDarts (coins : List R) (queries : List Q)
    (g : Graph (α → α → Bool)) (hcoins : coins.Nodup) (hqueries : queries.Nodup) :
    (composeDarts coins queries g).Nodup :=
  (List.nodup_range.product hcoins).product hqueries

open Classical in
/-- Composition retains the ordered edge, coin and query occurrences, even when stored
edge values coincide. -/
noncomputable def composeEnumeration (number : ComposeSlot I P R ≃ Fin width)
    (coins : List R) (queries : List Q) (g : Graph (α → α → Bool))
    (hcoins : coins.Nodup) (hqueries : queries.Nodup)
    (hmemCoins : ∀ ω, ω ∈ coins) (hmemQueries : ∀ i, i ∈ queries) :
    List.Enumeration (compose impl number coins queries g).edges
      (fun p : (Fin g.edges.length × R) × Q =>
        composeEdge impl number (g.edgeAt (fun _ _ => false) p.1.1.val) p.1.1.val p.1.2 p.2) :=
  (((List.Enumeration.range g.edges.length).prod
    (List.Enumeration.ofNodup coins hcoins hmemCoins)).prod
      (List.Enumeration.ofNodup queries hqueries hmemQueries)).map
        (fun p => composeEdge impl number (g.edgeAt (fun _ _ => false) p.1.1) p.1.1 p.1.2 p.2)

/-- Enumerating every coin and query once gives exactly the existing composed graph, with
the specified vertex numbering and the explicit output edge order. -/
theorem toGraph_compose (hreal : impl.Realizes T) [BEq Γ] [LawfulBEq Γ]
    (number : ComposeSlot I P R ≃ Fin width)
    (coins : List R) (queries : List Q) (g : Graph (α → α → Bool))
    (hcoins : coins.Nodup) (hqueries : queries.Nodup)
    (hmemCoins : ∀ ω, ω ∈ coins) (hmemQueries : ∀ i, i ∈ queries) :
    (compose impl number coins queries g).toGraph (composeEval impl) =
      ((T.compose (g.toGraph id)).map (composeVertex number Fin.val)).comap
        (composeEnumeration impl number coins queries g hcoins hqueries
          hmemCoins hmemQueries).equiv := by
  apply toGraph_eq_comap _ _ (composeEnumeration impl number coins queries g hcoins hqueries
    hmemCoins hmemQueries)
  · intro p
    rfl
  · intro p
    simp only [composeEdge, edgeAt, List.getD_eq_get, AssignmentTester.compose,
      LocalTest.toConstraintGraph, AssignmentTester.composeTest,
      LocalTest.mix, LocalTest.map, composeVertex]
    rw [hreal.query_eq, composePosition_eq]
    rfl
  · intro p a b
    simp only [composeEdge, edgeAt, List.getD_eq_get, AssignmentTester.compose,
      LocalTest.toConstraintGraph, AssignmentTester.composeTest, LocalTest.mix, LocalTest.map,
      composeEval, Bool.and_eq_true, beq_iff_eq, hreal.accepts_eq_true,
      toGraph, id_eq]

/-- Exact interpretation and injective numbering preserve the mathematical composition value. -/
theorem unsatVal_compose_eq (hreal : impl.Realizes T) [Fintype R] [Fintype Q] [Nonempty R]
    [Nonempty Γ] [BEq Γ] [LawfulBEq Γ] (number : ComposeSlot I P R ≃ Fin width)
    (coins : List R) (queries : List Q) (g : Graph (α → α → Bool))
    (hcoins : coins.Nodup) (hqueries : queries.Nodup)
    (hmemCoins : ∀ ω, ω ∈ coins) (hmemQueries : ∀ i, i ∈ queries) :
    ((compose impl number coins queries g).toGraph (composeEval impl)).unsatVal =
      (T.compose (g.toGraph id)).unsatVal := by
  rw [toGraph_compose impl hreal number coins queries g hcoins hqueries hmemCoins hmemQueries,
    ConstraintGraph.unsatVal_comap_map_of_injective _
      (composeVertex_injective number Fin.val_injective)]

/-- Full executable composition preserves satisfiability. -/
theorem satisfiable_compose_iff (hreal : impl.Realizes T)
    [Fintype R] [Finite Q] [Nonempty R] [Nonempty Q]
    [Nonempty α] [Nonempty Γ] [BEq Γ] [LawfulBEq Γ]
    (hcomplete : T.IsComplete) {decode : (I → Γ) → α} {δ : ℝ}
    (hsound : T.Sound decode δ) (hδ : 0 < δ) (number : ComposeSlot I P R ≃ Fin width)
    (coins : List R) (queries : List Q) (g : Graph (α → α → Bool))
    (hcoins : coins.Nodup) (hqueries : queries.Nodup)
    (hmemCoins : ∀ ω, ω ∈ coins) (hmemQueries : ∀ i, i ∈ queries) :
    ((compose impl number coins queries g).toGraph (composeEval impl)).Satisfiable ↔
      (g.toGraph id).Satisfiable := by
  let := Fintype.ofFinite Q
  rw [toGraph_compose impl hreal number coins queries g hcoins hqueries hmemCoins hmemQueries,
    ConstraintGraph.satisfiable_comap_map_iff _
      (composeVertex_injective number Fin.val_injective) (Equiv.surjective _),
    AssignmentTester.satisfiable_compose_iff hcomplete hsound hδ]

/-- Executable composition retains the mathematical tester’s quantitative gap bound. -/
theorem le_unsatVal_compose (hreal : impl.Realizes T)
    [Fintype R] [Fintype Q] [Nonempty R] [Nonempty Q]
    [Nonempty Γ] [BEq Γ] [LawfulBEq Γ]
    {decode : (I → Γ) → α} {δ : ℝ} (hsound : T.Sound decode δ) (hδ : 0 < δ)
    (number : ComposeSlot I P R ≃ Fin width)
    (coins : List R) (queries : List Q) (g : Graph (α → α → Bool))
    (hcoins : coins.Nodup) (hqueries : queries.Nodup)
    (hmemCoins : ∀ ω, ω ∈ coins) (hmemQueries : ∀ i, i ∈ queries) :
    (g.toGraph id).unsatVal / (Fintype.card Q / δ) ≤
      ((compose impl number coins queries g).toGraph (composeEval impl)).unsatVal := by
  rw [unsatVal_compose_eq impl hreal number coins queries g hcoins hqueries hmemCoins hmemQueries]
  exact AssignmentTester.le_unsatVal_compose hsound hδ _

/-- Tabulating the output constraints preserves the exact mathematical composition value. -/
theorem unsatVal_composeTabulated_eq (hreal : impl.Realizes T) [Fintype R] [Fintype Q] [Nonempty R]
    [Nonempty Γ] [BEq Γ] [LawfulBEq Γ] (number : ComposeSlot I P R ≃ Fin width)
    (coins : List R) (queries : List Q) (g : Graph (α → α → Bool))
    (hcoins : coins.Nodup) (hqueries : queries.Nodup)
    (hmemCoins : ∀ ω, ω ∈ coins) (hmemQueries : ∀ i, i ∈ queries) :
    ((composeTabulated impl number coins queries g).toGraph id).unsatVal =
      (T.compose (g.toGraph id)).unsatVal := by
  rw [composeTabulated, unsatVal_mapConstraints]
  exact unsatVal_compose_eq impl hreal number coins queries g hcoins hqueries hmemCoins hmemQueries

/-- Tabulated full composition preserves satisfiability. -/
theorem satisfiable_composeTabulated_iff (hreal : impl.Realizes T)
    [Fintype R] [Finite Q] [Nonempty R] [Nonempty Q]
    [Nonempty α] [Nonempty Γ] [BEq Γ] [LawfulBEq Γ]
    (hcomplete : T.IsComplete) {decode : (I → Γ) → α} {δ : ℝ}
    (hsound : T.Sound decode δ) (hδ : 0 < δ) (number : ComposeSlot I P R ≃ Fin width)
    (coins : List R) (queries : List Q) (g : Graph (α → α → Bool))
    (hcoins : coins.Nodup) (hqueries : queries.Nodup)
    (hmemCoins : ∀ ω, ω ∈ coins) (hmemQueries : ∀ i, i ∈ queries) :
    ((composeTabulated impl number coins queries g).toGraph id).Satisfiable ↔
      (g.toGraph id).Satisfiable := by
  let := Fintype.ofFinite Q
  rw [composeTabulated, satisfiable_mapConstraints_iff]
  exact satisfiable_compose_iff impl hreal hcomplete hsound hδ number coins queries g
    hcoins hqueries hmemCoins hmemQueries

end Implementation

end AssignmentTester

end Cslib.PCP
