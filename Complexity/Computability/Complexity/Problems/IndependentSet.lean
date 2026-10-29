/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph
public import Complexity.Computability.Complexity.Problems.SAT.PolyTime
public import Complexity.Computability.Complexity.Reduction
public import Complexity.Logics.Propositional.CNF.ModelCount
public import Mathlib.Combinatorics.SimpleGraph.Clique
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives

/-!
# Independent sets

`IndependentSet` is the set of graphs, given by a list of vertices and a list of edges, together
with a number `m`, such that the graph has an independent set of `m` declared vertices [Arora and
Barak, Section 2.4][AroraBarak09]. Graphs are read on their declared vertices through
`Cslib.Complexity.Graph.induced`, and independent sets through `SimpleGraph.IsNIndepSet`.

The reduction `SAT.toIndependentSet` from `SAT` is Karp's: one vertex for each occurrence of a
literal, edges between occurrences in the same clause and between complementary occurrences, and
`m` the number of clauses [Karp1972]. An independent set with one vertex in each clause picks a
literal in each clause without contradictions, which is exactly a satisfying assignment.

Vertices and target sizes use binary encoding (`encNat`). A certificate masks the declared vertex
list at first occurrences so duplicate vertex entries cannot inflate the selected set, and checks
the selected count in binary without unary expansion of `m`. The verifier is an instance of the
subset-witness verifier `Cslib.Complexity.subsetVerifier`, which handles the certificate length.

The same problem as a class of finite structures, closed under isomorphism and without an
encoding, with the target size given by a unary relation, is
`Cslib.Logic.FO.sizedGraph.IndependentSet`. There loops are ignored, edges need not be symmetric,
and the reductions between independent set, clique and vertex cover are quantifier-free
first-order interpretations.

## Main definitions

* `Cslib.Complexity.IndependentSet`.
* `Cslib.Complexity.IndependentSet.verifier`.
* `Cslib.Complexity.SAT.toIndependentSet`.
* `Cslib.Complexity.Graph.indepNum`: the independence number (`G.induced.indepNum`).

## Main results

* `Cslib.Complexity.mem_IndependentSet_iff`: independent sets as subsets of `ℕ` contained in the
  declared vertices.
* `Cslib.Complexity.SAT.toIndependentSet_mem_iff`: `toIndependentSet φ ∈ IndependentSet ↔ φ ∈ SAT`.
* `Cslib.Complexity.SAT.exists_card_add_countUnsat_le`: an independent set of Karp's graph gives an
  assignment satisfying as many clauses.
* `Cslib.Complexity.Graph.le_indepNum_iff`: the independence number is the largest target of
  `IndependentSet`.
* `Cslib.Complexity.SAT.computableInPolyTime_toIndependentSet`: Karp's reduction is
  polynomial-time.
* `Cslib.Complexity.IndependentSet.isVerifier`, `Cslib.Complexity.IndependentSet.mem_NP`:
  `IndependentSet ∈ NP (encPair encGraph encNat)`.
* `Cslib.Complexity.polyTimeReducible_SAT_IndependentSet`,
  `Cslib.Complexity.IndependentSet_npHard`, `Cslib.Complexity.IndependentSet_npComplete`:
  `IndependentSet` is `NP`-complete.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

/-- The graphs with an independent set of `m` of their vertices
[Arora and Barak, Section 2.4][AroraBarak09]. -/
def IndependentSet : Set (Graph × ℕ) :=
  {x | ∃ S : Finset {v // v ∈ x.1.1}, x.1.induced.IsNIndepSet x.2 S}

/-- Membership in `IndependentSet` as a finite set of `m` declared vertices that is independent in
`G.toSimpleGraph`. -/
theorem mem_IndependentSet_iff {G : Graph} {m : ℕ} :
    (G, m) ∈ IndependentSet ↔
      ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ G.1) ∧ G.toSimpleGraph.IsNIndepSet m S := by
  simpa only [IndependentSet, Set.mem_ofPred_eq, SimpleGraph.isNIndepSet_iff,
    SimpleGraph.IsIndepSet, Graph.induced_adj] using
    Graph.exists_subtype_pairwise_iff (P := fun u v => ¬G.toSimpleGraph.Adj u v)

namespace SAT

/-! ### Karp's reduction -/

/-- The vertex of an occurrence. -/
def _root_.Cslib.Logic.PL.Occurrence.vertex (o : Occurrence ℕ) : ℕ := Nat.pair o.1 o.2.1

/-- Two occurrences conflict when they are in the same clause or are complementary. -/
def _root_.Cslib.Logic.PL.Occurrence.Conflict (o o' : Occurrence ℕ) : Prop :=
  (o.1 = o'.1 ∧ o.2.1 ≠ o'.2.1) ∨ (o.2.2.1 = o'.2.2.1 ∧ o.2.2.2 ≠ o'.2.2.2)

instance : DecidableRel Occurrence.Conflict := fun _ _ => by
  unfold Occurrence.Conflict; infer_instance

/-- Karp's reduction from `SAT` to `IndependentSet`. -/
def toIndependentSet (φ : CNF ℕ) : Graph × ℕ :=
  (((occurrences φ).map Occurrence.vertex,
    (occurrences φ).flatMap fun o =>
      ((occurrences φ).filter fun o' => decide (o.Conflict o')).map
        fun o' => (o.vertex, o'.vertex)),
    φ.length)

theorem _root_.Cslib.Logic.PL.Occurrence.Conflict.symm {o o' : Occurrence ℕ}
    (h : o.Conflict o') : o'.Conflict o := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl ⟨h₁.symm, h₂.symm⟩
  · exact Or.inr ⟨h₁.symm, h₂.symm⟩

private theorem _root_.Cslib.Logic.PL.Occurrence.Conflict.ne {o o' : Occurrence ℕ}
    (h : o.Conflict o') : o ≠ o' := by
  rintro rfl
  rcases h with ⟨-, h⟩ | ⟨-, h⟩ <;> exact h rfl

/-- An occurrence is determined by its vertex. -/
private theorem vertex_injOn {φ : CNF ℕ} {o o' : Occurrence ℕ} (ho : o ∈ occurrences φ)
    (ho' : o' ∈ occurrences φ) (h : o.vertex = o'.vertex) : o = o' := by
  obtain ⟨i, j, l⟩ := o
  obtain ⟨i', j', l'⟩ := o'
  simp only [Occurrence.vertex, Nat.pair_eq_pair] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨h₁, h₂, hl⟩ := mem_occurrences.1 ho
  obtain ⟨h₁', h₂', hl'⟩ := mem_occurrences.1 ho'
  simp only at hl hl'
  rw [hl, hl']

/-- In the graph of Karp's reduction, two occurrences are adjacent exactly when they conflict. -/
theorem adj_toIndependentSet_iff {φ : CNF ℕ} {o o' : Occurrence ℕ} (ho : o ∈ occurrences φ)
    (ho' : o' ∈ occurrences φ) :
    (toIndependentSet φ).1.toSimpleGraph.Adj o.vertex o'.vertex ↔ o.Conflict o' := by
  have hedge : ∀ {p p'}, p ∈ occurrences φ → p' ∈ occurrences φ →
      ((p.vertex, p'.vertex) ∈ (toIndependentSet φ).1.2 ↔ p.Conflict p') := by
    intro p p' hp hp'
    simp only [toIndependentSet, List.mem_flatMap, List.mem_map, List.mem_filter,
      decide_eq_true_eq, Prod.mk.injEq]
    constructor
    · rintro ⟨q, hq, q', ⟨hq', hc⟩, h₁, h₂⟩
      rwa [← vertex_injOn hq hp h₁, ← vertex_injOn hq' hp' h₂]
    · intro hc
      exact ⟨p, hp, p', ⟨hp', hc⟩, rfl, rfl⟩
  simp only [Graph.toSimpleGraph_adj, ne_eq, hedge ho ho', hedge ho' ho]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · exact h.symm
  · intro h
    exact ⟨fun hv => h.ne (vertex_injOn ho ho' hv), Or.inl h⟩

/-- **An independent set of Karp's graph gives an assignment satisfying as many clauses**: the
assignment making the chosen positive literals true satisfies the clause of every chosen
occurrence, and distinct chosen occurrences lie in distinct clauses. -/
theorem exists_card_add_countUnsat_le {φ : CNF ℕ} {S : Finset ℕ}
    (hSV : ∀ v ∈ S, v ∈ (toIndependentSet φ).1.1)
    (hS : (toIndependentSet φ).1.toSimpleGraph.IsIndepSet (S : Set ℕ)) :
    ∃ σ : ℕ → Bool, S.card + φ.countUnsat σ ≤ φ.length := by
  classical
  have hocc : ∀ v ∈ S, ∃ o ∈ occurrences φ, o.vertex = v := fun v hv => by
    simpa [toIndependentSet] using hSV v hv
  choose! occ hocc_mem hocc_vertex using hocc
  have hadj : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬(occ u).Conflict (occ v) := by
    intro u hu v hv huv hc
    have := (adj_toIndependentSet_iff (hocc_mem u hu) (hocc_mem v hv)).2 hc
    rw [hocc_vertex u hu, hocc_vertex v hv] at this
    exact hS hu hv huv this
  -- Distinct chosen occurrences lie in distinct clauses.
  have hinj : Set.InjOn (fun v => (occ v).1) S := by
    intro u hu v hv h
    by_contra huv
    refine hadj u hu v hv huv (Or.inl ⟨h, fun hj => huv ?_⟩)
    rw [← hocc_vertex u hu, ← hocc_vertex v hv]
    simp [Occurrence.vertex, h, hj]
  -- The assignment making the chosen positive literals true.
  let σ : ℕ → Bool := fun x => decide (∃ v ∈ S, (occ v).2.2 = (x, true))
  -- It satisfies the clause of every chosen occurrence.
  have hsat : ∀ v ∈ S, ((φ.zipIdx.filter fun c => c.1.eval σ).map Prod.snd).contains
      (occ v).1 = true := by
    intro v hv
    have hov := hocc_mem v hv
    rcases hocc : occ v with ⟨i, j, x, b⟩
    rw [hocc] at hov
    obtain ⟨hi, hj, hl⟩ := mem_occurrences.1 hov
    have hl' : (x, b) = φ[i][j] := hl
    have heval : φ[i].eval σ = true := by
      rw [Clause.eval_eq_true_iff]
      refine ⟨(x, b), by rw [hl']; exact List.getElem_mem hj, ?_⟩
      cases b
      · simp only [σ, decide_eq_false_iff_not, not_exists, not_and]
        intro v' hv' hv'x
        have hne : v ≠ v' := by
          rintro rfl
          rw [hocc] at hv'x
          simp at hv'x
        refine hadj v hv v' hv' hne ?_
        rw [hocc]
        exact Or.inr ⟨by simp [hv'x], by simp [hv'x]⟩
      · simp only [σ, decide_eq_true_eq]
        exact ⟨v, hv, by rw [hocc]⟩
    simp only [List.contains_iff_mem, List.mem_map, List.mem_filter]
    exact ⟨(φ[i], i), ⟨List.mem_zipIdx_iff_getElem?.2 (by simp [hi]), heval⟩, rfl⟩
  refine ⟨σ, ?_⟩
  have hcard : S.card ≤ φ.countP fun c => c.eval σ := by
    calc S.card = (S.image fun v => (occ v).1).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ ((φ.zipIdx.filter fun c => c.1.eval σ).map Prod.snd).toFinset.card := by
          refine Finset.card_le_card fun i hi => ?_
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hi
          exact List.mem_toFinset.2 (List.contains_iff_mem.1 (hsat v hv))
      _ ≤ ((φ.zipIdx.filter fun c => c.1.eval σ).map Prod.snd).length :=
          List.toFinset_card_le _
      _ = φ.countP fun c => c.eval σ := by
          rw [List.length_map, ← List.countP_eq_length_filter]
          conv_rhs => rw [← List.zipIdx_map_fst 0 φ]
          rw [List.countP_map]
          rfl
  have hsplit := List.length_eq_countP_add_countP (fun c : Clause ℕ => c.eval σ) (l := φ)
  have hunsat : φ.countUnsat σ = φ.countP fun c => ¬(c.eval σ = true) := by
    rw [CNF.countUnsat]
    exact List.countP_congr fun c _ => by simp
  omega

/-- **Correctness of Karp's reduction.** A formula is satisfiable exactly when its graph has an
independent set with as many vertices as the formula has clauses. -/
theorem toIndependentSet_mem_iff (φ : CNF ℕ) : toIndependentSet φ ∈ IndependentSet ↔ φ ∈ SAT := by
  rw [mem_IndependentSet_iff]
  constructor
  · rintro ⟨S, hSV, hS⟩
    obtain ⟨σ, hσ⟩ := exists_card_add_countUnsat_le hSV hS.isIndepSet
    have hcard : S.card = φ.length := hS.card_eq
    exact ⟨σ, CNF.countUnsat_eq_zero_iff.1 (by omega)⟩
  · rintro ⟨σ, hσ⟩
    have hcl : ∀ i : Fin φ.length, ∃ j : Fin φ[i].length, σ φ[i][j].1 = φ[i][j].2 := by
      intro i
      obtain ⟨l, hl, hσl⟩ := (Clause.eval_eq_true_iff _ _).1
        ((CNF.eval_eq_true_iff _ _).1 hσ φ[i] (List.getElem_mem i.2))
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
      exact ⟨⟨j, hj⟩, hσl⟩
    choose J hJ using hcl
    let o : Fin φ.length → Occurrence ℕ := fun i => (i, J i, φ[i][J i])
    have ho : ∀ i, o i ∈ occurrences φ := fun i => mem_occurrences.2 ⟨i.2, (J i).2, rfl⟩
    have hoinj : Function.Injective fun i => (o i).vertex := by
      intro i i' h
      simp only [o, Occurrence.vertex, Nat.pair_eq_pair] at h
      exact Fin.ext h.1
    refine ⟨Finset.univ.image fun i => (o i).vertex, fun v hv => ?_, ⟨?_, ?_⟩⟩
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      simp only [toIndependentSet, List.mem_map]
      exact ⟨o i, ho i, rfl⟩
    · intro u hu w hw huw hadj
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨i', -, rfl⟩ := Finset.mem_image.1 hw
      have hii' : i ≠ i' := fun h => huw (by rw [h])
      rcases (adj_toIndependentSet_iff (ho i) (ho i')).1 hadj with ⟨h, -⟩ | ⟨hx, hb⟩
      · exact hii' (Fin.ext h)
      · have h₁ := hJ i
        have h₂ := hJ i'
        simp only [o] at hx hb
        rw [hx] at h₁
        exact hb (h₁.symm.trans h₂)
    · rw [Finset.card_image_of_injective _ hoinj, Finset.card_univ, Fintype.card_fin]
      rfl

/-! ### Polynomial-time reduction -/

/-- Computing the binary vertex label of an occurrence from its unary indices is polynomial-time. -/
@[fun_prop]
theorem _root_.Cslib.Logic.PL.Occurrence.computableInPolyTime_vertex :
    ComputableInPolyTime Occurrence.vertex encOccurrence encNat := by
  unfold Occurrence.vertex encOccurrence Cslib.Logic.PL.encOccurrence
  exact unary_to_binary.comp (by fun_prop)

/-- Testing whether two occurrences conflict is polynomial-time. -/
@[fun_prop]
theorem _root_.Cslib.Logic.PL.Occurrence.computableInPolyTime_conflict :
    ComputableInPolyTime (fun p : Occurrence ℕ × Occurrence ℕ => decide (p.1.Conflict p.2))
      (encPair encOccurrence encOccurrence) encBool := by
  unfold Occurrence.Conflict encOccurrence Cslib.Logic.PL.encOccurrence
  fun_prop

/-- Karp's reduction `toIndependentSet` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toIndependentSet :
    ComputableInPolyTime toIndependentSet encCNF (encPair encGraph encNat) := by
  have hlen : ComputableInPolyTime (fun φ : CNF ℕ => φ.length) encCNF encNat :=
    length_list_binary _
  unfold toIndependentSet encGraph
  fun_prop

end SAT

namespace IndependentSet

/-- The verifier for `IndependentSet`: select distinct declared vertices from the certificate mask,
check that their count equals `m`, and check that no two distinct selected vertices are adjacent. -/
def verifier : (Graph × ℕ) × List Bool → Bool :=
  Graph.verifySubset fun G u v => !G.adjBool u v

/-- `IndependentSet.verifier` verifies `IndependentSet` with certificates as long as the encoded
instance. -/
theorem isVerifier :
    IsVerifier (encPair encGraph encNat) Polynomial.X verifier IndependentSet := by
  have h := Graph.isVerifier_verifySubset (P := fun G u v => ¬G.toSimpleGraph.Adj u v)
    (fun G u v _ => by rw [Bool.not_eq_true', Graph.adjBool_eq_false_iff])
  intro x
  simpa only [IndependentSet, Set.mem_ofPred_eq, SimpleGraph.isNIndepSet_iff,
    SimpleGraph.IsIndepSet, Graph.induced_adj, verifier] using h x

/-- The `IndependentSet` verifier is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier
      (encPair (encPair encGraph encNat) encBits) encBool :=
  Graph.computableInPolyTime_verifySubset (by fun_prop)

/-- `IndependentSet` belongs to `NP`. -/
theorem mem_NP : IndependentSet ∈ NP (encPair encGraph encNat) :=
  ⟨Polynomial.X, verifier, computableInPolyTime_verifier, isVerifier⟩

end IndependentSet

/-- `SAT` reduces to `IndependentSet` in polynomial time via `SAT.toIndependentSet`. -/
theorem polyTimeReducible_SAT_IndependentSet :
    PolyTimeReducible encCNF (encPair encGraph encNat) SAT IndependentSet :=
  ⟨SAT.toIndependentSet, SAT.computableInPolyTime_toIndependentSet,
    fun φ => (SAT.toIndependentSet_mem_iff φ).symm⟩

/-- `IndependentSet` is `NP`-hard. -/
theorem IndependentSet_npHard : NPHard (encPair encGraph encNat) IndependentSet :=
  CookLevin.SAT_npHard.trans polyTimeReducible_SAT_IndependentSet

/-- **`IndependentSet` is NP-complete** [Arora and Barak, Section 2.4][AroraBarak09]. -/
theorem IndependentSet_npComplete : NPComplete (encPair encGraph encNat) IndependentSet :=
  ⟨IndependentSet.mem_NP, IndependentSet_npHard⟩

/-! ### The independence number -/

namespace Graph

/-- The **independence number** of a graph: the largest number of declared vertices that are
pairwise non-adjacent. -/
noncomputable def indepNum (G : Graph) : ℕ := G.induced.indepNum

variable {G : Graph} {k k' : ℕ}

/-- Fewer vertices of an independent set are independent. -/
theorem mem_IndependentSet_of_le (h : (G, k) ∈ IndependentSet) (hk : k' ≤ k) :
    (G, k') ∈ IndependentSet := by
  obtain ⟨S, hS, hcard : S.card = k⟩ := h
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq (hcard ▸ hk)
  exact ⟨T, hS.mono (Finset.coe_subset.2 hTS), hT⟩

/-- The independence number is the size of an independent set. -/
theorem indepNum_mem_IndependentSet (G : Graph) : (G, G.indepNum) ∈ IndependentSet :=
  G.induced.exists_isNIndepSet_indepNum

/-- **The independence number is the largest target of `IndependentSet`.** -/
theorem le_indepNum_iff : k ≤ G.indepNum ↔ (G, k) ∈ IndependentSet :=
  ⟨mem_IndependentSet_of_le G.indepNum_mem_IndependentSet,
    fun ⟨_, hS, (hcard : _ = k)⟩ => hcard ▸ hS.card_le_indepNum⟩

/-- The independence number is at most the number of distinct declared vertices. -/
theorem indepNum_le_card (G : Graph) : G.indepNum ≤ G.1.toFinset.card := by
  rw [indepNum, ← G.induced.cliqueNum_compl, ← G.natCard_vertexSubtype]
  exact G.inducedᶜ.cliqueNum_le_natCard

/-- An independent set has at most as many vertices as the distinct declared vertices. -/
theorem le_card_of_mem_IndependentSet (h : (G, k) ∈ IndependentSet) :
    k ≤ G.1.toFinset.card :=
  (le_indepNum_iff.2 h).trans G.indepNum_le_card

end Graph

end Cslib.Complexity
