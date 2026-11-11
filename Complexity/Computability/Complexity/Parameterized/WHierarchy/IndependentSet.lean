/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Parameterized.WHierarchy
public import Complexity.Computability.Complexity.Problems.IndependentSet
public import Complexity.Computability.Complexity.Problems.Clique
public import Complexity.Computability.Circuit.Encoding.Evaluation
import Complexity.Computability.Circuit.Encoding.Layer
import Complexity.Computability.Complexity.Parameterized.Clique
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# Independent Set and Clique are in `W[1]`

The circuit of a graph (`IndependentSet.toCircuit`) has one input for each distinct declared vertex,
read as membership in a set of vertices. It negates every input, takes for every edge the
disjunction of the negations of its two ends, and outputs the conjunction of these disjunctions.
So it outputs `true` exactly when no edge has both ends in the set, and it has a satisfying input
with `k` ones exactly when the graph has an independent set of `k` vertices
(`IndependentSet.toCircuit_satisfiableWithWeight_iff`). Its only large gate is the final
conjunction, so it has weft at most `1`, and it has depth at most `3`. Building it is
polynomial-time, so `IndependentSet` fpt-reduces to `WCS 1 3` and is in `W[1]`
[Cygan et al., Section 13.3][CyganEtAl2015]. `Clique` fpt-reduces to `IndependentSet` by
complementing the graph, so it is in `W[1]` too.

## Main definitions

* `Cslib.Complexity.IndependentSet.edgeIndices`: the edges of a graph as pairs of positions of
  distinct vertices.
* `Cslib.Complexity.IndependentSet.circuitGates`, `Cslib.Complexity.IndependentSet.toCircuit`: the
  circuit of a graph.
* `Cslib.Complexity.IndependentSet.toWCS`: the instance of `WCS 1 3` of a graph and a target.

## Main results

* `Cslib.Complexity.IndependentSet.toCircuit_satisfiableWithWeight_iff`: the circuit has a
  satisfying input with `k` ones exactly when the graph has an independent set of `k` vertices.
* `Cslib.Complexity.IndependentSet.weft_toCircuit_le`,
  `Cslib.Complexity.IndependentSet.depth_toCircuit_le`: weft at most `1` and depth at most `3`.
* `Cslib.Complexity.IndependentSet.fptReducible_WCS`: `IndependentSet` fpt-reduces to `WCS 1 3`.
* `Cslib.Complexity.IndependentSet_mem_W`, `Cslib.Complexity.Clique_mem_W`: both problems are in
  `W[1]`.

## References

* [M. Cygan et al., *Parameterized Algorithms*, Section 13.3][CyganEtAl2015]
-/

@[expose] public section

namespace Cslib.Complexity

open Circuits Circuits.Boolean Turing.MultiTapeTM

namespace IndependentSet

/-- The edges of `G` between distinct declared vertices, as pairs of positions in
`G.distinctVertices`. -/
def edgeIndices (G : Graph) : List (ℕ × ℕ) :=
  (G.2.filter fun e => decide (e.1 ∈ G.1 ∧ e.2 ∈ G.1 ∧ e.1 ≠ e.2)).map fun e =>
    (G.distinctVertices.idxOf e.1, G.distinctVertices.idxOf e.2)

/-- The gates of the circuit on `n` inputs for the edges `E`: the negation of every input, the
disjunction of the negations of the two ends of every edge, and the conjunction of these
disjunctions. -/
def circuitGates (n : ℕ) (E : List (ℕ × ℕ)) : List (Unbounded.Op × List ℕ) :=
  (List.range n).map (fun i => (.not, [i])) ++
    E.map (fun e => (.or 2, [n + e.1, n + e.2])) ++
    [(.and E.length, (List.range E.length).map (n + n + ·))]

/-- The code of the circuit of `G`: its gates, and as output the final conjunction. -/
def circuitCode (G : Graph) : List (Unbounded.Op × List ℕ) × List ℕ :=
  (circuitGates G.distinctVertices.length (edgeIndices G),
    [G.distinctVertices.length + G.distinctVertices.length + (edgeIndices G).length])

/-- The positions in `edgeIndices G` are positions of distinct declared vertices. -/
theorem lt_of_mem_edgeIndices {G : Graph} {e : ℕ × ℕ} (he : e ∈ edgeIndices G) :
    e.1 < G.distinctVertices.length ∧ e.2 < G.distinctVertices.length := by
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.1 he
  simp only [List.mem_filter, decide_eq_true_eq] at hab
  exact ⟨List.idxOf_lt_length_iff.2 (Graph.mem_distinctVertices.2 hab.2.1),
    List.idxOf_lt_length_iff.2 (Graph.mem_distinctVertices.2 hab.2.2.1)⟩

/-- The gates of the circuit read only inputs and earlier gates, with as many arguments as their
arities. -/
theorem isCodeFrom_circuitGates {n : ℕ} {E : List (ℕ × ℕ)} (hE : ∀ e ∈ E, e.1 < n ∧ e.2 < n) :
    Program.IsCodeFrom Unbounded.signature n 0 (circuitGates n E) := by
  rw [circuitGates, Program.isCodeFrom_append, Program.isCodeFrom_append]
  refine ⟨⟨Program.isCodeFrom_of_forall ?_, Program.isCodeFrom_of_forall ?_⟩,
    Program.isCodeFrom_of_forall ?_⟩
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
    simp only [List.mem_range] at hi
    exact ⟨rfl, by simp only [List.mem_singleton]; omega⟩
  · intro g hg
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hg
    have := hE e he
    simp only [List.length_map, List.length_range]
    exact ⟨rfl, by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega⟩
  · intro g hg
    simp only [List.mem_singleton] at hg
    subst hg
    refine ⟨by simp, ?_⟩
    simp only [List.length_append, List.length_map, List.length_range, List.mem_map,
      List.mem_range]
    rintro _ ⟨j, hj, rfl⟩
    omega

/-- The code of the circuit of a graph decodes to a circuit. -/
theorem isSome_ofCode_circuitCode (G : Graph) :
    (Circuit.ofCode G.distinctVertices.length 1 (circuitCode G) :
      Option (Circuit Unbounded.signature _ 1)).isSome := by
  rw [Circuit.isSome_ofCode_iff]
  refine ⟨isCodeFrom_circuitGates fun e he => lt_of_mem_edgeIndices he, rfl, ?_⟩
  simp only [circuitCode, circuitGates, List.mem_singleton, forall_eq, List.length_append,
    List.length_map, List.length_range, List.length_singleton]
  omega

/-- **The circuit of a graph**: one input for each distinct declared vertex, and the gates of
`circuitCode`. -/
def toCircuit (G : Graph) : Σ n, Circuit Unbounded.signature n 1 :=
  ⟨G.distinctVertices.length,
    (Circuit.ofCode _ 1 (circuitCode G)).get (isSome_ofCode_circuitCode G)⟩

/-- The code of the circuit of `G` is `circuitCode G`. -/
theorem code_toCircuit (G : Graph) : (toCircuit G).2.code = circuitCode G :=
  Circuit.code_of_ofCode_eq_some (Option.some_get _).symm

/-- **Evaluating the gates.** On inputs `x`, the final conjunction is `true` exactly when no edge
of `E` has both ends `true`. -/
theorem evalCode_circuitGates {n : ℕ} {E : List (ℕ × ℕ)} (hE : ∀ e ∈ E, e.1 < n ∧ e.2 < n)
    (x : List Bool) (hx : x.length = n) :
    (evalCode Unbounded.interpretation false x (circuitGates n E)).getD (n + n + E.length) false =
      decide (∀ e ∈ E, ¬(x.getD e.1 false = true ∧ x.getD e.2 false = true)) := by
  subst hx
  rw [circuitGates, evalCode_append, evalCode_append]
  have h1 : evalCode Unbounded.interpretation false x
      ((List.range x.length).map fun i => (Unbounded.Op.not, [i])) = x ++ x.map (!·) := by
    rw [evalCode_layer]
    · simp only [List.map_map]
      congr 1
      refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
      simp only [List.length_map, List.length_range] at h₁
      simp [List.getElem?_eq_getElem h₁]
    · intro g hg i hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
      simp only [List.mem_range] at hj
      simp only [List.mem_singleton] at hi
      omega
  have h2 : evalCode Unbounded.interpretation false (x ++ x.map (!·))
      (E.map fun e => (Unbounded.Op.or 2, [x.length + e.1, x.length + e.2])) =
      (x ++ x.map (!·)) ++ E.map fun e => (!x.getD e.1 false || !x.getD e.2 false) := by
    rw [evalCode_layer]
    · simp only [List.map_map]
      congr 1
      refine List.map_congr_left fun e he => ?_
      obtain ⟨h₁, h₂⟩ := hE e he
      simp [List.getElem?_append_right, List.getElem?_eq_getElem h₁,
        List.getElem?_eq_getElem h₂, Fin.exists_fin_two]
    · intro g hg i hi
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hg
      obtain ⟨h₁, h₂⟩ := hE e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      simp only [List.length_append, List.length_map]
      omega
  rw [h1, h2, evalCode_layer]
  · have hlen : (x ++ x.map (!·) ++
        E.map fun e => (!x.getD e.1 false || !x.getD e.2 false)).length =
        x.length + x.length + E.length := by
      simp only [List.length_append, List.length_map]
    rw [← hlen, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
    simp only [List.map_singleton, List.getD_cons_zero, Unbounded.interpretation_and]
    rw [decide_eq_decide, List.forall_mem_iff_getElem, Fin.forall_iff]
    refine forall_congr' fun j => forall_congr' fun hj => ?_
    rw [List.getElem?_eq_getElem (by simpa using hj)]
    simp only [Option.elim_some, List.getElem_map, List.getElem_range]
    rw [show x.length + x.length + j = (x ++ x.map (!·)).length + j by simp,
      List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
    cases x.getD E[j].1 false <;> cases x.getD E[j].2 false <;> decide
  · intro g hg i hi
    simp only [List.mem_singleton] at hg
    subst hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
    simp only [List.mem_range] at hj
    simp only [List.length_append, List.length_map]
    omega

/-- The circuit of `G` has one input for each distinct declared vertex. -/
theorem toCircuit_fst (G : Graph) : (toCircuit G).1 = G.distinctVertices.length := rfl

/-- The circuit of `G` outputs `true` exactly when no edge has both ends `true`. -/
theorem eval_toCircuit (G : Graph) (x : BitString (toCircuit G).1) :
    (toCircuit G).2.eval Unbounded.interpretation x 0 =
      decide (∀ e ∈ edgeIndices G, ¬((List.ofFn x).getD e.1 false = true ∧
        (List.ofFn x).getD e.2 false = true)) := by
  have hout : ((toCircuit G).2.outputs 0).toNat =
      G.distinctVertices.length + G.distinctVertices.length + (edgeIndices G).length :=
    congrArg (fun c => c.2.headD 0) (code_toCircuit G)
  rw [Circuit.eval_eq_getD _ _ false, hout, code_toCircuit]
  exact evalCode_circuitGates (fun e he => lt_of_mem_edgeIndices he) _ (List.length_ofFn)

/-- The declared vertices at the positions where `x` is `true`. -/
private def vertexSet (G : Graph) (x : BitString (toCircuit G).1) : Finset ℕ :=
  (Finset.univ.filter fun i => x i = true).map
    ⟨fun i => G.distinctVertices[i.val]'(i.isLt.trans_eq (toCircuit_fst G)), fun _ _ h =>
      Fin.ext ((List.Nodup.getElem_inj_iff G.nodup_distinctVertices).1 h)⟩

private theorem mem_vertexSet {G : Graph} {x : BitString (toCircuit G).1} {v : ℕ} :
    v ∈ vertexSet G x ↔ ∃ h : v ∈ G.1,
      x ⟨G.distinctVertices.idxOf v,
        List.idxOf_lt_length_iff.2 (Graph.mem_distinctVertices.2 h)⟩ = true := by
  simp only [vertexSet, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨Graph.mem_distinctVertices.1 (List.getElem_mem _), ?_⟩
    convert hi using 2
    exact Fin.ext (G.nodup_distinctVertices.idxOf_getElem _ _)
  · rintro ⟨hv, hx⟩
    exact ⟨_, hx, List.getElem_idxOf _⟩

private theorem edgeIndices_iff (G : Graph) (x : BitString (toCircuit G).1) :
    (∀ e ∈ edgeIndices G, ¬((List.ofFn x).getD e.1 false = true ∧
      (List.ofFn x).getD e.2 false = true)) ↔
      G.toSimpleGraph.IsIndepSet (vertexSet G x : Set ℕ) := by
  have hget : ∀ a (ha : a ∈ G.1), (List.ofFn x).getD (G.distinctVertices.idxOf a) false =
      x ⟨G.distinctVertices.idxOf a,
        List.idxOf_lt_length_iff.2 (Graph.mem_distinctVertices.2 ha)⟩ := fun a ha => by
    rw [List.getD_eq_getElem _ _ (by
      rw [List.length_ofFn]
      exact List.idxOf_lt_length_iff.2 (Graph.mem_distinctVertices.2 ha)),
      List.getElem_ofFn]
  rw [SimpleGraph.isIndepSet_iff]
  constructor
  · intro h u hu v hv huv hadj
    obtain ⟨hu₁, hu₂⟩ := mem_vertexSet.1 (Finset.mem_coe.1 hu)
    obtain ⟨hv₁, hv₂⟩ := mem_vertexSet.1 (Finset.mem_coe.1 hv)
    obtain ⟨-, hadj⟩ := Graph.toSimpleGraph_adj.1 hadj
    rcases hadj with he | he
    · refine h _ (List.mem_map.2 ⟨(u, v), List.mem_filter.2 ⟨he, ?_⟩, rfl⟩) ?_
      · simpa using ⟨hu₁, hv₁, huv⟩
      · exact ⟨(hget u hu₁).trans hu₂, (hget v hv₁).trans hv₂⟩
    · refine h _ (List.mem_map.2 ⟨(v, u), List.mem_filter.2 ⟨he, ?_⟩, rfl⟩) ?_
      · simpa using ⟨hv₁, hu₁, Ne.symm huv⟩
      · exact ⟨(hget v hv₁).trans hv₂, (hget u hu₁).trans hu₂⟩
  · rintro h e he ⟨h₁, h₂⟩
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.1 he
    simp only [List.mem_filter, decide_eq_true_eq] at hab
    obtain ⟨hab, ha, hb, hne⟩ := hab
    dsimp only at h₁ h₂
    rw [hget a ha] at h₁
    rw [hget b hb] at h₂
    exact h (Finset.mem_coe.2 (mem_vertexSet.2 ⟨ha, h₁⟩))
      (Finset.mem_coe.2 (mem_vertexSet.2 ⟨hb, h₂⟩)) hne
      (Graph.toSimpleGraph_adj.2 ⟨hne, Or.inl hab⟩)

/-- **Correctness of the circuit.** The circuit of `G` has a satisfying input with `k` ones exactly
when `G` has an independent set of `k` declared vertices. -/
theorem toCircuit_satisfiableWithWeight_iff (G : Graph) (k : ℕ) :
    (toCircuit G).2.SatisfiableWithWeight Unbounded.interpretation k ↔
      (G, k) ∈ IndependentSet := by
  rw [mem_IndependentSet_iff]
  constructor
  · rintro ⟨x, hk, hx⟩
    rw [eval_toCircuit, decide_eq_true_eq, edgeIndices_iff] at hx
    refine ⟨vertexSet G x, fun v hv => (mem_vertexSet.1 hv).1, hx, ?_⟩
    exact (Finset.card_map _).trans hk
  · rintro ⟨S, hS, hind, hk⟩
    let x : BitString (toCircuit G).1 := fun i =>
      decide (G.distinctVertices[i.val]'(i.isLt.trans_eq (toCircuit_fst G)) ∈ S)
    have hvS : vertexSet G x = S := by
      ext v
      rw [mem_vertexSet]
      constructor
      · rintro ⟨hv, hx⟩
        simp only [x, decide_eq_true_eq] at hx
        rwa [List.getElem_idxOf] at hx
      · intro hv
        refine ⟨hS v hv, ?_⟩
        simp only [x, decide_eq_true_eq]
        rwa [List.getElem_idxOf]
    refine ⟨x, ?_, ?_⟩
    · rw [← hk, ← hvS]
      exact (Finset.card_map _).symm
    · rw [eval_toCircuit, decide_eq_true_eq, edgeIndices_iff, hvS]
      exact hind

/-- The values that the circuit computes in the depth interpretation, from zero inputs, are at most
the sum of bounds on the costs of its three layers. -/
private theorem le_of_mem_evalCode_circuitGates (cost : Unbounded.Op → ℕ) {n : ℕ}
    {E : List (ℕ × ℕ)} (hE : ∀ e ∈ E, e.1 < n ∧ e.2 < n) {c₁ c₂ c₃ : ℕ}
    (h₁ : cost Unbounded.Op.not ≤ c₁) (h₂ : cost (Unbounded.Op.or 2) ≤ c₂)
    (h₃ : cost (Unbounded.Op.and E.length) ≤ c₃) :
    ∀ v ∈ evalCode (depthInterpretation (σ := Unbounded.signature) cost) 0 (List.replicate n 0)
      (circuitGates n E),
      v ≤ 0 + c₁ + c₂ + c₃ := by
  rw [circuitGates, evalCode_append, evalCode_append]
  refine le_of_mem_evalCode_depth_layer _ _ _ ?_ (le_of_mem_evalCode_depth_layer _ _ _ ?_
    (le_of_mem_evalCode_depth_layer _ _ _ ?_ ?_ ?_) ?_) ?_
  · intro g hg i hi
    simp only [List.mem_singleton] at hg
    subst hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
    simp only [List.mem_range] at hj
    simp only [length_evalCode, List.length_replicate, List.length_map, List.length_range]
    omega
  · intro g hg i hi
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hg
    obtain ⟨he₁, he₂⟩ := hE e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [length_evalCode, List.length_replicate, List.length_map, List.length_range]
    omega
  · intro g hg i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
    simp only [List.mem_range] at hj
    simp only [List.mem_singleton] at hi
    simp only [List.length_replicate]
    omega
  · intro v hv
    exact (List.eq_of_mem_replicate hv).le
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
    exact h₁
  · intro g hg
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hg
    exact h₂
  · intro g hg
    simp only [List.mem_singleton] at hg
    subst hg
    exact h₃

/-- The circuit of a graph has weft at most `1`: its only large gate is the final conjunction. -/
theorem weft_toCircuit_le (G : Graph) : (toCircuit G).2.weft ≤ 1 := by
  refine Circuit.depthWith_le_of_evalCode _ _ fun v hv => ?_
  rw [code_toCircuit] at hv
  have := le_of_mem_evalCode_circuitGates (largeGateCost Unbounded.signature)
    (fun e he => lt_of_mem_edgeIndices he) (c₁ := 0) (c₂ := 0) (by decide) (by decide)
    (largeGateCost_le_one _) v hv
  omega

/-- The circuit of a graph has depth at most `3`. -/
theorem depth_toCircuit_le (G : Graph) : (toCircuit G).2.depth ≤ 3 := by
  rw [← Circuit.depthWith_one]
  refine Circuit.depthWith_le_of_evalCode _ _ fun v hv => ?_
  rw [code_toCircuit] at hv
  have := le_of_mem_evalCode_circuitGates 1 (fun e he => lt_of_mem_edgeIndices he) le_rfl le_rfl
    le_rfl v hv
  simpa using this

/-- Listing the positions of the ends of the edges is polynomial-time. -/
theorem computableInPolyTime_edgeIndices :
    ComputableInPolyTime edgeIndices encGraph (encList (encPair encUnary encUnary)) := by
  unfold edgeIndices
  fun_prop

/-- Writing the code of the circuit of a graph is polynomial-time. -/
theorem computableInPolyTime_circuitCode :
    ComputableInPolyTime circuitCode encGraph (Circuit.encCode Unbounded.encOp) := by
  have hE := computableInPolyTime_edgeIndices
  have hV := Graph.computableInPolyTime_distinctVertices
  have hm : ComputableInPolyTime (fun G : Graph => (edgeIndices G).length) encGraph encUnary := by
    fun_prop
  have hnot : ComputableInPolyTime
      (fun G : Graph => (List.range G.distinctVertices.length).map
        fun i => ((Unbounded.Op.not, [i]) : Unbounded.Op × List ℕ))
      encGraph (encList (Circuit.encGate Unbounded.encOp)) := by
    have hb := ComputableInPolyTime.unary_to_binary
    fun_prop
  have hb := ComputableInPolyTime.unary_to_binary
  have hor : ComputableInPolyTime
      (fun G : Graph => (edgeIndices G).map fun e =>
        ((Unbounded.Op.or 2, [G.distinctVertices.length + e.1, G.distinctVertices.length + e.2]) :
          Unbounded.Op × List ℕ))
      encGraph (encList (Circuit.encGate Unbounded.encOp)) := by
    refine ComputableInPolyTime.mapWithInput hE ?_
    have hop : ComputableInPolyTime (fun _ : Graph × (ℕ × ℕ) => Unbounded.Op.or 2)
        (encPair encGraph (encPair encUnary encUnary)) Unbounded.encOp :=
      ComputableInPolyTime.const _
    have h₁ : ComputableInPolyTime (fun p : Graph × (ℕ × ℕ) =>
        p.1.distinctVertices.length + p.2.1)
        (encPair encGraph (encPair encUnary encUnary)) encUnary := by
      fun_prop
    have h₂ : ComputableInPolyTime (fun p : Graph × (ℕ × ℕ) =>
        p.1.distinctVertices.length + p.2.2)
        (encPair encGraph (encPair encUnary encUnary)) encUnary := by
      fun_prop
    exact hop.prod (ComputableInPolyTime.cons' (hb.comp h₁)
      (ComputableInPolyTime.cons' (hb.comp h₂) (ComputableInPolyTime.const [])))
  have hand : ComputableInPolyTime
      (fun G : Graph => [((Unbounded.Op.and (edgeIndices G).length,
        (List.range (edgeIndices G).length).map
          (G.distinctVertices.length + G.distinctVertices.length + ·)) :
          Unbounded.Op × List ℕ)])
      encGraph (encList (Circuit.encGate Unbounded.encOp)) := by
    have hop := Unbounded.computableInPolyTime_and.comp hm
    have hargs : ComputableInPolyTime (fun G : Graph =>
        (List.range (edgeIndices G).length).map
          (G.distinctVertices.length + G.distinctVertices.length + ·))
        encGraph (encList encNat) := by
      refine ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hm) ?_
      have h : ComputableInPolyTime (fun p : Graph × ℕ =>
          p.1.distinctVertices.length + p.1.distinctVertices.length + p.2)
          (encPair encGraph encUnary) encUnary := by
        fun_prop
      exact hb.comp h
    exact ComputableInPolyTime.cons' (hop.prod hargs) (ComputableInPolyTime.const [])
  have hsum : ComputableInPolyTime (fun G : Graph => G.distinctVertices.length +
      G.distinctVertices.length + (edgeIndices G).length) encGraph encUnary := by
    fun_prop
  have hout : ComputableInPolyTime
      (fun G : Graph => [G.distinctVertices.length + G.distinctVertices.length +
        (edgeIndices G).length]) encGraph (encList encNat) :=
    ComputableInPolyTime.cons' (hb.comp hsum) (ComputableInPolyTime.const [])
  unfold circuitCode circuitGates
  exact (ComputableInPolyTime.listAppend' (ComputableInPolyTime.listAppend' hnot hor) hand).prod
    hout

/-- **The instance of `WCS 1 3` of a graph and a target**: the circuit of the graph, of weft at most
`1` and depth at most `3`, with the target as weight. -/
def toWCS : Graph × ℕ → WeftCircuit 1 3 × ℕ
  | (G, k) => (⟨toCircuit G, weft_toCircuit_le G, depth_toCircuit_le G⟩, k)

/-- The instance of `WCS 1 3` of `(G, k)` is a yes-instance exactly when `G` has an independent
set of `k` declared vertices. -/
theorem toWCS_mem_WCS_iff (x : Graph × ℕ) : toWCS x ∈ WCS 1 3 ↔ x ∈ IndependentSet :=
  toCircuit_satisfiableWithWeight_iff x.1 x.2

/-- Building the instance of `WCS 1 3` is polynomial-time. -/
theorem computableInPolyTime_toWCS :
    ComputableInPolyTime toWCS (encPair encGraph encNat) (encWCS 1 3) := by
  have hc := computableInPolyTime_circuitCode
  have hV := Graph.computableInPolyTime_distinctVertices
  have h : ComputableInPolyTime
      (fun x : Graph × ℕ => ((x.1.distinctVertices.length, circuitCode x.1), x.2))
      (encPair encGraph encNat)
      (encPair (encPair encUnary (Circuit.encCode Unbounded.encOp)) encNat) := by
    fun_prop
  refine h.of_enc_eq fun x => ?_
  obtain ⟨G, k⟩ := x
  simp only [toWCS, encPair_apply, encWeftCircuit_apply, Circuit.encCircuit_apply,
    code_toCircuit]
  rfl

/-- **`IndependentSet` fpt-reduces to `WCS 1 3`**, by a polynomial-time reduction that keeps the
parameter. -/
theorem fptReducible_WCS :
    FPTReducible (encPair encGraph encNat) (encWCS 1 3) Prod.snd Prod.snd IndependentSet
      (WCS 1 3) :=
  FPTReducible.of_computableInPolyTime computableInPolyTime_toWCS (h := id)
    (fun _ => le_rfl) fun x => (toWCS_mem_WCS_iff x).symm

end IndependentSet

/-- **Independent Set is in `W[1]`** [Cygan et al., Section 13.3][CyganEtAl2015]. -/
theorem IndependentSet_mem_W : IndependentSet ∈ W 1 (encPair encGraph encNat) Prod.snd :=
  ⟨3, IndependentSet.fptReducible_WCS⟩

/-- **Clique is in `W[1]`** [Cygan et al., Section 13.3][CyganEtAl2015]. -/
theorem Clique_mem_W : Clique ∈ W 1 (encPair encGraph encNat) Prod.snd :=
  fptReducible_Clique_IndependentSet.mem_W IndependentSet_mem_W

end Cslib.Complexity
