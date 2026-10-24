/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Encoded.Basic
public import Complexity.Computability.Complexity.Classes.PCP
public import Complexity.Foundations.Data.BitString.List.Binary
public import Complexity.Foundations.Data.BitString.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi

/-!
# Checking an encoded constraint graph with local proof queries

One random word selects an edge by capped binary decoding. A valid index reads fixed-width
blocks for the two endpoints and checks their decoded labels. Padding indices make dummy queries
at zero and accept independently of their answers. Fixed answer-block lengths support independent
repetition. The cap charges arbitrary malformed random words without constructing exponentially
large unary indices. The alphabet decoder and block width are fixed before the runtime graph.

## Main definitions

* `Cslib.PCP.Encoded.Edge.proofQueries`: the bit positions of the two endpoint blocks.
* `Cslib.PCP.Encoded.Graph.edgeVerifier`: the nonadaptive graph verifier.

## Main results

* `Cslib.PCP.Encoded.Graph.polyTime_edgeVerifier`: complete cost certificates for the coin count,
  binary query indices, and verdict on arbitrary inputs.
* `Cslib.PCP.Encoded.Graph.edgeVerifier_accepts`: the exact constraint checked for every proof.
* `Cslib.PCP.Encoded.Graph.accepts_proofOfLabels`: a satisfying labelling gives a finite proof.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 11.
-/

@[expose] public section

namespace Cslib.PCP.Encoded

open Turing.MultiTapeTM Cslib.Complexity

namespace Edge

variable {C α : Type}

/-- Read the two endpoint blocks, retaining both copies when the edge is a loop. -/
def proofQueries (width : ℕ) (edge : Edge C) : List ℕ :=
  (List.range width).map (fun i => width * edge.src + i) ++
    (List.range width).map (fun i => width * edge.dst + i)

/-- Interpret the two blocks of answers, with missing bits defaulting to `false`. -/
def proofVerdict (width : ℕ) (decode : (Fin width → Bool) → α)
    (eval : C → α → α → Bool) (edge : Edge C) (answers : List Bool) : Bool :=
  eval edge.constraint (decode fun i => answers.getD i.val false)
    (decode fun i => answers.getD (width + i.val) false)

/-- A constraint check always requests two blocks of the declared width. -/
@[simp]
theorem length_proofQueries (width : ℕ) (edge : Edge C) :
    (edge.proofQueries width).length = 2 * width := by
  simp [proofQueries, two_mul]

/-- Reading the query list returns exactly the two endpoint bit blocks, including repeated bits. -/
theorem proofVerdict_answers (width : ℕ) (decode : (Fin width → Bool) → α)
    (eval : C → α → α → Bool) (edge : Edge C) (proof : List Bool) :
    edge.proofVerdict width decode eval (PCPVerifier.answers proof (edge.proofQueries width)) =
      eval edge.constraint (decode fun i => proof.getD (width * edge.src + i.val) false)
        (decode fun i => proof.getD (width * edge.dst + i.val) false) := by
  unfold proofVerdict
  congr 1 <;> congr 1 <;> funext i
  · simp [PCPVerifier.answers, proofQueries, List.getElem?_append, i.isLt]
  · simp [PCPVerifier.answers, proofQueries, i.isLt]

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- Query construction is efficient, with positions returned in binary. -/
@[fun_prop]
theorem isPolyTime_proofQueries (width : ℕ) (enc : C ↪ List Bool) :
    ComputableInPolyTime (proofQueries width : Edge C → List ℕ)
      (encoding enc) (encList encNat) := by
  refine .of_tidy ?_
  have h : ComputableTidilyInPolyTime (proofQueries width : Edge C → List ℕ)
      (encoding enc) (encList encUnary) := by
    unfold proofQueries
    fun_prop
  simpa only [List.map_id', Function.comp_def] using
    ComputableTidilyInPolyTime.unary_to_binary.map.comp h

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- A fixed finite decoder and a joint evaluator give an efficient verdict on arbitrary answers. -/
@[fun_prop]
theorem isPolyTime_proofVerdict (width : ℕ) (decode : (Fin width → Bool) → α)
    {enc : C ↪ List Bool} {alphabet : α ↪ List Bool} {eval : C → α → α → Bool}
    (heval : ComputableInPolyTime (fun p : C × α × α => eval p.1 p.2.1 p.2.2)
      (encPair enc (encPair alphabet alphabet)) encBool) :
    ComputableInPolyTime
      (fun p : Edge C × List Bool => p.1.proofVerdict width decode eval p.2)
      (encPair (encoding enc) encBits) encBool := by
  have heval := heval.tidy
  refine .of_tidy ?_
  have hdecode : ComputableTidilyInPolyTime decode (encPi encBool) alphabet := .of_finite _
  unfold proofVerdict
  fun_prop

end Edge

namespace Graph

variable {C α : Type}

/-- Select an edge using bounded binary decoding; indices in the padding range give `none`. -/
def sampleEdge (g : Graph C) (random : List Bool) : Option (Edge C) :=
  g.edges[BitString.boundedBinaryValue g.edges.length random]?

/-- Edge selection charges the graph, the entire random word, and the bounded decoded index. -/
@[fun_prop]
theorem isPolyTime_sampleEdge {Input : Type} {input : Input ↪ List Bool} {enc : C ↪ List Bool}
    {graph : Input → Graph C} {random : Input → List Bool}
    (hgraph : ComputableInPolyTime graph input (encoding enc))
    (hrandom : ComputableInPolyTime random input encBits) :
    ComputableInPolyTime (fun x => (graph x).sampleEdge (random x))
      input (encOption (Edge.encoding enc)) := by
  unfold sampleEdge
  fun_prop

/-- A local verifier with accepting padding; all numeric indices are computed under the edge cap. -/
def edgeVerifier (width : ℕ) (decode : (Fin width → Bool) → α) (eval : C → α → α → Bool) :
    PCPVerifier (Graph C) where
  coins g := Nat.clog 2 g.edges.length
  queries p :=
    (p.1.sampleEdge p.2).elim (List.replicate (2 * width) 0) (Edge.proofQueries width)
  verdict p :=
    (p.1.1.sampleEdge p.1.2).elim true
      (fun edge => edge.proofVerdict width decode eval p.2)

/-- A local check uses the ceiling of the binary logarithm of the edge count. -/
@[simp]
theorem coins_edgeVerifier (width : ℕ) (decode : (Fin width → Bool) → α)
    (eval : C → α → α → Bool) (g : Graph C) :
    (edgeVerifier width decode eval).coins g = Nat.clog 2 g.edges.length := rfl

/-- Every proof word, including short words, determines one consistent label at each vertex. -/
def proofLabels (width : ℕ) (decode : (Fin width → Bool) → α) (proof : List Bool) : ℕ → α :=
  fun vertex => decode fun i => proof.getD (width * vertex + i.val) false

/-- Pack labels at all declared vertices into consecutive fixed-width proof blocks. -/
def proofOfLabels (width vertices : ℕ) (encode : α → Fin width → Bool) (labels : ℕ → α) :
    List Bool :=
  List.ofFn (BitString.blocksEquiv.symm (fun vertex : Fin vertices => encode (labels vertex)))

/-- Every declared vertex recovers its original label from the packed proof. -/
theorem proofLabels_proofOfLabels (width vertices : ℕ)
    (encode : α → Fin width → Bool) (decode : (Fin width → Bool) → α)
    (hdecode : Function.LeftInverse decode encode) (labels : ℕ → α)
    {vertex : ℕ} (hvertex : vertex < vertices) :
    proofLabels width decode (proofOfLabels width vertices encode labels) vertex =
      labels vertex := by
  have h := congrFun (BitString.blocksEquiv.apply_symm_apply
    (fun vertex : Fin vertices => encode (labels vertex))) ⟨vertex, hvertex⟩
  have hbits : (fun i : Fin width =>
      (proofOfLabels width vertices encode labels).getD (width * vertex + i.val) false) =
      encode (labels vertex) := by
    rw [← BitString.ofList_ofFn (BitString.blocksEquiv.symm
      (fun vertex : Fin vertices => encode (labels vertex)))] at h
    funext i
    simpa only [proofOfLabels, BitString.blocksEquiv_apply, BitString.block, BitString.ofList,
      finProdFinEquiv, Equiv.coe_fn_mk, Nat.add_comm] using congrFun h i
  exact (congrArg decode hbits).trans (hdecode _)

/-- The verdict checks the labels determined by the proof at the selected edge. -/
theorem edgeVerifier_accepts (width : ℕ) (decode : (Fin width → Bool) → α)
    (eval : C → α → α → Bool) (g : Graph C) (proof random : List Bool) :
    (edgeVerifier width decode eval).accepts g proof random =
      (g.sampleEdge random).elim true (fun edge =>
        eval edge.constraint (proofLabels width decode proof edge.src)
          (proofLabels width decode proof edge.dst)) := by
  cases h : g.sampleEdge random <;>
    simp [PCPVerifier.accepts, edgeVerifier, h, Edge.proofVerdict_answers, proofLabels]

/-- A single check always uses two blocks, retaining ignored dummy queries on padding indices. -/
@[simp]
theorem length_queries_edgeVerifier (width : ℕ) (decode : (Fin width → Bool) → α)
    (eval : C → α → α → Bool) (g : Graph C) (random : List Bool) :
    ((edgeVerifier width decode eval).queries (g, random)).length = 2 * width := by
  cases h : g.sampleEdge random <;> simp [edgeVerifier, h]

/-- Queries use a declared vertex block or the dummy position zero. -/
theorem query_edgeVerifier_lt (width : ℕ) (decode : (Fin width → Bool) → α)
    (eval : C → α → α → Bool) {g : Graph C} (hg : g.WellFormed) (random : List Bool)
    {index : ℕ} (hindex : index ∈ (edgeVerifier width decode eval).queries (g, random)) :
    index < width * g.vertices + 1 := by
  cases h : g.sampleEdge random with
  | none =>
    simp only [edgeVerifier, h, Option.elim_none] at hindex
    have hzero : index = 0 := (List.mem_replicate.mp hindex).2
    simp [hzero]
  | some edge =>
    have hedge := hg edge (List.mem_of_getElem? h)
    simp only [edgeVerifier, h, Option.elim_some, Edge.proofQueries, List.mem_append,
      List.mem_map, List.mem_range] at hindex
    rcases hindex with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · have hbound := Nat.mul_le_mul_left width (Nat.succ_le_of_lt hedge.1)
      nlinarith
    · have hbound := Nat.mul_le_mul_left width (Nat.succ_le_of_lt hedge.2)
      nlinarith

/-- A satisfying labelling gives a finite proof accepted on every random word. -/
theorem accepts_proofOfLabels (width : ℕ) (encode : α → Fin width → Bool)
    (decode : (Fin width → Bool) → α) (hdecode : Function.LeftInverse decode encode)
    (eval : C → α → α → Bool) {g : Graph C} (hg : g.WellFormed) (labels : ℕ → α)
    (hsat : ∀ edge, (g.toGraph eval).Satisfies labels edge) (random : List Bool) :
    (edgeVerifier width decode eval).accepts g
      (proofOfLabels width g.vertices encode labels) random = true := by
  rw [edgeVerifier_accepts]
  cases h : g.sampleEdge random with
  | none => rfl
  | some edge =>
    have hmem := List.mem_of_getElem? h
    have hedge := hg edge hmem
    dsimp only [Option.elim_some]
    rw [proofLabels_proofOfLabels width g.vertices encode decode hdecode labels hedge.1,
      proofLabels_proofOfLabels width g.vertices encode decode hdecode labels hedge.2]
    obtain ⟨i, hi⟩ := List.get_of_mem hmem
    simpa only [ConstraintGraph.Satisfies, toGraph, hi] using hsat i

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- All verifier functions are polynomial-time, including on random strings of the wrong length. -/
theorem polyTime_edgeVerifier (width : ℕ) (decode : (Fin width → Bool) → α)
    {enc : C ↪ List Bool} {alphabet : α ↪ List Bool} {eval : C → α → α → Bool}
    (heval : ComputableInPolyTime (fun p : C × α × α => eval p.1 p.2.1 p.2.2)
      (encPair enc (encPair alphabet alphabet)) encBool) :
    (edgeVerifier width decode eval).PolyTime (encoding enc) := by
  have heval := heval.tidy
  refine ⟨.of_tidy ?_, .of_tidy ?_, .of_tidy ?_⟩
  · exact ComputableTidilyInPolyTime.unary_to_binary.comp (by
      change ComputableTidilyInPolyTime (fun g : Graph C => Nat.clog 2 g.edges.length)
        (encoding enc) encUnary
      fun_prop)
  · unfold edgeVerifier
    fun_prop
  · unfold edgeVerifier
    fun_prop

end Graph

end Cslib.PCP.Encoded
