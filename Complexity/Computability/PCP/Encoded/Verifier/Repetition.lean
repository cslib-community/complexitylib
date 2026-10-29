/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Encoded.Verifier.Soundness
import Complexity.Probability.BitString.List.All
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log

/-!
# Independent repetitions of the encoded edge verifier

Disjoint coin blocks select independent edges. Every round reads the same number of proof bits,
so its answer block has an explicit fixed offset. All rounds must accept. The repetition count
and alphabet width are fixed before the runtime graph.

## Main definitions

* `Cslib.PCP.Encoded.Graph.repeatedEdgeVerifier`: repeated local graph checking.

## Main results

* `Cslib.PCP.Encoded.Graph.polyTime_repeatedEdgeVerifier`: all repeated-verifier computation is
  polynomial-time on arbitrary random strings and supplied answer words.
* `Cslib.PCP.Encoded.Graph.repeatedEdgeVerifier_accepts`: each answer block preserves its check.
* `Cslib.PCP.Encoded.Graph.acceptProb_repeatedEdgeVerifier`: the exact independent product law.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 11.
-/

@[expose] public section

namespace Cslib.PCP.Encoded.Graph

open Cslib.Complexity Turing.MultiTapeTM

variable {C α : Type}

/-- Run fixed many edge checks on disjoint coin and answer blocks, accepting their conjunction. -/
def repeatedEdgeVerifier (width repeats : ℕ) (decode : (Fin width → Bool) → α)
    (eval : C → α → α → Bool) : PCPVerifier (Graph C) :=
  let single := edgeVerifier width decode eval
  { coins := fun g => repeats * single.coins g
    queries := fun p => (List.range repeats).flatMap fun i =>
      single.queries (p.1, BitString.listRow (single.coins p.1) i p.2)
    verdict := fun p => (List.range repeats).all fun i =>
      single.verdict ((p.1.1, BitString.listRow (single.coins p.1.1) i p.1.2),
        BitString.listRow (2 * width) i p.2) }

/-- Independent checks use one separate coin block per repetition. -/
@[simp]
theorem coins_repeatedEdgeVerifier (width repeats : ℕ) (decode : (Fin width → Bool) → α)
    (eval : C → α → α → Bool) (g : Graph C) :
    (repeatedEdgeVerifier width repeats decode eval).coins g =
      repeats * Nat.clog 2 g.edges.length := rfl

private theorem listRow_flatten_ofFn {count : ℕ} (width : ℕ)
    (rows : Fin count → List Bool) (hlen : ∀ i, (rows i).length = width) (i : Fin count) :
    BitString.listRow width i.val (List.ofFn rows).flatten = rows i := by
  let bits := fun i => BitString.ofList width (rows i)
  have hrows : (fun i => List.ofFn (bits i)) = rows := by
    funext i
    exact BitString.ofFn_ofList (hlen i)
  have hpack : (List.ofFn rows).flatten =
      List.ofFn (BitString.blocksEquiv.symm bits) := by
    rw [BitString.ofFn_blocksEquiv_symm, hrows]
  rw [hpack, BitString.listRow_eq_ofFn, BitString.ofList_ofFn]
  change List.ofFn (BitString.blocksEquiv (BitString.blocksEquiv.symm bits) i) = rows i
  rw [Equiv.apply_symm_apply]
  exact BitString.ofFn_ofList (hlen i)

private theorem listRow_flatMap_range {count : ℕ} (width : ℕ)
    (rows : ℕ → List Bool) (hlen : ∀ i < count, (rows i).length = width) (i : Fin count) :
    BitString.listRow width i.val ((List.range count).flatMap rows) = rows i := by
  have hmap : (List.range count).map rows = List.ofFn (fun i : Fin count => rows i.val) := by
    simpa using (List.ofFn_getElem_eq_map (List.range count) rows).symm
  have hflat : ((List.range count).map rows).flatten = (List.range count).flatMap rows := by
    simp [List.flatten_eq_flatMap, List.flatMap_map]
  rw [← hflat, hmap]
  exact listRow_flatten_ofFn width _ (fun i => hlen i i.isLt) i

/-- Repeated checks retain a fixed answer block even when a selected edge is padding. -/
@[simp]
theorem length_queries_repeatedEdgeVerifier (width repeats : ℕ)
    (decode : (Fin width → Bool) → α) (eval : C → α → α → Bool)
    (g : Graph C) (random : List Bool) :
    ((repeatedEdgeVerifier width repeats decode eval).queries (g, random)).length =
      repeats * (2 * width) := by
  simp [repeatedEdgeVerifier, List.length_flatMap]

/-- Concatenating queries and slicing their answers preserves each individual check. -/
theorem repeatedEdgeVerifier_accepts (width repeats : ℕ) (decode : (Fin width → Bool) → α)
    (eval : C → α → α → Bool) (g : Graph C) (proof random : List Bool) :
    (repeatedEdgeVerifier width repeats decode eval).accepts g proof random =
      (List.range repeats).all (fun i => (edgeVerifier width decode eval).accepts g proof
        (BitString.listRow (Nat.clog 2 g.edges.length) i random)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [PCPVerifier.accepts, repeatedEdgeVerifier, List.all_eq_true]
  refine forall_congr' fun i => forall_congr' fun hi => ?_
  have hrow := listRow_flatMap_range (2 * width)
    (fun i => PCPVerifier.answers proof ((edgeVerifier width decode eval).queries
      (g, BitString.listRow (Nat.clog 2 g.edges.length) i random)))
    (by simp [PCPVerifier.answers]) ⟨i, List.mem_range.mp hi⟩
  apply Iff.of_eq
  simpa only [PCPVerifier.answers, List.map_flatMap, coins_edgeVerifier] using congrArg
    (fun answers => (edgeVerifier width decode eval).verdict
      ((g, BitString.listRow (Nat.clog 2 g.edges.length) i random), answers) = true) hrow

/-- A satisfying labelling is accepted by every repeated check, including on malformed coins. -/
theorem repeated_accepts_proofOfLabels (width repeats : ℕ) (encode : α → Fin width → Bool)
    (decode : (Fin width → Bool) → α) (hdecode : Function.LeftInverse decode encode)
    (eval : C → α → α → Bool) {g : Graph C} (hg : g.WellFormed) (labels : ℕ → α)
    (hsat : ∀ edge, (g.toGraph eval).Satisfies labels edge) (random : List Bool) :
    (repeatedEdgeVerifier width repeats decode eval).accepts g
      (proofOfLabels width g.vertices encode labels) random = true := by
  rw [repeatedEdgeVerifier_accepts, List.all_eq_true]
  exact fun _ _ => accepts_proofOfLabels width encode decode hdecode eval hg labels hsat _

/-- Repetition does not increase the range of proof positions used by one check. -/
theorem query_repeatedEdgeVerifier_lt (width repeats : ℕ)
    (decode : (Fin width → Bool) → α) (eval : C → α → α → Bool)
    {g : Graph C} (hg : g.WellFormed) (random : List Bool) {index : ℕ}
    (hindex : index ∈ (repeatedEdgeVerifier width repeats decode eval).queries (g, random)) :
    index < width * g.vertices + 1 := by
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hindex
  exact query_edgeVerifier_lt width decode eval hg _ hi

/-- Repetition charges construction of every query, every extracted bit block, and every verdict. -/
theorem polyTime_repeatedEdgeVerifier (width repeats : ℕ) (decode : (Fin width → Bool) → α)
    {enc : C ↪ List Bool} {alphabet : α ↪ List Bool} {eval : C → α → α → Bool}
    (heval : ComputableInPolyTime (fun p : C × α × α => eval p.1 p.2.1 p.2.2)
      (encPair enc (encPair alphabet alphabet)) encBool) :
    (repeatedEdgeVerifier width repeats decode eval).PolyTime (encoding enc) := by
  obtain ⟨_, hqueries, hverdict⟩ := polyTime_edgeVerifier width decode heval
  have hclog : ComputableInPolyTime (fun g : Graph C => (edgeVerifier width decode eval).coins g)
      (encoding enc) encUnary :=
    (ComputableInPolyTime.unary_clog_const 2).comp
      ((ComputableInPolyTime.length_list (Edge.encoding enc)).comp (isPolyTime_edges .id'))
  refine ⟨?_, ?_, ?_⟩
  · exact ComputableInPolyTime.unary_to_binary.comp
      (ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const repeats).prod hclog))
  · exact ComputableInPolyTime.flatMapWithInput
      (.const (encOut := encList encUnary) (List.range repeats))
      (hqueries.comp
        (((ComputableInPolyTime.fst _ _).fst').prod
          (ComputableInPolyTime.bitsRowWithInput
            (hclog.comp ((ComputableInPolyTime.fst _ _).fst'))
            (.snd _ _) ((ComputableInPolyTime.fst _ _).snd'))))
  · exact ComputableInPolyTime.allWithInput
      (.const (encOut := encList encUnary) (List.range repeats))
      (hverdict.comp
        ((((ComputableInPolyTime.fst _ _).fst'.fst').prod
          (ComputableInPolyTime.bitsRowWithInput
            (hclog.comp ((ComputableInPolyTime.fst _ _).fst'.fst'))
            (.snd _ _) ((ComputableInPolyTime.fst _ _).fst'.snd'))).prod
          (ComputableInPolyTime.bitsRowWithInput
            (.const (2 * width)) (.snd _ _) ((ComputableInPolyTime.fst _ _).snd'))))

/-- Disjoint random blocks make the repeated acceptance mass the power of the single-check mass. -/
theorem acceptProb_repeatedEdgeVerifier (width repeats : ℕ)
    (decode : (Fin width → Bool) → α) (eval : C → α → α → Bool)
    (g : Graph C) (proof : List Bool) :
    ((BitString.uniformList (repeats * Nat.clog 2 g.edges.length)).map
      (fun random => (repeatedEdgeVerifier width repeats decode eval).accepts g proof random))
        true =
      (((BitString.uniformList (Nat.clog 2 g.edges.length)).map
        (fun random => (edgeVerifier width decode eval).accepts g proof random))
          true) ^ repeats := by
  simpa only [repeatedEdgeVerifier_accepts] using
    BitString.uniformList_all_listRow_true repeats (Nat.clog 2 g.edges.length)
      (fun random => (edgeVerifier width decode eval).accepts g proof random)

/-- Repetition decreases acceptance geometrically in the graph's unsatisfiability gap. -/
theorem acceptProb_repeatedEdgeVerifier_le (width repeats : ℕ)
    (decode : (Fin width → Bool) → α) (eval : C → α → α → Bool)
    (g : Graph C) (proof : List Bool) :
    (((BitString.uniformList (repeats * Nat.clog 2 g.edges.length)).map
      (fun random => (repeatedEdgeVerifier width repeats decode eval).accepts g proof random))
        true).toReal ≤ (1 - (g.toGraph eval).unsatVal / 2) ^ repeats := by
  rw [acceptProb_repeatedEdgeVerifier, ENNReal.toReal_pow]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg
    (acceptProb_edgeVerifier_le width decode eval g proof) _

end Cslib.PCP.Encoded.Graph
