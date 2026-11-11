/-
Copyright (c) 2026 Shriya Thakur, Hugo Akitaya, Freddy Stock, and Adriano Corbellino.
All rights reserved. Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Akitaya, Shriya Thakur, Freddy Stock, and Adriano Corbellino
-/
module
-- upstream: candidate


-- Import vertex cover to prove that hitting set is NP hard
public import CslibFrontier.Computability.Complexity.Problems.vertexCover
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length

/-!
# Hitting Set

This module formalizes the Hitting Set decision problem and proves
that it is NP-complete via a polynomial-time reduction from Vertex Cover.

An instance consists of a finite universe U, a collection of subsets
of U, and a target cardinality k. The problem asks whether there
exists a subset of U of cardinality exactly k that intersects every
set in the collection.

## definitions

* `HittingSetInstance`: The type of Hitting Set instances.
* `encHittingSet`: Binary encoding of Hitting Set instances.
* `HittingSet`: The Hitting Set decision problem.
* `HittingSet.verifier`: A verifier for Hitting Set certificates.
* `vertexCoverToHittingSet`: Reduction from Vertex Cover to Hitting Set.

## Theorems

* `HittingSet.isVerifier`: Correctness of the verifier.
* `HittingSet.computableInPolyTime_verifier`: Polynomial-time verification.
* `HittingSet.mem_NP`: Hitting Set belongs to NP.
* `vertexCoverToHittingSet_mem_iff`: Correctness of the reduction.
* `polyTimeReducible_VertexCover_HittingSet`: Polynomial-time reduction.
* `HittingSet_npHard`: Hitting Set is NP-hard.
* `HittingSet_npComplete`: Hitting Set is NP-complete.
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime
/-- A Hitting Set instance consists of a universe (U), a collection of subsets (S),
and a target cardinality (k) -/
structure HittingSetInstance where
  finiteUniverse : List ℕ
  subsets : List (List ℕ)
  k : ℕ

/-- Encode a hitting set instance as a bit string with a universe, collection of subsets,
and cardinality in the given order -/
enc_structure encHittingSet : HittingSetInstance where
  finiteUniverse : (encList encNat), subsets : (encList (encList encNat)), k : encNat


/-- Instances admitting a hitting set of exactly k elements from the universe. -/
def HittingSet : Set HittingSetInstance := {x | ∃ H : Finset {u // u ∈ x.finiteUniverse},
  -- for all subsets of S atleast 1 element of H belongs to S
  H.card = x.k ∧ ∀ S ∈ x.subsets, ∃ u ∈ H, (u : ℕ) ∈ S}

-- sets = [[1, 2], [2, 3], [3, 4]]
-- selected = [2, 3]
-- isHittingSet will give true here

/-- Check that the selected elements intersect every subset. -/
def isHittingSet (sets : List (List ℕ)) (selected : List ℕ) : Bool :=
  sets.all (fun S => S.any (fun u => selected.contains u))

/-- Verify a Hitting Set certificate by selecting universe elements
and checking its card and intersection with every subset. -/
def HittingSet.verifier : HittingSetInstance × List Bool → Bool :=
  subsetVerifier (fun x => x.finiteUniverse) fun y =>
    decide (y.2.length = y.1.k) &&
    isHittingSet y.1.subsets y.2

/-- Proves that isHittingSet returns true exactly when the selected elements hit every subset -/
theorem isHittingSet_eq_true_iff (sets : List (List ℕ)) (selected : List ℕ) :
isHittingSet sets selected = true ↔
∀ S ∈ sets, ∃ u ∈ selected, u ∈ S := by
  unfold isHittingSet
  -- convert boolean all checks into universal quantifier
  simp only [List.all_eq_true]
  -- similarly for exists
  simp only [List.any_eq_true]
  -- and contains checks into a prop of element membership
  simp only [List.contains_iff_mem]
  simp only [and_comm]

/-- A hitting set can be represented as a finite set of elements from U or a finite set
-- of nats whose elements are all in the universe
-- This lemma later helps us use Finset N witnesses instead of manipulating subtype elem
-- which helps make the verifier correctness proof and
reduction from vertex cover easier to express. -/
theorem mem_HittingSet_iff (x : HittingSetInstance) : x ∈ HittingSet ↔ ∃ H : Finset ℕ,
(∀ u ∈ H, u ∈ x.finiteUniverse) ∧ H.card = x.k ∧ (∀ S ∈ x.subsets, ∃ u ∈ H, u ∈ S) := by
  unfold HittingSet
  simp only [Set.mem_ofPred_eq]
  -- convert a finite set of subtype elements into a finite set of nats
  constructor
  · intro h
    obtain ⟨H, hcard, hhit⟩ := h
    -- remove subtyep info from each elem
    let H' : Finset ℕ := H.map (Function.Embedding.subtype _)
    refine ⟨H', ?_, ?_, ?_⟩
    -- every elem of H' belongs to U
    · intro u hu
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hu
      exact v.property
    -- mapping through an embedding preserves cardinality
    · change (H.map (Function.Embedding.subtype _)).card = x.k
      rw [Finset.card_map]
      exact hcard
    -- every subset hit by H is also hit by H'
    · intro S hS
      obtain ⟨u, huH, huS⟩ := hhit S hS
      refine ⟨(u : ℕ), ?_, huS⟩
      exact Finset.mem_map.mpr ⟨u, huH, rfl⟩
  -- reverse: turn a finite set of natural numbers into a fin set whose elem carry proof of
  -- universe membership
  · intro h
    obtain ⟨ H, hmem, hcard, hhit⟩ := h
    -- Attach membership proofs to elements of H, then use hmem to construct elements of type U
    let H' : Finset {u // u ∈ x.finiteUniverse} :=
    H.attach.map
      ⟨fun u => ⟨u.val, hmem u.val u.property⟩,
        by
          intro a b h
          apply Subtype.ext
          exact congrArg
            (fun v : {u // u ∈ x.finiteUniverse} => v.val) h⟩
    refine ⟨H', ?_, ?_⟩
    -- Attachig proofs and mapping through an embedding does not change the # of selected elem
    · change (H.attach.map _).card = x.k
      rw [Finset.card_map, Finset.card_attach]
      exact hcard
    -- every subset hit by H is also hit by H'
    · intro S hS
      obtain ⟨u, huH, huS⟩ := hhit S hS
      -- Use the same elem but with a proof that it is part of U
      refine ⟨⟨u, hmem u huH⟩, ?_, huS⟩
      -- Show that the element belongs to the mapped fin set.
      apply Finset.mem_map.mpr
      refine ⟨⟨u, huH⟩, ?_, ?_⟩
      · exact Finset.mem_attach H ⟨u, huH⟩
      · apply Subtype.ext
        rfl

/-- verifier correctle recognizes the YES instances using cert of length bounded by input size -/
theorem HittingSet.isVerifier : IsVerifier encHittingSet Polynomial.X
  HittingSet.verifier HittingSet := by
  -- Rewrite hitting set membership using Finset N instead of a finite set of subtype elem
  have hset : HittingSet = {x | ∃ H : Finset ℕ,
    (∀ u ∈ H, u ∈ x.finiteUniverse) ∧ H.card = x.k ∧ (∀ S ∈ x.subsets, ∃ u ∈ H, u ∈ S)} :=
  Set.ext fun x => by simpa only [Set.mem_ofPred_eq] using mem_HittingSet_iff x
  rw [hset]
  -- Use the general subset verifier theorem
  -- We need to prove the cert length bound and verifier correctness
  refine isVerifier_subsetVerifier
    -- The cert length is <= length of encoded input
    (fun x => by
      have hlen := length_le_length_encList encNat x.finiteUniverse
      -- poly  x evals to input length
      simp only [Polynomial.eval_X]
      rw [encHittingSet_apply]
      -- definitional eq
      change x.finiteUniverse.length ≤
        ((encPair (encList encNat) (encPair (encList (encList encNat)) encNat))
          (x.finiteUniverse, (x.subsets, x.k))).length
      rw [length_encPair, length_encPair]
      -- simplify proj so omega can use the cert length bound
      change x.finiteUniverse.length ≤  2 * ((encList encNat) x.finiteUniverse).length + 1 +
        (2 * ((encList (encList encNat)) x.subsets).length + 1 + (encNat x.k).length)
      omega)
      -- show that bool verifier accepts only valid hitting sets
    (fun x l hl _ => by
      -- replace bool conjunct and cardinality comparison with a proposition
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      -- replace bool hitting set check w its spec
      rw [isHittingSet_eq_true_iff]
      -- rewrite membership in cert finset as list membership
      simp only [List.mem_toFinset]
      -- Since the selected list has no duplicates its
      -- length = card of finset
      rw [List.toFinset_card_of_nodup hl])

/-- Checking whether a nat belongs to a list is poly time if we can compute
both the list and the elemnt in poly time -/
@[fun_prop]
theorem computableInPolyTime_containsNat : ComputableInPolyTime
  (fun p : List ℕ × ℕ => p.1.contains p.2)
  (encPair (encList encNat) encNat)
  encBool := by
  apply ComputableInPolyTime.contains
  · fun_prop
  · fun_prop

/-- Check whether the selected elements intersect a given subset -/
def hitsSubset (selected : List ℕ) (S : List ℕ) : Bool := S.any (fun u => selected.contains u)

example : hitsSubset [2, 3] [1, 2] = true := by decide

example : hitsSubset [2, 3] [4, 5] = false := by decide

/-- Checking whether selected elements hit one subset is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_hitsSubset :
ComputableInPolyTime
  (fun p : List ℕ × List ℕ => hitsSubset p.1 p.2)
  (encPair (encList encNat) (encList encNat))
  encBool := by
  unfold hitsSubset
  fun_prop

/-- Checking whether selected elements hit every subset is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_isHittingSet : ComputableInPolyTime
  (fun p : List (List ℕ) × List ℕ =>
      isHittingSet p.1 p.2)
  (encPair (encList (encList encNat)) (encList encNat))
  encBool := by
  unfold isHittingSet
  fun_prop

-- #check Turing.MultiTapeTM.ComputableTidilyInPolyTime.allWith
-- #check Turing.MultiTapeTM.ComputableTidilyInPolyTime.anyWith

/-- The Hitting Set verifier runs in polynomial time.
-- We do this by proving the complexity of the verifier by composing smaller
-- poly time computations -/
@[fun_prop]
theorem HittingSet.computableInPolyTime_verifier : ComputableInPolyTime HittingSet.verifier
  (encPair encHittingSet encBits) encBool := by
  unfold HittingSet.verifier
  -- Use the poly time result for subset verification
  -- We must show that extracting the universe and checking
  -- the selected elements are both poly time
  refine computableInPolyTime_subsetVerifier (encγ := encNat) ?_ ?_
  -- Extracting the universe from fro the instance is poly time
  · fun_prop
  -- The verifier does 2 bool checks and we prove that each check is poly time
  · refine bool_and' ?_ ?_
    -- Checking that # of selected elements = k is poly time
    · exact ((length_list_binary encNat).comp (snd _ _)).decide_eq' (by fun_prop)
    -- Extracting the collection of subsets and the selected elements from the verifier
    -- input is poly time
    · have hp : ComputableInPolyTime
          (fun y : HittingSetInstance × List ℕ => (y.1.subsets, y.2))
          (encPair encHittingSet (encList encNat))
          (encPair (encList (encList encNat)) (encList encNat)) := by
        unfold encHittingSet
        fun_prop
      -- compose the extraction with our poly time hitting set checker
      exact computableInPolyTime_isHittingSet.comp hp

/-- Reduce from vertex cover to a hittings set instance.
-- The graphs vertices stay as the universe
-- convert each valid edge into a 2 elem subset and preserve k
-- Covering an edge is equivalent to hitting its corresponding subset. -/
def vertexCoverToHittingSet (x : Graph × ℕ) : HittingSetInstance :=
  let ((vertices, graphEdges), k) := x
  -- vertex cover ignores edges with undeclared endpoints and self loops
  let edges := graphEdges.filter fun (u, v) =>
    decide (u ∈ vertices) &&
    decide (v ∈ vertices) &&
    decide (u ≠ v)
  -- convert each leftover (u, v) into [u, v]
  let subsets := edges.map fun (u, v) => [u, v]
  -- construct hitting set intance using the same target size k
  { finiteUniverse := vertices, subsets := subsets, k := k }

/-- The reduction preserves YES instances
A graph has a vertex cover of size k iff the constructed hitting set
instance has a hitting set sized k. -/
theorem vertexCoverToHittingSet_mem_iff (x : Graph × ℕ) :
  vertexCoverToHittingSet x ∈ HittingSet ↔ x ∈ VertexCover := by
  -- separate Graph and target size k
  obtain ⟨G, k⟩ := x
  -- rewrite both problems using ordinary finite sets of natural numbers
  rw [mem_HittingSet_iff]
  unfold vertexCoverToHittingSet
  dsimp
  rw [mem_VertexCover_iff]
  -- graph adj using edge list
  simp only [Graph.toSimpleGraph_adj]
  -- xpand membership in the filtered and mapped edge list
  simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  -- Forward: hitting set gives us vertex cover
  · rintro ⟨H, hmem, hcard, hhit⟩
    -- Same H as in vertex cover
    -- Mebership in U and cardinality are known
    refine ⟨H, hmem, ?_, hcard⟩
    -- consider ny 2 distinct vertices conn by an edge
    intro u hu v hv ⟨hne, hedge⟩
    -- the edge may appear in either orientation in the graphs edge list
    rcases hedge with hedge | hedge
    -- case 1: (u, v) ∈ graph
    · have hhit_uv := hhit [u, v] (by
        -- show that [u, v] is one of the subsets created by the reduction
        refine ⟨(u, v), ?_, rfl⟩
        exact ⟨hedge, ⟨hu, hv⟩, hne⟩)
      -- Since H hits [u, v] some element w of H is either u or v
      obtain ⟨w, hwH, hwlist⟩ := hhit_uv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hwlist
      -- Either case an endpoint of the edge belongs to H
      rcases hwlist with hwu | hwv
      · exact Or.inl (hwu ▸ hwH)
      · exact Or.inr (hwv ▸ hwH)
    -- case 2: (v, u) ∈ G
    · have hhit_vu := hhit [v, u] (by
      -- show that [v, u] is one of the subsets created by the reduction
      refine ⟨(v, u), ?_, rfl⟩
      exact ⟨hedge, ⟨hv, hu⟩, hne.symm⟩)
      -- Hitting set contains atleast 1 endpoint
      obtain ⟨w, hwH, hwlist⟩ := hhit_vu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hwlist
      -- handle 2 possible endpoints when flipped
      rcases hwlist with hwv | hwu
      · exact Or.inr (hwv ▸ hwH)
      · exact Or.inl (hwu ▸ hwH)
  -- A vertex cover gives us a hitting set
  · rintro ⟨S, hmem, hcover, hcard⟩
    -- use the same set S as the hitting set
    refine ⟨S, hmem, hcard, ?_⟩
    -- Every subset in the constructed instance comes from a valid edge
    -- Extract that and replace the subset w/ its 2 endpoints.
    rintro T ⟨a, ⟨ha, ⟨hu, hv⟩, hne⟩, rfl⟩
    -- Since S is a vertexCover it contains atleast one endpoint of a
    have h := hcover a.1 hu a.2 hv ⟨hne, Or.inl ha⟩
    -- Use whichever endpoint belongs to S as a hitting set witness
    rcases h with h₁ | h₂
    -- when the first endpoint is in S and to the corresponding subset
    · refine ⟨a.1, h₁, ?_⟩
      simp
    -- similarly for when the second is
    · refine ⟨a.2, h₂, ?_⟩
      simp


/-- Converting from vertex cover to hitting set instance is poly time -/
@[fun_prop]
theorem computableInPolyTime_vertexCoverToHittingSet : ComputableInPolyTime vertexCoverToHittingSet
  (encPair encGraph encNat) encHittingSet := by
  unfold vertexCoverToHittingSet
  fun_prop

/-- Vertex Cover reduces to Hitting Set in polynomial time -/
theorem polyTimeReducible_VertexCover_HittingSet : PolyTimeReducible (encPair encGraph encNat)
  encHittingSet VertexCover HittingSet :=
  ⟨vertexCoverToHittingSet,
    computableInPolyTime_vertexCoverToHittingSet,
    fun x => (vertexCoverToHittingSet_mem_iff x).symm⟩

/-- Hitting Set is NP-hard because vertex cover is NP hard and redces to hitting set -/
theorem HittingSet_npHard : NPHard encHittingSet HittingSet :=
  VertexCover_npHard.trans polyTimeReducible_VertexCover_HittingSet

/-- Hitting Set belongs to NP because it has a poly time verifier -/
theorem HittingSet.mem_NP : HittingSet ∈ NP encHittingSet := ⟨Polynomial.X, HittingSet.verifier,
  HittingSet.computableInPolyTime_verifier, HittingSet.isVerifier⟩

/-- Np complete = mebership in NP + NP hard -/
theorem HittingSet_npComplete : NPComplete encHittingSet HittingSet :=
  ⟨HittingSet.mem_NP, HittingSet_npHard⟩

end Cslib.Complexity
