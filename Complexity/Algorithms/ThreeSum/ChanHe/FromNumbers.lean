/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ThreeSum.ChanHe.Recursion

/-!
# Complete finite Chan–He reduction from ordinary integer 3SUM

Adapted from Anthropic's [FromNumbers.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec3/Theorem21a/ChanHe/FromNumbers.lean), lines 261–299 and 396–468,
at `formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
The generic distinct-position frontend and array packing are imported rather than duplicated.
The construction uses only finite sets, deterministic prime searches and bounded recursion.

## Main definitions

* `instances`: finite one-array convolution instances of the ordinary 3SUM input.
* `scanPairs`: the candidate-prime/element count, explicitly not a RAM running time.

## Main results

* `instances_correct`: equivalence for every `n ≥ 1` and every input bounded by `U`.
* `length_instances_le`: at most `(2 * labelBits (2U)^2 + 2) * (2 * log₂ n + 2)^5` instances.
* `abs_instances_le`: every output entry has magnitude at most `120U + 40`.

No native preprocessing, word-width threshold or charged-time claim follows from this module.

## References

* [T. M. Chan and Q. He, *Reducing 3SUM to Convolution-3SUM*][ChanHe2020], Theorem 5.1.
-/

@[expose] public section

namespace Cslib.Algorithms.ThreeSum.ChanHe

open Finset

/-- The one-array convolution instance of a recursion node. -/
def Node.oneArray (ν : Node) (U : ℕ) : ℕ → ℤ :=
  ThreeSum.oneArray (2 * U + 1) (arrXY ν.S₁ ν.M U) (arrXY ν.S₂ ν.M U) (arrZ ν.S₃ ν.M U)

/-- All recursion nodes for the distinct-position frontend's three-set inputs. -/
def allNodes (n U : ℕ) (x : Fin n → ℤ) : List Node :=
  (inputs U x).flatMap fun T => reduction n (2 * U) T.1 T.2.1 T.2.2

/-- The list of one-array convolution instances, each read at length `8 * mPar n (2U)^2`. -/
def instances (n U : ℕ) (x : Fin n → ℤ) : List (ℕ → ℤ) :=
  (allNodes n U x).map fun ν => ν.oneArray (2 * U)

/-- Candidate-prime/element pairs scanned by both searches at all nodes.
This is a combinatorial count, not a charged running time. In particular it omits sieving,
sorting/counting residues, search tests, heavy-element extraction, frontend and array writing.
The mathematical `coll` definition itself enumerates ordered pairs. -/
def scanPairs (n U : ℕ) (x : Fin n → ℤ) : ℕ :=
  ((allNodes n U x).map fun ν =>
    2 * #(Nat.primesLE (mPar n (2 * U))) * (#ν.S₁ + #ν.S₂ + #ν.S₃)).sum

section node

variable {n U : ℕ} {ν : Node}

/-- The entries of the three arrays of a node are bounded by the number `2U + 1` with which its
one-array instance is built. -/
private theorem Node.abs_arr_le (b₁ : Bdd U ν.S₁) (b₂ : Bdd U ν.S₂) (b₃ : Bdd U ν.S₃) :
    (∀ i, |arrXY ν.S₁ ν.M U i| ≤ ((2 * U + 1 : ℕ) : ℤ)) ∧
      (∀ i, |arrXY ν.S₂ ν.M U i| ≤ ((2 * U + 1 : ℕ) : ℤ)) ∧
      ∀ i, |arrZ ν.S₃ ν.M U i| ≤ ((2 * U + 1 : ℕ) : ℤ) := by
  push_cast
  exact ⟨abs_arrXY_le ν.M b₁, abs_arrXY_le ν.M b₂, abs_arrZ_le ν.M b₃⟩

/-- The three-array instance of a node and its one-array instance have the same answer. -/
theorem Node.conv_iff_convolution (b₁ : Bdd U ν.S₁) (b₂ : Bdd U ν.S₂) (b₃ : Bdd U ν.S₃) (N : ℕ) :
    ν.Conv U N ↔ Convolution (4 * N) (ν.oneArray U) :=
  let ⟨hX, hY, hZ⟩ := Node.abs_arr_le b₁ b₂ b₃
  oneArray_correct (fun i _ => hX i) (fun i _ => hY i) (fun i _ => hZ i)

/-- The entries of the one-array instance of a node have absolute value at most `60U + 40`. -/
theorem Node.abs_oneArray_le (b₁ : Bdd U ν.S₁) (b₂ : Bdd U ν.S₂) (b₃ : Bdd U ν.S₃) (u : ℕ) :
    |ν.oneArray U u| ≤ 60 * (U : ℤ) + 40 := by
  obtain ⟨hX, hY, hZ⟩ := Node.abs_arr_le b₁ b₂ b₃
  refine (ThreeSum.abs_oneArray_le (N := u + 1) (fun i _ => hX i) (fun i _ => hY i)
    (fun i _ => hZ i) (by omega)).trans_eq ?_
  push_cast
  ring

/-- `reduction_correct` with one-array instances, read at length `8 * mPar n U ^ 2`. -/
theorem reduction_correct_oneArray (hn : 1 ≤ n) {T₁ T₂ T₃ : Finset ℤ}
    (h : Admissible n U T₁ T₂ T₃) :
    HasThreeSetSolution T₁ T₂ T₃ ↔
      ∃ ν ∈ reduction n U T₁ T₂ T₃, Convolution (8 * mPar n U ^ 2) (ν.oneArray U) := by
  rw [reduction_correct hn le_rfl h, show 8 * mPar n U ^ 2 = 4 * (2 * mPar n U ^ 2) by ring]
  refine exists_congr fun ν => and_congr_right fun hν => ?_
  have hν' := h.of_mem hν
  exact Node.conv_iff_convolution hν'.bdd₁ hν'.bdd₂ hν'.bdd₃ _

end node

variable {n U : ℕ} {x : Fin n → ℤ}

/-- Nodes are exactly the nodes produced by one of the frontend inputs. -/
theorem mem_allNodes_iff {ν : Node} :
    ν ∈ allNodes n U x ↔ ∃ T₁ T₂ T₃, IsInput U x T₁ T₂ T₃ ∧
      ν ∈ reduction n (2 * U) T₁ T₂ T₃ := by
  simp only [allNodes, List.mem_flatMap]
  constructor
  · rintro ⟨⟨T₁, T₂, T₃⟩, hT, hν⟩
    exact ⟨T₁, T₂, T₃, mem_inputs_iff.mp hT, hν⟩
  · rintro ⟨T₁, T₂, T₃, hT, hν⟩
    exact ⟨(T₁, T₂, T₃), mem_inputs_iff.mpr hT, hν⟩

/-- Frontend bounds meet the recursion's cardinality and magnitude hypotheses. -/
theorem admissible_of_input (hn : 1 ≤ n) (hx : ∀ i, |x i| ≤ (U : ℤ))
    {T₁ T₂ T₃ : Finset ℤ} (h : IsInput U x T₁ T₂ T₃) : Admissible n (2 * U) T₁ T₂ T₃ :=
  let ⟨c₁, c₂, c₃, b₁, b₂, b₃⟩ := h.bounds hn hx
  ⟨c₁, c₂, c₃, b₁, b₂, b₃⟩

/-- Each node of the whole reduction has at most `n` elements in each set, of absolute value at
most `2U`. -/
private theorem admissible_of_mem_allNodes (hn : 1 ≤ n) (hx : ∀ i, |x i| ≤ (U : ℤ)) {ν : Node}
    (hν : ν ∈ allNodes n U x) : Admissible n (2 * U) ν.S₁ ν.S₂ ν.S₃ :=
  let ⟨_, _, _, hT, hν'⟩ := mem_allNodes_iff.mp hν
  (admissible_of_input hn hx hT).of_mem hν'


/-! ## The whole reduction -/

/-- **Correctness of the whole reduction.**  Let `x` consist of `n ≥ 1` integers of absolute value
at most `U`.  Then three entries of `x` at different positions sum to 0 iff one of the instances,
read at length `8 * mPar n (2 * U) ^ 2`, has a solution. -/
theorem instances_correct (n U : ℕ) (hn : 1 ≤ n) (x : Fin n → ℤ) (hx : ∀ i, |x i| ≤ (U : ℤ)) :
    HasSolution x ↔ ∃ y ∈ instances n U x, Convolution (8 * mPar n (2 * U) ^ 2) y :=
  calc HasSolution x
      ↔ ∃ T₁ T₂ T₃, IsInput U x T₁ T₂ T₃ ∧ HasThreeSetSolution T₁ T₂ T₃ :=
      threeSum_iff_exists_input hx
    _ ↔ ∃ T₁ T₂ T₃, IsInput U x T₁ T₂ T₃ ∧ ∃ ν ∈ reduction n (2 * U) T₁ T₂ T₃,
          Convolution (8 * mPar n (2 * U) ^ 2) (ν.oneArray (2 * U)) :=
        exists₃_congr fun _ _ _ => and_congr_right fun hT =>
          reduction_correct_oneArray hn (admissible_of_input hn hx hT)
    _ ↔ ∃ ν ∈ allNodes n U x, Convolution (8 * mPar n (2 * U) ^ 2) (ν.oneArray (2 * U)) :=
        ⟨fun ⟨T₁, T₂, T₃, hT, ν, hν, h⟩ => ⟨ν, mem_allNodes_iff.mpr ⟨T₁, T₂, T₃, hT, hν⟩, h⟩,
          fun ⟨ν, hν, h⟩ =>
            let ⟨T₁, T₂, T₃, hT, hν'⟩ := mem_allNodes_iff.mp hν
            ⟨T₁, T₂, T₃, hT, ν, hν', h⟩⟩
    _ ↔ ∃ y ∈ instances n U x, Convolution (8 * mPar n (2 * U) ^ 2) y := by
        simp only [instances, List.mem_map, exists_exists_and_eq_and]

/-- **Number of instances**: at most `(2 (labelBits (2U))² + 2) (2⌊log₂ n⌋ + 2)⁵`. -/
theorem length_instances_le (n U : ℕ) (x : Fin n → ℤ) :
    (instances n U x).length ≤ (2 * labelBits (2 * U) ^ 2 + 2) * (2 * Nat.log 2 n + 2) ^ 5 := by
  set B := (2 * Nat.log 2 n + 2) ^ 5
  calc (instances n U x).length = (allNodes n U x).length := List.length_map _
    _ ≤ (inputs U x).length * B := by
        unfold allNodes
        rw [List.length_flatMap]
        exact (List.sum_le_length_nsmul _ _ fun _ h => by
          obtain ⟨T, _, rfl⟩ := List.mem_map.mp h
          exact length_reduction_le ..).trans_eq (by simp [B, smul_eq_mul])
    _ = (2 * labelBits (2 * U) ^ 2 + 2) * B := by rw [length_inputs]

/-- **Entries of the instances**: they have absolute value at most `120U + 40`. -/
theorem abs_instances_le {n U : ℕ} (hn : 1 ≤ n) {x : Fin n → ℤ} (hx : ∀ i, |x i| ≤ (U : ℤ))
    {y : ℕ → ℤ} (hy : y ∈ instances n U x) (u : ℕ) : |y u| ≤ 120 * (U : ℤ) + 40 := by
  obtain ⟨ν, hν, rfl⟩ := List.mem_map.mp hy
  have hν' := admissible_of_mem_allNodes hn hx hν
  refine (Node.abs_oneArray_le hν'.bdd₁ hν'.bdd₂ hν'.bdd₃ u).trans_eq ?_
  push_cast
  ring

/-- **The searches look at no more than (number of nodes) · 2m · 3n pairs.**  This bounds the count
`scanPairs`, which we define; it is not a running time. -/
theorem scanPairs_le {n U : ℕ} (hn : 1 ≤ n) {x : Fin n → ℤ} (hx : ∀ i, |x i| ≤ (U : ℤ)) :
    scanPairs n U x ≤ (instances n U x).length * (2 * mPar n (2 * U) * (3 * n)) := by
  unfold scanPairs instances
  refine (List.sum_le_length_nsmul _ _ fun t ht => ?_).trans_eq
    (by rw [List.length_map, List.length_map, smul_eq_mul])
  obtain ⟨ν, hν, rfl⟩ := List.mem_map.mp ht
  exact scan_node_le (admissible_of_mem_allNodes hn hx hν)


end Cslib.Algorithms.ThreeSum.ChanHe
