/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Transcript

/-!
# MQOM correlated-tree indices and validation transcripts

The correlated-tree variant of MQOM v3 uses a perfect binary tree with `N = 2 ^ height` leaves
and the one-based heap convention of Algorithms 21--23 in [MQOM2026, Section 2.5.4, pp. 32--33].
Leaf `i` is node `N + i`. Its opening lists one sibling per level, starting at the leaf: replace
the current node by `node ^^^ 1`, then move the hidden node to `node / 2`.

The PGOW-MQ validation oracle in [MQOM2026, Definition 2, pp. 69--70] returns true exactly when a
candidate is the designated secret prefix. `validationTranscript` records chronological calls
using the library's existing reverse-chronological `Cslib.OracleComp.Transcript` convention.
`ValidationRun.accepted` checks the final output separately: the final challenger check is not an
extra adversary query and the output need not have appeared in the transcript.

This module contains no node labels, seed expansion, MQ arithmetic or sampled game. In
particular, it states no runtime, success-probability, hardness or unforgeability result.

## Main definitions

* `Cslib.Crypto.MQOM.leafNode`: the one-based heap node of a correlated-tree leaf.
* `Cslib.Crypto.MQOM.siblingPathNodes`: the bottom-up node indices in an opening.
* `Cslib.Crypto.MQOM.validationReply`: the exact-equality validation oracle.
* `Cslib.Crypto.MQOM.validationTranscript`: replies in the existing typed transcript format.
* `Cslib.Crypto.MQOM.ValidationRun`: prior calls and the separately checked final output.

## Main results

* `Cslib.Crypto.MQOM.siblingNode_parent`: a path entry and the hidden node have the same parent.
* `Cslib.Crypto.MQOM.siblingNode_ne_hiddenNode`: the revealed sibling is not the hidden node.
* `Cslib.Crypto.MQOM.length_siblingPathNodes`: an opening contains exactly `height` nodes.
* `Cslib.Crypto.MQOM.transcriptConsistent_validationTranscript`: every recorded reply is exact.
* `Cslib.Crypto.MQOM.ValidationRun.queryCount_eq_length_transcript`: failed and repeated calls
  are counted exactly once.

## References

* [R. Benadjila, C. Bouillaguet, T. Feneuil, M. Rivain, *MQOM: MQ on my Mind, Algorithm
  Specifications and Supporting Documentation*, version 3.0][MQOM2026]
-/

public section

namespace Cslib.Crypto.MQOM

/-! ### Correlated-tree indices -/

/-- The `N = 2 ^ height` leaf positions of an MQOM correlated tree. -/
abbrev LeafIndex (height : Nat) := Fin (2 ^ height)

/-- The number `N = 2 ^ height` of leaves in a perfect correlated tree. -/
@[expose] def leafCount (height : Nat) : Nat := 2 ^ height

/-- One-based heap index `N + i` of leaf `i`, as in Algorithms 22--23. -/
@[expose] def leafNode {height : Nat} (leaf : LeafIndex height) : Nat :=
  leafCount height + leaf

/-- Move a one-based heap node towards the root by repeated parent steps. -/
@[expose] def ancestorNode (node : Nat) : Nat → Nat
  | 0 => node
  | level + 1 => ancestorNode node level / 2

/-- The hidden node after `level` parent steps. The root is available at level `height`. -/
@[expose] def hiddenNode {height : Nat} (leaf : LeafIndex height)
    (level : Fin (height + 1)) : Nat :=
  ancestorNode (leafNode leaf) level

/-- The sibling revealed at a bottom-up opening level. -/
@[expose] def siblingNode {height : Nat} (leaf : LeafIndex height)
    (level : Fin height) : Nat :=
  hiddenNode leaf (Fin.castSucc level) ^^^ 1

/-- Algorithms 22--23's sibling indices, ordered from the leaf level towards the root. -/
@[expose] def siblingPathNodes {height : Nat} (leaf : LeafIndex height) : List Nat :=
  List.ofFn (siblingNode leaf)

@[simp] theorem ancestorNode_zero (node : Nat) : ancestorNode node 0 = node := rfl

@[simp] theorem ancestorNode_succ (node level : Nat) :
    ancestorNode node (level + 1) = ancestorNode node level / 2 := rfl

theorem ancestorNode_le (node level : Nat) : ancestorNode node level ≤ node := by
  induction level with
  | zero => exact le_rfl
  | succ level ih =>
    rw [ancestorNode]
    exact (Nat.div_le_self _ _).trans ih

theorem leafCount_le_leafNode {height : Nat} (leaf : LeafIndex height) :
    leafCount height ≤ leafNode leaf := by
  simp only [leafNode]
  omega

theorem leafNode_lt {height : Nat} (leaf : LeafIndex height) :
    leafNode leaf < 2 * leafCount height := by
  have hleaf := leaf.isLt
  simp only [leafNode, leafCount] at *
  omega

@[simp] theorem hiddenNode_zero {height : Nat} (leaf : LeafIndex height) :
    hiddenNode leaf (0 : Fin (height + 1)) = leafNode leaf := rfl

/-- One more source loop iteration moves the hidden node to its parent. -/
theorem hiddenNode_succ {height : Nat} (leaf : LeafIndex height) (level : Fin height) :
    hiddenNode leaf level.succ = hiddenNode leaf (Fin.castSucc level) / 2 := rfl

theorem hiddenNode_lt {height : Nat} (leaf : LeafIndex height)
    (level : Fin (height + 1)) : hiddenNode leaf level < 2 * leafCount height := by
  exact (ancestorNode_le (leafNode leaf) level).trans_lt (leafNode_lt leaf)

/-- Every sibling-path index belongs to the source tree array `1, ..., 2N - 1`. -/
theorem siblingNode_lt {height : Nat} (leaf : LeafIndex height) (level : Fin height) :
    siblingNode leaf level < 2 * leafCount height := by
  have hnode := hiddenNode_lt leaf (Fin.castSucc level)
  simp only [siblingNode]
  generalize hiddenNode leaf (Fin.castSucc level) = node at hnode ⊢
  rcases Nat.even_or_odd node with he | ho
  · rw [Nat.xor_one_of_even he]
    obtain ⟨k, rfl⟩ := he
    omega
  · rw [Nat.xor_one_of_odd ho]
    omega

/-- The revealed node and the hidden node are the two children of the same parent. -/
theorem siblingNode_parent {height : Nat} (leaf : LeafIndex height) (level : Fin height) :
    siblingNode leaf level / 2 = hiddenNode leaf (Fin.castSucc level) / 2 := by
  simp only [siblingNode]
  generalize hiddenNode leaf (Fin.castSucc level) = node
  rcases Nat.even_or_odd node with he | ho
  · rw [Nat.xor_one_of_even he]
    obtain ⟨k, rfl⟩ := he
    omega
  · rw [Nat.xor_one_of_odd ho]
    obtain ⟨k, rfl⟩ := ho
    omega

/-- An opening never reveals the hidden node at the same level. -/
theorem siblingNode_ne_hiddenNode {height : Nat} (leaf : LeafIndex height)
    (level : Fin height) : siblingNode leaf level ≠ hiddenNode leaf (Fin.castSucc level) := by
  simp only [siblingNode]
  generalize hiddenNode leaf (Fin.castSucc level) = node
  rcases Nat.even_or_odd node with he | ho
  · rw [Nat.xor_one_of_even he]
    obtain ⟨k, rfl⟩ := he
    omega
  · rw [Nat.xor_one_of_odd ho]
    obtain ⟨k, rfl⟩ := ho
    omega

/-- A correlated-tree opening contains exactly one sibling for each tree level. -/
theorem length_siblingPathNodes {height : Nat} (leaf : LeafIndex height) :
    (siblingPathNodes leaf).length = height := by
  exact List.length_ofFn

/-! ### Validation-oracle transcripts -/

/-- A candidate for the `k` field coordinates in the PGOW-MQ validation oracle. -/
abbrev ValidationPrefix (Coordinate : Type) (width : Nat) := Fin width → Coordinate

/-- The validation interface returns one Boolean for every candidate prefix. -/
abbrev ValidationResponse (Coordinate : Type) (width : Nat) :
    ValidationPrefix Coordinate width → Type :=
  fun _ => Bool

/-- Definition 2's validation oracle: accept exactly the designated secret prefix. -/
@[expose] def validationReply {Coordinate : Type} [DecidableEq Coordinate] {width : Nat}
    (secret candidate : ValidationPrefix Coordinate width) : Bool :=
  decide (candidate = secret)

theorem validationReply_eq_true_iff {Coordinate : Type} [DecidableEq Coordinate] {width : Nat}
    {secret candidate : ValidationPrefix Coordinate width} :
    validationReply secret candidate = true ↔ candidate = secret := by
  simp only [validationReply, decide_eq_true_eq]

theorem validationReply_eq_false_iff {Coordinate : Type} [DecidableEq Coordinate] {width : Nat}
    {secret candidate : ValidationPrefix Coordinate width} :
    validationReply secret candidate = false ↔ candidate ≠ secret := by
  simp only [validationReply, decide_eq_false_iff_not]

/-- The replies to chronological calls, stored newest first as `OracleComp.withTranscript` does.
Wrong and repeated candidates remain present and therefore remain charged queries. -/
@[expose] def validationTranscript {Coordinate : Type} [DecidableEq Coordinate] {width : Nat}
    (secret : ValidationPrefix Coordinate width)
    (queries : List (ValidationPrefix Coordinate width)) :
    OracleComp.Transcript (ValidationResponse Coordinate width) :=
  queries.reverse.map fun candidate => ⟨candidate, validationReply secret candidate⟩

/-- Every entry agrees with the exact-equality validation oracle. -/
@[expose] def TranscriptConsistent {Coordinate : Type} [DecidableEq Coordinate] {width : Nat}
    (secret : ValidationPrefix Coordinate width)
    (transcript : OracleComp.Transcript (ValidationResponse Coordinate width)) : Prop :=
  ∀ entry ∈ transcript, entry.2 = validationReply secret entry.1

/-- Earlier chronological calls form the suffix of the stored transcript. -/
theorem validationTranscript_append {Coordinate : Type} [DecidableEq Coordinate] {width : Nat}
    (secret : ValidationPrefix Coordinate width)
    (earlier later : List (ValidationPrefix Coordinate width)) :
    validationTranscript secret (earlier ++ later) =
      validationTranscript secret later ++ validationTranscript secret earlier := by
  simp only [validationTranscript, List.reverse_append, List.map_append]

/-- A newly appended chronological call becomes the head of the stored transcript. -/
theorem validationTranscript_append_singleton {Coordinate : Type} [DecidableEq Coordinate]
    {width : Nat} (secret : ValidationPrefix Coordinate width)
    (queries : List (ValidationPrefix Coordinate width))
    (candidate : ValidationPrefix Coordinate width) :
    validationTranscript secret (queries ++ [candidate]) =
      ⟨candidate, validationReply secret candidate⟩ :: validationTranscript secret queries := by
  rw [validationTranscript_append]
  rfl

theorem length_validationTranscript {Coordinate : Type} [DecidableEq Coordinate] {width : Nat}
    (secret : ValidationPrefix Coordinate width)
    (queries : List (ValidationPrefix Coordinate width)) :
    (validationTranscript secret queries).length = queries.length := by
  simp only [validationTranscript, List.length_map, List.length_reverse]

/-- Forgetting replies recovers the calls in the reverse-chronological storage order. -/
theorem queries_validationTranscript {Coordinate : Type} [DecidableEq Coordinate] {width : Nat}
    (secret : ValidationPrefix Coordinate width)
    (queries : List (ValidationPrefix Coordinate width)) :
    (validationTranscript secret queries).map (fun entry => entry.1) = queries.reverse := by
  simp [validationTranscript]

theorem transcriptConsistent_validationTranscript {Coordinate : Type} [DecidableEq Coordinate]
    {width : Nat} (secret : ValidationPrefix Coordinate width)
    (queries : List (ValidationPrefix Coordinate width)) :
    TranscriptConsistent secret (validationTranscript secret queries) := by
  intro entry hentry
  simp only [validationTranscript, List.mem_map] at hentry
  obtain ⟨candidate, _, rfl⟩ := hentry
  rfl

/-- The observable part of a PGOW validation run. `queries` are chronological adversary calls;
`output` is checked by the challenger after those calls. -/
structure ValidationRun (Coordinate : Type) (width : Nat) where
  /-- Chronological validation-oracle calls, including failed and repeated candidates. -/
  queries : List (ValidationPrefix Coordinate width)
  /-- The final candidate returned to the challenger. -/
  output : ValidationPrefix Coordinate width

namespace ValidationRun

variable {Coordinate : Type} [DecidableEq Coordinate] {width : Nat}

/-- The exact transcript observable from the run's adversary calls. -/
@[expose] def transcript (run : ValidationRun Coordinate width)
    (secret : ValidationPrefix Coordinate width) :
    OracleComp.Transcript (ValidationResponse Coordinate width) :=
  validationTranscript secret run.queries

/-- The source resource `Q`: adversary oracle calls, excluding the final challenger check. -/
@[expose] def queryCount (run : ValidationRun Coordinate width) : Nat := run.queries.length

/-- Whether the separately returned final candidate is accepted. -/
@[expose] def accepted (run : ValidationRun Coordinate width)
    (secret : ValidationPrefix Coordinate width) : Bool :=
  validationReply secret run.output

theorem queryCount_eq_length_transcript (run : ValidationRun Coordinate width)
    (secret : ValidationPrefix Coordinate width) :
    run.queryCount = (run.transcript secret).length := by
  simp only [queryCount, transcript, length_validationTranscript]

theorem accepted_eq_true_iff (run : ValidationRun Coordinate width)
    (secret : ValidationPrefix Coordinate width) :
    run.accepted secret = true ↔ run.output = secret := by
  exact validationReply_eq_true_iff

end ValidationRun

end Cslib.Crypto.MQOM
