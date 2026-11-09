/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MerkleTree.Binding
public import CslibFrontier.Languages.Probabilistic.RandomOracle
public import CslibFrontier.Languages.Probabilistic.UntilBad
public import CslibFrontier.Probability.BitString
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import Mathlib.Data.List.GetD

/-!
# Straight-line Merkle trace extraction in the random-oracle model

In the standard model, extracting the committed table of a Merkle tree from a cheating prover
requires rewinding two accepting executions on the same commitment and finding a conflicting pair
of openings (`CslibFrontier.Crypto.Computational.MerkleTree.Binding`,
`CslibFrontier.Crypto.Computational.Kilian.Soundness`). In the random-oracle model, as in Micali's
computationally sound proofs and the BCS transformation ([BenSassonChiesaSpooner2016]; see also
Chiesa and Yogev, *Building Cryptographic Proofs from Hash Functions*, Construction 18.5.3 and
Lemma 18.5.7), extraction is *straight-line*: given the query-answer trace
`tr : List (List Bool × List Bool)` of hash queries `(q, ans)` made so far, one can
deterministically reconstruct the unique table committed under a Merkle root `rt` at depth `d`
without rewinding.

## Extraction from a query trace

The tree of `CslibFrontier.Crypto.Computational.MerkleTree` hashes a leaf `x` to `H k x` and pairs
two
child nodes `(l, r)` into `encPair encBits encBits (l, r) = frame l ++ r`, which `unframe` and
`dropFrame` invert on every encoded pair:

* `findQueryInTrace tr digest` returns the first query `q` recorded in `tr` with answer `digest`.
* `findPreimageInTrace tr digest` decodes that query into `(unframe q, dropFrame q)`, the candidate
  left and right child digests of an internal node.
* `extractNodeFromTrace tr d rt i` walks `d` levels down from `rt` along the binary digits
  `(i / 2 ^ level) % 2` of position `i`, returning the level-`0` leaf digest.
* `extractLeafFromTrace tr d rt i` inverts that level-`0` digest in `tr` to recover the leaf at
  position `i`, and `extractTableFromTrace tr d rt defaultLeaf` tabulates all `2 ^ d` positions.

## Consistency and collision extraction

* **Consistency (`extractLeafFromTrace_eq_some_of_merkleVerify`)**: if `tr` has no output collisions
  (`TraceCollisionFree tr`) and records every hash evaluation along a valid depth-`d` opening
  (`PathQueriedInTrace H k tr i leaf path` and `merkleVerify H k d rt i leaf path = true`), then
  `extractLeafFromTrace tr d rt i = some leaf`, and entry `i` of
  `extractTableFromTrace tr d rt defaultLeaf` is `leaf`
  (`getD_extractTableFromTrace_eq_of_merkleVerify`). Any two openings of position `i` accepted
  against `rt` whose paths are recorded in a collision-free trace must therefore open to the same
  leaf (`leaf_eq_of_merkleVerify_of_traceCollisionFree`).
* **Dual collision extraction (`extractTraceCollision`, `isCollision_extractTraceCollision`)**:
  conversely, if `tr` is consistent with `H k` (`TraceConsistentWith (H k) tr`) and records all hash
  steps of an accepted opening `(leaf, path)` at position `i`, yet
  `extractLeafFromTrace tr d rt i ≠ some leaf`, then `extractTraceCollision H k tr i leaf path`
  deterministically extracts a collision `(q₁, q₂)` from `tr` with `q₁ ≠ q₂` and
  `H k q₁ = H k q₂`.

## Random-oracle collision and preimage bounds

For a lazy random oracle sampling uniform `m`-bit digests
(`memoize (fun _ => BitString.uniformList m)`):

* `toOuterMeasure_uniformList_mem_list_le` bounds the probability that a fresh `m`-bit digest hits
  a list `targets` of digests by `targets.length * (1 / 2 ^ m)`.
* `toOuterMeasure_memoize_not_traceCollisionFree_step` bounds the probability that one memoized
  oracle call from a collision-free trace `tr` creates a collision by `tr.length * (1 / 2 ^ m)`.
* `toOuterMeasure_run_memoize_not_traceCollisionFree_le` composes this per-call bound via
  `OracleComp.toOuterMeasure_bad_le`: any program making at most `Q` oracle queries produces a
  collision in its final trace with probability at most `Q * (Q * (1 / 2 ^ m))`.

## Main definitions

* `Cslib.Crypto.TraceConsistentWith`, `Cslib.Crypto.TraceCollisionFree`,
  `Cslib.Crypto.PathQueriedInTrace`: trace consistency, collision-freeness, and path coverage.
* `Cslib.Crypto.findQueryInTrace`, `Cslib.Crypto.findPreimageInTrace`: trace inversion primitives.
* `Cslib.Crypto.extractNodeFromTrace`, `Cslib.Crypto.extractLeafFromTrace`,
  `Cslib.Crypto.extractTableFromTrace`: straight-line Merkle node, leaf, and table extractors.
* `Cslib.Crypto.extractTraceCollision`: deterministic collision extractor when trace extraction
  disagrees with an accepted opening.

## Main results

* `Cslib.Crypto.extractLeafFromTrace_eq_some_of_merkleVerify`,
  `Cslib.Crypto.getD_extractTableFromTrace_eq_of_merkleVerify`: straight-line extraction agrees
  with every valid opening whose path is in a collision-free trace.
* `Cslib.Crypto.extractLeafFromTrace_cons_of_ne`,
  `Cslib.Crypto.extractTableFromTrace_cons_of_ne`: straight-line leaf and table extraction are
  invariant under prepending a Merkle query whose digest avoids the root and existing query
  children.
* `Cslib.Crypto.isCollision_extractTraceCollision`,
  `Cslib.Crypto.exists_collision_of_extractLeafFromTrace_ne`: disagreement between an accepted
  queried opening and the trace extractor yields an explicit hash collision in the trace.
* `Cslib.Crypto.toOuterMeasure_uniformList_mem_list_le`,
  `Cslib.Crypto.toOuterMeasure_memoize_not_traceCollisionFree_step`,
  `Cslib.Crypto.toOuterMeasure_run_memoize_not_traceCollisionFree_le`,
  `Cslib.Crypto.mem_support_memoize_nodup`: union bounds and trace-support invariants for lazy
  random oracles.

## References

* [E. Ben-Sasson, A. Chiesa, N. Spooner, *Interactive Oracle Proofs*][BenSassonChiesaSpooner2016]
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Section 8.9.
* [J. Kilian, *A note on efficient zero-knowledge proofs and arguments*][Kilian1992]
-/

@[expose] public section

namespace Cslib.Crypto

open Probability OracleComp Turing.MultiTapeTM
open scoped ENNReal

/-! ### Trace consistency and collision predicates -/

section Predicates

variable {Query Digest : Type*}

/-- Every recorded query-answer pair `(q, ans)` in `tr` agrees with the function `h`. -/
def TraceConsistentWith (h : Query → Digest) (tr : List (Query × Digest)) : Prop :=
  ∀ p ∈ tr, h p.1 = p.2

instance [DecidableEq Digest] (h : Query → Digest) (tr : List (Query × Digest)) :
    Decidable (TraceConsistentWith h tr) :=
  inferInstanceAs (Decidable (∀ p ∈ tr, h p.1 = p.2))

/-- No two entries in `tr` with distinct query inputs share the same output digest. -/
def TraceCollisionFree (tr : List (Query × Digest)) : Prop :=
  ∀ p₁ ∈ tr, ∀ p₂ ∈ tr, p₁.2 = p₂.2 → p₁.1 = p₂.1

instance [DecidableEq Query] [DecidableEq Digest] (tr : List (Query × Digest)) :
    Decidable (TraceCollisionFree tr) :=
  inferInstanceAs (Decidable (∀ p₁ ∈ tr, ∀ p₂ ∈ tr, p₁.2 = p₂.2 → p₁.1 = p₂.1))

@[simp]
theorem traceConsistentWith_nil (h : Query → Digest) :
    TraceConsistentWith h ([] : List (Query × Digest)) := by
  intro _ hp
  cases hp

@[simp]
theorem traceConsistentWith_cons {h : Query → Digest} {p : Query × Digest}
    {tr : List (Query × Digest)} :
    TraceConsistentWith h (p :: tr) ↔ h p.1 = p.2 ∧ TraceConsistentWith h tr :=
  List.forall_mem_cons

@[simp]
theorem traceCollisionFree_nil : TraceCollisionFree ([] : List (Query × Digest)) := by
  intro _ hp
  cases hp

theorem traceCollisionFree_cons_iff {q : Query} {ans : Digest} {tr : List (Query × Digest)} :
    TraceCollisionFree ((q, ans) :: tr) ↔
      TraceCollisionFree tr ∧ ∀ p ∈ tr, p.2 = ans → p.1 = q := by
  constructor
  · intro h
    refine ⟨fun p₁ hp₁ p₂ hp₂ heq => h p₁ (List.mem_cons_of_mem _ hp₁)
      p₂ (List.mem_cons_of_mem _ hp₂) heq, fun p hp heq => ?_⟩
    exact h p (List.mem_cons_of_mem _ hp) (q, ans) List.mem_cons_self heq
  · rintro ⟨htr, hnew⟩ p₁ hp₁ p₂ hp₂ heq
    rcases List.mem_cons.mp hp₁ with rfl | hp₁ <;>
      rcases List.mem_cons.mp hp₂ with rfl | hp₂
    · rfl
    · exact (hnew p₂ hp₂ heq.symm).symm
    · exact hnew p₁ hp₁ heq
    · exact htr p₁ hp₁ p₂ hp₂ heq

/-- Search `tr` for the first query-answer pair whose digest is `digest`, returning its query. -/
def findQueryInTrace [BEq Digest] (tr : List (Query × Digest)) (digest : Digest) : Option Query :=
  (tr.find? fun p => p.2 == digest).map Prod.fst

@[simp]
theorem findQueryInTrace_nil [BEq Digest] (digest : Digest) :
    findQueryInTrace ([] : List (Query × Digest)) digest = none :=
  rfl

variable [BEq Digest] [LawfulBEq Digest]

/-- If `findQueryInTrace tr digest = some q`, then `(q, digest)` is a recorded entry of `tr`. -/
theorem mem_of_findQueryInTrace_eq_some {tr : List (Query × Digest)} {digest : Digest} {q : Query}
    (h : findQueryInTrace tr digest = some q) : (q, digest) ∈ tr := by
  unfold findQueryInTrace at h
  obtain ⟨⟨q, d'⟩, hfind, rfl⟩ := Option.map_eq_some_iff.mp h
  have hmem := List.mem_of_find?_eq_some hfind
  have hd := List.find?_some hfind
  simp only [beq_iff_eq] at hd
  subst hd
  exact hmem

/-- In a trace consistent with `h`, any query returned by `findQueryInTrace tr digest` hashes to
`digest` under `h`. -/
theorem hash_eq_of_findQueryInTrace_eq_some {h : Query → Digest} {tr : List (Query × Digest)}
    {digest : Digest} {q : Query} (hcons : TraceConsistentWith h tr)
    (hfind : findQueryInTrace tr digest = some q) : h q = digest :=
  hcons (q, digest) (mem_of_findQueryInTrace_eq_some hfind)

/-- If `(q, digest) ∈ tr`, then `findQueryInTrace tr digest` succeeds and returns some query
recorded with `digest` in `tr`. -/
theorem exists_findQueryInTrace_eq_some_of_mem {tr : List (Query × Digest)} {q : Query}
    {digest : Digest} (hmem : (q, digest) ∈ tr) :
    ∃ q', findQueryInTrace tr digest = some q' ∧ (q', digest) ∈ tr := by
  have hsome : (tr.find? fun p => p.2 == digest).isSome = true :=
    List.find?_isSome.mpr ⟨(q, digest), hmem, by simp⟩
  obtain ⟨⟨q', d'⟩, hfind⟩ := Option.isSome_iff_exists.mp hsome
  have hmem' := List.mem_of_find?_eq_some hfind
  have hd := List.find?_some hfind
  simp only [beq_iff_eq] at hd
  subst hd
  exact ⟨q', by simp [findQueryInTrace, hfind], hmem'⟩

/-- In a collision-free trace, `findQueryInTrace tr digest` recovers the unique query `q` recorded
with `digest`. -/
theorem findQueryInTrace_eq_some_of_traceCollisionFree {tr : List (Query × Digest)} {q : Query}
    {digest : Digest} (hfree : TraceCollisionFree tr) (hmem : (q, digest) ∈ tr) :
    findQueryInTrace tr digest = some q := by
  obtain ⟨q', hfind, hmem'⟩ := exists_findQueryInTrace_eq_some_of_mem hmem
  have hq : q' = q := hfree (q', digest) hmem' (q, digest) hmem rfl
  subst hq
  exact hfind

/-- Prepending `(q, ans)` to `tr` leaves `findQueryInTrace` at `digest` unchanged whenever
`ans ≠ digest`. -/
theorem findQueryInTrace_cons_of_ne (tr : List (Query × Digest)) (q : Query) {ans digest : Digest}
    (hne : ans ≠ digest) :
    findQueryInTrace ((q, ans) :: tr) digest = findQueryInTrace tr digest := by
  simp [findQueryInTrace, beq_false_of_ne hne]

end Predicates

/-! ### Straight-line Merkle trace extraction -/

section Extract

variable (H : List Bool → List Bool → List Bool) (k : List Bool)

/-- Every hash evaluation along the recomputation of the root from `leaf` at position `i` along
`path` appears as a recorded `(q, H k q)` entry in `tr`. -/
def PathQueriedInTrace (tr : List (List Bool × List Bool)) (i : ℕ) (leaf : List Bool)
    (path : List (List Bool)) : Prop :=
  ∀ q ∈ merkleInputs H k leaf i path, (q, H k q) ∈ tr

instance (tr : List (List Bool × List Bool)) (i : ℕ) (leaf : List Bool)
    (path : List (List Bool)) : Decidable (PathQueriedInTrace H k tr i leaf path) :=
  inferInstanceAs (Decidable (∀ q ∈ merkleInputs H k leaf i path, (q, H k q) ∈ tr))

variable {H k}

/-- If `tr` is consistent with `H k` and every hash input along `merkleInputs H k leaf i path`
appears in `tr.map Prod.fst`, then `PathQueriedInTrace H k tr i leaf path` holds. -/
theorem PathQueriedInTrace.of_mem_map_fst {tr : List (List Bool × List Bool)} {i : ℕ}
    {leaf : List Bool} {path : List (List Bool)} (hcons : TraceConsistentWith (H k) tr)
    (hmem : ∀ q ∈ merkleInputs H k leaf i path, q ∈ tr.map Prod.fst) :
    PathQueriedInTrace H k tr i leaf path := by
  intro q hq
  obtain ⟨⟨q', ans⟩, hp, rfl⟩ := List.mem_map.mp (hmem q hq)
  have hans : H k q' = ans := hcons (q', ans) hp
  rwa [hans]

/-- Invert an internal-node digest `digest` in `tr` by finding the first query `q` with answer
`digest` and splitting `q = encPair encBits encBits (left, right)` into `(unframe q, dropFrame q)`.
-/
def findPreimageInTrace (tr : List (List Bool × List Bool)) (digest : List Bool) :
    Option (List Bool × List Bool) :=
  (findQueryInTrace tr digest).map fun q => (unframe q, dropFrame q)

@[simp]
theorem findPreimageInTrace_nil (digest : List Bool) :
    findPreimageInTrace [] digest = none :=
  rfl

/-- If `findQueryInTrace` recovers `encPair encBits encBits (left, right)`, then
`findPreimageInTrace` recovers `(left, right)`. -/
theorem findPreimageInTrace_eq_some_of_findQueryInTrace {tr : List (List Bool × List Bool)}
    {digest left right : List Bool}
    (h : findQueryInTrace tr digest = some (encPair encBits encBits (left, right))) :
    findPreimageInTrace tr digest = some (left, right) := by
  simp [findPreimageInTrace, h]

/-- In a collision-free trace containing `(encPair encBits encBits (left, right), digest)`,
`findPreimageInTrace tr digest` returns `some (left, right)`. -/
theorem findPreimageInTrace_eq_some_of_traceCollisionFree {tr : List (List Bool × List Bool)}
    {digest left right : List Bool} (hfree : TraceCollisionFree tr)
    (hmem : (encPair encBits encBits (left, right), digest) ∈ tr) :
    findPreimageInTrace tr digest = some (left, right) :=
  findPreimageInTrace_eq_some_of_findQueryInTrace
    (findQueryInTrace_eq_some_of_traceCollisionFree hfree hmem)

/-- Walk `d` internal levels down from the root digest `rt` along the bits of position `i` using
`findPreimageInTrace`, returning the level-`0` leaf digest if every step finds a preimage in `tr`.
-/
def extractNodeFromTrace (tr : List (List Bool × List Bool)) :
    ℕ → List Bool → ℕ → Option (List Bool)
  | 0, rt, _ => some rt
  | d + 1, rt, i =>
    (findPreimageInTrace tr rt).bind fun (left, right) =>
      extractNodeFromTrace tr d (if (i / 2 ^ d) % 2 = 0 then left else right) i

@[simp]
theorem extractNodeFromTrace_zero (tr : List (List Bool × List Bool)) (rt : List Bool) (i : ℕ) :
    extractNodeFromTrace tr 0 rt i = some rt :=
  rfl

@[simp]
theorem extractNodeFromTrace_succ (tr : List (List Bool × List Bool)) (d : ℕ) (rt : List Bool)
    (i : ℕ) :
    extractNodeFromTrace tr (d + 1) rt i =
      (findPreimageInTrace tr rt).bind fun (left, right) =>
        extractNodeFromTrace tr d (if (i / 2 ^ d) % 2 = 0 then left else right) i :=
  rfl

/-- Extract the leaf committed at position `i` of a depth-`d` Merkle tree with root `rt` from the
query-answer trace `tr`: walk `d` internal levels down from `rt` to the leaf digest, then invert
the leaf hash in `tr`. -/
def extractLeafFromTrace (tr : List (List Bool × List Bool)) (d : ℕ) (rt : List Bool) (i : ℕ) :
    Option (List Bool) :=
  (extractNodeFromTrace tr d rt i).bind (findQueryInTrace tr)

/-- Extract the full table of `2 ^ d` leaves committed under root `rt` at depth `d` from the
query-answer trace `tr`, filling missing entries with `defaultLeaf`. -/
def extractTableFromTrace (tr : List (List Bool × List Bool)) (d : ℕ) (rt : List Bool)
    (defaultLeaf : List Bool) : List (List Bool) :=
  (List.range (2 ^ d)).map fun i => (extractLeafFromTrace tr d rt i).getD defaultLeaf

@[simp]
theorem length_extractTableFromTrace (tr : List (List Bool × List Bool)) (d : ℕ)
    (rt defaultLeaf : List Bool) :
    (extractTableFromTrace tr d rt defaultLeaf).length = 2 ^ d := by
  simp [extractTableFromTrace]

@[simp]
theorem getElem_extractTableFromTrace (tr : List (List Bool × List Bool)) (d : ℕ)
    (rt defaultLeaf : List Bool) (i : ℕ)
    (hi : i < (extractTableFromTrace tr d rt defaultLeaf).length) :
    (extractTableFromTrace tr d rt defaultLeaf)[i] =
      (extractLeafFromTrace tr d rt i).getD defaultLeaf := by
  simp [extractTableFromTrace]

theorem getD_extractTableFromTrace {tr : List (List Bool × List Bool)} {d : ℕ}
    {rt defaultLeaf : List Bool} {i : ℕ} (hi : i < 2 ^ d) :
    (extractTableFromTrace tr d rt defaultLeaf).getD i defaultLeaf =
      (extractLeafFromTrace tr d rt i).getD defaultLeaf := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), getElem_extractTableFromTrace]

theorem findPreimageInTrace_cons_of_ne (tr : List (List Bool × List Bool)) (q : List Bool)
    {ans digest : List Bool} (hne : ans ≠ digest) :
    findPreimageInTrace ((q, ans) :: tr) digest = findPreimageInTrace tr digest := by
  simp [findPreimageInTrace, findQueryInTrace_cons_of_ne tr q hne]

/-- If `extractNodeFromTrace tr d rt i = some digest`, then `digest` is either `rt` (when `d = 0`)
or one of `unframe p.1`, `dropFrame p.1` for some entry `p ∈ tr`. -/
theorem eq_or_mem_of_extractNodeFromTrace_eq_some {tr : List (List Bool × List Bool)} {d : ℕ}
    {rt : List Bool} {i : ℕ} {digest : List Bool}
    (h : extractNodeFromTrace tr d rt i = some digest) :
    digest = rt ∨ ∃ p ∈ tr, digest = unframe p.1 ∨ digest = dropFrame p.1 := by
  induction d generalizing rt with
  | zero =>
    simp only [extractNodeFromTrace_zero, Option.some.injEq] at h
    exact Or.inl h.symm
  | succ d ih =>
    rw [extractNodeFromTrace_succ, Option.bind_eq_some_iff] at h
    obtain ⟨⟨left, right⟩, hpre, hnode⟩ := h
    unfold findPreimageInTrace at hpre
    obtain ⟨q₀, hfind, hpair⟩ := Option.map_eq_some_iff.mp hpre
    rw [Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    have hmem : (q₀, rt) ∈ tr := mem_of_findQueryInTrace_eq_some hfind
    rcases ih hnode with htop | ⟨p, hp, hchild⟩
    · refine Or.inr ⟨(q₀, rt), hmem, ?_⟩
      by_cases hbit : (i / 2 ^ d) % 2 = 0
      · left; simpa [hbit] using htop
      · right; simpa [hbit] using htop
    · exact Or.inr ⟨p, hp, hchild⟩

/-- Prepending `(q, ans)` to `tr` leaves `extractNodeFromTrace` at `rt` unchanged whenever
`ans ≠ rt` and `ans` does not equal `unframe p.1` or `dropFrame p.1` for any `p ∈ tr`. -/
theorem extractNodeFromTrace_cons_of_ne (tr : List (List Bool × List Bool)) (q : List Bool)
    {ans rt : List Bool} (d i : ℕ) (hrt : ans ≠ rt)
    (hchildren : ∀ p ∈ tr, ans ≠ unframe p.1 ∧ ans ≠ dropFrame p.1) :
    extractNodeFromTrace ((q, ans) :: tr) d rt i = extractNodeFromTrace tr d rt i := by
  induction d generalizing rt with
  | zero => rfl
  | succ d ih =>
    rw [extractNodeFromTrace_succ, extractNodeFromTrace_succ,
      findPreimageInTrace_cons_of_ne tr q hrt]
    cases hpre : findPreimageInTrace tr rt with
    | none => rfl
    | some pair =>
      rcases pair with ⟨left, right⟩
      simp only [Option.bind_some]
      unfold findPreimageInTrace at hpre
      obtain ⟨q₀, hfind, hpair⟩ := Option.map_eq_some_iff.mp hpre
      rw [Prod.mk.injEq] at hpair
      obtain ⟨rfl, rfl⟩ := hpair
      have hmem : (q₀, rt) ∈ tr := mem_of_findQueryInTrace_eq_some hfind
      have hne_child : ans ≠ (if (i / 2 ^ d) % 2 = 0 then unframe q₀ else dropFrame q₀) := by
        split_ifs
        · exact (hchildren (q₀, rt) hmem).1
        · exact (hchildren (q₀, rt) hmem).2
      exact ih hne_child

/-- Prepending `(q, ans)` to `tr` leaves `extractLeafFromTrace` at `rt` unchanged whenever
`ans ≠ rt` and `ans` does not equal `unframe p.1` or `dropFrame p.1` for any `p ∈ tr`. -/
theorem extractLeafFromTrace_cons_of_ne (tr : List (List Bool × List Bool)) (q : List Bool)
    {ans rt : List Bool} (d i : ℕ) (hrt : ans ≠ rt)
    (hchildren : ∀ p ∈ tr, ans ≠ unframe p.1 ∧ ans ≠ dropFrame p.1) :
    extractLeafFromTrace ((q, ans) :: tr) d rt i = extractLeafFromTrace tr d rt i := by
  unfold extractLeafFromTrace
  rw [extractNodeFromTrace_cons_of_ne tr q d i hrt hchildren]
  cases hnode : extractNodeFromTrace tr d rt i with
  | none => rfl
  | some digest =>
    simp only [Option.bind_some]
    have hne : ans ≠ digest := by
      rcases eq_or_mem_of_extractNodeFromTrace_eq_some hnode with rfl | ⟨p, hp, hchild | hchild⟩
      · exact hrt
      · exact hchild ▸ (hchildren p hp).1
      · exact hchild ▸ (hchildren p hp).2
    exact findQueryInTrace_cons_of_ne tr q hne

/-- Prepending `(q, ans)` to `tr` leaves `extractTableFromTrace` at `rt` unchanged whenever
`ans ≠ rt` and `ans` does not equal `unframe p.1` or `dropFrame p.1` for any `p ∈ tr`. -/
theorem extractTableFromTrace_cons_of_ne (tr : List (List Bool × List Bool)) (q : List Bool)
    {ans rt : List Bool} (d : ℕ) (defaultLeaf : List Bool) (hrt : ans ≠ rt)
    (hchildren : ∀ p ∈ tr, ans ≠ unframe p.1 ∧ ans ≠ dropFrame p.1) :
    extractTableFromTrace ((q, ans) :: tr) d rt defaultLeaf =
      extractTableFromTrace tr d rt defaultLeaf := by
  unfold extractTableFromTrace
  refine List.map_congr_left fun i _ => ?_
  rw [extractLeafFromTrace_cons_of_ne tr q d i hrt hchildren]

/-! ### Structure of `merkleInputs` and consistency of trace extraction -/

/-- Appending one sibling at the top of `path` prepends the top internal-node hash input to
`merkleInputs H k leaf i path`. -/
theorem merkleInputs_concat (leaf : List Bool) (i : ℕ) (path : List (List Bool))
    (sibling : List Bool) :
    merkleInputs H k leaf i (path ++ [sibling]) =
      (if (i / 2 ^ path.length) % 2 = 0 then
        encPair encBits encBits (merkleRootOfPath H k leaf i path, sibling)
      else
        encPair encBits encBits (sibling, merkleRootOfPath H k leaf i path)) ::
        merkleInputs H k leaf i path := by
  simp only [merkleInputs, merkleRootOfPath, List.foldl_concat, merkleInputsStep,
    snd_foldl_merkleInputsStep]

/-- Recomputing the root along `path ++ [sibling]` hashes the pair of `merkleRootOfPath` on `path`
and `sibling`, ordered by bit `path.length` of `i`. -/
theorem merkleRootOfPath_concat (leaf : List Bool) (i : ℕ) (path : List (List Bool))
    (sibling : List Bool) :
    merkleRootOfPath H k leaf i (path ++ [sibling]) =
      H k (if (i / 2 ^ path.length) % 2 = 0 then
        encPair encBits encBits (merkleRootOfPath H k leaf i path, sibling)
      else
        encPair encBits encBits (sibling, merkleRootOfPath H k leaf i path)) := by
  rw [merkleRootOfPath, merkleInputs_concat, List.headD_cons]

/-- The leaf itself is always one of the hash inputs in `merkleInputs H k leaf i path`. -/
theorem leaf_mem_merkleInputs (leaf : List Bool) (i : ℕ) (path : List (List Bool)) :
    leaf ∈ merkleInputs H k leaf i path := by
  induction path using List.reverseRecOn with
  | nil => simp [merkleInputs]
  | append_singleton path sibling ih =>
    rw [merkleInputs_concat]
    exact List.mem_cons_of_mem _ ih

variable (H k) in
/-- Every `merkleInputs H k leaf i path` list is non-empty. -/
theorem merkleInputs_ne_nil (leaf : List Bool) (i : ℕ) (path : List (List Bool)) :
    merkleInputs H k leaf i path ≠ [] := by
  induction path using List.reverseRecOn with
  | nil => simp [merkleInputs]
  | append_singleton path sibling _ =>
    rw [merkleInputs_concat]
    exact List.cons_ne_nil _ _

/-- If `findQueryInTrace tr (H k q) = some q` for every hash input `q` along `(leaf, i, path)`,
then `extractNodeFromTrace` from the recomputed root recovers the leaf digest `some (H k leaf)`. -/
theorem extractNodeFromTrace_eq_some_of_findQueryInTrace {tr : List (List Bool × List Bool)}
    {leaf : List Bool} {i : ℕ} {path : List (List Bool)}
    (hfind : ∀ q ∈ merkleInputs H k leaf i path, findQueryInTrace tr (H k q) = some q) :
    extractNodeFromTrace tr path.length (merkleRootOfPath H k leaf i path) i =
      some (H k leaf) := by
  induction path using List.reverseRecOn with
  | nil =>
    simp [merkleRootOfPath, merkleInputs]
  | append_singleton path sibling ih =>
    rw [List.length_append, List.length_singleton, merkleRootOfPath_concat,
      extractNodeFromTrace_succ]
    set q := if (i / 2 ^ path.length) % 2 = 0 then
        encPair encBits encBits (merkleRootOfPath H k leaf i path, sibling)
      else
        encPair encBits encBits (sibling, merkleRootOfPath H k leaf i path)
    have hq_mem : q ∈ merkleInputs H k leaf i (path ++ [sibling]) := by
      rw [merkleInputs_concat]
      exact List.mem_cons_self
    have hq_find : findQueryInTrace tr (H k q) = some q := hfind q hq_mem
    rcases Nat.mod_two_eq_zero_or_one (i / 2 ^ path.length) with hbit | hbit
    · simp only [q, hbit, ↓reduceIte] at hq_find ⊢
      rw [findPreimageInTrace_eq_some_of_findQueryInTrace hq_find, Option.bind_some]
      refine ih fun q' hq' => hfind q' ?_
      rw [merkleInputs_concat]
      exact List.mem_cons_of_mem _ hq'
    · simp only [q, hbit, one_ne_zero, ↓reduceIte] at hq_find ⊢
      rw [findPreimageInTrace_eq_some_of_findQueryInTrace hq_find, Option.bind_some]
      refine ih fun q' hq' => hfind q' ?_
      rw [merkleInputs_concat]
      exact List.mem_cons_of_mem _ hq'

/-- If `findQueryInTrace tr (H k q) = some q` for every hash input `q` along `(leaf, i, path)`,
then `extractLeafFromTrace` from the recomputed root recovers `some leaf`. -/
theorem extractLeafFromTrace_eq_some_of_findQueryInTrace {tr : List (List Bool × List Bool)}
    {leaf : List Bool} {i : ℕ} {path : List (List Bool)}
    (hfind : ∀ q ∈ merkleInputs H k leaf i path, findQueryInTrace tr (H k q) = some q) :
    extractLeafFromTrace tr path.length (merkleRootOfPath H k leaf i path) i = some leaf := by
  unfold extractLeafFromTrace
  rw [extractNodeFromTrace_eq_some_of_findQueryInTrace hfind, Option.bind_some]
  exact hfind leaf (leaf_mem_merkleInputs leaf i path)

/-- **Trace extraction consistency for `merkleRootOfPath`**: in a collision-free trace containing
all hash steps of `(leaf, i, path)`, `extractLeafFromTrace` at `merkleRootOfPath H k leaf i path`
returns `some leaf`. -/
theorem extractLeafFromTrace_eq_some_of_merkleRootOfPath {tr : List (List Bool × List Bool)}
    {leaf : List Bool} {i : ℕ} {path : List (List Bool)} (hfree : TraceCollisionFree tr)
    (hpath : PathQueriedInTrace H k tr i leaf path) :
    extractLeafFromTrace tr path.length (merkleRootOfPath H k leaf i path) i = some leaf :=
  extractLeafFromTrace_eq_some_of_findQueryInTrace fun _ hq =>
    findQueryInTrace_eq_some_of_traceCollisionFree hfree (hpath _ hq)

/-- **Main consistency theorem** (Chiesa–Yogev Lemma 18.5.7): if `tr` is collision-free and
contains all hash evaluations along an opening `(leaf, path)` of position `i` accepted by
`merkleVerify H k d rt i leaf path`, then `extractLeafFromTrace tr d rt i = some leaf`. -/
theorem extractLeafFromTrace_eq_some_of_merkleVerify {tr : List (List Bool × List Bool)}
    {d : ℕ} {rt : List Bool} {i : ℕ} {leaf : List Bool} {path : List (List Bool)}
    (hfree : TraceCollisionFree tr) (hpath : PathQueriedInTrace H k tr i leaf path)
    (hver : merkleVerify H k d rt i leaf path = true) :
    extractLeafFromTrace tr d rt i = some leaf := by
  simp only [merkleVerify, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hver
  obtain ⟨⟨hlen, -⟩, hroot⟩ := hver
  rw [← hlen, ← hroot]
  exact extractLeafFromTrace_eq_some_of_merkleRootOfPath hfree hpath

/-- Under the hypotheses of `extractLeafFromTrace_eq_some_of_merkleVerify`, position `i` of the
extracted table `extractTableFromTrace tr d rt defaultLeaf` equals `leaf`. -/
theorem getD_extractTableFromTrace_eq_of_merkleVerify {tr : List (List Bool × List Bool)}
    {d : ℕ} {rt defaultLeaf : List Bool} {i : ℕ} {leaf : List Bool} {path : List (List Bool)}
    (hfree : TraceCollisionFree tr) (hpath : PathQueriedInTrace H k tr i leaf path)
    (hver : merkleVerify H k d rt i leaf path = true) :
    (extractTableFromTrace tr d rt defaultLeaf).getD i defaultLeaf = leaf := by
  have hi : i < 2 ^ d := by
    simp only [merkleVerify, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hver
    exact hver.1.2
  rw [getD_extractTableFromTrace hi,
    extractLeafFromTrace_eq_some_of_merkleVerify hfree hpath hver, Option.getD_some]

/-- Indexed form of `getD_extractTableFromTrace_eq_of_merkleVerify`. -/
theorem getElem_extractTableFromTrace_eq_of_merkleVerify {tr : List (List Bool × List Bool)}
    {d : ℕ} {rt defaultLeaf : List Bool} {i : ℕ} {leaf : List Bool} {path : List (List Bool)}
    (hfree : TraceCollisionFree tr) (hpath : PathQueriedInTrace H k tr i leaf path)
    (hver : merkleVerify H k d rt i leaf path = true)
    (hi : i < (extractTableFromTrace tr d rt defaultLeaf).length) :
    (extractTableFromTrace tr d rt defaultLeaf)[i] = leaf := by
  rw [getElem_extractTableFromTrace,
    extractLeafFromTrace_eq_some_of_merkleVerify hfree hpath hver, Option.getD_some]

/-- Any two openings of the same position `i` accepted against `rt` at depth `d` whose hash paths
are recorded in a collision-free trace `tr` must open to the same leaf. -/
theorem leaf_eq_of_merkleVerify_of_traceCollisionFree {tr : List (List Bool × List Bool)}
    {d : ℕ} {rt : List Bool} {i : ℕ} {leaf₁ leaf₂ : List Bool} {path₁ path₂ : List (List Bool)}
    (hfree : TraceCollisionFree tr) (hpath₁ : PathQueriedInTrace H k tr i leaf₁ path₁)
    (hpath₂ : PathQueriedInTrace H k tr i leaf₂ path₂)
    (hver₁ : merkleVerify H k d rt i leaf₁ path₁ = true)
    (hver₂ : merkleVerify H k d rt i leaf₂ path₂ = true) :
    leaf₁ = leaf₂ := by
  have h₁ := extractLeafFromTrace_eq_some_of_merkleVerify hfree hpath₁ hver₁
  have h₂ := extractLeafFromTrace_eq_some_of_merkleVerify hfree hpath₂ hver₂
  exact Option.some.inj (h₁.symm.trans h₂)

/-! ### Dual collision extraction from trace disagreement -/

variable (H k) in
/-- Deterministically extract a hash collision from `tr` when an opening `(leaf, path)` at position
`i` disagrees with `extractLeafFromTrace`: find the first hash input `q` in
`merkleInputs H k leaf i path` whose digest `H k q` is inverted by `findQueryInTrace tr` to a
different query. -/
def extractTraceCollision (tr : List (List Bool × List Bool)) (i : ℕ) (leaf : List Bool)
    (path : List (List Bool)) : List Bool × List Bool :=
  match (merkleInputs H k leaf i path).find? fun q =>
    findQueryInTrace tr (H k q) != some q with
  | some q => (q, (findQueryInTrace tr (H k q)).getD [])
  | none => ([], [])

/-- **Dual collision extraction**: if `tr` is consistent with `H k` and contains all hash steps of
an opening `(leaf, path)` accepted by `merkleVerify H k d rt i leaf path`, yet
`extractLeafFromTrace tr d rt i ≠ some leaf`, then `extractTraceCollision H k tr i leaf path`
returns two distinct queries in `tr` with the same hash under `H k`. -/
theorem extractTraceCollision_spec {tr : List (List Bool × List Bool)} {d : ℕ} {rt : List Bool}
    {i : ℕ} {leaf : List Bool} {path : List (List Bool)}
    (hcons : TraceConsistentWith (H k) tr) (hpath : PathQueriedInTrace H k tr i leaf path)
    (hver : merkleVerify H k d rt i leaf path = true)
    (hne : extractLeafFromTrace tr d rt i ≠ some leaf) :
    let col := extractTraceCollision H k tr i leaf path
    (col.1, H k col.1) ∈ tr ∧ (col.2, H k col.1) ∈ tr ∧ col.1 ≠ col.2 ∧ H k col.1 = H k col.2 := by
  simp only [merkleVerify, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hver
  obtain ⟨⟨hlen, -⟩, hroot⟩ := hver
  have hnot_all : ¬ ∀ q ∈ merkleInputs H k leaf i path, findQueryInTrace tr (H k q) = some q := by
    intro hall
    apply hne
    rw [← hlen, ← hroot]
    exact extractLeafFromTrace_eq_some_of_findQueryInTrace hall
  push Not at hnot_all
  obtain ⟨q₀, hq₀_mem, hq₀_ne⟩ := hnot_all
  have hsome :
      ((merkleInputs H k leaf i path).find? fun q =>
        findQueryInTrace tr (H k q) != some q).isSome = true :=
    List.find?_isSome.mpr ⟨q₀, hq₀_mem, bne_iff_ne.mpr hq₀_ne⟩
  obtain ⟨q₁, hfind⟩ := Option.isSome_iff_exists.mp hsome
  have hq₁_mem : q₁ ∈ merkleInputs H k leaf i path := List.mem_of_find?_eq_some hfind
  have hq₁_ne : findQueryInTrace tr (H k q₁) ≠ some q₁ := by
    have h := List.find?_some hfind
    simpa using h
  have hq₁_tr : (q₁, H k q₁) ∈ tr := hpath q₁ hq₁_mem
  obtain ⟨q₂, hq₂_find, hq₂_tr⟩ := exists_findQueryInTrace_eq_some_of_mem hq₁_tr
  have hne_q : q₁ ≠ q₂ := by
    intro heq
    subst heq
    exact hq₁_ne hq₂_find
  have hhash_eq : H k q₁ = H k q₂ := (hcons (q₂, H k q₁) hq₂_tr).symm
  have hcol : extractTraceCollision H k tr i leaf path = (q₁, q₂) := by
    simp [extractTraceCollision, hfind, hq₂_find]
  rw [hcol]
  exact ⟨hq₁_tr, hq₂_tr, hne_q, hhash_eq⟩

/-- **Collision-game form of `extractTraceCollision_spec`**: when an accepted opening whose path is
in `tr` disagrees with `extractLeafFromTrace`, `extractTraceCollision` produces a valid collision
for `isCollision H (fun _ _ => true) n k`. -/
theorem isCollision_extractTraceCollision {tr : List (List Bool × List Bool)} {d : ℕ}
    {rt : List Bool} {i : ℕ} {leaf : List Bool} {path : List (List Bool)}
    (hcons : TraceConsistentWith (H k) tr) (hpath : PathQueriedInTrace H k tr i leaf path)
    (hver : merkleVerify H k d rt i leaf path = true)
    (hne : extractLeafFromTrace tr d rt i ≠ some leaf) (n : ℕ) :
    let col := extractTraceCollision H k tr i leaf path
    isCollision H (fun _ _ => true) n k col.1 col.2 = true := by
  obtain ⟨-, -, hne_q, hhash_eq⟩ := extractTraceCollision_spec hcons hpath hver hne
  simp [isCollision, hne_q, hhash_eq]

/-- Existential form of `extractTraceCollision_spec`: if an accepted opening with all hash steps in
`tr` disagrees with `extractLeafFromTrace`, then `tr` contains two distinct queries with the same
hash under `H k`. -/
theorem exists_collision_of_extractLeafFromTrace_ne {tr : List (List Bool × List Bool)} {d : ℕ}
    {rt : List Bool} {i : ℕ} {leaf : List Bool} {path : List (List Bool)}
    (hcons : TraceConsistentWith (H k) tr) (hpath : PathQueriedInTrace H k tr i leaf path)
    (hver : merkleVerify H k d rt i leaf path = true)
    (hne : extractLeafFromTrace tr d rt i ≠ some leaf) :
    ∃ q₁ ∈ tr.map Prod.fst, ∃ q₂ ∈ tr.map Prod.fst, q₁ ≠ q₂ ∧ H k q₁ = H k q₂ := by
  obtain ⟨hq₁, hq₂, hne_q, hhash_eq⟩ := extractTraceCollision_spec hcons hpath hver hne
  exact ⟨_, List.mem_map.mpr ⟨_, hq₁, rfl⟩,
    _, List.mem_map.mpr ⟨_, hq₂, rfl⟩, hne_q, hhash_eq⟩

end Extract

/-! ### Random-oracle collision and preimage probability bounds -/

section ProbabilityBounds

variable {Query α : Type} [BEq Query] [LawfulBEq Query]

/-- **Preimage / target-hitting union bound**: a uniform `m`-bit digest lands in a list `targets`
of candidate digests with probability at most `targets.length * (1 / 2 ^ m)`. -/
theorem toOuterMeasure_uniformList_mem_list_le (m : ℕ) (targets : List (List Bool)) :
    (BitString.uniformList m).toOuterMeasure {y | y ∈ targets} ≤
      (targets.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ m) := by
  calc (BitString.uniformList m).toOuterMeasure {y | y ∈ targets}
      ≤ (BitString.uniformList m).toOuterMeasure (targets.toFinset : Set (List Bool)) := by
        refine (BitString.uniformList m).toOuterMeasure.mono fun y hy => ?_
        exact List.mem_toFinset.mpr hy
    _ ≤ (targets.toFinset.card : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ m) :=
        BitString.toOuterMeasure_uniformList_finset_le m targets.toFinset
    _ ≤ (targets.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ m) := by
        gcongr
        exact_mod_cast List.toFinset_card_le targets

omit [BEq Query] [LawfulBEq Query] in
/-- Adding a freshly sampled `(q, ans)` to a collision-free trace `tr` violates
`TraceCollisionFree` only if `ans` hits one of the digests already recorded in `tr.map Prod.snd`. -/
theorem mem_map_snd_of_not_traceCollisionFree_cons {q : Query} {ans : List Bool}
    {tr : List (Query × List Bool)} (htr : TraceCollisionFree tr)
    (hbad : ¬ TraceCollisionFree ((q, ans) :: tr)) :
    ans ∈ tr.map Prod.snd := by
  rw [traceCollisionFree_cons_iff] at hbad
  push Not at hbad
  obtain ⟨p, hp, heq, -⟩ := hbad htr
  rw [← heq]
  exact List.mem_map.mpr ⟨p, hp, rfl⟩

omit [LawfulBEq Query] in
/-- **Single-step collision bound for a lazy random oracle**: from a collision-free trace `tr`,
one call to `memoize (fun _ => BitString.uniformList m) q tr` produces a trace with a collision
with probability at most `tr.length * (1 / 2 ^ m)`. -/
theorem toOuterMeasure_memoize_not_traceCollisionFree_step (m : ℕ) (q : Query)
    {tr : List (Query × List Bool)} (htr : TraceCollisionFree tr) :
    (memoize (fun _ : Query => BitString.uniformList m) q tr).toOuterMeasure
      {x | ¬ TraceCollisionFree x.2} ≤
      (tr.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ m) := by
  classical
  cases hlookup : tr.lookup q with
  | some ans =>
    rw [memoize_of_some _ _ _ _ hlookup, PMF.monad_pure_eq_pure, PMF.toOuterMeasure_pure_apply]
    simp [htr]
  | none =>
    rw [memoize_of_none _ _ _ hlookup]
    change ((BitString.uniformList m).map (fun ans => (ans, (q, ans) :: tr))).toOuterMeasure
      {x | ¬ TraceCollisionFree x.2} ≤ _
    rw [PMF.toOuterMeasure_map_apply]
    calc (BitString.uniformList m).toOuterMeasure
          {ans | ¬ TraceCollisionFree ((q, ans) :: tr)}
        ≤ (BitString.uniformList m).toOuterMeasure {ans | ans ∈ tr.map Prod.snd} := by
          refine (BitString.uniformList m).toOuterMeasure.mono fun ans hans => ?_
          exact mem_map_snd_of_not_traceCollisionFree_cons htr hans
      _ ≤ ((tr.map Prod.snd).length : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ m) :=
          toOuterMeasure_uniformList_mem_list_le m (tr.map Prod.snd)
      _ = (tr.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ m) := by simp

omit [LawfulBEq Query] in
/-- Each call to `memoize` increases the trace length by at most one. -/
theorem length_le_of_mem_support_memoize {Value : Type} (distribution : Query → PMF Value)
    (q : Query) (tr : List (Query × Value)) {x : Value × List (Query × Value)}
    (hx : x ∈ (memoize distribution q tr).support) :
    x.2.length ≤ tr.length + 1 := by
  rcases (RandomOracle.mem_support_memoize_iff distribution q tr x).mp hx with
    ⟨_, hnext⟩ | ⟨_, _, hnext⟩
  · rw [hnext]
    exact Nat.le_succ _
  · rw [hnext, List.length_cons]

omit [LawfulBEq Query] in
/-- **Accumulated collision bound for a query-bounded ROM program**: any `OracleComp` program
making at most `Q` queries to a lazy uniform `m`-bit random oracle starting from the empty trace
produces a collision in its final trace with probability at most `Q * (Q * (1 / 2 ^ m))`. -/
theorem toOuterMeasure_run_memoize_not_traceCollisionFree_le (m : ℕ)
    {program : OracleComp (fun _ : Query => List Bool) α} {Q : ℕ}
    (hQ : IsQueryBounded program Q) :
    ((OracleComp.interpret (memoize (fun _ : Query => BitString.uniformList m)) program).run
      []).toOuterMeasure {x | ¬ TraceCollisionFree x.2} ≤
      (Q : ℝ≥0∞) * ((Q : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ m)) := by
  have hbound := OracleComp.toOuterMeasure_bad_le
    (handler := memoize (fun _ : Query => BitString.uniformList m))
    (bad := fun tr => ¬ TraceCollisionFree tr)
    (fun _ => 1)
    (fun tr => (tr.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ m))
    ((1 : ℝ≥0∞) / 2 ^ m)
    (fun q tr htr => by
      rw [Nat.cast_one, one_mul]
      exact toOuterMeasure_memoize_not_traceCollisionFree_step m q (not_not.mp htr))
    (fun q tr _ x hx _ => by
      calc (x.2.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ m)
          ≤ ((tr.length + 1 : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ m) := by
            gcongr
            exact_mod_cast length_le_of_mem_support_memoize _ q tr hx
        _ = (tr.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ m) + (1 : ℝ≥0∞) / 2 ^ m := by
            rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul])
    hQ hQ (s := []) (not_not.mpr traceCollisionFree_nil)
  simpa using hbound

/-- If `tr` has no duplicate keys, then `tr` is consistent with the canonical lookup function
`fun q => (tr.lookup q).getD defaultDigest`. -/
theorem traceConsistentWith_lookup_of_nodup {Digest : Type*} (tr : List (Query × Digest))
    (defaultDigest : Digest) (hnodup : (tr.map Prod.fst).Nodup) :
    TraceConsistentWith (fun q => (tr.lookup q).getD defaultDigest) tr := by
  induction tr with
  | nil => exact traceConsistentWith_nil _
  | cons entry rest ih =>
    rcases entry with ⟨q, ans⟩
    rw [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hq_not_mem, hnodup_rest⟩ := hnodup
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · simp
    · have hne : p.1 ≠ q := by
        intro heq
        apply hq_not_mem
        rw [← heq]
        exact List.mem_map.mpr ⟨p, hp, rfl⟩
      dsimp only
      rw [List.lookup_cons, beq_false_of_ne hne]
      exact ih hnodup_rest p hp

private theorem lookup_ne_none_of_mem {Value : Type}
    {tr : List (Query × Value)} {q : Query} {v : Value} (h : (q, v) ∈ tr) :
    tr.lookup q ≠ none := by
  induction tr with
  | nil => cases h
  | cons hd tl ih =>
    rw [List.lookup_cons]
    cases heq : q == hd.1
    · rcases List.mem_cons.mp h with rfl | htl
      · simp at heq
      · exact ih htl
    · exact Option.some_ne_none _

/-- A single call to `memoize` records `(q, ans)` in the output trace, preserves existing entries,
keeps keys `Nodup`, and preserves support membership in `dist`. -/
theorem mem_support_memoize_nodup {Value : Type}
    (dist : Query → PMF Value) (q : Query) {tr tr' : List (Query × Value)} {ans : Value}
    (hnodup : (tr.map Prod.fst).Nodup)
    (hsupp : ∀ e ∈ tr, e.2 ∈ (dist e.1).support)
    (hmem : (ans, tr') ∈ (memoize dist q tr).support) :
    (q, ans) ∈ tr' ∧
      (∀ e ∈ tr, e ∈ tr') ∧
      (tr'.map Prod.fst).Nodup ∧
      (∀ e ∈ tr', e.2 ∈ (dist e.1).support) := by
  rcases (RandomOracle.mem_support_memoize_iff dist q tr (ans, tr')).mp hmem with
    ⟨hlookup, hnext⟩ | ⟨hlookup, hans, hnext⟩
  · change tr' = tr at hnext
    subst hnext
    obtain ⟨before, after, hlist, _⟩ := List.lookup_eq_some_iff.mp hlookup
    exact ⟨by simp [hlist], fun _ h => h, hnodup, hsupp⟩
  · change ans ∈ (dist q).support at hans
    change tr' = (q, ans) :: tr at hnext
    subst hnext
    refine ⟨List.mem_cons_self, fun _ h => List.mem_cons_of_mem _ h, ?_, ?_⟩
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, hnodup⟩
      rintro hq_in
      obtain ⟨⟨q', v'⟩, hp, rfl⟩ := List.mem_map.mp hq_in
      exact lookup_ne_none_of_mem hp hlookup
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hans
      · exact hsupp e he

end ProbabilityBounds

end Cslib.Crypto
