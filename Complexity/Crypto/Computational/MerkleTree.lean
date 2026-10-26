/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.CollisionResistant
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Foundations.Data.Nat.Log
import Complexity.Tactic.PolyTime
import Mathlib.Data.List.GetD

/-!
# Merkle trees

A Merkle tree hashes a list of leaves to a single root so that each leaf can later be opened
against the root with a short authentication path ([Merkle1989], Section 6; [BonehShoup2023],
Section 8.9). Here the hash is a keyed function `H : List Bool → List Bool → List Bool`, as in
`CollisionResistant`. As in both sources, a leaf `x` becomes the node `H k x`, and the parent of
nodes `l` and `r` is `H k (encPair encBits encBits (l, r))`. The pairing `encPair` is injective,
so nodes of any length can be paired without ambiguity.

The tree over `leaves` has depth `Nat.clog 2 leaves.length`, the least `d` with
`leaves.length ≤ 2 ^ d`. Missing leaves read as the empty word, padding the tree to `2 ^ d` leaves
as [BonehShoup2023] suggests. For `2 ^ d` leaves this is Merkle's `H(1, 2 ^ d, Y)`, with his
`Y_i` as `leaves.getD (i - 1) []`. For other leaf counts it differs from Merkle's recursion, which
splits at the midpoint without padding.

An authentication path for position `i` lists the sibling of each node on the way from leaf `i`
to the root. `merkleRootOfPath` recomputes a root from a leaf, a position and a path. Its
correctness is `merkleRootOfPath_merklePath`. Binding is `isCollision_extractMerkleCollision`: two
openings of the same position to different leaves, along paths of equal length and with the same
recomputed root, contain a collision of `H k`, found deterministically by
`extractMerkleCollision`. This is the reduction behind [BonehShoup2023], Theorem 8.8.

**What a verifier must check.** Leaves and internal nodes are hashed with the same `H k`, with no
domain separation, so a recomputed root alone binds nothing. A verifier must fix the path length
to the depth `d` and check `i < 2 ^ d`:

* with a shorter path, an internal node's hash input opens as a leaf; for leaves `[a, b]`, the
  "leaf" `encPair encBits encBits (H k a, H k b)` at position `0` with path `[]` recomputes the
  root;
* `merkleRootOfPath` reads only the low `path.length` bits of `i`, so positions wrap modulo
  `2 ^ path.length`;
* the root does not fix the number of leaves: `[a, b, c]` and `[a, b, c, []]` have the same root.

The root, the path, root recomputation and extraction have plain polynomial-time certificates for
hash families whose digests have the length of the key. Positions are unary in these
certificates, which suits trees with polynomially many leaves.

## Main definitions

* `Cslib.Crypto.merkleParents`, `Cslib.Crypto.merkleLevel`: one level of the tree from the one
  below, and level `j` counted from the hashed leaves.
* `Cslib.Crypto.merkleRoot`, `Cslib.Crypto.merklePath`: the root and the authentication path of
  a position.
* `Cslib.Crypto.merkleInputs`, `Cslib.Crypto.merkleRootOfPath`: the hash inputs met while
  recomputing a root from an opening, and the recomputed root.
* `Cslib.Crypto.extractMerkleCollision`: the first differing pair of hash inputs of two openings.

## Main results

* `Cslib.Crypto.length_merkleLevel`, `Cslib.Crypto.length_merklePath`: level sizes and path
  length.
* `Cslib.Crypto.merkleRootOfPath_merklePath`: an honest opening recomputes the root.
* `Cslib.Crypto.isCollision_extractMerkleCollision`: a second opening of a position yields a
  collision.
* `Cslib.Crypto.computableInPolyTime_merkleRoot`, `Cslib.Crypto.computableInPolyTime_merklePath`,
  `Cslib.Crypto.computableInPolyTime_merkleRootOfPath`,
  `Cslib.Crypto.computableInPolyTime_extractMerkleCollision`: plain polynomial-time certificates.

## References

* [R. C. Merkle, *A Certified Digital Signature*][Merkle1989], Section 6.
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Section 8.9,
  Figure 8.12 and Theorem 8.8.
-/

@[expose] public section

namespace Cslib.Crypto

open Turing.MultiTapeTM

variable (H : List Bool → List Bool → List Bool) (k : List Bool)

/-! ### The tree -/

/-- The hashed leaves of the tree over `leaves`, padded with the empty word to `2 ^ d` leaves for
`d = Nat.clog 2 leaves.length`. -/
def merkleLeafLevel (leaves : List (List Bool)) : List (List Bool) :=
  (List.range (2 ^ Nat.clog 2 leaves.length)).map fun i => H k (leaves.getD i [])

/-- The parents of a level: node `i` hashes the pair of nodes `2 * i` and `2 * i + 1`. -/
def merkleParents (level : List (List Bool)) : List (List Bool) :=
  (List.range (level.length / 2)).map fun i =>
    H k (encPair encBits encBits (level.getD (2 * i) [], level.getD (2 * i + 1) []))

/-- Level `j` of the tree over `leaves`, counted from the hashed leaves at level `0`. -/
def merkleLevel (leaves : List (List Bool)) (j : ℕ) : List (List Bool) :=
  (merkleParents H k)^[j] (merkleLeafLevel H k leaves)

/-- The root of the Merkle tree over `leaves` ([BonehShoup2023], Section 8.9). -/
def merkleRoot (leaves : List (List Bool)) : List Bool :=
  (merkleLevel H k leaves (Nat.clog 2 leaves.length)).headD []

/-- The position of the sibling of node `p` within its level. -/
def merkleSibling (p : ℕ) : ℕ :=
  if p % 2 = 0 then p + 1 else p - 1

/-- One step of `merklePath`: record the sibling of the current node, then move to the parent
level and position. -/
def merklePathStep (state : List (List Bool) × ℕ × List (List Bool)) :
    List (List Bool) × ℕ × List (List Bool) :=
  (merkleParents H k state.1, state.2.1 / 2,
    state.2.2 ++ [state.1.getD (merkleSibling state.2.1) []])

/-- The authentication path of position `i`: the sibling of each node on the way from leaf `i` up
to the root, starting at the leaves ([BonehShoup2023], Figure 8.12). -/
def merklePath (leaves : List (List Bool)) (i : ℕ) : List (List Bool) :=
  ((merklePathStep H k)^[Nat.clog 2 leaves.length] (merkleLeafLevel H k leaves, i, [])).2.2

/-! ### Recomputing a root from an opening -/

/-- One step of `merkleInputs`: hash the current input to a node and pair it with `sibling`,
putting the node on the left when the current position is even. -/
def merkleInputsStep (state : List (List Bool) × ℕ) (sibling : List Bool) :
    List (List Bool) × ℕ :=
  let node := H k (state.1.headD [])
  ((if state.2 % 2 = 0 then encPair encBits encBits (node, sibling)
    else encPair encBits encBits (sibling, node)) :: state.1, state.2 / 2)

/-- The hash inputs met while recomputing a root from `leaf` at position `i` along `path`, from
the input of the root down to `leaf` itself. -/
def merkleInputs (leaf : List Bool) (i : ℕ) (path : List (List Bool)) : List (List Bool) :=
  (path.foldl (merkleInputsStep H k) ([leaf], i)).1

/-- The root recomputed from `leaf` at position `i` along the authentication path `path`
([BonehShoup2023], (8.16)). Only the low `path.length` bits of `i` are read, and nothing checks
the path length: a verifier must fix `path.length` to the depth `d` and check `i < 2 ^ d` (see
the module documentation). -/
def merkleRootOfPath (leaf : List Bool) (i : ℕ) (path : List (List Bool)) : List Bool :=
  H k ((merkleInputs H k leaf i path).headD [])

/-- The first pair of differing hash inputs, from the root down, of two openings of position `i`,
or `([], [])` if there is none. -/
def extractMerkleCollision (leaf₁ leaf₂ : List Bool) (i : ℕ) (path₁ path₂ : List (List Bool)) :
    List Bool × List Bool :=
  (((merkleInputs H k leaf₁ i path₁).zip (merkleInputs H k leaf₂ i path₂)).find?
    (fun p => p.1 != p.2)).getD ([], [])

variable {H k}

/-! ### Shape of the tree -/

/-- The tree over `leaves` has `2 ^ Nat.clog 2 leaves.length` hashed leaves. -/
@[simp]
theorem length_merkleLeafLevel (leaves : List (List Bool)) :
    (merkleLeafLevel H k leaves).length = 2 ^ Nat.clog 2 leaves.length := by
  simp [merkleLeafLevel]

/-- A level has half as many parents as nodes, rounded down. -/
@[simp]
theorem length_merkleParents (level : List (List Bool)) :
    (merkleParents H k level).length = level.length / 2 := by
  simp [merkleParents]

/-- Parent `i` hashes the pair of nodes `2 * i` and `2 * i + 1`. -/
theorem getD_merkleParents {level : List (List Bool)} {i : ℕ} (hi : i < level.length / 2) :
    (merkleParents H k level).getD i [] =
      H k (encPair encBits encBits (level.getD (2 * i) [], level.getD (2 * i + 1) [])) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp [merkleParents]

/-- Level `j` of the tree of depth `d = Nat.clog 2 leaves.length` has `2 ^ d / 2 ^ j` nodes. -/
theorem length_merkleLevel (leaves : List (List Bool)) (j : ℕ) :
    (merkleLevel H k leaves j).length = 2 ^ Nat.clog 2 leaves.length / 2 ^ j := by
  induction j with
  | zero => simp [merkleLevel]
  | succ j ih =>
    rw [merkleLevel, Function.iterate_succ_apply', ← merkleLevel, length_merkleParents, ih,
      Nat.div_div_eq_div_mul, ← pow_succ]

/-- Each level consists of the parents of the level below. -/
theorem merkleLevel_succ (leaves : List (List Bool)) (j : ℕ) :
    merkleLevel H k leaves (j + 1) = merkleParents H k (merkleLevel H k leaves j) := by
  rw [merkleLevel, Function.iterate_succ_apply', ← merkleLevel]

private theorem merklePathStep_iterate (leaves : List (List Bool)) (i j : ℕ) :
    (merklePathStep H k)^[j] (merkleLeafLevel H k leaves, i, []) =
      (merkleLevel H k leaves j, i / 2 ^ j, (List.range j).map fun t =>
        (merkleLevel H k leaves t).getD (merkleSibling (i / 2 ^ t)) []) := by
  induction j with
  | zero => simp [merkleLevel]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [merklePathStep, merkleLevel_succ, Nat.div_div_eq_div_mul, ← pow_succ,
      List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- The authentication path of position `i` lists, for each level `t` below the root, the sibling
of the ancestor of leaf `i` at level `t`. -/
theorem merklePath_eq (leaves : List (List Bool)) (i : ℕ) :
    merklePath H k leaves i = (List.range (Nat.clog 2 leaves.length)).map fun t =>
      (merkleLevel H k leaves t).getD (merkleSibling (i / 2 ^ t)) [] := by
  rw [merklePath, merklePathStep_iterate]

/-- An authentication path has one sibling per level below the root. -/
@[simp]
theorem length_merklePath (leaves : List (List Bool)) (i : ℕ) :
    (merklePath H k leaves i).length = Nat.clog 2 leaves.length := by
  simp [merklePath_eq]

/-- Hashed leaves have the length of the key when the hash's digests do. -/
theorem length_of_mem_merkleLeafLevel (hlen : ∀ k x, (H k x).length = k.length)
    {leaves : List (List Bool)} {y : List Bool} (hy : y ∈ merkleLeafLevel H k leaves) :
    y.length = k.length := by
  simp only [merkleLeafLevel, List.mem_map] at hy
  obtain ⟨_, _, rfl⟩ := hy
  exact hlen _ _

/-- Parents have the length of the key when the hash's digests do. -/
theorem length_of_mem_merkleParents (hlen : ∀ k x, (H k x).length = k.length)
    {level : List (List Bool)} {y : List Bool} (hy : y ∈ merkleParents H k level) :
    y.length = k.length := by
  simp only [merkleParents, List.mem_map] at hy
  obtain ⟨_, _, rfl⟩ := hy
  exact hlen _ _

/-! ### Correctness of honest openings -/

private theorem merkleInputs_append (leaf : List Bool) (i : ℕ) (path : List (List Bool))
    (sibling : List Bool) :
    (path ++ [sibling]).foldl (merkleInputsStep H k) ([leaf], i) =
      merkleInputsStep H k (path.foldl (merkleInputsStep H k) ([leaf], i)) sibling :=
  List.foldl_concat _ _ _ _

private theorem snd_foldl_merkleInputsStep (leaf : List Bool) (i : ℕ) (path : List (List Bool)) :
    (path.foldl (merkleInputsStep H k) ([leaf], i)).2 = i / 2 ^ path.length := by
  induction path using List.reverseRecOn with
  | nil => simp
  | append_singleton path sibling ih =>
    rw [merkleInputs_append]
    simp only [merkleInputsStep, ih, List.length_append, List.length_singleton,
      Nat.div_div_eq_div_mul, ← pow_succ]

/-- Opening leaf `i < 2 ^ d` with its honest path recomputes, after `j` steps, the ancestor of
the leaf at level `j`. -/
private theorem hash_head_merkleInputs_take (leaves : List (List Bool)) {i : ℕ}
    (hi : i < 2 ^ Nat.clog 2 leaves.length) (j : ℕ) (hj : j ≤ Nat.clog 2 leaves.length) :
    H k ((((merklePath H k leaves i).take j).foldl (merkleInputsStep H k)
      ([leaves.getD i []], i)).1.headD []) =
      (merkleLevel H k leaves j).getD (i / 2 ^ j) [] := by
  set d := Nat.clog 2 leaves.length
  induction j with
  | zero =>
    have hlt : i < (merkleLeafLevel H k leaves).length := by simpa using hi
    simp only [List.take_zero, List.foldl_nil, List.headD_cons, merkleLevel,
      Function.iterate_zero, id, pow_zero, Nat.div_one]
    rw [List.getD_eq_getElem _ _ hlt]
    simp only [merkleLeafLevel, List.getElem_map, List.getElem_range]
  | succ j ih =>
    have hjd : j < d := hj
    have hpath : j < (merklePath H k leaves i).length := by simpa using hjd
    rw [List.take_succ_eq_append_getElem hpath, merkleInputs_append]
    have hsnd := snd_foldl_merkleInputsStep (H := H) (k := k) (leaves.getD i []) i
      ((merklePath H k leaves i).take j)
    rw [List.length_take_of_le hpath.le] at hsnd
    simp only [merkleInputsStep, List.headD_cons, hsnd, ih hjd.le]
    have hsib : (merklePath H k leaves i)[j] =
        (merkleLevel H k leaves j).getD (merkleSibling (i / 2 ^ j)) [] := by
      simp [merklePath_eq]
    rw [hsib, merkleLevel_succ]
    have hlevel := length_merkleLevel (H := H) (k := k) leaves j
    have hq : i / 2 ^ (j + 1) < (merkleLevel H k leaves j).length / 2 := by
      rw [hlevel, Nat.div_div_eq_div_mul, ← pow_succ]
      exact Nat.div_lt_div_of_lt_of_dvd (pow_dvd_pow 2 (by omega)) hi
    rw [getD_merkleParents hq]
    have hdiv : i / 2 ^ (j + 1) = i / 2 ^ j / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
    rw [hdiv]
    rcases Nat.mod_two_eq_zero_or_one (i / 2 ^ j) with hp | hp
    · have h1 : 2 * (i / 2 ^ j / 2) = i / 2 ^ j := by omega
      simp only [hp, ↓reduceIte, merkleSibling, h1]
    · have h1 : 2 * (i / 2 ^ j / 2) = i / 2 ^ j - 1 := by omega
      have h2 : 2 * (i / 2 ^ j / 2) + 1 = i / 2 ^ j := by omega
      rw [h2, h1]
      simp only [hp, one_ne_zero, ↓reduceIte, merkleSibling]

/-- **Correctness**: opening leaf `i` with its authentication path recomputes the root. -/
theorem merkleRootOfPath_merklePath (leaves : List (List Bool)) {i : ℕ}
    (hi : i < 2 ^ Nat.clog 2 leaves.length) :
    merkleRootOfPath H k (leaves.getD i []) i (merklePath H k leaves i) =
      merkleRoot H k leaves := by
  have h := hash_head_merkleInputs_take (H := H) (k := k) leaves hi _ le_rfl
  rw [← length_merklePath (H := H) (k := k) leaves i, List.take_length] at h
  rw [merkleRootOfPath, merkleInputs, h, merkleRoot, length_merklePath,
    Nat.div_eq_of_lt hi, List.headD_eq_getD]

/-! ### Binding -/

/-- The property preserved by each step of two openings of one position: when the current hash
inputs hash to the same node, the scan of `extractMerkleCollision` finds a collision. -/
private def ScanFinds (H : List Bool → List Bool → List Bool) (k : List Bool)
    (inputs₁ inputs₂ : List (List Bool)) : Prop :=
  H k (inputs₁.headD []) = H k (inputs₂.headD []) →
    ∃ x₁ x₂, (inputs₁.zip inputs₂).find? (fun p => p.1 != p.2) = some (x₁, x₂) ∧
      H k x₁ = H k x₂

private theorem scanFinds_cons {inputs₁ inputs₂ : List (List Bool)} {a b : List Bool}
    (h : ScanFinds H k inputs₁ inputs₂)
    (hab : a = b → H k (inputs₁.headD []) = H k (inputs₂.headD [])) :
    ScanFinds H k (a :: inputs₁) (b :: inputs₂) := by
  intro hhash
  rw [List.headD_cons, List.headD_cons] at hhash
  rw [List.zip_cons_cons, List.find?_cons]
  by_cases hab' : a = b
  · subst hab'
    simp only [bne_self_eq_false]
    exact h (hab rfl)
  · simp only [bne_iff_ne.mpr hab']
    exact ⟨a, b, rfl, hhash⟩

private theorem scanFinds_step {inputs₁ inputs₂ : List (List Bool)} {i : ℕ}
    (h : ScanFinds H k inputs₁ inputs₂) (sibling₁ sibling₂ : List Bool) :
    ScanFinds H k (merkleInputsStep H k (inputs₁, i) sibling₁).1
      (merkleInputsStep H k (inputs₂, i) sibling₂).1 := by
  have hinj := (encPair encBits encBits).injective
  by_cases hi : i % 2 = 0
  · simp only [merkleInputsStep, hi, ↓reduceIte]
    exact scanFinds_cons h fun hab => congrArg Prod.fst (hinj hab)
  · simp only [merkleInputsStep, hi, ↓reduceIte]
    exact scanFinds_cons h fun hab => congrArg Prod.snd (hinj hab)

private theorem scanFinds_foldl {inputs₁ inputs₂ : List (List Bool)} {i : ℕ}
    (h : ScanFinds H k inputs₁ inputs₂) (path₁ path₂ : List (List Bool))
    (hlen : path₁.length = path₂.length) :
    ScanFinds H k (path₁.foldl (merkleInputsStep H k) (inputs₁, i)).1
      (path₂.foldl (merkleInputsStep H k) (inputs₂, i)).1 := by
  induction path₁ generalizing path₂ inputs₁ inputs₂ i with
  | nil =>
    rw [List.length_nil, eq_comm, List.length_eq_zero_iff] at hlen
    subst hlen
    exact h
  | cons sibling₁ path₁ ih =>
    cases path₂ with
    | nil => simp at hlen
    | cons sibling₂ path₂ =>
      simp only [List.foldl_cons]
      have hstep := scanFinds_step (i := i) h sibling₁ sibling₂
      exact ih hstep path₂ (by simpa using hlen)

/-- **Binding**, the deterministic reduction behind [BonehShoup2023], Theorem 8.8: two openings
of position `i` to different leaves, along paths of equal length and with the same recomputed
root, contain a collision of `H k`, which `extractMerkleCollision` finds. Equal path lengths are
essential, since leaves and internal nodes are not domain-separated; a verifier that fixes the
path length to the depth `d` and checks `i < 2 ^ d` gives this hypothesis. -/
theorem isCollision_extractMerkleCollision {leaf₁ leaf₂ : List Bool} {i : ℕ}
    {path₁ path₂ : List (List Bool)} (n : ℕ) (hlen : path₁.length = path₂.length)
    (hne : leaf₁ ≠ leaf₂)
    (hroot : merkleRootOfPath H k leaf₁ i path₁ = merkleRootOfPath H k leaf₂ i path₂) :
    isCollision H (fun _ _ => true) n k (extractMerkleCollision H k leaf₁ leaf₂ i path₁ path₂).1
      (extractMerkleCollision H k leaf₁ leaf₂ i path₁ path₂).2 = true := by
  have hbase : ScanFinds H k [leaf₁] [leaf₂] := by
    intro hhash
    exact ⟨leaf₁, leaf₂, by simp [hne], by simpa using hhash⟩
  obtain ⟨x₁, x₂, hfind, hhash⟩ := scanFinds_foldl (i := i) hbase path₁ path₂ hlen hroot
  have hne' : x₁ ≠ x₂ := by
    have := List.find?_some hfind
    simpa using this
  rw [extractMerkleCollision, merkleInputs, merkleInputs, hfind, Option.getD_some]
  simp [isCollision, hne', hhash]

/-! ### Polynomial time -/

section PolyTime

variable {γ : Type} {encIn : γ ↪ List Bool}

private theorem pow_clog_two_le (L : ℕ) : 2 ^ Nat.clog 2 L ≤ 2 * L + 1 := by
  rcases eq_or_ne L 0 with rfl | hL
  · simp
  · exact (Nat.pow_clog_le_mul (by norm_num) hL).trans (Nat.le_succ _)

private theorem computableTidilyInPolyTime_hash
    (hH : ComputableTidilyInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    {k x : γ → List Bool} (hk : ComputableTidilyInPolyTime k encIn encBits)
    (hx : ComputableTidilyInPolyTime x encIn encBits) :
    ComputableTidilyInPolyTime (fun a => H (k a) (x a)) encIn encBits :=
  hH.comp (hk.prod hx)

private theorem computableTidilyInPolyTime_pairWord {x y : γ → List Bool}
    (hx : ComputableTidilyInPolyTime x encIn encBits)
    (hy : ComputableTidilyInPolyTime y encIn encBits) :
    ComputableTidilyInPolyTime (fun a => encPair encBits encBits (x a, y a)) encIn encBits :=
  (ComputableTidilyInPolyTime.of_eq (encIn := encPair encBits encBits) (encMid := encBits)
    fun _ => rfl).comp (hx.prod hy)

private theorem computableTidilyInPolyTime_merkleLeafLevel
    (hH : ComputableTidilyInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    {k : γ → List Bool} {leaves : γ → List (List Bool)}
    (hk : ComputableTidilyInPolyTime k encIn encBits)
    (hleaves : ComputableTidilyInPolyTime leaves encIn (encList encBits)) :
    ComputableTidilyInPolyTime (fun a => merkleLeafLevel H (k a) (leaves a)) encIn
      (encList encBits) := by
  unfold merkleLeafLevel
  have hcount : ComputableTidilyInPolyTime
      (fun a => 2 ^ Nat.clog 2 (leaves a).length) encIn encUnary :=
    ComputableTidilyInPolyTime.unary_pow_clog_const
      ((ComputableTidilyInPolyTime.length encBits).comp hleaves) 2 2
  refine ComputableTidilyInPolyTime.mapWithInput
    (ComputableTidilyInPolyTime.range.comp hcount) ?_
  have hget : ComputableTidilyInPolyTime (fun p : γ × ℕ => (leaves p.1).getD p.2 [])
      (encPair encIn encUnary) encBits :=
    (ComputableTidilyInPolyTime.listGetD (encA := encBits) []).comp
      ((hleaves.comp (ComputableTidilyInPolyTime.fst _ _)).prod
        (ComputableTidilyInPolyTime.snd _ _))
  exact computableTidilyInPolyTime_hash hH (hk.comp (ComputableTidilyInPolyTime.fst _ _)) hget

private theorem computableTidilyInPolyTime_merkleParents
    (hH : ComputableTidilyInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    {k : γ → List Bool} {level : γ → List (List Bool)}
    (hk : ComputableTidilyInPolyTime k encIn encBits)
    (hlevel : ComputableTidilyInPolyTime level encIn (encList encBits)) :
    ComputableTidilyInPolyTime (fun a => merkleParents H (k a) (level a)) encIn
      (encList encBits) := by
  unfold merkleParents
  have hcount : ComputableTidilyInPolyTime (fun a => (level a).length / 2) encIn encUnary :=
    (ComputableTidilyInPolyTime.unary_div_const 2).comp
      ((ComputableTidilyInPolyTime.length encBits).comp hlevel)
  refine ComputableTidilyInPolyTime.mapWithInput
    (ComputableTidilyInPolyTime.range.comp hcount) ?_
  have hlevel' := hlevel.comp (ComputableTidilyInPolyTime.fst encIn encUnary)
  have hi := ComputableTidilyInPolyTime.snd encIn encUnary
  have hget (offset : ℕ) : ComputableTidilyInPolyTime
      (fun p : γ × ℕ => (level p.1).getD (2 * p.2 + offset) []) (encPair encIn encUnary)
      encBits :=
    (ComputableTidilyInPolyTime.listGetD (encA := encBits) []).comp
      (hlevel'.prod (by polytime))
  have hleft : ComputableTidilyInPolyTime
      (fun p : γ × ℕ => (level p.1).getD (2 * p.2) []) (encPair encIn encUnary) encBits := by
    simpa using hget 0
  exact computableTidilyInPolyTime_hash hH (hk.comp (ComputableTidilyInPolyTime.fst _ _))
    (computableTidilyInPolyTime_pairWord hleft (hget 1))

private theorem computableTidilyInPolyTime_iterate_merkleParents
    (hH : ComputableTidilyInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length) :
    ComputableTidilyInPolyTime (fun p : List Bool × List (List Bool) =>
      (merkleParents H p.1)^[Nat.clog 2 p.2.length] (merkleLeafLevel H p.1 p.2))
      (encPair encBits (encList encBits)) (encList encBits) := by
  have hk := ComputableTidilyInPolyTime.fst encBits (encList encBits)
  have hleaves := ComputableTidilyInPolyTime.snd encBits (encList encBits)
  refine (ComputableTidilyInPolyTime.iterateWith_spec
    (par := fun p : List Bool × List (List Bool) => p.1)
    (count := fun p => Nat.clog 2 p.2.length)
    (step := fun k level => merkleParents H k level)
    hk ((ComputableTidilyInPolyTime.unary_clog_const 2).comp
      ((ComputableTidilyInPolyTime.length encBits).comp hleaves))
    (computableTidilyInPolyTime_merkleLeafLevel hH hk hleaves)
    (computableTidilyInPolyTime_merkleParents hH (ComputableTidilyInPolyTime.fst _ _)
      (ComputableTidilyInPolyTime.snd _ _))
    (fun p _ level => (∀ y ∈ level, y.length = p.1.length) ∧
      level.length ≤ 2 ^ Nat.clog 2 p.2.length)
    (fun p => ⟨fun y hy => length_of_mem_merkleLeafLevel hlen hy, by simp⟩)
    (fun p _ level _ hinv => ⟨fun y hy => length_of_mem_merkleParents hlen hy,
      by simpa using (Nat.div_le_self _ _).trans hinv.2⟩)
    (size := fun p => (2 * p.2.length + 1) * (2 * p.1.length + 1))
    ?_ ?_).1
  · refine PolyBounded.of_forall_le 9 2 fun p => ?_
    have h1 : p.1.length ≤ (encPair encBits (encList encBits) p).length := by
      simp only [encPair_apply, encBits_apply, List.length_append, length_frame]
      omega
    have h2 : p.2.length ≤ (encPair encBits (encList encBits) p).length := by
      have := length_le_length_encList encBits p.2
      simp only [length_encPair, encBits_apply]
      omega
    set s := (encPair encBits (encList encBits) p).length
    calc (2 * p.2.length + 1) * (2 * p.1.length + 1) ≤ (2 * s + 1) * (2 * s + 1) := by
          gcongr
      _ ≤ 9 * (s + 1) ^ 2 := by nlinarith
  · intro p _ level _ hinv
    refine (length_encList_le encBits _ fun y hy => (hinv.1 y hy).le).trans ?_
    exact Nat.mul_le_mul_right _ (hinv.2.trans (pow_clog_two_le _))

private theorem computableTidilyInPolyTime_merkleRoot
    (hH : ComputableTidilyInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length) :
    ComputableTidilyInPolyTime (fun p : List Bool × List (List Bool) => merkleRoot H p.1 p.2)
      (encPair encBits (encList encBits)) encBits :=
  ComputableTidilyInPolyTime.listHeadDWithInput []
    (computableTidilyInPolyTime_iterate_merkleParents hH hlen)

/-- Computing the root of a Merkle tree is polynomial-time for a polynomial-time keyed hash whose
digests have the length of the key. -/
@[program_certificate]
theorem computableInPolyTime_merkleRoot
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length) :
    ComputableInPolyTime (fun p : List Bool × List (List Bool) => merkleRoot H p.1 p.2)
      (encPair encBits (encList encBits)) encBits :=
  .of_tidy (computableTidilyInPolyTime_merkleRoot hH.tidy hlen)

private theorem computableTidilyInPolyTime_merkleSibling :
    ComputableTidilyInPolyTime merkleSibling encUnary encUnary := by
  unfold merkleSibling
  polytime

private theorem computableTidilyInPolyTime_merklePathStep
    (hH : ComputableTidilyInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableTidilyInPolyTime
      (fun p : List Bool × (List (List Bool) × ℕ × List (List Bool)) => merklePathStep H p.1 p.2)
      (encPair encBits (encPair (encList encBits) (encPair encUnary (encList encBits))))
      (encPair (encList encBits) (encPair encUnary (encList encBits))) := by
  have hk := ComputableTidilyInPolyTime.fst encBits
    (encPair (encList encBits) (encPair encUnary (encList encBits)))
  have hstate := ComputableTidilyInPolyTime.snd encBits
    (encPair (encList encBits) (encPair encUnary (encList encBits)))
  have hlevel := (ComputableTidilyInPolyTime.fst _ _).comp hstate
  have hidx := (ComputableTidilyInPolyTime.fst _ _).comp
    ((ComputableTidilyInPolyTime.snd _ _).comp hstate)
  have hpath := (ComputableTidilyInPolyTime.snd _ _).comp
    ((ComputableTidilyInPolyTime.snd _ _).comp hstate)
  have hsib := (ComputableTidilyInPolyTime.listGetD (encA := encBits) []).comp
    (hlevel.prod (computableTidilyInPolyTime_merkleSibling.comp hidx))
  exact (computableTidilyInPolyTime_merkleParents hH hk hlevel).prod
    (((ComputableTidilyInPolyTime.unary_div_const 2).comp hidx).prod
      (ComputableTidilyInPolyTime.listAppend' hpath
        (ComputableTidilyInPolyTime.cons' hsib (ComputableTidilyInPolyTime.const []))))

private theorem computableTidilyInPolyTime_merklePath
    (hH : ComputableTidilyInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length) :
    ComputableTidilyInPolyTime
      (fun p : List Bool × List (List Bool) × ℕ => merklePath H p.1 p.2.1 p.2.2)
      (encPair encBits (encPair (encList encBits) encUnary)) (encList encBits) := by
  have hk := ComputableTidilyInPolyTime.fst encBits (encPair (encList encBits) encUnary)
  have hleaves := (ComputableTidilyInPolyTime.fst _ _).comp
    (ComputableTidilyInPolyTime.snd encBits (encPair (encList encBits) encUnary))
  have hi := (ComputableTidilyInPolyTime.snd _ _).comp
    (ComputableTidilyInPolyTime.snd encBits (encPair (encList encBits) encUnary))
  have hinit : ComputableTidilyInPolyTime
      (fun p : List Bool × List (List Bool) × ℕ =>
        (merkleLeafLevel H p.1 p.2.1, p.2.2, ([] : List (List Bool))))
      (encPair encBits (encPair (encList encBits) encUnary))
      (encPair (encList encBits) (encPair encUnary (encList encBits))) :=
    (computableTidilyInPolyTime_merkleLeafLevel hH hk hleaves).prod
      (hi.prod (ComputableTidilyInPolyTime.const []))
  have hiter := (ComputableTidilyInPolyTime.iterateWith_spec
    (par := fun p : List Bool × List (List Bool) × ℕ => p.1)
    (count := fun p => Nat.clog 2 p.2.1.length)
    (step := fun k state => merklePathStep H k state)
    hk ((ComputableTidilyInPolyTime.unary_clog_const 2).comp
      ((ComputableTidilyInPolyTime.length encBits).comp hleaves))
    hinit (computableTidilyInPolyTime_merklePathStep hH)
    (fun p j state => (∀ y ∈ state.1, y.length = p.1.length) ∧
      state.1.length ≤ 2 ^ Nat.clog 2 p.2.1.length ∧ state.2.1 ≤ p.2.2 ∧
      (∀ y ∈ state.2.2, y.length ≤ p.1.length) ∧ state.2.2.length ≤ j)
    (fun p => ⟨fun y hy => length_of_mem_merkleLeafLevel hlen hy, by simp, le_rfl,
      by simp, by simp⟩)
    (fun p j state _ hinv => ⟨fun y hy => length_of_mem_merkleParents hlen hy,
      by simpa [merklePathStep] using (Nat.div_le_self _ _).trans hinv.2.1,
      (Nat.div_le_self _ _).trans hinv.2.2.1,
      by
        intro y hy
        simp only [merklePathStep, List.mem_append, List.mem_singleton] at hy
        rcases hy with hy | rfl
        · exact hinv.2.2.2.1 y hy
        · rw [List.getD_eq_getElem?_getD]
          cases hget : state.1[merkleSibling state.2.1]? with
          | none => simp
          | some y => exact (hinv.1 y (List.mem_of_getElem? hget)).le,
      by simpa [merklePathStep] using hinv.2.2.2.2⟩)
    (size := fun p => 3 * ((2 * p.2.1.length + 1) * (2 * p.1.length + 1)) + 2 * p.2.2 + 2)
    ?_ ?_).1
  · exact (ComputableTidilyInPolyTime.snd _ _).comp
      ((ComputableTidilyInPolyTime.snd _ _).comp hiter)
  · refine PolyBounded.of_forall_le 40 2 fun p => ?_
    set s := (encPair encBits (encPair (encList encBits) encUnary) p).length
    have h1 : p.1.length ≤ s := by
      simp only [s, encPair_apply, encBits_apply, List.length_append, length_frame]
      omega
    have h2 : p.2.1.length ≤ s := by
      have := length_le_length_encList encBits p.2.1
      simp only [s, encPair_apply, encBits_apply, List.length_append, length_frame]
      omega
    have h3 : p.2.2 ≤ s := by
      simp only [s, encPair_apply, encBits_apply, encUnary_apply, List.length_append,
        length_frame, List.length_replicate]
      omega
    calc 3 * ((2 * p.2.1.length + 1) * (2 * p.1.length + 1)) + 2 * p.2.2 + 2 ≤
        3 * ((2 * s + 1) * (2 * s + 1)) + 2 * s + 2 := by gcongr
      _ ≤ 40 * (s + 1) ^ 2 := by nlinarith
  · intro p j state hj hinv
    have hL := pow_clog_two_le p.2.1.length
    have hlevel := (length_encList_le encBits _ fun y hy => (hinv.1 y hy).le).trans
      (Nat.mul_le_mul_right (2 * p.1.length + 1) (hinv.2.1.trans hL))
    have hjL : j ≤ 2 * p.2.1.length + 1 := hj.trans ((Nat.lt_pow_self (by norm_num)).le.trans hL)
    have hpath := (length_encList_le encBits _ hinv.2.2.2.1).trans
      (Nat.mul_le_mul_right (2 * p.1.length + 1) (hinv.2.2.2.2.trans hjL))
    simp only [encPair_apply, encUnary_apply, List.length_append, length_frame,
      List.length_replicate]
    have := hinv.2.2.1
    omega

/-- Computing an authentication path is polynomial-time for a polynomial-time keyed hash whose
digests have the length of the key. -/
@[program_certificate]
theorem computableInPolyTime_merklePath
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length) :
    ComputableInPolyTime
      (fun p : List Bool × List (List Bool) × ℕ => merklePath H p.1 p.2.1 p.2.2)
      (encPair encBits (encPair (encList encBits) encUnary)) (encList encBits) :=
  .of_tidy (computableTidilyInPolyTime_merklePath hH.tidy hlen)

private theorem computableTidilyInPolyTime_merkleInputs
    (hH : ComputableTidilyInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length)
    {k leaf : γ → List Bool} {i : γ → ℕ} {path : γ → List (List Bool)}
    (hk : ComputableTidilyInPolyTime k encIn encBits)
    (hleaf : ComputableTidilyInPolyTime leaf encIn encBits)
    (hi : ComputableTidilyInPolyTime i encIn encUnary)
    (hpath : ComputableTidilyInPolyTime path encIn (encList encBits)) :
    ComputableTidilyInPolyTime (fun a => merkleInputs H (k a) (leaf a) (i a) (path a)) encIn
      (encList encBits) := by
  have hstep : ComputableTidilyInPolyTime
      (fun p : (List Bool × (List (List Bool) × ℕ)) × List Bool =>
        merkleInputsStep H p.1.1 p.1.2 p.2)
      (encPair (encPair encBits (encPair (encList encBits) encUnary)) encBits)
      (encPair (encList encBits) encUnary) := by
    have hk' : ComputableTidilyInPolyTime
        (fun p : (List Bool × (List (List Bool) × ℕ)) × List Bool => p.1.1)
        (encPair (encPair encBits (encPair (encList encBits) encUnary)) encBits) encBits := by
      polytime
    have hinputs : ComputableTidilyInPolyTime
        (fun p : (List Bool × (List (List Bool) × ℕ)) × List Bool => p.1.2.1)
        (encPair (encPair encBits (encPair (encList encBits) encUnary)) encBits)
        (encList encBits) := by
      polytime
    have hidx : ComputableTidilyInPolyTime
        (fun p : (List Bool × (List (List Bool) × ℕ)) × List Bool => p.1.2.2)
        (encPair (encPair encBits (encPair (encList encBits) encUnary)) encBits) encUnary := by
      polytime
    have hsib : ComputableTidilyInPolyTime
        (fun p : (List Bool × (List (List Bool) × ℕ)) × List Bool => p.2)
        (encPair (encPair encBits (encPair (encList encBits) encUnary)) encBits) encBits := by
      polytime
    have hnode := computableTidilyInPolyTime_hash hH hk'
      (ComputableTidilyInPolyTime.listHeadDWithInput [] hinputs)
    have hleft := computableTidilyInPolyTime_pairWord hnode hsib
    have hright := computableTidilyInPolyTime_pairWord hsib hnode
    have hnext : ComputableTidilyInPolyTime
        (fun p : (List Bool × (List (List Bool) × ℕ)) × List Bool =>
          if p.1.2.2 % 2 = 0 then
            encPair encBits encBits (H p.1.1 (p.1.2.1.headD []), p.2)
          else encPair encBits encBits (p.2, H p.1.1 (p.1.2.1.headD [])))
        (encPair (encPair encBits (encPair (encList encBits) encUnary)) encBits) encBits := by
      polytime
    unfold merkleInputsStep
    exact (ComputableTidilyInPolyTime.cons' hnext hinputs).prod
      ((ComputableTidilyInPolyTime.unary_div_const 2).comp hidx)
  have hfold := ComputableTidilyInPolyTime.foldlWith_of_bounded_growth
    (encA := encBits) (encL := encList encBits) (encP := encBits)
    (encB := encPair (encList encBits) encUnary)
    (step := fun k state sibling => merkleInputsStep H k state sibling)
    hk hpath
    ((ComputableTidilyInPolyTime.cons' hleaf (ComputableTidilyInPolyTime.const [])).prod hi)
    hstep (growth := fun a => 8 * (k a).length + 8 * (encList encBits (path a)).length + 6)
    ((((PolyBounded.const 8).mul hk.polyBounded_length).add
      ((PolyBounded.const 8).mul hpath.polyBounded_length)).add (.const 6))
    (by
      intro a state sibling hmem
      have hsib : sibling.length ≤ (encList encBits (path a)).length := by
        have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun x : List Bool => x.length) hmem)
        exact this.trans ((sum_length_le_length_encList encBits (path a)).trans_eq' (by simp))
      have hnode := hlen (k a) (state.1.headD [])
      unfold merkleInputsStep
      split_ifs <;>
      · simp only [encPair_apply, encBits_apply, encUnary_apply, encList_cons, List.length_append,
          length_frame, List.length_replicate, hnode]
        have := Nat.div_le_self state.2 2
        omega)
  exact (ComputableTidilyInPolyTime.fst _ _).comp hfold

/-- Recomputing a root from an opening is polynomial-time for a polynomial-time keyed hash whose
digests have the length of the key. -/
@[program_certificate]
theorem computableInPolyTime_merkleRootOfPath
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length) :
    ComputableInPolyTime
      (fun p : List Bool × List Bool × ℕ × List (List Bool) =>
        merkleRootOfPath H p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encBits (encPair encBits (encPair encUnary (encList encBits)))) encBits := by
  apply ComputableInPolyTime.of_tidy
  have hk := ComputableTidilyInPolyTime.fst encBits
    (encPair encBits (encPair encUnary (encList encBits)))
  have hrest := ComputableTidilyInPolyTime.snd encBits
    (encPair encBits (encPair encUnary (encList encBits)))
  have hleaf := (ComputableTidilyInPolyTime.fst _ _).comp hrest
  have hi := (ComputableTidilyInPolyTime.fst _ _).comp
    ((ComputableTidilyInPolyTime.snd _ _).comp hrest)
  have hpath := (ComputableTidilyInPolyTime.snd _ _).comp
    ((ComputableTidilyInPolyTime.snd _ _).comp hrest)
  exact computableTidilyInPolyTime_hash hH.tidy hk (ComputableTidilyInPolyTime.listHeadDWithInput []
    (computableTidilyInPolyTime_merkleInputs hH.tidy hlen hk hleaf hi hpath))

/-- Extracting a collision from two openings is polynomial-time for a polynomial-time keyed hash
whose digests have the length of the key. -/
@[program_certificate]
theorem computableInPolyTime_extractMerkleCollision
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length) :
    ComputableInPolyTime
      (fun p : List Bool × (List Bool × List Bool) × ℕ × List (List Bool) × List (List Bool) =>
        extractMerkleCollision H p.1 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
      (encPair encBits (encPair (encPair encBits encBits)
        (encPair encUnary (encPair (encList encBits) (encList encBits)))))
      (encPair encBits encBits) := by
  apply ComputableInPolyTime.of_tidy
  have hk := ComputableTidilyInPolyTime.fst encBits (encPair (encPair encBits encBits)
    (encPair encUnary (encPair (encList encBits) (encList encBits))))
  have hrest := ComputableTidilyInPolyTime.snd encBits (encPair (encPair encBits encBits)
    (encPair encUnary (encPair (encList encBits) (encList encBits))))
  have hleaves := (ComputableTidilyInPolyTime.fst _ _).comp hrest
  have hleaf₁ := (ComputableTidilyInPolyTime.fst _ _).comp hleaves
  have hleaf₂ := (ComputableTidilyInPolyTime.snd _ _).comp hleaves
  have hopen := (ComputableTidilyInPolyTime.snd _ _).comp hrest
  have hi := (ComputableTidilyInPolyTime.fst _ _).comp hopen
  have hpaths := (ComputableTidilyInPolyTime.snd _ _).comp hopen
  have hpath₁ := (ComputableTidilyInPolyTime.fst _ _).comp hpaths
  have hpath₂ := (ComputableTidilyInPolyTime.snd _ _).comp hpaths
  have hzip := (ComputableTidilyInPolyTime.zip encBits encBits).comp
    ((computableTidilyInPolyTime_merkleInputs hH.tidy hlen hk hleaf₁ hi hpath₁).prod
      (computableTidilyInPolyTime_merkleInputs hH.tidy hlen hk hleaf₂ hi hpath₂))
  have hfind := ComputableTidilyInPolyTime.findWithInput
    (test := fun _ p => p.1 != p.2) hzip (by polytime)
  exact ComputableTidilyInPolyTime.optionGetDWithInput hfind (.const ([], []))

end PolyTime

end Cslib.Crypto
