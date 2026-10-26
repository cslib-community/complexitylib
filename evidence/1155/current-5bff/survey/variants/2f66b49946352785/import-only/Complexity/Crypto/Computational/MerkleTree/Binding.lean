/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.MerkleTree
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Crypto.Negligible.Basic
import Complexity.Probability.PMF.Bind
import Complexity.Tactic.PolyTime
import Complexity.Tactic.PPT


import Diag1155.Measure
/-!
# Merkle trees as authenticated data structures: verification and position binding

`Cslib.Crypto.merkleRoot` hashes a list of leaves and `Cslib.Crypto.merklePath` opens one position.
This module adds the verifier and the security notion of an authenticated data structure scheme
([BonehShoup2023], Section 8.9.1): a verifier `merkleVerify` with completeness, binding and a
polynomial-time certificate, the game of Attack Game 8.2, and the security of Theorem 8.8,
reduced to collision resistance with no loss.

* **The verifier.** `merkleVerify H k d root i leaf path` accepts when `path` has `d` labels,
  `i < 2 ^ d`, and the root recomputed from `leaf` at position `i` along `path` is `root`
  (the `V` of [BonehShoup2023], Definition 8.3). These are the checks that the module
  documentation of `Complexity.Crypto.Computational.MerkleTree` requires of a verifier, under
  "What a verifier must check"; without them binding fails. Honest openings are accepted
  (`merkleVerify_merklePath`, `merkleVerify_merklePath_of_clog_eq`), the correctness requirement
  of Definition 8.3. An opening has one label per level, each of at most `k.length` bits when
  `H k` returns `k.length` bits (`length_le_of_mem_merklePath`).
* **Binding of the verifier.** Two openings of one position to different leaves, both accepted at
  the same depth, give a collision of `H k`, found by `extractMerkleCollision`
  (`isCollision_of_merkleVerify`).
* **The game.** In `merkleBindingGame` the adversary receives the security parameter and a uniform
  key `k`, and outputs a root, a position and two openings. It wins when both openings are
  accepted at the depth of the first path and their leaves differ (`merkleBreaksBinding`).
  `MerklePositionBinding H` asks that every uniform strict PPT adversary win with negligible
  probability.
* **The reduction.** `merkleCollisionFinder` runs the adversary and applies
  `extractMerkleCollision` to its two openings. Every win yields a collision, so the binding
  advantage is at most the collision advantage at every parameter
  (`succProbability_merkleBindingGame_le`), and the reduction is strict PPT
  (`isPPT_merkleCollisionFinder`). Hence every collision-resistant `HashFamily` gives position
  binding (`HashFamily.merklePositionBinding`).

**Differences from [BonehShoup2023].** Attack Game 8.2 is stated for a scheme over `(X^n, Y)`
with a fixed number `n` of items; here:
* the hash is a keyed family with a uniform `n`-bit key, and adversaries are uniform strict PPT
  programs, as in `CollisionResistant`;
* the adversary chooses the depth `d`, the length of its first path, and must open both leaves at
  that depth, which makes the game stronger than one with a fixed depth;
* positions are `0 ≤ i < 2 ^ d`, the padding positions included, rather than `1 ≤ i ≤ n`;
* the adversary writes its position in unary (`encMerkleBindingOutput`), so the game covers
  polynomially bounded positions: enough for trees with polynomially many leaves, but not for
  trees whose leaves are indexed by superpolynomially many positions.

**Kilian's construction.** Kilian's succinct arguments commit to a PCP proof with a hash tree and
open the queried positions ([Barak and Goldreich][BarakGoldreich2001], Construction 3.4, steps
P1.3 and V3). That tree differs from this one, which is [BonehShoup2023]'s Figure 8.12: its leaf
labels are the proof bits themselves, not their hashes, and an internal label hashes the plain
concatenation `ℓ_γ0 ℓ_γ1` of its children's labels, not their `encPair` pairing. Its prover sends
both child labels at every level of a path rather than only the siblings, and the verifier checks
the same hash equations along the path. Barak and Goldreich's hashing family resists non-uniform
circuits.

## Main definitions

* `Cslib.Crypto.merkleVerify`: accepting an opening at a given depth.
* `Cslib.Crypto.MerkleBindingOutput`, `Cslib.Crypto.encMerkleBindingOutput`,
  `Cslib.Crypto.MerkleBindingAdversary`: the adversary's output, its encoding, and adversaries.
* `Cslib.Crypto.merkleBreaksBinding`, `Cslib.Crypto.merkleBindingGame`,
  `Cslib.Crypto.MerklePositionBinding`: the position-binding game and security notion.
* `Cslib.Crypto.merkleCollisionFinder`: the reduction to collision finding.

## Main results

* `Cslib.Crypto.merkleVerify_merklePath`, `Cslib.Crypto.merkleVerify_merklePath_of_clog_eq`:
  honest openings are accepted.
* `Cslib.Crypto.length_of_mem_merkleLevel`, `Cslib.Crypto.length_le_of_mem_merklePath`: tree
  nodes have `k.length` bits, and the labels of an opening at most `k.length` bits.
* `Cslib.Crypto.computableInPolyTime_merkleVerify`: verification takes polynomial time.
* `Cslib.Crypto.isCollision_of_merkleVerify`: two accepted openings of one position to different
  leaves yield a collision.
* `Cslib.Crypto.isCollision_of_merkleBreaksBinding`,
  `Cslib.Crypto.succProbability_merkleBindingGame_le`,
  `Cslib.Crypto.isPPT_merkleCollisionFinder`: the certified reduction, with no loss.
* `Cslib.Crypto.MerklePositionBinding.negligible`,
  `Cslib.Crypto.MerklePositionBinding.of_negligible`: position binding as negligible success.
* `Cslib.Crypto.HashFamily.merklePositionBinding`: collision-resistant hash families give
  position binding.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Section 8.9.1,
  Definitions 8.3 and 8.4, Attack Game 8.2 and Theorem 8.8.
* [B. Barak, O. Goldreich, *Universal Arguments and their Applications*][BarakGoldreich2001],
  Construction 3.4.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-! ### Verifying openings -/

section Verify

variable (H : List Bool → List Bool → List Bool) (k : List Bool)

/-- Accept `path` as an opening of position `i` of a depth-`d` tree with root `root` to `leaf`:
the path has `d` labels, `i < 2 ^ d`, and the recomputed root is `root`. This is the verifier `V`
of the Merkle tree as an authenticated data structure ([BonehShoup2023], Definition 8.3), with the
depth as an explicit argument. -/
def merkleVerify (d : ℕ) (root : List Bool) (i : ℕ) (leaf : List Bool)
    (path : List (List Bool)) : Bool :=
  path.length == d && decide (i < 2 ^ d) && merkleRootOfPath H k leaf i path == root

variable {H k}

/-- **Honest openings are accepted**: every position `i < 2 ^ Nat.clog 2 leaves.length` of the
tree over `leaves`, opened by its authentication path, is accepted against the root (the
correctness requirement of [BonehShoup2023], Definition 8.3). -/
theorem merkleVerify_merklePath (leaves : List (List Bool)) {i : ℕ}
    (hi : i < 2 ^ Nat.clog 2 leaves.length) :
    merkleVerify H k (Nat.clog 2 leaves.length) (merkleRoot H k leaves) i (leaves.getD i [])
      (merklePath H k leaves i) = true := by
  rw [merkleVerify, merkleRootOfPath_merklePath leaves hi]
  simp [hi]

/-- Honest openings are accepted at any depth `d` equal to the tree's depth, for instance
`d = Nat.clog 2 N` for `N` leaves. -/
theorem merkleVerify_merklePath_of_clog_eq {leaves : List (List Bool)} {d i : ℕ}
    (hd : Nat.clog 2 leaves.length = d) (hi : i < 2 ^ d) :
    merkleVerify H k d (merkleRoot H k leaves) i (leaves.getD i [])
      (merklePath H k leaves i) = true := by
  subst hd
  exact merkleVerify_merklePath leaves hi

/-- Every node of the tree has `k.length` bits when `H k` returns `k.length` bits. -/
theorem length_of_mem_merkleLevel (hlen : ∀ k x, (H k x).length = k.length)
    {leaves : List (List Bool)} {j : ℕ} {y : List Bool} (hy : y ∈ merkleLevel H k leaves j) :
    y.length = k.length := by
  cases j with
  | zero => exact length_of_mem_merkleLeafLevel hlen hy
  | succ j =>
    rw [merkleLevel_succ] at hy
    exact length_of_mem_merkleParents hlen hy

/-- **Openings are short**: the labels of an authentication path have at most `k.length` bits
(a sibling outside the tree reads as `[]`), so an opening of the tree over `leaves` has at most
`Nat.clog 2 leaves.length * k.length` bits of labels. -/
theorem length_le_of_mem_merklePath (hlen : ∀ k x, (H k x).length = k.length)
    {leaves : List (List Bool)} {i : ℕ} {s : List Bool} (hs : s ∈ merklePath H k leaves i) :
    s.length ≤ k.length := by
  rw [merklePath_eq] at hs
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hs
  rw [List.getD_eq_getElem?_getD]
  cases h : (merkleLevel H k leaves t)[merkleSibling (i / 2 ^ t)]? with
  | none => simp
  | some y => exact (length_of_mem_merkleLevel hlen (List.mem_of_getElem? h)).le

/-- **Binding of the verifier**: two openings of position `i` to different leaves, both accepted
against `root` at depth `d`, contain a collision of `H k`, which `extractMerkleCollision` finds.
The length check makes the two paths equally long, as `isCollision_extractMerkleCollision`
requires. -/
theorem isCollision_of_merkleVerify {d : ℕ} {root : List Bool} {i : ℕ}
    {leaf₁ leaf₂ : List Bool} {path₁ path₂ : List (List Bool)}
    (h₁ : merkleVerify H k d root i leaf₁ path₁ = true)
    (h₂ : merkleVerify H k d root i leaf₂ path₂ = true) (hne : leaf₁ ≠ leaf₂) (n : ℕ) :
    isCollision H (fun _ _ => true) n k (extractMerkleCollision H k leaf₁ leaf₂ i path₁ path₂).1
      (extractMerkleCollision H k leaf₁ leaf₂ i path₁ path₂).2 = true := by
  simp only [merkleVerify, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h₁ h₂
  exact isCollision_extractMerkleCollision n (h₁.1.1.trans h₂.1.1.symm) hne
    (h₁.2.trans h₂.2.symm)

/-- Verifying an opening takes polynomial time: the key, the depth in unary, the root, the
position in unary, the leaf and the path. -/
@[program_certificate]
theorem computableInPolyTime_merkleVerify
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length) :
    ComputableInPolyTime
      (fun p : (List Bool × ℕ) × (List Bool × ℕ) × (List Bool × List (List Bool)) =>
        merkleVerify H p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2)
      (encPair (encPair encBits encUnary)
        (encPair (encPair encBits encUnary) (encPair encBits (encList encBits)))) encBool := by
  have hargs : ComputableInPolyTime
      (fun p : (List Bool × ℕ) × (List Bool × ℕ) × (List Bool × List (List Bool)) =>
        (p.1.1, p.2.2.1, p.2.1.2, p.2.2.2))
      (encPair (encPair encBits encUnary)
        (encPair (encPair encBits encUnary) (encPair encBits (encList encBits))))
      (encPair encBits (encPair encBits (encPair encUnary (encList encBits)))) := by
    fun_prop
  have hroot : ComputableInPolyTime
      (fun p : (List Bool × ℕ) × (List Bool × ℕ) × (List Bool × List (List Bool)) =>
        merkleRootOfPath H p.1.1 p.2.2.1 p.2.1.2 p.2.2.2 == p.2.1.1)
      (encPair (encPair encBits encUnary)
        (encPair (encPair encBits encUnary) (encPair encBits (encList encBits)))) encBool :=
    ComputableInPolyTime.beq ((computableInPolyTime_merkleRootOfPath hH hlen).comp hargs)
      (by fun_prop)
  have hi : ComputableInPolyTime
      (fun p : (List Bool × ℕ) × (List Bool × ℕ) × (List Bool × List (List Bool)) => p.2.1.2)
      (encPair (encPair encBits encUnary)
        (encPair (encPair encBits encUnary) (encPair encBits (encList encBits)))) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hd : ComputableInPolyTime
      (fun p : (List Bool × ℕ) × (List Bool × ℕ) × (List Bool × List (List Bool)) => p.1.2)
      (encPair (encPair encBits encUnary)
        (encPair (encPair encBits encUnary) (encPair encBits (encList encBits)))) encUnary := by
    fun_prop
  have hrange : ComputableInPolyTime
      (fun p : (List Bool × ℕ) × (List Bool × ℕ) × (List Bool × List (List Bool)) =>
        decide (p.2.1.2 < 2 ^ p.1.2))
      (encPair (encPair encBits encUnary)
        (encPair (encPair encBits encUnary) (encPair encBits (encList encBits)))) encBool :=
    .of_tidy (ComputableTidilyInPolyTime.binary_lt' hi.tidy
      (ComputableInPolyTime.binary_two_pow.comp hd).tidy)
  have hlength : ComputableInPolyTime
      (fun p : (List Bool × ℕ) × (List Bool × ℕ) × (List Bool × List (List Bool)) =>
        p.2.2.2.length == p.1.2)
      (encPair (encPair encBits encUnary)
        (encPair (encPair encBits encUnary) (encPair encBits (encList encBits)))) encBool :=
    ComputableInPolyTime.beq (encB := encUnary) (by fun_prop) hd
  exact ComputableInPolyTime.bool_and.comp
    ((ComputableInPolyTime.bool_and.comp (hlength.prod hrange)).prod hroot)

end Verify

/-! ### Position binding -/

/-- The output of a position-binding adversary: a root and a position, then two openings of that
position, each a leaf and its path. The depth is the length of the first path. -/
abbrev MerkleBindingOutput :=
  (List Bool × ℕ) × (List Bool × List (List Bool)) × (List Bool × List (List Bool))

/-- The encoding of `MerkleBindingOutput`: bit strings as themselves, the position in unary, as
in `computableInPolyTime_extractMerkleCollision`. An efficient adversary therefore outputs only
polynomially bounded positions. -/
abbrev encMerkleBindingOutput : MerkleBindingOutput ↪ List Bool :=
  encPair (encPair encBits encUnary)
    (encPair (encPair encBits (encList encBits)) (encPair encBits (encList encBits)))

/-- A position-binding adversary receives the unary security parameter `n` and the hash key, and
outputs a root, a position and two openings. -/
abbrev MerkleBindingAdversary := ℕ → List Bool → ProbComp MerkleBindingOutput

section Binding

variable (H : List Bool → List Bool → List Bool)

/-- `out` breaks position binding under the key `k`: both openings are accepted at the same
position of the same root, at the depth of the first path, and their leaves differ. -/
def merkleBreaksBinding (k : List Bool) (out : MerkleBindingOutput) : Bool :=
  merkleVerify H k out.2.1.2.length out.1.1 out.1.2 out.2.1.1 out.2.1.2 &&
    merkleVerify H k out.2.1.2.length out.1.1 out.1.2 out.2.2.1 out.2.2.2 &&
      out.2.1.1 != out.2.2.1

/-- The position-binding experiment ([BonehShoup2023], Attack Game 8.2, for a keyed hash): sample
a uniform `n`-bit key `k`, run the adversary on `(n, k)`, and accept when its output breaks
binding under `k`. -/
noncomputable def merkleBindingGame (adversary : MerkleBindingAdversary) (n : ℕ) :
    ProbComp Bool := do
  let k ← BitString.sampleList n
  let out ← adversary n k
  return merkleBreaksBinding H k out

/-- Position binding of Merkle trees over `H` ([BonehShoup2023], Definition 8.4): every uniform
strict PPT adversary breaks binding with negligible probability. Adversaries write positions in
unary, so this covers polynomially bounded positions. -/
def MerklePositionBinding : Prop :=
  Game.Indistinguishable (fun adversary n => ProbComp.eval (merkleBindingGame H adversary n))
    (fun _ _ => PMF.pure false) (IsPPT encMerkleBindingOutput)

/-- The collision finder built from a position-binding adversary: run it, and extract a collision
from its two openings with `extractMerkleCollision`. -/
def merkleCollisionFinder (adversary : MerkleBindingAdversary) : CollisionFinder := fun n k => do
  let out ← adversary n k
  return extractMerkleCollision H k out.2.1.1 out.2.2.1 out.1.2 out.2.1.2 out.2.2.2

variable {H}

/-- **A binding break yields a collision**: if `out` breaks position binding under `k`, then
`extractMerkleCollision` finds two different inputs with the same hash under `k`. -/
theorem isCollision_of_merkleBreaksBinding {k : List Bool} {out : MerkleBindingOutput}
    (h : merkleBreaksBinding H k out = true) (n : ℕ) :
    isCollision H (fun _ _ => true) n k
      (extractMerkleCollision H k out.2.1.1 out.2.2.1 out.1.2 out.2.1.2 out.2.2.2).1
      (extractMerkleCollision H k out.2.1.1 out.2.2.1 out.1.2 out.2.1.2 out.2.2.2).2 = true := by
  simp only [merkleBreaksBinding, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact isCollision_of_merkleVerify h.1.1 h.1.2 h.2 n

/-- **The reduction loses nothing**: at every security parameter, a position-binding adversary
succeeds at most as often as its collision finder. -/
theorem succProbability_merkleBindingGame_le (adversary : MerkleBindingAdversary) (n : ℕ) :
    Game.succProbability (ProbComp.eval (merkleBindingGame H adversary n)) ≤
      Game.succProbability (ProbComp.eval
        (collisionGame H (fun _ _ => true) (merkleCollisionFinder H adversary) n)) := by
  unfold Game.succProbability
  apply ENNReal.toNNReal_mono (PMF.apply_ne_top _ _)
  simp only [merkleBindingGame, collisionGame, merkleCollisionFinder, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  apply PMF.bind_apply_mono_on_support
  intro k _
  apply PMF.bind_apply_mono_on_support
  intro out _
  cases hbreak : merkleBreaksBinding H k out
  · simp
  · rw [isCollision_of_merkleBreaksBinding hbreak n]

/-- **The reduction is efficient**: the collision finder of a strict PPT binding adversary is
strict PPT, for a polynomial-time `H` that returns `k.length` bits. -/
theorem isPPT_merkleCollisionFinder
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length) {adversary : MerkleBindingAdversary}
    (hadversary : IsPPT encMerkleBindingOutput adversary) :
    IsPPT (encPair encBits encBits) (merkleCollisionFinder H adversary) := by
  have hargs : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × MerkleBindingOutput =>
        (p.1.2, (p.2.2.1.1, p.2.2.2.1), p.2.1.2, p.2.2.1.2, p.2.2.2.2))
      (encPair (encPair encUnary encBits) encMerkleBindingOutput)
      (encPair encBits (encPair (encPair encBits encBits)
        (encPair encUnary (encPair (encList encBits) (encList encBits))))) := by
    fun_prop
  have hpost := ((computableInPolyTime_extractMerkleCollision hH hlen).comp hargs).tidy
  change IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
    (fun p => merkleCollisionFinder H adversary p.1 p.2)
  exact hadversary.bind_with hpost.isPPTOn

/-- Position binding gives negligible success probability to every strict PPT adversary. -/
theorem MerklePositionBinding.negligible (h : MerklePositionBinding H)
    (adversary : MerkleBindingAdversary) (hadversary : IsPPT encMerkleBindingOutput adversary) :
    Negligible fun n => Game.succProbability (ProbComp.eval (merkleBindingGame H adversary n)) := by
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Establish position binding by bounding every strict PPT adversary's success probability. -/
theorem MerklePositionBinding.of_negligible
    (h : ∀ adversary, IsPPT encMerkleBindingOutput adversary →
      Negligible fun n => Game.succProbability (ProbComp.eval (merkleBindingGame H adversary n))) :
    MerklePositionBinding H := by
  intro adversary hadversary
  simpa only [Game.advantage_pure_false] using h adversary hadversary

end Binding

/-- **Collision-resistant hash families give position-binding Merkle trees**
([BonehShoup2023], Theorem 8.8, for keyed families and uniform adversaries): no uniform strict
PPT adversary can open a position of a Merkle tree over a `HashFamily` to two different leaves,
except with negligible probability. The reduction is `merkleCollisionFinder`, with no loss
(`succProbability_merkleBindingGame_le`). -/
theorem HashFamily.merklePositionBinding {H : List Bool → List Bool → List Bool}
    (hH : HashFamily H) : MerklePositionBinding H :=
  MerklePositionBinding.of_negligible fun adversary hadversary =>
    negligible_of_le (hH.collisionResistant.negligible _
      (isPPT_merkleCollisionFinder hH.polyTime (fun k x => hH.length_eq k x) hadversary))
      (succProbability_merkleBindingGame_le adversary)

end Cslib.Crypto
