/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.CollisionResistant
public import CslibFrontier.Crypto.Computational.PedersenCommitment
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PowMod
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits

/-!
# Discrete-logarithm collision-resistant hash families

Over a `PrimeOrderGroupFamily`, this module formalizes the encoded collision-resistance endpoint of
Katz and Lindell's discrete-logarithm hash ([KatzLindell2020], Section 9.4.2, Construction 9.78 and
Theorem 9.79, pp. 357–359; [BonehShoup2023], Section 8.5.1). The family samples a group description
`d ← setup n` and a uniform group element `h = α • g` (`groupHashSetup`), and hashes a
`2 * blockLen d`-bit input `x` by splitting `x` into two `blockLen d`-bit halves `(x₁, x₂)` (read
as natural numbers in little-endian binary via `ofBits`) and evaluating
`encode (x₁ • g + x₂ • h)` (`groupHash`).

When `2 ^ blockLen d ≤ F.order d`, the two `blockLen d`-bit halves represent elements strictly
below the prime order `q = F.order d`. Any collision `x ≠ y` of length `2 * blockLen d` with
`groupHash blockLen (d, encode d (α • g)) x = groupHash blockLen (d, encode d (α • g)) y` satisfies
`x₁ + x₂ * α = y₁ + y₂ * α` in `ZMod q` with `(y₂ : ZMod q) ≠ x₂`, so `pedersenExtractNat`
recovers the discrete logarithm `α = (y₂ - x₂)⁻¹ * (x₁ - y₁)` in deterministic polynomial time.
This yields an exact zero-loss reduction
(`succProbability_collisionGameFor_groupHash_le_discreteLogGame`) showing that `F.DiscreteLog setup`
implies `CollisionResistantForOn` for `groupHash` (`DiscreteLog.collisionResistantForOn_groupHash`).

This is the collision-resistance reduction of Theorem 9.79 for the encoded outputs. It does not
establish the packaging conditions discussed with Construction 9.78 ([KatzLindell2020],
pp. 357–358), which remain separate obligations for a client that needs a fixed-length compression
function:

* **Fixed digest width.** `PrimeOrderGroupFamily.encode` may produce variable-length or padded
  encodings, so no fixed output length is asserted; the source pads outputs to a fixed length.
* **Compression.** `2 ^ blockLen d ≤ F.order d` bounds only the input scalars. The source notes that
  the construction compresses only when group elements are represented in fewer bits than the
  input; no such representation-length bound is assumed here.
* **Efficient setup.** `setup` is an arbitrary distribution with no efficient-generation
  certificate, whereas the source's key generation runs a polynomial-time group generator.

We also formalize the algebraic core of the multi-generator generalization ([KatzLindell2020],
Exercise 9.28, Construction 9.81, p. 363), `multiGeneratorHash d hs xs = ∑ i, xs i • hs i`, with
its linear homomorphisms and coordinate-wise discrete-logarithm extraction identity
(`multiGeneratorHash_extract_of_eq`).

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.groupHashSetup`: public parameter distribution drawing
  `d ← setup n` and `α ← ZMod (F.order d)` and returning `(d, F.encode d (α • F.generator d))`.
* `Cslib.Crypto.PrimeOrderGroupFamily.validGroupHashInput`: domain predicate testing whether an
  input word has length `2 * blockLen pk.1`.
* `Cslib.Crypto.PrimeOrderGroupFamily.groupHash`: discrete-logarithm hash on
  `2 * blockLen pk.1`-bit inputs, splitting `x` at `blockLen pk.1` and evaluating
  `F.encodePedersenCommit` (encoded output; no fixed output width or compression is asserted).
* `Cslib.Crypto.PrimeOrderGroupFamily.groupHashToDLAdversary`: discrete-logarithm reduction from a
  `groupHash` collision finder via `pedersenExtractNat`.
* `Cslib.Crypto.PrimeOrderGroupFamily.multiGeneratorHash`: multi-generator vector hash
  `∑ i, xs i • hs i` (algebraic core of [KatzLindell2020], Construction 9.81).

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.groupHash_encode`,
  `Cslib.Crypto.PrimeOrderGroupFamily.groupHash_append_of_length_eq`: algebraic characterization of
  `groupHash` via `pedersenCommit`.
* `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_validGroupHashInput`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_groupHash`: polynomial-time evaluation
  of the domain test and hash function when `blockLen` is polynomial-time in unary.
* `Cslib.Crypto.PrimeOrderGroupFamily.pedersenExtractNat_eq_of_isCollisionFor_groupHash`: any valid
  `groupHash` collision under `h = α • g` when `2 ^ blockLen d ≤ F.order d` recovers `α`.
* `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_groupHashToDLAdversary`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DiscreteLog.collisionResistantForOn_groupHash`, and
  `Cslib.Crypto.PrimeOrderGroupFamily.succProbability_collisionGameFor_groupHash_le_discreteLogGame`
  — exact zero-loss reduction and encoded collision resistance under the discrete-logarithm
  assumption (the reduction of [KatzLindell2020], Theorem 9.79, without the output-padding,
  compression and efficient-setup conditions above).
* `Cslib.Crypto.PrimeOrderGroupFamily.multiGeneratorHash_add`,
  `Cslib.Crypto.PrimeOrderGroupFamily.multiGeneratorHash_smul`,
  `Cslib.Crypto.PrimeOrderGroupFamily.multiGeneratorHash_smul_generator_eq_iff`,
  `Cslib.Crypto.PrimeOrderGroupFamily.multiGeneratorHash_extract_of_eq`: algebraic laws and
  coordinate discrete-logarithm extraction for `multiGeneratorHash`
  (ingredients of the proof of [KatzLindell2020], Exercise 9.28(a); not proved here).

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Section 9.4.2 (Construction 9.78 and Theorem 9.79, pp. 357–359) and Exercise 9.28
  (Construction 9.81, p. 363).
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 8.5.1.
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM
open scoped ENNReal NNReal BigOperators

variable (F : PrimeOrderGroupFamily)

/-! ### Discrete-logarithm hash family (Construction 9.78 & Theorem 9.79) -/

/-- Setup distribution for the discrete-logarithm hash family ([KatzLindell2020],
Construction 9.78, p. 358): draw `d ← setup n` and a uniform exponent
`α ← PMF.uniformOfFintype (ZMod (F.order d))`, and output the public parameter
`(d, F.encode d (α • F.generator d))`. -/
noncomputable def groupHashSetup (setup : ℕ → PMF F.Desc) (n : ℕ) :
    PMF (F.Desc × List Bool) := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  return (d, F.encode d (α • F.generator d))

/-- Domain validity predicate for `groupHash`: at group parameter `pk = (d, h)`, valid inputs are
bit strings of length `2 * blockLen d`. -/
def validGroupHashInput (blockLen : F.Desc → ℕ) (_n : ℕ) (pk : F.Desc × List Bool)
    (x : List Bool) : Bool :=
  x.length == 2 * blockLen pk.1

@[simp]
theorem validGroupHashInput_eq_true_iff (blockLen : F.Desc → ℕ) (n : ℕ)
    (pk : F.Desc × List Bool) (x : List Bool) :
    F.validGroupHashInput blockLen n pk x = true ↔ x.length = 2 * blockLen pk.1 :=
  beq_iff_eq

/-- Discrete-logarithm hash function ([KatzLindell2020], Construction 9.78, p. 358), with the
source's fixed input length `2 * blockLen d` and an encoded group element as output: given public
parameter `pk = (d, h)` and input `x : List Bool`, split `x` at `w = blockLen d` into
`(x.take w, x.drop w)` and evaluate
`F.encodePedersenCommit (d, h, ofBits (x.take w), ofBits (x.drop w))`. -/
def groupHash (blockLen : F.Desc → ℕ) (pk : F.Desc × List Bool) (x : List Bool) : List Bool :=
  let w := blockLen pk.1
  F.encodePedersenCommit (pk.1, pk.2, ofBits (x.take w), ofBits (x.drop w))

/-- On an encoded group element `F.encode d h`, `groupHash` computes the encoding of
`F.pedersenCommit d h (ofBits (x.take (blockLen d))) (ofBits (x.drop (blockLen d)))`. -/
@[simp]
theorem groupHash_encode (blockLen : F.Desc → ℕ) (d : F.Desc) (h : F.Carrier d) (x : List Bool) :
    F.groupHash blockLen (d, F.encode d h) x =
      F.encode d (F.pedersenCommit d h
        (ofBits (x.take (blockLen d))) (ofBits (x.drop (blockLen d)))) := by
  simp [groupHash]

/-- When `x₁` has length `blockLen d`, hashing the concatenation `x₁ ++ x₂` under
`(d, F.encode d h)` evaluates `F.encode d (F.pedersenCommit d h (ofBits x₁) (ofBits x₂))`. -/
theorem groupHash_append_of_length_eq (blockLen : F.Desc → ℕ) (d : F.Desc) (h : F.Carrier d)
    {x₁ x₂ : List Bool} (hx₁ : x₁.length = blockLen d) :
    F.groupHash blockLen (d, F.encode d h) (x₁ ++ x₂) =
      F.encode d (F.pedersenCommit d h (ofBits x₁) (ofBits x₂)) := by
  rw [groupHash_encode, List.take_left' hx₁, List.drop_left' hx₁]

/-- Testing whether an input satisfies `validGroupHashInput blockLen` is computable in polynomial
time whenever `blockLen` is computable in polynomial time in unary. -/
theorem computableInPolyTime_validGroupHashInput {blockLen : F.Desc → ℕ}
    (hblock : ComputableInPolyTime blockLen F.encDesc encUnary) :
    ComputableInPolyTime
      (fun p : ℕ × (F.Desc × List Bool) × List Bool =>
        F.validGroupHashInput blockLen p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair (encPair F.encDesc encBits) encBits)) encBool := by
  have hbt := hblock.tidy
  unfold validGroupHashInput
  polytime

/-- Evaluating `groupHash blockLen` is computable in polynomial time whenever `blockLen` is
computable in polynomial time in unary. -/
theorem computableInPolyTime_groupHash {blockLen : F.Desc → ℕ}
    (hblock : ComputableInPolyTime blockLen F.encDesc encUnary) :
    ComputableInPolyTime
      (fun p : (F.Desc × List Bool) × List Bool => F.groupHash blockLen p.1 p.2)
      (encPair (encPair F.encDesc encBits) encBits) encBits := by
  have hbt := hblock.tidy
  have hped := F.computableInPolyTime_encodePedersenCommit.tidy
  unfold groupHash
  polytime

/-- **Collision extraction for `groupHash`** (step 2 of the proof of [KatzLindell2020],
Theorem 9.79, pp. 358–359): if `2 ^ blockLen d ≤ F.order d`, any valid collision `(x, y)` for
`groupHash blockLen` under `(d, F.encode d (α • F.generator d))` recovers `α` via
`pedersenExtractNat`. -/
theorem pedersenExtractNat_eq_of_isCollisionFor_groupHash (blockLen : F.Desc → ℕ)
    (n : ℕ) (d : F.Desc) (α : ZMod (F.order d)) {x y : List Bool}
    (hsize : 2 ^ blockLen d ≤ F.order d)
    (hcoll : isCollisionFor (Param := F.Desc × List Bool) (Digest := fun _ => List Bool)
      (F.groupHash blockLen) (F.validGroupHashInput blockLen)
      n (d, F.encode d (α • F.generator d)) x y = true) :
    let w := blockLen d
    (pedersenExtractNat (F.order d)
      (ofBits (x.take w)) (ofBits (x.drop w))
      (ofBits (y.take w)) (ofBits (y.drop w)) : ZMod (F.order d)) = α := by
  dsimp only
  set w := blockLen d
  rw [isCollisionFor_eq_true_iff, validGroupHashInput_eq_true_iff,
    validGroupHashInput_eq_true_iff, groupHash_encode, groupHash_encode] at hcoll
  rcases hcoll with ⟨hx_len, hy_len, hne, hhash⟩
  change x.length = 2 * w at hx_len
  change y.length = 2 * w at hy_len
  have hxt_len : (x.take w).length = w := by rw [List.length_take, hx_len]; omega
  have hxd_len : (x.drop w).length = w := by rw [List.length_drop, hx_len]; omega
  have hyt_len : (y.take w).length = w := by rw [List.length_take, hy_len]; omega
  have hyd_len : (y.drop w).length = w := by rw [List.length_drop, hy_len]; omega
  have hxt_lt : ofBits (x.take w) < F.order d :=
    (ofBits_lt_two_pow (x.take w)).trans_le (by rw [hxt_len]; exact hsize)
  have hxd_lt : ofBits (x.drop w) < F.order d :=
    (ofBits_lt_two_pow (x.drop w)).trans_le (by rw [hxd_len]; exact hsize)
  have hyt_lt : ofBits (y.take w) < F.order d :=
    (ofBits_lt_two_pow (y.take w)).trans_le (by rw [hyt_len]; exact hsize)
  have hyd_lt : ofBits (y.drop w) < F.order d :=
    (ofBits_lt_two_pow (y.drop w)).trans_le (by rw [hyd_len]; exact hsize)
  have hlin :
      (ofBits (x.take w) : ZMod (F.order d)) + (ofBits (x.drop w) : ZMod (F.order d)) * α =
        (ofBits (y.take w) : ZMod (F.order d)) + (ofBits (y.drop w) : ZMod (F.order d)) * α :=
    (F.pedersenCommit_smul_generator_eq_iff d α _ _ _ _).mp (F.encode_injective d hhash)
  have hmul :
      ((ofBits (y.drop w) : ZMod (F.order d)) - ofBits (x.drop w)) * α =
        (ofBits (x.take w) : ZMod (F.order d)) - ofBits (y.take w) := by
    linear_combination -hlin
  have hr : (ofBits (y.drop w) : ZMod (F.order d)) ≠ ofBits (x.drop w) := by
    intro hreq
    apply hne
    have hdrop_nat : ofBits (x.drop w) = ofBits (y.drop w) := by
      have hval := congrArg ZMod.val hreq.symm
      rwa [ZMod.val_natCast_of_lt hxd_lt, ZMod.val_natCast_of_lt hyd_lt] at hval
    have htake_zmod : (ofBits (x.take w) : ZMod (F.order d)) = ofBits (y.take w) := by
      have hzero : ((ofBits (y.drop w) : ZMod (F.order d)) - ofBits (x.drop w)) * α = 0 := by
        rw [sub_eq_zero.mpr hreq, zero_mul]
      exact sub_eq_zero.mp (hmul.symm.trans hzero)
    have htake_nat : ofBits (x.take w) = ofBits (y.take w) := by
      have hval := congrArg ZMod.val htake_zmod
      rwa [ZMod.val_natCast_of_lt hxt_lt, ZMod.val_natCast_of_lt hyt_lt] at hval
    have htake_eq : x.take w = y.take w :=
      ofBits_injective_of_length_eq (hxt_len.trans hyt_len.symm) htake_nat
    have hdrop_eq : x.drop w = y.drop w :=
      ofBits_injective_of_length_eq (hxd_len.trans hyd_len.symm) hdrop_nat
    rw [← List.take_append_drop w x, ← List.take_append_drop w y, htake_eq, hdrop_eq]
  rw [pedersenExtractNat_cast hr, ← hmul, inv_mul_cancel_left₀ (sub_ne_zero.mpr hr)]

/-- Turn a `groupHash` collision finder into a discrete-logarithm adversary by splitting the two
candidate colliding words at `blockLen d` and extracting `pedersenExtractNat` in binary
([KatzLindell2020], Theorem 9.79, pp. 358–359). -/
def groupHashToDLAdversary (blockLen : F.Desc → ℕ)
    (adversary : CollisionFinderFor (F.Desc × List Bool))
    (n : ℕ) (pk : F.Desc × List Bool) : ProbComp (List Bool) := do
  let pair ← adversary n pk
  let w := blockLen pk.1
  return (pedersenExtractNat (F.order pk.1)
    (ofBits (pair.1.take w)) (ofBits (pair.1.drop w))
    (ofBits (pair.2.take w)) (ofBits (pair.2.drop w))).bits

/-- **Exact collision-to-discrete-logarithm reduction** ([KatzLindell2020], Theorem 9.79,
pp. 358–359): whenever every group `d` in the support of `setup n` satisfies
`2 ^ blockLen d ≤ F.order d`, the collision-finding success probability of `adversary` in
`collisionGameFor (F.groupHashSetup setup) (F.groupHash blockLen) (F.validGroupHashInput blockLen)`
is at most the discrete-logarithm success probability of
`F.groupHashToDLAdversary blockLen adversary`. -/
theorem succProbability_collisionGameFor_groupHash_le_discreteLogGame
    (setup : ℕ → PMF F.Desc) (blockLen : F.Desc → ℕ)
    (adversary : CollisionFinderFor (F.Desc × List Bool)) (n : ℕ)
    (hsize : ∀ d ∈ (setup n).support, 2 ^ blockLen d ≤ F.order d) :
    Game.succProbability
      (collisionGameFor (Param := F.Desc × List Bool) (Digest := fun _ => List Bool)
        (F.groupHashSetup setup) (F.groupHash blockLen) (F.validGroupHashInput blockLen)
        adversary n) ≤
      Game.succProbability
        (F.discreteLogGame setup (F.groupHashToDLAdversary blockLen adversary) n) := by
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) ?_
  dsimp only [collisionGameFor, groupHashSetup, discreteLogGame, groupHashToDLAdversary,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  refine PMF.bind_apply_mono_on_support (setup n) true fun d hd => ?_
  refine PMF.bind_apply_mono_on_support (PMF.uniformOfFintype (ZMod (F.order d))) true fun α _ => ?_
  refine PMF.bind_apply_mono_on_support
    (ProbComp.eval (adversary n (d, F.encode d (α • F.generator d)))) true fun pair _ => ?_
  by_cases hcoll :
      isCollisionFor (Param := F.Desc × List Bool) (Digest := fun _ => List Bool)
        (F.groupHash blockLen) (F.validGroupHashInput blockLen)
        n (d, F.encode d (α • F.generator d)) pair.1 pair.2 = true
  · have hextract :=
      F.pedersenExtractNat_eq_of_isCollisionFor_groupHash blockLen n d α (hsize d hd) hcoll
    simp [hcoll, hextract]
  · simp [Bool.eq_false_iff.mpr hcoll]

/-- `groupHashToDLAdversary` is uniform strict PPT whenever `blockLen` is computable in polynomial
time in unary and `adversary` is uniform strict PPT. -/
theorem isPPTOn_groupHashToDLAdversary {blockLen : F.Desc → ℕ}
    (hblock : ComputableInPolyTime blockLen F.encDesc encUnary)
    {adversary : CollisionFinderFor (F.Desc × List Bool)}
    (hA : IsPPTOn (encPair encUnary (encPair F.encDesc encBits)) (encPair encBits encBits)
      (fun p => adversary p.1 p.2)) :
    IsPPTOn (encPair encUnary (encPair F.encDesc encBits)) encBits
      (fun p => F.groupHashToDLAdversary blockLen adversary p.1 p.2) := by
  unfold groupHashToDLAdversary
  refine hA.bind_with ?_
  have hbt := hblock.tidy
  have hextract : ComputableTidilyInPolyTime
      (fun p : (ℕ × (F.Desc × List Bool)) × (List Bool × List Bool) =>
        (pedersenExtractNat (F.order p.1.2.1)
          (ofBits (p.2.1.take (blockLen p.1.2.1))) (ofBits (p.2.1.drop (blockLen p.1.2.1)))
          (ofBits (p.2.2.take (blockLen p.1.2.1))) (ofBits (p.2.2.drop (blockLen p.1.2.1)))).bits)
      (encPair (encPair encUnary (encPair F.encDesc encBits)) (encPair encBits encBits))
      encBits := by
    change ComputableTidilyInPolyTime
      (fun p : (ℕ × (F.Desc × List Bool)) × (List Bool × List Bool) =>
        encNat (pedersenExtractNat (F.order p.1.2.1)
          (ofBits (p.2.1.take (blockLen p.1.2.1))) (ofBits (p.2.1.drop (blockLen p.1.2.1)))
          (ofBits (p.2.2.take (blockLen p.1.2.1))) (ofBits (p.2.2.drop (blockLen p.1.2.1)))))
      _ encBits
    have hpe := F.computableInPolyTime_pedersenExtractNat.tidy.comp'
      (g := fun p : (ℕ × (F.Desc × List Bool)) × (List Bool × List Bool) =>
        (p.1.2.1, (ofBits (p.2.1.take (blockLen p.1.2.1)), ofBits (p.2.1.drop (blockLen p.1.2.1))),
          (ofBits (p.2.2.take (blockLen p.1.2.1)), ofBits (p.2.2.drop (blockLen p.1.2.1)))))
      (encIn := encPair (encPair encUnary (encPair F.encDesc encBits)) (encPair encBits encBits))
      (by fun_prop)
    exact ComputableTidilyInPolyTime.id'.comp (by fun_prop)
  exact hextract.isPPTOn

/-- **Collision resistance of the discrete-logarithm hash family under the discrete-logarithm
assumption** ([KatzLindell2020], Section 9.4.2, Theorem 9.79, pp. 358–359): if
`F.DiscreteLog setup` holds, `blockLen` is computable in polynomial time in unary, and
`2 ^ blockLen d ≤ F.order d` for every supported group `d ∈ (setup n).support` at all sufficiently
large `n`, then `F.groupHash blockLen` is collision-resistant on `F.validGroupHashInput blockLen`
under `F.groupHashSetup setup`. This is the encoded collision-resistance endpoint: a fixed digest
width, compression and an efficient `setup` are not established (see the module docstring). -/
theorem DiscreteLog.collisionResistantForOn_groupHash {F : PrimeOrderGroupFamily}
    {setup : ℕ → PMF F.Desc} (hDL : F.DiscreteLog setup)
    {blockLen : F.Desc → ℕ} (hblock : ComputableInPolyTime blockLen F.encDesc encUnary)
    (hsize : ∀ᶠ n in Filter.atTop, ∀ d ∈ (setup n).support, 2 ^ blockLen d ≤ F.order d) :
    CollisionResistantForOn (Param := F.Desc × List Bool) (Digest := fun _ => List Bool)
      (encPair F.encDesc encBits) (F.groupHashSetup setup) (F.groupHash blockLen)
      (F.validGroupHashInput blockLen) := by
  refine CollisionResistantForOn.of_negligible fun adversary hA => ?_
  refine negligible_of_eventually_le
    (hDL (F.groupHashToDLAdversary blockLen adversary)
      (F.isPPTOn_groupHashToDLAdversary hblock hA)) ?_
  filter_upwards [hsize] with n hn
  exact F.succProbability_collisionGameFor_groupHash_le_discreteLogGame
    setup blockLen adversary n hn

/-! ### Algebraic core of the multi-generator hash (Construction 9.81, Exercise 9.28) -/

/-- Algebraic multi-generator discrete-logarithm vector hash ([KatzLindell2020], Exercise 9.28,
Construction 9.81, p. 363; algebraic core only: `hs` is arbitrary, whereas KL's `Gen` fixes
`h₁ = g` and samples the other `hᵢ` uniformly, and no key generation or game is defined here):
given generators `hs : ι → F.Carrier d` and a scalar vector `xs : ι → ZMod (F.order d)`, compute
`∑ i, xs i • hs i`. -/
def multiGeneratorHash {ι : Type*} [Fintype ι] (d : F.Desc)
    (hs : ι → F.Carrier d) (xs : ι → ZMod (F.order d)) : F.Carrier d :=
  ∑ i, xs i • hs i

@[simp]
theorem multiGeneratorHash_zero {ι : Type*} [Fintype ι] (d : F.Desc)
    (hs : ι → F.Carrier d) :
    F.multiGeneratorHash d hs 0 = 0 := by
  simp [multiGeneratorHash]

/-- **Additive homomorphism of `multiGeneratorHash`**. -/
theorem multiGeneratorHash_add {ι : Type*} [Fintype ι] (d : F.Desc)
    (hs : ι → F.Carrier d) (xs ys : ι → ZMod (F.order d)) :
    F.multiGeneratorHash d hs (xs + ys) =
      F.multiGeneratorHash d hs xs + F.multiGeneratorHash d hs ys := by
  simp only [multiGeneratorHash, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- **Subtractive homomorphism of `multiGeneratorHash`**. -/
theorem multiGeneratorHash_sub {ι : Type*} [Fintype ι] (d : F.Desc)
    (hs : ι → F.Carrier d) (xs ys : ι → ZMod (F.order d)) :
    F.multiGeneratorHash d hs (xs - ys) =
      F.multiGeneratorHash d hs xs - F.multiGeneratorHash d hs ys := by
  simp only [multiGeneratorHash, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

/-- **Scalar-multiplication homomorphism of `multiGeneratorHash`**. -/
theorem multiGeneratorHash_smul {ι : Type*} [Fintype ι] (d : F.Desc)
    (hs : ι → F.Carrier d) (c : ZMod (F.order d)) (xs : ι → ZMod (F.order d)) :
    F.multiGeneratorHash d hs (c • xs) = c • F.multiGeneratorHash d hs xs := by
  simp only [multiGeneratorHash, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- When `hs i = αs i • F.generator d` for each `i`, `multiGeneratorHash` evaluates
`(∑ i, xs i * αs i) • F.generator d`. -/
theorem multiGeneratorHash_smul_generator {ι : Type*} [Fintype ι] (d : F.Desc)
    (αs xs : ι → ZMod (F.order d)) :
    F.multiGeneratorHash d (fun i => αs i • F.generator d) xs =
      (∑ i, xs i * αs i) • F.generator d := by
  simp only [multiGeneratorHash, smul_smul, Finset.sum_smul]

/-- Two input vectors `xs, ys` collide under `hs i = αs i • F.generator d` if and only if
`∑ i, xs i * αs i = ∑ i, ys i * αs i` in `ZMod (F.order d)`. -/
theorem multiGeneratorHash_smul_generator_eq_iff {ι : Type*} [Fintype ι] (d : F.Desc)
    (αs xs ys : ι → ZMod (F.order d)) :
    F.multiGeneratorHash d (fun i => αs i • F.generator d) xs =
      F.multiGeneratorHash d (fun i => αs i • F.generator d) ys ↔
      ∑ i, xs i * αs i = ∑ i, ys i * αs i := by
  rw [multiGeneratorHash_smul_generator, multiGeneratorHash_smul_generator]
  exact (F.smul_generator_injective d).eq_iff

/-- **Coordinate discrete-logarithm extraction from a `multiGeneratorHash` collision**
(ingredient of the proof of [KatzLindell2020], Exercise 9.28(a), p. 363): if `xs` and `ys`
collide under `hs i = αs i • F.generator d` and differ at coordinate `j` (`ys j ≠ xs j`), then the
discrete logarithm `αs j` is given by
`(ys j - xs j)⁻¹ * ∑ i ∈ Finset.univ.erase j, (xs i - ys i) * αs i`. -/
theorem multiGeneratorHash_extract_of_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : F.Desc) (αs xs ys : ι → ZMod (F.order d)) {j : ι} (hj : ys j ≠ xs j)
    (hcoll : F.multiGeneratorHash d (fun i => αs i • F.generator d) xs =
      F.multiGeneratorHash d (fun i => αs i • F.generator d) ys) :
    αs j =
      (ys j - xs j)⁻¹ * ∑ i ∈ Finset.univ.erase j, (xs i - ys i) * αs i := by
  have hsum := (F.multiGeneratorHash_smul_generator_eq_iff d αs xs ys).mp hcoll
  have hdiff : ∑ i : ι, (xs i - ys i) * αs i = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, hsum, sub_self]
  have hsplit :=
    Finset.add_sum_erase Finset.univ (fun i => (xs i - ys i) * αs i) (Finset.mem_univ j)
  rw [hdiff] at hsplit
  have hmul : (ys j - xs j) * αs j = ∑ i ∈ Finset.univ.erase j, (xs i - ys i) * αs i := by
    linear_combination -hsplit
  rw [← hmul, inv_mul_cancel_left₀ (sub_ne_zero.mpr hj)]

end Cslib.Crypto.PrimeOrderGroupFamily
