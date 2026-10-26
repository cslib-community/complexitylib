/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.CollisionResistant
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Tactic.PolyTime
import Complexity.Tactic.PPT

/-!
# The Merkle–Damgård transform

Given a keyed `2n → n` collision-resistant compression family
`h : List Bool → List Bool → List Bool`, the Merkle–Damgård transform ([BonehShoup2023],
Section 8.4, Figure 8.5 and Theorem 8.3) constructs a collision-resistant hash family on
arbitrary-length messages by iterating `h k` over a sequence of `n`-bit blocks starting from a
fixed `n`-bit initialization vector `0^n`.

We formalize the transform and its collision-extraction reduction at two levels:

1. **Block-chain level (`merkleDamgardChain`, `extractChainCollision`)**:
   Iterating `h k` over a list of `n`-bit blocks produces an `n`-bit digest. Whenever two block
   lists `bs₁` and `bs₂` of `n`-bit blocks produce the same final digest under `merkleDamgardChain`
   and neither block list is a suffix of the other (`¬ (bs₁ <:+ bs₂) ∧ ¬ (bs₂ <:+ bs₁)`), scanning
   the compression inputs backward from the final step (`extractChainCollision`) deterministically
   finds a `2n`-bit collision `(x₁, x₂)` for `h k` in polynomial time. In particular, this covers
   both cases of the classical length-strengthened Merkle–Damgård proof ([BonehShoup2023],
   Theorem 8.3):
   * `isCollision_extractChainCollision_of_getLast?_ne`: the final (length-encoding) blocks of
     `bs₁` and `bs₂` differ;
   * `isCollision_extractChainCollision_of_length_eq`: `bs₁` and `bs₂` have the same number of
     blocks and `bs₁ ≠ bs₂`.
   Consequently, any polynomial-time suffix-free block encoding turns a `CompressionFamily` into a
   collision-resistant hash family (`CompressionFamily.collisionResistantOn_merkleDamgardChain`).

2. **Unrestricted bit-string level (`mdBlocks`, `merkleDamgard`, `extractMerkleDamgardCollision`)**:
   Encoding an arbitrary bit string `msg : List Bool` as the initial marker block `0^n` followed by
   one `n`-bit data block `1 ‖ b ‖ 0^{n-2}` per bit `b` of `msg` produces a suffix-free block
   encoding of **all** bit strings for every `n ≥ 2`, with no upper bound on message length.
   Iterating `h` over `mdBlocks k.length msg` yields
   `merkleDamgard h : List Bool → List Bool → List Bool`, which is collision-resistant on all
   arbitrary-length bit strings (`CompressionFamily.collisionResistant_merkleDamgard`,
   `CompressionFamily.hashFamily_merkleDamgard`).

## Main definitions

* `Cslib.Crypto.padOrTake`: fixed-width bit-string normalization to exact length `n`.
* `Cslib.Crypto.merkleDamgardChain`: block-level iterated compression
  `blocks.foldl (fun acc b => h k (acc ++ b)) iv`.
* `Cslib.Crypto.chainTraceStep`, `Cslib.Crypto.chainTrace`,
  `Cslib.Crypto.extractChainCollision`: polynomial-time backward scan extracting a `2n`-bit
  compression collision from colliding block chains.
* `Cslib.Crypto.mdEndBlock`, `Cslib.Crypto.mdDataBlock`, `Cslib.Crypto.mdBlocks`: suffix-free
  `n`-bit block encoding of arbitrary bit strings.
* `Cslib.Crypto.merkleDamgard`, `Cslib.Crypto.extractMerkleDamgardCollision`: domain-extended
  keyed hash family and its deterministic collision extractor.

## Main results

* `Cslib.Crypto.length_merkleDamgardChain`, `Cslib.Crypto.length_merkleDamgard`: digest length
  preservation.
* `Cslib.Crypto.isCollision_extractChainCollision_of_not_suffix`,
  `Cslib.Crypto.isCollision_extractChainCollision_of_getLast?_ne`,
  `Cslib.Crypto.isCollision_extractChainCollision_of_length_eq`: fundamental Merkle–Damgård chain
  collision extraction lemmas.
* `Cslib.Crypto.CompressionFamily.collisionResistantOn_merkleDamgardChain`: collision resistance
  for any polynomial-time suffix-free block encoding.
* `Cslib.Crypto.mdBlocks_suffix_iff`: suffix-freeness of `mdBlocks n` for `n ≥ 2`.
* `Cslib.Crypto.isCollision_extractMerkleDamgardCollision`: deterministic collision extraction for
  `merkleDamgard`.
* `Cslib.Crypto.CompressionFamily.collisionResistant_merkleDamgard`,
  `Cslib.Crypto.CompressionFamily.hashFamily_merkleDamgard`: any `2n → n` collision-resistant
  compression family yields an unrestricted collision-resistant hash family on `List Bool`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 8.4 (Figure 8.5 and Theorem 8.3).
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], Section 5.2.
-/

@[expose] public section

namespace Cslib.Crypto

open Turing.MultiTapeTM

/-! ### Fixed-width normalization -/

/-- Normalize a bit string to exact length `n` by right-padding with `false` or truncating.
On words already of length `n`, this is the identity. -/
def padOrTake (n : ℕ) (w : List Bool) : List Bool :=
  (w ++ List.replicate n false).take n

@[simp]
theorem length_padOrTake (n : ℕ) (w : List Bool) : (padOrTake n w).length = n := by
  simp only [padOrTake, List.length_take, List.length_append, List.length_replicate]
  omega

@[simp]
theorem padOrTake_eq_self {n : ℕ} {w : List Bool} (hw : w.length = n) :
    padOrTake n w = w := by
  subst hw
  simp [padOrTake]

@[local fun_prop]
private theorem computableTidilyInPolyTime_padOrTake
    {γ : Type} {encIn : γ ↪ List Bool} {n : γ → ℕ} {w : γ → List Bool}
    (hn : ComputableTidilyInPolyTime n encIn encUnary)
    (hw : ComputableTidilyInPolyTime w encIn encBits) :
    ComputableTidilyInPolyTime (fun a => padOrTake (n a) (w a)) encIn encBits := by
  unfold padOrTake
  polytime

/-- Normalizing a word to unary length `n` is computable in plain polynomial time. -/
@[program_certificate]
theorem computableInPolyTime_padOrTake :
    ComputableInPolyTime (fun p : ℕ × List Bool => padOrTake p.1 p.2)
      (encPair encUnary encBits) encBits :=
  .of_tidy (computableTidilyInPolyTime_padOrTake (by fun_prop) (by fun_prop))

/-! ### Block-level Merkle–Damgård chain and collision extraction -/

/-- Block-level Merkle–Damgård iterated compression ([BonehShoup2023], Section 8.4, Figure 8.5):
starting from the initial chaining value `iv`, fold over `blocks` by feeding `acc ++ b` to
`h k` at each step. -/
def merkleDamgardChain (h : List Bool → List Bool → List Bool)
    (k iv : List Bool) (blocks : List (List Bool)) : List Bool :=
  blocks.foldl (fun acc b => h k (acc ++ b)) iv

@[simp]
theorem merkleDamgardChain_nil (h : List Bool → List Bool → List Bool) (k iv : List Bool) :
    merkleDamgardChain h k iv [] = iv := rfl

@[simp]
theorem merkleDamgardChain_cons (h : List Bool → List Bool → List Bool)
    (k iv b : List Bool) (blocks : List (List Bool)) :
    merkleDamgardChain h k iv (b :: blocks) =
      merkleDamgardChain h k (h k (iv ++ b)) blocks := rfl

@[simp]
theorem merkleDamgardChain_append (h : List Bool → List Bool → List Bool)
    (k iv : List Bool) (bs₁ bs₂ : List (List Bool)) :
    merkleDamgardChain h k iv (bs₁ ++ bs₂) =
      merkleDamgardChain h k (merkleDamgardChain h k iv bs₁) bs₂ :=
  List.foldl_append

theorem merkleDamgardChain_concat (h : List Bool → List Bool → List Bool)
    (k iv : List Bool) (blocks : List (List Bool)) (b : List Bool) :
    merkleDamgardChain h k iv (blocks ++ [b]) =
      h k (merkleDamgardChain h k iv blocks ++ b) :=
  List.foldl_concat _ _ _ _

/-- If the initial vector and every block have length `k.length`, and `h k` maps `2 * k.length`-bit
inputs to `k.length`-bit outputs, then `merkleDamgardChain` produces a `k.length`-bit digest. -/
theorem length_merkleDamgardChain {h : List Bool → List Bool → List Bool}
    {k iv : List Bool} {blocks : List (List Bool)}
    (hlen : ∀ x, x.length = 2 * k.length → (h k x).length = k.length)
    (hiv : iv.length = k.length)
    (hblocks : ∀ b ∈ blocks, b.length = k.length) :
    (merkleDamgardChain h k iv blocks).length = k.length := by
  induction blocks generalizing iv with
  | nil => exact hiv
  | cons b bs ih =>
    apply ih
    · apply hlen
      rw [List.length_append, hiv, hblocks b List.mem_cons_self]
      omega
    · intro b' hb'
      exact hblocks b' (List.mem_cons_of_mem _ hb')

/-- Single step of `chainTrace`: normalize the current chaining value and block to `k.length` bits,
compress their concatenation under `h k`, and prepend the `2 * k.length`-bit compression input to
the reverse-chronological trace. -/
def chainTraceStep (h : List Bool → List Bool → List Bool) (k : List Bool)
    (state : List Bool × List (List Bool)) (b : List Bool) :
    List Bool × List (List Bool) :=
  let x := padOrTake k.length state.1 ++ padOrTake k.length b
  (h k x, x :: state.2)

/-- Run the Merkle–Damgård block chain while recording, in reverse chronological order, the
`2n`-bit compression inputs fed to `h k` at each step. Each step normalizes the chaining value and
block to `k.length` bits via `padOrTake k.length`, which is the identity on valid `k.length`-bit
chains and guarantees polynomial state growth on all inputs. -/
def chainTrace (h : List Bool → List Bool → List Bool) (k iv : List Bool)
    (blocks : List (List Bool)) : List Bool × List (List Bool) :=
  blocks.foldl (chainTraceStep h k) (iv, [])

@[simp]
theorem chainTrace_nil (h : List Bool → List Bool → List Bool) (k iv : List Bool) :
    chainTrace h k iv [] = (iv, []) := rfl

private theorem chainTrace_concat (h : List Bool → List Bool → List Bool) (k iv : List Bool)
    (blocks : List (List Bool)) (b : List Bool) :
    chainTrace h k iv (blocks ++ [b]) =
      chainTraceStep h k (chainTrace h k iv blocks) b :=
  List.foldl_concat _ _ _ _

/-- On valid `k.length`-bit chains, the first component of `chainTrace` agrees with
`merkleDamgardChain`. -/
private theorem fst_chainTrace_eq_merkleDamgardChain {h : List Bool → List Bool → List Bool}
    {k iv : List Bool} {blocks : List (List Bool)}
    (hlen : ∀ x, x.length = 2 * k.length → (h k x).length = k.length)
    (hiv : iv.length = k.length)
    (hblocks : ∀ b ∈ blocks, b.length = k.length) :
    (chainTrace h k iv blocks).1 = merkleDamgardChain h k iv blocks := by
  induction blocks using List.reverseRecOn with
  | nil => rfl
  | append_singleton bs b ih =>
    have hbs : ∀ b' ∈ bs, b'.length = k.length :=
      fun b' hb' => hblocks b' (List.mem_append_left _ hb')
    have hb : b.length = k.length :=
      hblocks b (List.mem_append_right _ (List.mem_singleton_self b))
    have hchainLen : (merkleDamgardChain h k iv bs).length = k.length :=
      length_merkleDamgardChain hlen hiv hbs
    rw [chainTrace_concat, merkleDamgardChain_concat]
    simp only [chainTraceStep, ih hbs, padOrTake_eq_self hchainLen, padOrTake_eq_self hb]

/-- Appending a `k.length`-bit block `b` to a valid chain prepends the final compression input
`merkleDamgardChain h k iv blocks ++ b` to the recorded trace. -/
private theorem snd_chainTrace_concat_of_length {h : List Bool → List Bool → List Bool}
    {k iv : List Bool} {blocks : List (List Bool)} {b : List Bool}
    (hlen : ∀ x, x.length = 2 * k.length → (h k x).length = k.length)
    (hiv : iv.length = k.length)
    (hblocks : ∀ b' ∈ blocks, b'.length = k.length)
    (hb : b.length = k.length) :
    (chainTrace h k iv (blocks ++ [b])).2 =
      (merkleDamgardChain h k iv blocks ++ b) :: (chainTrace h k iv blocks).2 := by
  have hchainLen : (merkleDamgardChain h k iv blocks).length = k.length :=
    length_merkleDamgardChain hlen hiv hblocks
  rw [chainTrace_concat]
  simp only [chainTraceStep, fst_chainTrace_eq_merkleDamgardChain hlen hiv hblocks,
    padOrTake_eq_self hchainLen, padOrTake_eq_self hb]

@[local fun_prop]
private theorem computableTidilyInPolyTime_chainTrace
    {h : List Bool → List Bool → List Bool}
    (hh : ComputableTidilyInPolyTime (fun p : List Bool × List Bool => h p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, x.length = 2 * k.length → (h k x).length = k.length)
    {γ : Type} {encIn : γ ↪ List Bool}
    {k iv : γ → List Bool} {bs : γ → List (List Bool)}
    (hk : ComputableTidilyInPolyTime k encIn encBits)
    (hiv : ComputableTidilyInPolyTime iv encIn encBits)
    (hbs : ComputableTidilyInPolyTime bs encIn (encList encBits)) :
    ComputableTidilyInPolyTime (fun a => chainTrace h (k a) (iv a) (bs a))
      encIn (encPair encBits (encList encBits)) := by
  have hstep : ComputableTidilyInPolyTime
      (fun p : (List Bool × (List Bool × List (List Bool))) × List Bool =>
        chainTraceStep h p.1.1 p.1.2 p.2)
      (encPair (encPair encBits (encPair encBits (encList encBits))) encBits)
      (encPair encBits (encList encBits)) := by
    have hk_p : ComputableTidilyInPolyTime
        (fun p : (List Bool × (List Bool × List (List Bool))) × List Bool => p.1.1)
        (encPair (encPair encBits (encPair encBits (encList encBits))) encBits) encBits := by
      fun_prop
    have hx_p : ComputableTidilyInPolyTime
        (fun p : (List Bool × (List Bool × List (List Bool))) × List Bool =>
          padOrTake p.1.1.length p.1.2.1 ++ padOrTake p.1.1.length p.2)
        (encPair (encPair encBits (encPair encBits (encList encBits))) encBits) encBits := by
      polytime
    have hhx : ComputableTidilyInPolyTime
        (fun p : (List Bool × (List Bool × List (List Bool))) × List Bool =>
          h p.1.1 (padOrTake p.1.1.length p.1.2.1 ++ padOrTake p.1.1.length p.2))
        (encPair (encPair encBits (encPair encBits (encList encBits))) encBits) encBits :=
      hh.comp (hk_p.prod hx_p)
    have htail_p : ComputableTidilyInPolyTime
        (fun p : (List Bool × (List Bool × List (List Bool))) × List Bool => p.1.2.2)
        (encPair (encPair encBits (encPair encBits (encList encBits))) encBits)
        (encList encBits) := by
      fun_prop
    exact hhx.prod (hx_p.cons' htail_p)
  apply ComputableTidilyInPolyTime.foldlWith_of_bounded_growth
    (encA := encBits) (encL := encList encBits)
    (encP := encBits) (encB := encPair encBits (encList encBits))
    (step := chainTraceStep h)
    hk hbs (hiv.prod (.const [])) hstep
    (growth := fun a => 6 * (k a).length + 2)
    (((PolyBounded.const 6).mul hk.polyBounded_length).add (.const 2))
  intro a state b _
  have hxlen : (padOrTake (k a).length state.1 ++ padOrTake (k a).length b).length =
      2 * (k a).length := by
    rw [List.length_append, length_padOrTake, length_padOrTake]
    omega
  have hhlen : (h (k a) (padOrTake (k a).length state.1 ++ padOrTake (k a).length b)).length =
      (k a).length :=
    hlen (k a) _ hxlen
  simp only [chainTraceStep, length_encPair, encList_cons, List.length_append, length_frame,
    encBits_apply, hhlen, hxlen]
  lia

/-- Computing `chainTrace` is polynomial-time for any polynomial-time compression function `h`. -/
@[program_certificate]
theorem computableInPolyTime_chainTrace
    {h : List Bool → List Bool → List Bool}
    (hh : ComputableInPolyTime (fun p : List Bool × List Bool => h p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, x.length = 2 * k.length → (h k x).length = k.length) :
    ComputableInPolyTime
      (fun p : List Bool × List Bool × List (List Bool) =>
        chainTrace h p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encBits (encList encBits)))
      (encPair encBits (encList encBits)) :=
  .of_tidy (computableTidilyInPolyTime_chainTrace hh.tidy hlen
    (by fun_prop) (by fun_prop) (by fun_prop))

/-- Extract a candidate `2n`-bit collision `(x₁, x₂)` for `h k` from two block chains `bs₁` and
`bs₂` by scanning their compression inputs backward from the final step and returning the first
differing pair of inputs (or `([], [])` if none differ). -/
def extractChainCollision (h : List Bool → List Bool → List Bool)
    (k iv : List Bool) (bs₁ bs₂ : List (List Bool)) : List Bool × List Bool :=
  (((chainTrace h k iv bs₁).2.zip (chainTrace h k iv bs₂).2).find?
    (fun p => p.1 != p.2)).getD ([], [])

@[local fun_prop]
private theorem computableTidilyInPolyTime_extractChainCollision
    {h : List Bool → List Bool → List Bool}
    (hh : ComputableTidilyInPolyTime (fun p : List Bool × List Bool => h p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, x.length = 2 * k.length → (h k x).length = k.length)
    {γ : Type} {encIn : γ ↪ List Bool}
    {k iv : γ → List Bool} {bs₁ bs₂ : γ → List (List Bool)}
    (hk : ComputableTidilyInPolyTime k encIn encBits)
    (hiv : ComputableTidilyInPolyTime iv encIn encBits)
    (hbs₁ : ComputableTidilyInPolyTime bs₁ encIn (encList encBits))
    (hbs₂ : ComputableTidilyInPolyTime bs₂ encIn (encList encBits)) :
    ComputableTidilyInPolyTime
      (fun a => extractChainCollision h (k a) (iv a) (bs₁ a) (bs₂ a))
      encIn (encPair encBits encBits) := by
  have ht₁ := (computableTidilyInPolyTime_chainTrace hh hlen hk hiv hbs₁).snd'
  have ht₂ := (computableTidilyInPolyTime_chainTrace hh hlen hk hiv hbs₂).snd'
  have hzip : ComputableTidilyInPolyTime
      (fun a => (chainTrace h (k a) (iv a) (bs₁ a)).2.zip (chainTrace h (k a) (iv a) (bs₂ a)).2)
      encIn (encList (encPair encBits encBits)) :=
    (ComputableTidilyInPolyTime.zip encBits encBits).comp (ht₁.prod ht₂)
  have hfind : ComputableTidilyInPolyTime
      (fun a => ((chainTrace h (k a) (iv a) (bs₁ a)).2.zip
        (chainTrace h (k a) (iv a) (bs₂ a)).2).find? (fun p => p.1 != p.2))
      encIn (encOption (encPair encBits encBits)) :=
    ComputableTidilyInPolyTime.findWithInput (test := fun _ p => p.1 != p.2) hzip (by polytime)
  exact ComputableTidilyInPolyTime.optionGetDWithInput hfind (.const ([], []))

/-- Extracting a compression collision from two block chains is computable in plain polynomial
time. -/
@[program_certificate]
theorem computableInPolyTime_extractChainCollision
    {h : List Bool → List Bool → List Bool}
    (hh : ComputableInPolyTime (fun p : List Bool × List Bool => h p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, x.length = 2 * k.length → (h k x).length = k.length) :
    ComputableInPolyTime
      (fun p : List Bool × List Bool × List (List Bool) × List (List Bool) =>
        extractChainCollision h p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encBits (encPair encBits (encPair (encList encBits) (encList encBits))))
      (encPair encBits encBits) :=
  .of_tidy (computableTidilyInPolyTime_extractChainCollision hh.tidy hlen
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop))

/-- Stepping `extractChainCollision` from the right on two non-empty valid chains: if the final
compression inputs `x₁` and `x₂` differ, return `(x₁, x₂)`; otherwise peel the final blocks and
continue on the prefixes `bs₁` and `bs₂`. -/
private theorem extractChainCollision_concat_of_length {h : List Bool → List Bool → List Bool}
    {k iv : List Bool} {bs₁ bs₂ : List (List Bool)} {b₁ b₂ : List Bool}
    (hlen : ∀ x, x.length = 2 * k.length → (h k x).length = k.length)
    (hiv : iv.length = k.length)
    (hbs₁ : ∀ b ∈ bs₁, b.length = k.length) (hb₁ : b₁.length = k.length)
    (hbs₂ : ∀ b ∈ bs₂, b.length = k.length) (hb₂ : b₂.length = k.length) :
    extractChainCollision h k iv (bs₁ ++ [b₁]) (bs₂ ++ [b₂]) =
      let x₁ := merkleDamgardChain h k iv bs₁ ++ b₁
      let x₂ := merkleDamgardChain h k iv bs₂ ++ b₂
      if x₁ != x₂ then (x₁, x₂) else extractChainCollision h k iv bs₁ bs₂ := by
  simp only [extractChainCollision,
    snd_chainTrace_concat_of_length hlen hiv hbs₁ hb₁,
    snd_chainTrace_concat_of_length hlen hiv hbs₂ hb₂,
    List.zip_cons_cons, List.find?_cons]
  cases merkleDamgardChain h k iv bs₁ ++ b₁ != merkleDamgardChain h k iv bs₂ ++ b₂ <;> rfl

/-- **Fundamental Merkle–Damgård chain collision lemma (suffix-free form)**:
if `bs₁` and `bs₂` are lists of `k.length`-bit blocks such that neither is a suffix of the other
and `merkleDamgardChain h k iv bs₁ = merkleDamgardChain h k iv bs₂`, then
`extractChainCollision h k iv bs₁ bs₂` produces a valid `2 * k.length`-bit collision for `h k`. -/
theorem isCollision_extractChainCollision_of_not_suffix
    {h : List Bool → List Bool → List Bool} {k iv : List Bool}
    {bs₁ bs₂ : List (List Bool)}
    (hlen : ∀ x, x.length = 2 * k.length → (h k x).length = k.length)
    (hiv : iv.length = k.length)
    (hbs₁ : ∀ b ∈ bs₁, b.length = k.length)
    (hbs₂ : ∀ b ∈ bs₂, b.length = k.length)
    (hchain : merkleDamgardChain h k iv bs₁ = merkleDamgardChain h k iv bs₂)
    (hsuf₁ : ¬ (bs₁ <:+ bs₂))
    (hsuf₂ : ¬ (bs₂ <:+ bs₁)) :
    isCollision h validCompressionInput k.length k
      (extractChainCollision h k iv bs₁ bs₂).1
      (extractChainCollision h k iv bs₁ bs₂).2 = true := by
  induction bs₁ using List.reverseRecOn generalizing bs₂ with
  | nil => exact False.elim (hsuf₁ List.nil_suffix)
  | append_singleton bs₁' b₁ ih =>
    induction bs₂ using List.reverseRecOn with
    | nil => exact False.elim (hsuf₂ List.nil_suffix)
    | append_singleton bs₂' b₂ _ =>
      have hbs₁' : ∀ b ∈ bs₁', b.length = k.length :=
        fun b hb => hbs₁ b (List.mem_append_left _ hb)
      have hb₁ : b₁.length = k.length :=
        hbs₁ b₁ (List.mem_append_right _ (List.mem_singleton_self b₁))
      have hbs₂' : ∀ b ∈ bs₂', b.length = k.length :=
        fun b hb => hbs₂ b (List.mem_append_left _ hb)
      have hb₂ : b₂.length = k.length :=
        hbs₂ b₂ (List.mem_append_right _ (List.mem_singleton_self b₂))
      have hlen₁' : (merkleDamgardChain h k iv bs₁').length = k.length :=
        length_merkleDamgardChain hlen hiv hbs₁'
      have hlen₂' : (merkleDamgardChain h k iv bs₂').length = k.length :=
        length_merkleDamgardChain hlen hiv hbs₂'
      rw [extractChainCollision_concat_of_length hlen hiv hbs₁' hb₁ hbs₂' hb₂]
      dsimp only
      cases hbne : (merkleDamgardChain h k iv bs₁' ++ b₁ !=
          merkleDamgardChain h k iv bs₂' ++ b₂)
      · have hne : merkleDamgardChain h k iv bs₁' ++ b₁ =
            merkleDamgardChain h k iv bs₂' ++ b₂ := bne_eq_false_iff_eq.mp hbne
        have hinj := List.append_inj hne (by rw [hlen₁', hlen₂'])
        have hchain' : merkleDamgardChain h k iv bs₁' = merkleDamgardChain h k iv bs₂' := hinj.1
        have hb_eq : b₁ = b₂ := hinj.2
        subst hb_eq
        apply ih hbs₁' hbs₂' hchain'
        · rintro ⟨p, rfl⟩
          exact hsuf₁ ⟨p, (List.append_assoc p bs₁' [b₁]).symm⟩
        · rintro ⟨p, rfl⟩
          exact hsuf₂ ⟨p, (List.append_assoc p bs₂' [b₁]).symm⟩
      · have hne : merkleDamgardChain h k iv bs₁' ++ b₁ ≠
            merkleDamgardChain h k iv bs₂' ++ b₂ := bne_iff_ne.mp hbne
        simp only [↓reduceIte, isCollision_eq_true_iff, validCompressionInput_eq_true_iff]
        refine ⟨by rw [List.length_append, hlen₁', hb₁]; omega,
          by rw [List.length_append, hlen₂', hb₂]; omega, hne, ?_⟩
        simpa only [merkleDamgardChain_concat] using hchain

/-- **Merkle–Damgård chain collision lemma (distinct final blocks, [BonehShoup2023], Theorem 8.3
Case 1)**: if two non-empty `k.length`-bit block chains `bs₁` and `bs₂` differ in their last block
(`bs₁.getLast? ≠ bs₂.getLast?`) and produce the same chain digest, then `extractChainCollision`
returns a `2 * k.length`-bit collision for `h k`. -/
theorem isCollision_extractChainCollision_of_getLast?_ne
    {h : List Bool → List Bool → List Bool} {k iv : List Bool}
    {bs₁ bs₂ : List (List Bool)}
    (hlen : ∀ x, x.length = 2 * k.length → (h k x).length = k.length)
    (hiv : iv.length = k.length)
    (hbs₁ : ∀ b ∈ bs₁, b.length = k.length)
    (hbs₂ : ∀ b ∈ bs₂, b.length = k.length)
    (hne₁ : bs₁ ≠ []) (hne₂ : bs₂ ≠ [])
    (hlast : bs₁.getLast? ≠ bs₂.getLast?)
    (hchain : merkleDamgardChain h k iv bs₁ = merkleDamgardChain h k iv bs₂) :
    isCollision h validCompressionInput k.length k
      (extractChainCollision h k iv bs₁ bs₂).1
      (extractChainCollision h k iv bs₁ bs₂).2 = true := by
  apply isCollision_extractChainCollision_of_not_suffix hlen hiv hbs₁ hbs₂ hchain
  · rintro ⟨p, rfl⟩
    exact hlast (List.getLast?_append_of_ne_nil p hne₁).symm
  · rintro ⟨p, rfl⟩
    exact hlast (List.getLast?_append_of_ne_nil p hne₂)

/-- **Merkle–Damgård chain collision lemma (equal block lengths, [BonehShoup2023], Theorem 8.3
Case 2)**: if two distinct `k.length`-bit block chains `bs₁ ≠ bs₂` of equal length
(`bs₁.length = bs₂.length`) produce the same chain digest, then `extractChainCollision` returns a
`2 * k.length`-bit collision for `h k`. -/
theorem isCollision_extractChainCollision_of_length_eq
    {h : List Bool → List Bool → List Bool} {k iv : List Bool}
    {bs₁ bs₂ : List (List Bool)}
    (hlen : ∀ x, x.length = 2 * k.length → (h k x).length = k.length)
    (hiv : iv.length = k.length)
    (hbs₁ : ∀ b ∈ bs₁, b.length = k.length)
    (hbs₂ : ∀ b ∈ bs₂, b.length = k.length)
    (hblen : bs₁.length = bs₂.length)
    (hne : bs₁ ≠ bs₂)
    (hchain : merkleDamgardChain h k iv bs₁ = merkleDamgardChain h k iv bs₂) :
    isCollision h validCompressionInput k.length k
      (extractChainCollision h k iv bs₁ bs₂).1
      (extractChainCollision h k iv bs₁ bs₂).2 = true := by
  apply isCollision_extractChainCollision_of_not_suffix hlen hiv hbs₁ hbs₂ hchain
  · rintro ⟨p, hp⟩
    have hplen : p.length = 0 := by
      have := congrArg List.length hp
      rw [List.length_append] at this
      omega
    rw [List.eq_nil_of_length_eq_zero hplen, List.nil_append] at hp
    exact hne hp
  · rintro ⟨p, hp⟩
    have hplen : p.length = 0 := by
      have := congrArg List.length hp
      rw [List.length_append] at this
      omega
    rw [List.eq_nil_of_length_eq_zero hplen, List.nil_append] at hp
    exact hne hp.symm

/-- **General suffix-free block-encoding Merkle–Damgård reduction**:
for any polynomial-time block encoder `encode : ℕ → List Bool → List (List Bool)` that maps valid
messages at parameter `n` (for all sufficiently large `n`) into suffix-free lists of `n`-bit
blocks, iterating a collision-resistant `CompressionFamily` over `encode k.length msg` yields a
collision-resistant hash family on `valid`. -/
theorem CompressionFamily.collisionResistantOn_merkleDamgardChain
    {h : List Bool → List Bool → List Bool} (hh : CompressionFamily h)
    (encode : ℕ → List Bool → List (List Bool))
    (valid : ℕ → List Bool → Bool)
    (hencode : ComputableInPolyTime
      (fun p : ℕ × List Bool => encode p.1 p.2)
      (encPair encUnary encBits) (encList encBits))
    (hblocks : ∀ᶠ n in Filter.atTop, ∀ m, valid n m = true →
      ∀ b ∈ encode n m, b.length = n)
    (hsuffix : ∀ᶠ n in Filter.atTop, ∀ m₁ m₂,
      valid n m₁ = true → valid n m₂ = true → m₁ ≠ m₂ →
      ¬ (encode n m₁ <:+ encode n m₂)) :
    CollisionResistantOn
      (fun k msg => merkleDamgardChain h k (List.replicate k.length false) (encode k.length msg))
      valid := by
  let extract (n : ℕ) (k m₁ m₂ : List Bool) : List Bool × List Bool :=
    extractChainCollision h k (List.replicate n false) (encode n m₁) (encode n m₂)
  have hextract : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool × List Bool => extract p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair encBits (encPair encBits encBits)))
      (encPair encBits encBits) := by
    apply ComputableInPolyTime.of_tidy
    have henc₁ : ComputableTidilyInPolyTime
        (fun p : ℕ × List Bool × List Bool × List Bool => encode p.1 p.2.2.1)
        (encPair encUnary (encPair encBits (encPair encBits encBits)))
        (encList encBits) :=
      hencode.tidy.comp ((ComputableTidilyInPolyTime.fst _ _).prod
        ((ComputableTidilyInPolyTime.snd _ _).snd'.fst'))
    have henc₂ : ComputableTidilyInPolyTime
        (fun p : ℕ × List Bool × List Bool × List Bool => encode p.1 p.2.2.2)
        (encPair encUnary (encPair encBits (encPair encBits encBits)))
        (encList encBits) :=
      hencode.tidy.comp ((ComputableTidilyInPolyTime.fst _ _).prod
        ((ComputableTidilyInPolyTime.snd _ _).snd'.snd'))
    exact computableTidilyInPolyTime_extractChainCollision hh.polyTime.tidy hh.length_eq
      (by fun_prop) (by polytime) henc₁ henc₂
  refine hh.collisionResistant.of_extract extract hextract ?_
  filter_upwards [hblocks, hsuffix] with n hblk hsuf k hklen m₁ m₂ hcol
  rw [isCollision_eq_true_iff] at hcol
  rcases hcol with ⟨hv₁, hv₂, hne, hdigest⟩
  subst hklen
  exact isCollision_extractChainCollision_of_not_suffix (hh.length_eq k)
    (List.length_replicate) (hblk m₁ hv₁) (hblk m₂ hv₂) hdigest
    (hsuf m₁ m₂ hv₁ hv₂ hne) (hsuf m₂ m₁ hv₂ hv₁ hne.symm)

/-! ### Prefix-tagged bit-block encoding and unrestricted Merkle–Damgård hash family -/

/-- The initial marker block `0^n` placed at the start of `mdBlocks n msg`. -/
def mdEndBlock (n : ℕ) : List Bool :=
  List.replicate n false

/-- Encode a single message bit `b` as an `n`-bit block `1 ‖ b ‖ 0^{n-2}` (truncated to `n` bits
when `n < 2`). For `n ≥ 2`, the leading tag bit `true` distinguishes every data block from
`mdEndBlock n`, and the second bit `b` distinguishes the two bit values. -/
def mdDataBlock (n : ℕ) (b : Bool) : List Bool :=
  (true :: b :: List.replicate (n - 2) false).take n

/-- Encode an arbitrary bit string `msg : List Bool` as a non-empty list of `n`-bit blocks:
the initial marker block `mdEndBlock n` followed by one `mdDataBlock n` per bit of `msg`.
Because `mdEndBlock n` starts with `false` and every `mdDataBlock n b` starts with `true`, no
distinct message encoding can be a suffix of another whenever `n ≥ 2`. -/
def mdBlocks (n : ℕ) (msg : List Bool) : List (List Bool) :=
  mdEndBlock n :: msg.map (mdDataBlock n)

@[simp]
theorem length_mdEndBlock (n : ℕ) : (mdEndBlock n).length = n :=
  List.length_replicate

@[simp]
theorem length_mdDataBlock (n : ℕ) (b : Bool) : (mdDataBlock n b).length = n := by
  simp only [mdDataBlock, List.length_take, List.length_cons, List.length_replicate]
  omega

private theorem length_of_mem_mdBlocks {n : ℕ} {msg : List Bool} {b : List Bool}
    (hb : b ∈ mdBlocks n msg) : b.length = n := by
  simp only [mdBlocks, List.mem_cons, List.mem_map] at hb
  rcases hb with rfl | ⟨bit, _, rfl⟩
  · exact length_mdEndBlock n
  · exact length_mdDataBlock n bit

private theorem mdEndBlock_ne_mdDataBlock {n : ℕ} (hn : 1 ≤ n) (b : Bool) :
    mdEndBlock n ≠ mdDataBlock n b := by
  cases n with
  | zero => omega
  | succ m =>
    intro h
    have hhead := congrArg List.head? h
    simp [mdEndBlock, mdDataBlock, List.replicate_succ] at hhead

private theorem mdEndBlock_not_mem_map_mdDataBlock {n : ℕ} (hn : 1 ≤ n) (msg : List Bool) :
    mdEndBlock n ∉ msg.map (mdDataBlock n) := by
  rw [List.mem_map]
  rintro ⟨b, _, hb⟩
  exact mdEndBlock_ne_mdDataBlock hn b hb.symm

private theorem mdDataBlock_injective {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective (mdDataBlock n) := by
  rcases n with _ | _ | m
  · omega
  · omega
  · intro b₁ b₂ h
    have htail := congrArg (fun l => l.tail.head?) h
    simpa [mdDataBlock] using htail

/-- For `n ≥ 2`, `mdBlocks n m₁` is a suffix of `mdBlocks n m₂` if and only if `m₁ = m₂`. -/
theorem mdBlocks_suffix_iff {n : ℕ} (hn : 2 ≤ n) {m₁ m₂ : List Bool} :
    mdBlocks n m₁ <:+ mdBlocks n m₂ ↔ m₁ = m₂ := by
  constructor
  · rintro ⟨p, hp⟩
    cases p with
    | nil =>
      simp only [mdBlocks, List.nil_append, List.cons.injEq, true_and] at hp
      exact List.map_injective_iff.mpr (mdDataBlock_injective hn) hp
    | cons a p' =>
      simp only [mdBlocks, List.cons_append, List.cons.injEq] at hp
      have hmem : mdEndBlock n ∈ m₂.map (mdDataBlock n) := by
        rw [← hp.2]
        exact List.mem_append_right _ List.mem_cons_self
      exact False.elim (mdEndBlock_not_mem_map_mdDataBlock (by omega) m₂ hmem)
  · rintro rfl
    exact List.suffix_refl _

private theorem not_suffix_mdBlocks {n : ℕ} (hn : 2 ≤ n) {m₁ m₂ : List Bool} (hne : m₁ ≠ m₂) :
    ¬ (mdBlocks n m₁ <:+ mdBlocks n m₂) :=
  mt (mdBlocks_suffix_iff hn).mp hne

@[local fun_prop]
private theorem computableTidilyInPolyTime_mdEndBlock
    {γ : Type} {encIn : γ ↪ List Bool} {n : γ → ℕ}
    (hn : ComputableTidilyInPolyTime n encIn encUnary) :
    ComputableTidilyInPolyTime (fun a => mdEndBlock (n a)) encIn encBits := by
  unfold mdEndBlock
  polytime

@[local fun_prop]
private theorem computableTidilyInPolyTime_mdDataBlock
    {γ : Type} {encIn : γ ↪ List Bool} {n : γ → ℕ} {b : γ → Bool}
    (hn : ComputableTidilyInPolyTime n encIn encUnary)
    (hb : ComputableTidilyInPolyTime b encIn encBool) :
    ComputableTidilyInPolyTime (fun a => mdDataBlock (n a) (b a)) encIn encBits := by
  unfold mdDataBlock
  polytime

@[local fun_prop]
private theorem computableTidilyInPolyTime_mdBlocks
    {γ : Type} {encIn : γ ↪ List Bool} {n : γ → ℕ} {msg : γ → List Bool}
    (hn : ComputableTidilyInPolyTime n encIn encUnary)
    (hmsg : ComputableTidilyInPolyTime msg encIn encBits) :
    ComputableTidilyInPolyTime (fun a => mdBlocks (n a) (msg a)) encIn (encList encBits) := by
  have hhead : ComputableTidilyInPolyTime (fun a => mdEndBlock (n a)) encIn encBits :=
    computableTidilyInPolyTime_mdEndBlock hn
  have htail : ComputableTidilyInPolyTime
      (fun a => (msg a).map (mdDataBlock (n a))) encIn (encList encBits) :=
    ComputableTidilyInPolyTime.mapWithInput
      (ComputableTidilyInPolyTime.bitsToList.comp hmsg)
      (computableTidilyInPolyTime_mdDataBlock
        (hn.comp (ComputableTidilyInPolyTime.fst _ _))
        (ComputableTidilyInPolyTime.snd _ _))
  exact hhead.cons' htail

/-- Encoding a bit string into `n`-bit Merkle–Damgård blocks is computable in plain polynomial
time. -/
@[program_certificate]
theorem computableInPolyTime_mdBlocks :
    ComputableInPolyTime (fun p : ℕ × List Bool => mdBlocks p.1 p.2)
      (encPair encUnary encBits) (encList encBits) :=
  .of_tidy (computableTidilyInPolyTime_mdBlocks (by fun_prop) (by fun_prop))

/-- **The Merkle–Damgård hash family (`merkleDamgard`)**: hash an arbitrary-length bit string
`msg : List Bool` under key `k : List Bool` by iterating the `2n → n` compression function `h k`
over `mdBlocks k.length msg` from the initial vector `0^{k.length}`. -/
def merkleDamgard (h : List Bool → List Bool → List Bool) (k msg : List Bool) : List Bool :=
  merkleDamgardChain h k (List.replicate k.length false) (mdBlocks k.length msg)

/-- For any compression function `h` mapping `2 * k.length`-bit inputs to `k.length`-bit outputs,
`merkleDamgard h k msg` always has length `k.length`. -/
theorem length_merkleDamgard {h : List Bool → List Bool → List Bool}
    {k msg : List Bool}
    (hlen : ∀ x, x.length = 2 * k.length → (h k x).length = k.length) :
    (merkleDamgard h k msg).length = k.length :=
  length_merkleDamgardChain hlen List.length_replicate
    (fun _ hb => length_of_mem_mdBlocks hb)

/-- On every key `k` and message `msg`, `merkleDamgard h k msg` agrees with the first component of
`chainTrace`. -/
private theorem merkleDamgard_eq_fst_chainTrace {h : List Bool → List Bool → List Bool}
    {k msg : List Bool}
    (hlen : ∀ x, x.length = 2 * k.length → (h k x).length = k.length) :
    merkleDamgard h k msg =
      (chainTrace h k (List.replicate k.length false) (mdBlocks k.length msg)).1 :=
  (fst_chainTrace_eq_merkleDamgardChain hlen List.length_replicate
    (fun _ hb => length_of_mem_mdBlocks hb)).symm

@[local fun_prop]
private theorem computableTidilyInPolyTime_merkleDamgard
    {h : List Bool → List Bool → List Bool}
    (hh : ComputableTidilyInPolyTime (fun p : List Bool × List Bool => h p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, x.length = 2 * k.length → (h k x).length = k.length)
    {γ : Type} {encIn : γ ↪ List Bool} {k msg : γ → List Bool}
    (hk : ComputableTidilyInPolyTime k encIn encBits)
    (hmsg : ComputableTidilyInPolyTime msg encIn encBits) :
    ComputableTidilyInPolyTime (fun a => merkleDamgard h (k a) (msg a)) encIn encBits := by
  have heq : (fun a => merkleDamgard h (k a) (msg a)) =
      fun a => (chainTrace h (k a) (List.replicate (k a).length false)
        (mdBlocks (k a).length (msg a))).1 := by
    funext a
    exact merkleDamgard_eq_fst_chainTrace (hlen (k a))
  rw [heq]
  exact (computableTidilyInPolyTime_chainTrace hh hlen hk (by polytime)
    (computableTidilyInPolyTime_mdBlocks (by polytime) hmsg)).fst'

/-- Evaluating `merkleDamgard h` is computable in plain polynomial time whenever `h` is computable
in polynomial time and compresses `2n`-bit inputs to `n`-bit digests. -/
@[program_certificate]
theorem computableInPolyTime_merkleDamgard
    {h : List Bool → List Bool → List Bool}
    (hh : ComputableInPolyTime (fun p : List Bool × List Bool => h p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, x.length = 2 * k.length → (h k x).length = k.length) :
    ComputableInPolyTime (fun p : List Bool × List Bool => merkleDamgard h p.1 p.2)
      (encPair encBits encBits) encBits :=
  .of_tidy (computableTidilyInPolyTime_merkleDamgard hh.tidy hlen (by fun_prop) (by fun_prop))

/-- Deterministically extract a `2 * k.length`-bit compression collision for `h k` from two
messages `m₁, m₂ : List Bool` that collide under `merkleDamgard h k`. -/
def extractMerkleDamgardCollision (h : List Bool → List Bool → List Bool)
    (k m₁ m₂ : List Bool) : List Bool × List Bool :=
  extractChainCollision h k (List.replicate k.length false)
    (mdBlocks k.length m₁) (mdBlocks k.length m₂)

/-- Extracting a `2n`-bit compression collision from a `merkleDamgard h` collision is computable
in plain polynomial time. -/
@[program_certificate]
theorem computableInPolyTime_extractMerkleDamgardCollision
    {h : List Bool → List Bool → List Bool}
    (hh : ComputableInPolyTime (fun p : List Bool × List Bool => h p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, x.length = 2 * k.length → (h k x).length = k.length) :
    ComputableInPolyTime
      (fun p : List Bool × List Bool × List Bool =>
        extractMerkleDamgardCollision h p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encBits encBits))
      (encPair encBits encBits) := by
  apply ComputableInPolyTime.of_tidy
  exact computableTidilyInPolyTime_extractChainCollision hh.tidy hlen
    (by fun_prop) (by polytime)
    (computableTidilyInPolyTime_mdBlocks (by polytime) (by fun_prop))
    (computableTidilyInPolyTime_mdBlocks (by polytime) (by fun_prop))

/-- **Deterministic Merkle–Damgård collision extraction ([BonehShoup2023], Theorem 8.3)**:
for any key `k` of length `≥ 2` and any two distinct messages `m₁ ≠ m₂` with
`merkleDamgard h k m₁ = merkleDamgard h k m₂`, `extractMerkleDamgardCollision h k m₁ m₂` outputs a
valid `2 * k.length`-bit collision `(x₁, x₂)` for `h k`. -/
theorem isCollision_extractMerkleDamgardCollision
    {h : List Bool → List Bool → List Bool} {k m₁ m₂ : List Bool}
    (hlen : ∀ x, x.length = 2 * k.length → (h k x).length = k.length)
    (hk : 2 ≤ k.length) (hne : m₁ ≠ m₂)
    (hcol : merkleDamgard h k m₁ = merkleDamgard h k m₂) :
    isCollision h validCompressionInput k.length k
      (extractMerkleDamgardCollision h k m₁ m₂).1
      (extractMerkleDamgardCollision h k m₁ m₂).2 = true :=
  isCollision_extractChainCollision_of_not_suffix hlen List.length_replicate
    (fun _ hb => length_of_mem_mdBlocks hb)
    (fun _ hb => length_of_mem_mdBlocks hb)
    hcol (not_suffix_mdBlocks hk hne) (not_suffix_mdBlocks hk hne.symm)

/-- **Security of the Merkle–Damgård transform ([BonehShoup2023], Theorem 8.3)**:
if `h` is a `2n → n` collision-resistant compression family (`CompressionFamily h`), then
`merkleDamgard h` is collision-resistant on all arbitrary-length bit strings (`List Bool`). -/
theorem CompressionFamily.collisionResistant_merkleDamgard
    {h : List Bool → List Bool → List Bool} (hh : CompressionFamily h) :
    CollisionResistant (merkleDamgard h) := by
  refine hh.collisionResistantOn_merkleDamgardChain mdBlocks (fun _ _ => true)
    computableInPolyTime_mdBlocks ?_ ?_
  · exact Filter.Eventually.of_forall fun _ _ _ _ hb => length_of_mem_mdBlocks hb
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn m₁ m₂ _ _ hne
    exact not_suffix_mdBlocks hn hne

/-- **Domain extension from compression families to unrestricted hash families**:
every `2n → n` collision-resistant `CompressionFamily h` induces a full-domain collision-resistant
`HashFamily (merkleDamgard h)` on arbitrary bit strings. -/
theorem CompressionFamily.hashFamily_merkleDamgard
    {h : List Bool → List Bool → List Bool} (hh : CompressionFamily h) :
    HashFamily (merkleDamgard h) where
  polyTime := computableInPolyTime_merkleDamgard hh.polyTime hh.length_eq
  length_eq k _ := length_merkleDamgard (hh.length_eq k)
  collisionResistant := hh.collisionResistant_merkleDamgard

end Cslib.Crypto
