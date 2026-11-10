/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.CollisionResistant
public import CslibFrontier.Crypto.Computational.MerkleDamgard
public import CslibFrontier.Foundations.Data.BitString.List
public import CslibFrontier.Foundations.Data.BitString.List.Binary
public import CslibFrontier.Languages.Probabilistic.UniformNat
public import CslibFrontier.Probability.UniformNat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Foundations.Data.BitString.Binary
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event

/-!
# Target collision resistance and universal one-way hash families

A keyed hash family `H` with key-length schedule `keyLen : ℕ → ℕ` is **target collision-resistant**
(equivalently, a **universal one-way hash family**, UOWHF; [NaorYung1989], Section 2;
[BonehShoup2023], Section 8.11.2, Attack Game 8.5 and Definition 8.7; [Goldreich2004],
Section 6.4.3) if no uniform strict PPT two-stage adversary `A = (choose, find)` can win the
following game with non-negligible probability:

1. Given `1^n`, `A.choose n` selects a target input `m₀` and saved state `st` *before* the hash key
   is sampled;
2. A uniform key `k ← {0, 1}^{keyLen n}` is sampled;
3. Given `(1^n, st, k)`, `A.find n st k` outputs a candidate input `m₁`;
4. `A` wins when `m₀` and `m₁` satisfy the domain predicate `valid n`, `m₀ ≠ m₁`, and
   `H n k m₀ = H n k m₁`.

Unlike full collision resistance (`CollisionResistantOn`), where a single key `k` can be reused
across every Merkle–Damgård step, plugging a target collision-resistant compression function with
one fixed key directly into Merkle–Damgård can fail to give a target collision-resistant hash
([BonehShoup2023], Section 8.11.3, p. 340). The tree constructions adapted here use independent keys
across stages so that the reduction can compute the target compression input at a guessed stage
before receiving the challenge key at that stage ([NaorYung1989], March 13, 1995 manuscript
revision, Section 2.3; [Goldreich2004], Section 6.4.3.2, June 2003 chapter draft Constructions
6.4.24 and 6.4.26, Propositions 6.4.25 and 6.4.27).

We formalize:
1. Two-stage target-collision adversaries (`TargetCollisionFinder`, `TargetCollisionFinder.IsPPT`),
   the experiment `targetCollisionGame` with strict PPT certificates, and security predicates
   `TargetCollisionResistantOn` and `TargetCollisionResistant`, together with the zero-loss
   implication from full collision resistance (`CollisionResistantOn.targetCollisionResistantOn`).
2. Syntactic and plain polynomial-time bundled interfaces `KeyedCompressionFamily` (`2M(n) → M(n)`
   under `keyLen n`-bit keys with `n ≤ M(n)`) and `KeyedHashFamily` (unrestricted bit-string inputs
   under `keyLen n`-bit keys with `n ≤ digestLen n`), allowing polynomial key and digest schedules,
   plus bridges from `CompressionFamily` and `HashFamily`.
3. Level-keyed binary-tree + length-block domain extension (`uowhfTreeHash`), stretching any
   target collision-resistant `KeyedCompressionFamily` to an unrestricted target collision-resistant
   `KeyedHashFamily` on all `List Bool` using `(n + 1) * keyLen n`-bit keys
   (`KeyedCompressionFamily.treeHash`, `KeyedCompressionFamily.targetCollisionResistant_treeHash`).

### Source mapping and finite-parameter boundary

Whereas [BonehShoup2023], Section 8.11.3 (pp. 339–340, Fig. 8.15 and Theorem 8.13) presents a linear
chain that reuses one compression key `k₁` at every step and XORs one of `1 + log₂ L` masks
`k₂[ν(i)]` into the chaining value, so that its key is logarithmic in the message length (and
mentions a tree-based alternative with logarithmic-size keys on p. 340), and the Naor–Yung (1995
revision, Section 2.3) and Goldreich (June 2003 draft, Section 6.4.3.2) tree constructions hash
fixed-length block sequences before composing with length disambiguation, `uowhfTreeHash` adapts
level-keyed binary-tree hashing into a single total function on `List Bool`:
* `uowhfLeaves` encodes each bit of `msg` as a zero-padded `M`-bit leaf block (`[0^M]` when
  `msg = []`), where `M = blockLen n` satisfies `n ≤ M`;
* `uowhfTreeLevels` folds `n` fixed binary-tree halving levels under independent subkeys
  `k_0, ..., k_{n-1}`, and `top.headD []` selects the first resulting block;
* a final `(n + 1)`-st compression under `k_n` combines that block with
  `BitString.lowBits M msg.length` (`msg.length mod 2^M`).

At any fixed parameter `n`, messages with `msg.length > 2 ^ n` exceed the `n`-level tree capacity:
`top` has multiple blocks and `top.headD []` discards the extra roots (for example, at `n = 1`,
`[false, false, false]` and `[false, false, true]` produce identical digests for every `h`, `K`,
`keyLen`, and `blockLen`). The arbitrary-input security theorem
`KeyedCompressionFamily.targetCollisionResistant_treeHash` holds asymptotically because strict-PPT
admissibility bounds the output lengths of both `adversary.choose` and `adversary.find` by
polynomials in `n`; for all sufficiently large `n`, every supported `m₀` and `m₁` satisfies
`length < 2 ^ n ≤ 2 ^ M`, within the injective tree and length-block regime where `top` is a
singleton and `lowBits M` records `msg.length` injectively.

## Main definitions

* `Cslib.Crypto.TargetCollisionFinder`, `Cslib.Crypto.TargetCollisionFinder.IsPPT`: two-stage
  target-collision adversaries and uniform strict PPT admissibility.
* `Cslib.Crypto.targetCollisionGame`, `Cslib.Crypto.TargetCollisionResistantOn`,
  `Cslib.Crypto.TargetCollisionResistant`: two-stage target-collision game and security predicates.
* `Cslib.Crypto.KeyedCompressionFamily`, `Cslib.Crypto.KeyedHashFamily`: keyed compression and
  unrestricted hash families with polynomial key/digest schedules.
* `Cslib.Crypto.uowhfLeaves`, `Cslib.Crypto.uowhfPairInput`, `Cslib.Crypto.uowhfTreeStep`,
  `Cslib.Crypto.uowhfTreeLevels`, `Cslib.Crypto.uowhfTreeHash`: level-keyed binary-tree +
  length-block domain extension.
* `Cslib.Crypto.uowhfCandidateInput`, `Cslib.Crypto.uowhfTreeAdversary`: node compression-input
  extractor and two-stage planted-subkey reduction.

## Main results

* `Cslib.Crypto.isPPTOn_targetCollisionGame`, `Cslib.Crypto.isPPT_targetCollisionGame`: strict PPT
  certificates for `targetCollisionGame`.
* `Cslib.Crypto.CollisionResistantOn.targetCollisionResistantOn`: full collision resistance implies
  target collision resistance with identical game success probability.
* `Cslib.Crypto.computableInPolyTime_uowhfTreeHash`: plain polynomial-time evaluation of
  `uowhfTreeHash`.
* `Cslib.Crypto.exists_uowhfCandidateInput_collision`: deterministic extraction of a colliding
  `2M`-bit compression pair at some level `i ≤ n` and pair index `j < B`.
* `Cslib.Crypto.succProbability_targetCollisionGame_uowhfTreeHash_le`: concrete security bound for
  `uowhfTreeHash` with multiplicative loss `dyadicSize ((n + 1) * maxBlocks n)`.
* `Cslib.Crypto.KeyedCompressionFamily.targetCollisionResistant_treeHash`: any target
  collision-resistant `KeyedCompressionFamily` extends to an unrestricted target
  collision-resistant `KeyedHashFamily` on `List Bool`.

## References

* [M. Naor, M. Yung, *Universal One-Way Hash Functions and their Cryptographic
  Applications*][NaorYung1989], Section 2 (and Section 2.3 of the March 13, 1995 manuscript
  revision).
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Sections 8.11.2–8.11.3 (pp. 337–340).
* [O. Goldreich, *Foundations of Cryptography: Volume 2, Basic Applications*][Goldreich2004],
  Sections 6.4.3 and 6.4.3.2 (Constructions 6.4.24 and 6.4.26, Propositions 6.4.25 and 6.4.27 in
  the June 2003 chapter draft).
-/

public section

namespace Cslib.Crypto

open ProbComp Probability Turing.MultiTapeTM
open scoped NNReal

/-! ### Two-stage target collision resistance ([NaorYung1989], Section 2) -/

private theorem tidy_congr {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {f g : α → β} (h : ComputableTidilyInPolyTime f encIn encOut) (heq : ∀ a, f a = g a) :
    ComputableTidilyInPolyTime g encIn encOut :=
  funext heq ▸ h

private theorem of_tidy_congr {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {f g : α → β} (h : ComputableTidilyInPolyTime f encIn encOut) (heq : ∀ a, f a = g a) :
    ComputableInPolyTime g encIn encOut :=
  .of_tidy (tidy_congr h heq)

/-- A two-stage target-collision adversary ([NaorYung1989], Section 2; [BonehShoup2023],
Section 8.11.2, Attack Game 8.5 and Definition 8.7; [Goldreich2004], Section 6.4.3): `choose`
selects a target message and saved state from `1^n` before the hash key is sampled, and `find`
produces a second message after receiving the sampled key. -/
structure TargetCollisionFinder where
  /-- Select `(m₀, state)` given unary `n` before the hash key is chosen. -/
  choose : ℕ → ProbComp (List Bool × List Bool)
  /-- Given unary `n`, saved `state`, and sampled hash `key`, output a candidate `m₁`. -/
  find : ℕ → List Bool → List Bool → ProbComp (List Bool)

/-- Uniform strict PPT admissibility for both stages of a `TargetCollisionFinder`, charging the full
saved-state word passed from `choose` to `find`. -/
structure TargetCollisionFinder.IsPPT (adversary : TargetCollisionFinder) : Prop where
  /-- Target selection is uniform strict PPT on unary `n`. -/
  choose : IsPPTOn encUnary (encPair encBits encBits) adversary.choose
  /-- Second-preimage search is uniform strict PPT on `(1^n, state, key)`. -/
  find : IsPPTOn (encPair encUnary (encPair encBits encBits)) encBits
    (fun ⟨n, state, key⟩ => adversary.find n state key)

/-- The two-stage target-collision experiment ([NaorYung1989], Section 2; [BonehShoup2023],
Section 8.11.2, Attack Game 8.5): run `adversary.choose n` to obtain `(m₀, state)`, sample a
uniform `keyLen n`-bit key `k`, run `adversary.find n state k` to obtain `m₁`, and accept iff
`isCollision (H n) valid n k choice.1 m₁` holds. -/
@[expose]
noncomputable def targetCollisionGame
    (keyLen : ℕ → ℕ) (H : ℕ → List Bool → List Bool → List Bool)
    (valid : ℕ → List Bool → Bool)
    (adversary : TargetCollisionFinder) (n : ℕ) : ProbComp Bool := do
  let choice ← adversary.choose n
  let k ← BitString.sampleList (keyLen n)
  let m₁ ← adversary.find n choice.2 k
  return isCollision (H n) valid n k choice.1 m₁

/-- Run the complete target-collision experiment in uniform strict PPT on unary `n`. -/
@[program_certificate]
theorem isPPTOn_targetCollisionGame
    {keyLen : ℕ → ℕ} {H : ℕ → List Bool → List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} {adversary : TargetCollisionFinder}
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    (hH : ComputableInPolyTime (fun ⟨n, k, msg⟩ => H n k msg)
      (encPair encUnary (encPair encBits encBits)) encBits)
    (hvalid : ComputableInPolyTime (fun ⟨n, msg⟩ => valid n msg)
      (encPair encUnary encBits) encBool)
    (ha : adversary.IsPPT) :
    IsPPTOn encUnary encBool (targetCollisionGame keyLen H valid adversary) := by
  let E2 := encPair (encPair encUnary (encPair encBits encBits)) encBits
  let E3 := encPair E2 encBits
  have hq := ComputableTidilyInPolyTime.id' (encIn := E2)
  have hr := ComputableTidilyInPolyTime.id' (encIn := E3)
  have hn := hr.fst'.fst'.fst'; have hm₀ := hr.fst'.fst'.snd'.fst'
  have hk := hr.fst'.snd'; have hm₁ := hr.snd'
  have hcol : ComputableTidilyInPolyTime
      (fun r : ((ℕ × (List Bool × List Bool)) × List Bool) × List Bool =>
        isCollision (H r.1.1.1) valid r.1.1.1 r.1.2 r.1.1.2.1 r.2) E3 encBool :=
    tidy_congr ((((hvalid.tidy.comp (hn.prod hm₀)).bool_and'
      (hvalid.tidy.comp (hn.prod hm₁))).bool_and'
      (ComputableTidilyInPolyTime.bool_not.comp (hm₀.beq hm₁))).bool_and'
      (ComputableTidilyInPolyTime.beq
        (hH.tidy.comp (hn.prod (hk.prod hm₀))) (hH.tidy.comp (hn.prod (hk.prod hm₁)))))
      fun _ => rfl
  have hfind := ha.find.preprocess
    (of_tidy_congr (hq.fst'.fst'.prod (hq.fst'.snd'.snd'.prod hq.snd')) fun _ => rfl)
  exact ha.choose.bind_with
    ((isPPTOn_sampleList.preprocess (hkeyLen.comp' (ComputableInPolyTime.fst _ _))).bind_with
      (hfind.bind_with hcol.isPPTOn))

/-- The target-collision experiment is uniformly strict PPT, independently of unused auxiliary
input. -/
@[program_certificate]
theorem isPPT_targetCollisionGame
    {keyLen : ℕ → ℕ} {H : ℕ → List Bool → List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} {adversary : TargetCollisionFinder}
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    (hH : ComputableInPolyTime (fun ⟨n, k, msg⟩ => H n k msg)
      (encPair encUnary (encPair encBits encBits)) encBits)
    (hvalid : ComputableInPolyTime (fun ⟨n, msg⟩ => valid n msg)
      (encPair encUnary encBits) encBool)
    (ha : adversary.IsPPT) :
    IsPPT encBool (fun n _ => targetCollisionGame keyLen H valid adversary n) :=
  ((isPPTOn_targetCollisionGame hkeyLen hH hvalid ha).preprocess
    (ComputableInPolyTime.fst _ _)).isPPT

/-- Target collision resistance (universal one-wayness) of `H` with key-length schedule `keyLen` on
`valid` against every uniform strict PPT `TargetCollisionFinder` ([NaorYung1989], Section 2;
[BonehShoup2023], Section 8.11.2, Definition 8.7; [Goldreich2004], Section 6.4.3). -/
@[expose]
def TargetCollisionResistantOn
    (keyLen : ℕ → ℕ) (H : ℕ → List Bool → List Bool → List Bool)
    (valid : ℕ → List Bool → Bool) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (targetCollisionGame keyLen H valid adversary n))
    (fun _ _ => PMF.pure false)
    TargetCollisionFinder.IsPPT

/-- Unrestricted target collision resistance on all bit strings `List Bool`. -/
abbrev TargetCollisionResistant
    (keyLen : ℕ → ℕ) (H : ℕ → List Bool → List Bool → List Bool) : Prop :=
  TargetCollisionResistantOn keyLen H (fun _ _ => true)

/-- Target collision resistance gives negligible success probability in `targetCollisionGame` for
every strict PPT `TargetCollisionFinder`. -/
theorem TargetCollisionResistantOn.negligible
    {keyLen : ℕ → ℕ} {H : ℕ → List Bool → List Bool → List Bool}
    {valid : ℕ → List Bool → Bool}
    (h : TargetCollisionResistantOn keyLen H valid)
    (adversary : TargetCollisionFinder) (hPPT : adversary.IsPPT) :
    Negligible
      (fun n => Game.succProbability
        (ProbComp.eval (targetCollisionGame keyLen H valid adversary n))) := by
  simpa only [Game.advantage_pure_false] using h adversary hPPT

/-- Establish `TargetCollisionResistantOn` by bounding every strict PPT adversary's success
probability. -/
theorem TargetCollisionResistantOn.of_negligible
    {keyLen : ℕ → ℕ} {H : ℕ → List Bool → List Bool → List Bool}
    {valid : ℕ → List Bool → Bool}
    (h : ∀ adversary : TargetCollisionFinder, adversary.IsPPT →
      Negligible
        (fun n => Game.succProbability
          (ProbComp.eval (targetCollisionGame keyLen H valid adversary n)))) :
    TargetCollisionResistantOn keyLen H valid := by
  intro adversary hPPT
  simpa only [Game.advantage_pure_false] using h adversary hPPT

/-- Restricting the valid input domain preserves target collision resistance. -/
theorem TargetCollisionResistantOn.mono
    {keyLen : ℕ → ℕ} {H : ℕ → List Bool → List Bool → List Bool}
    {valid₁ valid₂ : ℕ → List Bool → Bool}
    (hTCR : TargetCollisionResistantOn keyLen H valid₂)
    (hsub : ∀ᶠ n in Filter.atTop, ∀ m, valid₁ n m = true → valid₂ n m = true) :
    TargetCollisionResistantOn keyLen H valid₁ := by
  apply TargetCollisionResistantOn.of_negligible
  intro adversary hadversary
  refine negligible_of_eventually_le (hTCR.negligible adversary hadversary) ?_
  filter_upwards [hsub] with n hn
  unfold Game.succProbability
  apply ENNReal.toNNReal_mono (PMF.apply_ne_top _ _)
  simp only [targetCollisionGame, ProbComp.eval_bind, ProbComp.eval_pure]
  apply PMF.bind_apply_mono_on_support; intro choice _
  apply PMF.bind_apply_mono_on_support; intro k _
  apply PMF.bind_apply_mono_on_support; intro m₁ _
  cases hcol : isCollision (H n) valid₁ n k choice.1 m₁
  · simp only [PMF.pure_apply, Bool.true_eq_false, ↓reduceIte, zero_le]
  · obtain ⟨h1, h2, hne, hh⟩ := isCollision_eq_true_iff.mp hcol
    rw [isCollision_eq_true_iff.mpr ⟨hn choice.1 h1, hn m₁ h2, hne, hh⟩]

/-- **Finding target collisions with probability bounded away from zero refutes
`TargetCollisionResistantOn`**: a strict PPT adversary whose success probability is at least a fixed
`c > 0` at every security parameter. -/
theorem not_targetCollisionResistantOn_of_le_succProbability
    {keyLen : ℕ → ℕ} {H : ℕ → List Bool → List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} {c : ℝ≥0} (hc : c ≠ 0)
    (adversary : TargetCollisionFinder) (hPPT : adversary.IsPPT)
    (h : ∀ n, c ≤ Game.succProbability
      (ProbComp.eval (targetCollisionGame keyLen H valid adversary n))) :
    ¬ TargetCollisionResistantOn keyLen H valid :=
  fun hTCR => not_negligible_const hc (negligible_of_le (hTCR.negligible adversary hPPT) h)

/-- **Full collision resistance implies target collision resistance**: running both stages of a
`TargetCollisionFinder` inside a single-stage `CollisionFinder` produces the exact same game
distribution, since `adversary.choose n` is independent of `BitString.sampleList n`. -/
theorem CollisionResistantOn.targetCollisionResistantOn
    {H : List Bool → List Bool → List Bool} {valid : ℕ → List Bool → Bool}
    (hCR : CollisionResistantOn H valid) :
    TargetCollisionResistantOn id (fun _ k msg => H k msg) valid := by
  apply TargetCollisionResistantOn.of_negligible
  intro adversary hadversary
  let colFinder : CollisionFinder := fun n k => do
    let choice ← adversary.choose n
    let m₁ ← adversary.find n choice.2 k
    return (choice.1, m₁)
  have hcolPPT : IsPPT (encPair encBits encBits) colFinder := by
    let E1 := encPair (encPair encUnary encBits) (encPair encBits encBits)
    have hq := ComputableTidilyInPolyTime.id' (encIn := E1)
    have hr := ComputableTidilyInPolyTime.id' (encIn := encPair E1 encBits)
    exact (hadversary.choose.preprocess (ComputableInPolyTime.fst _ _)).bind_with
      ((hadversary.find.preprocess
        (of_tidy_congr (hq.fst'.fst'.prod (hq.snd'.snd'.prod hq.fst'.snd')) fun _ => rfl)).bind_with
        (tidy_congr (hr.fst'.snd'.fst'.prod hr.snd') fun _ => rfl).isPPTOn)
  have heq (n : ℕ) :
      ProbComp.eval (targetCollisionGame id (fun _ k msg => H k msg) valid adversary n) =
        ProbComp.eval (collisionGame H valid colFinder n) := by
    simp only [targetCollisionGame, collisionGame, colFinder, id_eq, ProbComp.eval_bind,
      ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
    exact PMF.bind_comm _ _ _
  simpa only [heq] using hCR.negligible colFinder hcolPPT

/-! ### Bundled keyed compression and hash families -/

/-- A uniform keyed `2 * blockLen n → blockLen n` compression family with plain polynomial-time key
length, block length, and evaluation, satisfying `n ≤ blockLen n` so `n`-bit lengths embed
injectively into `blockLen n`-bit blocks. -/
structure KeyedCompressionFamily where
  /-- Key bit-length at security parameter `n`. -/
  keyLen : ℕ → ℕ
  /-- Output (and half-input) block bit-length at security parameter `n`. -/
  blockLen : ℕ → ℕ
  /-- Keyed compression evaluator `eval n k x`. -/
  eval : ℕ → List Bool → List Bool → List Bool
  /-- Key length is computable in plain polynomial time from unary `n`. -/
  keyLen_polyTime : ComputableInPolyTime keyLen encUnary encUnary
  /-- Block length is computable in plain polynomial time from unary `n`. -/
  blockLen_polyTime : ComputableInPolyTime blockLen encUnary encUnary
  /-- Compression is computable in plain polynomial time on `(1^n, k, x)`. -/
  polyTime : ComputableInPolyTime
    (fun ⟨n, k, x⟩ => eval n k x)
    (encPair encUnary (encPair encBits encBits)) encBits
  /-- Block length is at least `n` at security parameter `n`. -/
  le_blockLen : ∀ n, n ≤ blockLen n
  /-- Compressing a `2 * blockLen n`-bit input under a `keyLen n`-bit key produces a
  `blockLen n`-bit output. -/
  length_eq : ∀ n k x, k.length = keyLen n → x.length = 2 * blockLen n →
    (eval n k x).length = blockLen n

namespace KeyedCompressionFamily

attribute [program_certificate] keyLen_polyTime blockLen_polyTime polyTime

/-- Valid `2 * C.blockLen n`-bit compression inputs for `C` at security parameter `n`. -/
@[expose]
def validInput (C : KeyedCompressionFamily) (n : ℕ) (x : List Bool) : Bool :=
  x.length == 2 * C.blockLen n

@[simp]
theorem validInput_eq_true_iff (C : KeyedCompressionFamily) {n : ℕ} {x : List Bool} :
    C.validInput n x = true ↔ x.length = 2 * C.blockLen n :=
  beq_iff_eq

/-- Testing `C.validInput` is computable in plain polynomial time. -/
@[program_certificate]
theorem computableInPolyTime_validInput (C : KeyedCompressionFamily) :
    ComputableInPolyTime (fun ⟨n, x⟩ => C.validInput n x)
      (encPair encUnary encBits) encBool := by
  have hp := ComputableTidilyInPolyTime.id' (encIn := encPair encUnary encBits)
  exact of_tidy_congr (ComputableTidilyInPolyTime.unary_beq
    (ComputableTidilyInPolyTime.length_bits.comp hp.snd')
    (ComputableTidilyInPolyTime.unary_mul.comp
      ((ComputableTidilyInPolyTime.const 2).prod (C.blockLen_polyTime.tidy.comp hp.fst'))))
    fun _ => rfl

/-- Target collision resistance (UOWHF compression security) of `C` on `2 * C.blockLen n`-bit
inputs. -/
@[expose]
def TargetCollisionResistant (C : KeyedCompressionFamily) : Prop :=
  TargetCollisionResistantOn C.keyLen C.eval C.validInput

end KeyedCompressionFamily

/-- A uniform keyed hash family on arbitrary-length bit strings `List Bool`, with plain
polynomial-time key length, digest length, and evaluation, satisfying `n ≤ digestLen n`. -/
structure KeyedHashFamily where
  /-- Key bit-length at security parameter `n`. -/
  keyLen : ℕ → ℕ
  /-- Digest bit-length at security parameter `n`. -/
  digestLen : ℕ → ℕ
  /-- Keyed hash evaluator `eval n k msg`. -/
  eval : ℕ → List Bool → List Bool → List Bool
  /-- Key length is computable in plain polynomial time from unary `n`. -/
  keyLen_polyTime : ComputableInPolyTime keyLen encUnary encUnary
  /-- Digest length is computable in plain polynomial time from unary `n`. -/
  digestLen_polyTime : ComputableInPolyTime digestLen encUnary encUnary
  /-- Hashing is computable in plain polynomial time on `(1^n, k, msg)`. -/
  polyTime : ComputableInPolyTime
    (fun ⟨n, k, msg⟩ => eval n k msg)
    (encPair encUnary (encPair encBits encBits)) encBits
  /-- Digest length is at least `n` at security parameter `n`. -/
  le_digestLen : ∀ n, n ≤ digestLen n
  /-- Hashing any message under a `keyLen n`-bit key produces a `digestLen n`-bit digest. -/
  length_eq : ∀ n k msg, k.length = keyLen n → (eval n k msg).length = digestLen n

namespace KeyedHashFamily

attribute [program_certificate] keyLen_polyTime digestLen_polyTime polyTime

/-- Unrestricted target collision resistance (universal one-wayness) of `H` on all `List Bool`. -/
@[expose]
def TargetCollisionResistant (H : KeyedHashFamily) : Prop :=
  Cslib.Crypto.TargetCollisionResistant H.keyLen H.eval

end KeyedHashFamily

/-- View a `2n → n` collision-resistant `CompressionFamily` as a `KeyedCompressionFamily` with
`keyLen = id` and `blockLen = id`. -/
@[expose]
def CompressionFamily.toKeyedCompressionFamily
    {h : List Bool → List Bool → List Bool} (hh : CompressionFamily h) :
    KeyedCompressionFamily where
  keyLen := id
  blockLen := id
  eval := fun _ k x => h k x
  keyLen_polyTime := ComputableInPolyTime.id'
  blockLen_polyTime := ComputableInPolyTime.id'
  polyTime := hh.polyTime.comp (ComputableInPolyTime.snd _ _)
  le_blockLen := fun _ => le_rfl
  length_eq := fun _ k x hk hx => (hh.length_eq k x (by rw [id_eq] at hk hx; omega)).trans hk

/-- Every `CompressionFamily` is target collision-resistant on `2n`-bit inputs. -/
theorem CompressionFamily.targetCollisionResistant_toKeyedCompressionFamily
    {h : List Bool → List Bool → List Bool} (hh : CompressionFamily h) :
    hh.toKeyedCompressionFamily.TargetCollisionResistant :=
  hh.collisionResistant.targetCollisionResistantOn

/-- View an unrestricted `HashFamily` as a `KeyedHashFamily` with `keyLen = id` and
`digestLen = id`. -/
@[expose]
def HashFamily.toKeyedHashFamily
    {H : List Bool → List Bool → List Bool} (hH : HashFamily H) :
    KeyedHashFamily where
  keyLen := id
  digestLen := id
  eval := fun _ k msg => H k msg
  keyLen_polyTime := ComputableInPolyTime.id'
  digestLen_polyTime := ComputableInPolyTime.id'
  polyTime := hH.polyTime.comp (ComputableInPolyTime.snd _ _)
  le_digestLen := fun _ => le_rfl
  length_eq := fun _ k msg hk => (hH.length_eq k msg).trans hk

/-- Every `HashFamily` is unrestrictedly target collision-resistant on `List Bool`. -/
theorem HashFamily.targetCollisionResistant_toKeyedHashFamily
    {H : List Bool → List Bool → List Bool} (hH : HashFamily H) :
    hH.toKeyedHashFamily.TargetCollisionResistant :=
  hH.collisionResistant.targetCollisionResistantOn

/-! ### Level-keyed binary-tree + length-block domain extension -/

/-- Encode `msg` into a nonempty list of `M`-bit leaf blocks: `[0^M]` when `msg` is empty, and one
`M`-bit block `padOrTake M [b]` (`b :: 0^{M-1}` for `M ≥ 1`) per bit `b` of `msg` otherwise. -/
@[expose]
def uowhfLeaves (M : ℕ) (msg : List Bool) : List (List Bool) :=
  if msg.isEmpty then [List.replicate M false]
  else (List.range msg.length).map (fun i => padOrTake M [msg.getD i false])

theorem uowhfLeaves_ne_nil (M : ℕ) (msg : List Bool) : uowhfLeaves M msg ≠ [] := by
  unfold uowhfLeaves
  cases msg <;> simp only [List.isEmpty_nil, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
    ne_eq, List.cons_ne_self, not_false_eq_true, List.map_eq_nil_iff, List.range_eq_nil,
    List.length_cons, Nat.add_one_ne_zero]

theorem length_uowhfLeaves (M : ℕ) (msg : List Bool) :
    (uowhfLeaves M msg).length = max 1 msg.length := by
  unfold uowhfLeaves
  cases msg <;> simp only [List.isEmpty_nil, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
    List.length_cons, List.length_nil, List.length_map, List.length_range] <;> omega

theorem length_mem_uowhfLeaves {M : ℕ} {msg : List Bool} {w : List Bool}
    (hw : w ∈ uowhfLeaves M msg) : w.length = M := by
  unfold uowhfLeaves at hw
  split_ifs at hw
  · rw [List.mem_singleton.mp hw]; exact List.length_replicate
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hw; exact length_padOrTake M _

theorem uowhfLeaves_injective_of_length_eq {M : ℕ} (hM : 1 ≤ M) {m₀ m₁ : List Bool}
    (hlen : m₀.length = m₁.length) (heq : uowhfLeaves M m₀ = uowhfLeaves M m₁) :
    m₀ = m₁ := by
  cases m₀ with
  | nil => exact (List.length_eq_zero_iff.mp hlen.symm).symm
  | cons b₀ bs₀ =>
    cases m₁ with
    | nil => cases hlen
    | cons b₁ bs₁ =>
      refine List.ext_getElem hlen fun idx h₀ h₁ => ?_
      simp only [uowhfLeaves, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, hlen] at heq
      have hr : idx < (List.range (b₁ :: bs₁).length).length := by
        simpa only [List.length_range] using h₁
      have hcell : padOrTake M [(b₀ :: bs₀).getD idx false] =
          padOrTake M [(b₁ :: bs₁).getD idx false] := by
        simpa only [List.getElem?_map, List.getElem?_eq_getElem hr, List.getElem_range,
          Option.map_some, Option.some.injEq] using congrArg (fun l => l[idx]?) heq
      obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      simpa only [padOrTake, List.singleton_append, List.take_succ_cons, List.headD_cons,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₀,
        List.getElem?_eq_getElem h₁, Option.getD_some] using
        congrArg (fun w => w.headD false) hcell

@[program_certificate]
theorem computableInPolyTime_uowhfLeaves :
    ComputableInPolyTime (fun ⟨M, msg⟩ => uowhfLeaves M msg)
      (encPair encUnary encBits) (encList encBits) := by
  have hM := ComputableTidilyInPolyTime.fst encUnary encBits
  have hmsg := ComputableTidilyInPolyTime.snd encUnary encBits
  have hp := ComputableTidilyInPolyTime.id' (encIn := encPair (encPair encUnary encBits) encUnary)
  have hbit := ComputableTidilyInPolyTime.bitsGetDWithInput (hmsg.comp hp.fst') hp.snd' false
  have hcell := computableInPolyTime_padOrTake.tidy.comp
    ((hM.comp hp.fst').prod (ComputableTidilyInPolyTime.bitsCons hbit (.const [])))
  exact of_tidy_congr (ComputableTidilyInPolyTime.ite'
    (ComputableTidilyInPolyTime.bitsIsEmpty.comp hmsg)
    (ComputableTidilyInPolyTime.cons'
      ((ComputableTidilyInPolyTime.bitsReplicate false).comp hM) (.const []))
    (ComputableTidilyInPolyTime.mapWithInput
      (ComputableTidilyInPolyTime.range.comp (ComputableTidilyInPolyTime.length_bits.comp hmsg))
      hcell)) fun _ => rfl

/-- Concatenate the `2 * j`-th and `(2 * j + 1)`-st blocks of `level`, normalizing each to exact
width `M` via `padOrTake M` (defaulting missing odd-tail blocks to `0^M`). -/
@[expose]
def uowhfPairInput (M : ℕ) (level : List (List Bool)) (j : ℕ) : List Bool :=
  padOrTake M (level.getD (2 * j) []) ++ padOrTake M (level.getD (2 * j + 1) [])

@[simp]
theorem length_uowhfPairInput (M : ℕ) (level : List (List Bool)) (j : ℕ) :
    (uowhfPairInput M level j).length = 2 * M := by
  simp only [uowhfPairInput, List.length_append, length_padOrTake]; omega

@[program_certificate, fun_prop]
theorem computableInPolyTime_uowhfPairInput
    {γ : Type} {encIn : γ ↪ List Bool}
    {M j : γ → ℕ} {level : γ → List (List Bool)}
    (hM : ComputableInPolyTime M encIn encUnary)
    (hlevel : ComputableInPolyTime level encIn (encList encBits))
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun a => uowhfPairInput (M a) (level a) (j a)) encIn encBits := by
  have hpad := computableInPolyTime_padOrTake.tidy
  have hget := ComputableTidilyInPolyTime.listGetD (encA := encBits) (encL := encList encBits) []
  have h2j := ComputableTidilyInPolyTime.unary_mul.comp
    ((ComputableTidilyInPolyTime.const 2).prod hj.tidy)
  have h2j1 := ComputableTidilyInPolyTime.unary_add.comp (h2j.prod (.const 1))
  exact of_tidy_congr (ComputableTidilyInPolyTime.bitsAppend
    (hpad.comp (hM.tidy.prod (hget.comp (hlevel.tidy.prod h2j))))
    (hpad.comp (hM.tidy.prod (hget.comp (hlevel.tidy.prod h2j1))))) fun _ => rfl

/-- Compress one level of the binary hash tree under subkey `k`: keep `level` unchanged if it has at
most one block, and otherwise compress each adjacent pair into an `M`-bit block. -/
@[expose]
def uowhfTreeStep (h : ℕ → List Bool → List Bool → List Bool)
    (n κ M : ℕ) (k : List Bool) (level : List (List Bool)) : List (List Bool) :=
  if level.length ≤ 1 then level
  else (List.range ((level.length + 1) / 2)).map (fun j =>
    padOrTake M (h n (padOrTake κ k) (uowhfPairInput M level j)))

theorem length_uowhfTreeStep (h : ℕ → List Bool → List Bool → List Bool)
    (n κ M : ℕ) (k : List Bool) (level : List (List Bool)) :
    (uowhfTreeStep h n κ M k level).length =
      if level.length ≤ 1 then level.length else (level.length + 1) / 2 := by
  unfold uowhfTreeStep; split_ifs <;> simp only [List.length_map, List.length_range]

private theorem length_uowhfTreeStep_le (h : ℕ → List Bool → List Bool → List Bool)
    (n κ M : ℕ) (k : List Bool) (level : List (List Bool)) :
    (uowhfTreeStep h n κ M k level).length ≤ level.length := by
  rw [length_uowhfTreeStep]; split_ifs <;> omega

private theorem uowhfTreeStep_ne_nil (h : ℕ → List Bool → List Bool → List Bool)
    (n κ M : ℕ) (k : List Bool) {level : List (List Bool)} (hne : level ≠ []) :
    uowhfTreeStep h n κ M k level ≠ [] := by
  have hpos : 1 ≤ level.length := List.length_pos_iff.mpr hne
  rw [← List.length_pos_iff, length_uowhfTreeStep]; split_ifs <;> omega

private theorem length_mem_uowhfTreeStep {h : ℕ → List Bool → List Bool → List Bool}
    {n κ M : ℕ} {k : List Bool} {level : List (List Bool)}
    (hblocks : ∀ w ∈ level, w.length = M) {w : List Bool}
    (hw : w ∈ uowhfTreeStep h n κ M k level) : w.length = M := by
  unfold uowhfTreeStep at hw
  split_ifs at hw
  · exact hblocks w hw
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hw; exact length_padOrTake M _

private theorem length_mem_uowhfTreeStep_le {h : ℕ → List Bool → List Bool → List Bool}
    {n κ M B : ℕ} (hM : M ≤ B) {k : List Bool} {level : List (List Bool)}
    (hblocks : ∀ w ∈ level, w.length ≤ B) {w : List Bool}
    (hw : w ∈ uowhfTreeStep h n κ M k level) : w.length ≤ B := by
  unfold uowhfTreeStep at hw
  split_ifs at hw
  · exact hblocks w hw
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hw; rw [length_padOrTake]; exact hM

/-- Fold `uowhfTreeStep` across a list of level subkeys `keys`. -/
@[expose]
def uowhfTreeLevels (h : ℕ → List Bool → List Bool → List Bool)
    (n κ M : ℕ) (keys : List (List Bool)) (init : List (List Bool)) : List (List Bool) :=
  keys.foldl (fun level k => uowhfTreeStep h n κ M k level) init

@[simp]
theorem uowhfTreeLevels_nil (h : ℕ → List Bool → List Bool → List Bool)
    (n κ M : ℕ) (init : List (List Bool)) :
    uowhfTreeLevels h n κ M [] init = init := rfl

theorem uowhfTreeLevels_append (h : ℕ → List Bool → List Bool → List Bool)
    (n κ M : ℕ) (ks₁ ks₂ : List (List Bool)) (init : List (List Bool)) :
    uowhfTreeLevels h n κ M (ks₁ ++ ks₂) init =
      uowhfTreeLevels h n κ M ks₂ (uowhfTreeLevels h n κ M ks₁ init) :=
  List.foldl_append

private theorem length_uowhfTreeLevels_le (h : ℕ → List Bool → List Bool → List Bool)
    (n κ M : ℕ) (keys : List (List Bool)) (init : List (List Bool)) :
    (uowhfTreeLevels h n κ M keys init).length ≤ init.length := by
  induction keys generalizing init with
  | nil => exact le_rfl
  | cons k ks ih =>
    exact (ih (uowhfTreeStep h n κ M k init)).trans (length_uowhfTreeStep_le h n κ M k init)

private theorem length_mem_uowhfTreeLevels {h : ℕ → List Bool → List Bool → List Bool}
    {n κ M : ℕ} (keys : List (List Bool)) {init : List (List Bool)}
    (hinit : ∀ w ∈ init, w.length = M) {w : List Bool}
    (hw : w ∈ uowhfTreeLevels h n κ M keys init) : w.length = M := by
  induction keys generalizing init with
  | nil => exact hinit w hw
  | cons k ks ih => exact ih (fun _ => length_mem_uowhfTreeStep hinit) hw

private theorem length_mem_uowhfTreeLevels_le {h : ℕ → List Bool → List Bool → List Bool}
    {n κ M B : ℕ} (hM : M ≤ B) (keys : List (List Bool)) {init : List (List Bool)}
    (hinit : ∀ w ∈ init, w.length ≤ B) {w : List Bool}
    (hw : w ∈ uowhfTreeLevels h n κ M keys init) : w.length ≤ B := by
  induction keys generalizing init with
  | nil => exact hinit w hw
  | cons k ks ih => exact ih (fun _ => length_mem_uowhfTreeStep_le hM hinit) hw

private theorem length_uowhfTreeLevels_eq_of_length_eq (h : ℕ → List Bool → List Bool → List Bool)
    (n κ M : ℕ) (keys : List (List Bool)) {init₀ init₁ : List (List Bool)}
    (hlen : init₀.length = init₁.length) :
    (uowhfTreeLevels h n κ M keys init₀).length =
      (uowhfTreeLevels h n κ M keys init₁).length := by
  induction keys generalizing init₀ init₁ with
  | nil => exact hlen
  | cons k ks ih => exact ih (by rw [length_uowhfTreeStep, length_uowhfTreeStep, hlen])

/-- After `keys.length` tree-compression levels, any nonempty leaf list of length at most
`2 ^ keys.length` collapses to a single root block. -/
theorem length_uowhfTreeLevels_eq_one (h : ℕ → List Bool → List Bool → List Bool)
    (n κ M : ℕ) (keys : List (List Bool)) {init : List (List Bool)}
    (hne : init ≠ []) (hle : init.length ≤ 2 ^ keys.length) :
    (uowhfTreeLevels h n κ M keys init).length = 1 := by
  induction keys generalizing init with
  | nil =>
    simp only [List.length_nil, Nat.pow_zero] at hle
    exact le_antisymm hle (List.length_pos_iff.mpr hne)
  | cons k ks ih =>
    refine ih (uowhfTreeStep_ne_nil h n κ M k hne) ?_
    simp only [List.length_cons, Nat.pow_succ] at hle
    rw [length_uowhfTreeStep]
    split_ifs with hle1
    · exact hle1.trans Nat.one_le_two_pow
    · omega

/-- Folding `uowhfTreeStep` is computable in plain polynomial time whenever `h` and the parameters
are computable in plain polynomial time. -/
@[program_certificate, fun_prop]
theorem computableInPolyTime_uowhfTreeLevels
    {h : ℕ → List Bool → List Bool → List Bool}
    (hh : ComputableInPolyTime (fun ⟨n, k, x⟩ => h n k x)
      (encPair encUnary (encPair encBits encBits)) encBits)
    {γ : Type} {encIn : γ ↪ List Bool}
    {n κ M : γ → ℕ} {keys init : γ → List (List Bool)}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hκ : ComputableInPolyTime κ encIn encUnary)
    (hM : ComputableInPolyTime M encIn encUnary)
    (hkeys : ComputableInPolyTime keys encIn (encList encBits))
    (hinit : ComputableInPolyTime init encIn (encList encBits)) :
    ComputableInPolyTime
      (fun a => uowhfTreeLevels h (n a) (κ a) (M a) (keys a) (init a))
      encIn (encList encBits) := by
  let EPar := encPair encUnary (encPair encUnary encUnary)
  let EStep := encPair (encPair EPar (encList encBits)) encBits
  have hp := ComputableTidilyInPolyTime.id' (encIn := EStep)
  have hlev := hp.fst'.snd'
  have hlen := (ComputableTidilyInPolyTime.length_list encBits).comp hlev
  have hhalf := ComputableTidilyInPolyTime.unary_div.comp
    ((ComputableTidilyInPolyTime.unary_add.comp (hlen.prod (.const 1))).prod (.const 2))
  have hq := ComputableTidilyInPolyTime.id' (encIn := encPair EStep encUnary)
  have hpad := computableInPolyTime_padOrTake.tidy
  have hk_pad := hpad.comp ((hp.fst'.fst'.snd'.fst'.comp hq.fst').prod (hp.snd'.comp hq.fst'))
  have hpair := (computableInPolyTime_uowhfPairInput
    (.of_tidy (hp.fst'.fst'.snd'.snd'.comp hq.fst'))
    (.of_tidy (hlev.comp hq.fst')) (.of_tidy hq.snd')).tidy
  have hcell := hpad.comp ((hp.fst'.fst'.snd'.snd'.comp hq.fst').prod
    (hh.tidy.comp ((hp.fst'.fst'.fst'.comp hq.fst').prod (hk_pad.prod hpair))))
  have hstep : ComputableTidilyInPolyTime
      (fun q : ((ℕ × ℕ × ℕ) × List (List Bool)) × List Bool =>
        uowhfTreeStep h q.1.1.1 q.1.1.2.1 q.1.1.2.2 q.2 q.1.2)
      EStep (encList encBits) :=
    tidy_congr (ComputableTidilyInPolyTime.ite_decide (hlen.unary_le' (.const 1)) hlev
      (ComputableTidilyInPolyTime.mapWithInput
        (ComputableTidilyInPolyTime.range.comp hhalf) hcell)) fun _ => rfl
  let initLen (a : γ) : ℕ := (encList encBits (init a)).length
  let elemCap (a : γ) : ℕ := M a + initLen a
  have hM_pb : PolyBounded (fun a => (encIn a).length) M := by
    simpa only [encUnary_apply, List.length_replicate] using hM.tidy.polyBounded_length
  have hpoly : PolyBounded (fun a => (encIn a).length) (fun a => initLen a * (2 * elemCap a + 1)) :=
    hinit.tidy.polyBounded_length.mul
      (((PolyBounded.const 2).mul (hM_pb.add hinit.tidy.polyBounded_length)).add (.const 1))
  refine .of_tidy (ComputableTidilyInPolyTime.foldlWith
    (encA := encBits) (encL := encList encBits) (encP := EPar) (encB := encList encBits)
    (par := fun a => (n a, κ a, M a))
    (step := fun par level k => uowhfTreeStep h par.1 par.2.1 par.2.2 k level)
    (hn.tidy.prod (hκ.tidy.prod hM.tidy)) hkeys.tidy hinit.tidy hstep hpoly fun a i _ => ?_)
  let state := uowhfTreeLevels h (n a) (κ a) (M a) ((keys a).take i) (init a)
  refine (length_encList_le encBits state fun w hw =>
    length_mem_uowhfTreeLevels_le (Nat.le_add_right (M a) (initLen a)) ((keys a).take i)
      (fun u hu => (SizedListEncoding.length_elem_le (encA := encBits) (encL := encList encBits)
        (init a) u hu).trans (Nat.le_add_left (initLen a) (M a))) hw).trans
    (Nat.mul_le_mul_right (2 * elemCap a + 1)
      ((length_uowhfTreeLevels_le h (n a) (κ a) (M a) ((keys a).take i) (init a)).trans
        (SizedListEncoding.length_le (encA := encBits) (encL := encList encBits) (init a))))

/-- **Level-keyed binary-tree + length-block hash**: total fixed-depth adaptation of level-keyed
tree hashing ([NaorYung1989], 1995 revision, Section 2.3; [Goldreich2004], Section 6.4.3.2, June
2003 draft Constructions 6.4.24 and 6.4.26; cf. [BonehShoup2023], Section 8.11.3, p. 340). Split `K`
into `n` level subkeys `k_0, ..., k_{n-1}` plus one final subkey `k_n` of width `keyLen n`, fold
`uowhfTreeStep` across `k_0, ..., k_{n-1}` starting from the one-bit-per-leaf encoding
`uowhfLeaves (blockLen n) msg`, take `root := padOrTake (blockLen n) (top.headD [])`, and compress
`root ++ BitString.lowBits (blockLen n) msg.length` (`msg.length mod 2^{blockLen n}`) under `k_n`.

At fixed `n`, messages with `msg.length > 2 ^ n` leave multiple blocks in `top` and `top.headD []`
discards the extra roots; for `msg.length < 2 ^ n ≤ 2 ^ blockLen n`, `top` is a singleton and
`lowBits` records `msg.length` injectively. -/
@[expose]
def uowhfTreeHash (h : ℕ → List Bool → List Bool → List Bool)
    (keyLen blockLen : ℕ → ℕ) (n : ℕ) (K msg : List Bool) : List Bool :=
  let κ := keyLen n
  let M := blockLen n
  let treeKeys := BitString.listRows n κ K
  let finalKey := BitString.listRow κ n K
  let top := uowhfTreeLevels h n κ M treeKeys (uowhfLeaves M msg)
  let root := padOrTake M (top.headD [])
  padOrTake M (h n finalKey (root ++ BitString.lowBits M msg.length))

@[simp]
theorem length_uowhfTreeHash (h : ℕ → List Bool → List Bool → List Bool)
    (keyLen blockLen : ℕ → ℕ) (n : ℕ) (K msg : List Bool) :
    (uowhfTreeHash h keyLen blockLen n K msg).length = blockLen n :=
  length_padOrTake (blockLen n) _

/-- Evaluating `uowhfTreeHash` is computable in plain polynomial time on `(1^n, K, msg)`. -/
@[program_certificate]
theorem computableInPolyTime_uowhfTreeHash
    {h : ℕ → List Bool → List Bool → List Bool} {keyLen blockLen : ℕ → ℕ}
    (hh : ComputableInPolyTime (fun ⟨n, k, x⟩ => h n k x)
      (encPair encUnary (encPair encBits encBits)) encBits)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    (hblockLen : ComputableInPolyTime blockLen encUnary encUnary) :
    ComputableInPolyTime
      (fun ⟨n, K, msg⟩ => uowhfTreeHash h keyLen blockLen n K msg)
      (encPair encUnary (encPair encBits encBits)) encBits := by
  have hp := ComputableTidilyInPolyTime.id' (encIn := encPair encUnary (encPair encBits encBits))
  have hn := hp.fst'; have hK := hp.snd'.fst'; have hmsg := hp.snd'.snd'
  have hκ := hkeyLen.tidy.comp hn; have hM := hblockLen.tidy.comp hn
  have hpad := computableInPolyTime_padOrTake.tidy
  have htop := (computableInPolyTime_uowhfTreeLevels hh (.of_tidy hn) (.of_tidy hκ) (.of_tidy hM)
    (.of_tidy (ComputableTidilyInPolyTime.bitsRowsWithInput hn hκ hK))
    (computableInPolyTime_uowhfLeaves.comp (.of_tidy (hM.prod hmsg)))).tidy
  have hroot := hpad.comp (hM.prod
    ((ComputableTidilyInPolyTime.headD (encA := encBits) (encL := encList encBits) []).comp htop))
  have hlow := ComputableTidilyInPolyTime.bitsLow hM
    (ComputableTidilyInPolyTime.unary_to_binary.comp
      (ComputableTidilyInPolyTime.length_bits.comp hmsg))
  exact of_tidy_congr (hpad.comp (hM.prod (hh.tidy.comp
    (hn.prod ((ComputableTidilyInPolyTime.bitsRowWithInput hκ hn hK).prod
      (ComputableTidilyInPolyTime.bitsAppend hroot hlow)))))) fun _ => rfl

/-- Candidate `2 * M`-bit compression input fed to subkey `i` (`0 ≤ i ≤ n`) at pair index `j`
during evaluation of `uowhfTreeHash` on `msg`, using only the prefix `front` containing subkeys
`< i`. -/
@[expose]
def uowhfCandidateInput (h : ℕ → List Bool → List Bool → List Bool)
    (n κ M i j : ℕ) (front msg : List Bool) : List Bool :=
  if i < n then
    let level := uowhfTreeLevels h n κ M (BitString.listRows i κ front) (uowhfLeaves M msg)
    uowhfPairInput M level j
  else
    let top := uowhfTreeLevels h n κ M (BitString.listRows n κ front) (uowhfLeaves M msg)
    padOrTake M (top.headD []) ++ BitString.lowBits M msg.length

@[simp]
theorem length_uowhfCandidateInput (h : ℕ → List Bool → List Bool → List Bool)
    (n κ M i j : ℕ) (front msg : List Bool) :
    (uowhfCandidateInput h n κ M i j front msg).length = 2 * M := by
  unfold uowhfCandidateInput
  split_ifs
  · exact length_uowhfPairInput M _ j
  · simp only [List.length_append, length_padOrTake, BitString.length_lowBits]; omega

@[program_certificate, fun_prop]
theorem computableInPolyTime_uowhfCandidateInput
    {h : ℕ → List Bool → List Bool → List Bool}
    (hh : ComputableInPolyTime (fun ⟨n, k, x⟩ => h n k x)
      (encPair encUnary (encPair encBits encBits)) encBits)
    {γ : Type} {encIn : γ ↪ List Bool}
    {n κ M i j : γ → ℕ} {front msg : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hκ : ComputableInPolyTime κ encIn encUnary)
    (hM : ComputableInPolyTime M encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary)
    (hj : ComputableInPolyTime j encIn encUnary)
    (hfront : ComputableInPolyTime front encIn encBits)
    (hmsg : ComputableInPolyTime msg encIn encBits) :
    ComputableInPolyTime
      (fun a => uowhfCandidateInput h (n a) (κ a) (M a) (i a) (j a) (front a) (msg a))
      encIn encBits := by
  have hleaves := computableInPolyTime_uowhfLeaves.comp (hM.prod hmsg)
  have hlev := computableInPolyTime_uowhfTreeLevels hh hn hκ hM
    (.of_tidy (ComputableTidilyInPolyTime.bitsRowsWithInput hi.tidy hκ.tidy hfront.tidy)) hleaves
  have htop := (computableInPolyTime_uowhfTreeLevels hh hn hκ hM
    (.of_tidy (ComputableTidilyInPolyTime.bitsRowsWithInput hn.tidy hκ.tidy hfront.tidy))
    hleaves).tidy
  have hroot := computableInPolyTime_padOrTake.tidy.comp (hM.tidy.prod
    ((ComputableTidilyInPolyTime.headD (encA := encBits) (encL := encList encBits) []).comp htop))
  have hlow := ComputableTidilyInPolyTime.bitsLow hM.tidy
    (ComputableTidilyInPolyTime.unary_to_binary.comp
      (ComputableTidilyInPolyTime.length_bits.comp hmsg.tidy))
  exact of_tidy_congr (ComputableTidilyInPolyTime.ite_decide (hi.tidy.unary_lt' hn.tidy)
    (computableInPolyTime_uowhfPairInput hM hlev hj).tidy
    (ComputableTidilyInPolyTime.bitsAppend hroot hlow)) fun _ => rfl

/-! ### Deterministic tree collision witness -/

private theorem exists_step_eq_of_ne {α : Type*} (f g : ℕ → α) {n : ℕ}
    (h0 : f 0 ≠ g 0) (hn : f n = g n) :
    ∃ i < n, f i ≠ g i ∧ f (i + 1) = g (i + 1) := by
  induction n with
  | zero => exact absurd hn h0
  | succ m ih =>
    by_cases hm : f m = g m
    · obtain ⟨i, hi, hne, heq⟩ := ih hm
      exact ⟨i, by omega, hne, heq⟩
    · exact ⟨m, by omega, hm, hn⟩

private theorem listRows_succ_eq_snoc (r κ : ℕ) (K : List Bool) :
    BitString.listRows (r + 1) κ K = BitString.listRows r κ K ++ [BitString.listRow κ r K] := by
  simp only [BitString.listRows, List.range_succ, List.map_append, List.map_singleton]

private theorem listRows_take_mul_eq (i κ : ℕ) (K : List Bool) :
    BitString.listRows i κ (K.take (i * κ)) = BitString.listRows i κ K := by
  refine List.map_congr_left fun r hr =>
    List.ext_getElem (by simp only [BitString.length_listRow]) fun c hc _ => ?_
  simp only [BitString.length_listRow] at hc
  have hr_lt : r < i := List.mem_range.mp hr
  have hidx : r * κ + c < i * κ :=
    calc r * κ + c < r * κ + κ := by omega
      _ = (r + 1) * κ := by ring
      _ ≤ i * κ := Nat.mul_le_mul_right κ (by omega)
  rw [BitString.getElem_listRow hc, BitString.getElem_listRow hc]
  rcases lt_or_ge (r * κ + c) K.length with hK | hK
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hidx,
      List.getElem?_eq_getElem hK]
  · simp only [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none ((List.length_take .. ▸ Nat.min_le_right _ _).trans hK),
      List.getElem?_eq_none hK]

private theorem uowhfCandidateInput_take_eq (h : ℕ → List Bool → List Bool → List Bool)
    {n κ M i j : ℕ} (hi : i ≤ n) (K msg : List Bool) :
    uowhfCandidateInput h n κ M i j (K.take (i * κ)) msg =
      uowhfCandidateInput h n κ M i j K msg := by
  unfold uowhfCandidateInput
  split_ifs with hlt
  · rw [listRows_take_mul_eq]
  · obtain rfl : i = n := le_antisymm hi (Nat.not_lt.mp hlt)
    rw [listRows_take_mul_eq]

/-- **Deterministic node-collision extraction for `uowhfTreeHash`**: assume that `h n` maps every
`keyLen n`-bit key and `2 * blockLen n`-bit input to a `blockLen n`-bit output. Whenever two
distinct messages `m₀ ≠ m₁` of length `< 2 ^ n` (with `m₀.length ≤ B`, `1 ≤ B`, `1 ≤ n`, and
`n ≤ blockLen n`) produce the same digest under `uowhfTreeHash`, there exist a subkey index
`i ≤ n` and a pair index `j < B` whose `2 * blockLen n`-bit candidate inputs collide under
`BitString.listRow (keyLen n) i K`. -/
theorem exists_uowhfCandidateInput_collision
    {h : ℕ → List Bool → List Bool → List Bool} {keyLen blockLen : ℕ → ℕ}
    {n B : ℕ} {K m₀ m₁ : List Bool}
    (hn : 1 ≤ n) (hM_ge : n ≤ blockLen n) (hB : 1 ≤ B)
    (hm₀_B : m₀.length ≤ B) (hm₀_pow : m₀.length < 2 ^ n) (hm₁_pow : m₁.length < 2 ^ n)
    (hlen_h : ∀ k x, k.length = keyLen n → x.length = 2 * blockLen n →
      (h n k x).length = blockLen n)
    (hne : m₀ ≠ m₁)
    (hcol : uowhfTreeHash h keyLen blockLen n K m₀ = uowhfTreeHash h keyLen blockLen n K m₁) :
    ∃ i ≤ n, ∃ j < B,
      let x₀ := uowhfCandidateInput h n (keyLen n) (blockLen n) i j K m₀
      let x₁ := uowhfCandidateInput h n (keyLen n) (blockLen n) i j K m₁
      x₀ ≠ x₁ ∧
        h n (BitString.listRow (keyLen n) i K) x₀ =
          h n (BitString.listRow (keyLen n) i K) x₁ := by
  let κ := keyLen n; let M := blockLen n
  have hM_pos : 1 ≤ M := hn.trans hM_ge
  let xFinal (m : List Bool) := uowhfCandidateInput h n κ M n 0 K m
  have hxFinal_def (m : List Bool) : xFinal m =
      padOrTake M ((uowhfTreeLevels h n κ M (BitString.listRows n κ K)
        (uowhfLeaves M m)).headD []) ++ BitString.lowBits M m.length := by
    simp only [xFinal, uowhfCandidateInput, lt_self_iff_false, ↓reduceIte]
  have hhash_final (m : List Bool) :
      uowhfTreeHash h keyLen blockLen n K m = h n (BitString.listRow κ n K) (xFinal m) := by
    simp only [uowhfTreeHash, ← hxFinal_def m, κ, M]
    exact padOrTake_eq_self (hlen_h _ _ (BitString.length_listRow κ n K)
      (length_uowhfCandidateInput h n κ M n 0 K m))
  have hfinal_col : h n (BitString.listRow κ n K) (xFinal m₀) =
      h n (BitString.listRow κ n K) (xFinal m₁) :=
    (hhash_final m₀).symm.trans (hcol.trans (hhash_final m₁))
  by_cases hfinal_ne : xFinal m₀ ≠ xFinal m₁
  · exact ⟨n, le_rfl, 0, hB, hfinal_ne, hfinal_col⟩
  · push Not at hfinal_ne
    rw [hxFinal_def m₀, hxFinal_def m₁] at hfinal_ne
    obtain ⟨hroot_eq, hlow_eq⟩ := List.append_inj hfinal_ne (by simp only [length_padOrTake])
    have hpow_le : 2 ^ n ≤ 2 ^ M := Nat.pow_le_pow_right (by omega) hM_ge
    have hlen_eq : m₀.length = m₁.length := by
      have hlsb := congrArg BitString.lsbValue hlow_eq
      rwa [BitString.lsbValue_lowBits (hm₀_pow.trans_le hpow_le),
        BitString.lsbValue_lowBits (hm₁_pow.trans_le hpow_le)] at hlsb
    let L (m : List Bool) (r : ℕ) :=
      uowhfTreeLevels h n κ M (BitString.listRows r κ K) (uowhfLeaves M m)
    have hL0_ne : L m₀ 0 ≠ L m₁ 0 := by
      simp only [L, BitString.listRows, List.range_zero, List.map_nil, uowhfTreeLevels_nil]
      exact fun heq => hne (uowhfLeaves_injective_of_length_eq hM_pos hlen_eq heq)
    have htop_singleton {m : List Bool} (hm : m.length < 2 ^ n) :
        ∃ w, L m n = [w] ∧ w.length = M := by
      obtain ⟨w, hw⟩ := List.length_eq_one_iff.mp
        (length_uowhfTreeLevels_eq_one h n κ M (BitString.listRows n κ K) (uowhfLeaves_ne_nil M m)
          (by rw [BitString.length_listRows, length_uowhfLeaves]
              exact max_le Nat.one_le_two_pow hm.le))
      exact ⟨w, hw, length_mem_uowhfTreeLevels _ (fun _ => length_mem_uowhfLeaves)
        (hw ▸ List.mem_singleton_self w)⟩
    have hLn_eq : L m₀ n = L m₁ n := by
      obtain ⟨w₀, hw₀, hw₀_len⟩ := htop_singleton hm₀_pow
      obtain ⟨w₁, hw₁, hw₁_len⟩ := htop_singleton hm₁_pow
      have hpad_eq : w₀ = w₁ := by
        dsimp only [L] at hw₀ hw₁
        simpa only [hw₀, hw₁, List.headD_cons, padOrTake_eq_self hw₀_len,
          padOrTake_eq_self hw₁_len] using hroot_eq
      rw [hw₀, hw₁, hpad_eq]
    obtain ⟨i, hi_lt, hLi_ne, hLi_succ⟩ := exists_step_eq_of_ne (L m₀) (L m₁) hL0_ne hLn_eq
    have hstep_i (m : List Bool) :
        L m (i + 1) = uowhfTreeStep h n κ M (BitString.listRow κ i K) (L m i) := by
      simp only [L, listRows_succ_eq_snoc, uowhfTreeLevels_append]; rfl
    rw [hstep_i m₀, hstep_i m₁] at hLi_succ
    have hLi_len_eq : (L m₀ i).length = (L m₁ i).length :=
      length_uowhfTreeLevels_eq_of_length_eq h n κ M _ (by simp only [length_uowhfLeaves, hlen_eq])
    have hLi_len_le_B : (L m₀ i).length ≤ B :=
      (length_uowhfTreeLevels_le h n κ M _ _).trans
        ((length_uowhfLeaves M m₀).le.trans (max_le hB hm₀_B))
    have hgt1 : ¬ (L m₀ i).length ≤ 1 := fun hle1 => by
      have hle1' : (L m₁ i).length ≤ 1 := hLi_len_eq ▸ hle1
      simp only [uowhfTreeStep, hle1, hle1', ↓reduceIte] at hLi_succ
      exact hLi_ne hLi_succ
    have hmem (m : List Bool) : ∀ w ∈ L m i, w.length = M :=
      fun _ => length_mem_uowhfTreeLevels _ (fun _ => length_mem_uowhfLeaves)
    obtain ⟨idx, hidx_lt, hidx_ne⟩ : ∃ idx : ℕ, ∃ h₀ : idx < (L m₀ i).length,
        (L m₀ i)[idx]'h₀ ≠ (L m₁ i)[idx]'(hLi_len_eq ▸ h₀) := by
      by_contra! hall
      exact hLi_ne (List.ext_getElem hLi_len_eq fun idx h₀ _ => hall idx h₀)
    let j := idx / 2
    have hj_half : j < ((L m₀ i).length + 1) / 2 := by omega
    refine ⟨i, Nat.le_of_lt hi_lt, j, by omega, ?_, ?_⟩
    · simp only [uowhfCandidateInput, uowhfPairInput, hi_lt, ↓reduceIte]
      intro hpair_eq
      obtain ⟨heven, hodd⟩ := List.append_inj hpair_eq (by simp only [length_padOrTake])
      have hrefute {k : ℕ} (hk : k = idx)
          (heq : padOrTake M ((L m₀ i).getD k []) = padOrTake M ((L m₁ i).getD k [])) : False := by
        subst hk
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx_lt,
          List.getElem?_eq_getElem (hLi_len_eq ▸ hidx_lt), Option.getD_some,
          padOrTake_eq_self (hmem m₀ _ (List.getElem_mem hidx_lt)),
          padOrTake_eq_self (hmem m₁ _ (List.getElem_mem (hLi_len_eq ▸ hidx_lt)))] at heq
        exact hidx_ne heq
      rcases (show 2 * j = idx ∨ 2 * j + 1 = idx by omega) with hk | hk
      · exact hrefute hk heven
      · exact hrefute hk hodd
    · simp only [uowhfCandidateInput, hi_lt, ↓reduceIte]
      have hgt1' : ¬ (L m₁ i).length ≤ 1 := hLi_len_eq ▸ hgt1
      simp only [uowhfTreeStep, hgt1, hgt1', ↓reduceIte] at hLi_succ
      have hr₀ : j < (List.range (((L m₀ i).length + 1) / 2)).length := by
        simpa only [List.length_range] using hj_half
      have hr₁ : j < (List.range (((L m₁ i).length + 1) / 2)).length := by
        simpa only [List.length_range, ← hLi_len_eq] using hj_half
      have hj_entry := congrArg (fun l => l[j]?) hLi_succ
      simp only [List.getElem?_map, List.getElem?_eq_getElem hr₀,
        List.getElem?_eq_getElem hr₁, List.getElem_range, Option.map_some,
        Option.some.injEq, padOrTake_eq_self (BitString.length_listRow κ i K)] at hj_entry
      rwa [padOrTake_eq_self (hlen_h _ _ (BitString.length_listRow κ i K)
          (length_uowhfPairInput M (L m₀ i) j)),
        padOrTake_eq_self (hlen_h _ _ (BitString.length_listRow κ i K)
          (length_uowhfPairInput M (L m₁ i) j))] at hj_entry

/-! ### Two-stage planted-subkey reduction for `uowhfTreeHash` -/

private abbrev TreeState := Bool × ℕ × ℕ × List Bool × List Bool

private abbrev encTreeState : TreeState ↪ List Bool :=
  encPair encBool (encPair encUnary (encPair encUnary (encPair encBits encBits)))

private def treeStateDecoder : Decoder encTreeState :=
  Decoder.pair Decoder.bool
    (Decoder.pair Decoder.unary
      (Decoder.pair Decoder.unary (Decoder.pair Decoder.bits Decoder.bits)))

/-- Two-stage target-collision reduction from `uowhfTreeHash` to the underlying compression family
`h`: Stage 1 samples a dyadic slot `slot < (n + 1) * maxBlocks n` encoding `(i, j)` (`i ≤ n`,
`j < maxBlocks n`), runs `adversary.choose n`, samples `i` prefix subkeys `front` before seeing the
challenge subkey, and outputs the `(i, j)` target compression input `x₀`; Stage 2 receives the
challenge subkey `kStar`, samples the remaining `n - i` suffix subkeys `back`, runs
`adversary.find` on `front ++ kStar ++ back`, and extracts the `(i, j)` candidate input `x₁`. -/
noncomputable def uowhfTreeAdversary
    (h : ℕ → List Bool → List Bool → List Bool)
    (keyLen blockLen maxBlocks : ℕ → ℕ)
    (adversary : TargetCollisionFinder) : TargetCollisionFinder where
  choose n := do
    let slot ← sampleDyadicIndex ((n + 1) * maxBlocks n)
    let choice ← adversary.choose n
    let active := decide (slot < (n + 1) * maxBlocks n)
    let i := if active then slot / maxBlocks n else 0
    let j := if active then slot % maxBlocks n else 0
    let front ← BitString.sampleList (i * keyLen n)
    let x₀ := uowhfCandidateInput h n (keyLen n) (blockLen n) i j front choice.1
    return (x₀, encTreeState (active, i, j, front, choice.2))
  find n savedState kStar := do
    let s := treeStateDecoder.decode savedState
    let i := min n s.2.1
    let back ← BitString.sampleList ((n - i) * keyLen n)
    let m₁ ← adversary.find n s.2.2.2.2 (s.2.2.2.1 ++ kStar ++ back)
    return if s.1 then
      uowhfCandidateInput h n (keyLen n) (blockLen n) i s.2.2.1 s.2.2.2.1 m₁
    else []

/-- `uowhfTreeAdversary` is a uniform strict PPT `TargetCollisionFinder` whenever `h`, `keyLen`,
`blockLen`, `maxBlocks` are plain polynomial-time and `adversary` is strict PPT. -/
theorem isPPT_uowhfTreeAdversary
    {h : ℕ → List Bool → List Bool → List Bool}
    {keyLen blockLen maxBlocks : ℕ → ℕ} {adversary : TargetCollisionFinder}
    (hh : ComputableInPolyTime (fun ⟨n, k, x⟩ => h n k x)
      (encPair encUnary (encPair encBits encBits)) encBits)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    (hblockLen : ComputableInPolyTime blockLen encUnary encUnary)
    (hmaxBlocks : ComputableInPolyTime maxBlocks encUnary encUnary)
    (ha : adversary.IsPPT) :
    (uowhfTreeAdversary h keyLen blockLen maxBlocks adversary).IsPPT := by
  have hkt := hkeyLen.tidy; have hbt := hblockLen.tidy; have hmt := hmaxBlocks.tidy
  have hdec := treeStateDecoder.computableInPolyTime.tidy
  have hbound : ComputableTidilyInPolyTime (fun n => (n + 1) * maxBlocks n) encUnary encUnary :=
    tidy_congr (ComputableTidilyInPolyTime.unary_mul.comp
      ((ComputableTidilyInPolyTime.unary_add.comp
        (ComputableTidilyInPolyTime.id'.prod (.const 1))).prod hmt)) fun _ => rfl
  constructor
  · let E2 := encPair (encPair encUnary encUnary) (encPair encBits encBits)
    have hq := ComputableTidilyInPolyTime.id' (encIn := E2)
    have hn2 := hq.fst'.fst'; have hslot2 := hq.fst'.snd'
    have hact2 := hslot2.unary_lt' (hbound.comp hn2); have hB2 := hmt.comp hn2
    have hi2 := ComputableTidilyInPolyTime.ite' hact2
      (ComputableTidilyInPolyTime.unary_div.comp (hslot2.prod hB2)) (.const 0)
    have hj2 := ComputableTidilyInPolyTime.ite' hact2
      (ComputableTidilyInPolyTime.unary_mod.comp (hslot2.prod hB2)) (.const 0)
    have hflen := ComputableTidilyInPolyTime.unary_mul.comp (hi2.prod (hkt.comp hn2))
    have hr := ComputableTidilyInPolyTime.id' (encIn := encPair E2 encBits)
    have hn3 := hn2.comp hr.fst'; have hi3 := hi2.comp hr.fst'; have hj3 := hj2.comp hr.fst'
    have hx₀ := (computableInPolyTime_uowhfCandidateInput hh
      (.of_tidy hn3) (.of_tidy (hkt.comp hn3)) (.of_tidy (hbt.comp hn3))
      (.of_tidy hi3) (.of_tidy hj3) (.of_tidy hr.snd') (.of_tidy hr.fst'.snd'.fst')).tidy
    have hst := ((hact2.comp hr.fst').prod
      (hi3.prod (hj3.prod (hr.snd'.prod hr.fst'.snd'.snd')))).encoded
    exact (isPPTOn_sampleDyadicIndex (.of_tidy hbound)).bind_with
      ((ha.choose.preprocess (ComputableInPolyTime.fst encUnary encUnary)).bind_with
        ((isPPTOn_sampleList.preprocess (of_tidy_congr hflen fun _ => rfl)).bind_with
          (tidy_congr (hx₀.prod hst) fun _ => rfl).isPPTOn))
  · let EF0 := encPair encUnary (encPair encBits encBits)
    let EF1 := encPair EF0 encBits
    have hp := ComputableTidilyInPolyTime.id' (encIn := EF0)
    have hs0 := hdec.comp hp.snd'.fst'
    have hi0 := ComputableTidilyInPolyTime.unary_min.comp (hp.fst'.prod hs0.snd'.fst')
    have hblen := ComputableTidilyInPolyTime.unary_mul.comp
      ((ComputableTidilyInPolyTime.unary_sub.comp (hp.fst'.prod hi0)).prod (hkt.comp hp.fst'))
    have hq := ComputableTidilyInPolyTime.id' (encIn := EF1)
    have hK1 := ComputableTidilyInPolyTime.bitsAppend
      (ComputableTidilyInPolyTime.bitsAppend (hs0.snd'.snd'.snd'.fst'.comp hq.fst')
        hq.fst'.snd'.snd') hq.snd'
    have hfin := hq.fst'.fst'.prod ((hs0.snd'.snd'.snd'.snd'.comp hq.fst').prod hK1)
    have hr := ComputableTidilyInPolyTime.id' (encIn := encPair EF1 encBits)
    have hr0 := hr.fst'.fst'; have hn3 := hr0.fst'
    have hret := ComputableTidilyInPolyTime.ite' (hs0.fst'.comp hr0)
      (computableInPolyTime_uowhfCandidateInput hh (.of_tidy hn3)
        (.of_tidy (hkt.comp hn3)) (.of_tidy (hbt.comp hn3))
        (.of_tidy (hi0.comp hr0)) (.of_tidy (hs0.snd'.snd'.fst'.comp hr0))
        (.of_tidy (hs0.snd'.snd'.snd'.fst'.comp hr0)) (.of_tidy hr.snd')).tidy
      (.const [])
    exact (isPPTOn_sampleList.preprocess (of_tidy_congr hblen fun _ => rfl)).bind_with
      ((ha.find.preprocess (of_tidy_congr hfin fun _ => rfl)).bind_with
        (tidy_congr hret fun _ => rfl).isPPTOn)

private theorem uniformList_bind_three_split {α : Type*} (a b c : ℕ)
    (Φ : List Bool → List Bool → List Bool → PMF α) :
    (BitString.uniformList a).bind (fun front =>
      (BitString.uniformList b).bind (fun mid =>
        (BitString.uniformList c).bind (fun back =>
          Φ front mid (front ++ mid ++ back)))) =
      (BitString.uniformList (a + b + c)).bind (fun K =>
        Φ (K.take a) ((K.drop a).take b) K) := by
  rw [Nat.add_assoc, BitString.uniformList_add a (b + c), BitString.uniformList_add b c]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  refine PMF.bind_congr_on_support _ _ _ fun front hfront =>
    PMF.bind_congr_on_support _ _ _ fun mid hmid =>
      PMF.bind_congr_on_support _ _ _ fun back _ => ?_
  have hfront_len : front.length = a := BitString.length_of_mem_support_uniformList hfront
  have hmid_len : mid.length = b := BitString.length_of_mem_support_uniformList hmid
  simp only [List.append_assoc, List.take_left' hfront_len, List.drop_left' hfront_len,
    List.take_left' hmid_len]

private theorem listRow_eq_drop_take_of_le {κ n i : ℕ} (hi : i ≤ n) {K : List Bool}
    (hK : K.length = (n + 1) * κ) :
    (K.drop (i * κ)).take κ = BitString.listRow κ i K := by
  have hrem : κ ≤ (K.drop (i * κ)).length := by
    rw [List.length_drop, hK]
    have : (i + 1) * κ ≤ (n + 1) * κ := Nat.mul_le_mul_right κ (by omega)
    have : i * κ + κ = (i + 1) * κ := by ring
    omega
  unfold BitString.listRow; rw [List.take_append_of_le_length hrem]

private theorem pmf_map_true_le_sum {α : Type*} (μ : PMF α) (D : ℕ)
    (W : α → Bool) (Wi : Fin D → α → Bool)
    (hcover : ∀ a ∈ μ.support, W a = true → ∃ s : Fin D, Wi s a = true) :
    (μ.map W) true ≤ ∑ s : Fin D, (μ.map (Wi s)) true := by
  let F (j : ℕ) (a : α) : Bool := if hj : j < D then Wi ⟨j, hj⟩ a else false
  have hmono : (μ.map W) true ≤ (μ.map (fun a => (List.range D).any (fun j => F j a))) true := by
    refine PMF.map_true_mono μ fun a ha hW => ?_
    obtain ⟨⟨j, hj⟩, hs⟩ := hcover a ha hW
    exact List.any_eq_true.mpr ⟨j, List.mem_range.mpr hj, by simp only [F, hj, ↓reduceDIte, hs]⟩
  refine hmono.trans ((PMF.map_any_range_true_le_sum μ D F).trans ?_)
  rw [Finset.sum_fin_eq_sum_range]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj_lt : j < D := Finset.mem_range.mp hj
  have hF : F j = Wi ⟨j, hj_lt⟩ := funext fun a => by simp only [F, hj_lt, ↓reduceDIte]
  simp only [hj_lt, ↓reduceDIte, hF, le_rfl]

/-- **Concrete security bound for `uowhfTreeHash`**: at any security parameter `n ≥ 1` with
`n ≤ blockLen n`, `1 ≤ maxBlocks n`, `h n` mapping every `keyLen n`-bit key and
`2 * blockLen n`-bit input to a `blockLen n`-bit output, and every supported message pair
`(m₀, m₁)` of `adversary` satisfying `m₀.length ≤ maxBlocks n`, `m₀.length < 2 ^ n`, and
`m₁.length < 2 ^ n`, the target-collision success probability of `adversary` against
`uowhfTreeHash` is at most `dyadicSize ((n + 1) * maxBlocks n)` times that of
`uowhfTreeAdversary` against `h`. -/
theorem succProbability_targetCollisionGame_uowhfTreeHash_le
    {h : ℕ → List Bool → List Bool → List Bool}
    {keyLen blockLen maxBlocks : ℕ → ℕ}
    (adversary : TargetCollisionFinder) (n : ℕ)
    (hn : 1 ≤ n) (hM_ge : n ≤ blockLen n) (hB : 1 ≤ maxBlocks n)
    (hlen_h : ∀ k x, k.length = keyLen n → x.length = 2 * blockLen n →
      (h n k x).length = blockLen n)
    (hm₀_bound : ∀ choice ∈ (ProbComp.eval (adversary.choose n)).support,
      choice.1.length ≤ maxBlocks n ∧ choice.1.length < 2 ^ n)
    (hm₁_bound : ∀ choice ∈ (ProbComp.eval (adversary.choose n)).support,
      ∀ K ∈ (BitString.uniformList ((n + 1) * keyLen n)).support,
      ∀ m₁ ∈ (ProbComp.eval (adversary.find n choice.2 K)).support,
      m₁.length < 2 ^ n) :
    Game.succProbability
      (ProbComp.eval
        (targetCollisionGame (fun m => (m + 1) * keyLen m)
          (uowhfTreeHash h keyLen blockLen) (fun _ _ => true) adversary n)) ≤
      (dyadicSize ((n + 1) * maxBlocks n) : ℝ≥0) *
        Game.succProbability
          (ProbComp.eval
            (targetCollisionGame keyLen h (fun m x => x.length == 2 * blockLen m)
              (uowhfTreeAdversary h keyLen blockLen maxBlocks adversary) n)) := by
  let κ := keyLen n; let M := blockLen n; let B := maxBlocks n; let bound := (n + 1) * B
  let validComp (m : ℕ) (x : List Bool) : Bool := x.length == 2 * blockLen m
  let μ : PMF ((List Bool × List Bool) × List Bool × List Bool) :=
    (ProbComp.eval (adversary.choose n)).bind fun choice =>
      (BitString.uniformList ((n + 1) * κ)).bind fun K =>
        (ProbComp.eval (adversary.find n choice.2 K)).map fun m₁ => (choice, K, m₁)
  let W (t : (List Bool × List Bool) × List Bool × List Bool) : Bool :=
    isCollision (uowhfTreeHash h keyLen blockLen n) (fun _ _ => true) n t.2.1 t.1.1 t.2.2
  let slotTrial (slot : ℕ) : Game :=
    let active := decide (slot < bound)
    let i := if active then slot / B else 0
    let j := if active then slot % B else 0
    (ProbComp.eval (adversary.choose n)).bind fun choice =>
      (BitString.uniformList (i * κ)).bind fun front =>
        (BitString.uniformList κ).bind fun kStar =>
          (BitString.uniformList ((n - min n i) * κ)).bind fun back =>
            (ProbComp.eval (adversary.find n choice.2 (front ++ kStar ++ back))).bind fun m₁ =>
              PMF.pure (isCollision (h n) validComp n kStar
                (uowhfCandidateInput h n κ M i j front choice.1)
                (if active then uowhfCandidateInput h n κ M (min n i) j front m₁ else []))
  have hred_eq :
      ProbComp.eval
        (targetCollisionGame keyLen h validComp
          (uowhfTreeAdversary h keyLen blockLen maxBlocks adversary) n) =
        (PMF.uniformOfFintype (Fin (dyadicSize bound))).bind (fun s => slotTrial s.val) := by
    dsimp only [targetCollisionGame, uowhfTreeAdversary, slotTrial, κ, M, B, bound]
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, eval_sampleDyadicIndex,
      BitString.eval_sampleList, treeStateDecoder.decode_enc, PMF.bind_bind, PMF.pure_bind,
      PMF.bind_map, Function.comp_def]
  have htree_eq :
      ProbComp.eval
        (targetCollisionGame (fun m => (m + 1) * keyLen m)
          (uowhfTreeHash h keyLen blockLen) (fun _ _ => true) adversary n) =
        μ.map W := by
    simp only [targetCollisionGame, μ, W, ProbComp.eval_bind, ProbComp.eval_pure,
      BitString.eval_sampleList, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def, κ]
  let Wi (s : Fin (dyadicSize bound))
      (t : (List Bool × List Bool) × List Bool × List Bool) : Bool :=
    if s.val < bound then
      let i := s.val / B
      let j := s.val % B
      isCollision (h n) validComp n (BitString.listRow κ i t.2.1)
        (uowhfCandidateInput h n κ M i j t.2.1 t.1.1)
        (uowhfCandidateInput h n κ M i j t.2.1 t.2.2)
    else false
  have hslot_eq (s : Fin (dyadicSize bound)) (hs : s.val < bound) :
      slotTrial s.val = μ.map (Wi s) := by
    have hi_le : s.val / B ≤ n := Nat.le_of_lt_succ
      (Nat.div_lt_of_lt_mul (by simpa only [B, bound, Nat.mul_comm] using hs))
    have hlen_sum : s.val / B * κ + κ + (n - s.val / B) * κ = (n + 1) * κ := by
      rw [show s.val / B * κ + κ + (n - s.val / B) * κ =
          (s.val / B + 1 + (n - s.val / B)) * κ by ring,
        show s.val / B + 1 + (n - s.val / B) = n + 1 by omega]
    dsimp only [slotTrial, μ, Wi]
    simp only [hs, decide_true, ↓reduceIte, Nat.min_eq_right hi_le,
      PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
    refine PMF.bind_congr_on_support _ _ _ fun choice _ => ?_
    let Φ (front kStar full : List Bool) : PMF Bool :=
      (ProbComp.eval (adversary.find n choice.2 full)).bind fun m₁ =>
        PMF.pure
          (isCollision (h n) validComp n kStar
            (uowhfCandidateInput h n κ M (s.val / B) (s.val % B) front choice.1)
            (uowhfCandidateInput h n κ M (s.val / B) (s.val % B) front m₁))
    exact (uniformList_bind_three_split (s.val / B * κ) κ ((n - s.val / B) * κ) Φ).trans <| by
      rw [hlen_sum]
      refine PMF.bind_congr_on_support _ _ _ fun K hK => ?_
      have hK_len : K.length = (n + 1) * κ := BitString.length_of_mem_support_uniformList hK
      dsimp only [Φ]
      rw [listRow_eq_drop_take_of_le hi_le hK_len,
        uowhfCandidateInput_take_eq h hi_le K choice.1]
      refine PMF.bind_congr_on_support _ _ _ fun m₁ _ => ?_
      rw [uowhfCandidateInput_take_eq h hi_le K m₁]
  have hcover : ∀ t ∈ μ.support, W t = true → ∃ s : Fin (dyadicSize bound), Wi s t = true := by
    rintro ⟨choice, K, m₁⟩ ht hW
    simp only [μ, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at ht
    obtain ⟨choice', hchoice, K', hK, ⟨m₁', hm₁, htuple⟩⟩ := ht
    injection htuple with h1 h23; injection h23 with h2 h3; subst h1 h2 h3
    obtain ⟨_, _, hne, hcol⟩ := isCollision_eq_true_iff.mp hW
    obtain ⟨hm₀_B, hm₀_pow⟩ := hm₀_bound choice' hchoice
    obtain ⟨i, hi_le, j, hj_lt, hx_ne, hx_col⟩ :=
      exists_uowhfCandidateInput_collision hn hM_ge hB hm₀_B hm₀_pow
        (hm₁_bound choice' hchoice K' hK m₁' hm₁) hlen_h hne hcol
    let slot := i * B + j
    have hslot_lt : slot < bound :=
      (Nat.add_lt_add_left hj_lt _).trans_le
        (by rw [show i * B + B = (i + 1) * B by ring]; exact Nat.mul_le_mul_right B (by omega))
    have hdiv : slot / B = i := by
      dsimp only [slot]
      rw [Nat.mul_comm i B, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj_lt, Nat.add_zero]
    have hmod : slot % B = j := by
      dsimp only [slot]; rw [Nat.mul_comm i B, Nat.mul_add_mod, Nat.mod_eq_of_lt hj_lt]
    refine ⟨⟨slot, hslot_lt.trans (lt_dyadicSize bound)⟩, ?_⟩
    simp only [Wi, hslot_lt, ↓reduceIte, hdiv, hmod, isCollision_eq_true_iff, validComp,
      beq_iff_eq, length_uowhfCandidateInput, true_and, M]
    exact ⟨hx_ne, hx_col⟩
  have hsum_le : (μ.map W) true ≤ ∑ s : Fin (dyadicSize bound), (slotTrial s.val) true := by
    refine (pmf_map_true_le_sum μ (dyadicSize bound) W Wi hcover).trans
      (Finset.sum_le_sum fun s _ => ?_)
    by_cases hs : s.val < bound
    · rw [hslot_eq s hs]
    · simp only [Wi, hs, ↓reduceIte, PMF.map_apply, Bool.true_eq_false, tsum_zero, zero_le]
  have hpos : (0 : ℝ≥0) < dyadicSize bound := by exact_mod_cast dyadicSize_pos bound
  rw [htree_eq, hred_eq, Game.succProbability_uniform, Fintype.card_fin,
    mul_div_cancel₀ _ hpos.ne']
  have hmono := ENNReal.toNNReal_mono
    (ne_of_lt (ENNReal.sum_lt_top.mpr fun s _ => (PMF.apply_ne_top _ _).lt_top)) hsum_le
  rwa [ENNReal.toNNReal_sum fun s _ => PMF.apply_ne_top _ _] at hmono

/-- Extend any `KeyedCompressionFamily` `C` (`2 * C.blockLen n → C.blockLen n` under
`C.keyLen n`-bit keys) to an unrestricted `KeyedHashFamily` on `List Bool` with
`(n + 1) * C.keyLen n`-bit keys and `C.blockLen n`-bit digests via `uowhfTreeHash`. Note that at
fixed `n`, `uowhfTreeHash` has injective tree capacity `< 2 ^ n` bits and discards extra roots
beyond `2 ^ n` via `List.headD`; asymptotic security on all `List Bool` relies on strict-PPT
adversary output-length bounds. -/
@[expose]
def KeyedCompressionFamily.treeHash (C : KeyedCompressionFamily) : KeyedHashFamily where
  keyLen := fun n => (n + 1) * C.keyLen n
  digestLen := C.blockLen
  eval := uowhfTreeHash C.eval C.keyLen C.blockLen
  keyLen_polyTime := by
    exact (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.unary_mul.comp
      ((ComputableTidilyInPolyTime.unary_add.comp
        (ComputableTidilyInPolyTime.id'.prod (.const 1))).prod C.keyLen_polyTime.tidy))).of_enc_eq
      fun _ => rfl
  digestLen_polyTime := C.blockLen_polyTime
  polyTime := computableInPolyTime_uowhfTreeHash C.polyTime C.keyLen_polyTime C.blockLen_polyTime
  le_digestLen := C.le_blockLen
  length_eq := fun n K msg _ => length_uowhfTreeHash C.eval C.keyLen C.blockLen n K msg

/-- **Domain extension for target collision resistance** (adapting [NaorYung1989], 1995 revision,
Section 2.3 and [Goldreich2004], Section 6.4.3.2, June 2003 draft Constructions 6.4.24 and 6.4.26,
Propositions 6.4.25 and 6.4.27; cf. [BonehShoup2023], Section 8.11.3, pp. 339–340): if `C` is
target collision-resistant on `2 * C.blockLen n`-bit inputs, then `C.treeHash` is unrestrictedly
target collision-resistant on all `List Bool`. Strict-PPT admissibility bounds the output lengths of
both `adversary.choose` and `adversary.find` by polynomials in `n`, placing every supported `m₀` and
`m₁` strictly below `2 ^ n ≤ 2 ^ C.blockLen n` for all sufficiently large `n`. -/
theorem KeyedCompressionFamily.targetCollisionResistant_treeHash
    {C : KeyedCompressionFamily} (hC : C.TargetCollisionResistant) :
    C.treeHash.TargetCollisionResistant := by
  apply TargetCollisionResistantOn.of_negligible
  intro adversary hadversary
  obtain ⟨c₁, d₁, hlen₁⟩ := hadversary.choose.length_le
  obtain ⟨c₂, d₂, hlen₂⟩ := hadversary.find.length_le
  let maxBlocks (n : ℕ) : ℕ := c₁ * (n + 1) ^ d₁ + 1
  have hn1 := ComputableTidilyInPolyTime.unary_add.comp
    (ComputableTidilyInPolyTime.id'.prod (.const 1))
  have hmaxBlocks_polyTime : ComputableInPolyTime maxBlocks encUnary encUnary :=
    of_tidy_congr (ComputableTidilyInPolyTime.unary_add.comp
      ((ComputableTidilyInPolyTime.unary_mul.comp
        ((ComputableTidilyInPolyTime.const c₁).prod
          ((ComputableTidilyInPolyTime.unary_pow d₁).comp hn1))).prod (.const 1))) fun _ => rfl
  let redAdversary := uowhfTreeAdversary C.eval C.keyLen C.blockLen maxBlocks adversary
  have hredPPT : redAdversary.IsPPT :=
    isPPT_uowhfTreeAdversary C.polyTime C.keyLen_polyTime C.blockLen_polyTime
      hmaxBlocks_polyTime hadversary
  have hkeyLen_pb : PolynomiallyBounded C.keyLen := C.keyLen_polyTime.polynomiallyBounded
  have hmaxBlocks_pb : PolynomiallyBounded maxBlocks :=
    ((PolynomiallyBounded.const c₁).mul ((PolynomiallyBounded.id.add (.const 1)).pow d₁)).add
      (.const 1)
  have hfindCap_pb : PolynomiallyBounded
      (fun n => c₂ * (2 * n + 2 * maxBlocks n + (n + 1) * C.keyLen n + 4) ^ d₂) :=
    (PolynomiallyBounded.const c₂).mul
      ((((((PolynomiallyBounded.const 2).mul .id).add
        ((PolynomiallyBounded.const 2).mul hmaxBlocks_pb)).add
          ((PolynomiallyBounded.id.add (.const 1)).mul hkeyLen_pb)).add (.const 4)).pow d₂)
  have hloss_pb : PolynomiallyBounded (fun n => dyadicSize ((n + 1) * maxBlocks n)) :=
    PolynomiallyBounded.comp dyadicSize_polynomiallyBounded
      ((PolynomiallyBounded.id.add (.const 1)).mul hmaxBlocks_pb)
  refine negligible_of_eventually_le
    ((hC.negligible redAdversary hredPPT).polynomiallyBounded_mul hloss_pb) ?_
  filter_upwards [Filter.eventually_ge_atTop 1,
      hmaxBlocks_pb.eventually_lt_two_pow,
      hfindCap_pb.eventually_lt_two_pow] with n hn hm₀_exp hm₁_exp
  have hchoice_le {choice} (hchoice : choice ∈ (ProbComp.eval (adversary.choose n)).support) :
      choice.1.length ≤ maxBlocks n ∧ choice.2.length ≤ maxBlocks n := by
    have henc := hlen₁ n choice hchoice
    simp only [length_encPair, encBits, Function.Embedding.refl_apply, encUnary_apply,
      List.length_replicate, maxBlocks] at henc ⊢
    omega
  unfold KeyedCompressionFamily.treeHash KeyedCompressionFamily.validInput
  dsimp only [redAdversary]
  refine succProbability_targetCollisionGame_uowhfTreeHash_le
    (h := C.eval) (keyLen := C.keyLen) (blockLen := C.blockLen) (maxBlocks := maxBlocks)
    adversary n hn (C.le_blockLen n)
    (Nat.le_add_left 1 _) (C.length_eq n)
    (fun choice hchoice => ⟨(hchoice_le hchoice).1, (hchoice_le hchoice).1.trans_lt hm₀_exp⟩) ?_
  intro choice hchoice K hK m₁ hm₁
  have hst_le := (hchoice_le hchoice).2
  have hK_len : K.length = (n + 1) * C.keyLen n := BitString.length_of_mem_support_uniformList hK
  have henc₂ := hlen₂ (n, choice.2, K) m₁ hm₁
  simp only [length_encPair, encBits, Function.Embedding.refl_apply, encUnary_apply,
    List.length_replicate, hK_len] at henc₂
  have hinput_le :
      2 * n + 1 + (2 * choice.2.length + 1 + (n + 1) * C.keyLen n) + 1 ≤
        2 * n + 2 * maxBlocks n + (n + 1) * C.keyLen n + 4 := by omega
  exact (henc₂.trans (Nat.mul_le_mul_left c₂ (Nat.pow_le_pow_left hinput_le d₂))).trans_lt hm₁_exp

end Cslib.Crypto
