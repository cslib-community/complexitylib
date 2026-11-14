/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.InaccessibleEntropy.Amplify
public import CslibFrontier.Crypto.Computational.InaccessibleEntropy.ShoupComposition
public import CslibFrontier.Crypto.Computational.TargetCollisionResistant
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool

/-!
# Target collision-resistant hashing from inaccessible entropy and one-way functions

Completing the construction of universal one-way hash families (target collision-resistant hash
families) from arbitrary one-way functions (`[Rompel1990]`; `[Shoup2000]`; `[HHRVW2020]`,
Section 5.1, Theorem 5.1, STEPS 4–5, Lemmas 5.6 and 5.7, pp. 29–32):

1. **Target shift (`rompelShiftedStep`; `[HHRVW2020]`, Section 5.1.4, Lemma 5.6, pp. 29–30, and
   Section 5.1.5, STEP 4, p. 31)**:
   given a `ShrinkingCollisionGrid` `G` whose `gridCount n` candidates compress `G.inLen n =
   G.outLen n + G.shrinkLen n` bits to `G.outLen n` bits (with `G.shrinkLen n = Nat.log 2 n + 1`
   on the canonical grid `AdversaryInaccessibleEntropyFamily.exists_shrinkingCollisionGrid_log`),
   shifting the input of candidate `q` by a `G.inLen n`-bit key mask `y` via
   `w ↦ G.evalGrid n q (listXor (G.inLen n) [w, y])` converts random-input collision resistance at
   `q = goodIdx n` into keyed target collision resistance on `G.inLen n`-bit inputs.
2. **Shoup `O(|y| log t)` XOR-masking cascade and candidate concatenation (`rompelCandidateEval`,
   `rompelCompressionEval`, `rompelCompression`, `rompelKeyLen_le`; `[Shoup2000]`;
   `[HHRVW2020]`, Section 5.1.4, Lemma 5.7, p. 30, and Section 5.1.5, STEP 5(ii–iii), p. 32)**:
   iterating `rompelCascadeSteps G n = ⌈(2 * G.gridCount n - 1) * G.outLen n / G.shrinkLen n⌉`
   steps of `shoupCascade` under one base shift `y : {0, 1}^{G.inLen n}` and `⌊log₂ t⌋ + 1` shared
   `G.outLen n`-bit masks compresses `2 * rompelBlockLen G n` bits to `G.outLen n` bits for each
   `q < G.gridCount n`, and concatenating all `G.gridCount n` candidate outputs produces a halving
   `KeyedCompressionFamily` (`rompelCompression G`) with block width `rompelBlockLen G n =
   G.gridCount n * G.outLen n`.
   - **Key length (`rompelKeyLen_le`)**: the shared key `K = y ++ masks` has exact bit-length
     `rompelKeyLen G n = G.inLen n + (Nat.log 2 (rompelCascadeSteps G n) + 1) * G.outLen n ≤
     (Nat.log 2 (rompelCascadeSteps G n) + 2) * G.inLen n`, matching `[HHRVW2020]` Lemma 5.7's
     `O(|y| log t)` bound directly on `rompelCompression G`.
   - **Shared key across candidates vs. `[HHRVW2020]` STEP 5(iii)**: sharing one Shoup key
     `K = (y, M₀, …, M_d)` across all `G.gridCount n` candidate rows suffices for every security,
     PPT, key-length, and domain-extension claim in the library because for each strict PPT
     adversary `adv`, `G.exists_good_candidate` supplies one index `goodIdx n`, so
     `rompelCompressionInverter G adv` only needs faithful key simulation at `goodIdx n`. Sharing
     `K` achieves the exact same multiplicative reduction loss `dyadicSize (G.gridCount n) *
     dyadicSize (rompelCascadeSteps G n)` with `G.gridCount n`-times shorter keys than
     per-candidate keys (no downstream theorem asks for key independence at rows `q ≠ goodIdx`).
3. **Single-stage planted-subkey reduction (`rompelCompressionInverter`,
   `succProbability_targetCollisionGame_rompelCompression_le`,
   `ShrinkingCollisionGrid.targetCollisionResistant_rompelCompression`)**:
   given a uniform `G.inLen n`-bit challenge `zWord` for `randomCollisionGame` at `goodIdx n`,
   sampling dyadic guesses `(qGuess, slot)` (`i* = min (slot + 1) (rompelCascadeSteps G n)`),
   running `adversary.choose n`, sampling the `shoupMasksLen` vector `T`, forming the planted step
   input `w₀`, setting `yStar := listXor (G.inLen n) [zWord, w₀]` so `w₀ ⊕ yStar = zWord`, and
   reconstructing the XOR masks via `shoupPackMasks` achieves exact key simulation with
   multiplicative loss `dyadicSize (G.gridCount n) * dyadicSize (rompelCascadeSteps G n)` and zero
   additive error. Because `rompelCompressionInverter` never reads `goodIdx`, the reduction works
   directly against adversary-dependent `goodIdx` from Definition 3.9
   (`AdversaryInaccessibleEntropyFamily`).
4. **Domain extension to `List Bool` (`rompelHash`,
   `ShrinkingCollisionGrid.targetCollisionResistant_rompelHash`,
   `AdversaryInaccessibleEntropyFamily.exists_targetCollisionResistantHash`,
   `OneWay.exists_targetCollisionResistant_keyedHashFamily`)**:
   composing `rompelCompression G` with `KeyedCompressionFamily.treeHash` (`uowhfTreeHash`) yields
   an unrestricted computational target collision-resistant `KeyedHashFamily` on `List Bool` from
   any uniform `OneWay` function: although the compressed `rompelBlockLen G n`-bit digest cannot be
   injective on long messages, on inputs of length `< 2 ^ n` at parameter `n` the leaf/length
   encoding is injective and the fixed `n`-level binary tree reduces all leaves to a single root
   without discarding extra roots, so any collision among strict-PPT adversary outputs (which have
   length `< 2 ^ n` for sufficiently large `n`) extracts a compression-step collision.

## Main definitions

* `Cslib.Crypto.rompelShiftedStep`: XOR-masked `G.shrinkLen n`-bit shrinking candidate step
  (Lemma 5.6, STEP 4).
* `Cslib.Crypto.rompelCascadeSteps`, `Cslib.Crypto.rompelBlockLen`, `Cslib.Crypto.rompelKeyLen`:
  step, block, and shared `O(|y| log t)` key-length schedules for `rompelCompression`.
* `Cslib.Crypto.rompelCandidateEval`, `Cslib.Crypto.rompelCascadeInput`: Shoup XOR-masked
  `G.shrinkLen n`-bit shrinking cascade and step-`i` compression-input extractor (`[Shoup2000]`;
  `[HHRVW2020]`, Lemma 5.7, STEP 5(ii)).
* `Cslib.Crypto.rompelCompressionEval`, `Cslib.Crypto.rompelCompression`: `gridCount n`-way
  concatenated `2 * rompelBlockLen G n → rompelBlockLen G n` `KeyedCompressionFamily` (adapting
  STEP 5(iii) with shared Shoup key).
* `Cslib.Crypto.rompelCompressionInverter`: uniform strict-PPT reduction from target collisions of
  `rompelCompression G` to `randomCollisionGame` on `G`.
* `Cslib.Crypto.rompelHash`: unrestricted `KeyedHashFamily` `(rompelCompression G).treeHash`.

## Main results

* `Cslib.Crypto.rompelKeyLen_le`, `Cslib.Crypto.ShrinkingCollisionGrid.rompelCompression_keyLen_le`:
  explicit `O(|y| log t)` key-length bound `(Nat.log 2 (rompelCascadeSteps G n) + 2) * G.inLen n`
  for `rompelCompression G`.
* `Cslib.Crypto.exists_rompelCascadeInput_collision`: deterministic extraction of a step collision
  `1 ≤ i ≤ rompelCascadeSteps G n` from any `2 * rompelBlockLen G n`-bit collision of candidate `q`.
* `Cslib.Crypto.isPPT_rompelCompressionInverter`: uniform strict-PPT certificate for
  `rompelCompressionInverter`.
* `Cslib.Crypto.succProbability_targetCollisionGame_rompelCompression_le`: concrete security bound
  against `randomCollisionGame` at any candidate `qStar < G.gridCount n`.
* `Cslib.Crypto.ShrinkingCollisionGrid.targetCollisionResistant_rompelCompression`,
  `Cslib.Crypto.ShrinkingCollisionGrid.targetCollisionResistant_rompelHash`: target collision
  resistance of `rompelCompression G` and `rompelHash G`.
* `Cslib.Crypto.AdversaryInaccessibleEntropyFamily.exists_targetCollisionResistantCompression`,
  `Cslib.Crypto.AdversaryInaccessibleEntropyFamily.exists_targetCollisionResistantHash`: Theorem
  5.1 directly from Definition 3.9 (`AdversaryInaccessibleEntropyFamily`).
* `Cslib.Crypto.OneWay.exists_targetCollisionResistant_keyedCompressionFamily`,
  `Cslib.Crypto.OneWay.exists_targetCollisionResistant_keyedHashFamily`: every uniform `OneWay`
  function implies target collision-resistant compression and unrestricted `KeyedHashFamily`
  hashing.

## References

* [I. Haitner, T. Holenstein, O. Reingold, S. Vadhan, H. Wee, *Inaccessible Entropy II: IE
  Functions and Universal One-Way Hashing*, Sections 5.1.4–5.1.5, Theorem 5.1, Lemmas 5.6–5.7,
  pp. 29–32][HHRVW2020]
* [V. Shoup, *A Composition Theorem for Universal One-Way Hash Functions*, EUROCRYPT 2000,
  LNCS 1807, pp. 445–452][Shoup2000]
* [J. Rompel, *One-Way Functions are Necessary and Sufficient for Secure Signatures*][Rompel1990]
-/

public section

namespace Cslib.Crypto

open ProbComp Cslib.Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-! ### Schedules and XOR-shifted `G.shrinkLen n`-bit shrinking step (Lemma 5.6, STEP 4) -/

/-- Number of `G.shrinkLen n`-bit cascade steps `((2 * G.gridCount n - 1) * G.outLen n +
G.shrinkLen n - 1) / G.shrinkLen n` used by each candidate in `rompelCompression G`
(`[HHRVW2020]`, Section 5.1.5, STEP 5(ii), p. 32). -/
def rompelCascadeSteps (G : ShrinkingCollisionGrid) (n : ℕ) : ℕ :=
  ((2 * G.gridCount n - 1) * G.outLen n + G.shrinkLen n - 1) / G.shrinkLen n

/-- Output (and half-input) block width `G.gridCount n * G.outLen n` of `rompelCompression G`
(`[HHRVW2020]`, Section 5.1.5, STEP 5(iii), p. 32). -/
@[expose]
def rompelBlockLen (G : ShrinkingCollisionGrid) (n : ℕ) : ℕ :=
  G.gridCount n * G.outLen n

/-- Shared Shoup `O(|y| log t)` key bit-length
`G.inLen n + (Nat.log 2 (rompelCascadeSteps G n) + 1) * G.outLen n` of `rompelCompression G`
(`[Shoup2000]`; `[HHRVW2020]`, Section 5.1.4, Lemma 5.7, p. 30). -/
@[expose]
def rompelKeyLen (G : ShrinkingCollisionGrid) (n : ℕ) : ℕ :=
  shoupComposeKeyLen G.inLen G.outLen (rompelCascadeSteps G) n

theorem rompelKeyLen_eq (G : ShrinkingCollisionGrid) (n : ℕ) :
    rompelKeyLen G n = G.inLen n + (Nat.log 2 (rompelCascadeSteps G n) + 1) * G.outLen n :=
  rfl

/-- **`[HHRVW2020]` Lemma 5.7 `O(|y| log t)` key-length bound**:
`rompelKeyLen G n ≤ (Nat.log 2 (rompelCascadeSteps G n) + 2) * G.inLen n`. -/
theorem rompelKeyLen_le (G : ShrinkingCollisionGrid) (n : ℕ) :
    rompelKeyLen G n ≤ (Nat.log 2 (rompelCascadeSteps G n) + 2) * G.inLen n := by
  exact shoupComposeKeyLen_le (by have := G.outLen_add_shrink n; omega)

theorem rompelCascadeSteps_pos (G : ShrinkingCollisionGrid) (n : ℕ) :
    1 ≤ rompelCascadeSteps G n := by
  have hk := G.gridCount_pos n
  have hout := G.le_outLen n
  have hs := G.shrinkLen_pos n
  have hprod : 1 ≤ (2 * G.gridCount n - 1) * G.outLen n := Nat.mul_pos (by omega) (by omega)
  unfold rompelCascadeSteps
  exact Nat.div_pos (by omega) hs

theorem two_mul_rompelBlockLen_le (G : ShrinkingCollisionGrid) (n : ℕ) :
    2 * rompelBlockLen G n ≤ G.outLen n + rompelCascadeSteps G n * G.shrinkLen n := by
  have hk : 1 ≤ G.gridCount n := G.gridCount_pos n
  have hout : n + 1 ≤ G.outLen n := G.le_outLen n
  have hs : 1 ≤ G.shrinkLen n := G.shrinkLen_pos n
  have hprod : 1 ≤ (2 * G.gridCount n - 1) * G.outLen n := Nat.mul_pos (by omega) (by omega)
  have hsub : 1 + (2 * G.gridCount n - 1) = 2 * G.gridCount n := by omega
  have hdiv_add := Nat.div_add_mod
    ((2 * G.gridCount n - 1) * G.outLen n + G.shrinkLen n - 1) (G.shrinkLen n)
  have hmod_lt :
      ((2 * G.gridCount n - 1) * G.outLen n + G.shrinkLen n - 1) % G.shrinkLen n <
        G.shrinkLen n :=
    Nat.mod_lt _ hs
  have hceil : (2 * G.gridCount n - 1) * G.outLen n ≤ rompelCascadeSteps G n * G.shrinkLen n := by
    unfold rompelCascadeSteps
    rw [mul_comm] at hdiv_add
    omega
  calc
    2 * rompelBlockLen G n
      = (1 + (2 * G.gridCount n - 1)) * G.outLen n := by
        rw [rompelBlockLen, ← mul_assoc, hsub]
    _ = G.outLen n + (2 * G.gridCount n - 1) * G.outLen n := by rw [add_mul, one_mul]
    _ ≤ G.outLen n + rompelCascadeSteps G n * G.shrinkLen n := Nat.add_le_add_left hceil _

theorem le_rompelBlockLen (G : ShrinkingCollisionGrid) (n : ℕ) :
    n ≤ rompelBlockLen G n := by
  calc
    n ≤ G.outLen n := (Nat.le_succ n).trans (G.le_outLen n)
    _ = 1 * G.outLen n := (one_mul _).symm
    _ ≤ G.gridCount n * G.outLen n := Nat.mul_le_mul_right _ (G.gridCount_pos n)

@[fun_prop]
theorem computableInPolyTime_rompelCascadeSteps (G : ShrinkingCollisionGrid) :
    ComputableInPolyTime (rompelCascadeSteps G) encUnary encUnary := by
  unfold rompelCascadeSteps
  have h2k := ComputableInPolyTime.unary_mul' (.const 2) G.polyTime_gridCount
  have hnum := (h2k.unary_sub' (.const 1)).unary_mul' G.polyTime_outLen
  exact ComputableInPolyTime.unary_div'
    ((hnum.unary_add' G.polyTime_shrinkLen).unary_sub' (.const 1)) G.polyTime_shrinkLen

@[fun_prop]
theorem computableInPolyTime_rompelBlockLen (G : ShrinkingCollisionGrid) :
    ComputableInPolyTime (rompelBlockLen G) encUnary encUnary :=
  ComputableInPolyTime.unary_mul' G.polyTime_gridCount G.polyTime_outLen

@[fun_prop]
theorem computableInPolyTime_rompelKeyLen (G : ShrinkingCollisionGrid) :
    ComputableInPolyTime (rompelKeyLen G) encUnary encUnary :=
  computableInPolyTime_shoupComposeKeyLen G.polyTime_inLen G.polyTime_outLen
    (computableInPolyTime_rompelCascadeSteps G) (ComputableInPolyTime.id' (encIn := encUnary))

/-- **XOR-shifted `G.shrinkLen n`-bit shrinking step** (`[HHRVW2020]`, Section 5.1.4, Lemma 5.6,
pp. 29–30; Section 5.1.5, STEP 4, p. 31): masks `w` by `y` at width `G.inLen n` and evaluates
candidate `q` of `G` (`G.outLen n + G.shrinkLen n = G.inLen n`). -/
@[expose]
def rompelShiftedStep (G : ShrinkingCollisionGrid) (n q : ℕ) (y w : List Bool) : List Bool :=
  G.evalGrid n q (BitString.listXor (G.inLen n) [w, y])

@[simp]
theorem length_rompelShiftedStep (G : ShrinkingCollisionGrid) (n q : ℕ) (y w : List Bool) :
    (rompelShiftedStep G n q y w).length = G.outLen n :=
  G.length_evalGrid n q _

@[fun_prop]
theorem computableInPolyTime_rompelShiftedStep (G : ShrinkingCollisionGrid)
    {γ : Type} {encIn : γ ↪ List Bool}
    {n q : γ → ℕ} {y w : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hq : ComputableInPolyTime q encIn encUnary)
    (hy : ComputableInPolyTime y encIn encBits)
    (hw : ComputableInPolyTime w encIn encBits) :
    ComputableInPolyTime
      (fun a => rompelShiftedStep G (n a) (q a) (y a) (w a))
      encIn encBits :=
  G.polyTime_evalGrid.comp (hn.prod (hq.prod
    (ComputableInPolyTime.bitsXorWithInput (G.polyTime_inLen.comp hn)
      (.of_tidy (ComputableTidilyInPolyTime.cons' hw.tidy
        (ComputableTidilyInPolyTime.cons' hy.tidy (ComputableTidilyInPolyTime.const [])))))))

/-! ### Shoup `O(|y| log t)` XOR-masking cascade and step-collision extraction (Lemma 5.7) -/

/-- Candidate-`q` `2 * rompelBlockLen G n → G.outLen n` Shoup XOR-masking cascade evaluator under
compact key `K` (`y := BitString.listRow (G.inLen n) 0 K`, `masks := K.drop (G.inLen n)`). -/
@[expose]
def rompelCandidateEval (G : ShrinkingCollisionGrid) (n q : ℕ) (K x : List Bool) : List Bool :=
  shoupComposeEval G.inLen G.outLen G.shrinkLen (rompelCascadeSteps G)
    (fun m y w => rompelShiftedStep G m q y w) n K x

@[simp]
theorem length_rompelCandidateEval (G : ShrinkingCollisionGrid) (n q : ℕ) (K x : List Bool) :
    (rompelCandidateEval G n q K x).length = G.outLen n :=
  length_shoupComposeEval fun _ _ _ _ => length_rompelShiftedStep G n q _ _

@[fun_prop]
theorem computableInPolyTime_rompelCandidateEval (G : ShrinkingCollisionGrid)
    {γ : Type} {encIn : γ ↪ List Bool}
    {n q : γ → ℕ} {K x : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hq : ComputableInPolyTime q encIn encUnary)
    (hK : ComputableInPolyTime K encIn encBits)
    (hx : ComputableInPolyTime x encIn encBits) :
    ComputableInPolyTime
      (fun a => rompelCandidateEval G (n a) (q a) (K a) (x a))
      encIn encBits := by
  have hout := G.polyTime_outLen.comp hn
  have hshrink := G.polyTime_shrinkLen.comp hn
  have hsteps := (computableInPolyTime_rompelCascadeSteps G).comp hn
  have hy := ComputableInPolyTime.bitsRowWithInput (G.polyTime_inLen.comp hn) (.const 0) hK
  have hmasks := ComputableInPolyTime.bitsDropWithInput hK (G.polyTime_inLen.comp hn)
  have hp1 := ComputableInPolyTime.fst encIn encBits
  have hstep := computableInPolyTime_rompelShiftedStep G (hn.comp hp1) (hq.comp hp1) (hy.comp hp1)
    (ComputableInPolyTime.snd encIn encBits)
  exact computableInPolyTime_shoupCascade hout hshrink hsteps hstep
    (fun _ w _ => length_rompelShiftedStep G _ _ _ w) hmasks hx

/-- Step-`i` (`1 ≤ i ≤ rompelCascadeSteps G n`) `G.inLen n`-bit input fed to
`rompelShiftedStep G n q (BitString.listRow (G.inLen n) 0 K)` during
`rompelCandidateEval G n q K x`. -/
@[expose]
def rompelCascadeInput (G : ShrinkingCollisionGrid) (n q i : ℕ) (K x : List Bool) : List Bool :=
  let y := BitString.listRow (G.inLen n) 0 K
  let masks := K.drop (G.inLen n)
  shoupStepInput (G.outLen n) (G.shrinkLen n) masks x i
    (shoupState (G.outLen n) (G.shrinkLen n) (rompelShiftedStep G n q y) masks x (i - 1))

@[simp]
theorem length_rompelCascadeInput (G : ShrinkingCollisionGrid) (n q i : ℕ)
    (K x : List Bool) :
    (rompelCascadeInput G n q i K x).length = G.inLen n := by
  unfold rompelCascadeInput
  rw [length_shoupStepInput, G.outLen_add_shrink n]

@[fun_prop]
theorem computableInPolyTime_rompelCascadeInput (G : ShrinkingCollisionGrid)
    {γ : Type} {encIn : γ ↪ List Bool}
    {n q i : γ → ℕ} {K x : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hq : ComputableInPolyTime q encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary)
    (hK : ComputableInPolyTime K encIn encBits)
    (hx : ComputableInPolyTime x encIn encBits) :
    ComputableInPolyTime
      (fun a => rompelCascadeInput G (n a) (q a) (i a) (K a) (x a))
      encIn encBits := by
  have hout := G.polyTime_outLen.comp hn
  have hshrink := G.polyTime_shrinkLen.comp hn
  have hin := G.polyTime_inLen.comp hn
  have hy := ComputableInPolyTime.bitsRowWithInput hin (.const 0) hK
  have hmasks := ComputableInPolyTime.bitsDropWithInput hK hin
  have hp1 := ComputableInPolyTime.fst encIn encBits
  have hstep :
      ComputableInPolyTime
        (fun p : γ × List Bool =>
          rompelShiftedStep G (n p.1) (q p.1)
            (BitString.listRow (G.inLen (n p.1)) 0 (K p.1)) p.2)
        (encPair encIn encBits) encBits :=
    computableInPolyTime_rompelShiftedStep G (hn.comp hp1) (hq.comp hp1) (hy.comp hp1)
      (ComputableInPolyTime.snd encIn encBits)
  have hstate := computableInPolyTime_shoupState
    (step := fun a w => rompelShiftedStep G (n a) (q a)
      (BitString.listRow (G.inLen (n a)) 0 (K a)) w)
    hout hshrink (hi.unary_sub' (.const 1)) hstep
    (fun _ w _ => length_rompelShiftedStep G _ _ _ w) hmasks hx
  unfold rompelCascadeInput shoupStepInput shoupChunk
  have hmaskRow := ComputableInPolyTime.bitsRowWithInput hout
    (computableInPolyTime_padicValNat_two.comp hi) hmasks
  have hchunk := ComputableInPolyTime.bitsRowWithInput hshrink (hi.unary_sub' (.const 1))
    (ComputableInPolyTime.bitsDropWithInput hx hout)
  exact ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsXorWithInput hout
      (.of_tidy (ComputableTidilyInPolyTime.cons' hstate.tidy
        (ComputableTidilyInPolyTime.cons' hmaskRow.tidy (ComputableTidilyInPolyTime.const [])))))
    hchunk

/-- **Deterministic step-collision extraction (`[Shoup2000]`, `[HHRVW2020]`, Section 5.1.4,
Lemma 5.7, p. 30)**: if two distinct `2 * rompelBlockLen G n`-bit inputs `x₀ ≠ x₁` collide under
`rompelCandidateEval G n q K`, there exists a step `1 ≤ i ≤ rompelCascadeSteps G n` where their
`G.inLen n`-bit step inputs `rompelCascadeInput G n q i K` are distinct yet collide under
`rompelShiftedStep G n q (BitString.listRow (G.inLen n) 0 K)`. -/
theorem exists_rompelCascadeInput_collision (G : ShrinkingCollisionGrid)
    {n q : ℕ} {K x₀ x₁ : List Bool}
    (hx₀ : x₀.length = 2 * rompelBlockLen G n)
    (hx₁ : x₁.length = 2 * rompelBlockLen G n)
    (hne : x₀ ≠ x₁)
    (hcol : rompelCandidateEval G n q K x₀ = rompelCandidateEval G n q K x₁) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ rompelCascadeSteps G n ∧
      rompelCascadeInput G n q i K x₀ ≠ rompelCascadeInput G n q i K x₁ ∧
      rompelShiftedStep G n q (BitString.listRow (G.inLen n) 0 K)
          (rompelCascadeInput G n q i K x₀) =
        rompelShiftedStep G n q (BitString.listRow (G.inLen n) 0 K)
          (rompelCascadeInput G n q i K x₁) :=
  exists_shoupCascade_step_collision (G.shrinkLen_pos n)
    (calc
      G.outLen n = 1 * G.outLen n := (one_mul _).symm
      _ ≤ G.gridCount n * G.outLen n := Nat.mul_le_mul_right _ (G.gridCount_pos n)
      _ ≤ 2 * (G.gridCount n * G.outLen n) := by omega)
    (two_mul_rompelBlockLen_le G n)
    (rompelShiftedStep G n q (BitString.listRow (G.inLen n) 0 K))
    (fun w _ => length_rompelShiftedStep G n q _ w)
    (K.drop (G.inLen n)) x₀ x₁ hx₀ hx₁ hne hcol

/-! ### `gridCount n`-way candidate concatenation (adapting `[HHRVW2020]`, STEP 5(iii), p. 32) -/

/-- **`gridCount n`-way concatenated compression evaluator** (adapting `[HHRVW2020]`, Section 5.1.5,
STEP 5(iii), p. 32): evaluates `rompelCandidateEval G n q K x` for every `0 ≤ q < G.gridCount n`
under the shared key sequence `K` and concatenates the `G.outLen n`-bit digests into a
`rompelBlockLen G n`-bit block.
-/
def rompelCompressionEval (G : ShrinkingCollisionGrid) (n : ℕ) (K x : List Bool) : List Bool :=
  (List.range (G.gridCount n)).flatMap fun q => rompelCandidateEval G n q K x

@[simp]
theorem length_rompelCompressionEval (G : ShrinkingCollisionGrid) (n : ℕ) (K x : List Bool) :
    (rompelCompressionEval G n K x).length = rompelBlockLen G n := by
  have hmap : List.map (fun q => (rompelCandidateEval G n q K x).length)
      (List.range (G.gridCount n)) = List.replicate (G.gridCount n) (G.outLen n) := by
    rw [List.eq_replicate_iff]
    refine ⟨by simp, fun len hmem => ?_⟩
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hmem
    exact length_rompelCandidateEval G n q K x
  rw [rompelCompressionEval, List.length_flatMap, hmap, List.sum_replicate, smul_eq_mul,
    rompelBlockLen]

theorem listRow_rompelCompressionEval (G : ShrinkingCollisionGrid) (n : ℕ) (K x : List Bool)
    {q : ℕ} (hq : q < G.gridCount n) :
    BitString.listRow (G.outLen n) q (rompelCompressionEval G n K x) =
      rompelCandidateEval G n q K x := by
  have h := BitString.listRow_flatMap_append
    (width := G.outLen n)
    (fun idx => rompelCandidateEval G n idx K x)
    (List.range (G.gridCount n))
    (fun idx _ => length_rompelCandidateEval G n idx K x)
    [] q (by simpa only [List.length_range] using hq)
  simpa only [rompelCompressionEval, List.append_nil, List.getElem_range] using h

@[fun_prop]
theorem computableInPolyTime_rompelCompressionEval (G : ShrinkingCollisionGrid) :
    ComputableInPolyTime
      (fun ⟨n, K, x⟩ => rompelCompressionEval G n K x)
      (encPair encUnary (encPair encBits encBits)) encBits := by
  let encIn := encPair encUnary (encPair encBits encBits)
  unfold rompelCompressionEval
  apply ComputableInPolyTime.flatMapToBitsWithInput
    (ComputableInPolyTime.unary_range' (G.polyTime_gridCount.comp (ComputableInPolyTime.fst _ _)))
  have hp1 := ComputableInPolyTime.fst encIn encUnary
  have hrest := (ComputableInPolyTime.snd encUnary (encPair encBits encBits)).comp hp1
  exact computableInPolyTime_rompelCandidateEval G
    ((ComputableInPolyTime.fst encUnary (encPair encBits encBits)).comp hp1)
    (ComputableInPolyTime.snd encIn encUnary)
    ((ComputableInPolyTime.fst encBits encBits).comp hrest)
    ((ComputableInPolyTime.snd encBits encBits).comp hrest)

/-- **Rompel / HHRVW halving `KeyedCompressionFamily`** (adapting `[Shoup2000]`;
`[HHRVW2020]`, Section 5.1.5, STEP 4 and STEP 5(ii–iii), pp. 31–32): compresses
`2 * rompelBlockLen G n`-bit blocks to `rompelBlockLen G n`-bit blocks under shared
`O(|y| log t)` Shoup XOR-masking keys (`rompelKeyLen G n`). -/
@[expose]
def rompelCompression (G : ShrinkingCollisionGrid) : KeyedCompressionFamily where
  keyLen := rompelKeyLen G
  blockLen := rompelBlockLen G
  eval := rompelCompressionEval G
  keyLen_polyTime := computableInPolyTime_rompelKeyLen G
  blockLen_polyTime := computableInPolyTime_rompelBlockLen G
  polyTime := computableInPolyTime_rompelCompressionEval G
  le_blockLen := le_rompelBlockLen G
  length_eq n K x _ _ := length_rompelCompressionEval G n K x

/-- **`[HHRVW2020]` Lemma 5.7 `O(|y| log t)` key-length bound** directly on
`(rompelCompression G).keyLen`. -/
theorem ShrinkingCollisionGrid.rompelCompression_keyLen_le
    (G : ShrinkingCollisionGrid) (n : ℕ) :
    (rompelCompression G).keyLen n ≤ (Nat.log 2 (rompelCascadeSteps G n) + 2) * G.inLen n :=
  rompelKeyLen_le G n

/-! ### Single-stage planted-subkey reduction to `randomCollisionGame` -/

private def clampIdx (bound guess : ℕ) : ℕ :=
  (bound - 1) - ((bound - 1) - guess)

private theorem clampIdx_eq_of_lt {bound guess : ℕ} (h : guess < bound) :
    clampIdx bound guess = guess := by
  unfold clampIdx
  omega

private theorem computableInPolyTime_clampIdx {γ : Type} {encIn : γ ↪ List Bool}
    {bound guess : γ → ℕ}
    (hb : ComputableInPolyTime bound encIn encUnary)
    (hg : ComputableInPolyTime guess encIn encUnary) :
    ComputableInPolyTime (fun a => clampIdx (bound a) (guess a)) encIn encUnary :=
  have hb1 := hb.unary_sub' (.const 1)
  hb1.unary_sub' (hb1.unary_sub' hg)

private def pairXor (m : ℕ) (u v : List Bool) : List Bool :=
  BitString.listXor m [u, v]

private theorem computableInPolyTime_pairXor {γ : Type} {encIn : γ ↪ List Bool}
    {m : γ → ℕ} {u v : γ → List Bool}
    (hm : ComputableInPolyTime m encIn encUnary)
    (hu : ComputableInPolyTime u encIn encBits)
    (hv : ComputableInPolyTime v encIn encBits) :
    ComputableInPolyTime (fun a => pairXor (m a) (u a) (v a)) encIn encBits :=
  ComputableInPolyTime.bitsXorWithInput hm
    (.of_tidy (ComputableTidilyInPolyTime.cons' hu.tidy
      (ComputableTidilyInPolyTime.cons' hv.tidy (ComputableTidilyInPolyTime.const []))))

private def rompelSlotIdx (G : ShrinkingCollisionGrid) (n slot : ℕ) : ℕ :=
  min (slot + 1) (rompelCascadeSteps G n)

private theorem computableInPolyTime_rompelSlotIdx (G : ShrinkingCollisionGrid)
    {γ : Type} {encIn : γ ↪ List Bool} {n slot : γ → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hslot : ComputableInPolyTime slot encIn encUnary) :
    ComputableInPolyTime (fun a => rompelSlotIdx G (n a) (slot a)) encIn encUnary := by
  unfold rompelSlotIdx
  exact (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_min).comp
    ((hslot.unary_add' (.const 1)).prod ((computableInPolyTime_rompelCascadeSteps G).comp hn))

private def rompelPlantedWord (G : ShrinkingCollisionGrid) (n slot : ℕ)
    (x₀ T : List Bool) : List Bool :=
  let iStar := rompelSlotIdx G n slot
  BitString.listRow (G.outLen n) (padicValNat 2 iStar) T ++
    shoupChunk (G.outLen n) (G.shrinkLen n) iStar x₀

private theorem length_rompelPlantedWord (G : ShrinkingCollisionGrid) (n slot : ℕ)
    (x₀ T : List Bool) :
    (rompelPlantedWord G n slot x₀ T).length = G.inLen n := by
  unfold rompelPlantedWord
  rw [List.length_append, BitString.length_listRow, length_shoupChunk, G.outLen_add_shrink n]

private theorem computableInPolyTime_rompelPlantedWord (G : ShrinkingCollisionGrid)
    {γ : Type} {encIn : γ ↪ List Bool} {n slot : γ → ℕ} {x₀ T : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hslot : ComputableInPolyTime slot encIn encUnary)
    (hx₀ : ComputableInPolyTime x₀ encIn encBits)
    (hT : ComputableInPolyTime T encIn encBits) :
    ComputableInPolyTime
      (fun a => rompelPlantedWord G (n a) (slot a) (x₀ a) (T a))
      encIn encBits := by
  have hi := computableInPolyTime_rompelSlotIdx G hn hslot
  have hout := G.polyTime_outLen.comp hn
  have hs := G.polyTime_shrinkLen.comp hn
  unfold rompelPlantedWord shoupChunk
  exact ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsRowWithInput hout (computableInPolyTime_padicValNat_two.comp hi) hT)
    (ComputableInPolyTime.bitsRowWithInput hs (hi.unary_sub' (.const 1))
      (ComputableInPolyTime.bitsDropWithInput hx₀ hout))

private def rompelYStar (G : ShrinkingCollisionGrid) (n slot : ℕ)
    (zWord x₀ T : List Bool) : List Bool :=
  pairXor (G.inLen n) zWord (rompelPlantedWord G n slot x₀ T)

private theorem computableInPolyTime_rompelYStar (G : ShrinkingCollisionGrid)
    {γ : Type} {encIn : γ ↪ List Bool} {n slot : γ → ℕ} {zWord x₀ T : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hslot : ComputableInPolyTime slot encIn encUnary)
    (hz : ComputableInPolyTime zWord encIn encBits)
    (hx₀ : ComputableInPolyTime x₀ encIn encBits)
    (hT : ComputableInPolyTime T encIn encBits) :
    ComputableInPolyTime
      (fun a => rompelYStar G (n a) (slot a) (zWord a) (x₀ a) (T a))
      encIn encBits :=
  computableInPolyTime_pairXor (G.polyTime_inLen.comp hn) hz
    (computableInPolyTime_rompelPlantedWord G hn hslot hx₀ hT)

private def rompelStageMasks (G : ShrinkingCollisionGrid) (n qGuess slot : ℕ)
    (zWord x₀ T : List Bool) : List Bool :=
  let q := clampIdx (G.gridCount n) qGuess
  let iStar := rompelSlotIdx G n slot
  let yStar := rompelYStar G n slot zWord x₀ T
  shoupPackMasks (G.outLen n) (G.shrinkLen n) (rompelCascadeSteps G n) iStar
    (rompelShiftedStep G n q yStar) x₀ T

private theorem computableInPolyTime_rompelStageMasks (G : ShrinkingCollisionGrid)
    {γ : Type} {encIn : γ ↪ List Bool} {n qGuess slot : γ → ℕ}
    {zWord x₀ T : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hq : ComputableInPolyTime qGuess encIn encUnary)
    (hslot : ComputableInPolyTime slot encIn encUnary)
    (hz : ComputableInPolyTime zWord encIn encBits)
    (hx₀ : ComputableInPolyTime x₀ encIn encBits)
    (hT : ComputableInPolyTime T encIn encBits) :
    ComputableInPolyTime
      (fun a => rompelStageMasks G (n a) (qGuess a) (slot a) (zWord a) (x₀ a) (T a))
      encIn encBits := by
  have hyStar := computableInPolyTime_rompelYStar G hn hslot hz hx₀ hT
  have hqC := computableInPolyTime_clampIdx (G.polyTime_gridCount.comp hn) hq
  have hp1 := ComputableInPolyTime.fst encIn encBits
  have hstep := computableInPolyTime_rompelShiftedStep G (hn.comp hp1) (hqC.comp hp1)
    (hyStar.comp hp1) (ComputableInPolyTime.snd encIn encBits)
  exact computableInPolyTime_shoupPackMasks
    (G.polyTime_outLen.comp hn)
    (G.polyTime_shrinkLen.comp hn)
    ((computableInPolyTime_rompelCascadeSteps G).comp hn)
    (computableInPolyTime_rompelSlotIdx G hn hslot)
    hstep (fun _ w _ => length_rompelShiftedStep G _ _ _ w) hx₀ hT

private def rompelUnmaskWord (G : ShrinkingCollisionGrid) (n qGuess slot : ℕ)
    (zWord x₀ T x₁ : List Bool) : List Bool :=
  let q := clampIdx (G.gridCount n) qGuess
  let iStar := rompelSlotIdx G n slot
  let yStar := rompelYStar G n slot zWord x₀ T
  let masks := rompelStageMasks G n qGuess slot zWord x₀ T
  pairXor (G.inLen n) (rompelCascadeInput G n q iStar (yStar ++ masks) x₁) yStar

private theorem computableInPolyTime_rompelUnmaskWord (G : ShrinkingCollisionGrid)
    {γ : Type} {encIn : γ ↪ List Bool} {n qGuess slot : γ → ℕ}
    {zWord x₀ T x₁ : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hq : ComputableInPolyTime qGuess encIn encUnary)
    (hslot : ComputableInPolyTime slot encIn encUnary)
    (hz : ComputableInPolyTime zWord encIn encBits)
    (hx₀ : ComputableInPolyTime x₀ encIn encBits)
    (hT : ComputableInPolyTime T encIn encBits)
    (hx₁ : ComputableInPolyTime x₁ encIn encBits) :
    ComputableInPolyTime
      (fun a => rompelUnmaskWord G (n a) (qGuess a) (slot a) (zWord a) (x₀ a) (T a) (x₁ a))
      encIn encBits := by
  have hyStar := computableInPolyTime_rompelYStar G hn hslot hz hx₀ hT
  have hmasks := computableInPolyTime_rompelStageMasks G hn hq hslot hz hx₀ hT
  exact computableInPolyTime_pairXor (G.polyTime_inLen.comp hn)
    (computableInPolyTime_rompelCascadeInput G hn
      (computableInPolyTime_clampIdx (G.polyTime_gridCount.comp hn) hq)
      (computableInPolyTime_rompelSlotIdx G hn hslot)
      (ComputableInPolyTime.bitsAppend hyStar hmasks) hx₁)
    hyStar

private noncomputable def rompelInverterStage1 (G : ShrinkingCollisionGrid)
    (adversary : TargetCollisionFinder) (n : ℕ) :
    ProbComp ((ℕ × ℕ) × (List Bool × List Bool)) := do
  let qGuess ← sampleDyadicIndex (G.gridCount n)
  let slot ← sampleDyadicIndex (rompelCascadeSteps G n)
  let choice ← adversary.choose n
  return ((qGuess, slot), choice)

private theorem isPPTOn_rompelInverterStage1 (G : ShrinkingCollisionGrid)
    {adversary : TargetCollisionFinder} (ha : adversary.IsPPT) :
    IsPPTOn encUnary (encPair (encPair encUnary encUnary) (encPair encBits encBits))
      (rompelInverterStage1 G adversary) := by
  have hq := isPPTOn_sampleDyadicIndex G.polyTime_gridCount
  have hslot := isPPTOn_sampleDyadicIndex
    ((computableInPolyTime_rompelCascadeSteps G).comp (ComputableInPolyTime.fst encUnary encUnary))
  have hch := ha.choose.preprocess ((ComputableInPolyTime.fst encUnary encUnary).comp
    (ComputableInPolyTime.fst (encPair encUnary encUnary) encUnary))
  have hx1 := ComputableInPolyTime.fst
    (encPair (encPair encUnary encUnary) encUnary) (encPair encBits encBits)
  have hqG := (ComputableInPolyTime.snd encUnary encUnary).comp
    ((ComputableInPolyTime.fst (encPair encUnary encUnary) encUnary).comp hx1)
  have hsl := (ComputableInPolyTime.snd (encPair encUnary encUnary) encUnary).comp hx1
  exact hq.bind_with (hslot.bind_with (hch.bind_with
    (ComputableInPolyTime.isPPTOn ((hqG.prod hsl).prod (ComputableInPolyTime.snd _ _)))))

private noncomputable def rompelInverterStage2 (G : ShrinkingCollisionGrid)
    (adversary : TargetCollisionFinder) (n : ℕ) (zWord : List Bool)
    (s : (ℕ × ℕ) × (List Bool × List Bool)) : ProbComp (List Bool) := do
  let T ← BitString.sampleList (shoupMasksLen (G.outLen n) (rompelCascadeSteps G n))
  let yStar := rompelYStar G n s.1.2 zWord s.2.1 T
  let masks := rompelStageMasks G n s.1.1 s.1.2 zWord s.2.1 T
  let x₁ ← adversary.find n s.2.2 (yStar ++ masks)
  return rompelUnmaskWord G n s.1.1 s.1.2 zWord s.2.1 T x₁

private theorem isPPTOn_rompelInverterStage2 (G : ShrinkingCollisionGrid)
    {adversary : TargetCollisionFinder} (ha : adversary.IsPPT) :
    IsPPTOn
      (encPair (encPair encUnary encBits)
        (encPair (encPair encUnary encUnary) (encPair encBits encBits)))
      encBits
      (fun p => rompelInverterStage2 G adversary p.1.1 p.1.2 p.2) := by
  let encL := encPair encUnary encBits
  let encR := encPair (encPair encUnary encUnary) (encPair encBits encBits)
  let enc0 := encPair encL encR
  let enc1 := encPair enc0 encBits
  let enc2 := encPair enc1 encBits
  have h0_l := ComputableInPolyTime.fst encL encR
  have h0_r := ComputableInPolyTime.snd encL encR
  have h0_n := (ComputableInPolyTime.fst encUnary encBits).comp h0_l
  have h0_z := (ComputableInPolyTime.snd encUnary encBits).comp h0_l
  have h0_qs :=
    (ComputableInPolyTime.fst (encPair encUnary encUnary) (encPair encBits encBits)).comp h0_r
  have h0_ch :=
    (ComputableInPolyTime.snd (encPair encUnary encUnary) (encPair encBits encBits)).comp h0_r
  have h0_qG := (ComputableInPolyTime.fst encUnary encUnary).comp h0_qs
  have h0_slot := (ComputableInPolyTime.snd encUnary encUnary).comp h0_qs
  have h0_x0 := (ComputableInPolyTime.fst encBits encBits).comp h0_ch
  have h0_st := (ComputableInPolyTime.snd encBits encBits).comp h0_ch
  have hmLen := computableInPolyTime_shoupMasksLen
    (G.polyTime_outLen.comp h0_n) ((computableInPolyTime_rompelCascadeSteps G).comp h0_n)
  have h1_p := ComputableInPolyTime.fst enc0 encBits
  have h1_T := ComputableInPolyTime.snd enc0 encBits
  have h1_n := h0_n.comp h1_p
  have h1_z := h0_z.comp h1_p
  have h1_qG := h0_qG.comp h1_p
  have h1_slot := h0_slot.comp h1_p
  have h1_x0 := h0_x0.comp h1_p
  have h1_st := h0_st.comp h1_p
  have hK := ComputableInPolyTime.bitsAppend
    (computableInPolyTime_rompelYStar G h1_n h1_slot h1_z h1_x0 h1_T)
    (computableInPolyTime_rompelStageMasks G h1_n h1_qG h1_slot h1_z h1_x0 h1_T)
  have h2_q := ComputableInPolyTime.fst enc1 encBits
  exact hmLen.sampleList.bind_with
    ((ha.find.preprocess (h1_n.prod (h1_st.prod hK))).bind_with
      (ComputableInPolyTime.isPPTOn
        (computableInPolyTime_rompelUnmaskWord G
          (h1_n.comp h2_q) (h1_qG.comp h2_q) (h1_slot.comp h2_q)
          (h1_z.comp h2_q) (h1_x0.comp h2_q) (h1_T.comp h2_q)
          (ComputableInPolyTime.snd enc1 encBits))))

/-- Uniform strict-PPT reduction from `targetCollisionGame` on `rompelCompression G` to
`randomCollisionGame` on `G`: guess dyadic indices `(qGuess, slot)`, clamp to valid ranges,
run `adversary.choose n`, sample `shoupMasksLen` template bits `T`, plant `zWord ⊕ w₀(T)` at
step `i*` via `shoupPackMasks`, run `adversary.find`, and unmask via `rompelUnmaskWord`. -/
noncomputable def rompelCompressionInverter (G : ShrinkingCollisionGrid)
    (adversary : TargetCollisionFinder) (n : ℕ) (zWord : List Bool) : ProbComp (List Bool) := do
  let s ← rompelInverterStage1 G adversary n
  rompelInverterStage2 G adversary n zWord s

private theorem isPPT_bind_stages {α β : Type} {encα : α ↪ List Bool}
    {encβ : β ↪ List Bool} {f₁ : ℕ → ProbComp α} {f₂ : ℕ → List Bool → α → ProbComp β}
    (hf₁ : IsPPTOn encUnary encα f₁)
    (hf₂ : IsPPTOn (encPair (encPair encUnary encBits) encα) encβ
      (fun p => f₂ p.1.1 p.1.2 p.2)) :
    IsPPT encβ (fun n z => do
      let s ← f₁ n
      f₂ n z s) := by
  have hp := hf₁.preprocess (input := encPair encUnary encBits)
    (prepare := fun p : ℕ × List Bool => p.1) (ComputableInPolyTime.fst encUnary encBits)
  exact (hp.bind_with (second := fun p s => f₂ p.1 p.2 s) hf₂).isPPT

/-- `rompelCompressionInverter G adversary` is uniformly strict PPT whenever `adversary` is a strict
PPT `TargetCollisionFinder`. -/
theorem isPPT_rompelCompressionInverter (G : ShrinkingCollisionGrid)
    {adversary : TargetCollisionFinder} (ha : adversary.IsPPT) :
    IsPPT encBits (rompelCompressionInverter G adversary) :=
  isPPT_bind_stages (isPPTOn_rompelInverterStage1 G ha) (isPPTOn_rompelInverterStage2 G ha)

private noncomputable def rompelTargetDist (G : ShrinkingCollisionGrid)
    (adversary : TargetCollisionFinder) (n : ℕ) :
    PMF ((List Bool × List Bool) × List Bool × List Bool) := do
  let choice ← ProbComp.eval (adversary.choose n)
  let K ← BitString.uniformList (rompelKeyLen G n)
  (ProbComp.eval (adversary.find n choice.2 K)).map fun x₁ => (choice, K, x₁)

private noncomputable def rompelInverterTrial (G : ShrinkingCollisionGrid)
    (adversary : TargetCollisionFinder) (n qStar qGuess slot : ℕ) : Game := do
  let W := G.inLen n
  let B := G.outLen n
  let S := rompelCascadeSteps G n
  let zWord ← BitString.uniformList W
  let choice ← ProbComp.eval (adversary.choose n)
  let T ← BitString.uniformList (shoupMasksLen B S)
  let q := clampIdx (G.gridCount n) qGuess
  let iStar := rompelSlotIdx G n slot
  let w₀ := rompelPlantedWord G n slot choice.1 T
  let yStar := BitString.listXor W [zWord, w₀]
  let masks := shoupPackMasks B (G.shrinkLen n) S iStar
    (rompelShiftedStep G n q yStar) choice.1 T
  let x₁ ← ProbComp.eval (adversary.find n choice.2 (yStar ++ masks))
  let w₁ := rompelCascadeInput G n q iStar (yStar ++ masks) x₁
  let zWord' := BitString.listXor W [w₁, yStar]
  return decide (zWord'.length = W ∧ zWord' ≠ zWord ∧
    G.evalGrid n qStar zWord' = G.evalGrid n qStar zWord)

private def rompelSlotCollisionEvent (G : ShrinkingCollisionGrid) (n qStar slot : ℕ)
    (t : (List Bool × List Bool) × List Bool × List Bool) : Bool :=
  if slot < rompelCascadeSteps G n then
    let iStar := slot + 1
    let y := BitString.listRow (G.inLen n) 0 t.2.1
    let w₀ := rompelCascadeInput G n qStar iStar t.2.1 t.1.1
    let w₁ := rompelCascadeInput G n qStar iStar t.2.1 t.2.2
    decide (w₀ ≠ w₁ ∧ rompelShiftedStep G n qStar y w₀ = rompelShiftedStep G n qStar y w₁)
  else false

private theorem rompelInverterTrial_eq_map_slotCollisionEvent
    (G : ShrinkingCollisionGrid) (adversary : TargetCollisionFinder)
    {n qStar slot : ℕ} (hqStar : qStar < G.gridCount n) (hs : slot < rompelCascadeSteps G n) :
    rompelInverterTrial G adversary n qStar qStar slot =
      (rompelTargetDist G adversary n).map (rompelSlotCollisionEvent G n qStar slot) := by
  let W := G.inLen n
  let B := G.outLen n
  let S := rompelCascadeSteps G n
  let iStar := slot + 1
  have hi_pos : 1 ≤ iStar := Nat.succ_pos slot
  have hi_le : iStar ≤ S := hs
  have hslot_idx : rompelSlotIdx G n slot = iStar := by
    dsimp only [rompelSlotIdx, S, iStar]
    exact Nat.min_eq_left hs
  have hkey_len : rompelKeyLen G n = W + shoupMasksLen B S := rfl
  simp only [rompelInverterTrial, rompelSlotCollisionEvent, rompelTargetDist, hs,
    clampIdx_eq_of_lt hqStar, hslot_idx, ↓reduceIte,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map, PMF.bind_bind, PMF.pure_bind,
    Function.comp_def]
  rw [PMF.bind_comm (BitString.uniformList W) (ProbComp.eval (adversary.choose n))]
  refine PMF.bind_congr_on_support _ _ _ fun choice _ => ?_
  rw [PMF.bind_comm (BitString.uniformList W) (BitString.uniformList (shoupMasksLen B S))]
  let post (yStar masks : List Bool) : PMF Bool :=
    (ProbComp.eval (adversary.find n choice.2 (yStar ++ masks))).bind fun x₁ =>
      let w₀ := rompelCascadeInput G n qStar iStar (yStar ++ masks) choice.1
      let w₁ := rompelCascadeInput G n qStar iStar (yStar ++ masks) x₁
      PMF.pure (decide (w₀ ≠ w₁ ∧
        rompelShiftedStep G n qStar yStar w₀ = rompelShiftedStep G n qStar yStar w₁))
  have hrew :
      (BitString.uniformList (shoupMasksLen B S)).bind (fun T =>
        (BitString.uniformList W).bind fun zWord =>
          let w₀ := rompelPlantedWord G n slot choice.1 T
          let yStar := BitString.listXor W [zWord, w₀]
          let masks := shoupPackMasks B (G.shrinkLen n) S iStar
            (rompelShiftedStep G n qStar yStar) choice.1 T
          (ProbComp.eval (adversary.find n choice.2 (yStar ++ masks))).bind fun x₁ =>
            let w₁ := rompelCascadeInput G n qStar iStar (yStar ++ masks) x₁
            let zWord' := BitString.listXor W [w₁, yStar]
            PMF.pure (decide (zWord'.length = W ∧ zWord' ≠ zWord ∧
              G.evalGrid n qStar zWord' = G.evalGrid n qStar zWord))) =
      (BitString.uniformList (shoupMasksLen B S)).bind fun T =>
        (BitString.uniformList W).bind fun zWord =>
          let w₀ := rompelPlantedWord G n slot choice.1 T
          let yStar := BitString.listXor W [zWord, w₀]
          post yStar (shoupPackMasks B (G.shrinkLen n) S iStar
            (rompelShiftedStep G n qStar yStar) choice.1 T) := by
    refine PMF.bind_congr_on_support _ _ _ fun T _ =>
      PMF.bind_congr_on_support _ _ _ fun zWord hzWord => ?_
    have hz_len : zWord.length = W := BitString.length_of_mem_support_uniformList hzWord
    let w₀ := rompelPlantedWord G n slot choice.1 T
    have hw₀_len : w₀.length = W := length_rompelPlantedWord G n slot choice.1 T
    let yStar := BitString.listXor W [zWord, w₀]
    have hy_len : yStar.length = W := BitString.length_listXor W _
    have hz_rec : BitString.listXor W [w₀, yStar] = zWord := by
      dsimp only [yStar]
      rw [BitString.listXor_pair_comm W zWord w₀,
        BitString.listXor_pair_self_left_of_length w₀ hz_len]
    let masks := shoupPackMasks B (G.shrinkLen n) S iStar
      (rompelShiftedStep G n qStar yStar) choice.1 T
    have hstep_len : ∀ w, w.length = B + G.shrinkLen n →
        (rompelShiftedStep G n qStar yStar w).length = B :=
      fun w _ => length_rompelShiftedStep G n qStar yStar w
    have hrow_y : BitString.listRow W 0 (yStar ++ masks) = yStar := by
      rw [BitString.listRow_zero, BitString.ofFn_ofList_eq_take,
        List.take_append_of_le_length (by simp [hy_len]), List.take_left' hy_len]
    have hdrop_y : (yStar ++ masks).drop W = masks := List.drop_left' hy_len
    have hw₀_planted : rompelCascadeInput G n qStar iStar (yStar ++ masks) choice.1 = w₀ := by
      dsimp only [rompelCascadeInput]
      change shoupStepInput B (G.shrinkLen n) ((yStar ++ masks).drop W) choice.1 iStar
        (shoupState B (G.shrinkLen n)
          (rompelShiftedStep G n qStar (BitString.listRow W 0 (yStar ++ masks)))
          ((yStar ++ masks).drop W) choice.1 (iStar - 1)) = w₀
      rw [hrow_y, hdrop_y]
      rw [shoupStepInput_shoupPackMasks (rompelShiftedStep G n qStar yStar) hstep_len hi_pos hi_le
        choice.1 T]
      dsimp only [w₀, rompelPlantedWord, B]
      rw [hslot_idx]
    dsimp only [post]
    refine PMF.bind_congr_on_support _ _ _ fun x₁ _ => ?_
    let w₁ := rompelCascadeInput G n qStar iStar (yStar ++ masks) x₁
    have hw₁_len : w₁.length = W := length_rompelCascadeInput G n qStar iStar (yStar ++ masks) x₁
    have hne_iff : BitString.listXor W [w₁, yStar] ≠ zWord ↔ w₀ ≠ w₁ := by
      conv_lhs => rw [← hz_rec]
      exact ((BitString.listXor_pair_left_inj hw₁_len hw₀_len yStar).not).trans ne_comm
    have heval_iff :
        G.evalGrid n qStar (BitString.listXor W [w₁, yStar]) = G.evalGrid n qStar zWord ↔
          rompelShiftedStep G n qStar yStar w₀ = rompelShiftedStep G n qStar yStar w₁ := by
      dsimp only [rompelShiftedStep, W]
      rw [hz_rec, eq_comm]
    congr 1
    rw [hw₀_planted]
    exact decide_eq_decide.mpr
      ⟨fun ⟨_, hne, hev⟩ => ⟨hne_iff.mp hne, heval_iff.mp hev⟩,
       fun ⟨hne, hev⟩ => ⟨BitString.length_listXor W _, hne_iff.mpr hne, heval_iff.mpr hev⟩⟩
  have hxorshift :
      (BitString.uniformList (shoupMasksLen B S)).bind (fun T =>
        (BitString.uniformList W).bind fun zWord =>
          let w₀ := rompelPlantedWord G n slot choice.1 T
          let yStar := BitString.listXor W [zWord, w₀]
          post yStar (shoupPackMasks B (G.shrinkLen n) S iStar
            (rompelShiftedStep G n qStar yStar) choice.1 T)) =
      (BitString.uniformList (shoupMasksLen B S)).bind fun T =>
        (BitString.uniformList W).bind fun yStar =>
          post yStar (shoupPackMasks B (G.shrinkLen n) S iStar
            (rompelShiftedStep G n qStar yStar) choice.1 T) := by
    refine PMF.bind_congr_on_support _ _ _ fun T _ => ?_
    let w₀ := rompelPlantedWord G n slot choice.1 T
    have hm :
        (BitString.uniformList W).bind (fun zWord =>
          let yStar := BitString.listXor W [zWord, w₀]
          post yStar (shoupPackMasks B (G.shrinkLen n) S iStar
            (rompelShiftedStep G n qStar yStar) choice.1 T)) =
          ((BitString.uniformList W).map (fun zWord => BitString.listXor W [zWord, w₀])).bind
            (fun yStar => post yStar (shoupPackMasks B (G.shrinkLen n) S iStar
              (rompelShiftedStep G n qStar yStar) choice.1 T)) := by
      rw [PMF.bind_map]
      rfl
    rw [hm, BitString.uniformList_map_listXor W w₀]
  have hpackshift :
      (BitString.uniformList W).bind (fun yStar =>
        (BitString.uniformList (shoupMasksLen B S)).bind fun T =>
          post yStar (shoupPackMasks B (G.shrinkLen n) S iStar
            (rompelShiftedStep G n qStar yStar) choice.1 T)) =
      (BitString.uniformList W).bind fun yStar =>
        (BitString.uniformList (shoupMasksLen B S)).bind fun masks => post yStar masks := by
    refine PMF.bind_congr_on_support _ _ _ fun yStar _ => ?_
    have hstep_len : ∀ w, w.length = B + G.shrinkLen n →
        (rompelShiftedStep G n qStar yStar w).length = B :=
      fun w _ => length_rompelShiftedStep G n qStar yStar w
    have hm :
        (BitString.uniformList (shoupMasksLen B S)).bind (fun T =>
          post yStar (shoupPackMasks B (G.shrinkLen n) S iStar
            (rompelShiftedStep G n qStar yStar) choice.1 T)) =
          ((BitString.uniformList (shoupMasksLen B S)).map
            (shoupPackMasks B (G.shrinkLen n) S iStar
              (rompelShiftedStep G n qStar yStar) choice.1)).bind
            (fun masks => post yStar masks) := by
      rw [PMF.bind_map]
      rfl
    rw [hm, uniformList_map_shoupPackMasks B (G.shrinkLen n) S iStar
      (rompelShiftedStep G n qStar yStar) hstep_len hi_pos hi_le choice.1]
  rw [hrew, hxorshift, PMF.bind_comm, hpackshift,
    ← BitString.uniformList_bind_split W (shoupMasksLen B S) post, ← hkey_len]
  refine PMF.bind_congr_on_support _ _ _ fun K hK => ?_
  have hK_len : K.length = W + shoupMasksLen B S := by
    rw [← hkey_len]
    exact BitString.length_of_mem_support_uniformList hK
  have htake_drop : K.take W ++ K.drop W = K := List.take_append_drop W K
  have hrow0 : K.take W = BitString.listRow (G.inLen n) 0 K := by
    rw [BitString.listRow_zero, BitString.ofFn_ofList_eq_take,
      List.take_append_of_le_length (by omega)]
  dsimp only [post]
  rw [htake_drop]
  refine PMF.bind_congr_on_support _ _ _ fun x₁ _ => ?_
  congr 1
  exact decide_eq_decide.mpr (by rw [hrow0])

/-- **Concrete security bound for `rompelCompression G`**: at every candidate index
`qStar < G.gridCount n`, the target-collision success probability of `adversary` against
`rompelCompression G` is at most `dyadicSize (G.gridCount n) * dyadicSize (rompelCascadeSteps G n)`
times the random-collision success probability of `rompelCompressionInverter G adversary` against
candidate `qStar`. -/
theorem succProbability_targetCollisionGame_rompelCompression_le
    (G : ShrinkingCollisionGrid) (adversary : TargetCollisionFinder)
    {n qStar : ℕ} (hqStar : qStar < G.gridCount n) :
    Game.succProbability
      (ProbComp.eval
        (targetCollisionGame (rompelCompression G).keyLen (rompelCompression G).eval
          (rompelCompression G).validInput adversary n)) ≤
      (dyadicSize (G.gridCount n) * dyadicSize (rompelCascadeSteps G n) : ℝ≥0) *
        Game.succProbability
          (ProbComp.eval
            (randomCollisionGame (fun k => G.evalGrid k qStar) G.inLen
              (rompelCompressionInverter G adversary) n)) := by
  let W := G.inLen n
  let S := rompelCascadeSteps G n
  let Dq := dyadicSize (G.gridCount n)
  let Ds := dyadicSize S
  let μ := rompelTargetDist G adversary n
  let winComp (t : (List Bool × List Bool) × List Bool × List Bool) : Bool :=
    isCollision (rompelCompressionEval G n) (rompelCompression G).validInput n t.2.1 t.1.1 t.2.2
  let trial := rompelInverterTrial G adversary n qStar
  have hcomp_eq :
      ProbComp.eval
        (targetCollisionGame (rompelCompression G).keyLen (rompelCompression G).eval
          (rompelCompression G).validInput adversary n) =
        μ.map winComp := by
    simp only [targetCollisionGame, rompelCompression, rompelKeyLen, μ, rompelTargetDist, winComp,
      ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList, PMF.monad_bind_eq_bind,
      PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
  have hred_eq :
      ProbComp.eval
        (randomCollisionGame (fun k => G.evalGrid k qStar) G.inLen
          (rompelCompressionInverter G adversary) n) =
        (PMF.uniformOfFintype (Fin Dq × Fin Ds)).bind (fun p => trial p.1.val p.2.val) := by
    have h1 :
        ProbComp.eval
          (randomCollisionGame (fun k => G.evalGrid k qStar) G.inLen
            (rompelCompressionInverter G adversary) n) =
          (PMF.uniformOfFintype (Fin Dq)).bind fun a =>
            (PMF.uniformOfFintype (Fin Ds)).bind fun b => trial a.val b.val := by
      simp only [randomCollisionGame, rompelCompressionInverter, rompelInverterStage1,
        rompelInverterStage2, rompelYStar, rompelStageMasks, rompelUnmaskWord, pairXor, trial,
        rompelInverterTrial, ProbComp.eval_bind, ProbComp.eval_pure, eval_sampleDyadicIndex,
        BitString.eval_sampleList, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
        PMF.pure_bind, PMF.bind_map, Function.comp_def, S, Dq, Ds]
      rw [PMF.bind_comm (BitString.uniformList W) (PMF.uniformOfFintype (Fin Dq))]
      refine PMF.bind_congr_on_support _ _ _ fun a _ => ?_
      rw [PMF.bind_comm (BitString.uniformList W) (PMF.uniformOfFintype (Fin Ds))]
    rw [h1, ← PMF.uniformOfFintype_prod, PMF.bind_bind]
    refine PMF.bind_congr_on_support _ _ _ fun a _ => ?_
    rw [PMF.bind_map]
    rfl
  have hcover : ∀ t ∈ μ.support, winComp t = true →
      ∃ s : Fin Ds, rompelSlotCollisionEvent G n qStar s.val t = true := by
    intro t ht hW
    simp only [μ, rompelTargetDist, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff,
      PMF.mem_support_map_iff] at ht
    obtain ⟨choice, _, K, _, ⟨x₁, _, rfl⟩⟩ := ht
    rw [isCollision_eq_true_iff] at hW
    obtain ⟨hx₀_v, hx₁_v, hne, hcol⟩ := hW
    have hcand_col :
        rompelCandidateEval G n qStar K choice.1 = rompelCandidateEval G n qStar K x₁ := by
      rw [← listRow_rompelCompressionEval G n K choice.1 hqStar,
        ← listRow_rompelCompressionEval G n K x₁ hqStar, hcol]
    obtain ⟨i, hi_pos, hi_le, hw_ne, hw_col⟩ :=
      exists_rompelCascadeInput_collision G
        ((rompelCompression G).validInput_eq_true_iff.mp hx₀_v)
        ((rompelCompression G).validInput_eq_true_iff.mp hx₁_v)
        hne hcand_col
    have hs_lt : i - 1 < S := by omega
    have hs_lt' : i - 1 < rompelCascadeSteps G n := hs_lt
    refine ⟨⟨i - 1, hs_lt.trans (lt_dyadicSize S)⟩, ?_⟩
    have hi_eq : i - 1 + 1 = i := by omega
    simp only [rompelSlotCollisionEvent, hs_lt', ↓reduceIte, decide_eq_true_eq, hi_eq]
    exact ⟨hw_ne, hw_col⟩
  obtain ⟨val, hval⟩ : ∃ val : ℕ → ℕ → ℝ≥0∞, ∀ q i, (trial q i) true = val q i :=
    ⟨_, fun _ _ => rfl⟩
  have hsum_s : (μ.map winComp) true ≤ ∑ s : Fin Ds, val qStar s.val := by
    have hmono :
        (μ.map winComp) true ≤
          (μ.map (fun t => (List.range Ds).any
            (fun j => rompelSlotCollisionEvent G n qStar j t))) true := by
      refine PMF.map_true_mono μ fun t ht hW => ?_
      obtain ⟨⟨j, hj⟩, hs⟩ := hcover t ht hW
      exact List.any_eq_true.mpr ⟨j, List.mem_range.mpr hj, hs⟩
    refine (hmono.trans (PMF.map_any_range_true_le_sum μ Ds
      (rompelSlotCollisionEvent G n qStar))).trans ?_
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_le_sum fun j hj => ?_
    simp only [Finset.mem_range.mp hj, ↓reduceDIte, ← hval]
    by_cases hs : j < S
    · dsimp only [trial, μ]
      rw [rompelInverterTrial_eq_map_slotCollisionEvent G adversary hqStar hs]
    · have hWi : rompelSlotCollisionEvent G n qStar j = fun _ => false := funext fun t => by
        simp only [rompelSlotCollisionEvent, hs, ↓reduceIte, S]
      rw [hWi]
      simp
  let aStar : Fin Dq := ⟨qStar, hqStar.trans (lt_dyadicSize (G.gridCount n))⟩
  have hsum_prod :
      (μ.map winComp) true ≤ ∑ p : Fin Dq × Fin Ds, val p.1.val p.2.val :=
    hsum_s.trans (by
      rw [Fintype.sum_prod_type]
      exact Finset.single_le_sum (f := fun a : Fin Dq => ∑ y : Fin Ds, val a.val y.val)
        (fun _ _ => zero_le) (Finset.mem_univ aStar))
  have : Nonempty (Fin Dq) := ⟨aStar⟩
  have : Nonempty (Fin Ds) := ⟨⟨0, dyadicSize_pos S⟩⟩
  have hcard : (Fintype.card (Fin Dq × Fin Ds) : ℝ≥0) = (Dq * Ds : ℝ≥0) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  have hpos : (0 : ℝ≥0) < Dq * Ds :=
    mul_pos (by exact_mod_cast dyadicSize_pos _) (by exact_mod_cast dyadicSize_pos _)
  rw [hcomp_eq, hred_eq, Game.succProbability_uniform, hcard, mul_div_cancel₀ _ hpos.ne']
  have hsum_val_eq :
      (∑ p : Fin Dq × Fin Ds, Game.succProbability (trial p.1.val p.2.val)) =
        (∑ p : Fin Dq × Fin Ds, val p.1.val p.2.val).toNNReal := by
    rw [ENNReal.toNNReal_sum fun p _ => by rw [← hval]; exact PMF.apply_ne_top _ _]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Game.succProbability, hval]
  rw [hsum_val_eq]
  have hsum_ne_top : (∑ p : Fin Dq × Fin Ds, val p.1.val p.2.val) ≠ ⊤ :=
    ne_of_lt (ENNReal.sum_lt_top.mpr fun p _ => by
      rw [← hval]; exact (PMF.apply_ne_top _ _).lt_top)
  exact ENNReal.toNNReal_mono hsum_ne_top hsum_prod

/-- **Adapting `[HHRVW2020]`, Section 5.1.5, STEP 4 and STEP 5(ii–iii) (pp. 31–32)**: for any
`ShrinkingCollisionGrid` `G`, `rompelCompression G` is a target collision-resistant
`KeyedCompressionFamily`. -/
theorem ShrinkingCollisionGrid.targetCollisionResistant_rompelCompression
    (G : ShrinkingCollisionGrid) :
    (rompelCompression G).TargetCollisionResistant := by
  apply TargetCollisionResistantOn.of_negligible
  intro adversary hadversary
  have hinv_ppt : IsPPT encBits (rompelCompressionInverter G adversary) :=
    isPPT_rompelCompressionInverter G hadversary
  obtain ⟨goodIdx, hgood_lt, hneg_rand⟩ :=
    G.exists_good_candidate (rompelCompressionInverter G adversary) hinv_ppt
  have hdq_pb : PolynomiallyBounded (fun n => dyadicSize (G.gridCount n)) :=
    dyadicSize_polynomiallyBounded.comp G.polyTime_gridCount.polynomiallyBounded
  have hds_pb : PolynomiallyBounded (fun n => dyadicSize (rompelCascadeSteps G n)) :=
    dyadicSize_polynomiallyBounded.comp
      (computableInPolyTime_rompelCascadeSteps G).polynomiallyBounded
  have hloss_pb : PolynomiallyBounded
      (fun n => dyadicSize (G.gridCount n) * dyadicSize (rompelCascadeSteps G n)) :=
    hdq_pb.mul hds_pb
  have hbound_neg := hneg_rand.polynomiallyBounded_mul hloss_pb
  refine negligible_of_le hbound_neg fun n => ?_
  have hgame :
      randomCollisionGame (fun k => G.evalGrid k (goodIdx k)) G.inLen
        (rompelCompressionInverter G adversary) n =
      randomCollisionGame (fun k => G.evalGrid k (goodIdx n)) G.inLen
        (rompelCompressionInverter G adversary) n := rfl
  rw [hgame, Nat.cast_mul]
  exact succProbability_targetCollisionGame_rompelCompression_le G adversary (hgood_lt n)

/-! ### Unrestricted `KeyedHashFamily` and `OneWay` UOWHF endpoints -/

/-- **Rompel / HHRVW unrestricted `KeyedHashFamily`** (`[Rompel1990]`; `[HHRVW2020]`,
Section 5.1, Theorem 5.1, p. 26): hashes arbitrary-length bit strings `List Bool` to
`rompelBlockLen G n`-bit digests via `(rompelCompression G).treeHash` (inheriting `uowhfTreeHash`'s
`< 2 ^ n` finite-parameter tree capacity). -/
@[expose]
def rompelHash (G : ShrinkingCollisionGrid) : KeyedHashFamily :=
  (rompelCompression G).treeHash

/-- `rompelHash G` is unrestrictedly target collision-resistant on all `List Bool`. -/
theorem ShrinkingCollisionGrid.targetCollisionResistant_rompelHash
    (G : ShrinkingCollisionGrid) :
    (rompelHash G).TargetCollisionResistant :=
  KeyedCompressionFamily.targetCollisionResistant_treeHash
    G.targetCollisionResistant_rompelCompression

/-- **`[HHRVW2020]`, Section 5.1, Theorem 5.1 (p. 26) from Definition 3.9**: every
`AdversaryInaccessibleEntropyFamily` yields a target collision-resistant
`KeyedCompressionFamily`. -/
theorem AdversaryInaccessibleEntropyFamily.exists_targetCollisionResistantCompression
    (F : AdversaryInaccessibleEntropyFamily) :
    ∃ C : KeyedCompressionFamily, C.TargetCollisionResistant := by
  obtain ⟨G⟩ := F.exists_shrinkingCollisionGrid
  exact ⟨rompelCompression G, G.targetCollisionResistant_rompelCompression⟩

/-- **`[HHRVW2020]`, Section 5.1, Theorem 5.1 (p. 26) from Definition 3.9**: every
`AdversaryInaccessibleEntropyFamily` yields an unrestricted target collision-resistant
`KeyedHashFamily` on `List Bool`. -/
theorem AdversaryInaccessibleEntropyFamily.exists_targetCollisionResistantHash
    (F : AdversaryInaccessibleEntropyFamily) :
    ∃ H : KeyedHashFamily, H.TargetCollisionResistant := by
  obtain ⟨G⟩ := F.exists_shrinkingCollisionGrid
  exact ⟨rompelHash G, G.targetCollisionResistant_rompelHash⟩

/-- Every uniform `OneWay` function yields a target collision-resistant `KeyedCompressionFamily`. -/
theorem OneWay.exists_targetCollisionResistant_keyedCompressionFamily
    {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ C : KeyedCompressionFamily, C.TargetCollisionResistant := by
  obtain ⟨F⟩ := hf.exists_inaccessibleEntropyFamily
  exact F.toAdversaryInaccessibleEntropyFamily.exists_targetCollisionResistantCompression

/-- **Rompel–HHRVW universal one-way hash theorem** (`[Rompel1990]`; `[HHRVW2020]`,
Section 5.1, Theorem 5.1, p. 26): every uniform `OneWay` function implies the existence of an
unrestricted target collision-resistant `KeyedHashFamily` on `List Bool`. -/
theorem OneWay.exists_targetCollisionResistant_keyedHashFamily
    {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ H : KeyedHashFamily, H.TargetCollisionResistant := by
  obtain ⟨F⟩ := hf.exists_inaccessibleEntropyFamily
  exact F.toAdversaryInaccessibleEntropyFamily.exists_targetCollisionResistantHash

end Cslib.Crypto
