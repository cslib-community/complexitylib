/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.InaccessibleEntropy.Amplify
public import Complexity.Crypto.Computational.TargetCollisionResistant
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import Complexity.Computability.Probabilistic.UniformNat
import Complexity.Crypto.Game.Hybrid
import Complexity.Crypto.Negligible.Basic
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential
import Complexity.Probability.BitString.List
import Complexity.Probability.PMF
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Event
import Complexity.Tactic.PolyTime
import Complexity.Tactic.PPT

/-!
# Target collision-resistant hashing from inaccessible entropy and one-way functions

Completing the construction of universal one-way hash families (target collision-resistant hash
families) from arbitrary one-way functions (`[Rompel1990]`; `[HHRVW2020]`, Section 5.1,
Theorem 5.1, STEPS 4–5, Lemmas 5.6 and 5.7, pp. 29–32):

1. **Target shift (`rompelShiftedStep`; `[HHRVW2020]`, Section 5.1.4, Lemma 5.6, pp. 29–30, and
   Section 5.1.5, STEP 4, p. 31)**:
   given a `ShrinkingCollisionGrid` `G` whose `gridCount n` candidates compress `G.inLen n =
   G.outLen n + 1` bits to `G.outLen n` bits, shifting the input of candidate `q` by a `G.inLen n`
   key mask `y` via `w ↦ G.evalGrid n q (listXor (G.inLen n) [w, y])` converts random-input
   collision resistance at `q = goodIdx n` into keyed target collision resistance on `G.inLen n`-bit
   inputs.
2. **Length-increasing `1`-bit cascade and candidate concatenation (`rompelCascade`,
   `rompelCandidateEval`, `rompelCompressionEval`, `rompelCompression`; adapting `[HHRVW2020]`,
   Section 5.1.4, Lemma 5.7, p. 30, and Section 5.1.5, STEP 5(ii–iii), p. 32)**:
   iterating `rompelCascadeSteps G n = (2 * G.gridCount n - 1) * G.outLen n` independently masked
   `1`-bit shrinking steps compresses `G.outLen n + rompelCascadeSteps G n =
   2 * (G.gridCount n * G.outLen n)` bits to `G.outLen n` bits for each `q < G.gridCount n`, and
   concatenating all `G.gridCount n` candidate outputs produces a halving `KeyedCompressionFamily`
   (`rompelCompression G`) with block width `rompelBlockLen G n = G.gridCount n * G.outLen n`.
   Two deliberate adaptations simplify the formalization without claiming Lemma 5.7's compact
   `O(|y| log t)` key-length bound (proved from `log n`-bit shrinkage): each `1`-bit step consumes
   its own fresh `G.inLen n`-bit subkey (`rompelKeyLen G n = rompelCascadeSteps G n * G.inLen n`),
   and that single step-key sequence `K` is shared across all `G.gridCount n` candidates rather than
   indexing separate candidate keys as in STEP 5(iii) (sound because the reduction only needs key
   simulation at the single existential `goodIdx n`).
3. **Single-stage planted-subkey reduction (`rompelCompressionInverter`,
   `succProbability_targetCollisionGame_rompelCompression_le`,
   `ShrinkingCollisionGrid.targetCollisionResistant_rompelCompression`)**:
   given a uniform `G.inLen n`-bit challenge `zWord` for `randomCollisionGame` at `goodIdx n`,
   sampling dyadic guesses `(qGuess, slot)` for `(goodIdx n, i*)`, running `adversary.choose n`,
   sampling `front`, planting `yStar := listXor (G.inLen n) [zWord, w₀]` so `w₀ ⊕ yStar = zWord`
   while `yStar` remains uniform, and completing `K := front ++ yStar ++ back` achieves exact key
   simulation with multiplicative loss `dyadicSize (G.gridCount n) *
   dyadicSize (rompelCascadeSteps G n)` and zero additive error.
4. **Domain extension to `List Bool` (`rompelHash`,
   `ShrinkingCollisionGrid.targetCollisionResistant_rompelHash`,
   `OneWay.exists_targetCollisionResistant_keyedHashFamily`)**:
   composing `rompelCompression G` with `KeyedCompressionFamily.treeHash` (`uowhfTreeHash`) yields
   an unrestricted computational target collision-resistant `KeyedHashFamily` on `List Bool` from
   any uniform `OneWay` function: although the compressed `rompelBlockLen G n`-bit digest cannot be
   injective on long messages, on inputs of length `< 2 ^ n` at parameter `n` the leaf/length
   encoding is injective and the fixed `n`-level binary tree reduces all leaves to a single root
   without discarding extra roots, so any collision among strict-PPT adversary outputs (which have
   length `< 2 ^ n` for sufficiently large `n`) extracts a compression-step collision.

## Main definitions

* `Cslib.Crypto.rompelShiftedStep`: XOR-masked `1`-bit shrinking candidate step (Lemma 5.6, STEP 4).
* `Cslib.Crypto.rompelCascadeSteps`, `Cslib.Crypto.rompelBlockLen`, `Cslib.Crypto.rompelKeyLen`:
  step, block, and shared key-length schedules for `rompelCompression`.
* `Cslib.Crypto.rompelCascadeStep`, `Cslib.Crypto.rompelCascade`,
  `Cslib.Crypto.rompelCandidateEval`, `Cslib.Crypto.rompelCascadeInput`: `1`-bit shrinking cascade
  and step-`i` compression-input extractor (adapting Lemma 5.7 and STEP 5(ii)).
* `Cslib.Crypto.rompelCompressionEval`, `Cslib.Crypto.rompelCompression`: `gridCount n`-way
  concatenated `2 * rompelBlockLen G n → rompelBlockLen G n` `KeyedCompressionFamily` (adapting
  STEP 5(iii)).
* `Cslib.Crypto.rompelCompressionInverter`: uniform strict-PPT reduction from target collisions of
  `rompelCompression G` to `randomCollisionGame` on `G`.
* `Cslib.Crypto.rompelHash`: unrestricted `KeyedHashFamily` `(rompelCompression G).treeHash`.

## Main results

* `Cslib.Crypto.exists_rompelCascadeInput_collision`: deterministic extraction of a step collision
  `i < rompelCascadeSteps G n` from any `2 * rompelBlockLen G n`-bit collision of candidate `q`.
* `Cslib.Crypto.isPPT_rompelCompressionInverter`: uniform strict-PPT certificate for
  `rompelCompressionInverter`.
* `Cslib.Crypto.succProbability_targetCollisionGame_rompelCompression_le`: concrete security bound
  against `randomCollisionGame` at any candidate `qStar < G.gridCount n`.
* `Cslib.Crypto.ShrinkingCollisionGrid.targetCollisionResistant_rompelCompression`,
  `Cslib.Crypto.ShrinkingCollisionGrid.targetCollisionResistant_rompelHash`: target collision
  resistance of `rompelCompression G` and `rompelHash G`.
* `Cslib.Crypto.OneWay.exists_targetCollisionResistant_keyedCompressionFamily`,
  `Cslib.Crypto.OneWay.exists_targetCollisionResistant_keyedHashFamily`: every uniform `OneWay`
  function implies target collision-resistant compression and unrestricted `KeyedHashFamily`
  hashing.

## References

* [I. Haitner, T. Holenstein, O. Reingold, S. Vadhan, H. Wee, *Inaccessible Entropy II: IE
  Functions and Universal One-Way Hashing*, Sections 5.1.4–5.1.5, Theorem 5.1, Lemmas 5.6–5.7,
  pp. 29–32][HHRVW2020]
* [J. Rompel, *One-Way Functions are Necessary and Sufficient for Secure Signatures*][Rompel1990]
-/

public section

namespace Cslib.Crypto

open ProbComp Cslib.Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

attribute [local program_certificate, local fun_prop]
  ShrinkingCollisionGrid.polyTime_inLen
  ShrinkingCollisionGrid.polyTime_outLen
  ShrinkingCollisionGrid.polyTime_gridCount
  ShrinkingCollisionGrid.polyTime_evalGrid

/-! ### Schedules and XOR-shifted `1`-bit shrinking step (Lemma 5.6, STEP 4) -/

/-- Number of `1`-bit cascade steps `(2 * G.gridCount n - 1) * G.outLen n` used by each candidate in
`rompelCompression G` (adapting `[HHRVW2020]`, Section 5.1.5, STEP 5(ii), p. 32). -/
def rompelCascadeSteps (G : ShrinkingCollisionGrid) (n : ℕ) : ℕ :=
  (2 * G.gridCount n - 1) * G.outLen n

/-- Output (and half-input) block width `G.gridCount n * G.outLen n` of `rompelCompression G`
(`[HHRVW2020]`, Section 5.1.5, STEP 5(iii), p. 32). -/
@[expose]
def rompelBlockLen (G : ShrinkingCollisionGrid) (n : ℕ) : ℕ :=
  G.gridCount n * G.outLen n

/-- Shared key bit-length `rompelCascadeSteps G n * G.inLen n` of `rompelCompression G` (consuming
one `G.inLen n`-bit subkey per `1`-bit step and sharing that sequence across candidates rather than
claiming Lemma 5.7's `O(|y| log t)` compact-key bound or STEP 5(iii)'s per-candidate keys). -/
@[expose]
def rompelKeyLen (G : ShrinkingCollisionGrid) (n : ℕ) : ℕ :=
  rompelCascadeSteps G n * G.inLen n

theorem rompelCascadeSteps_pos (G : ShrinkingCollisionGrid) (n : ℕ) :
    1 ≤ rompelCascadeSteps G n := by
  have hk := G.gridCount_pos n
  have hout := G.le_outLen n
  unfold rompelCascadeSteps
  exact Nat.mul_pos (by omega) (by omega)

theorem outLen_add_rompelCascadeSteps (G : ShrinkingCollisionGrid) (n : ℕ) :
    G.outLen n + rompelCascadeSteps G n = 2 * rompelBlockLen G n := by
  have hk : 1 ≤ G.gridCount n := G.gridCount_pos n
  have hsub : 1 + (2 * G.gridCount n - 1) = 2 * G.gridCount n := by omega
  calc
    G.outLen n + rompelCascadeSteps G n
      = 1 * G.outLen n + (2 * G.gridCount n - 1) * G.outLen n := by
        simp only [one_mul, rompelCascadeSteps]
    _ = (1 + (2 * G.gridCount n - 1)) * G.outLen n := (Nat.add_mul _ _ _).symm
    _ = 2 * rompelBlockLen G n := by rw [hsub, rompelBlockLen, mul_assoc]

theorem le_rompelBlockLen (G : ShrinkingCollisionGrid) (n : ℕ) :
    n ≤ rompelBlockLen G n := by
  calc
    n ≤ G.outLen n := (Nat.le_succ n).trans (G.le_outLen n)
    _ = 1 * G.outLen n := (one_mul _).symm
    _ ≤ G.gridCount n * G.outLen n := Nat.mul_le_mul_right _ (G.gridCount_pos n)

@[program_certificate, fun_prop]
theorem computableInPolyTime_rompelCascadeSteps (G : ShrinkingCollisionGrid) :
    ComputableInPolyTime (rompelCascadeSteps G) encUnary encUnary := by
  unfold rompelCascadeSteps
  have h2k := ComputableInPolyTime.unary_mul' (.const 2) G.polyTime_gridCount
  exact ComputableInPolyTime.unary_mul' (h2k.unary_sub' (.const 1)) G.polyTime_outLen

@[program_certificate, fun_prop]
theorem computableInPolyTime_rompelBlockLen (G : ShrinkingCollisionGrid) :
    ComputableInPolyTime (rompelBlockLen G) encUnary encUnary :=
  ComputableInPolyTime.unary_mul' G.polyTime_gridCount G.polyTime_outLen

@[program_certificate, fun_prop]
theorem computableInPolyTime_rompelKeyLen (G : ShrinkingCollisionGrid) :
    ComputableInPolyTime (rompelKeyLen G) encUnary encUnary :=
  ComputableInPolyTime.unary_mul' (computableInPolyTime_rompelCascadeSteps G) G.polyTime_inLen

/-- **XOR-shifted `1`-bit shrinking step** (`[HHRVW2020]`, Section 5.1.4, Lemma 5.6, pp. 29–30;
Section 5.1.5, STEP 4, p. 31): masks `w` by `y` at width `G.inLen n` and evaluates candidate `q` of
`G`. -/
@[expose]
def rompelShiftedStep (G : ShrinkingCollisionGrid) (n q : ℕ) (y w : List Bool) : List Bool :=
  G.evalGrid n q (BitString.listXor (G.inLen n) [w, y])

@[simp]
theorem length_rompelShiftedStep (G : ShrinkingCollisionGrid) (n q : ℕ) (y w : List Bool) :
    (rompelShiftedStep G n q y w).length = G.outLen n :=
  G.length_evalGrid n q _

@[program_certificate, fun_prop]
theorem computableInPolyTime_rompelShiftedStep (G : ShrinkingCollisionGrid)
    {γ : Type} {encIn : γ ↪ List Bool}
    {n q : γ → ℕ} {y w : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hq : ComputableInPolyTime q encIn encUnary)
    (hy : ComputableInPolyTime y encIn encBits)
    (hw : ComputableInPolyTime w encIn encBits) :
    ComputableInPolyTime
      (fun a => rompelShiftedStep G (n a) (q a) (y a) (w a))
      encIn encBits := by
  unfold rompelShiftedStep
  polytime

/-! ### `1`-bit shrinking cascade and step-collision extraction (adapting Lemma 5.7, STEP 5(ii)) -/

/-- One step of the `1`-bit shrinking cascade for candidate `q`: append the next remaining message
bit to `acc.1`, apply `rompelShiftedStep G n q y`, and drop that bit from `acc.2`. -/
def rompelCascadeStep (G : ShrinkingCollisionGrid) (n q : ℕ)
    (acc : List Bool × List Bool) (y : List Bool) : List Bool × List Bool :=
  (rompelShiftedStep G n q y (acc.1 ++ [acc.2.headD false]), acc.2.drop 1)

/-- Fold `rompelCascadeStep G n q` across `subkeys`, starting from `(state, rest)` and returning the
final `G.outLen n`-bit state (adapting `[HHRVW2020]`, Section 5.1.4, Lemma 5.7, p. 30, and
Section 5.1.5, STEP 5(ii), p. 32 with one fresh subkey per `1`-bit step rather than compact
`O(|y| log t)` keys). -/
def rompelCascade (G : ShrinkingCollisionGrid) (n q : ℕ)
    (subkeys : List (List Bool)) (state rest : List Bool) : List Bool :=
  (subkeys.foldl (rompelCascadeStep G n q) (state, rest)).1

private theorem snd_foldl_rompelCascadeStep (G : ShrinkingCollisionGrid) (n q : ℕ)
    (subkeys : List (List Bool)) (state rest : List Bool) :
    (subkeys.foldl (rompelCascadeStep G n q) (state, rest)).2 = rest.drop subkeys.length := by
  induction subkeys generalizing state rest with
  | nil => simp
  | cons y ks ih =>
    simp only [List.foldl_cons, rompelCascadeStep, ih, List.drop_drop, List.length_cons]
    rw [Nat.add_comm 1 ks.length]

theorem length_rompelCascade (G : ShrinkingCollisionGrid) (n q : ℕ)
    (subkeys : List (List Bool)) {state : List Bool}
    (hstate : state.length = G.outLen n) (rest : List Bool) :
    (rompelCascade G n q subkeys state rest).length = G.outLen n := by
  induction subkeys generalizing state rest with
  | nil => simpa only [rompelCascade, List.foldl_nil] using hstate
  | cons y ks ih =>
    simp only [rompelCascade, List.foldl_cons, rompelCascadeStep]
    exact ih (length_rompelShiftedStep G n q y _) (rest.drop 1)

private theorem length_rompelCascade_le (G : ShrinkingCollisionGrid) (n q : ℕ)
    (subkeys : List (List Bool)) (state rest : List Bool) :
    (rompelCascade G n q subkeys state rest).length ≤ state.length + G.outLen n := by
  cases subkeys with
  | nil =>
    simp only [rompelCascade, List.foldl_nil]
    omega
  | cons y ks =>
    have heq :=
      length_rompelCascade G n q ks (length_rompelShiftedStep G n q y (state ++ [rest.headD false]))
        (rest.drop 1)
    change (rompelCascade G n q ks (rompelShiftedStep G n q y (state ++ [rest.headD false]))
      (rest.drop 1)).length ≤ state.length + G.outLen n
    omega

theorem rompelCascade_append_singleton (G : ShrinkingCollisionGrid) (n q : ℕ)
    (ks : List (List Bool)) (y state rest : List Bool) :
    rompelCascade G n q (ks ++ [y]) state rest =
      rompelShiftedStep G n q y
        (rompelCascade G n q ks state rest ++ [rest.getD ks.length false]) := by
  have hhead : (rest.drop ks.length).headD false = rest.getD ks.length false := by
    rw [List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD]
  simp only [rompelCascade, List.foldl_append, List.foldl_cons, List.foldl_nil,
    rompelCascadeStep, snd_foldl_rompelCascadeStep, hhead]

/-- Folding `rompelCascade` is computable in plain polynomial time for any `ShrinkingCollisionGrid`.
-/
@[program_certificate, fun_prop]
theorem computableInPolyTime_rompelCascade (G : ShrinkingCollisionGrid)
    {γ : Type} {encIn : γ ↪ List Bool}
    {n q : γ → ℕ} {subkeys : γ → List (List Bool)} {state rest : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hq : ComputableInPolyTime q encIn encUnary)
    (hsubkeys : ComputableInPolyTime subkeys encIn (encList encBits))
    (hstate : ComputableInPolyTime state encIn encBits)
    (hrest : ComputableInPolyTime rest encIn encBits) :
    ComputableInPolyTime
      (fun a => rompelCascade G (n a) (q a) (subkeys a) (state a) (rest a))
      encIn encBits := by
  have hstep : ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × (List Bool × List Bool)) × List Bool =>
        rompelCascadeStep G p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair encUnary encUnary) (encPair encBits encBits)) encBits)
      (encPair encBits encBits) := by
    unfold rompelCascadeStep
    polytime
  let outN (a : γ) : ℕ := G.outLen (n a)
  have houtN : ComputableInPolyTime outN encIn encUnary := G.polyTime_outLen.comp hn
  let stateBound (a : γ) : ℕ :=
    2 * ((state a).length + outN a) + 1 + (rest a).length
  have hpoly : PolyBounded (fun a => (encIn a).length) stateBound := by
    have hs := hstate.polyBounded_length
    have hr := hrest.polyBounded_length
    simp only [encBits_apply] at hs hr
    exact (((PolyBounded.const 2).mul (hs.add houtN.polyBounded)).add (.const 1)).add hr
  have hfold : ComputableInPolyTime
      (fun a => (subkeys a).foldl (rompelCascadeStep G (n a) (q a)) (state a, rest a))
      encIn (encPair encBits encBits) := by
    apply ComputableInPolyTime.foldlWith
      (encA := encBits) (encL := encList encBits)
      (encP := encPair encUnary encUnary) (encB := encPair encBits encBits)
      (par := fun a => (n a, q a))
      (step := fun p acc y => rompelCascadeStep G p.1 p.2 acc y)
      (hn.prod hq) hsubkeys (hstate.prod hrest) hstep hpoly
    intro a i _
    let pair := ((subkeys a).take i).foldl (rompelCascadeStep G (n a) (q a)) (state a, rest a)
    change (encPair encBits encBits pair).length ≤ stateBound a
    have h1 : pair.1.length ≤ (state a).length + outN a :=
      length_rompelCascade_le G (n a) (q a) ((subkeys a).take i) (state a) (rest a)
    have h2 : pair.2.length ≤ (rest a).length := by
      have heq := snd_foldl_rompelCascadeStep G (n a) (q a) ((subkeys a).take i) (state a) (rest a)
      change (((subkeys a).take i).foldl (rompelCascadeStep G (n a) (q a))
        (state a, rest a)).2.length ≤ (rest a).length
      rw [heq, List.length_drop]
      omega
    simp only [length_encPair, encBits_apply, stateBound]
    omega
  exact (ComputableInPolyTime.fst encBits encBits).comp hfold

/-- Candidate-`q` `2 * rompelBlockLen G n → G.outLen n` cascade evaluator under key `K`. -/
def rompelCandidateEval (G : ShrinkingCollisionGrid) (n q : ℕ) (K x : List Bool) : List Bool :=
  rompelCascade G n q (BitString.listRows (rompelCascadeSteps G n) (G.inLen n) K)
    (BitString.listRow (G.outLen n) 0 x) (x.drop (G.outLen n))

@[simp]
theorem length_rompelCandidateEval (G : ShrinkingCollisionGrid) (n q : ℕ) (K x : List Bool) :
    (rompelCandidateEval G n q K x).length = G.outLen n :=
  length_rompelCascade G n q _ (BitString.length_listRow (G.outLen n) 0 x) _

@[program_certificate, fun_prop]
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
  unfold rompelCandidateEval
  polytime

/-- Step-`i` `G.inLen n`-bit input fed to subkey `i` during `rompelCandidateEval G n q`, computed
from only the prefix `front` containing the first `i` subkeys. -/
def rompelCascadeInput (G : ShrinkingCollisionGrid) (n q i : ℕ)
    (front x : List Bool) : List Bool :=
  let tail := x.drop (G.outLen n)
  rompelCascade G n q (BitString.listRows i (G.inLen n) front)
    (BitString.listRow (G.outLen n) 0 x) tail ++ [tail.getD i false]

@[simp]
theorem length_rompelCascadeInput (G : ShrinkingCollisionGrid) (n q i : ℕ)
    (front x : List Bool) :
    (rompelCascadeInput G n q i front x).length = G.inLen n := by
  simp only [rompelCascadeInput, List.length_append, List.length_singleton,
    length_rompelCascade G n q _ (BitString.length_listRow (G.outLen n) 0 x), G.outLen_add_one n]

@[program_certificate, fun_prop]
theorem computableInPolyTime_rompelCascadeInput (G : ShrinkingCollisionGrid)
    {γ : Type} {encIn : γ ↪ List Bool}
    {n q i : γ → ℕ} {front x : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hq : ComputableInPolyTime q encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary)
    (hfront : ComputableInPolyTime front encIn encBits)
    (hx : ComputableInPolyTime x encIn encBits) :
    ComputableInPolyTime
      (fun a => rompelCascadeInput G (n a) (q a) (i a) (front a) (x a))
      encIn encBits := by
  unfold rompelCascadeInput
  polytime

theorem rompelCascadeInput_take_eq (G : ShrinkingCollisionGrid) {n q i : ℕ}
    (K x : List Bool) :
    rompelCascadeInput G n q i (K.take (i * G.inLen n)) x = rompelCascadeInput G n q i K x := by
  have hof : BitString.ofList (i * G.inLen n) (K.take (i * G.inLen n)) =
      BitString.ofList (i * G.inLen n) K := by
    funext k
    simp only [BitString.ofList, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt k.isLt]
  have hrows :
      BitString.listRows i (G.inLen n) (K.take (i * G.inLen n)) =
        BitString.listRows i (G.inLen n) K := by
    rw [BitString.listRows_eq_ofFn, BitString.listRows_eq_ofFn, hof]
  simp only [rompelCascadeInput, hrows]

/-- **Deterministic step-collision extraction (`[HHRVW2020]`, Section 5.1.4, Lemma 5.7, p. 30)**:
if two distinct `2 * rompelBlockLen G n`-bit inputs `x₀ ≠ x₁` collide under
`rompelCandidateEval G n q K`, there exists a step `i < rompelCascadeSteps G n` where their
`G.inLen n`-bit step inputs `rompelCascadeInput G n q i K` are distinct yet collide under
`rompelShiftedStep G n q (BitString.listRow (G.inLen n) i K)`. -/
theorem exists_rompelCascadeInput_collision (G : ShrinkingCollisionGrid)
    {n q : ℕ} {K x₀ x₁ : List Bool}
    (hx₀ : x₀.length = 2 * rompelBlockLen G n)
    (hx₁ : x₁.length = 2 * rompelBlockLen G n)
    (hne : x₀ ≠ x₁)
    (hcol : rompelCandidateEval G n q K x₀ = rompelCandidateEval G n q K x₁) :
    ∃ i < rompelCascadeSteps G n,
      rompelCascadeInput G n q i K x₀ ≠ rompelCascadeInput G n q i K x₁ ∧
      rompelShiftedStep G n q (BitString.listRow (G.inLen n) i K)
        (rompelCascadeInput G n q i K x₀) =
        rompelShiftedStep G n q (BitString.listRow (G.inLen n) i K)
          (rompelCascadeInput G n q i K x₁) := by
  by_contra hno
  simp only [not_exists, not_and] at hno
  let steps := rompelCascadeSteps G n
  let W := G.inLen n
  let M := G.outLen n
  have hsum : M + steps = 2 * rompelBlockLen G n := outLen_add_rompelCascadeSteps G n
  let S (x : List Bool) (j : ℕ) : List Bool :=
    rompelCascade G n q (BitString.listRows j W K) (BitString.listRow M 0 x) (x.drop M)
  have hstep_S : ∀ (x : List Bool) (j : ℕ),
      S x (j + 1) =
        rompelShiftedStep G n q (BitString.listRow W j K) (rompelCascadeInput G n q j K x) := by
    intro x j
    have hrows_succ : BitString.listRows (j + 1) W K =
        BitString.listRows j W K ++ [BitString.listRow W j K] := by
      simp [BitString.listRows, List.range_succ]
    dsimp only [S, rompelCascadeInput, W, M]
    rw [hrows_succ, rompelCascade_append_singleton, BitString.length_listRows]
  have hback : ∀ t ≤ steps,
      S x₀ (steps - t) = S x₁ (steps - t) ∧
      ∀ j, steps - t ≤ j → j < steps →
        (x₀.drop M).getD j false = (x₁.drop M).getD j false := by
    intro t ht
    induction t with
    | zero =>
      refine ⟨hcol, fun j hj_ge hj_lt => ?_⟩
      omega
    | succ t ih =>
      obtain ⟨hS_prev, hbits_prev⟩ := ih (by omega)
      let i := steps - 1 - t
      have hi_lt : i < steps := by omega
      have hsucc_eq : i + 1 = steps - t := by omega
      have hsub_eq : steps - (t + 1) = i := by omega
      have hstep_eq :
          rompelShiftedStep G n q (BitString.listRow W i K) (rompelCascadeInput G n q i K x₀) =
            rompelShiftedStep G n q (BitString.listRow W i K)
              (rompelCascadeInput G n q i K x₁) := by
        rw [← hstep_S x₀ i, ← hstep_S x₁ i, hsucc_eq, hS_prev]
      have hinp_eq : rompelCascadeInput G n q i K x₀ = rompelCascadeInput G n q i K x₁ := by
        by_contra hinp_ne
        exact hno i hi_lt hinp_ne hstep_eq
      have hlen_S₀ : (S x₀ i).length = M :=
        length_rompelCascade G n q _ (BitString.length_listRow M 0 x₀) _
      have hlen_S₁ : (S x₁ i).length = M :=
        length_rompelCascade G n q _ (BitString.length_listRow M 0 x₁) _
      obtain ⟨hSi_eq, hbit_i⟩ :=
        List.append_inj hinp_eq (hlen_S₀.trans hlen_S₁.symm)
      rw [List.singleton_inj] at hbit_i
      rw [hsub_eq]
      refine ⟨hSi_eq, fun j hj_ge hj_lt => ?_⟩
      rcases eq_or_lt_of_le hj_ge with rfl | _
      · exact hbit_i
      · exact hbits_prev j (by omega) hj_lt
  obtain ⟨hS0, hbits_all⟩ := hback steps le_rfl
  simp only [Nat.sub_self, S, BitString.listRows, List.range_zero, List.map_nil, rompelCascade,
    List.foldl_nil] at hS0 hbits_all
  have htake_eq : x₀.take M = x₁.take M := by
    have h0 : BitString.listRow M 0 x₀ = x₀.take M := by
      unfold BitString.listRow
      simp only [Nat.zero_mul, List.drop_zero]
      exact List.take_append_of_le_length (by omega)
    have h1 : BitString.listRow M 0 x₁ = x₁.take M := by
      unfold BitString.listRow
      simp only [Nat.zero_mul, List.drop_zero]
      exact List.take_append_of_le_length (by omega)
    rwa [h0, h1] at hS0
  have hdrop_len₀ : (x₀.drop M).length = steps := by rw [List.length_drop, hx₀]; omega
  have hdrop_len₁ : (x₁.drop M).length = steps := by rw [List.length_drop, hx₁]; omega
  have hdrop_eq : x₀.drop M = x₁.drop M := by
    apply List.ext_getElem (hdrop_len₀.trans hdrop_len₁.symm)
    intro j hj₀ hj₁
    have hj_lt : j < steps := by omega
    have hget := hbits_all j (Nat.zero_le j) hj_lt
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj₀,
      List.getElem?_eq_getElem hj₁, Option.getD_some] using hget
  apply hne
  rw [← List.take_append_drop M x₀, ← List.take_append_drop M x₁, htake_eq, hdrop_eq]

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

@[program_certificate]
theorem computableInPolyTime_rompelCompressionEval (G : ShrinkingCollisionGrid) :
    ComputableInPolyTime
      (fun ⟨n, K, x⟩ => rompelCompressionEval G n K x)
      (encPair encUnary (encPair encBits encBits)) encBits := by
  let encIn := encPair encUnary (encPair encBits encBits)
  unfold rompelCompressionEval
  apply ComputableInPolyTime.flatMapToBitsWithInput
    (ComputableInPolyTime.unary_range' (G.polyTime_gridCount.comp (ComputableInPolyTime.fst _ _)))
  have hn : ComputableInPolyTime
      (fun p : (ℕ × List Bool × List Bool) × ℕ => p.1.1)
      (encPair encIn encUnary) encUnary := by polytime
  have hq : ComputableInPolyTime
      (fun p : (ℕ × List Bool × List Bool) × ℕ => p.2)
      (encPair encIn encUnary) encUnary := by polytime
  have hK : ComputableInPolyTime
      (fun p : (ℕ × List Bool × List Bool) × ℕ => p.1.2.1)
      (encPair encIn encUnary) encBits := by polytime
  have hx : ComputableInPolyTime
      (fun p : (ℕ × List Bool × List Bool) × ℕ => p.1.2.2)
      (encPair encIn encUnary) encBits := by polytime
  exact computableInPolyTime_rompelCandidateEval G hn hq hK hx

/-- **Rompel / HHRVW halving `KeyedCompressionFamily`** (adapting `[HHRVW2020]`, Section 5.1.5,
STEP 4 and STEP 5(ii–iii), pp. 31–32): compresses `2 * rompelBlockLen G n`-bit blocks to
`rompelBlockLen G n`-bit blocks under shared `rompelKeyLen G n`-bit step-key sequences. -/
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

/-! ### Single-stage planted-subkey reduction to `randomCollisionGame` -/

private def clampIdx (bound guess : ℕ) : ℕ :=
  (bound - 1) - ((bound - 1) - guess)

private theorem clampIdx_eq_of_lt {bound guess : ℕ} (h : guess < bound) :
    clampIdx bound guess = guess := by
  unfold clampIdx
  omega

@[local fun_prop]
private theorem computableInPolyTime_clampIdx {γ : Type} {encIn : γ ↪ List Bool}
    {bound guess : γ → ℕ}
    (hb : ComputableInPolyTime bound encIn encUnary)
    (hg : ComputableInPolyTime guess encIn encUnary) :
    ComputableInPolyTime (fun a => clampIdx (bound a) (guess a)) encIn encUnary := by
  unfold clampIdx
  polytime

private def pairXor (m : ℕ) (u v : List Bool) : List Bool :=
  BitString.listXor m [u, v]

@[local fun_prop]
private theorem computableInPolyTime_pairXor {γ : Type} {encIn : γ ↪ List Bool}
    {m : γ → ℕ} {u v : γ → List Bool}
    (hm : ComputableInPolyTime m encIn encUnary)
    (hu : ComputableInPolyTime u encIn encBits)
    (hv : ComputableInPolyTime v encIn encBits) :
    ComputableInPolyTime (fun a => pairXor (m a) (u a) (v a)) encIn encBits := by
  unfold pairXor
  polytime

private def rompelFrontLen (G : ShrinkingCollisionGrid) (n slot : ℕ) : ℕ :=
  clampIdx (rompelCascadeSteps G n) slot * G.inLen n

@[local fun_prop]
private theorem computableInPolyTime_rompelFrontLen (G : ShrinkingCollisionGrid)
    {γ : Type} {encIn : γ ↪ List Bool} {n slot : γ → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hslot : ComputableInPolyTime slot encIn encUnary) :
    ComputableInPolyTime (fun a => rompelFrontLen G (n a) (slot a)) encIn encUnary := by
  unfold rompelFrontLen
  polytime

private def rompelBackLen (G : ShrinkingCollisionGrid) (n slot : ℕ) : ℕ :=
  (rompelCascadeSteps G n - 1 - clampIdx (rompelCascadeSteps G n) slot) * G.inLen n

@[local fun_prop]
private theorem computableInPolyTime_rompelBackLen (G : ShrinkingCollisionGrid)
    {γ : Type} {encIn : γ ↪ List Bool} {n slot : γ → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hslot : ComputableInPolyTime slot encIn encUnary) :
    ComputableInPolyTime (fun a => rompelBackLen G (n a) (slot a)) encIn encUnary := by
  unfold rompelBackLen
  polytime

private def rompelYStar (G : ShrinkingCollisionGrid) (n qGuess slot : ℕ)
    (zWord front x₀ : List Bool) : List Bool :=
  let q := clampIdx (G.gridCount n) qGuess
  let i := clampIdx (rompelCascadeSteps G n) slot
  pairXor (G.inLen n) zWord (rompelCascadeInput G n q i front x₀)

@[local fun_prop]
private theorem computableInPolyTime_rompelYStar (G : ShrinkingCollisionGrid)
    {γ : Type} {encIn : γ ↪ List Bool} {n qGuess slot : γ → ℕ} {zWord front x₀ : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hq : ComputableInPolyTime qGuess encIn encUnary)
    (hs : ComputableInPolyTime slot encIn encUnary)
    (hz : ComputableInPolyTime zWord encIn encBits)
    (hf : ComputableInPolyTime front encIn encBits)
    (hx₀ : ComputableInPolyTime x₀ encIn encBits) :
    ComputableInPolyTime
      (fun a => rompelYStar G (n a) (qGuess a) (slot a) (zWord a) (front a) (x₀ a))
      encIn encBits := by
  unfold rompelYStar
  polytime

private def rompelUnmaskWord (G : ShrinkingCollisionGrid) (n qGuess slot : ℕ)
    (zWord front x₀ x₁ : List Bool) : List Bool :=
  let q := clampIdx (G.gridCount n) qGuess
  let i := clampIdx (rompelCascadeSteps G n) slot
  let yStar := rompelYStar G n qGuess slot zWord front x₀
  pairXor (G.inLen n) (rompelCascadeInput G n q i front x₁) yStar

@[local fun_prop]
private theorem computableInPolyTime_rompelUnmaskWord (G : ShrinkingCollisionGrid)
    {γ : Type} {encIn : γ ↪ List Bool} {n qGuess slot : γ → ℕ}
    {zWord front x₀ x₁ : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hq : ComputableInPolyTime qGuess encIn encUnary)
    (hs : ComputableInPolyTime slot encIn encUnary)
    (hz : ComputableInPolyTime zWord encIn encBits)
    (hf : ComputableInPolyTime front encIn encBits)
    (hx₀ : ComputableInPolyTime x₀ encIn encBits)
    (hx₁ : ComputableInPolyTime x₁ encIn encBits) :
    ComputableInPolyTime
      (fun a => rompelUnmaskWord G (n a) (qGuess a) (slot a) (zWord a) (front a) (x₀ a) (x₁ a))
      encIn encBits := by
  unfold rompelUnmaskWord
  polytime

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
  have hchoose := ha.choose
  unfold rompelInverterStage1
  ppt

private noncomputable def rompelInverterStage2 (G : ShrinkingCollisionGrid)
    (adversary : TargetCollisionFinder) (n : ℕ) (zWord : List Bool)
    (s : (ℕ × ℕ) × (List Bool × List Bool)) : ProbComp (List Bool) := do
  let front ← BitString.sampleList (rompelFrontLen G n s.1.2)
  let back ← BitString.sampleList (rompelBackLen G n s.1.2)
  let x₁ ← adversary.find n s.2.2
    (front ++ rompelYStar G n s.1.1 s.1.2 zWord front s.2.1 ++ back)
  return rompelUnmaskWord G n s.1.1 s.1.2 zWord front s.2.1 x₁

private theorem isPPTOn_rompelInverterStage2 (G : ShrinkingCollisionGrid)
    {adversary : TargetCollisionFinder} (ha : adversary.IsPPT) :
    IsPPTOn
      (encPair (encPair encUnary encBits)
        (encPair (encPair encUnary encUnary) (encPair encBits encBits)))
      encBits
      (fun p => rompelInverterStage2 G adversary p.1.1 p.1.2 p.2) := by
  have hfind := ha.find
  dsimp only [rompelInverterStage2]
  ppt

/-- Uniform strict-PPT reduction from `targetCollisionGame` on `rompelCompression G` to
`randomCollisionGame` on `G`: guess dyadic indices `(qGuess, slot)`, clamp to valid ranges via unary
subtraction, run `adversary.choose n`, sample `front`, mask `zWord` by `w₀` via
`rompelYStar`, sample `back`, run `adversary.find`, and unmask via `rompelUnmaskWord`. -/
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

private theorem listXor_ne_listXor_iff {W : ℕ} {w₀ w₁ y : List Bool}
    (hw₀ : w₀.length = W) (hw₁ : w₁.length = W) :
    BitString.listXor W [w₁, y] ≠ BitString.listXor W [w₀, y] ↔ w₀ ≠ w₁ := by
  constructor
  · intro hne heq
    exact hne (by rw [heq])
  · intro hne heq
    apply hne
    have hfin : BitString.ofList W w₁ + BitString.ofList W y =
        BitString.ofList W w₀ + BitString.ofList W y := by
      simpa only [BitString.ofList_listXor_pair] using congrArg (BitString.ofList W) heq
    have hof : BitString.ofList W w₀ = BitString.ofList W w₁ :=
      (add_left_inj (BitString.ofList W y)).mp hfin.symm
    rw [← BitString.ofFn_ofList hw₀, ← BitString.ofFn_ofList hw₁, hof]

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
  let μ : PMF ((List Bool × List Bool) × List Bool × List Bool) :=
    (ProbComp.eval (adversary.choose n)).bind fun choice =>
      (BitString.uniformList (S * W)).bind fun K =>
        (ProbComp.eval (adversary.find n choice.2 K)).map fun x₁ => (choice, K, x₁)
  let winComp (t : (List Bool × List Bool) × List Bool × List Bool) : Bool :=
    isCollision (rompelCompressionEval G n) (rompelCompression G).validInput n t.2.1 t.1.1 t.2.2
  have hcomp_eq :
      ProbComp.eval
        (targetCollisionGame (rompelCompression G).keyLen (rompelCompression G).eval
          (rompelCompression G).validInput adversary n) =
        μ.map winComp := by
    simp only [targetCollisionGame, rompelCompression, rompelKeyLen, μ, winComp,
      ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList, PMF.map, PMF.bind_bind,
      PMF.pure_bind, Function.comp_def, S, W]
  let trial (qGuess slot : ℕ) : Game := do
    let zWord ← BitString.uniformList W
    let choice ← ProbComp.eval (adversary.choose n)
    let q := clampIdx (G.gridCount n) qGuess
    let i := clampIdx S slot
    let front ← BitString.uniformList (i * W)
    let w₀ := rompelCascadeInput G n q i front choice.1
    let yStar := BitString.listXor W [zWord, w₀]
    let back ← BitString.uniformList ((S - 1 - i) * W)
    let x₁ ← ProbComp.eval (adversary.find n choice.2 (front ++ yStar ++ back))
    let w₁ := rompelCascadeInput G n q i front x₁
    let zWord' := BitString.listXor W [w₁, yStar]
    return decide (zWord'.length = W ∧ zWord' ≠ zWord ∧
      G.evalGrid n qStar zWord' = G.evalGrid n qStar zWord)
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
        rompelInverterStage2, rompelFrontLen, rompelBackLen,
        rompelYStar, rompelUnmaskWord, pairXor, trial, ProbComp.eval_bind,
        ProbComp.eval_pure, eval_sampleDyadicIndex, BitString.eval_sampleList,
        PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind,
        PMF.bind_map, Function.comp_def, W, S, Dq, Ds]
      rw [PMF.bind_comm (BitString.uniformList W) (PMF.uniformOfFintype (Fin Dq))]
      refine PMF.bind_congr_on_support _ _ _ fun a _ => ?_
      rw [PMF.bind_comm (BitString.uniformList W) (PMF.uniformOfFintype (Fin Ds))]
    rw [h1, ← PMF.uniformOfFintype_prod, PMF.bind_bind]
    refine PMF.bind_congr_on_support _ _ _ fun a _ => ?_
    rw [PMF.bind_map]
    rfl
  let Wi (s : Fin Ds) (t : (List Bool × List Bool) × List Bool × List Bool) : Bool :=
    if s.val < S then
      let w₀ := rompelCascadeInput G n qStar s.val t.2.1 t.1.1
      let w₁ := rompelCascadeInput G n qStar s.val t.2.1 t.2.2
      let y := BitString.listRow W s.val t.2.1
      decide (w₀ ≠ w₁ ∧ rompelShiftedStep G n qStar y w₀ = rompelShiftedStep G n qStar y w₁)
    else false
  have hslot_eq : ∀ s : Fin Ds, s.val < S → trial qStar s.val = μ.map (Wi s) := by
    intro s hs
    have hq_clamp : clampIdx (G.gridCount n) qStar = qStar := clampIdx_eq_of_lt hqStar
    have hs_clamp : clampIdx S s.val = s.val := clampIdx_eq_of_lt hs
    have hlen_sum : s.val * W + (W + (S - 1 - s.val) * W) = S * W := by
      calc
        s.val * W + (W + (S - 1 - s.val) * W)
          = (s.val + 1 + (S - 1 - s.val)) * W := by ring
        _ = S * W := by rw [show s.val + 1 + (S - 1 - s.val) = S by omega]
    simp only [trial, Wi, μ, hs, hq_clamp, hs_clamp, ↓reduceIte,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map, PMF.bind_bind, PMF.pure_bind,
      Function.comp_def]
    rw [PMF.bind_comm (BitString.uniformList W) (ProbComp.eval (adversary.choose n))]
    refine PMF.bind_congr_on_support _ _ _ fun choice _ => ?_
    rw [PMF.bind_comm (BitString.uniformList W) (BitString.uniformList (s.val * W))]
    calc
      (BitString.uniformList (s.val * W)).bind (fun front =>
        (BitString.uniformList W).bind (fun zWord =>
          let w₀ := rompelCascadeInput G n qStar s.val front choice.1
          let yStar := BitString.listXor W [zWord, w₀]
          (BitString.uniformList ((S - 1 - s.val) * W)).bind (fun back =>
            (ProbComp.eval (adversary.find n choice.2 (front ++ yStar ++ back))).bind fun x₁ =>
              let w₁ := rompelCascadeInput G n qStar s.val front x₁
              let zWord' := BitString.listXor W [w₁, yStar]
              PMF.pure (decide (zWord'.length = W ∧ zWord' ≠ zWord ∧
                G.evalGrid n qStar zWord' = G.evalGrid n qStar zWord)))))
        = (BitString.uniformList (s.val * W)).bind (fun front =>
            let w₀ := rompelCascadeInput G n qStar s.val front choice.1
            (BitString.uniformList W).bind (fun yStar =>
              (BitString.uniformList ((S - 1 - s.val) * W)).bind (fun back =>
                (ProbComp.eval (adversary.find n choice.2 (front ++ yStar ++ back))).bind fun x₁ =>
                  let w₁ := rompelCascadeInput G n qStar s.val front x₁
                  PMF.pure (decide (w₀ ≠ w₁ ∧
                    rompelShiftedStep G n qStar yStar w₀ =
                      rompelShiftedStep G n qStar yStar w₁))))) := by
          refine PMF.bind_congr_on_support _ _ _ fun front _ => ?_
          let w₀ := rompelCascadeInput G n qStar s.val front choice.1
          have hw₀_len : w₀.length = W := length_rompelCascadeInput G n qStar s.val front choice.1
          let post (yStar : List Bool) : PMF Bool :=
            (BitString.uniformList ((S - 1 - s.val) * W)).bind fun back =>
              (ProbComp.eval (adversary.find n choice.2 (front ++ yStar ++ back))).bind fun x₁ =>
                let w₁ := rompelCascadeInput G n qStar s.val front x₁
                PMF.pure (decide (w₀ ≠ w₁ ∧
                  rompelShiftedStep G n qStar yStar w₀ = rompelShiftedStep G n qStar yStar w₁))
          have hcongr_z :
              (BitString.uniformList W).bind (fun zWord =>
                let yStar := BitString.listXor W [zWord, w₀]
                (BitString.uniformList ((S - 1 - s.val) * W)).bind (fun back =>
                  (ProbComp.eval (adversary.find n choice.2 (front ++ yStar ++ back))).bind
                    fun x₁ =>
                      let w₁ := rompelCascadeInput G n qStar s.val front x₁
                      let zWord' := BitString.listXor W [w₁, yStar]
                      PMF.pure (decide (zWord'.length = W ∧ zWord' ≠ zWord ∧
                        G.evalGrid n qStar zWord' = G.evalGrid n qStar zWord)))) =
              (BitString.uniformList W).bind (fun zWord =>
                post (BitString.listXor W [zWord, w₀])) := by
            refine PMF.bind_congr_on_support _ _ _ fun zWord hzWord => ?_
            have hz_len : zWord.length = W := BitString.length_of_mem_support_uniformList hzWord
            let yStar := BitString.listXor W [zWord, w₀]
            have hz_rec : BitString.listXor W [w₀, yStar] = zWord := by
              dsimp only [yStar]
              rw [BitString.listXor_pair_comm W zWord w₀,
                BitString.listXor_pair_self_left_of_length w₀ hz_len]
            dsimp only [post]
            refine PMF.bind_congr_on_support _ _ _ fun back _ => ?_
            refine PMF.bind_congr_on_support _ _ _ fun x₁ _ => ?_
            let w₁ := rompelCascadeInput G n qStar s.val front x₁
            have hw₁_len : w₁.length = W := length_rompelCascadeInput G n qStar s.val front x₁
            have hne_iff : BitString.listXor W [w₁, yStar] ≠ zWord ↔ w₀ ≠ w₁ := by
              conv_lhs => rw [← hz_rec]
              exact listXor_ne_listXor_iff hw₀_len hw₁_len
            have heval_iff :
                G.evalGrid n qStar (BitString.listXor W [w₁, yStar]) = G.evalGrid n qStar zWord ↔
                  rompelShiftedStep G n qStar yStar w₀ =
                    rompelShiftedStep G n qStar yStar w₁ := by
              dsimp only [rompelShiftedStep, W]
              rw [hz_rec, eq_comm]
            congr 1
            exact decide_eq_decide.mpr
              ⟨fun ⟨_, hne, hev⟩ => ⟨hne_iff.mp hne, heval_iff.mp hev⟩,
               fun ⟨hne, hev⟩ => ⟨BitString.length_listXor W _, hne_iff.mpr hne, heval_iff.mpr hev⟩⟩
          have hcomp_post :
              (fun zWord => post (BitString.listXor W [zWord, w₀])) =
                post ∘ (fun zWord => BitString.listXor W [zWord, w₀]) := rfl
          rw [hcongr_z, hcomp_post, ← PMF.bind_map, BitString.uniformList_map_listXor W w₀]
      _ = (BitString.uniformList (s.val * W)).bind (fun front =>
            (BitString.uniformList (W + (S - 1 - s.val) * W)).bind (fun rest =>
              (ProbComp.eval (adversary.find n choice.2
                (front ++ rest.take W ++ rest.drop W))).bind fun x₁ =>
                let w₀ := rompelCascadeInput G n qStar s.val front choice.1
                let w₁ := rompelCascadeInput G n qStar s.val front x₁
                PMF.pure (decide (w₀ ≠ w₁ ∧
                  rompelShiftedStep G n qStar (rest.take W) w₀ =
                    rompelShiftedStep G n qStar (rest.take W) w₁)))) := by
          refine PMF.bind_congr_on_support _ _ _ fun front _ => ?_
          exact (BitString.uniformList_bind_split W ((S - 1 - s.val) * W) _).symm
      _ = (BitString.uniformList (s.val * W + (W + (S - 1 - s.val) * W))).bind (fun K =>
            let front := K.take (s.val * W)
            let rest := K.drop (s.val * W)
            (ProbComp.eval (adversary.find n choice.2
              (front ++ rest.take W ++ rest.drop W))).bind fun x₁ =>
              let w₀ := rompelCascadeInput G n qStar s.val front choice.1
              let w₁ := rompelCascadeInput G n qStar s.val front x₁
              PMF.pure (decide (w₀ ≠ w₁ ∧
                rompelShiftedStep G n qStar (rest.take W) w₀ =
                  rompelShiftedStep G n qStar (rest.take W) w₁))) :=
          (BitString.uniformList_bind_split (s.val * W) (W + (S - 1 - s.val) * W) _).symm
      _ = _ := by
          rw [hlen_sum]
          refine PMF.bind_congr_on_support _ _ _ fun K hK => ?_
          have hK_len : K.length = S * W := BitString.length_of_mem_support_uniformList hK
          have hrejoin : K.take (s.val * W) ++ (K.drop (s.val * W)).take W ++
              (K.drop (s.val * W)).drop W = K := by
            rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
          have hrow : (K.drop (s.val * W)).take W = BitString.listRow W s.val K := by
            have hrem : W ≤ (K.drop (s.val * W)).length := by
              rw [List.length_drop, hK_len]
              have : (s.val + 1) * W ≤ S * W := Nat.mul_le_mul_right W (by omega)
              have : s.val * W + W = (s.val + 1) * W := by ring
              omega
            unfold BitString.listRow
            rw [List.take_append_of_le_length hrem]
          dsimp only
          rw [hrejoin, hrow, rompelCascadeInput_take_eq G K choice.1]
          refine PMF.bind_congr_on_support _ _ _ fun x₁ _ => ?_
          rw [rompelCascadeInput_take_eq G K x₁]
  have hcover : ∀ t ∈ μ.support, winComp t = true → ∃ s : Fin Ds, Wi s t = true := by
    intro t ht hW
    simp only [μ, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at ht
    obtain ⟨choice, _, K, _, ⟨x₁, _, rfl⟩⟩ := ht
    rw [isCollision_eq_true_iff] at hW
    obtain ⟨hx₀_v, hx₁_v, hne, hcol⟩ := hW
    have hcand_col :
        rompelCandidateEval G n qStar K choice.1 = rompelCandidateEval G n qStar K x₁ := by
      rw [← listRow_rompelCompressionEval G n K choice.1 hqStar,
        ← listRow_rompelCompressionEval G n K x₁ hqStar, hcol]
    obtain ⟨i, hi_lt, hw_ne, hw_col⟩ :=
      exists_rompelCascadeInput_collision G
        ((rompelCompression G).validInput_eq_true_iff.mp hx₀_v)
        ((rompelCompression G).validInput_eq_true_iff.mp hx₁_v)
        hne hcand_col
    refine ⟨⟨i, hi_lt.trans (lt_dyadicSize S)⟩, ?_⟩
    dsimp only [Wi, W, S]
    simp only [hi_lt, ↓reduceIte, decide_eq_true_eq]
    exact ⟨hw_ne, hw_col⟩
  obtain ⟨val, hval⟩ : ∃ val : ℕ → ℕ → ℝ≥0∞, ∀ q i, (trial q i) true = val q i :=
    ⟨_, fun _ _ => rfl⟩
  have hsum_s : (μ.map winComp) true ≤ ∑ s : Fin Ds, val qStar s.val := by
    let F (j : ℕ) (t : (List Bool × List Bool) × List Bool × List Bool) : Bool :=
      if hj : j < Ds then Wi ⟨j, hj⟩ t else false
    have hmono :
        (μ.map winComp) true ≤
          (μ.map (fun t => (List.range Ds).any (fun j => F j t))) true := by
      refine PMF.map_true_mono μ fun t ht hW => ?_
      obtain ⟨⟨j, hj⟩, hs⟩ := hcover t ht hW
      refine List.any_eq_true.mpr ⟨j, List.mem_range.mpr hj, ?_⟩
      simpa only [F, hj, ↓reduceDIte] using hs
    refine (hmono.trans (PMF.map_any_range_true_le_sum μ Ds F)).trans ?_
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj_lt : j < Ds := Finset.mem_range.mp hj
    have hF : F j = Wi ⟨j, hj_lt⟩ := funext fun t => by simp only [F, hj_lt, ↓reduceDIte]
    simp only [hF, hj_lt, ↓reduceDIte, ← hval]
    by_cases hs : j < S
    · rw [hslot_eq ⟨j, hj_lt⟩ hs]
    · have hWi : Wi ⟨j, hj_lt⟩ = fun _ => false := funext fun t => by
        dsimp only [Wi]
        simp only [hs, ↓reduceIte]
      rw [hWi]
      simp
  let aStar : Fin Dq := ⟨qStar, hqStar.trans (lt_dyadicSize (G.gridCount n))⟩
  have hsum_prod :
      (μ.map winComp) true ≤ ∑ p : Fin Dq × Fin Ds, val p.1.val p.2.val := by
    refine hsum_s.trans ?_
    rw [Fintype.sum_prod_type]
    exact Finset.single_le_sum
      (f := fun a : Fin Dq => ∑ y : Fin Ds, val a.val y.val)
      (fun _ _ => zero_le) (Finset.mem_univ aStar)
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
  obtain ⟨goodIdx, hgood_lt, hgood_sec⟩ := G.exists_good_candidate
  apply TargetCollisionResistantOn.of_negligible
  intro adversary hadversary
  have hinv_ppt : IsPPT encBits (rompelCompressionInverter G adversary) :=
    isPPT_rompelCompressionInverter G hadversary
  have hneg_rand := hgood_sec (rompelCompressionInverter G adversary) hinv_ppt
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
Section 5.1, Theorem 5.1, p. 25): hashes arbitrary-length bit strings `List Bool` to
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

/-- Every uniform `OneWay` function yields a target collision-resistant `KeyedCompressionFamily`. -/
theorem OneWay.exists_targetCollisionResistant_keyedCompressionFamily
    {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ C : KeyedCompressionFamily, C.TargetCollisionResistant := by
  obtain ⟨G⟩ := hf.exists_shrinkingCollisionGrid
  exact ⟨rompelCompression G, G.targetCollisionResistant_rompelCompression⟩

/-- **Rompel–HHRVW universal one-way hash theorem** (`[Rompel1990]`; `[HHRVW2020]`,
Section 5.1, Theorem 5.1, p. 25): every uniform `OneWay` function implies the existence of an
unrestricted target collision-resistant `KeyedHashFamily` on `List Bool`. -/
theorem OneWay.exists_targetCollisionResistant_keyedHashFamily
    {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ H : KeyedHashFamily, H.TargetCollisionResistant := by
  obtain ⟨G⟩ := hf.exists_shrinkingCollisionGrid
  exact ⟨rompelHash G, G.targetCollisionResistant_rompelHash⟩

end Cslib.Crypto
