/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.FuzzyExtractor.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform

/-!
# LWE decode-then-extract computational fuzzy extractor

Construction 4.1 of Fuller, Meng, and Reyzin ([FullerMengReyzin2020], Section 4) builds a
computational fuzzy extractor over the Hamming space `(Fin m → ZMod q, hammingDist)` by reversing
the role of the noisy source reading `w`: rather than extracting randomness from `w`, `Gen(w)`
samples a uniform matrix `A : Matrix (Fin m) (Fin n) (ZMod q)` and secret `s : Fin n → ZMod q`
and uses `w` as the error vector in an LWE-style code-offset sample `c = A s + w`.

Given a close reading `w'` with `hammingDist w w' ≤ t`, `Rep(w', p)` subtracts `w'` from `c` to
form `c - w' = A s + (w - w')`, where the residual error `e = w - w'` has Hamming weight
`hammingWeight (w - w') = hammingDist w w' ≤ t`, runs a `t`-error decoder `decode A (c - w')` to
recover `s`, and derives the key from `s`.

## Main definitions

* `Cslib.Crypto.DecodeContext`, `Cslib.Crypto.DecodeHelper`: the LWE sample `(A, c)` and full
  public helper `(A, c, x)` of the decode-then-extract construction.
* `Cslib.Crypto.decodeThenExtract`: the decode-then-extract `FuzzyExtractor` (Construction 4.1).
* `Cslib.Crypto.DecoderCorrect`, `Cslib.Crypto.decodeCheck`, `Cslib.Crypto.decodeGame`,
  `Cslib.Crypto.DecoderCorrectWithError`: zero-error and `(1 - δ)` average-case decoding
  correctness up to Hamming weight `t`.
* `Cslib.Crypto.realContextDistribution`, `Cslib.Crypto.uniformContextDistribution`,
  `Cslib.Crypto.hybridDistribution`, `Cslib.Crypto.uniformIdealDistribution`,
  `Cslib.Crypto.lweRealContext`, `Cslib.Crypto.lweUniformContext`,
  `Cslib.Crypto.lweContextAdvantage`: the real, hybrid, and ideal distributions and Decisional
  LWE advantage (Definition 4.5).
* `Cslib.Crypto.realContextReduction`, `Cslib.Crypto.idealLweReduction`: the induced reductions
  from context distinguishing games to fuzzy-extractor distinguishers.

## Main results

* `Cslib.Crypto.cipher_sub_eq_mulVec_add_sub`,
  `Cslib.Crypto.hammingNorm_sub_eq_hammingDist`: the code-offset algebraic identity
  `(A s + w) - w' = A s + (w - w')` and `hammingNorm (w - w') = hammingDist w w'`.
* `Cslib.Crypto.DecoderCorrect.correctHamming_decodeThenExtract`: zero-error decoder correctness
  implies zero-error Hamming fuzzy-extractor correctness.
* `Cslib.Crypto.failProbability_reproduceGame_decodeThenExtract_le`,
  `Cslib.Crypto.DecoderCorrectWithError.correctHammingWithError_decodeThenExtract`: `δ`-error
  average-case decoder correctness over uniform `A` implies `δ`-error Hamming fuzzy-extractor
  correctness (and reproduction success probability at least `1 - δ`).
* `Cslib.Crypto.securityAdvantage_decodeThenExtract_le_three_hop`,
  `Cslib.Crypto.securityAdvantage_decodeThenExtract_le`,
  `Cslib.Crypto.computationallySecureFor_decodeThenExtract`: the hybrid reduction bounding
  `securityAdvantage` by `2 * ε_lwe + ε_ext`.
* `Cslib.Crypto.realContextDistribution_uniform`, `Cslib.Crypto.lweRealContext_uniform`,
  `Cslib.Crypto.securityAdvantage_decodeThenExtract_uniform_eq`: when `W` is uniform over
  `Fin m → ZMod q`, the LWE terms vanish identically by translation invariance.
* `Cslib.Crypto.hybridDistribution_add_eq_uniformIdealDistribution`,
  `Cslib.Crypto.securityAdvantage_decodeThenExtract_add_le`,
  `Cslib.Crypto.securityAdvantage_decodeThenExtract_add_uniform_eq_zero`: when `ext s x = s + x`,
  the extractor hop has advantage `0` (`ε_ext = 0`).

## References

* [B. Fuller, X. Meng, and L. Reyzin, *Computational Fuzzy Extractors*][FullerMengReyzin2020],
  Section 4 (Construction 4.1, Definition 4.5, Lemma 4.7, Theorem 4.11).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability
open scoped ENNReal NNReal

/-- The LWE sample `(A, c)` portion of the public helper in the decode-then-extract construction
([FullerMengReyzin2020], Construction 4.1 and Definition 4.5). -/
structure DecodeContext (m n q : ℕ) where
  /-- The public random matrix `A ∈ Z_q^{m × n}`. -/
  matrix : Matrix (Fin m) (Fin n) (ZMod q)
  /-- The code-offset vector `c = A s + w ∈ Z_q^m`. -/
  cipher : Fin m → ZMod q
  deriving DecidableEq

/-- The public helper `p = (A, c, x)` of the decode-then-extract construction, pairing the LWE
sample `(A, c)` with the public extractor seed `x`. -/
structure DecodeHelper (m n q : ℕ) (Seed : Type) where
  /-- The public random matrix `A ∈ Z_q^{m × n}`. -/
  matrix : Matrix (Fin m) (Fin n) (ZMod q)
  /-- The code-offset vector `c = A s + w ∈ Z_q^m`. -/
  cipher : Fin m → ZMod q
  /-- The public extractor seed `x`. -/
  seed : Seed
  deriving DecidableEq

/-- Project the LWE context `(A, c)` out of a `DecodeHelper`. -/
def DecodeHelper.context {m n q : ℕ} {Seed : Type} (p : DecodeHelper m n q Seed) :
    DecodeContext m n q :=
  ⟨p.matrix, p.cipher⟩

/-! ### Construction 4.1: Decode-then-extract fuzzy extractor -/

/-- The decode-then-extract computational fuzzy extractor ([FullerMengReyzin2020],
Construction 4.1):
* `Gen(w)` samples uniform `A : Matrix (Fin m) (Fin n) (ZMod q)`, uniform secret
  `s : Fin n → ZMod q`, and uniform seed `x : Seed`, and outputs `(ext s x, ⟨A, A s + w, x⟩)`;
* `Rep(w', p)` computes `p.cipher - w'`, runs `decode p.matrix (p.cipher - w')`, and outputs
  `ext s' p.seed` when the decoder returns `some s'` (or `default` on `none`). -/
noncomputable def decodeThenExtract (m n q : ℕ) [NeZero q]
    {Seed Key : Type} [Fintype Seed] [Nonempty Seed] [Inhabited Key]
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q)))
    (ext : (Fin n → ZMod q) → Seed → Key) :
    FuzzyExtractor (Fin m → ZMod q) Key (DecodeHelper m n q Seed) where
  gen w := do
    let A ← ProbComp.uniform (Matrix (Fin m) (Fin n) (ZMod q))
    let s ← ProbComp.uniform (Fin n → ZMod q)
    let x ← ProbComp.uniform Seed
    return (ext s x, ⟨A, A.mulVec s + w, x⟩)
  rep w' p := do
    let sOpt ← decode p.matrix (p.cipher - w')
    match sOpt with
    | some s' => return ext s' p.seed
    | none => return default

/-! ### Algebraic code-offset identities and reproduction correctness -/

/-- Subtracting the noisy reading `w'` from the helper ciphertext `c = A s + w` yields
`A s + (w - w')`, shifting the difference `w - w'` into the error position of the code-offset
sample. -/
theorem cipher_sub_eq_mulVec_add_sub {m n q : ℕ}
    (A : Matrix (Fin m) (Fin n) (ZMod q)) (s : Fin n → ZMod q) (w w' : Fin m → ZMod q) :
    A.mulVec s + w - w' = A.mulVec s + (w - w') :=
  add_sub_assoc (A.mulVec s) w w'

/-- The Hamming weight (`hammingNorm`) of the difference vector `w - w'` equals the Hamming
distance `hammingDist w w'`. -/
theorem hammingNorm_sub_eq_hammingDist {m q : ℕ} (w w' : Fin m → ZMod q) :
    hammingNorm (w - w') = hammingDist w w' := by
  simp only [hammingNorm, hammingDist, Pi.sub_apply, ne_eq, sub_eq_zero]

/-- Zero-error decoder correctness up to Hamming weight `t`: for every matrix `A`, secret `s`,
and error vector `e` with `hammingNorm e ≤ t`, every outcome in the support of
`decode A (A s + e)` is `some s`. -/
def DecoderCorrect {m n q : ℕ}
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q)))
    (t : ℕ) : Prop :=
  ∀ (A : Matrix (Fin m) (Fin n) (ZMod q)) (s : Fin n → ZMod q) (e : Fin m → ZMod q),
    hammingNorm e ≤ t →
      ∀ sOpt ∈ (ProbComp.eval (decode A (A.mulVec s + e))).support, sOpt = some s

/-- The average-case decoding check on secret `s` and error `e` over a uniform matrix `A`:
sample `A ← Matrix (Fin m) (Fin n) (ZMod q)`, run `decode A (A s + e)`, and test whether the
output equals `some s`. -/
noncomputable def decodeCheck {m n q : ℕ} [NeZero q]
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q)))
    (s : Fin n → ZMod q) (e : Fin m → ZMod q) : ProbComp Bool := do
  let A ← ProbComp.uniform (Matrix (Fin m) (Fin n) (ZMod q))
  let sOpt ← decode A (A.mulVec s + e)
  return decide (sOpt = some s)

/-- The average-case decoding experiment on `(s, e)` as a Boolean `Game`. -/
noncomputable def decodeGame {m n q : ℕ} [NeZero q]
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q)))
    (s : Fin n → ZMod q) (e : Fin m → ZMod q) : Game :=
  ProbComp.eval (decodeCheck decode s e)

/-- Average-case decoder correctness with failure probability at most `δ` up to Hamming weight `t`
([FullerMengReyzin2020], Lemma 4.10): for every secret `s` and error `e` with
`hammingNorm e ≤ t`, `decode A (A s + e)` fails to output `some s` with probability at most `δ`
over uniform `A` and the coins of `decode`. -/
def DecoderCorrectWithError {m n q : ℕ} [NeZero q]
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q)))
    (t : ℕ) (δ : ℝ≥0) : Prop :=
  ∀ (s : Fin n → ZMod q) (e : Fin m → ZMod q),
    hammingNorm e ≤ t → Game.failProbability (decodeGame decode s e) ≤ δ

/-- Zero-error decoder correctness implies zero-error Hamming reproduction correctness of
`decodeThenExtract`. -/
theorem DecoderCorrect.correctHamming_decodeThenExtract {m n q : ℕ} [NeZero q]
    {Seed Key : Type} [Fintype Seed] [Nonempty Seed] [Inhabited Key]
    {decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q))}
    {t : ℕ} (hdec : DecoderCorrect decode t) (ext : (Fin n → ZMod q) → Seed → Key) :
    (decodeThenExtract m n q decode ext).CorrectHamming t := by
  intro w w' hdis r p hrp r' hr'
  change (r, p) ∈ (ProbComp.eval (do
    let A ← ProbComp.uniform (Matrix (Fin m) (Fin n) (ZMod q))
    let s ← ProbComp.uniform (Fin n → ZMod q)
    let x ← ProbComp.uniform Seed
    return (ext s x, DecodeHelper.mk A (A.mulVec s + w) x))).support at hrp
  change r' ∈ (ProbComp.eval (do
    let sOpt ← decode p.matrix (p.cipher - w')
    match sOpt with
    | some s' => return ext s' p.seed
    | none => return default)).support at hr'
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, PMF.mem_support_uniformOfFintype,
    true_and, Prod.mk.injEq] at hrp hr'
  obtain ⟨A, s, x, rfl, rfl⟩ := hrp
  obtain ⟨sOpt, hsOpt, hr'⟩ := hr'
  rw [cipher_sub_eq_mulVec_add_sub] at hsOpt
  have hwt : hammingNorm (w - w') ≤ t := by
    rwa [hammingNorm_sub_eq_hammingDist]
  rw [hdec A s (w - w') hwt sOpt hsOpt] at hr'
  simpa using hr'

/-- Zero-error decoder correctness implies `DecoderCorrectWithError` with error `0`. -/
theorem DecoderCorrect.decoderCorrectWithError_zero {m n q : ℕ} [NeZero q]
    {decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q))}
    {t : ℕ} (hdec : DecoderCorrect decode t) :
    DecoderCorrectWithError decode t 0 := by
  intro s e he
  have hgame : decodeGame decode s e = PMF.pure true := by
    simp only [decodeGame, decodeCheck, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbComp.eval_uniform]
    calc
      (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind (fun A =>
          (ProbComp.eval (decode A (A.mulVec s + e))).bind (fun sOpt =>
            PMF.pure (decide (sOpt = some s))))
        = (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind (fun _ =>
            PMF.pure true) := by
          refine PMF.bind_congr_on_support _ _ _ fun A _ => ?_
          calc
            (ProbComp.eval (decode A (A.mulVec s + e))).bind (fun sOpt =>
                PMF.pure (decide (sOpt = some s)))
              = (ProbComp.eval (decode A (A.mulVec s + e))).bind (fun _ =>
                  PMF.pure true) := by
                refine PMF.bind_congr_on_support _ _ _ fun sOpt hsOpt => ?_
                simp [hdec A s e he sOpt hsOpt]
            _ = PMF.pure true := PMF.bind_const _ _
      _ = PMF.pure true := PMF.bind_const _ _
  rw [hgame]
  simp [Game.failProbability]

/-- Pointwise bound on the reproduction failure probability of `decodeThenExtract`:
whenever `decodeGame decode s (w - w')` fails with probability at most `δ` for every secret `s`,
`reproduceGame w w'` also fails with probability at most `δ`. -/
theorem failProbability_reproduceGame_decodeThenExtract_le {m n q : ℕ} [NeZero q]
    {Seed Key : Type} [Fintype Seed] [Nonempty Seed] [Inhabited Key] [DecidableEq Key]
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q)))
    (ext : (Fin n → ZMod q) → Seed → Key)
    {w w' : Fin m → ZMod q} {δ : ℝ≥0}
    (hδ : ∀ s : Fin n → ZMod q, Game.failProbability (decodeGame decode s (w - w')) ≤ δ) :
    Game.failProbability ((decodeThenExtract m n q decode ext).reproduceGame w w') ≤ δ := by
  rw [← ENNReal.coe_le_coe]
  simp only [Game.failProbability, ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)]
  simp only [FuzzyExtractor.reproduceGame, FuzzyExtractor.reproduceCheck, decodeThenExtract,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    PMF.bind_bind, PMF.pure_bind]
  rw [PMF.bind_comm (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q)))
    (PMF.uniformOfFintype (Fin n → ZMod q))]
  refine PMF.bind_apply_le_on_support _ fun s _ => ?_
  have hs : decodeGame decode s (w - w') false ≤ (δ : ℝ≥0∞) := by
    have := ENNReal.coe_le_coe.mpr (hδ s)
    rwa [Game.failProbability, ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)] at this
  refine le_trans ?_ hs
  simp only [decodeGame, decodeCheck, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_uniform]
  refine PMF.bind_apply_mono_on_support _ false fun A _ => ?_
  refine PMF.bind_apply_le_on_support _ fun x _ => ?_
  rw [cipher_sub_eq_mulVec_add_sub]
  refine PMF.bind_apply_mono_on_support _ false fun sOpt _ => ?_
  by_cases h : sOpt = some s
  · subst h
    simp
  · rw [decide_eq_false h, PMF.pure_apply_self]
    exact PMF.coe_le_one _ _

/-- Average-case decoder correctness with error `δ` implies `δ`-error Hamming reproduction
correctness of `decodeThenExtract` ([FullerMengReyzin2020], Theorem 4.11). -/
theorem DecoderCorrectWithError.correctHammingWithError_decodeThenExtract
    {m n q : ℕ} [NeZero q]
    {Seed Key : Type} [Fintype Seed] [Nonempty Seed] [Inhabited Key] [DecidableEq Key]
    {decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q))}
    {t : ℕ} {δ : ℝ≥0}
    (hdec : DecoderCorrectWithError decode t δ)
    (ext : (Fin n → ZMod q) → Seed → Key) :
    (decodeThenExtract m n q decode ext).CorrectHammingWithError t δ := by
  intro w w' hdis
  refine failProbability_reproduceGame_decodeThenExtract_le decode ext fun s => ?_
  refine hdec s (w - w') ?_
  rwa [hammingNorm_sub_eq_hammingDist]

/-! ### Hybrid distributions and security reduction -/

/-- The real joint distribution `(s, ⟨A, A s + w⟩)` of the secret `s` and LWE context
`(A, A s + w)` for a source `W : PMF (Fin m → ZMod q)`. -/
noncomputable def realContextDistribution (m n q : ℕ) [NeZero q]
    (W : PMF (Fin m → ZMod q)) : PMF ((Fin n → ZMod q) × DecodeContext m n q) := do
  let w ← W
  let A ← PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))
  let s ← PMF.uniformOfFintype (Fin n → ZMod q)
  pure (s, ⟨A, A.mulVec s + w⟩)

/-- The uniform context distribution `(s, ⟨A, u⟩)` where `A`, `u`, and `s` are independent and
uniform. -/
noncomputable def uniformContextDistribution (m n q : ℕ) [NeZero q] :
    PMF ((Fin n → ZMod q) × DecodeContext m n q) := do
  let A ← PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))
  let u ← PMF.uniformOfFintype (Fin m → ZMod q)
  let s ← PMF.uniformOfFintype (Fin n → ZMod q)
  pure (s, ⟨A, u⟩)

/-- The hybrid fuzzy-extractor distribution `(ext s x, ⟨A, u, x⟩)` in which the code-offset
ciphertext `c = A s + w` is replaced by an independent uniform vector `u`. -/
noncomputable def hybridDistribution (m n q : ℕ) [NeZero q]
    {Seed Key : Type} [Fintype Seed] [Nonempty Seed]
    (ext : (Fin n → ZMod q) → Seed → Key) : PMF (Key × DecodeHelper m n q Seed) := do
  let A ← PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))
  let u ← PMF.uniformOfFintype (Fin m → ZMod q)
  let s ← PMF.uniformOfFintype (Fin n → ZMod q)
  let x ← PMF.uniformOfFintype Seed
  pure (ext s x, ⟨A, u, x⟩)

/-- The fully uniform ideal distribution `(r, ⟨A, u, x⟩)` in which both the key `r` and the
ciphertext `u` are uniform and independent of `(A, x)`. -/
noncomputable def uniformIdealDistribution (m n q : ℕ) [NeZero q]
    {Seed Key : Type} [Fintype Seed] [Nonempty Seed] [Fintype Key] [Nonempty Key] :
    PMF (Key × DecodeHelper m n q Seed) := do
  let A ← PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))
  let u ← PMF.uniformOfFintype (Fin m → ZMod q)
  let x ← PMF.uniformOfFintype Seed
  let r ← PMF.uniformOfFintype Key
  pure (r, ⟨A, u, x⟩)

/-- The real Decisional LWE distribution `(A, A s + w)` for error source `W`
([FullerMengReyzin2020], Definition 4.5). -/
noncomputable def lweRealContext (m n q : ℕ) [NeZero q]
    (W : PMF (Fin m → ZMod q)) : PMF (DecodeContext m n q) := do
  let w ← W
  let A ← PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))
  let s ← PMF.uniformOfFintype (Fin n → ZMod q)
  pure ⟨A, A.mulVec s + w⟩

/-- The uniform Decisional LWE distribution `(A, u)` ([FullerMengReyzin2020], Definition 4.5). -/
noncomputable def lweUniformContext (m n q : ℕ) [NeZero q] : PMF (DecodeContext m n q) := do
  let A ← PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))
  let u ← PMF.uniformOfFintype (Fin m → ZMod q)
  pure ⟨A, u⟩

/-- The Decisional LWE advantage of a context distinguisher `B` on error distribution `W`
([FullerMengReyzin2020], Definition 4.5). -/
noncomputable abbrev lweContextAdvantage (m n q : ℕ) [NeZero q]
    (W : PMF (Fin m → ZMod q)) (B : DecodeContext m n q → PMF Bool) : ℝ≥0 :=
  Game.advantage ((lweRealContext m n q W).bind B) ((lweUniformContext m n q).bind B)

/-- Reduction from a `(secret, context)` pair `(s, ⟨A, c⟩)` to a fuzzy-extractor distinguisher
`D`: sample uniform seed `x ← Seed` and run `D (ext s x, ⟨A, c, x⟩)`. -/
noncomputable def realContextReduction {m n q : ℕ} {Seed Key : Type}
    [Fintype Seed] [Nonempty Seed]
    (ext : (Fin n → ZMod q) → Seed → Key)
    (D : Key × DecodeHelper m n q Seed → PMF Bool)
    (sc : (Fin n → ZMod q) × DecodeContext m n q) : PMF Bool := do
  let x ← PMF.uniformOfFintype Seed
  D (ext sc.1 x, ⟨sc.2.matrix, sc.2.cipher, x⟩)

/-- Reduction from a Decisional LWE context `⟨A, c⟩` to a fuzzy-extractor distinguisher `D`
in the ideal game: sample uniform seed `x ← Seed` and uniform key `r ← Key`, and run
`D (r, ⟨A, c, x⟩)`. -/
noncomputable def idealLweReduction {m n q : ℕ} {Seed Key : Type}
    [Fintype Seed] [Nonempty Seed] [Fintype Key] [Nonempty Key]
    (D : Key × DecodeHelper m n q Seed → PMF Bool)
    (ctx : DecodeContext m n q) : PMF Bool := do
  let x ← PMF.uniformOfFintype Seed
  let r ← PMF.uniformOfFintype Key
  D (r, ⟨ctx.matrix, ctx.cipher, x⟩)

/-- Running `realContextReduction ext D` on `realContextDistribution` equals the real
fuzzy-extractor game of `decodeThenExtract`. -/
theorem realContextDistribution_bind_realContextReduction (m n q : ℕ) [NeZero q]
    {Seed Key : Type} [Fintype Seed] [Nonempty Seed] [Inhabited Key]
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q)))
    (ext : (Fin n → ZMod q) → Seed → Key)
    (W : PMF (Fin m → ZMod q)) (D : Key × DecodeHelper m n q Seed → PMF Bool) :
    (realContextDistribution m n q W).bind (realContextReduction ext D) =
      (decodeThenExtract m n q decode ext).realGame W D := by
  simp only [realContextDistribution, realContextReduction, FuzzyExtractor.realGame,
    FuzzyExtractor.realDistribution, decodeThenExtract, ProbComp.eval_bind,
    ProbComp.eval_pure, ProbComp.eval_uniform, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]

/-- Running `realContextReduction ext D` on `uniformContextDistribution` equals the hybrid game
`(hybridDistribution m n q ext).bind D`. -/
theorem uniformContextDistribution_bind_realContextReduction (m n q : ℕ) [NeZero q]
    {Seed Key : Type} [Fintype Seed] [Nonempty Seed]
    (ext : (Fin n → ZMod q) → Seed → Key)
    (D : Key × DecodeHelper m n q Seed → PMF Bool) :
    (uniformContextDistribution m n q).bind (realContextReduction ext D) =
      (hybridDistribution m n q ext).bind D := by
  simp only [uniformContextDistribution, realContextReduction, hybridDistribution,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]

/-- Running `idealLweReduction D` on `lweRealContext` equals the ideal fuzzy-extractor game of
`decodeThenExtract`. -/
theorem lweRealContext_bind_idealLweReduction (m n q : ℕ) [NeZero q]
    {Seed Key : Type} [Fintype Seed] [Nonempty Seed] [Fintype Key] [Nonempty Key] [Inhabited Key]
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q)))
    (ext : (Fin n → ZMod q) → Seed → Key)
    (W : PMF (Fin m → ZMod q)) (D : Key × DecodeHelper m n q Seed → PMF Bool) :
    (lweRealContext m n q W).bind (idealLweReduction D) =
      (decodeThenExtract m n q decode ext).idealGame W D := by
  simp only [lweRealContext, idealLweReduction, FuzzyExtractor.idealGame,
    FuzzyExtractor.idealDistribution, decodeThenExtract, ProbComp.eval_bind,
    ProbComp.eval_pure, ProbComp.eval_uniform, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]

/-- Running `idealLweReduction D` on `lweUniformContext` equals the fully uniform ideal game
`(uniformIdealDistribution m n q).bind D`. -/
theorem lweUniformContext_bind_idealLweReduction (m n q : ℕ) [NeZero q]
    {Seed Key : Type} [Fintype Seed] [Nonempty Seed] [Fintype Key] [Nonempty Key]
    (D : Key × DecodeHelper m n q Seed → PMF Bool) :
    (lweUniformContext m n q).bind (idealLweReduction D) =
      (uniformIdealDistribution m n q).bind D := by
  simp only [lweUniformContext, idealLweReduction, uniformIdealDistribution,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]

/-- Three-hop hybrid bound on the fuzzy-extractor advantage of `decodeThenExtract`:
1. replacing `(s, A, A s + w)` with `(s, A, u)` via `realContextReduction ext D`;
2. replacing `ext s x` with uniform `r` on the uniform context `(A, u)`;
3. replacing `(A, u)` back with `(A, A s + w)` in the ideal game via `idealLweReduction D`. -/
theorem securityAdvantage_decodeThenExtract_le_three_hop (m n q : ℕ) [NeZero q]
    {Seed Key : Type} [Fintype Seed] [Nonempty Seed] [Fintype Key] [Nonempty Key] [Inhabited Key]
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q)))
    (ext : (Fin n → ZMod q) → Seed → Key)
    (W : PMF (Fin m → ZMod q)) (D : Key × DecodeHelper m n q Seed → PMF Bool) :
    (decodeThenExtract m n q decode ext).securityAdvantage W D ≤
      Game.advantage
        ((realContextDistribution m n q W).bind (realContextReduction ext D))
        ((uniformContextDistribution m n q).bind (realContextReduction ext D)) +
      Game.advantage
        ((hybridDistribution m n q ext).bind D)
        ((uniformIdealDistribution m n q).bind D) +
      lweContextAdvantage m n q W (idealLweReduction D) := by
  rw [realContextDistribution_bind_realContextReduction m n q decode ext W D,
    uniformContextDistribution_bind_realContextReduction m n q ext D]
  have hideal : lweContextAdvantage m n q W (idealLweReduction D) =
      Game.advantage ((uniformIdealDistribution m n q).bind D)
        ((decodeThenExtract m n q decode ext).idealGame W D) := by
    rw [lweContextAdvantage, Game.advantage_comm,
      lweRealContext_bind_idealLweReduction m n q decode ext W D,
      lweUniformContext_bind_idealLweReduction m n q D]
  rw [hideal]
  calc
    Game.advantage ((decodeThenExtract m n q decode ext).realGame W D)
        ((decodeThenExtract m n q decode ext).idealGame W D)
      ≤ Game.advantage ((decodeThenExtract m n q decode ext).realGame W D)
          ((uniformIdealDistribution m n q).bind D) +
        Game.advantage ((uniformIdealDistribution m n q).bind D)
          ((decodeThenExtract m n q decode ext).idealGame W D) :=
      Game.advantage_triangle _ _ _
    _ ≤ Game.advantage ((decodeThenExtract m n q decode ext).realGame W D)
          ((hybridDistribution m n q ext).bind D) +
        Game.advantage ((hybridDistribution m n q ext).bind D)
          ((uniformIdealDistribution m n q).bind D) +
        Game.advantage ((uniformIdealDistribution m n q).bind D)
          ((decodeThenExtract m n q decode ext).idealGame W D) := by
      gcongr
      exact Game.advantage_triangle _ _ _

/-- Concrete `2 * ε_lwe + ε_ext` security bound for `decodeThenExtract`:
if both context distinguishing hops are bounded by `ε_lwe` and the extractor hop on uniform
context is bounded by `ε_ext`, then `(decodeThenExtract m n q decode ext).securityAdvantage W D`
is at most `2 * ε_lwe + ε_ext`. -/
theorem securityAdvantage_decodeThenExtract_le (m n q : ℕ) [NeZero q]
    {Seed Key : Type} [Fintype Seed] [Nonempty Seed] [Fintype Key] [Nonempty Key] [Inhabited Key]
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q)))
    (ext : (Fin n → ZMod q) → Seed → Key)
    {W : PMF (Fin m → ZMod q)} {D : Key × DecodeHelper m n q Seed → PMF Bool}
    {ε_lwe ε_ext : ℝ≥0}
    (hlwe₁ : Game.advantage
      ((realContextDistribution m n q W).bind (realContextReduction ext D))
      ((uniformContextDistribution m n q).bind (realContextReduction ext D)) ≤ ε_lwe)
    (hext : Game.advantage
      ((hybridDistribution m n q ext).bind D)
      ((uniformIdealDistribution m n q).bind D) ≤ ε_ext)
    (hlwe₂ : lweContextAdvantage m n q W (idealLweReduction D) ≤ ε_lwe) :
    (decodeThenExtract m n q decode ext).securityAdvantage W D ≤ 2 * ε_lwe + ε_ext := by
  calc
    (decodeThenExtract m n q decode ext).securityAdvantage W D
      ≤ ε_lwe + ε_ext + ε_lwe :=
      (securityAdvantage_decodeThenExtract_le_three_hop m n q decode ext W D).trans
        (add_le_add (add_le_add hlwe₁ hext) hlwe₂)
    _ = 2 * ε_lwe + ε_ext := by ring

/-- Source-family computational security theorem for `decodeThenExtract`. -/
theorem computationallySecureFor_decodeThenExtract (m n q : ℕ) [NeZero q]
    {Seed Key : Type} [Fintype Seed] [Nonempty Seed] [Fintype Key] [Nonempty Key] [Inhabited Key]
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q)))
    (ext : (Fin n → ZMod q) → Seed → Key)
    {sources : Set (PMF (Fin m → ZMod q))}
    {Admissible : (Key × DecodeHelper m n q Seed → PMF Bool) → Prop}
    {ε_lwe ε_ext : ℝ≥0}
    (hlwe₁ : ∀ W ∈ sources, ∀ D, Admissible D →
      Game.advantage
        ((realContextDistribution m n q W).bind (realContextReduction ext D))
        ((uniformContextDistribution m n q).bind (realContextReduction ext D)) ≤ ε_lwe)
    (hext : ∀ D, Admissible D →
      Game.advantage
        ((hybridDistribution m n q ext).bind D)
        ((uniformIdealDistribution m n q).bind D) ≤ ε_ext)
    (hlwe₂ : ∀ W ∈ sources, ∀ D, Admissible D →
      lweContextAdvantage m n q W (idealLweReduction D) ≤ ε_lwe) :
    (decodeThenExtract m n q decode ext).ComputationallySecureFor
      sources Admissible (2 * ε_lwe + ε_ext) :=
  fun W hW D hD =>
    securityAdvantage_decodeThenExtract_le m n q decode ext
      (hlwe₁ W hW D hD) (hext D hD) (hlwe₂ W hW D hD)

/-! ### Exact translation invariance for uniform error sources -/

/-- When the source `W` is the uniform distribution over `Fin m → ZMod q`, the real context
distribution `(s, ⟨A, A s + w⟩)` is identically equal to `uniformContextDistribution` because
translation by `A s` is a bijection on `Fin m → ZMod q`. -/
theorem realContextDistribution_uniform (m n q : ℕ) [NeZero q] :
    realContextDistribution m n q (PMF.uniformOfFintype (Fin m → ZMod q)) =
      uniformContextDistribution m n q := by
  simp only [realContextDistribution, uniformContextDistribution,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  rw [PMF.bind_comm (PMF.uniformOfFintype (Fin m → ZMod q))
    (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q)))]
  congr 1 with A : 1
  rw [PMF.bind_comm (PMF.uniformOfFintype (Fin m → ZMod q))
    (PMF.uniformOfFintype (Fin n → ZMod q)),
    PMF.bind_comm (PMF.uniformOfFintype (Fin m → ZMod q))
    (PMF.uniformOfFintype (Fin n → ZMod q))]
  congr 1 with s : 1
  exact PMF.uniformOfFintype_bind_equiv (Equiv.addLeft (A.mulVec s))
    (fun u => PMF.pure (s, DecodeContext.mk A u))

/-- When `W` is the uniform distribution over `Fin m → ZMod q`, `lweRealContext` is identically
equal to `lweUniformContext`. -/
theorem lweRealContext_uniform (m n q : ℕ) [NeZero q] :
    lweRealContext m n q (PMF.uniformOfFintype (Fin m → ZMod q)) =
      lweUniformContext m n q := by
  simp only [lweRealContext, lweUniformContext, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure]
  rw [PMF.bind_comm (PMF.uniformOfFintype (Fin m → ZMod q))
    (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q)))]
  congr 1 with A : 1
  rw [PMF.bind_comm (PMF.uniformOfFintype (Fin m → ZMod q))
    (PMF.uniformOfFintype (Fin n → ZMod q))]
  calc
    (PMF.uniformOfFintype (Fin n → ZMod q)).bind (fun s =>
        (PMF.uniformOfFintype (Fin m → ZMod q)).bind (fun w =>
          PMF.pure (DecodeContext.mk A (A.mulVec s + w))))
      = (PMF.uniformOfFintype (Fin n → ZMod q)).bind (fun _ =>
          (PMF.uniformOfFintype (Fin m → ZMod q)).bind (fun u =>
            PMF.pure (DecodeContext.mk A u))) := by
        congr 1 with s : 1
        exact PMF.uniformOfFintype_bind_equiv (Equiv.addLeft (A.mulVec s))
          (fun u => PMF.pure (DecodeContext.mk A u))
    _ = (PMF.uniformOfFintype (Fin m → ZMod q)).bind (fun u => PMF.pure (DecodeContext.mk A u)) :=
      PMF.bind_const _ _

/-- On a uniform source `W = PMF.uniformOfFintype (Fin m → ZMod q)`, the fuzzy-extractor
distinguishing advantage of `decodeThenExtract` equals the extractor distinguishing advantage on
`uniformContextDistribution`. -/
theorem securityAdvantage_decodeThenExtract_uniform_eq (m n q : ℕ) [NeZero q]
    {Seed Key : Type} [Fintype Seed] [Nonempty Seed] [Fintype Key] [Nonempty Key] [Inhabited Key]
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q)))
    (ext : (Fin n → ZMod q) → Seed → Key)
    (D : Key × DecodeHelper m n q Seed → PMF Bool) :
    (decodeThenExtract m n q decode ext).securityAdvantage
        (PMF.uniformOfFintype (Fin m → ZMod q)) D =
      Game.advantage
        ((hybridDistribution m n q ext).bind D)
        ((uniformIdealDistribution m n q).bind D) := by
  have hreal : (decodeThenExtract m n q decode ext).realGame
      (PMF.uniformOfFintype (Fin m → ZMod q)) D = (hybridDistribution m n q ext).bind D := by
    rw [← realContextDistribution_bind_realContextReduction m n q decode ext,
      realContextDistribution_uniform,
      uniformContextDistribution_bind_realContextReduction]
  have hideal : (decodeThenExtract m n q decode ext).idealGame
      (PMF.uniformOfFintype (Fin m → ZMod q)) D = (uniformIdealDistribution m n q).bind D := by
    rw [← lweRealContext_bind_idealLweReduction m n q decode ext,
      lweRealContext_uniform,
      lweUniformContext_bind_idealLweReduction]
  simp only [FuzzyExtractor.securityAdvantage, hreal, hideal]

/-! ### Zero-loss extractor specialization (`ext s x = s + x`) -/

/-- When the extractor is one-time-pad addition `fun s x => s + x` on `Fin n → ZMod q`,
`hybridDistribution` is identically equal to `uniformIdealDistribution` because translation by `x`
is a bijection on the uniform secret `s`. -/
theorem hybridDistribution_add_eq_uniformIdealDistribution (m n q : ℕ) [NeZero q] :
    hybridDistribution m n q (fun (s x : Fin n → ZMod q) => s + x) =
      uniformIdealDistribution m n q (Seed := Fin n → ZMod q) (Key := Fin n → ZMod q) := by
  simp only [hybridDistribution, uniformIdealDistribution,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  congr 1 with A : 1
  congr 1 with u : 1
  rw [PMF.bind_comm (PMF.uniformOfFintype (Fin n → ZMod q))
    (PMF.uniformOfFintype (Fin n → ZMod q))]
  congr 1 with x : 1
  exact PMF.uniformOfFintype_bind_equiv (Equiv.addRight x)
    (fun r => PMF.pure (r, DecodeHelper.mk A u x))

/-- For the additive extractor `fun s x => s + x`, the extractor hop vanishes (`ε_ext = 0`),
so the fuzzy-extractor distinguishing advantage is at most `2 * ε_lwe`. -/
theorem securityAdvantage_decodeThenExtract_add_le (m n q : ℕ) [NeZero q]
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q)))
    {W : PMF (Fin m → ZMod q)}
    {D : (Fin n → ZMod q) × DecodeHelper m n q (Fin n → ZMod q) → PMF Bool}
    {ε_lwe : ℝ≥0}
    (hlwe₁ : Game.advantage
      ((realContextDistribution m n q W).bind
        (realContextReduction (fun (s x : Fin n → ZMod q) => s + x) D))
      ((uniformContextDistribution m n q).bind
        (realContextReduction (fun (s x : Fin n → ZMod q) => s + x) D)) ≤ ε_lwe)
    (hlwe₂ : lweContextAdvantage m n q W (idealLweReduction D) ≤ ε_lwe) :
    (decodeThenExtract m n q decode (fun (s x : Fin n → ZMod q) => s + x)).securityAdvantage
        W D ≤ 2 * ε_lwe := by
  have hext : Game.advantage
      ((hybridDistribution m n q (fun (s x : Fin n → ZMod q) => s + x)).bind D)
      ((uniformIdealDistribution m n q).bind D) ≤ 0 := by
    rw [hybridDistribution_add_eq_uniformIdealDistribution, Game.advantage_self]
  simpa using securityAdvantage_decodeThenExtract_le m n q decode
    (fun (s x : Fin n → ZMod q) => s + x) hlwe₁ hext hlwe₂

/-- On a uniform source `W = PMF.uniformOfFintype (Fin m → ZMod q)` with the additive extractor
`fun s x => s + x`, every distinguisher has fuzzy-extractor advantage `0`. -/
theorem securityAdvantage_decodeThenExtract_add_uniform_eq_zero (m n q : ℕ) [NeZero q]
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q)))
    (D : (Fin n → ZMod q) × DecodeHelper m n q (Fin n → ZMod q) → PMF Bool) :
    (decodeThenExtract m n q decode (fun (s x : Fin n → ZMod q) => s + x)).securityAdvantage
        (PMF.uniformOfFintype (Fin m → ZMod q)) D = 0 := by
  rw [securityAdvantage_decodeThenExtract_uniform_eq,
    hybridDistribution_add_eq_uniformIdealDistribution, Game.advantage_self]

end Cslib.Crypto
