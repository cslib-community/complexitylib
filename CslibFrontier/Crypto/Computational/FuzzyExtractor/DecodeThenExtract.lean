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
public import CslibFrontier.Crypto.Computational.LWE.Basic
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
`hammingNorm (w - w') = hammingDist w w' ≤ t`, runs a `t`-error decoder `decode A (c - w')` to
recover `s`, and derives the key from `s`.

## Main definitions

* `Cslib.Crypto.FuzzyExtractor.DecodeHelper`: the public helper `(A, c, x)` of the
  decode-then-extract construction.
* `Cslib.Crypto.FuzzyExtractor.decodeThenExtract`: the generic decode-then-extract
  `FuzzyExtractor`, with the key derived from the decoded secret by an arbitrary seeded function
  `ext`.
* `Cslib.Crypto.FuzzyExtractor.lweFuzzyExtractor`: Construction 4.1 as stated in the paper
  (key = the first `k` coordinates of the secret, no seed).
* `Cslib.Crypto.FuzzyExtractor.DecoderCorrect`, `Cslib.Crypto.FuzzyExtractor.decodeCheck`,
  `Cslib.Crypto.FuzzyExtractor.decodeGame`, `Cslib.Crypto.FuzzyExtractor.DecoderCorrectWithError`:
  zero-error and `(1 - δ)` average-case decoding correctness up to Hamming weight `t`.
* `Cslib.Crypto.FuzzyExtractor.joinCols`, `Cslib.Crypto.FuzzyExtractor.hardcoreKeyReduction`,
  `Cslib.Crypto.FuzzyExtractor.hardcoreUniformReduction`: the secret-splitting reductions behind
  Lemma 4.7, as LWE distinguishers `Matrix (Fin m) (Fin l) (ZMod q) → (Fin m → ZMod q) →
  Experiment`.

## Main results

* `Cslib.Crypto.FuzzyExtractor.DecoderCorrect.correctHamming_decodeThenExtract`: zero-error
  decoder correctness implies zero-error Hamming fuzzy-extractor correctness.
* `Cslib.Crypto.FuzzyExtractor.failProbability_reproduceGame_decodeThenExtract_le`,
  `Cslib.Crypto.FuzzyExtractor.DecoderCorrectWithError.correctHammingWithError_decodeThenExtract`:
  `δ`-error average-case decoder correctness over uniform `A` implies `δ`-error Hamming
  fuzzy-extractor correctness (the correctness part of Theorem 4.11, with the decoder of
  Lemma 4.10 taken as a hypothesis).
* `Cslib.Crypto.FuzzyExtractor.securityAdvantage_lweFuzzyExtractor_le`: for every source `W` and
  every distinguisher `D`, the security advantage of `lweFuzzyExtractor` is at most the sum of two
  decisional LWE advantages `Cslib.Crypto.LWE.advantage`, with a uniform secret in dimension `l`
  and error distribution `W`, against explicit reductions that never see the secret of their
  challenge. This is Lemma 4.7 (secret-splitting form) composed into the security part of
  Theorem 4.11.
* `Cslib.Crypto.FuzzyExtractor.realDistribution_decodeThenExtract_add_uniform`,
  `Cslib.Crypto.FuzzyExtractor.securityAdvantage_decodeThenExtract_add_uniform_eq_zero`: sanity
  checks for a uniform source and the additive key derivation `ext s x = s + x`, where the real
  and ideal distributions coincide.

## What is not proved

* Hardness of LWE with error distribution `W` (Theorems 4.6 and 4.8 of the paper, which rest on
  Döttling and Müller-Quade and on Regev); the security theorem is a reduction to that
  assumption, stated as an inequality between advantages.
* Running time of the reductions and asymptotic security, here. The parameters `m, k, l, q` are
  fixed, so `securityAdvantage_lweFuzzyExtractor_le` is a concrete reduction inequality, not a
  security theorem on its own. The module
  `CslibFrontier.Crypto.Computational.FuzzyExtractor.DecodeThenExtract.Security` certifies the
  reductions as strict PPT and proves the asymptotic theorem
  `computationallySecure_lweFuzzyExtractor`.
* Correctness of the decoder of Construction 4.9 (Lemma 4.10); it is a hypothesis.
* The symbol-fixing and block-source results of Section 5.
* No security claim is made for `decodeThenExtract` with a general `ext`: with a public seed and
  an `ext` that reveals the secret (for example `ext s x = s + x`), the key determines the
  secret and the construction is insecure for non-uniform `W`.

## References

* [B. Fuller, X. Meng, and L. Reyzin, *Computational Fuzzy Extractors*][FullerMengReyzin2020],
  Section 4 (Construction 4.1, Definition 4.5, Lemma 4.7, Theorem 4.11).
-/

@[expose] public section

namespace Cslib.Crypto.FuzzyExtractor

open Probability
open scoped ENNReal NNReal

/-- The public helper `p = (A, c, x)` of the decode-then-extract construction
([FullerMengReyzin2020], Construction 4.1), pairing the LWE sample `(A, c)` with the public
extractor seed `x`. -/
structure DecodeHelper (m n q : ℕ) (Seed : Type) where
  /-- The public random matrix `A ∈ Z_q^{m × n}`. -/
  matrix : Matrix (Fin m) (Fin n) (ZMod q)
  /-- The code-offset vector `c = A s + w ∈ Z_q^m`. -/
  cipher : Fin m → ZMod q
  /-- The public extractor seed `x`. -/
  seed : Seed
  deriving DecidableEq

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

/-- The Hamming weight (`hammingNorm`) of the difference vector `w - w'` equals the Hamming
distance `hammingDist w w'`. -/
private theorem hammingNorm_sub_eq_hammingDist {m q : ℕ} (w w' : Fin m → ZMod q) :
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
    (s : Fin n → ZMod q) (e : Fin m → ZMod q) : Experiment := do
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
  rw [add_sub_assoc] at hsOpt
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
  rw [add_sub_assoc]
  refine PMF.bind_apply_mono_on_support _ false fun sOpt _ => ?_
  by_cases h : sOpt = some s
  · subst h
    simp
  · rw [decide_eq_false h, PMF.pure_apply_self]
    exact PMF.coe_le_one _ _

/-- Average-case decoder correctness with error `δ` implies `δ`-error Hamming reproduction
correctness of `decodeThenExtract` (the correctness part of [FullerMengReyzin2020],
Theorem 4.11, with the decoder of Lemma 4.10 taken as the hypothesis `h`). -/
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

/-! ### Exact uniformity for a uniform source -/

/-- A uniform offset `u` absorbs the translation `A s`: over uniform `u`, `A`, and `s`, the
code-offset vector `A s + u` is uniform and independent of `(A, s)`. -/
private theorem uniform_bind_offset {m n q : ℕ} [NeZero q] {α : Type}
    (G : Matrix (Fin m) (Fin n) (ZMod q) → (Fin n → ZMod q) → (Fin m → ZMod q) → PMF α) :
    ((PMF.uniformOfFintype (Fin m → ZMod q)).bind fun u =>
      (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
        (PMF.uniformOfFintype (Fin n → ZMod q)).bind fun s => G A s (A.mulVec s + u)) =
      (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
        (PMF.uniformOfFintype (Fin n → ZMod q)).bind fun s =>
          (PMF.uniformOfFintype (Fin m → ZMod q)).bind fun u => G A s u := by
  rw [PMF.bind_comm (PMF.uniformOfFintype (Fin m → ZMod q))]
  congr 1 with A : 1
  rw [PMF.bind_comm (PMF.uniformOfFintype (Fin m → ZMod q))]
  congr 1 with s : 1
  exact Probability.PMF.uniformOfFintype_bind_equiv (Equiv.addLeft (A.mulVec s)) (G A s)

/-- Sanity check for a uniform source: with `W` uniform on `Fin m → ZMod q` and the additive key
derivation `ext s x = s + x`, the real distribution `(R, P)` of `decodeThenExtract` equals the
ideal distribution `(U, P)`, because translation by `A s` and then by `x` are bijections. -/
theorem realDistribution_decodeThenExtract_add_uniform (m n q : ℕ) [NeZero q]
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q))) :
    (decodeThenExtract m n q decode fun (s x : Fin n → ZMod q) => s + x).realDistribution
        (PMF.uniformOfFintype (Fin m → ZMod q)) =
      (decodeThenExtract m n q decode fun (s x : Fin n → ZMod q) => s + x).idealDistribution
        (PMF.uniformOfFintype (Fin m → ZMod q)) := by
  simp only [realDistribution, idealDistribution, decodeThenExtract, ProbComp.eval_bind,
    ProbComp.eval_pure, ProbComp.eval_uniform, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind]
  refine (uniform_bind_offset fun A s c => (PMF.uniformOfFintype (Fin n → ZMod q)).bind fun x =>
    PMF.pure (s + x, DecodeHelper.mk A c x)).trans (Eq.trans ?_
      (uniform_bind_offset fun A _ c => (PMF.uniformOfFintype (Fin n → ZMod q)).bind fun x =>
        (PMF.uniformOfFintype (Fin n → ZMod q)).bind fun u =>
          PMF.pure (u, DecodeHelper.mk A c x)).symm)
  congr 1 with A : 1
  conv_rhs => rw [PMF.bind_const]
  rw [PMF.bind_comm (PMF.uniformOfFintype (Fin n → ZMod q))
    (PMF.uniformOfFintype (Fin m → ZMod q))]
  congr 1 with c : 1
  rw [PMF.bind_comm (PMF.uniformOfFintype (Fin n → ZMod q))
    (PMF.uniformOfFintype (Fin n → ZMod q))]
  congr 1 with x : 1
  exact Probability.PMF.uniformOfFintype_bind_equiv (Equiv.addRight x)
    (fun u => PMF.pure (u, DecodeHelper.mk A c x))

/-- On a uniform source with the additive key derivation `ext s x = s + x`, every distinguisher
has advantage `0` against `decodeThenExtract`. -/
theorem securityAdvantage_decodeThenExtract_add_uniform_eq_zero (m n q : ℕ) [NeZero q]
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q)))
    (D : (Fin n → ZMod q) → DecodeHelper m n q (Fin n → ZMod q) → Experiment) :
    (decodeThenExtract m n q decode fun (s x : Fin n → ZMod q) => s + x).securityAdvantage
        (PMF.uniformOfFintype (Fin m → ZMod q)) D = 0 :=
  securityAdvantage_eq_zero_of_realDistribution_eq
    (realDistribution_decodeThenExtract_add_uniform m n q decode) D

/-! ### Construction 4.1 with hardcore key coordinates (Lemma 4.7) -/

section Hardcore

variable {m k l q : ℕ} [NeZero q]

/-- The matrix `[A₁ | A₂]` whose first `k` columns are `A₁` and whose last `l` columns are
`A₂`. -/
def joinCols (A₁ : Matrix (Fin m) (Fin k) (ZMod q)) (A₂ : Matrix (Fin m) (Fin l) (ZMod q)) :
    Matrix (Fin m) (Fin (k + l)) (ZMod q) :=
  Matrix.of fun i => Fin.append (A₁ i) (A₂ i)

/-- Splitting the columns identifies pairs `(A₁, A₂)` with matrices `[A₁ | A₂]`. -/
private def joinColsEquiv :
    Matrix (Fin m) (Fin k) (ZMod q) × Matrix (Fin m) (Fin l) (ZMod q) ≃
      Matrix (Fin m) (Fin (k + l)) (ZMod q) where
  toFun A := joinCols A.fst A.snd
  invFun A :=
    (Matrix.of fun i j => A i (Fin.castAdd l j), Matrix.of fun i j => A i (Fin.natAdd k j))
  left_inv A := by
    obtain ⟨A₁, A₂⟩ := A
    ext <;> simp [joinCols]
  right_inv A := by
    ext i j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [joinCols]

omit [NeZero q] in
/-- `[A₁ | A₂] (x₁ ‖ x₂) = A₁ x₁ + A₂ x₂`. -/
private theorem joinCols_mulVec_append (A₁ : Matrix (Fin m) (Fin k) (ZMod q))
    (A₂ : Matrix (Fin m) (Fin l) (ZMod q)) (x₁ : Fin k → ZMod q) (x₂ : Fin l → ZMod q) :
    (joinCols A₁ A₂).mulVec (Fin.append x₁ x₂) = A₁.mulVec x₁ + A₂.mulVec x₂ := by
  ext i
  simp [joinCols, Matrix.mulVec, dotProduct, Fin.sum_univ_add]

/-- Two independent uniform draws pushed through an equivalence `e : α × β ≃ γ` are one uniform
draw from `γ`. -/
private theorem uniform_bind_bind_equiv {α β γ δ : Type} [Fintype α] [Nonempty α] [Fintype β]
    [Nonempty β] [Fintype γ] [Nonempty γ] (e : α × β ≃ γ) (f : γ → PMF δ) :
    ((PMF.uniformOfFintype α).bind fun a =>
      (PMF.uniformOfFintype β).bind fun b => f (e (a, b))) =
      (PMF.uniformOfFintype γ).bind f :=
  Probability.PMF.uniformOfFintype_bind_bind_fst_equiv
    (e.trans (Equiv.prodPUnit γ : γ × Unit ≃ γ).symm) f

/-- Construction 4.1 of [FullerMengReyzin2020] as stated in the paper: the secret is
`x : Fin (k + l) → ZMod q` (the paper takes `k = n/2`), and the key is the first `k` coordinates
`r = x₁, …, x_k`. There is no extractor seed (`Seed = Unit`). -/
noncomputable def lweFuzzyExtractor (m k l q : ℕ) [NeZero q]
    (decode : Matrix (Fin m) (Fin (k + l)) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin (k + l) → ZMod q))) :
    FuzzyExtractor (Fin m → ZMod q) (Fin k → ZMod q) (DecodeHelper m (k + l) q Unit) :=
  decodeThenExtract m (k + l) q decode fun x _ i => x (Fin.castAdd l i)

/-- The real-key branch of the reduction behind [FullerMengReyzin2020], Lemma 4.7 (from
Akavia, Goldwasser, and Vaikuntanathan), as an LWE distinguisher: given a sample `(A₂, c₂)` for
secret dimension `l`, sample `A₁` and `x₁` itself and run `D x₁ ⟨[A₁ | A₂], A₁ x₁ + c₂, ()⟩`.
The reduction never sees the secret of the sample it is given. -/
noncomputable def hardcoreKeyReduction
    (D : (Fin k → ZMod q) → DecodeHelper m (k + l) q Unit → Experiment)
    (A₂ : Matrix (Fin m) (Fin l) (ZMod q)) (c₂ : Fin m → ZMod q) : Experiment := do
  let A₁ ← ProbComp.uniform (Matrix (Fin m) (Fin k) (ZMod q))
  let x₁ ← ProbComp.uniform (Fin k → ZMod q)
  D x₁ ⟨joinCols A₁ A₂, A₁.mulVec x₁ + c₂, ()⟩

/-- The uniform-key branch of the reduction behind [FullerMengReyzin2020], Lemma 4.7: as
`hardcoreKeyReduction`, but `D` receives an independent uniform key `r` in place of `x₁`. -/
noncomputable def hardcoreUniformReduction
    (D : (Fin k → ZMod q) → DecodeHelper m (k + l) q Unit → Experiment)
    (A₂ : Matrix (Fin m) (Fin l) (ZMod q)) (c₂ : Fin m → ZMod q) : Experiment := do
  let A₁ ← ProbComp.uniform (Matrix (Fin m) (Fin k) (ZMod q))
  let x₁ ← ProbComp.uniform (Fin k → ZMod q)
  let r ← ProbComp.uniform (Fin k → ZMod q)
  D r ⟨joinCols A₁ A₂, A₁.mulVec x₁ + c₂, ()⟩

/-- Embedding a dimension-`l` sample `(A₂, A₂ x₂ + w)` into `([A₁ | A₂], A₁ x₁ + A₂ x₂ + w)`
for fresh uniform `A₁, x₁` gives a dimension-`(k + l)` sample with uniform matrix and secret
`x₁ ‖ x₂`. -/
private theorem realGame_embed (W : PMF (Fin m → ZMod q))
    (F : (Fin k → ZMod q) → Matrix (Fin m) (Fin (k + l)) (ZMod q) → (Fin m → ZMod q) →
      PMF Bool) :
    ((PMF.uniformOfFintype (Fin l → ZMod q)).bind fun x₂ => W.bind fun w =>
      (PMF.uniformOfFintype (Matrix (Fin m) (Fin l) (ZMod q))).bind fun A₂ =>
        (PMF.uniformOfFintype (Matrix (Fin m) (Fin k) (ZMod q))).bind fun A₁ =>
          (PMF.uniformOfFintype (Fin k → ZMod q)).bind fun x₁ =>
            F x₁ (joinCols A₁ A₂) (A₁.mulVec x₁ + (A₂.mulVec x₂ + w))) =
      W.bind fun w =>
        (PMF.uniformOfFintype (Matrix (Fin m) (Fin (k + l)) (ZMod q))).bind fun A =>
          (PMF.uniformOfFintype (Fin (k + l) → ZMod q)).bind fun x =>
            F (fun i => x (Fin.castAdd l i)) A (A.mulVec x + w) := by
  rw [PMF.bind_comm (PMF.uniformOfFintype (Fin l → ZMod q)) W]
  congr 1 with w : 1
  rw [PMF.bind_comm (PMF.uniformOfFintype (Fin l → ZMod q))]
  conv_rhs => rw [← uniform_bind_bind_equiv joinColsEquiv,
    PMF.bind_comm (PMF.uniformOfFintype (Matrix (Fin m) (Fin k) (ZMod q)))]
  congr 1 with A₂ : 1
  rw [PMF.bind_comm (PMF.uniformOfFintype (Fin l → ZMod q))]
  congr 1 with A₁ : 1
  conv_rhs => rw [← uniform_bind_bind_equiv (Fin.appendEquiv k l)]
  rw [PMF.bind_comm (PMF.uniformOfFintype (Fin l → ZMod q))]
  congr 1 with x₁ : 1
  congr 1 with x₂ : 1
  change F x₁ _ _ = F (fun i => Fin.append x₁ x₂ (Fin.castAdd l i)) (joinCols A₁ A₂)
    ((joinCols A₁ A₂).mulVec (Fin.append x₁ x₂) + w)
  rw [joinCols_mulVec_append, add_assoc]
  simp

private theorem uniformOfFintype_unit : PMF.uniformOfFintype Unit = PMF.pure () := by
  ext u
  simp

/-- The LWE real game of `hardcoreKeyReduction D` (uniform secret, error law `W`) is the real
fuzzy-extractor game of `lweFuzzyExtractor`. -/
private theorem realGame_hardcoreKeyReduction
    (decode : Matrix (Fin m) (Fin (k + l)) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin (k + l) → ZMod q)))
    (W : PMF (Fin m → ZMod q))
    (D : (Fin k → ZMod q) → DecodeHelper m (k + l) q Unit → Experiment) :
    LWE.realGame (PMF.uniformOfFintype (Fin l → ZMod q)) W (hardcoreKeyReduction D) =
      (lweFuzzyExtractor m k l q decode).realGame W D := by
  have h := realGame_embed (k := k) W fun x₁ A c => ProbComp.eval (D x₁ ⟨A, c, ()⟩)
  simp only [LWE.realGame, LWE.eval_realExperiment, hardcoreKeyReduction, ProbComp.eval_bind,
    ProbComp.eval_uniform, PMF.monad_bind_eq_bind]
  refine h.trans ?_
  simp only [lweFuzzyExtractor, decodeThenExtract, realGame, Game.withSetup, realExperiment,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform, uniformOfFintype_unit,
    PMF.bind_bind, PMF.pure_bind]

/-- The LWE real game of `hardcoreUniformReduction D` (uniform secret, error law `W`) is the
ideal fuzzy-extractor game of `lweFuzzyExtractor`. -/
private theorem realGame_hardcoreUniformReduction
    (decode : Matrix (Fin m) (Fin (k + l)) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin (k + l) → ZMod q)))
    (W : PMF (Fin m → ZMod q))
    (D : (Fin k → ZMod q) → DecodeHelper m (k + l) q Unit → Experiment) :
    LWE.realGame (PMF.uniformOfFintype (Fin l → ZMod q)) W (hardcoreUniformReduction D) =
      (lweFuzzyExtractor m k l q decode).idealGame W D := by
  have h := realGame_embed (k := k) W fun _ A c =>
    (PMF.uniformOfFintype (Fin k → ZMod q)).bind fun r => ProbComp.eval (D r ⟨A, c, ()⟩)
  simp only [LWE.realGame, LWE.eval_realExperiment, hardcoreUniformReduction,
    ProbComp.eval_bind, ProbComp.eval_uniform, PMF.monad_bind_eq_bind]
  refine h.trans ?_
  simp only [lweFuzzyExtractor, decodeThenExtract, idealGame, Game.withSetup, idealExperiment,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform, uniformOfFintype_unit,
    PMF.bind_bind, PMF.pure_bind]

/-- On uniform dimension-`l` samples the two reductions agree: `A₁ x₁ + u` is uniform and
independent of `x₁`, so the key `x₁` is distributed exactly like a fresh uniform key. -/
private theorem randomGame_hardcoreKeyReduction
    (D : (Fin k → ZMod q) → DecodeHelper m (k + l) q Unit → Experiment) :
    LWE.randomGame (hardcoreKeyReduction D) = LWE.randomGame (hardcoreUniformReduction D) := by
  simp only [LWE.randomGame, LWE.eval_randomExperiment, hardcoreKeyReduction,
    hardcoreUniformReduction, ProbComp.eval_bind, ProbComp.eval_uniform]
  congr 1 with A₂ : 1
  refine (uniform_bind_offset fun A₁ x₁ c =>
      ProbComp.eval (D x₁ ⟨joinCols A₁ A₂, c, ()⟩)).trans
    (Eq.trans ?_ (uniform_bind_offset fun A₁ _ c =>
      (PMF.uniformOfFintype (Fin k → ZMod q)).bind fun r =>
        ProbComp.eval (D r ⟨joinCols A₁ A₂, c, ()⟩)).symm)
  congr 1 with A₁ : 1
  rw [PMF.bind_const, PMF.bind_comm]

/-- Security of Construction 4.1 from decisional LWE in dimension `l`
([FullerMengReyzin2020], Lemma 4.7 and the security part of Theorem 4.11): for every source `W`
(used as the LWE error distribution) and every distinguisher `D`, the advantage of `D` against
`lweFuzzyExtractor` is at most the sum of the decisional LWE advantages `LWE.advantage`, with a
uniform secret in dimension `l` and error distribution `W`, of the two explicit reductions
`hardcoreKeyReduction D` and `hardcoreUniformReduction D`.

This is an exact statement with no hypotheses; it does not bound the running time of the
reductions, and it does not prove that LWE with error distribution `W` is hard (the paper obtains
this from Theorem 4.6 for uniform-interval errors). The asymptotic theorem built on it is
`computationallySecure_lweFuzzyExtractor`, whose reductions are certified strict PPT. -/
theorem securityAdvantage_lweFuzzyExtractor_le
    (decode : Matrix (Fin m) (Fin (k + l)) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin (k + l) → ZMod q)))
    (W : PMF (Fin m → ZMod q))
    (D : (Fin k → ZMod q) → DecodeHelper m (k + l) q Unit → Experiment) :
    (lweFuzzyExtractor m k l q decode).securityAdvantage W D ≤
      LWE.advantage (PMF.uniformOfFintype (Fin l → ZMod q)) W (hardcoreKeyReduction D) +
        LWE.advantage (PMF.uniformOfFintype (Fin l → ZMod q)) W (hardcoreUniformReduction D) := by
  simp only [LWE.advantage, securityAdvantage]
  rw [realGame_hardcoreKeyReduction decode, realGame_hardcoreUniformReduction decode,
    randomGame_hardcoreKeyReduction,
    Game.advantage_comm ((lweFuzzyExtractor m k l q decode).idealGame W D)]
  exact Game.advantage_triangle _ _ _

end Hardcore

end Cslib.Crypto.FuzzyExtractor
