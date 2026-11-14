/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module

public import CslibFrontier.Crypto.Computational.FuzzyExtractor.Basic
public import CslibFrontier.Crypto.Computational.FuzzyExtractor.DecodeThenExtract
import CslibFrontier.Probability.PMF.Uniform

/-!
# Computational fuzzy extractor tests

Exercise the fuzzy-extractor definitions, the sketch-and-extract construction (Lemma 2.5), and the
LWE decode-then-extract construction (Construction 4.1) on concrete finite-field parameters.
Distinguishers are `Experiment` programs. Includes positive instances (zero-error
sketch-and-extract, the additive extractor on a uniform source, the LWE security bound for
Construction 4.1 at concrete dimensions against `LWE.advantage`, a concrete Hamming distance) and a
separating negative fixture
(`revealingFuzzyExtractor`) that is perfectly reproducible for every distance threshold `t` yet
has distinguishing advantage `1 / 2` on a uniform 1-bit source.
-/

public section

namespace CslibFrontierTests.Crypto.Computational.FuzzyExtractorTest

open Cslib Cslib.Crypto Cslib.Crypto.FuzzyExtractor Cslib.Probability
open scoped ENNReal NNReal

/-! ### Concrete Hamming distance -/

/-- Concrete verification of `hammingDist w w' = 1` on two 3-symbol vectors over `ZMod 5`. -/
example : hammingDist ![(1 : ZMod 5), 2, 3] ![(1 : ZMod 5), 4, 3] = 1 := by
  decide

/-! ### Concrete sketch-and-extract instance (Lemma 2.5) -/

/-- Trivial exact secure sketch on `Fin 3 → ZMod 2` for zero-noise readings (`t = 0`). -/
def trivialSecureSketch : SecureSketch (Fin 3 → ZMod 2) Unit where
  sketch _ := return ()
  recover w' _ := return w'

theorem correct_trivialSecureSketch : trivialSecureSketch.Correct hammingDist 0 := by
  intro w w' hdis s _ wHat hwHat
  simp only [trivialSecureSketch, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hwHat
  have hw : w = w' := hammingDist_eq_zero.mp (Nat.eq_zero_of_le_zero hdis)
  rw [hwHat, hw]

/-- Applying `sketchAndExtract` with the one-time-pad extractor `fun w x => w + x` yields a
zero-error Hamming fuzzy extractor at threshold `t = 0`. -/
theorem correctHamming_trivialSketchAndExtract :
    (trivialSecureSketch.sketchAndExtract (fun (w x : Fin 3 → ZMod 2) => w + x)).CorrectHamming
      0 :=
  correct_trivialSecureSketch.sketchAndExtract _

/-- On identical readings `w' = w`, the reproduction game of the sketch-and-extract instance
always outputs `true` with failure probability `0`. -/
example (w : Fin 3 → ZMod 2) :
    Game.failProbability
      ((trivialSecureSketch.sketchAndExtract
        (fun (v x : Fin 3 → ZMod 2) => v + x)).reproduceGame w w) = 0 := by
  have h := correctHamming_trivialSketchAndExtract.correctWithError_zero w w
    (by simp [hammingDist_self])
  exact le_antisymm h zero_le

/-! ### Concrete decode-then-extract security (Construction 4.1) -/

/-- Concrete instantiation of `decodeThenExtract` on `m = 3, n = 2, q = 5` with the additive
extractor `fun s x => s + x`: on a uniform source `W`, every distinguisher has advantage `0`. -/
theorem securityAdvantage_decodeThenExtract_concrete_zero
    (decode : Matrix (Fin 3) (Fin 2) (ZMod 5) → (Fin 3 → ZMod 5) →
      ProbComp (Option (Fin 2 → ZMod 5)))
    (D : (Fin 2 → ZMod 5) → DecodeHelper 3 2 5 (Fin 2 → ZMod 5) → Experiment) :
    (decodeThenExtract 3 2 5 decode (fun (s x : Fin 2 → ZMod 5) => s + x)).securityAdvantage
        (PMF.uniformOfFintype (Fin 3 → ZMod 5)) D = 0 :=
  securityAdvantage_decodeThenExtract_add_uniform_eq_zero 3 2 5 decode D

/-- Construction 4.1 at `m = 4, k = 1, l = 1, q = 7`: for every source and distinguisher, the
advantage is at most the sum of two dimension-`1` decisional LWE advantages. -/
example
    (decode : Matrix (Fin 4) (Fin (1 + 1)) (ZMod 7) → (Fin 4 → ZMod 7) →
      ProbComp (Option (Fin (1 + 1) → ZMod 7)))
    (W : PMF (Fin 4 → ZMod 7))
    (D : (Fin 1 → ZMod 7) → DecodeHelper 4 (1 + 1) 7 Unit → Experiment) :
    (lweFuzzyExtractor 4 1 1 7 decode).securityAdvantage W D ≤
      LWE.advantage (PMF.uniformOfFintype (Fin 1 → ZMod 7)) W (hardcoreKeyReduction D) +
        LWE.advantage (PMF.uniformOfFintype (Fin 1 → ZMod 7)) W (hardcoreUniformReduction D) :=
  securityAdvantage_lweFuzzyExtractor_le decode W D

/-- With a uniform error distribution, the decisional LWE advantage of every distinguisher is `0`:
`A s + e` is uniform and independent of `(A, s)`. -/
theorem lweAdvantage_uniform_error_eq_zero
    (B : Matrix (Fin 4) (Fin 1) (ZMod 7) → (Fin 4 → ZMod 7) → Experiment) :
    LWE.advantage (PMF.uniformOfFintype (Fin 1 → ZMod 7))
      (PMF.uniformOfFintype (Fin 4 → ZMod 7)) B = 0 := by
  have hreal : LWE.realGame (PMF.uniformOfFintype (Fin 1 → ZMod 7))
      (PMF.uniformOfFintype (Fin 4 → ZMod 7)) B = LWE.randomGame B := by
    simp only [LWE.realGame, LWE.randomGame, LWE.eval_realExperiment,
      LWE.eval_randomExperiment, PMF.monad_bind_eq_bind]
    refine Eq.trans ?_ (PMF.bind_const (PMF.uniformOfFintype (Fin 1 → ZMod 7)) _)
    congr 1 with s : 1
    rw [PMF.bind_comm (PMF.uniformOfFintype (Fin 4 → ZMod 7))]
    congr 1 with A : 1
    exact PMF.uniformOfFintype_bind_equiv (Equiv.addLeft (A.mulVec s))
      (fun b => ProbComp.eval (B A b))
  rw [LWE.advantage, hreal, Game.advantage_self]

/-- For the uniform source, both LWE advantages in `securityAdvantage_lweFuzzyExtractor_le` vanish,
so Construction 4.1 is `0`-secure for it against every distinguisher. -/
example
    (decode : Matrix (Fin 4) (Fin (1 + 1)) (ZMod 7) → (Fin 4 → ZMod 7) →
      ProbComp (Option (Fin (1 + 1) → ZMod 7))) :
    (lweFuzzyExtractor 4 1 1 7 decode).ComputationallySecureFor
      {PMF.uniformOfFintype (Fin 4 → ZMod 7)} (fun _ => True) 0 := by
  intro W hW D _
  rw [Set.mem_singleton_iff] at hW
  subst hW
  simpa only [lweAdvantage_uniform_error_eq_zero, add_zero] using
    securityAdvantage_lweFuzzyExtractor_le decode (PMF.uniformOfFintype (Fin 4 → ZMod 7)) D

/-! ### Separating fixture: reproducible for all `t`, but insecure -/

/-- A fuzzy extractor on `Bool` that outputs `(w, w)`: `Rep` ignores `w'` and returns the helper
bit `p = w`, so reproduction succeeds for every distance threshold `t`, but the helper leaks the
key completely. -/
def revealingFuzzyExtractor : FuzzyExtractor Bool Bool Bool where
  gen w := return (w, w)
  rep _ p := return p

/-- `revealingFuzzyExtractor` is zero-error correct for every distance function `dis` and every
threshold `t`. -/
theorem correct_revealingFuzzyExtractor (dis : Bool → Bool → ℕ) (t : ℕ) :
    revealingFuzzyExtractor.Correct dis t := by
  intro w w' _ r p hrp r' hr'
  simp only [revealingFuzzyExtractor, ProbComp.eval_pure, PMF.mem_support_pure_iff,
    Prod.mk.injEq] at hrp hr'
  rw [hr', hrp.2, hrp.1]

/-- The equality distinguisher on `Bool` keys and helpers, testing whether the key equals the
helper bit. -/
def eqBitDistinguisher (r p : Bool) : Experiment :=
  pure (decide (r = p))

/-- On a uniform 1-bit source, `revealingFuzzyExtractor` has distinguishing advantage `1 / 2`
against `eqBitDistinguisher`. -/
theorem securityAdvantage_revealingFuzzyExtractor :
    revealingFuzzyExtractor.securityAdvantage (PMF.uniformOfFintype Bool) eqBitDistinguisher =
      (1 : ℝ≥0) / 2 := by
  simp only [FuzzyExtractor.securityAdvantage, FuzzyExtractor.realGame_eq_bind,
    FuzzyExtractor.idealGame_eq_bind, FuzzyExtractor.realDistribution,
    FuzzyExtractor.idealDistribution, revealingFuzzyExtractor, eqBitDistinguisher,
    ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind, decide_true, PMF.bind_const,
    Game.advantage, Game.succProbability, PMF.pure_apply_self,
    PMF.bind_apply, PMF.uniformOfFintype_apply, Fintype.card_bool, tsum_bool,
    Bool.true_eq_false, decide_false, PMF.pure_apply, Bool.false_eq_true, ↓reduceIte,
    mul_zero, mul_one, add_zero, zero_add]
  norm_num [NNReal.nndist_eq]
  rw [ENNReal.toNNReal_add] <;>
    norm_num [ENNReal.toNNReal_add, ENNReal.toNNReal_mul, ENNReal.toNNReal_inv,
      ENNReal.toNNReal_ofNat, ENNReal.mul_eq_top, ENNReal.inv_eq_top]
  norm_num [NNReal.sub_def, Real.toNNReal_div]
  rw [Real.toNNReal_of_nonpos (by norm_num)]
  positivity

end CslibFrontierTests.Crypto.Computational.FuzzyExtractorTest
