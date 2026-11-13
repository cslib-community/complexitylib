/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Basic
public import CslibFrontier.Crypto.Game.Experiment
public import Mathlib.InformationTheory.Hamming
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform

/-!
# Computational fuzzy extractors and secure sketches

A fuzzy extractor `(Gen, Rep)` over a metric space `(M, dis)` derives a reproducible key `r : Key`
and public helper value `p : Helper` from a noisy source reading `w : M`, and reproduces `r` from
any reading `w'` within distance `t` of `w` using `p` ([DodisOstrovskyReyzinSmith2008], Section 8;
[FullerMengReyzin2020], Section 2.1, Definitions 2.1 and 2.2).

In the computational setting of Fuller, Meng, and Reyzin ([FullerMengReyzin2020], Definition 2.2),
security is parameterized by a family of source distributions `sources : Set (PMF M)` and requires
that for every `W ∈ sources`, the joint distribution `(R, P)` produced by `Gen(W)` is
computationally indistinguishable from `(U, P)`, where `U` is uniform over `Key` and independent of
`P`.

This module also formalizes secure sketches ([FullerMengReyzin2020], Definition 2.3), average-case
extractors (Definition 2.4), and the sketch-and-extract construction (Lemma 2.5), proving that
sketch-and-extract preserves both zero-error and `δ`-error reproduction correctness and transfers
average-case extractor security on `(W, SS(W))` directly to fuzzy-extractor security.

## Main definitions

* `Cslib.Crypto.FuzzyExtractor`: syntax of a fuzzy extractor `(gen, rep)` as `ProbComp` programs.
* `Cslib.Crypto.FuzzyExtractor.reproduceCheck`, `Cslib.Crypto.FuzzyExtractor.reproduceGame`:
  the reproduction correctness experiment on `(w, w')`.
* `Cslib.Crypto.FuzzyExtractor.Correct`, `Cslib.Crypto.FuzzyExtractor.CorrectWithError`,
  `Cslib.Crypto.FuzzyExtractor.CorrectHamming`,
  `Cslib.Crypto.FuzzyExtractor.CorrectHammingWithError`: zero-error and `δ`-error correctness
  for general distance functions and for Hamming distance.
* `Cslib.Crypto.FuzzyExtractor.realDistribution`, `Cslib.Crypto.FuzzyExtractor.idealDistribution`:
  the real `(R, P)` and ideal `(U, P)` distributions on a source `W` (Definition 2.2).
* `Cslib.Crypto.FuzzyExtractor.realExperiment`, `Cslib.Crypto.FuzzyExtractor.idealExperiment`,
  `Cslib.Crypto.FuzzyExtractor.realGame`, `Cslib.Crypto.FuzzyExtractor.idealGame`,
  `Cslib.Crypto.FuzzyExtractor.securityAdvantage`,
  `Cslib.Crypto.FuzzyExtractor.ComputationallySecureFor`: the distinguishing experiments on a fixed
  reading, the games averaging them over `W` with `Cslib.Crypto.Game.withSetup`, the advantage, and
  computational security over a source family (Definition 2.2). Distinguishers are
  `Cslib.Crypto.Experiment` programs `Key → Helper → Experiment`.
* `Cslib.Crypto.SecureSketch`, `Cslib.Crypto.SketchHelper`,
  `Cslib.Crypto.SecureSketch.sketchAndExtract`: secure sketches (Definition 2.3) and the
  sketch-and-extract fuzzy extractor (Lemma 2.5).

## Main results

* `Cslib.Crypto.FuzzyExtractor.Correct.reproduceGame_eq_pure_true`,
  `Cslib.Crypto.FuzzyExtractor.Correct.correctWithError`: zero-error correctness implies
  `reproduceGame w w' = PMF.pure true` and `CorrectWithError` for every `δ`.
* `Cslib.Crypto.FuzzyExtractor.CorrectWithError.one_sub_le_succProbability`: a failure bound `δ`
  implies reproduction success probability at least `1 - δ`.
* `Cslib.Crypto.FuzzyExtractor.realGame_eq_bind`, `Cslib.Crypto.FuzzyExtractor.idealGame_eq_bind`:
  the games are the distinguisher run on `realDistribution W` and `idealDistribution W`.
* `Cslib.Crypto.FuzzyExtractor.securityAdvantage_eq_zero_of_realDistribution_eq`,
  `Cslib.Crypto.FuzzyExtractor.computationallySecureFor_zero_of_realDistribution_eq`:
  exact equality of `(R, P)` and `(U, P)` implies zero distinguishing advantage against all
  distinguishers.
* `Cslib.Crypto.SecureSketch.failProbability_reproduceGame_sketchAndExtract_le`,
  `Cslib.Crypto.SecureSketch.Correct.sketchAndExtract`,
  `Cslib.Crypto.SecureSketch.CorrectWithError.sketchAndExtract`,
  `Cslib.Crypto.SecureSketch.securityAdvantage_sketchAndExtract_eq`: Lemma 2.5 correctness and
  security transfer for sketch-and-extract.

## References

* [Y. Dodis, R. Ostrovsky, L. Reyzin, and A. Smith, *Fuzzy Extractors: How to Generate Strong Keys
  from Biometrics and Other Noisy Data*][DodisOstrovskyReyzinSmith2008], Section 8.
* [B. Fuller, X. Meng, and L. Reyzin, *Computational Fuzzy Extractors*][FullerMengReyzin2020],
  Sections 2.1 and 2.2 (Definitions 2.1–2.4, Lemma 2.5).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability
open scoped ENNReal NNReal

/-- A fuzzy extractor `(Gen, Rep)` over a metric space `M` with extracted key type `Key` and
public helper type `Helper` ([FullerMengReyzin2020], Definitions 2.1 and 2.2). -/
structure FuzzyExtractor (M Key Helper : Type) where
  /-- Generation procedure `Gen(w)`, outputting an extracted key `r` and public helper `p`. -/
  gen : M → ProbComp (Key × Helper)
  /-- Reproduction procedure `Rep(w', p)`, recovering the key from a close reading `w'` and
  helper `p`. -/
  rep : M → Helper → ProbComp Key

namespace FuzzyExtractor

variable {M Key Helper : Type}

/-! ### Reproduction correctness (Definitions 2.1 and 2.2, item 3) -/

/-- The reproduction check program on original reading `w` and noisy reading `w'`: sample
`(r, p) ← Gen(w)`, sample `r' ← Rep(w', p)`, and test whether `r' = r`. -/
def reproduceCheck [DecidableEq Key] (fe : FuzzyExtractor M Key Helper) (w w' : M) :
    ProbComp Bool := do
  let (r, p) ← fe.gen w
  let r' ← fe.rep w' p
  return decide (r' = r)

/-- The reproduction correctness experiment on `(w, w')` as a Boolean `Game`. -/
noncomputable def reproduceGame [DecidableEq Key] (fe : FuzzyExtractor M Key Helper) (w w' : M) :
    Game :=
  ProbComp.eval (fe.reproduceCheck w w')

/-- Unfold `reproduceGame` into `PMF` bind form over `Gen(w)` and `Rep(w', p)`. -/
theorem reproduceGame_eq_bind [DecidableEq Key] (fe : FuzzyExtractor M Key Helper) (w w' : M) :
    fe.reproduceGame w w' = (do
      let (r, p) ← ProbComp.eval (fe.gen w)
      let r' ← ProbComp.eval (fe.rep w' p)
      pure (decide (r' = r))) := by
  simp only [reproduceGame, reproduceCheck, ProbComp.eval_bind, ProbComp.eval_pure]
  congr 1 with ⟨r, p⟩

/-- Zero-error reproduction correctness up to distance `t` with respect to `dis`:
whenever `dis w w' ≤ t`, every `(r, p)` in the support of `Gen(w)` and `r'` in the support of
`Rep(w', p)` satisfies `r' = r`. -/
def Correct (fe : FuzzyExtractor M Key Helper) (dis : M → M → ℕ) (t : ℕ) : Prop :=
  ∀ w w' : M, dis w w' ≤ t →
    ∀ r : Key, ∀ p : Helper, (r, p) ∈ (ProbComp.eval (fe.gen w)).support →
      ∀ r' ∈ (ProbComp.eval (fe.rep w' p)).support, r' = r

/-- Reproduction correctness with error `δ` up to distance `t` ([FullerMengReyzin2020],
Definition 2.1, item 3): whenever `dis w w' ≤ t`, `Rep(w', P)` fails to equal `R` with
probability at most `δ` over the coins of `Gen` and `Rep`. -/
def CorrectWithError [DecidableEq Key] (fe : FuzzyExtractor M Key Helper)
    (dis : M → M → ℕ) (t : ℕ) (δ : ℝ≥0) : Prop :=
  ∀ w w' : M, dis w w' ≤ t → Game.failProbability (fe.reproduceGame w w') ≤ δ

/-- Zero-error reproduction correctness for the Hamming metric on `Fin m → α`. -/
abbrev CorrectHamming {m : ℕ} {α : Type} [DecidableEq α]
    (fe : FuzzyExtractor (Fin m → α) Key Helper) (t : ℕ) : Prop :=
  fe.Correct hammingDist t

/-- Reproduction correctness with error `δ` for the Hamming metric on `Fin m → α`. -/
abbrev CorrectHammingWithError {m : ℕ} {α : Type} [DecidableEq α] [DecidableEq Key]
    (fe : FuzzyExtractor (Fin m → α) Key Helper) (t : ℕ) (δ : ℝ≥0) : Prop :=
  fe.CorrectWithError hammingDist t δ

/-- Under `CorrectWithError`, whenever `dis w w' ≤ t`, `Rep(w', P) = R` holds with probability
at least `1 - δ` ([FullerMengReyzin2020], Definition 2.1, item 3). -/
theorem CorrectWithError.one_sub_le_succProbability [DecidableEq Key]
    {fe : FuzzyExtractor M Key Helper} {dis : M → M → ℕ} {t : ℕ} {δ : ℝ≥0}
    (h : fe.CorrectWithError dis t δ) {w w' : M} (hdis : dis w w' ≤ t) :
    1 - δ ≤ Game.succProbability (fe.reproduceGame w w') := by
  have hfail := h w w' hdis
  have hsum := Game.succProbability_add_failProbability (fe.reproduceGame w w')
  exact tsub_le_iff_right.mpr (by rw [← hsum]; exact add_le_add_right hfail _)

/-- Relaxing the error bound `δ` or shrinking the distance threshold `t` preserves
`CorrectWithError`. -/
theorem CorrectWithError.mono [DecidableEq Key]
    {fe : FuzzyExtractor M Key Helper} {dis : M → M → ℕ} {t₁ t₂ : ℕ} {δ₁ δ₂ : ℝ≥0}
    (h : fe.CorrectWithError dis t₂ δ₁) (ht : t₁ ≤ t₂) (hδ : δ₁ ≤ δ₂) :
    fe.CorrectWithError dis t₁ δ₂ :=
  fun w w' hdis => (h w w' (hdis.trans ht)).trans hδ

/-- Zero-error correctness makes `reproduceGame w w'` identically `PMF.pure true` whenever
`dis w w' ≤ t`. -/
theorem Correct.reproduceGame_eq_pure_true [DecidableEq Key]
    {fe : FuzzyExtractor M Key Helper} {dis : M → M → ℕ} {t : ℕ}
    (h : fe.Correct dis t) {w w' : M} (hdis : dis w w' ≤ t) :
    fe.reproduceGame w w' = PMF.pure true := by
  rw [reproduceGame_eq_bind]
  calc
    (ProbComp.eval (fe.gen w)).bind (fun rp =>
        (ProbComp.eval (fe.rep w' rp.2)).bind (fun r' => PMF.pure (decide (r' = rp.1))))
      = (ProbComp.eval (fe.gen w)).bind (fun _ => PMF.pure true) := by
        refine PMF.bind_congr_on_support _ _ _ fun ⟨r, p⟩ hrp => ?_
        calc
          (ProbComp.eval (fe.rep w' p)).bind (fun r' => PMF.pure (decide (r' = r)))
            = (ProbComp.eval (fe.rep w' p)).bind (fun _ => PMF.pure true) := by
              refine PMF.bind_congr_on_support _ _ _ fun r' hr' => ?_
              simp [h w w' hdis r p hrp r' hr']
          _ = PMF.pure true := PMF.bind_const _ _
    _ = PMF.pure true := PMF.bind_const _ _

/-- Zero-error correctness implies `CorrectWithError` with error `0`. -/
theorem Correct.correctWithError_zero [DecidableEq Key]
    {fe : FuzzyExtractor M Key Helper} {dis : M → M → ℕ} {t : ℕ} (h : fe.Correct dis t) :
    fe.CorrectWithError dis t 0 := by
  intro w w' hdis
  rw [h.reproduceGame_eq_pure_true hdis]
  simp [Game.failProbability]

/-- Zero-error correctness implies `CorrectWithError` for every error bound `δ`. -/
theorem Correct.correctWithError [DecidableEq Key]
    {fe : FuzzyExtractor M Key Helper} {dis : M → M → ℕ} {t : ℕ}
    (h : fe.Correct dis t) (δ : ℝ≥0) :
    fe.CorrectWithError dis t δ :=
  h.correctWithError_zero.mono le_rfl zero_le

/-! ### Computational security (Definition 2.2, item 4) -/

/-- The real joint distribution `(R, P)` produced by `Gen(W)` on a source distribution `W : PMF M`
([FullerMengReyzin2020], Definition 2.2). -/
noncomputable def realDistribution (fe : FuzzyExtractor M Key Helper) (W : PMF M) :
    PMF (Key × Helper) :=
  W.bind fun w => ProbComp.eval (fe.gen w)

/-- The marginal distribution of the public helper string `P` produced by `Gen(W)`. -/
noncomputable def helperDistribution (fe : FuzzyExtractor M Key Helper) (W : PMF M) :
    PMF Helper :=
  (fe.realDistribution W).map Prod.snd

/-- The ideal joint distribution `(U, P)` for a source `W : PMF M`, where `P` is the helper string
from `Gen(W)` and `U` is uniform over `Key` and independent of `P`
([FullerMengReyzin2020], Definition 2.2). -/
noncomputable def idealDistribution [Fintype Key] [Nonempty Key]
    (fe : FuzzyExtractor M Key Helper) (W : PMF M) : PMF (Key × Helper) := do
  let w ← W
  let (_, p) ← ProbComp.eval (fe.gen w)
  let u ← PMF.uniformOfFintype Key
  pure (u, p)

/-- The ideal distribution samples `p ← helperDistribution W` and `u ← uniformOfFintype Key`
independently. -/
theorem idealDistribution_eq_helperDistribution_bind [Fintype Key] [Nonempty Key]
    (fe : FuzzyExtractor M Key Helper) (W : PMF M) :
    fe.idealDistribution W = (do
      let p ← fe.helperDistribution W
      let u ← PMF.uniformOfFintype Key
      pure (u, p)) := by
  simp only [idealDistribution, helperDistribution, realDistribution, PMF.monad_bind_eq_bind,
    PMF.bind_map, PMF.bind_bind, Function.comp_def]

/-- The real distinguishing experiment on a fixed reading `w`: sample `(r, p) ← Gen(w)` and run
`D r p`. -/
def realExperiment (fe : FuzzyExtractor M Key Helper) (w : M)
    (D : Key → Helper → Experiment) : Experiment := do
  let (r, p) ← fe.gen w
  D r p

/-- The ideal distinguishing experiment on a fixed reading `w`: sample `(_, p) ← Gen(w)` and an
independent uniform key `u`, and run `D u p`. -/
noncomputable def idealExperiment [Fintype Key] [Nonempty Key]
    (fe : FuzzyExtractor M Key Helper) (w : M) (D : Key → Helper → Experiment) :
    Experiment := do
  let (_, p) ← fe.gen w
  let u ← ProbComp.uniform Key
  D u p

/-- The real distinguishing game for source `W` and distinguisher `D`: sample `w ← W` and run
`realExperiment w D`. -/
noncomputable def realGame (fe : FuzzyExtractor M Key Helper) (W : PMF M)
    (D : Key → Helper → Experiment) : Game :=
  Game.withSetup W fun w => fe.realExperiment w D

/-- The ideal distinguishing game for source `W` and distinguisher `D`: sample `w ← W` and run
`idealExperiment w D`. -/
noncomputable def idealGame [Fintype Key] [Nonempty Key]
    (fe : FuzzyExtractor M Key Helper) (W : PMF M)
    (D : Key → Helper → Experiment) : Game :=
  Game.withSetup W fun w => fe.idealExperiment w D

/-- The real game runs `D` on a sample of `realDistribution W`. -/
theorem realGame_eq_bind (fe : FuzzyExtractor M Key Helper) (W : PMF M)
    (D : Key → Helper → Experiment) :
    fe.realGame W D = (fe.realDistribution W).bind fun rp => ProbComp.eval (D rp.1 rp.2) := by
  simp only [realGame, Game.withSetup, realExperiment, realDistribution, ProbComp.eval_bind,
    PMF.bind_bind]

/-- The ideal game runs `D` on a sample of `idealDistribution W`. -/
theorem idealGame_eq_bind [Fintype Key] [Nonempty Key] (fe : FuzzyExtractor M Key Helper)
    (W : PMF M) (D : Key → Helper → Experiment) :
    fe.idealGame W D = (fe.idealDistribution W).bind fun up => ProbComp.eval (D up.1 up.2) := by
  simp only [idealGame, Game.withSetup, idealExperiment, idealDistribution,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, ProbComp.eval_bind]
  congr 1 with w : 1
  congr 1 with ⟨r, p⟩
  simp only [ProbComp.eval_uniform, PMF.pure_bind]

/-- The distinguishing advantage `δ^D((R, P), (U, P))` of `D` on source `W`
([FullerMengReyzin2020], Definition 2.2). -/
noncomputable abbrev securityAdvantage [Fintype Key] [Nonempty Key]
    (fe : FuzzyExtractor M Key Helper) (W : PMF M)
    (D : Key → Helper → Experiment) : ℝ≥0 :=
  Game.advantage (fe.realGame W D) (fe.idealGame W D)

/-- Concrete computational security of a fuzzy extractor for a source family `sources` against
a distinguisher class `Admissible` with advantage bound `ε`
([FullerMengReyzin2020], Definition 2.2, item 4). -/
def ComputationallySecureFor [Fintype Key] [Nonempty Key]
    (fe : FuzzyExtractor M Key Helper) (sources : Set (PMF M))
    (Admissible : (Key → Helper → Experiment) → Prop) (ε : ℝ≥0) : Prop :=
  ∀ W ∈ sources, ∀ D, Admissible D → fe.securityAdvantage W D ≤ ε

/-- When the real `(R, P)` and ideal `(U, P)` distributions coincide, every distinguisher
(regardless of computational resources) has advantage `0`. -/
theorem securityAdvantage_eq_zero_of_realDistribution_eq [Fintype Key] [Nonempty Key]
    {fe : FuzzyExtractor M Key Helper} {W : PMF M}
    (h : fe.realDistribution W = fe.idealDistribution W)
    (D : Key → Helper → Experiment) :
    fe.securityAdvantage W D = 0 := by
  simp only [securityAdvantage, realGame_eq_bind, idealGame_eq_bind, h, Game.advantage_self]

/-- Exact equality of real and ideal distributions on every source in `sources` implies
`ComputationallySecureFor` with error `0` against any class of distinguishers. -/
theorem computationallySecureFor_zero_of_realDistribution_eq [Fintype Key] [Nonempty Key]
    {fe : FuzzyExtractor M Key Helper} {sources : Set (PMF M)}
    (h : ∀ W ∈ sources, fe.realDistribution W = fe.idealDistribution W)
    (Admissible : (Key → Helper → Experiment) → Prop) :
    fe.ComputationallySecureFor sources Admissible 0 :=
  fun W hW D _ => by rw [securityAdvantage_eq_zero_of_realDistribution_eq (h W hW) D]

/-- Enlarging the error budget `ε`, shrinking the source family, or restricting the admissible
distinguishers preserves `ComputationallySecureFor`. -/
theorem ComputationallySecureFor.mono [Fintype Key] [Nonempty Key]
    {fe : FuzzyExtractor M Key Helper} {sources₁ sources₂ : Set (PMF M)}
    {Admissible₁ Admissible₂ : (Key → Helper → Experiment) → Prop} {ε₁ ε₂ : ℝ≥0}
    (h : fe.ComputationallySecureFor sources₂ Admissible₂ ε₁)
    (hs : sources₁ ⊆ sources₂)
    (ha : ∀ D, Admissible₁ D → Admissible₂ D)
    (hε : ε₁ ≤ ε₂) :
    fe.ComputationallySecureFor sources₁ Admissible₁ ε₂ :=
  fun W hW D hD => (h W (hs hW) D (ha D hD)).trans hε

end FuzzyExtractor

/-! ### Secure sketches and the sketch-and-extract construction (Section 2.2) -/

/-- A secure sketch `(SS, Rec)` over `M` with sketch type `Sketch`
([FullerMengReyzin2020], Definition 2.3). -/
structure SecureSketch (M Sketch : Type) where
  /-- Sketching procedure `SS(w)`, producing a public sketch `s`. -/
  sketch : M → ProbComp Sketch
  /-- Recovery procedure `Rec(w', s)`, recovering `w` from a close reading `w'` and sketch `s`. -/
  recover : M → Sketch → ProbComp M

/-- The public helper value `p = (s, x)` of the sketch-and-extract construction
([FullerMengReyzin2020], Lemma 2.5), pairing a sketch `s` with an extractor seed `x`. -/
structure SketchHelper (Sketch Seed : Type) where
  /-- The public sketch `s ← SS(w)`. -/
  sketch : Sketch
  /-- The public uniform extractor seed `x`. -/
  seed : Seed
  deriving DecidableEq, Repr

namespace SecureSketch

variable {M Sketch Seed Key : Type}

/-- The recovery check program on original reading `w` and noisy reading `w'`: sample
`s ← SS(w)`, sample `wHat ← Rec(w', s)`, and test whether `wHat = w`. -/
def recoverCheck [DecidableEq M] (ss : SecureSketch M Sketch) (w w' : M) : ProbComp Bool := do
  let s ← ss.sketch w
  let wHat ← ss.recover w' s
  return decide (wHat = w)

/-- The recovery correctness experiment on `(w, w')` as a Boolean `Game`. -/
noncomputable def recoverGame [DecidableEq M] (ss : SecureSketch M Sketch) (w w' : M) : Game :=
  ProbComp.eval (ss.recoverCheck w w')

/-- Zero-error recovery correctness up to distance `t` with respect to `dis`. -/
def Correct (ss : SecureSketch M Sketch) (dis : M → M → ℕ) (t : ℕ) : Prop :=
  ∀ w w' : M, dis w w' ≤ t →
    ∀ s ∈ (ProbComp.eval (ss.sketch w)).support,
      ∀ wHat ∈ (ProbComp.eval (ss.recover w' s)).support, wHat = w

/-- Recovery correctness with error `δ` up to distance `t` ([FullerMengReyzin2020],
Definition 2.3, item 3). -/
def CorrectWithError [DecidableEq M] (ss : SecureSketch M Sketch)
    (dis : M → M → ℕ) (t : ℕ) (δ : ℝ≥0) : Prop :=
  ∀ w w' : M, dis w w' ≤ t → Game.failProbability (ss.recoverGame w w') ≤ δ

/-- The sketch-and-extract fuzzy extractor of [FullerMengReyzin2020], Lemma 2.5:
* `Gen(w)` samples `s ← SS(w)` and uniform seed `x ← Seed`, and outputs `(ext w x, ⟨s, x⟩)`;
* `Rep(w', ⟨s, x⟩)` recovers `wHat ← Rec(w', s)` and outputs `ext wHat x`. -/
noncomputable def sketchAndExtract [Fintype Seed] [Nonempty Seed]
    (ss : SecureSketch M Sketch) (ext : M → Seed → Key) :
    FuzzyExtractor M Key (SketchHelper Sketch Seed) where
  gen w := do
    let s ← ss.sketch w
    let x ← ProbComp.uniform Seed
    return (ext w x, ⟨s, x⟩)
  rep w' p := do
    let wHat ← ss.recover w' p.sketch
    return ext wHat p.seed

/-- Zero-error correctness of `sketchAndExtract` ([FullerMengReyzin2020], Lemma 2.5):
if `ss` recovers `w` without error within distance `t`, then `ss.sketchAndExtract ext`
reproduces `r = ext w x` without error within distance `t`. -/
theorem Correct.sketchAndExtract [Fintype Seed] [Nonempty Seed]
    {ss : SecureSketch M Sketch} {dis : M → M → ℕ} {t : ℕ}
    (h : ss.Correct dis t) (ext : M → Seed → Key) :
    (ss.sketchAndExtract ext).Correct dis t := by
  intro w w' hdis r p hrp r' hr'
  change (r, p) ∈ (ProbComp.eval (do
    let s ← ss.sketch w
    let x ← ProbComp.uniform Seed
    return (ext w x, SketchHelper.mk s x))).support at hrp
  change r' ∈ (ProbComp.eval (do
    let wHat ← ss.recover w' p.sketch
    return ext wHat p.seed)).support at hr'
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, PMF.mem_support_uniformOfFintype,
    true_and, Prod.mk.injEq] at hrp hr'
  obtain ⟨s, hs, x, rfl, rfl⟩ := hrp
  obtain ⟨wHat, hwHat, rfl⟩ := hr'
  rw [h w w' hdis s hs wHat hwHat]

/-- For every pair `(w, w')`, the reproduction failure probability of `ss.sketchAndExtract ext`
is at most the recovery failure probability of `ss`: whenever `Rec(w', s) = w`,
`ext (Rec(w', s)) x = ext w x` holds for every seed `x`. -/
theorem failProbability_reproduceGame_sketchAndExtract_le
    [DecidableEq M] [DecidableEq Key] [Fintype Seed] [Nonempty Seed]
    (ss : SecureSketch M Sketch) (ext : M → Seed → Key) (w w' : M) :
    Game.failProbability ((ss.sketchAndExtract ext).reproduceGame w w') ≤
      Game.failProbability (ss.recoverGame w w') := by
  simp only [Game.failProbability]
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) ?_
  simp only [FuzzyExtractor.reproduceGame, FuzzyExtractor.reproduceCheck, recoverGame,
    recoverCheck, sketchAndExtract, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_uniform, PMF.bind_bind, PMF.pure_bind]
  refine PMF.bind_apply_mono_on_support _ false fun s _ => ?_
  refine PMF.bind_apply_le_on_support _ fun x _ => ?_
  refine PMF.bind_apply_mono_on_support _ false fun wHat _ => ?_
  by_cases hw : wHat = w
  · subst hw
    simp
  · rw [decide_eq_false hw, PMF.pure_apply_self]
    exact PMF.coe_le_one _ _

/-- `δ`-error correctness of `sketchAndExtract` ([FullerMengReyzin2020], Lemma 2.5):
if `ss` recovers `w` with error at most `δ` within distance `t`, then `ss.sketchAndExtract ext`
reproduces `r` with error at most `δ` within distance `t`. -/
theorem CorrectWithError.sketchAndExtract
    [DecidableEq M] [DecidableEq Key] [Fintype Seed] [Nonempty Seed]
    {ss : SecureSketch M Sketch} {dis : M → M → ℕ} {t : ℕ} {δ : ℝ≥0}
    (h : ss.CorrectWithError dis t δ) (ext : M → Seed → Key) :
    (ss.sketchAndExtract ext).CorrectWithError dis t δ :=
  fun w w' hdis => (failProbability_reproduceGame_sketchAndExtract_le ss ext w w').trans
    (h w w' hdis)

/-- The joint distribution `(W, SS(W))` of a source reading and its sketch. -/
noncomputable def jointSketch (ss : SecureSketch M Sketch) (W : PMF M) : PMF (M × Sketch) := do
  let w ← W
  let s ← ProbComp.eval (ss.sketch w)
  pure (w, s)

/-- The real average-case extractor distribution `(ext(X, U_d), ⟨Y, U_d⟩)` on a joint source
`(X, Y) : PMF (M × Sketch)` ([FullerMengReyzin2020], Definition 2.4). -/
noncomputable def extractorRealLaw [Fintype Seed] [Nonempty Seed]
    (ext : M → Seed → Key) (XY : PMF (M × Sketch)) :
    PMF (Key × SketchHelper Sketch Seed) := do
  let (w, s) ← XY
  let x ← PMF.uniformOfFintype Seed
  pure (ext w x, ⟨s, x⟩)

/-- The ideal average-case extractor distribution `(U_Key, ⟨Y, U_d⟩)` on a joint source
`(X, Y) : PMF (M × Sketch)` ([FullerMengReyzin2020], Definition 2.4). -/
noncomputable def extractorIdealLaw [Fintype Seed] [Nonempty Seed] [Fintype Key] [Nonempty Key]
    (XY : PMF (M × Sketch)) : PMF (Key × SketchHelper Sketch Seed) := do
  let (_, s) ← XY
  let x ← PMF.uniformOfFintype Seed
  let u ← PMF.uniformOfFintype Key
  pure (u, ⟨s, x⟩)

/-- The real distribution of `ss.sketchAndExtract ext` on `W` is the average-case extractor real
law on `(W, SS(W))`. -/
theorem realDistribution_sketchAndExtract [Fintype Seed] [Nonempty Seed]
    (ss : SecureSketch M Sketch) (ext : M → Seed → Key) (W : PMF M) :
    (ss.sketchAndExtract ext).realDistribution W =
      extractorRealLaw ext (ss.jointSketch W) := by
  simp only [FuzzyExtractor.realDistribution, sketchAndExtract, extractorRealLaw, jointSketch,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]

/-- The ideal distribution of `ss.sketchAndExtract ext` on `W` is the average-case extractor ideal
law on `(W, SS(W))`. -/
theorem idealDistribution_sketchAndExtract
    [Fintype Seed] [Nonempty Seed] [Fintype Key] [Nonempty Key]
    (ss : SecureSketch M Sketch) (ext : M → Seed → Key) (W : PMF M) :
    (ss.sketchAndExtract ext).idealDistribution W =
      extractorIdealLaw (ss.jointSketch W) := by
  simp only [FuzzyExtractor.idealDistribution, sketchAndExtract, extractorIdealLaw, jointSketch,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]

/-- Security of `sketchAndExtract` ([FullerMengReyzin2020], Lemma 2.5): the fuzzy-extractor
distinguishing advantage of `D` on source `W` equals the average-case extractor advantage of `D`
on the joint distribution `(W, SS(W))`. -/
theorem securityAdvantage_sketchAndExtract_eq
    [Fintype Seed] [Nonempty Seed] [Fintype Key] [Nonempty Key]
    (ss : SecureSketch M Sketch) (ext : M → Seed → Key) (W : PMF M)
    (D : Key → SketchHelper Sketch Seed → Experiment) :
    (ss.sketchAndExtract ext).securityAdvantage W D =
      Game.advantage
        ((extractorRealLaw ext (ss.jointSketch W)).bind fun rp => ProbComp.eval (D rp.1 rp.2))
        ((extractorIdealLaw (ss.jointSketch W)).bind fun up => ProbComp.eval (D up.1 up.2)) := by
  simp only [FuzzyExtractor.securityAdvantage, FuzzyExtractor.realGame_eq_bind,
    FuzzyExtractor.idealGame_eq_bind, realDistribution_sketchAndExtract,
    idealDistribution_sketchAndExtract]

end SecureSketch

end Cslib.Crypto
