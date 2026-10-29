/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.PPT
public import Complexity.Computability.Probabilistic.PPT.Capture
public import Complexity.Foundations.Data.BitString.List
public import Complexity.Languages.Probabilistic.BitString
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Map

/-!
# Mild Average-Case Hardness of Functions Against Efficient Heuristics

This module formalizes generic mild average-case hardness definitions for functions
`f : List Bool → ℕ` (and `f : List Bool → ℕ∞`) over the uniform distribution on `{0, 1}^n`
following [Y. Liu and R. Pass, *On One-Way Functions and Kolmogorov Complexity*][LiuPass2020],
together with monotonicity, one-sided-to-symmetric shifting bridges, rounded-logarithm comparison
lemmas, and negative nonvacuity witnesses on the constant zero function. All section, definition,
theorem, lemma, and page locators follow the full version `arXiv:2009.11514v1` (and ECCC TR20-052).

## Main definitions

* `Cslib.Complexity.MildlyHardOnAverage`: mild average-case hardness of exact computation for
  `List Bool → ℕ` against uniform strict PPT heuristics
  ([Liu and Pass, Definition 2.4, §2.3, p. 8 of arXiv:2009.11514v1][LiuPass2020]).
* `Cslib.Complexity.MildlyHardOnAverageToApprox`: mild average-case hardness of symmetric
  $g(n)$-approximation (`Nat.dist v (f x) ≤ g n`, i.e., $|v - f(x)| \le g(|x|)$) for
  `List Bool → ℕ` against uniform strict PPT heuristics
  ([Liu and Pass, Definition 2.5, §2.3, p. 8 of arXiv:2009.11514v1][LiuPass2020]).
* `Cslib.Complexity.MildlyHardOnAverageToOneSidedApprox`: library helper for one-sided
  underestimation error (`f x - g n ≤ v ∧ v ≤ f x`) against uniform strict PPT heuristics.
* `Cslib.Complexity.MildlyHardOnAverageDet`, `Cslib.Complexity.MildlyHardOnAverageToApproxDet`,
  `Cslib.Complexity.MildlyHardOnAverageToOneSidedApproxDet`:
  library specializations to deterministic polynomial-time heuristics.
* `Cslib.Complexity.MildlyHardOnAverageIO`, `Cslib.Complexity.MildlyHardOnAverageToApproxIO`,
  `Cslib.Complexity.MildlyHardOnAverageToOneSidedApproxIO`:
  library infinitely-often (`∃ᶠ n in atTop`) deterministic companions.
* `Cslib.Complexity.MildlyHardOnAverageENat`, `Cslib.Complexity.MildlyHardOnAverageIOENat`:
  library `ℕ∞`-valued companions for `List Bool → ℕ∞`.

## Main results

* `Cslib.Complexity.MildlyHardOnAverageToApprox.mono`,
  `Cslib.Complexity.MildlyHardOnAverageToOneSidedApprox.mono`:
  monotonicity in the approximation error bound `g`.
* `Cslib.Complexity.MildlyHardOnAverageToOneSidedApprox.mildlyHardOnAverageToApprox`:
  shift + gap-scaling bridge converting one-sided $(2 g)$-approximation hardness into symmetric
  $g$-approximation hardness whenever `fun x => g x.length` is computable in polynomial time.
* `Cslib.Complexity.MildlyHardOnAverageToOneSidedApproxDet.mildlyHardOnAverageToApproxDet`: the
  same bridge for deterministic approximation.
* `Cslib.Complexity.MildlyHardOnAverageToApprox.eventually_real_abs_sub_le`:
  upper-rounded integer log window `d * (Nat.log 2 n + 1)` implies the real-valued symmetric window
  $|(v : \mathbb{R}) - f(x)| \le d \log_2 |x|$ of Definition 2.5.
* `Cslib.Complexity.not_mildlyHardOnAverageIO_zero`,
  `Cslib.Complexity.not_mildlyHardOnAverage_zero`:
  negative nonvacuity lemmas showing the constant zero function is not mildly hard on average.

## References

* [Y. Liu and R. Pass, *On One-Way Functions and Kolmogorov Complexity*][LiuPass2020],
  full version `arXiv:2009.11514v1` (Section 2.3).
-/

@[expose] public section

namespace Cslib.Complexity

open Filter Cslib.Probability Cslib.Probability.PMF Turing.MultiTapeTM

/-! ### Average-case hardness definitions
([Liu and Pass, Definitions 2.4 and 2.5, §2.3, p. 8 of arXiv:2009.11514v1][LiuPass2020]) -/

/-- **[Liu and Pass, Definition 2.4, §2.3, p. 8 of arXiv:2009.11514v1][LiuPass2020]:
Mildly hard on average (`MildlyHardOnAverage`).**
A function $f : \{0, 1\}^* \to \mathbb{N}$ is mildly hard on average if there exists a positive
polynomial $p$ such that for every uniform strict PPT heuristic
$\mathcal{H} : \{0, 1\}^* \to \mathrm{ProbComp}\ \mathbb{N}$, for all sufficiently large
$n \in \mathbb{N}$,
$$\Pr_{x \leftarrow \{0, 1\}^n, v \leftarrow \mathcal{H}(x)}[v = f(x)] \le 1 - \frac{1}{p(n)}.$$ -/
def MildlyHardOnAverage (f : List Bool → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, (∀ n, 0 < p.eval n) ∧
    ∀ H : List Bool → ProbComp ℕ, IsPPTOn encBits encNat H →
      ∀ᶠ n in atTop,
        (((BitString.uniformList n).bind fun x =>
          (ProbComp.eval (H x)).map fun v => decide (v = f x)) true).toReal ≤
          1 - 1 / ((p.eval n : ℕ) : ℝ)

/-- **[Liu and Pass, Definition 2.5, §2.3, p. 8 of arXiv:2009.11514v1][LiuPass2020]:
Mildly hard on average to $g$-approximate (`MildlyHardOnAverageToApprox`).**
A function $f : \{0, 1\}^* \to \mathbb{N}$ is mildly hard on average to $g$-approximate if there
exists a positive polynomial $p$ such that for every uniform strict PPT heuristic
$\mathcal{H} : \{0, 1\}^* \to \mathrm{ProbComp}\ \mathbb{N}$, for all sufficiently large
$n \in \mathbb{N}$,
$$\Pr_{x \leftarrow \{0, 1\}^n, v \leftarrow \mathcal{H}(x)}[|v - f(x)| \le g(n)]
  \le 1 - \frac{1}{p(n)},$$
where $|v - f(x)|$ is formalized on $\mathbb{N}$ by the symmetric distance `Nat.dist v (f x)`. -/
def MildlyHardOnAverageToApprox (g : ℕ → ℕ) (f : List Bool → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, (∀ n, 0 < p.eval n) ∧
    ∀ H : List Bool → ProbComp ℕ, IsPPTOn encBits encNat H →
      ∀ᶠ n in atTop,
        (((BitString.uniformList n).bind fun x =>
          (ProbComp.eval (H x)).map fun v =>
            decide (Nat.dist v (f x) ≤ g n)) true).toReal ≤
          1 - 1 / ((p.eval n : ℕ) : ℝ)

/-- **Library helper (`MildlyHardOnAverageToOneSidedApprox`):** one-sided underestimation
approximation hardness against uniform strict PPT heuristics, requiring
$$\Pr_{x \leftarrow \{0, 1\}^n, v \leftarrow \mathcal{H}(x)}[f(x) - g(n) \le v \le f(x)]
  \le 1 - \frac{1}{p(n)}$$
for all sufficiently large $n$. By
`MildlyHardOnAverageToOneSidedApprox.mildlyHardOnAverageToApprox`, one-sided
$(2 g)$-approximation hardness implies symmetric $g$-approximation hardness
(`MildlyHardOnAverageToApprox g f`) whenever `fun x => g x.length` is computable in polynomial time
by shifting any heuristic output down by $g(|x|)$. -/
def MildlyHardOnAverageToOneSidedApprox (g : ℕ → ℕ) (f : List Bool → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, (∀ n, 0 < p.eval n) ∧
    ∀ H : List Bool → ProbComp ℕ, IsPPTOn encBits encNat H →
      ∀ᶠ n in atTop,
        (((BitString.uniformList n).bind fun x =>
          (ProbComp.eval (H x)).map fun v =>
            decide (f x - g n ≤ v ∧ v ≤ f x)) true).toReal ≤
          1 - 1 / ((p.eval n : ℕ) : ℝ)

/-- **Library specialization (`MildlyHardOnAverageDet`):** deterministic polynomial-time heuristic
specialization of `MildlyHardOnAverage`. -/
def MildlyHardOnAverageDet (f : List Bool → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, (∀ n, 0 < p.eval n) ∧
    ∀ H : List Bool → ℕ, ComputableInPolyTime H encBits encNat →
      ∀ᶠ n in atTop,
        (((BitString.uniformList n).map fun x => decide (H x = f x)) true).toReal ≤
          1 - 1 / ((p.eval n : ℕ) : ℝ)

/-- **Library specialization (`MildlyHardOnAverageToApproxDet`):** deterministic polynomial-time
heuristic specialization of `MildlyHardOnAverageToApprox`. -/
def MildlyHardOnAverageToApproxDet (g : ℕ → ℕ) (f : List Bool → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, (∀ n, 0 < p.eval n) ∧
    ∀ H : List Bool → ℕ, ComputableInPolyTime H encBits encNat →
      ∀ᶠ n in atTop,
        (((BitString.uniformList n).map fun x =>
          decide (Nat.dist (H x) (f x) ≤ g n)) true).toReal ≤
          1 - 1 / ((p.eval n : ℕ) : ℝ)

/-- **Library specialization (`MildlyHardOnAverageToOneSidedApproxDet`):** deterministic
polynomial-time heuristic specialization of `MildlyHardOnAverageToOneSidedApprox`. -/
def MildlyHardOnAverageToOneSidedApproxDet (g : ℕ → ℕ) (f : List Bool → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, (∀ n, 0 < p.eval n) ∧
    ∀ H : List Bool → ℕ, ComputableInPolyTime H encBits encNat →
      ∀ᶠ n in atTop,
        (((BitString.uniformList n).map fun x =>
          decide (f x - g n ≤ H x ∧ H x ≤ f x)) true).toReal ≤
          1 - 1 / ((p.eval n : ℕ) : ℝ)

/-- **Library companion (`MildlyHardOnAverageIO`):** infinitely-often (`∃ᶠ n in atTop`)
deterministic-heuristic companion to `MildlyHardOnAverageDet`. -/
def MildlyHardOnAverageIO (f : List Bool → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, (∀ n, 0 < p.eval n) ∧
    ∀ H : List Bool → ℕ, ComputableInPolyTime H encBits encNat →
      ∃ᶠ n in atTop,
        (((BitString.uniformList n).map fun x => decide (H x = f x)) true).toReal ≤
          1 - 1 / ((p.eval n : ℕ) : ℝ)

/-- **Library companion (`MildlyHardOnAverageToApproxIO`):** infinitely-often (`∃ᶠ n in atTop`)
deterministic-heuristic companion to `MildlyHardOnAverageToApproxDet`. -/
def MildlyHardOnAverageToApproxIO (g : ℕ → ℕ) (f : List Bool → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, (∀ n, 0 < p.eval n) ∧
    ∀ H : List Bool → ℕ, ComputableInPolyTime H encBits encNat →
      ∃ᶠ n in atTop,
        (((BitString.uniformList n).map fun x =>
          decide (Nat.dist (H x) (f x) ≤ g n)) true).toReal ≤
          1 - 1 / ((p.eval n : ℕ) : ℝ)

/-- **Library companion (`MildlyHardOnAverageToOneSidedApproxIO`):** infinitely-often
(`∃ᶠ n in atTop`) deterministic-heuristic companion to `MildlyHardOnAverageToOneSidedApproxDet`. -/
def MildlyHardOnAverageToOneSidedApproxIO (g : ℕ → ℕ) (f : List Bool → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, (∀ n, 0 < p.eval n) ∧
    ∀ H : List Bool → ℕ, ComputableInPolyTime H encBits encNat →
      ∃ᶠ n in atTop,
        (((BitString.uniformList n).map fun x =>
          decide (f x - g n ≤ H x ∧ H x ≤ f x)) true).toReal ≤
          1 - 1 / ((p.eval n : ℕ) : ℝ)

/-- **Library companion (`MildlyHardOnAverageENat`):** `ℕ∞`-valued companion to
`MildlyHardOnAverage` for functions `f : List Bool → ℕ∞` such as `Kolmogorov.timeBounded t`. -/
def MildlyHardOnAverageENat (f : List Bool → ℕ∞) : Prop :=
  ∃ p : Polynomial ℕ, (∀ n, 0 < p.eval n) ∧
    ∀ H : List Bool → ProbComp ℕ, IsPPTOn encBits encNat H →
      ∀ᶠ n in atTop,
        (((BitString.uniformList n).bind fun x =>
          (ProbComp.eval (H x)).map fun v : ℕ => decide ((v : ℕ∞) = f x)) true).toReal ≤
          1 - 1 / ((p.eval n : ℕ) : ℝ)

/-- **Library companion (`MildlyHardOnAverageIOENat`):** `ℕ∞`-valued companion to
`MildlyHardOnAverageIO` for functions `f : List Bool → ℕ∞` such as `Kolmogorov.timeBounded t`. -/
def MildlyHardOnAverageIOENat (f : List Bool → ℕ∞) : Prop :=
  ∃ p : Polynomial ℕ, (∀ n, 0 < p.eval n) ∧
    ∀ H : List Bool → ℕ, ComputableInPolyTime H encBits encNat →
      ∃ᶠ n in atTop,
        (((BitString.uniformList n).map fun x => decide ((H x : ℕ∞) = f x)) true).toReal ≤
          1 - 1 / ((p.eval n : ℕ) : ℝ)

/-! ### Monotonicity, shifting, and specialization bridges -/

private theorem bind_map_decide_le_of_imp {n : ℕ} (q : List Bool → PMF ℕ)
    (P Q : List Bool → ℕ → Prop) [∀ x v, Decidable (P x v)] [∀ x v, Decidable (Q x v)]
    (himp : ∀ x ∈ (BitString.uniformList n).support, ∀ v, P x v → Q x v) :
    (((BitString.uniformList n).bind fun x =>
        (q x).map fun v => decide (P x v)) true).toReal ≤
      (((BitString.uniformList n).bind fun x =>
        (q x).map fun v => decide (Q x v)) true).toReal := by
  apply ENNReal.toReal_mono (PMF.apply_ne_top _ _)
  apply PMF.bind_apply_mono_on_support _ true
  intro x hx
  apply PMF.bind_apply_mono_on_support _ true
  intro v _
  simp only [Function.comp_apply, PMF.pure_apply]
  by_cases hp : P x v
  · have hq := himp x hx v hp
    simp [hp, hq]
  · simp [hp]

private theorem map_decide_le_of_imp {n : ℕ} (P Q : List Bool → Prop)
    [∀ x, Decidable (P x)] [∀ x, Decidable (Q x)]
    (himp : ∀ x ∈ (BitString.uniformList n).support, P x → Q x) :
    (((BitString.uniformList n).map fun x => decide (P x)) true).toReal ≤
      (((BitString.uniformList n).map fun x => decide (Q x)) true).toReal := by
  apply ENNReal.toReal_mono (PMF.apply_ne_top _ _)
  apply PMF.bind_apply_mono_on_support _ true
  intro x hx
  simp only [Function.comp_apply, PMF.pure_apply]
  by_cases hp : P x
  · have hq := himp x hx hp
    simp [hp, hq]
  · simp [hp]

/-- Monotonicity of `MildlyHardOnAverageToApprox` in the error window: if $g_1(n) \le g_2(n)$ for
all $n$, then hardness of $g_2$-approximation implies hardness of $g_1$-approximation. -/
theorem MildlyHardOnAverageToApprox.mono {g₁ g₂ : ℕ → ℕ} {f : List Bool → ℕ}
    (hle : ∀ n, g₁ n ≤ g₂ n) (h : MildlyHardOnAverageToApprox g₂ f) :
    MildlyHardOnAverageToApprox g₁ f := by
  obtain ⟨p, hp, hH⟩ := h
  refine ⟨p, hp, fun H hppt => ?_⟩
  filter_upwards [hH H hppt] with n hn
  refine (bind_map_decide_le_of_imp (fun x => ProbComp.eval (H x)) _ _ ?_).trans hn
  intro x _ v hv
  exact hv.trans (hle n)

/-- Monotonicity of `MildlyHardOnAverageToApproxDet` in the error window. -/
theorem MildlyHardOnAverageToApproxDet.mono {g₁ g₂ : ℕ → ℕ} {f : List Bool → ℕ}
    (hle : ∀ n, g₁ n ≤ g₂ n) (h : MildlyHardOnAverageToApproxDet g₂ f) :
    MildlyHardOnAverageToApproxDet g₁ f := by
  obtain ⟨p, hp, hH⟩ := h
  refine ⟨p, hp, fun H hpoly => ?_⟩
  filter_upwards [hH H hpoly] with n hn
  refine (map_decide_le_of_imp _ _ ?_).trans hn
  intro x _ hx
  exact hx.trans (hle n)

/-- Monotonicity of `MildlyHardOnAverageToOneSidedApprox` in the error window. -/
theorem MildlyHardOnAverageToOneSidedApprox.mono {g₁ g₂ : ℕ → ℕ} {f : List Bool → ℕ}
    (hle : ∀ n, g₁ n ≤ g₂ n) (h : MildlyHardOnAverageToOneSidedApprox g₂ f) :
    MildlyHardOnAverageToOneSidedApprox g₁ f := by
  obtain ⟨p, hp, hH⟩ := h
  refine ⟨p, hp, fun H hppt => ?_⟩
  filter_upwards [hH H hppt] with n hn
  refine (bind_map_decide_le_of_imp (fun x => ProbComp.eval (H x)) _ _ ?_).trans hn
  intro x _ v ⟨h1, h2⟩
  have hgn := hle n
  exact ⟨by omega, h2⟩

/-- Monotonicity of `MildlyHardOnAverageToOneSidedApproxDet` in the error window. -/
theorem MildlyHardOnAverageToOneSidedApproxDet.mono {g₁ g₂ : ℕ → ℕ} {f : List Bool → ℕ}
    (hle : ∀ n, g₁ n ≤ g₂ n) (h : MildlyHardOnAverageToOneSidedApproxDet g₂ f) :
    MildlyHardOnAverageToOneSidedApproxDet g₁ f := by
  obtain ⟨p, hp, hH⟩ := h
  refine ⟨p, hp, fun H hpoly => ?_⟩
  filter_upwards [hH H hpoly] with n hn
  refine (map_decide_le_of_imp _ _ ?_).trans hn
  intro x _ ⟨h1, h2⟩
  have hgn := hle n
  exact ⟨by omega, h2⟩

/-- Symmetric $g$-approximation hardness (`MildlyHardOnAverageToApprox g f`) implies one-sided
$g$-approximation hardness (`MildlyHardOnAverageToOneSidedApprox g f`). -/
theorem MildlyHardOnAverageToApprox.mildlyHardOnAverageToOneSidedApprox {g : ℕ → ℕ}
    {f : List Bool → ℕ} (h : MildlyHardOnAverageToApprox g f) :
    MildlyHardOnAverageToOneSidedApprox g f := by
  obtain ⟨p, hp, hH⟩ := h
  refine ⟨p, hp, fun H hppt => ?_⟩
  filter_upwards [hH H hppt] with n hn
  refine (bind_map_decide_le_of_imp (fun x => ProbComp.eval (H x)) _ _ ?_).trans hn
  intro x _ v ⟨h1, h2⟩
  unfold Nat.dist
  omega

/--
**Shift + gap-scaling bridge (`MildlyHardOnAverageToOneSidedApprox.mildlyHardOnAverageToApprox`):**
shifting a symmetric $g$-estimator $\mathcal{H}(x)$ down by $g(|x|)$ produces a one-sided
$(2 g)$-estimator $\mathcal{H}'(x) = \mathcal{H}(x) - g(|x|)$, because $|v - f(x)| \le g(|x|)$
implies $f(x) - 2 g(|x|) \le v - g(|x|) \le f(x)$. Consequently, when `fun x => g x.length` is
computable in polynomial time, one-sided $(2 g)$-approximation hardness against PPT heuristics
implies symmetric $g$-approximation hardness (`MildlyHardOnAverageToApprox g f`). -/
theorem MildlyHardOnAverageToOneSidedApprox.mildlyHardOnAverageToApprox {g : ℕ → ℕ}
    {f : List Bool → ℕ}
    (hg : ComputableInPolyTime (fun x : List Bool => g x.length) encBits encNat)
    (h : MildlyHardOnAverageToOneSidedApprox (fun n => 2 * g n) f) :
    MildlyHardOnAverageToApprox g f := by
  obtain ⟨p, hp, hH⟩ := h
  refine ⟨p, hp, fun H hppt => ?_⟩
  have hsub : ComputableInPolyTime (fun pair : List Bool × ℕ => pair.2 - g pair.1.length)
      (encPair encBits encNat) encNat :=
    ComputableInPolyTime.binary_sub'
      (ComputableInPolyTime.snd encBits encNat)
      (hg.comp (ComputableInPolyTime.fst encBits encNat))
  have hppt' : IsPPTOn encBits encNat (fun x => (fun v => v - g x.length) <$> H x) :=
    hppt.map_with hsub
  filter_upwards [hH (fun x => (fun v => v - g x.length) <$> H x) hppt'] with n hn
  refine (ENNReal.toReal_mono (PMF.apply_ne_top _ _) ?_).trans hn
  apply PMF.bind_apply_mono_on_support _ true
  intro x hx
  have hlen : x.length = n := by
    simp only [BitString.uniformList, PMF.mem_support_map_iff] at hx
    rcases hx with ⟨y, -, rfl⟩
    exact List.length_ofFn
  rw [ProbComp.eval_map, PMF.map_comp]
  apply PMF.bind_apply_mono_on_support _ true
  intro v _
  simp only [Function.comp_apply, PMF.pure_apply, hlen]
  by_cases hdist : Nat.dist v (f x) ≤ g n
  · have h_one_sided : f x - 2 * g n ≤ v - g n ∧ v - g n ≤ f x := by
      unfold Nat.dist at hdist
      omega
    simp [hdist, h_one_sided]
  · simp [hdist]

/-- Deterministic counterpart of
`MildlyHardOnAverageToOneSidedApprox.mildlyHardOnAverageToApprox`. -/
theorem MildlyHardOnAverageToOneSidedApproxDet.mildlyHardOnAverageToApproxDet {g : ℕ → ℕ}
    {f : List Bool → ℕ}
    (hg : ComputableInPolyTime (fun x : List Bool => g x.length) encBits encNat)
    (h : MildlyHardOnAverageToOneSidedApproxDet (fun n => 2 * g n) f) :
    MildlyHardOnAverageToApproxDet g f := by
  obtain ⟨p, hp, hH⟩ := h
  refine ⟨p, hp, fun H hpoly => ?_⟩
  have hpoly' : ComputableInPolyTime (fun x : List Bool => H x - g x.length) encBits encNat :=
    ComputableInPolyTime.binary_sub' hpoly hg
  filter_upwards [hH (fun x => H x - g x.length) hpoly'] with n hn
  refine (map_decide_le_of_imp _ _ ?_).trans hn
  intro x hx hdist
  have hlen : x.length = n := by
    simp only [BitString.uniformList, PMF.mem_support_map_iff] at hx
    rcases hx with ⟨y, -, rfl⟩
    exact List.length_ofFn
  rw [hlen]
  unfold Nat.dist at hdist
  omega

/-- `MildlyHardOnAverageDet` implies `MildlyHardOnAverageIO`. -/
theorem MildlyHardOnAverageDet.mildlyHardOnAverageIO {f : List Bool → ℕ}
    (h : MildlyHardOnAverageDet f) :
    MildlyHardOnAverageIO f := by
  obtain ⟨p, hp, hH⟩ := h
  exact ⟨p, hp, fun H hpoly => (hH H hpoly).frequently⟩

/-- `MildlyHardOnAverageToApproxDet` implies `MildlyHardOnAverageToApproxIO`. -/
theorem MildlyHardOnAverageToApproxDet.mildlyHardOnAverageToApproxIO {g : ℕ → ℕ}
    {f : List Bool → ℕ} (h : MildlyHardOnAverageToApproxDet g f) :
    MildlyHardOnAverageToApproxIO g f := by
  obtain ⟨p, hp, hH⟩ := h
  exact ⟨p, hp, fun H hpoly => (hH H hpoly).frequently⟩

/-- `MildlyHardOnAverageToOneSidedApproxDet` implies `MildlyHardOnAverageToOneSidedApproxIO`. -/
theorem MildlyHardOnAverageToOneSidedApproxDet.mildlyHardOnAverageToOneSidedApproxIO {g : ℕ → ℕ}
    {f : List Bool → ℕ} (h : MildlyHardOnAverageToOneSidedApproxDet g f) :
    MildlyHardOnAverageToOneSidedApproxIO g f := by
  obtain ⟨p, hp, hH⟩ := h
  exact ⟨p, hp, fun H hpoly => (hH H hpoly).frequently⟩

private theorem map_decide_eq_le_dist {f H : List Bool → ℕ} (g n : ℕ) :
    (((BitString.uniformList n).map fun x => decide (H x = f x)) true).toReal ≤
      (((BitString.uniformList n).map fun x =>
        decide (Nat.dist (H x) (f x) ≤ g)) true).toReal :=
  map_decide_le_of_imp _ _ fun x _ heq => by simp [heq]

private theorem map_decide_eq_le_oneSided {f H : List Bool → ℕ} (g n : ℕ) :
    (((BitString.uniformList n).map fun x => decide (H x = f x)) true).toReal ≤
      (((BitString.uniformList n).map fun x =>
        decide (f x - g ≤ H x ∧ H x ≤ f x)) true).toReal :=
  map_decide_le_of_imp _ _ fun x _ heq => by omega

/-- `MildlyHardOnAverageToApproxDet g f` implies `MildlyHardOnAverageDet f`. -/
theorem MildlyHardOnAverageToApproxDet.mildlyHardOnAverageDet {g : ℕ → ℕ} {f : List Bool → ℕ}
    (h : MildlyHardOnAverageToApproxDet g f) :
    MildlyHardOnAverageDet f := by
  obtain ⟨p, hp, hH⟩ := h
  refine ⟨p, hp, fun H hpoly => ?_⟩
  filter_upwards [hH H hpoly] with n hn
  exact (map_decide_eq_le_dist (g n) n).trans hn

/-- `MildlyHardOnAverageToOneSidedApproxDet g f` implies `MildlyHardOnAverageDet f`. -/
theorem MildlyHardOnAverageToOneSidedApproxDet.mildlyHardOnAverageDet {g : ℕ → ℕ}
    {f : List Bool → ℕ} (h : MildlyHardOnAverageToOneSidedApproxDet g f) :
    MildlyHardOnAverageDet f := by
  obtain ⟨p, hp, hH⟩ := h
  refine ⟨p, hp, fun H hpoly => ?_⟩
  filter_upwards [hH H hpoly] with n hn
  exact (map_decide_eq_le_oneSided (g n) n).trans hn

/-- `MildlyHardOnAverageToApproxIO g f` implies `MildlyHardOnAverageIO f`. -/
theorem MildlyHardOnAverageToApproxIO.mildlyHardOnAverageIO {g : ℕ → ℕ} {f : List Bool → ℕ}
    (h : MildlyHardOnAverageToApproxIO g f) :
    MildlyHardOnAverageIO f := by
  obtain ⟨p, hp, hH⟩ := h
  refine ⟨p, hp, fun H hpoly => ?_⟩
  exact (hH H hpoly).mono fun n hn => (map_decide_eq_le_dist (g n) n).trans hn

/-- `MildlyHardOnAverageToOneSidedApproxIO g f` implies `MildlyHardOnAverageIO f`. -/
theorem MildlyHardOnAverageToOneSidedApproxIO.mildlyHardOnAverageIO {g : ℕ → ℕ}
    {f : List Bool → ℕ} (h : MildlyHardOnAverageToOneSidedApproxIO g f) :
    MildlyHardOnAverageIO f := by
  obtain ⟨p, hp, hH⟩ := h
  refine ⟨p, hp, fun H hpoly => ?_⟩
  exact (hH H hpoly).mono fun n hn => (map_decide_eq_le_oneSided (g n) n).trans hn

/-- `MildlyHardOnAverageToApprox` implies `MildlyHardOnAverageToApproxDet` (since every
deterministic polynomial-time heuristic is a strict PPT heuristic). -/
theorem MildlyHardOnAverageToApprox.mildlyHardOnAverageToApproxDet {g : ℕ → ℕ}
    {f : List Bool → ℕ} (h : MildlyHardOnAverageToApprox g f) :
    MildlyHardOnAverageToApproxDet g f := by
  obtain ⟨p, hp, hH⟩ := h
  refine ⟨p, hp, fun H hpoly => ?_⟩
  have hppt : IsPPTOn encBits encNat (fun x => pure (H x)) := hpoly.isPPTOn
  filter_upwards [hH (fun x => pure (H x)) hppt] with n hn
  simp only [ProbComp.eval_pure, PMF.pure_map] at hn
  exact hn

/-- `MildlyHardOnAverageToOneSidedApprox` implies `MildlyHardOnAverageToOneSidedApproxDet`. -/
theorem MildlyHardOnAverageToOneSidedApprox.mildlyHardOnAverageToOneSidedApproxDet {g : ℕ → ℕ}
    {f : List Bool → ℕ} (h : MildlyHardOnAverageToOneSidedApprox g f) :
    MildlyHardOnAverageToOneSidedApproxDet g f := by
  obtain ⟨p, hp, hH⟩ := h
  refine ⟨p, hp, fun H hpoly => ?_⟩
  have hppt : IsPPTOn encBits encNat (fun x => pure (H x)) := hpoly.isPPTOn
  filter_upwards [hH (fun x => pure (H x)) hppt] with n hn
  simp only [ProbComp.eval_pure, PMF.pure_map] at hn
  exact hn

/-- `MildlyHardOnAverage` implies `MildlyHardOnAverageDet`. -/
theorem MildlyHardOnAverage.mildlyHardOnAverageDet {f : List Bool → ℕ}
    (h : MildlyHardOnAverage f) :
    MildlyHardOnAverageDet f := by
  obtain ⟨p, hp, hH⟩ := h
  refine ⟨p, hp, fun H hpoly => ?_⟩
  have hppt : IsPPTOn encBits encNat (fun x => pure (H x)) := hpoly.isPPTOn
  filter_upwards [hH (fun x => pure (H x)) hppt] with n hn
  simp only [ProbComp.eval_pure, PMF.pure_map] at hn
  exact hn

/-- `MildlyHardOnAverage` implies `MildlyHardOnAverageIO`. -/
theorem MildlyHardOnAverage.mildlyHardOnAverageIO {f : List Bool → ℕ}
    (h : MildlyHardOnAverage f) :
    MildlyHardOnAverageIO f :=
  h.mildlyHardOnAverageDet.mildlyHardOnAverageIO

/-- `MildlyHardOnAverageToApprox g f` implies `MildlyHardOnAverage f`. -/
theorem MildlyHardOnAverageToApprox.mildlyHardOnAverage {g : ℕ → ℕ} {f : List Bool → ℕ}
    (h : MildlyHardOnAverageToApprox g f) :
    MildlyHardOnAverage f := by
  obtain ⟨p, hp, hH⟩ := h
  refine ⟨p, hp, fun H hppt => ?_⟩
  filter_upwards [hH H hppt] with n hn
  refine (bind_map_decide_le_of_imp (fun x => ProbComp.eval (H x)) _ _ ?_).trans hn
  intro x _ v heq
  simp [heq]

/-- `MildlyHardOnAverageToOneSidedApprox g f` implies `MildlyHardOnAverage f`. -/
theorem MildlyHardOnAverageToOneSidedApprox.mildlyHardOnAverage {g : ℕ → ℕ} {f : List Bool → ℕ}
    (h : MildlyHardOnAverageToOneSidedApprox g f) :
    MildlyHardOnAverage f := by
  obtain ⟨p, hp, hH⟩ := h
  refine ⟨p, hp, fun H hppt => ?_⟩
  filter_upwards [hH H hppt] with n hn
  refine (bind_map_decide_le_of_imp (fun x => ProbComp.eval (H x)) _ _ ?_).trans hn
  intro x _ v heq
  omega

/-! ### Rounded logarithm bounds and real-valued log window bridge -/

/-- For every $n \in \mathbb{N}$, $\lceil \log_2 n \rceil \le \lfloor \log_2 n \rfloor + 1$. -/
theorem nat_clog_two_le_log_two_succ (n : ℕ) : Nat.clog 2 n ≤ Nat.log 2 n + 1 :=
  Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_succ_log_self Nat.one_lt_two n))

/-- For every $n \ge 1$, the real binary logarithm satisfies
$\log_2 n \le \lfloor \log_2 n \rfloor + 1$. -/
theorem real_logb_two_le_nat_log_two_succ {n : ℕ} (hn : 1 ≤ n) :
    Real.logb 2 (n : ℝ) ≤ (Nat.log 2 n + 1 : ℕ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hn_pos, Real.rpow_natCast]
  have hlt := Nat.lt_pow_succ_log_self Nat.one_lt_two n
  exact_mod_cast hlt.le

/-- Any real-valued symmetric approximation error $|(v : \mathbb{R}) - (w : \mathbb{R})| \le
d \log_2 n$ (for $n \ge 1$) implies the upper-rounded integer distance bound
`Nat.dist v w ≤ d * (Nat.log 2 n + 1)`. -/
theorem nat_dist_le_mul_log_two_succ_of_abs_sub_le_mul_logb {v w d n : ℕ} (hn : 1 ≤ n)
    (h : |(v : ℝ) - (w : ℝ)| ≤ (d : ℝ) * Real.logb 2 (n : ℝ)) :
    Nat.dist v w ≤ d * (Nat.log 2 n + 1) := by
  have hdist_real : ((Nat.dist v w : ℕ) : ℝ) = |(v : ℝ) - (w : ℝ)| := by
    rcases le_total v w with hvw | hwv
    · have h1 : Nat.dist v w = w - v := by
        unfold Nat.dist
        omega
      have hvw_real : (v : ℝ) ≤ (w : ℝ) := by exact_mod_cast hvw
      rw [h1, Nat.cast_sub hvw, abs_of_nonpos (by linarith)]
      ring
    · have h1 : Nat.dist v w = v - w := by
        unfold Nat.dist
        omega
      have hwv_real : (w : ℝ) ≤ (v : ℝ) := by exact_mod_cast hwv
      rw [h1, Nat.cast_sub hwv, abs_of_nonneg (by linarith)]
  have hlog := real_logb_two_le_nat_log_two_succ hn
  have hle : ((Nat.dist v w : ℕ) : ℝ) ≤ ((d * (Nat.log 2 n + 1) : ℕ) : ℝ) := by
    rw [hdist_real, Nat.cast_mul]
    exact h.trans (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg d))
  exact_mod_cast hle

/-- **Real-valued $d \log_2 n$ approximation window bridge:** if `f` is mildly hard on average to
approximate within the upper-rounded integer window `fun n => d * (Nat.log 2 n + 1)`, then `f` is
mildly hard on average to approximate within the real-valued window $d \log_2 n$ of
[Liu and Pass, Definition 2.5 and Theorem 3.1 (c), pp. 8–9 of arXiv:2009.11514v1][LiuPass2020]. -/
theorem MildlyHardOnAverageToApprox.eventually_real_abs_sub_le {d : ℕ} {f : List Bool → ℕ}
    (h : MildlyHardOnAverageToApprox (fun n => d * (Nat.log 2 n + 1)) f) :
    ∃ p : Polynomial ℕ, (∀ n, 0 < p.eval n) ∧
      ∀ H : List Bool → ProbComp ℕ, IsPPTOn encBits encNat H →
        ∀ᶠ n in atTop,
          (((BitString.uniformList n).bind fun x =>
            (ProbComp.eval (H x)).map fun v : ℕ =>
              decide (|(v : ℝ) - (f x : ℝ)| ≤ (d : ℝ) * Real.logb 2 (n : ℝ))) true).toReal ≤
            1 - 1 / ((p.eval n : ℕ) : ℝ) := by
  classical
  obtain ⟨p, hp, hH⟩ := h
  refine ⟨p, hp, fun H hppt => ?_⟩
  filter_upwards [hH H hppt, eventually_ge_atTop 1] with n hn hn1
  refine (bind_map_decide_le_of_imp (fun x => ProbComp.eval (H x))
    (fun x v => |(v : ℝ) - (f x : ℝ)| ≤ (d : ℝ) * Real.logb 2 (n : ℝ))
    (fun x v => Nat.dist v (f x) ≤ d * (Nat.log 2 n + 1)) ?_).trans hn
  intro x _ v hv
  exact nat_dist_le_mul_log_two_succ_of_abs_sub_le_mul_logb hn1 hv

/-! ### Negative-side nonvacuity lemmas for the constant zero function -/

/-- The constant zero function `fun _ => 0` is **not** `MildlyHardOnAverageIO`, because the
constant zero polynomial-time heuristic succeeds with probability $1$ on every input length. -/
theorem not_mildlyHardOnAverageIO_zero : ¬ MildlyHardOnAverageIO (fun _ => 0) := by
  rintro ⟨p, hp, hH⟩
  have h0 : ComputableInPolyTime (fun _ : List Bool => (0 : ℕ)) encBits encNat := by fun_prop
  have hfreq := hH (fun _ => 0) h0
  refine hfreq (Filter.Eventually.of_forall fun n => ?_)
  rw [not_le]
  have hp_pos : (0 : ℝ) < (p.eval n : ℕ) := by exact_mod_cast hp n
  have hdiv_pos : 0 < 1 / ((p.eval n : ℕ) : ℝ) := one_div_pos.mpr hp_pos
  have hval :
      (((BitString.uniformList n).map fun _ => decide ((0 : ℕ) = 0)) true).toReal = 1 := by
    simp
  rw [hval]
  linarith

/-- The constant zero function `fun _ => 0` is not `MildlyHardOnAverageDet`. -/
theorem not_mildlyHardOnAverageDet_zero : ¬ MildlyHardOnAverageDet (fun _ => 0) :=
  fun h => not_mildlyHardOnAverageIO_zero h.mildlyHardOnAverageIO

/-- The constant zero function `fun _ => 0` is not `MildlyHardOnAverage`. -/
theorem not_mildlyHardOnAverage_zero : ¬ MildlyHardOnAverage (fun _ => 0) :=
  fun h => not_mildlyHardOnAverageIO_zero h.mildlyHardOnAverageIO

/-- The constant zero function `fun _ => 0` is not `MildlyHardOnAverageToApproxIO g` for any error
function `g`. -/
theorem not_mildlyHardOnAverageToApproxIO_zero (g : ℕ → ℕ) :
    ¬ MildlyHardOnAverageToApproxIO g (fun _ => 0) :=
  fun h => not_mildlyHardOnAverageIO_zero h.mildlyHardOnAverageIO

/-- The constant zero function `fun _ => 0` is not `MildlyHardOnAverageToApproxDet g` for any error
function `g`. -/
theorem not_mildlyHardOnAverageToApproxDet_zero (g : ℕ → ℕ) :
    ¬ MildlyHardOnAverageToApproxDet g (fun _ => 0) :=
  fun h => not_mildlyHardOnAverageIO_zero h.mildlyHardOnAverageDet.mildlyHardOnAverageIO

/-- The constant zero function `fun _ => 0` is not `MildlyHardOnAverageToApprox g` for any error
function `g`. -/
theorem not_mildlyHardOnAverageToApprox_zero (g : ℕ → ℕ) :
    ¬ MildlyHardOnAverageToApprox g (fun _ => 0) :=
  fun h => not_mildlyHardOnAverageIO_zero h.mildlyHardOnAverage.mildlyHardOnAverageIO

/-- The constant zero function `fun _ => 0` is not `MildlyHardOnAverageToOneSidedApprox g` for any
error function `g`. -/
theorem not_mildlyHardOnAverageToOneSidedApprox_zero (g : ℕ → ℕ) :
    ¬ MildlyHardOnAverageToOneSidedApprox g (fun _ => 0) :=
  fun h => not_mildlyHardOnAverageIO_zero h.mildlyHardOnAverage.mildlyHardOnAverageIO

end Cslib.Complexity
