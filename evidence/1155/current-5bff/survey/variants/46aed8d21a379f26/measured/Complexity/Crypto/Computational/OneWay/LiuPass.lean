/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.OneWay.CondEPPRG
public import Complexity.Crypto.Computational.OneWay.LiuPassConverse
public import Complexity.Computability.Complexity.AverageCase
public import Complexity.Computability.Kolmogorov.AverageCase
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Foundations.Data.Nat.Asymptotics
import Complexity.Foundations.Data.Nat.Log
import Complexity.Tactic.PPT
import Complexity.Tactic.PolyTime


import Diag1155.Measure
/-!
# One-Way Functions and Average-Case Hardness of Time-Bounded Kolmogorov Complexity

This module proves the **M2a polynomial-threshold form** of the forward direction of the main
theorem of [Y. Liu and R. Pass, *On One-Way Functions and Kolmogorov Complexity*][LiuPass2020]
and combines it with the Section 4 converse
(`Complexity.Crypto.Computational.OneWay.LiuPassConverse`) to establish the headline equivalences
of Theorem 3.1:
* **Forward direction:** if one-way functions exist, then for every constant $d \in \mathbb{N}$
  there exists a polynomial $p(n) \ge n + 1$ such that for every time bound $t(n) \ge p(n)$,
  $t$-time-bounded Kolmogorov complexity $K^t$ is mildly hard on average against uniform strict PPT
  heuristics, and mildly hard on average to approximate within the symmetric error windows
  $d (\lfloor \log_2 n \rfloor + 1)$, $d \lceil \log_2 n \rceil$, $d \lfloor \log_2 n \rfloor$, and
  the real-valued window $d \log_2 n$.
* **Headline equivalences (Theorem 3.1 (a) $\Leftrightarrow$ (b) $\Leftrightarrow$ (c)):**
  one-way functions exist if and only if there exists a polynomial $p(n) \ge n + 1$ such that
  $K^p$ is mildly hard on average (`exists_oneWay_iff_exists_mildlyHardOnAverage_timeBoundedNat`),
  and equivalently in the polynomial-threshold and symmetric approximation forms.

All section, theorem, definition, lemma, and page locators follow the full version
`arXiv:2009.11514v1` (and ECCC TR20-052).

**Time-bound scope note (M2a polynomial-threshold form and $n + 1$-step sufficient clock):**
In [Liu and Pass, Theorem 3.1 (b)–(c), §3, p. 9 of arXiv:2009.11514v1][LiuPass2020], item (b)
quantifies over a polynomial $t(n) > 0$, while item (c) and the post-Theorem 3.1 remark give
hardness for every polynomial $t(n) \ge (1 + \varepsilon) n$. The source obtains that near-linear
range from a *rate-$1$ efficient* condEP-PRG, one whose running time on $n$-bit inputs is
$n + O(n^{c})$ for a constant $c < 1$ ([Liu and Pass, §5.1 and Theorem 5.2, §5.2, p. 11, and
Theorem 5.6, §5.3, p. 17 of arXiv:2009.11514v1][LiuPass2020]), built by a padding construction.
This module proves only the polynomial-threshold form $\exists p,\ \forall t \ge p$ of (c) and of
the threshold consequence; the near-linear range is not formalized.

The threshold comes from the generator's own running-time certificate. The proof of
`CondEPPRG.exists_mildlyHardOnAverageToOneSidedApprox_timeBoundedNat_log_succ` (Theorem 5.2)
applies `Kolmogorov.exists_timeBounded_of_computableInPolyTime` to the truncated generator, which
reads a truncation count in unary and a seed and drops that many trailing output bits. That
theorem extracts constants $c', d'$ bounding the running time by $c' (n + 1)^{d'}$ from the
`ComputableInPolyTime` certificate and takes $p_0(n) = (c' + 1)(n + 1)^{d' + 1}$, where $n$ is the
length of the encoded input. An output of length $m$ comes from an encoded input of length at most
$m + 2 \gamma + 3$, so the threshold is $p_G(m) = p_0(m + 2 \gamma + 3)$, and every $t \ge p_G$
gives the generator's multi-tape machine enough steps to print each output from its seed. In the
native model `DescriptionMethod.universalTM`, $K^t$ counts steps of the described machine, so
`DescriptionMethod.exists_etimeBoundedComplexity_universalTM_le_ofMultiTapeTM` is clock-preserving:
it compares `universalTM` with the generator's machine at the same step bound and contributes only
an additive constant to the description length. The threshold is polynomial because the certificate
bounds the generator's running time only by some polynomial; the near-linear range would need a
rate-$1$ step bound for the generator's machine.

Separately, the literal/copy program bound supplies a program that prints each $n$-bit string
within $n + 1$ steps (`Kolmogorov.timeBoundedNat_le_length_add`). Our statements therefore assume
$p(n) \ge n + 1$ as a sufficient clock hypothesis ensuring finite $K^t$ in the native model (rather
than a lower bound on every program or an equivalence with the source's $t(n) > 0$ convention).

**Symmetric approximation and logarithm rounding:**
[Liu and Pass, Definition 2.5, §2.3, p. 8 of arXiv:2009.11514v1][LiuPass2020] defines
$g$-approximation via the symmetric error bound $|v - f(x)| \le g(|x|)$, formalized on $\mathbb{N}$
by `Cslib.Complexity.MildlyHardOnAverageToApprox` (`Nat.dist v (f x) ≤ g n`). The threshold
distinguisher of Theorem 5.2 directly establishes one-sided underestimation hardness
(`Cslib.Complexity.MildlyHardOnAverageToOneSidedApprox`) for the upper-rounded integer log window
$g(n) = d (\lfloor \log_2 n \rfloor + 1)$ (`d * (Nat.log 2 n + 1)`). Applying the PPT shift and
gap-scaling bridge `MildlyHardOnAverageToOneSidedApprox.mildlyHardOnAverageToApprox` (shifting a
heuristic's output down by $g(|x|)$ and doubling the PRG stretch parameter from $2 d + 3$ to
$4 d + 3$) yields symmetric `MildlyHardOnAverageToApprox` for `d * (Nat.log 2 n + 1)`. Since
$\lfloor \log_2 n \rfloor \le \log_2 n \le \lceil \log_2 n \rceil \le \lfloor \log_2 n \rfloor + 1$
for all $n \ge 1$, monotonicity immediately yields symmetric approximation hardness for
`d * Nat.clog 2 n`, `d * Nat.log 2 n`, and the real-valued $|(v : \mathbb{R}) - K^t(x)| \le
d \log_2 |x|$ window (`OneWay.exists_eventually_real_abs_sub_le_timeBoundedNat`).

## Main results

* `Cslib.Crypto.CondEPPRG.exists_mildlyHardOnAverageToOneSidedApprox_timeBoundedNat_log_succ`:
  a $(1 / n^2, \gamma)$-condEP-PRG with $\gamma \ge 2 d + 3$ implies one-sided
  $d (\lfloor \log_2 n \rfloor + 1)$-approximation hardness of $K^t$ for all $t \ge p_G$
  ([Liu and Pass, Theorem 5.2, §5.2, p. 11 of arXiv:2009.11514v1][LiuPass2020], M2a
  polynomial-threshold one-sided helper).
* `Cslib.Crypto.CondEPPRG.exists_mildlyHardOnAverageToApprox_timeBoundedNat_log_succ`,
  `Cslib.Crypto.CondEPPRG.exists_mildlyHardOnAverageToApprox_timeBoundedNat_clog`,
  `Cslib.Crypto.CondEPPRG.exists_mildlyHardOnAverageToApprox_timeBoundedNat`:
  a $(1 / n^2, \gamma)$-condEP-PRG with $\gamma \ge 4 d + 3$ implies symmetric PPT approximation
  hardness of $K^t$ for all $t \ge p_G$ under $d (\lfloor \log_2 n \rfloor + 1)$,
  $d \lceil \log_2 n \rceil$, and $d \lfloor \log_2 n \rfloor$
  ([Liu and Pass, Theorem 5.2, §5.2, p. 11 of arXiv:2009.11514v1][LiuPass2020], M2a
  polynomial-threshold form).
* `Cslib.Crypto.CondEPPRG.exists_mildlyHardOnAverage_timeBoundedNat`:
  exact average-case PPT hardness specialization of Theorem 5.2 ($\gamma \ge 3$, M2a
  polynomial-threshold form).
* `Cslib.Crypto.OneWay.exists_mildlyHardOnAverageToApprox_timeBoundedNat_log_succ`,
  `Cslib.Crypto.OneWay.exists_mildlyHardOnAverageToApprox_timeBoundedNat_clog`,
  `Cslib.Crypto.OneWay.exists_mildlyHardOnAverageToApprox_timeBoundedNat`,
  `Cslib.Crypto.OneWay.exists_eventually_real_abs_sub_le_timeBoundedNat`:
  every one-way function implies the existence of a polynomial $p$ such that for all $t \ge p$,
  $K^t$ is mildly hard on average to approximate within $d (\lfloor \log_2 n \rfloor + 1)$,
  $d \lceil \log_2 n \rceil$, $d \lfloor \log_2 n \rfloor$, and real $d \log_2 n$ against uniform
  strict PPT heuristics
  ([Liu and Pass, Theorem 3.1 (a) $\Rightarrow$ (c), §3, p. 9 of arXiv:2009.11514v1][LiuPass2020],
  M2a polynomial-threshold form).
* `Cslib.Crypto.OneWay.exists_mildlyHardOnAverage_timeBoundedNat`:
  every one-way function implies the existence of a polynomial $p$ such that for all $t \ge p$,
  $K^t$ is mildly hard on average against uniform strict PPT heuristics
  ([Liu and Pass, Theorem 3.1 (a) $\Rightarrow$ (b), §3, p. 9 of arXiv:2009.11514v1][LiuPass2020],
  M2a polynomial-threshold form).
* `Cslib.Crypto.exists_mildlyHardOnAverageToApprox_of_exists_oneWay`,
  `Cslib.Crypto.exists_mildlyHardOnAverage_of_exists_oneWay`:
  existential M2a polynomial-threshold forms of [Liu and Pass, Theorem 3.1 (a) $\Rightarrow$ (c) and
  (a) $\Rightarrow$ (b), §3, p. 9 of arXiv:2009.11514v1][LiuPass2020].
* `Cslib.Crypto.exists_oneWay_iff_exists_mildlyHardOnAverage_timeBoundedNat`,
  `Cslib.Crypto.exists_oneWay_iff_exists_mildlyHardOnAverageENat_timeBounded`,
  `Cslib.Crypto.exists_oneWay_iff_exists_forall_mildlyHardOnAverage_timeBoundedNat`:
  headline characterizations of one-way functions via average-case hardness of $K^t$
  ([Liu and Pass, Theorem 3.1 (a) $\Leftrightarrow$ (b) and post-Theorem 3.1 threshold consequence,
  §3, p. 9 of arXiv:2009.11514v1][LiuPass2020]).
* `Cslib.Crypto.exists_oneWay_iff_forall_exists_mildlyHardOnAverageToApprox_clog_timeBoundedNat`,
  `Cslib.Crypto.exists_oneWay_iff_forall_exists_mildlyHardOnAverageToApprox_timeBoundedNat`:
  approximation-hardness characterizations of one-way functions
  ([Liu and Pass, Theorem 3.1 (a) $\Leftrightarrow$ (c), §3, p. 9 of
  arXiv:2009.11514v1][LiuPass2020]), together with the upper-rounded log-window variant
  `exists_oneWay_iff_forall_exists_mildlyHardOnAverageToApprox_log_succ_timeBoundedNat`.

## References

* [Y. Liu and R. Pass, *On One-Way Functions and Kolmogorov Complexity*][LiuPass2020],
  full version `arXiv:2009.11514v1` (Sections 3, 4, and 5).
-/


diag1155_install
@[expose] public section

namespace Cslib.Crypto

open Cslib.Complexity Probability Probability.PMF BitString Filter Kolmogorov Turing.MultiTapeTM

/-! ### Stretch schedule helpers -/

private def stretchLen (γ n : ℕ) : ℕ := n + γ * Nat.log 2 n

private theorem stretchLen_succ_le (γ n : ℕ) :
    stretchLen γ (n + 1) ≤ stretchLen γ n + γ + 1 := by
  dsimp [stretchLen]
  have h := Nat.mul_le_mul_left γ (Nat.log_add_one_le 2 n)
  rw [mul_add, mul_one] at h
  omega

private def seedLen (γ m : ℕ) : ℕ :=
  Nat.findGreatest (fun k => stretchLen γ k ≤ m) m + 1

private theorem lt_stretchLen_seedLen (γ m : ℕ) :
    m < stretchLen γ (seedLen γ m) ∧ stretchLen γ (seedLen γ m) ≤ m + γ + 1 := by
  let n₀ := Nat.findGreatest (fun k => stretchLen γ k ≤ m) m
  have hn₀_le_m : n₀ ≤ m := Nat.findGreatest_le m
  have hn₀_spec : stretchLen γ n₀ ≤ m :=
    Nat.findGreatest_spec (P := fun k => stretchLen γ k ≤ m) (Nat.zero_le m) (by simp [stretchLen])
  have hgt : m < stretchLen γ (n₀ + 1) := by
    by_cases hlt : n₀ < m
    · exact Nat.lt_of_not_ge (Nat.findGreatest_is_greatest
        (P := fun k => stretchLen γ k ≤ m) (Nat.lt_succ_self n₀) (by omega))
    · have heq : n₀ = m := by omega
      rw [heq]
      dsimp [stretchLen]
      omega
  have hle : stretchLen γ (n₀ + 1) ≤ m + γ + 1 :=
    (stretchLen_succ_le γ n₀).trans (by omega)
  exact ⟨hgt, hle⟩

private theorem seedLen_bound (γ m : ℕ) : m < (γ + 1) * seedLen γ m := by
  have hgt := (lt_stretchLen_seedLen γ m).1
  have hlog : Nat.log 2 (seedLen γ m) ≤ seedLen γ m := Nat.log_le_self 2 _
  dsimp [stretchLen] at hgt
  nlinarith

private theorem tendsto_seedLen (γ : ℕ) : Tendsto (seedLen γ) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro N
  refine ⟨(γ + 1) * N, fun m hm => ?_⟩
  have h := seedLen_bound γ m
  by_contra! hlt
  have : (γ + 1) * seedLen γ m ≤ (γ + 1) * N := Nat.mul_le_mul_left (γ + 1) hlt.le
  omega

/-! ### Truncated generator and threshold distinguisher for Theorem 5.2 -/

private def truncGen (G : List Bool → List Bool) (p : ℕ × List Bool) : List Bool :=
  (G p.2).take ((G p.2).length - p.1)

private theorem computableInPolyTime_truncGen {G : List Bool → List Bool}
    (hG : ComputableInPolyTime G encBits encBits) :
    ComputableInPolyTime (truncGen G) (encPair encUnary encBits) encBits := by
  unfold truncGen
  polytime

private def thresholdValue (γ d c n : ℕ) : ℕ :=
  let m := n + γ * Nat.log 2 n - c
  m - (2 * Nat.log 2 n + 3) - d * (Nat.log 2 m + 1)

private theorem computableInPolyTime_thresholdValue (γ d c : ℕ) :
    ComputableInPolyTime (thresholdValue γ d c) encUnary encUnary := by
  unfold thresholdValue
  have hlog : ComputableInPolyTime (Nat.log 2) encUnary encUnary :=
    .of_tidy (ComputableTidilyInPolyTime.unary_log_const 2)
  have hsub : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 - p.2)
      (encPair encUnary encUnary) encUnary :=
    ComputableInPolyTime.unary_sub
  have hid : ComputableInPolyTime (fun n : ℕ => n) encUnary encUnary := by fun_prop
  have hc (k : ℕ) : ComputableInPolyTime (fun _ : ℕ => k) encUnary encUnary := by fun_prop
  have hm := hsub.comp ((ComputableInPolyTime.unary_add.comp
    (hid.prod (ComputableInPolyTime.unary_mul.comp ((hc γ).prod hlog)))).prod (hc c))
  have hleft := hsub.comp (hm.prod (ComputableInPolyTime.unary_add.comp
    ((ComputableInPolyTime.unary_mul.comp ((hc 2).prod hlog)).prod (hc 3))))
  exact hsub.comp (hleft.prod (ComputableInPolyTime.unary_mul.comp
    ((hc d).prod (ComputableInPolyTime.unary_add.comp ((hlog.comp hm).prod (hc 1))))))

private theorem computableInPolyTime_mul_log_two_succ (d : ℕ) :
    ComputableInPolyTime (fun x : List Bool => d * (Nat.log 2 x.length + 1)) encBits encNat := by
  have hunary :
      ComputableInPolyTime (fun x : List Bool => d * (Nat.log 2 x.length + 1))
        encBits encUnary := by
    have hlog := ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_log_two
    fun_prop
  exact ComputableInPolyTime.unary_to_binary.comp hunary

private noncomputable def thresholdDistinguisher (γ d c : ℕ) (H : List Bool → ProbComp ℕ) :
    Distinguisher := fun n y =>
  (fun v => decide (thresholdValue γ d c n ≤ v)) <$>
    H (y.take (n + γ * Nat.log 2 n - c))

private theorem isPPT_thresholdDistinguisher (γ d c : ℕ) {H : List Bool → ProbComp ℕ}
    (hH : IsPPTOn encBits encNat H) :
    IsPPT encBool (thresholdDistinguisher γ d c H) := by
  change IsPPTOn (encPair encUnary encBits) encBool
    (fun p : ℕ × List Bool =>
      (fun v => decide (thresholdValue γ d c p.1 ≤ v)) <$>
        H (p.2.take (p.1 + γ * Nat.log 2 p.1 - c)))
  have hprep : ComputableInPolyTime
      (fun p : ℕ × List Bool => p.2.take (p.1 + γ * Nat.log 2 p.1 - c))
      (encPair encUnary encBits) encBits := by
    have hlog := ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_log_two
    fun_prop
  have hcmp : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × ℕ => decide (thresholdValue γ d c pair.1.1 ≤ pair.2))
      (encPair (encPair encUnary encBits) encNat) encBool := by
    have hthr : ComputableInPolyTime
        (fun pair : (ℕ × List Bool) × ℕ => thresholdValue γ d c pair.1.1)
        (encPair (encPair encUnary encBits) encNat) encUnary :=
      (computableInPolyTime_thresholdValue γ d c).comp
        ((ComputableInPolyTime.fst encUnary encBits).comp
          (ComputableInPolyTime.fst _ _))
    have hmin : ComputableInPolyTime
        (fun pair : (ℕ × List Bool) × ℕ => min (thresholdValue γ d c pair.1.1) pair.2)
        (encPair (encPair encUnary encBits) encNat) encUnary :=
      ComputableInPolyTime.binary_min_unary' hthr (ComputableInPolyTime.snd _ _)
    have heq :
        (fun pair : (ℕ × List Bool) × ℕ => decide (thresholdValue γ d c pair.1.1 ≤ pair.2)) =
        (fun pair : (ℕ × List Bool) × ℕ =>
          decide (thresholdValue γ d c pair.1.1 ≤ min (thresholdValue γ d c pair.1.1) pair.2)) := by
      funext pair
      simp
    rw [heq]
    exact ComputableInPolyTime.unary_le' hthr hmin
  exact (hH.preprocess hprep).map_with hcmp

/-! ### Theorem 5.2: Conditional EP-PRGs imply $K^t$ is mildly hard on average
(M2a polynomial-threshold form) -/

/-- **[Liu and Pass, Theorem 5.2, §5.2, p. 11 of arXiv:2009.11514v1][LiuPass2020] (M2a
polynomial-threshold one-sided helper):**
If $G$ is a $(1 / n^2, \gamma)$-condEP-PRG with entropy-loss constant $\alpha$ and stretch factor
$\gamma \ge 2 d + 3$, then there exists a polynomial $p_G$ (with $n + 1 \le p_G(n)$ for all $n$)
such that for every time bound $t : \mathbb{N} \to \mathbb{N}$ dominating $p_G$,
`Kolmogorov.timeBoundedNat t` is mildly hard on average to one-sidedly approximate within the
upper-rounded log window $d (\lfloor \log_2 n \rfloor + 1)$ (`d * (Nat.log 2 n + 1)`) against
uniform strict PPT heuristics. -/
theorem CondEPPRG.exists_mildlyHardOnAverageToOneSidedApprox_timeBoundedNat_log_succ
    {G : List Bool → List Bool} {γ α : ℕ} (d : ℕ) (hγ : 2 * d + 3 ≤ γ)
    (hG : CondEPPRG G (fun n => 1 / (n : ℝ) ^ 2) γ α) :
    ∃ pG : Polynomial ℕ, (∀ n, n + 1 ≤ pG.eval n) ∧
      ∀ {t : ℕ → ℕ}, (∀ n, pG.eval n ≤ t n) →
        MildlyHardOnAverageToOneSidedApprox
          (fun n => d * (Nat.log 2 n + 1)) (timeBoundedNat t) := by
  obtain ⟨hG_poly, hG_len, E, hE, hG_sec, hG_ent⟩ := hG
  obtain ⟨p₀, c_sim, hp₀_ge, hp₀_mono, hbound₀⟩ :=
    exists_timeBounded_of_computableInPolyTime (computableInPolyTime_truncGen hG_poly)
  let pG : Polynomial ℕ := p₀.comp (Polynomial.X + Polynomial.C (2 * γ + 3))
  have hpG_eval (m : ℕ) : pG.eval m = p₀.eval (m + (2 * γ + 3)) := by
    simp [pG]
  have hpG_ge (m : ℕ) : m + 1 ≤ pG.eval m := by
    rw [hpG_eval]
    have h := hp₀_ge (m + (2 * γ + 3))
    omega
  refine ⟨pG, hpG_ge, fun {t} ht => ?_⟩
  let q : Polynomial ℕ := Polynomial.C 16 * (Polynomial.X + 1) ^ (γ + α + 2)
  have hq_eval (m : ℕ) : q.eval m = 16 * (m + 1) ^ (γ + α + 2) := by
    simp [q]
  have hq_pos (m : ℕ) : 0 < q.eval m := by
    rw [hq_eval]
    positivity
  refine ⟨q, hq_pos, fun H hH => ?_⟩
  have hall_sec : ∀ᶠ n : ℕ in atTop, ∀ c : Fin (γ + 2),
      (Game.advantage
        ((((PMF.uniformOfFinset (E n) (hE n)).map List.ofFn).map G).bind
          fun y => ProbComp.eval (thresholdDistinguisher γ d c.val H n y))
        ((BitString.uniformList (n + γ * Nat.log 2 n)).bind
          fun y => ProbComp.eval (thresholdDistinguisher γ d c.val H n y)) : ℝ) ≤
        1 / (n : ℝ) ^ 2 :=
    Filter.eventually_all.mpr fun c => hG_sec (thresholdDistinguisher γ d c.val H)
      (isPPT_thresholdDistinguisher γ d c.val hH)
  set C₀ := 2 * γ + 3 + c_sim with hC₀_def
  have h_ev_n : ∀ᶠ n : ℕ in atTop, ∀ (c : Fin (γ + 2)) (m : ℕ),
      m = n + γ * Nat.log 2 n - c.val →
      (((BitString.uniformList m).bind fun x =>
        (ProbComp.eval (H x)).map fun v =>
          decide (timeBoundedNat t x - d * (Nat.log 2 m + 1) ≤ v ∧
            v ≤ timeBoundedNat t x)) true).toReal ≤
        1 - 1 / ((q.eval m : ℕ) : ℝ) := by
    filter_upwards [hall_sec, hG_ent,
      eventually_ge_atTop (4 * (γ + 1) + 4),
      Nat.eventually_le_log (γ + 2 * d + C₀ + 6) Nat.one_lt_two,
      Nat.eventually_add_mul_log_le (γ + 5) α Nat.one_lt_two] with
      n hn_sec hn_ent hn_4γ hlog_n_ge hlog_bound c m hm_def
    set m₀ := n + γ * Nat.log 2 n with hm₀_def
    have hc_le : c.val ≤ γ + 1 := Nat.le_of_lt_succ c.isLt
    have hγ_log_ge : γ + 1 ≤ γ * Nat.log 2 n := by nlinarith
    have hm_ge_n : n ≤ m := by omega
    have hm_le_m₀ : m ≤ m₀ := by omega
    have hm_pos : 1 ≤ m := by omega
    have hn_pos : 0 < n := by omega
    have hlog_m_le : Nat.log 2 m ≤ 2 * Nat.log 2 n + 1 := by
      have hlog_le : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
      have hm_le_sq : m ≤ n * n := by
        have hm₀_le : m₀ ≤ (γ + 1) * n := by nlinarith only [hm₀_def, hlog_le]
        have : (γ + 1) * n ≤ n * n := Nat.mul_le_mul_right n (by omega)
        omega
      have hn_lt_pow : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two n
      have hm_lt_pow : m < 2 ^ (2 * Nat.log 2 n + 2) := by
        calc
          m ≤ n * n := hm_le_sq
          _ < 2 ^ (Nat.log 2 n + 1) * 2 ^ (Nat.log 2 n + 1) :=
            Nat.mul_lt_mul'' hn_lt_pow hn_lt_pow
          _ = 2 ^ (2 * Nat.log 2 n + 2) := by
            rw [← pow_add]
            congr 1
            omega
      exact Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow (by omega) hm_lt_pow)
    set k := 2 * Nat.log 2 n + 3 with hk_def
    set g_err := d * (Nat.log 2 m + 1) with hg_err_def
    have hKt_low_arith : n + C₀ < m - k - g_err := by
      have hd_log : g_err ≤ 2 * d * Nat.log 2 n + 2 * d := by nlinarith only [hg_err_def, hlog_m_le]
      have hγ_split : 2 * d * Nat.log 2 n + 2 * Nat.log 2 n + Nat.log 2 n ≤ γ * Nat.log 2 n := by
        nlinarith only [hγ]
      omega
    -- Ideal distribution and Claim 1
    have hthr_eq : thresholdValue γ d c.val n = m - k - g_err := by
      dsimp [thresholdValue]
      rw [← hm_def, ← hk_def, ← hg_err_def]
    have hideal_eq :
        ((BitString.uniformList m₀).bind fun y =>
          ProbComp.eval (thresholdDistinguisher γ d c.val H n y)) =
        (BitString.uniformList m).bind fun y =>
          (ProbComp.eval (H y)).map fun v => decide (m - k - g_err ≤ v) := by
      simp only [thresholdDistinguisher, ProbComp.eval_map, ← hm₀_def, ← hm_def, hthr_eq]
      rw [← BitString.uniformList_take hm_le_m₀, PMF.bind_map]
      rfl
    have ht_ge_m : m + 1 ≤ t m := (hpG_ge m).trans (ht m)
    have hclaim1 := uniformList_threshold_accept_ge ht_ge_m k g_err (fun y => ProbComp.eval (H y))
    -- Real distribution and Claim 2
    let p_full : PMF (BitString m₀) :=
      (PMF.uniformOfFinset (E n) (hE n)).map fun x => BitString.ofList m₀ (G (List.ofFn x))
    let pG_dist : PMF (BitString m) :=
      p_full.map fun y => BitString.ofList m ((List.ofFn y).take m)
    have hpG_map :
        pG_dist.map List.ofFn =
          (((PMF.uniformOfFinset (E n) (hE n)).map List.ofFn).map G).map (List.take m) := by
      simp only [pG_dist, p_full, PMF.map_comp, Function.comp_def]
      congr 1
      funext x
      have hlen_Gx : (G (List.ofFn x)).length = m₀ := by
        simpa [hm₀_def] using hG_len (List.ofFn x)
      simp [BitString.ofFn_ofList, hlen_Gx, hm_le_m₀]
    have hreal_eq :
        ((((PMF.uniformOfFinset (E n) (hE n)).map List.ofFn).map G).bind fun y =>
          ProbComp.eval (thresholdDistinguisher γ d c.val H n y)) =
        (pG_dist.map List.ofFn).bind fun y =>
          (ProbComp.eval (H y)).map fun v => decide (m - k - g_err ≤ v) := by
      rw [hpG_map]
      simp only [PMF.bind_map, thresholdDistinguisher, ProbComp.eval_map, ← hm₀_def, ← hm_def,
        hthr_eq, Function.comp_def]
    set B : ℝ := (n : ℝ) - (α : ℝ) * (Nat.log 2 n : ℝ) - (c.val : ℝ) with hB_def
    have hB3 : 3 ≤ B := by
      have hlog_real : ((γ : ℝ) + 5) + (α : ℝ) * (Nat.log 2 n : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hlog_bound
      have hc_real : (c.val : ℝ) ≤ (γ : ℝ) + 1 := by exact_mod_cast hc_le
      linarith only [hB_def, hlog_real, hc_real]
    have hent_pG : B ≤ PMF.entropy pG_dist := by
      have hent_full : (n : ℝ) - (α : ℝ) * (Nat.log 2 n : ℝ) ≤ PMF.entropy p_full := hn_ent
      have htake := entropy_ofList_take_ge hm_le_m₀ p_full
      have hsub : ((m₀ - m : ℕ) : ℝ) = (c.val : ℝ) := by
        congr 1
        omega
      rw [hsub] at htake
      linarith only [hB_def, hent_full, htake]
    have hlow : ∀ y ∈ pG_dist.support, timeBoundedNat t (List.ofFn y) < m - k - g_err := by
      intro y hy
      have hy' : List.ofFn y ∈ (pG_dist.map List.ofFn).support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨y, hy, rfl⟩
      rw [hpG_map] at hy'
      obtain ⟨w, hw, hwy⟩ := (PMF.mem_support_map_iff _ _ _).mp hy'
      obtain ⟨z, hz, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hw
      obtain ⟨x, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
      have hlen_Gx : (G (List.ofFn x)).length = m₀ := by
        simpa [hm₀_def] using hG_len (List.ofFn x)
      have htrunc_eq : truncGen G (c.val, List.ofFn x) = List.ofFn y := by
        dsimp [truncGen]
        rw [hlen_Gx, ← hm_def, hwy]
      have hlen_enc : (encPair encUnary encBits (c.val, List.ofFn x)).length ≤ m + (2 * γ + 3) := by
        rw [length_encPair, encUnary_apply, List.length_replicate, encBits_apply, List.length_ofFn]
        omega
      have hstep : p₀.eval (encPair encUnary encBits (c.val, List.ofFn x)).length ≤
          t (truncGen G (c.val, List.ofFn x)).length := by
        rw [htrunc_eq, List.length_ofFn]
        refine (hp₀_mono hlen_enc).trans ?_
        dsimp only
        rw [← hpG_eval]
        exact ht m
      have hKt := hbound₀ (c.val, List.ofFn x) hstep
      rw [htrunc_eq] at hKt
      have hne : timeBounded t (List.ofFn y) ≠ ⊤ :=
        timeBounded_ne_top (by simpa [List.length_ofFn] using ht_ge_m)
      have hKt_nat : timeBoundedNat t (List.ofFn y) ≤
          (encPair encUnary encBits (c.val, List.ofFn x)).length + c_sim :=
        (timeBoundedNat_le_iff hne).mpr hKt
      have hlen_enc_n :
          (encPair encUnary encBits (c.val, List.ofFn x)).length + c_sim ≤ n + C₀ := by
        rw [length_encPair, encUnary_apply, List.length_replicate, encBits_apply, List.length_ofFn]
        omega
      exact (hKt_nat.trans hlen_enc_n).trans_lt hKt_low_arith
    have hclaim2 := generator_threshold_accept_le hm_pos hB3 hent_pG k g_err hlow
      (fun y => ProbComp.eval (H y))
    -- Security advantage bound from CondEPPRG
    have hadv := hn_sec c
    rw [Game.coe_advantage, Game.coe_succProbability, Game.coe_succProbability,
      hreal_eq, hideal_eq, abs_sub_comm] at hadv
    have hadv_diff :
        (((BitString.uniformList m).bind fun y =>
            (ProbComp.eval (H y)).map fun v => decide (m - k - g_err ≤ v)) true).toReal -
          (((pG_dist.map List.ofFn).bind fun y =>
            (ProbComp.eval (H y)).map fun v => decide (m - k - g_err ≤ v)) true).toReal ≤
          1 / (n : ℝ) ^ 2 :=
      (le_abs_self _).trans hadv
    -- Combine Claim 1, Claim 2, and hadv_diff
    set p_succ : ℝ :=
      (((BitString.uniformList m).bind fun x =>
        (ProbComp.eval (H x)).map fun v =>
          decide (timeBoundedNat t x - g_err ≤ v ∧ v ≤ timeBoundedNat t x)) true).toReal
    change p_succ ≤ 1 - 1 / ((q.eval m : ℕ) : ℝ)
    by_contra! h_contra
    have hfail_lt : 1 - p_succ < 1 / ((q.eval m : ℕ) : ℝ) := by linarith only [h_contra]
    -- Bound (2 : ℝ) ^ (-k) ≤ 1 / (2 * n ^ 2)
    have hk_pow : (2 : ℝ) ^ (-(k : ℝ)) ≤ 1 / (2 * (n : ℝ) ^ 2) := by
      have hn_lt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two n
      have hsq : 2 * n ^ 2 ≤ 2 ^ k := by
        rw [hk_def]
        calc
          2 * n ^ 2 = 2 * (n * n) := by ring
          _ ≤ 2 * (2 ^ (Nat.log 2 n + 1) * 2 ^ (Nat.log 2 n + 1)) :=
            Nat.mul_le_mul_left 2 (Nat.mul_le_mul hn_lt.le hn_lt.le)
          _ = 2 ^ (2 * Nat.log 2 n + 3) := by
            rw [← pow_add, ← pow_succ']
            congr 1
            omega
      have hsq_real : 2 * (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ k := by exact_mod_cast hsq
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast, one_div]
      exact inv_anti₀ (by positivity) hsq_real
    -- Bound (2 : ℝ) ^ ((m : ℝ) - (B - 3)) * (1 - p_succ)
    have hexp_eq : (m : ℝ) - (B - 3) = (((γ + α) * Nat.log 2 n + 3 : ℕ) : ℝ) := by
      have hm_real : (m : ℝ) = (n : ℝ) + (γ : ℝ) * (Nat.log 2 n : ℝ) - (c.val : ℝ) := by
        have : m + c.val = n + γ * Nat.log 2 n := by omega
        have h' : (m : ℝ) + (c.val : ℝ) = (n : ℝ) + (γ : ℝ) * (Nat.log 2 n : ℝ) := by
          exact_mod_cast this
        linarith only [h']
      rw [hB_def, hm_real]
      push_cast
      ring
    have hexp_bound : (2 : ℝ) ^ ((m : ℝ) - (B - 3)) ≤ 8 * ((m + 1 : ℕ) : ℝ) ^ (γ + α) := by
      rw [hexp_eq, Real.rpow_natCast]
      have hpow_nat : 2 ^ ((γ + α) * Nat.log 2 n + 3) ≤ 8 * (m + 1) ^ (γ + α) := by
        have hlog_pow : 2 ^ Nat.log 2 n ≤ m + 1 :=
          (Nat.pow_log_le_self 2 (by omega : n ≠ 0)).trans (by omega)
        calc
          2 ^ ((γ + α) * Nat.log 2 n + 3) = 8 * (2 ^ Nat.log 2 n) ^ (γ + α) := by
            rw [pow_add, mul_comm (γ + α), pow_mul, mul_comm]
            rfl
          _ ≤ 8 * (m + 1) ^ (γ + α) := Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hlog_pow _)
      exact_mod_cast hpow_nat
    have hfail_nonneg : 0 ≤ 1 - p_succ := by
      have hle : (((BitString.uniformList m).bind fun x =>
          (ProbComp.eval (H x)).map fun v =>
            decide (timeBoundedNat t x - g_err ≤ v ∧ v ≤ timeBoundedNat t x)) true) ≤ 1 :=
        PMF.coe_le_one _ _
      have h : p_succ ≤ 1 :=
        (ENNReal.toReal_mono ENNReal.one_ne_top hle).trans_eq ENNReal.toReal_one
      linarith only [h]
    have hprod_le :
        (2 : ℝ) ^ ((m : ℝ) - (B - 3)) * (1 - p_succ) ≤ 1 / (2 * ((m + 1 : ℕ) : ℝ) ^ 2) := by
      calc
        (2 : ℝ) ^ ((m : ℝ) - (B - 3)) * (1 - p_succ)
          ≤ (8 * ((m + 1 : ℕ) : ℝ) ^ (γ + α)) * (1 / ((q.eval m : ℕ) : ℝ)) :=
            mul_le_mul hexp_bound hfail_lt.le hfail_nonneg (by positivity)
        _ = 1 / (2 * ((m + 1 : ℕ) : ℝ) ^ 2) := by
            rw [hq_eval]
            push_cast
            have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
            rw [pow_add ((m : ℝ) + 1) (γ + α) 2]
            field_simp [hm1]
            ring
    have hfail_le_sq : 1 - p_succ ≤ 1 / (2 * ((m + 1 : ℕ) : ℝ) ^ 2) := by
      have h1 : (1 : ℝ) ≤ 8 * ((m + 1 : ℕ) : ℝ) ^ (γ + α) := by
        have : 1 ≤ 8 * (m + 1) ^ (γ + α) := Nat.one_le_iff_ne_zero.mpr (by positivity)
        exact_mod_cast this
      calc
        1 - p_succ = 1 * (1 - p_succ) := (one_mul _).symm
        _ ≤ (8 * ((m + 1 : ℕ) : ℝ) ^ (γ + α)) * (1 / ((q.eval m : ℕ) : ℝ)) :=
          mul_le_mul h1 hfail_lt.le hfail_nonneg (by positivity)
        _ = 1 / (2 * ((m + 1 : ℕ) : ℝ) ^ 2) := by
          rw [hq_eval]
          push_cast
          have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
          rw [pow_add ((m : ℝ) + 1) (γ + α) 2]
          field_simp [hm1]
          ring
    -- Now 1 / m ≤ 1 / (m + 1)^2 + 3 / (2 * n^2)
    have h_comb : 1 / (m : ℝ) ≤ 1 / ((m + 1 : ℕ) : ℝ) ^ 2 + 3 / (2 * (n : ℝ) ^ 2) := by
      have hdiv_add : 1 / (2 * (n : ℝ) ^ 2) + 1 / (n : ℝ) ^ 2 = 3 / (2 * (n : ℝ) ^ 2) := by ring
      have hdiv_m : 1 / (2 * ((m + 1 : ℕ) : ℝ) ^ 2) + 1 / (2 * ((m + 1 : ℕ) : ℝ) ^ 2) =
          1 / ((m + 1 : ℕ) : ℝ) ^ 2 := by ring
      linarith only [hclaim1, hclaim2, hadv_diff, hk_pow, hprod_le, hfail_le_sq, hdiv_add, hdiv_m]
    -- Contradiction since m ≥ 4 and 4 * m ≤ n ^ 2
    have hm_le_nsq : 4 * (m : ℝ) ≤ (n : ℝ) ^ 2 := by
      have hlog_le : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
      have hm₀_le : m ≤ (γ + 1) * n := by nlinarith only [hm_le_m₀, hm₀_def, hlog_le]
      have h4γ_n : 4 * (γ + 1) ≤ n := by omega
      have hm_le_nat : 4 * m ≤ n * n := by
        calc
          4 * m ≤ 4 * ((γ + 1) * n) := Nat.mul_le_mul_left 4 hm₀_le
          _ = (4 * (γ + 1)) * n := (mul_assoc _ _ _).symm
          _ ≤ n * n := Nat.mul_le_mul_right n h4γ_n
      have h' : (4 : ℝ) * (m : ℝ) ≤ (n : ℝ) * (n : ℝ) := by exact_mod_cast hm_le_nat
      linarith only [h', sq (n : ℝ)]
    have h1_lt : 1 / ((m + 1 : ℕ) : ℝ) ^ 2 < 1 / (2 * (m : ℝ)) := by
      apply one_div_lt_one_div_of_lt (by positivity)
      push_cast
      have hm4 : (4 : ℝ) ≤ (m : ℝ) := by
        have : 4 ≤ m := by omega
        exact_mod_cast this
      nlinarith only [hm4]
    have h2_le : 3 / (2 * (n : ℝ) ^ 2) ≤ 1 / (2 * (m : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [hm_le_nsq]
    have h_half : 1 / (2 * (m : ℝ)) + 1 / (2 * (m : ℝ)) = 1 / (m : ℝ) := by ring
    linarith only [h_comb, h1_lt, h2_le, h_half]
  filter_upwards [(tendsto_seedLen γ).eventually h_ev_n] with m hm
  have hseed := lt_stretchLen_seedLen γ m
  let c : Fin (γ + 2) := ⟨stretchLen γ (seedLen γ m) - m, by omega⟩
  have hm_eq : m = seedLen γ m + γ * Nat.log 2 (seedLen γ m) - c.val := by
    change m = stretchLen γ (seedLen γ m) - (stretchLen γ (seedLen γ m) - m)
    omega
  exact hm c m hm_eq

/-- One-sided $(d \lfloor \log_2 n \rfloor)$-approximation corollary of
`CondEPPRG.exists_mildlyHardOnAverageToOneSidedApprox_timeBoundedNat_log_succ`
($\gamma \ge 2 d + 3$). -/
theorem CondEPPRG.exists_mildlyHardOnAverageToOneSidedApprox_timeBoundedNat
    {G : List Bool → List Bool} {γ α : ℕ} (d : ℕ) (hγ : 2 * d + 3 ≤ γ)
    (hG : CondEPPRG G (fun n => 1 / (n : ℝ) ^ 2) γ α) :
    ∃ pG : Polynomial ℕ, (∀ n, n + 1 ≤ pG.eval n) ∧
      ∀ {t : ℕ → ℕ}, (∀ n, pG.eval n ≤ t n) →
        MildlyHardOnAverageToOneSidedApprox (fun n => d * Nat.log 2 n) (timeBoundedNat t) := by
  obtain ⟨pG, hpG, h⟩ :=
    hG.exists_mildlyHardOnAverageToOneSidedApprox_timeBoundedNat_log_succ d hγ
  exact ⟨pG, hpG, fun ht => (h ht).mono fun n => Nat.mul_le_mul_left d (Nat.le_succ _)⟩

/-- **[Liu and Pass, Theorem 5.2, §5.2, p. 11 of arXiv:2009.11514v1][LiuPass2020] (M2a
polynomial-threshold form, upper-rounded log window):**
If $G$ is a $(1 / n^2, \gamma)$-condEP-PRG with entropy-loss constant $\alpha$ and stretch factor
$\gamma \ge 4 d + 3$, then there exists a polynomial $p_G$ (with $n + 1 \le p_G(n)$ for all $n$)
such that for every time bound $t : \mathbb{N} \to \mathbb{N}$ dominating $p_G$,
`Kolmogorov.timeBoundedNat t` is mildly hard on average to symmetrically approximate within the
upper-rounded log window $d (\lfloor \log_2 n \rfloor + 1)$ (`d * (Nat.log 2 n + 1)`) against
uniform strict PPT heuristics. -/
theorem CondEPPRG.exists_mildlyHardOnAverageToApprox_timeBoundedNat_log_succ
    {G : List Bool → List Bool} {γ α : ℕ} (d : ℕ) (hγ : 4 * d + 3 ≤ γ)
    (hG : CondEPPRG G (fun n => 1 / (n : ℝ) ^ 2) γ α) :
    ∃ pG : Polynomial ℕ, (∀ n, n + 1 ≤ pG.eval n) ∧
      ∀ {t : ℕ → ℕ}, (∀ n, pG.eval n ≤ t n) →
        MildlyHardOnAverageToApprox
          (fun n => d * (Nat.log 2 n + 1)) (timeBoundedNat t) := by
  obtain ⟨pG, hpG, h⟩ :=
    hG.exists_mildlyHardOnAverageToOneSidedApprox_timeBoundedNat_log_succ (2 * d) (by omega)
  refine ⟨pG, hpG, fun {t} ht => ?_⟩
  have h2 : MildlyHardOnAverageToOneSidedApprox
      (fun n => 2 * (d * (Nat.log 2 n + 1))) (timeBoundedNat t) := by
    simpa only [mul_assoc] using h ht
  exact h2.mildlyHardOnAverageToApprox (computableInPolyTime_mul_log_two_succ d)

/-- **[Liu and Pass, Theorem 5.2, §5.2, p. 11 of arXiv:2009.11514v1][LiuPass2020] (M2a
polynomial-threshold form, ceiling log window `d * Nat.clog 2 n`):**
Symmetric $(d \lceil \log_2 n \rceil)$-approximation corollary of
`CondEPPRG.exists_mildlyHardOnAverageToApprox_timeBoundedNat_log_succ` ($\gamma \ge 4 d + 3$). -/
theorem CondEPPRG.exists_mildlyHardOnAverageToApprox_timeBoundedNat_clog
    {G : List Bool → List Bool} {γ α : ℕ} (d : ℕ) (hγ : 4 * d + 3 ≤ γ)
    (hG : CondEPPRG G (fun n => 1 / (n : ℝ) ^ 2) γ α) :
    ∃ pG : Polynomial ℕ, (∀ n, n + 1 ≤ pG.eval n) ∧
      ∀ {t : ℕ → ℕ}, (∀ n, pG.eval n ≤ t n) →
        MildlyHardOnAverageToApprox (fun n => d * Nat.clog 2 n) (timeBoundedNat t) := by
  obtain ⟨pG, hpG, h⟩ :=
    hG.exists_mildlyHardOnAverageToApprox_timeBoundedNat_log_succ d hγ
  exact ⟨pG, hpG, fun ht =>
    (h ht).mono fun n => Nat.mul_le_mul_left d (nat_clog_two_le_log_two_succ n)⟩

/-- **[Liu and Pass, Theorem 5.2, §5.2, p. 11 of arXiv:2009.11514v1][LiuPass2020] (M2a
polynomial-threshold form, floor log window `d * Nat.log 2 n`):**
Symmetric $(d \lfloor \log_2 n \rfloor)$-approximation corollary of
`CondEPPRG.exists_mildlyHardOnAverageToApprox_timeBoundedNat_log_succ` ($\gamma \ge 4 d + 3$). -/
theorem CondEPPRG.exists_mildlyHardOnAverageToApprox_timeBoundedNat
    {G : List Bool → List Bool} {γ α : ℕ} (d : ℕ) (hγ : 4 * d + 3 ≤ γ)
    (hG : CondEPPRG G (fun n => 1 / (n : ℝ) ^ 2) γ α) :
    ∃ pG : Polynomial ℕ, (∀ n, n + 1 ≤ pG.eval n) ∧
      ∀ {t : ℕ → ℕ}, (∀ n, pG.eval n ≤ t n) →
        MildlyHardOnAverageToApprox (fun n => d * Nat.log 2 n) (timeBoundedNat t) := by
  obtain ⟨pG, hpG, h⟩ :=
    hG.exists_mildlyHardOnAverageToApprox_timeBoundedNat_log_succ d hγ
  exact ⟨pG, hpG, fun ht => (h ht).mono fun n => Nat.mul_le_mul_left d (Nat.le_succ _)⟩

/-- Exact average-case PPT hardness specialization of Theorem 5.2 at $d = 0$ ($\gamma \ge 3$, M2a
polynomial-threshold form)
([Liu and Pass, Theorem 5.2, §5.2, p. 11 of arXiv:2009.11514v1][LiuPass2020]). -/
theorem CondEPPRG.exists_mildlyHardOnAverage_timeBoundedNat
    {G : List Bool → List Bool} {γ α : ℕ} (hγ : 3 ≤ γ)
    (hG : CondEPPRG G (fun n => 1 / (n : ℝ) ^ 2) γ α) :
    ∃ pG : Polynomial ℕ, (∀ n, n + 1 ≤ pG.eval n) ∧
      ∀ {t : ℕ → ℕ}, (∀ n, pG.eval n ≤ t n) →
        MildlyHardOnAverage (timeBoundedNat t) := by
  obtain ⟨pG, hpG, h⟩ :=
    hG.exists_mildlyHardOnAverageToOneSidedApprox_timeBoundedNat_log_succ 0 (by omega)
  exact ⟨pG, hpG, fun ht => (h ht).mildlyHardOnAverage⟩

/-- **Library corollary:** deterministic polynomial-time heuristic specialization of
`CondEPPRG.exists_mildlyHardOnAverageToApprox_timeBoundedNat` ($\gamma \ge 4 d + 3$). -/
theorem CondEPPRG.exists_mildlyHardOnAverageToApproxDet_timeBoundedNat
    {G : List Bool → List Bool} {γ α : ℕ} (d : ℕ) (hγ : 4 * d + 3 ≤ γ)
    (hG : CondEPPRG G (fun n => 1 / (n : ℝ) ^ 2) γ α) :
    ∃ pG : Polynomial ℕ, (∀ n, n + 1 ≤ pG.eval n) ∧
      ∀ {t : ℕ → ℕ}, (∀ n, pG.eval n ≤ t n) →
        MildlyHardOnAverageToApproxDet (fun n => d * Nat.log 2 n) (timeBoundedNat t) := by
  obtain ⟨pG, hpG, h⟩ := hG.exists_mildlyHardOnAverageToApprox_timeBoundedNat d hγ
  exact ⟨pG, hpG, fun ht => (h ht).mildlyHardOnAverageToApproxDet⟩

/-- **Library corollary:** deterministic polynomial-time heuristic specialization of
`CondEPPRG.exists_mildlyHardOnAverage_timeBoundedNat` ($\gamma \ge 3$). -/
theorem CondEPPRG.exists_mildlyHardOnAverageDet_timeBoundedNat
    {G : List Bool → List Bool} {γ α : ℕ} (hγ : 3 ≤ γ)
    (hG : CondEPPRG G (fun n => 1 / (n : ℝ) ^ 2) γ α) :
    ∃ pG : Polynomial ℕ, (∀ n, n + 1 ≤ pG.eval n) ∧
      ∀ {t : ℕ → ℕ}, (∀ n, pG.eval n ≤ t n) →
        MildlyHardOnAverageDet (timeBoundedNat t) := by
  obtain ⟨pG, hpG, h⟩ := hG.exists_mildlyHardOnAverage_timeBoundedNat hγ
  exact ⟨pG, hpG, fun ht => (h ht).mildlyHardOnAverageDet⟩

/-- **Library corollary:** `ℕ∞`-valued `Kolmogorov.timeBounded` version of
`CondEPPRG.exists_mildlyHardOnAverage_timeBoundedNat`. -/
theorem CondEPPRG.exists_mildlyHardOnAverageENat_timeBounded
    {G : List Bool → List Bool} {γ α : ℕ} (hγ : 3 ≤ γ)
    (hG : CondEPPRG G (fun n => 1 / (n : ℝ) ^ 2) γ α) :
    ∃ pG : Polynomial ℕ, (∀ n, n + 1 ≤ pG.eval n) ∧
      ∀ {t : ℕ → ℕ}, (∀ n, pG.eval n ≤ t n) →
        MildlyHardOnAverageENat (timeBounded t) := by
  obtain ⟨pG, hpG, h⟩ := hG.exists_mildlyHardOnAverage_timeBoundedNat hγ
  refine ⟨pG, hpG, fun {t} ht => ?_⟩
  rw [mildlyHardOnAverageENat_timeBounded_iff (fun n => (hpG n).trans (ht n))]
  exact h ht

/-! ### Theorem 3.1 (a) $\Rightarrow$ (c) and (a) $\Rightarrow$ (b): One-way functions imply
average-case hardness of $K^t$ (M2a polynomial-threshold form) -/

/-- **[Liu and Pass, Theorem 3.1 (a) $\Rightarrow$ (c), §3, p. 9 of
arXiv:2009.11514v1][LiuPass2020] (M2a polynomial-threshold form, upper-rounded log window):**
If $f$ is a one-way function, then for every approximation constant $d \in \mathbb{N}$ there exists
a polynomial $p \in \mathbb{N}[X]$ with $p(n) \ge n + 1$ such that for every time bound
$t : \mathbb{N} \to \mathbb{N}$ satisfying $t(n) \ge p(n)$ for all $n$, `timeBoundedNat t` is
mildly hard on average to symmetrically approximate within the upper-rounded integer log window
$d (\lfloor \log_2 n \rfloor + 1)$ (`d * (Nat.log 2 n + 1)`) against uniform strict PPT
heuristics. -/
theorem OneWay.exists_mildlyHardOnAverageToApprox_timeBoundedNat_log_succ
    {f : List Bool → List Bool} (hf : OneWay f) (d : ℕ) :
    ∃ p : Polynomial ℕ, (∀ n, n + 1 ≤ p.eval n) ∧
      ∀ {t : ℕ → ℕ}, (∀ n, p.eval n ≤ t n) →
        MildlyHardOnAverageToApprox
          (fun n => d * (Nat.log 2 n + 1)) (timeBoundedNat t) := by
  obtain ⟨G, α, hG⟩ := hf.exists_condEPPRG 2 (4 * d + 3)
  exact hG.exists_mildlyHardOnAverageToApprox_timeBoundedNat_log_succ d le_rfl

/-- **[Liu and Pass, Theorem 3.1 (a) $\Rightarrow$ (c), §3, p. 9 of
arXiv:2009.11514v1][LiuPass2020] (M2a polynomial-threshold form, ceiling log window):**
If $f$ is a one-way function, then for every $d \in \mathbb{N}$ there exists a polynomial
$p \in \mathbb{N}[X]$ with $p(n) \ge n + 1$ such that for every time bound $t(n) \ge p(n)$,
`timeBoundedNat t` is mildly hard on average to symmetrically approximate within
$d \lceil \log_2 n \rceil$ (`d * Nat.clog 2 n`) against uniform strict PPT heuristics. -/
theorem OneWay.exists_mildlyHardOnAverageToApprox_timeBoundedNat_clog
    {f : List Bool → List Bool} (hf : OneWay f) (d : ℕ) :
    ∃ p : Polynomial ℕ, (∀ n, n + 1 ≤ p.eval n) ∧
      ∀ {t : ℕ → ℕ}, (∀ n, p.eval n ≤ t n) →
        MildlyHardOnAverageToApprox (fun n => d * Nat.clog 2 n) (timeBoundedNat t) := by
  obtain ⟨p, hp, h⟩ := hf.exists_mildlyHardOnAverageToApprox_timeBoundedNat_log_succ d
  exact ⟨p, hp, fun ht =>
    (h ht).mono fun n => Nat.mul_le_mul_left d (nat_clog_two_le_log_two_succ n)⟩

/-- **[Liu and Pass, Theorem 3.1 (a) $\Rightarrow$ (c), §3, p. 9 of
arXiv:2009.11514v1][LiuPass2020] (M2a polynomial-threshold form, floor log window):**
If $f$ is a one-way function, then for every $d \in \mathbb{N}$ there exists a polynomial
$p \in \mathbb{N}[X]$ with $p(n) \ge n + 1$ such that for every time bound $t(n) \ge p(n)$,
`timeBoundedNat t` is mildly hard on average to symmetrically approximate within
$d \lfloor \log_2 n \rfloor$ (`d * Nat.log 2 n`) against uniform strict PPT heuristics. -/
theorem OneWay.exists_mildlyHardOnAverageToApprox_timeBoundedNat
    {f : List Bool → List Bool} (hf : OneWay f) (d : ℕ) :
    ∃ p : Polynomial ℕ, (∀ n, n + 1 ≤ p.eval n) ∧
      ∀ {t : ℕ → ℕ}, (∀ n, p.eval n ≤ t n) →
        MildlyHardOnAverageToApprox (fun n => d * Nat.log 2 n) (timeBoundedNat t) := by
  obtain ⟨p, hp, h⟩ := hf.exists_mildlyHardOnAverageToApprox_timeBoundedNat_log_succ d
  exact ⟨p, hp, fun ht => (h ht).mono fun n => Nat.mul_le_mul_left d (Nat.le_succ _)⟩

/-- **[Liu and Pass, Theorem 3.1 (a) $\Rightarrow$ (c), §3, p. 9 of
arXiv:2009.11514v1][LiuPass2020] (M2a polynomial-threshold form, real-valued $d \log_2 n$ window):**
If $f$ is a one-way function, then for every $d \in \mathbb{N}$ there exists a polynomial
$p \in \mathbb{N}[X]$ with $p(n) \ge n + 1$ such that for every time bound $t(n) \ge p(n)$,
there exists a positive polynomial $q$ such that for every uniform strict PPT heuristic
$\mathcal{H} : \{0, 1\}^* \to \mathrm{ProbComp}\ \mathbb{N}$ and all sufficiently large $n$,
$$\Pr_{x \leftarrow \{0, 1\}^n, v \leftarrow \mathcal{H}(x)}[|(v : \mathbb{R}) - K^t(x)| \le
  d \log_2 n] \le 1 - \frac{1}{q(n)}.$$ -/
theorem OneWay.exists_eventually_real_abs_sub_le_timeBoundedNat
    {f : List Bool → List Bool} (hf : OneWay f) (d : ℕ) :
    ∃ p : Polynomial ℕ, (∀ n, n + 1 ≤ p.eval n) ∧
      ∀ {t : ℕ → ℕ}, (∀ n, p.eval n ≤ t n) →
        ∃ q : Polynomial ℕ, (∀ n, 0 < q.eval n) ∧
          ∀ H : List Bool → ProbComp ℕ, IsPPTOn encBits encNat H →
            ∀ᶠ n in atTop,
              (((BitString.uniformList n).bind fun x =>
                (ProbComp.eval (H x)).map fun v : ℕ =>
                  decide (|(v : ℝ) - (timeBoundedNat t x : ℝ)| ≤
                    (d : ℝ) * Real.logb 2 (n : ℝ))) true).toReal ≤
                1 - 1 / ((q.eval n : ℕ) : ℝ) := by
  obtain ⟨p, hp, h⟩ := hf.exists_mildlyHardOnAverageToApprox_timeBoundedNat_log_succ d
  exact ⟨p, hp, fun ht => (h ht).eventually_real_abs_sub_le⟩

/-- **[Liu and Pass, Theorem 3.1 (a) $\Rightarrow$ (b), §3, p. 9 of
arXiv:2009.11514v1][LiuPass2020] (M2a polynomial-threshold form):**
If $f$ is a one-way function, then there exists a polynomial $p \in \mathbb{N}[X]$ with
$p(n) \ge n + 1$ such that for every time bound $t(n) \ge p(n)$, `timeBoundedNat t` is mildly hard
on average against uniform strict PPT heuristics. -/
theorem OneWay.exists_mildlyHardOnAverage_timeBoundedNat
    {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ p : Polynomial ℕ, (∀ n, n + 1 ≤ p.eval n) ∧
      ∀ {t : ℕ → ℕ}, (∀ n, p.eval n ≤ t n) →
        MildlyHardOnAverage (timeBoundedNat t) := by
  obtain ⟨G, α, hG⟩ := hf.exists_condEPPRG 2 3
  exact hG.exists_mildlyHardOnAverage_timeBoundedNat le_rfl

/-- **Library corollary:** deterministic polynomial-time heuristic specialization of
`OneWay.exists_mildlyHardOnAverageToApprox_timeBoundedNat`. -/
theorem OneWay.exists_mildlyHardOnAverageToApproxDet_timeBoundedNat
    {f : List Bool → List Bool} (hf : OneWay f) (d : ℕ) :
    ∃ p : Polynomial ℕ, (∀ n, n + 1 ≤ p.eval n) ∧
      ∀ {t : ℕ → ℕ}, (∀ n, p.eval n ≤ t n) →
        MildlyHardOnAverageToApproxDet (fun n => d * Nat.log 2 n) (timeBoundedNat t) := by
  obtain ⟨p, hp, h⟩ := hf.exists_mildlyHardOnAverageToApprox_timeBoundedNat d
  exact ⟨p, hp, fun ht => (h ht).mildlyHardOnAverageToApproxDet⟩

/-- **Library corollary:** deterministic polynomial-time heuristic specialization of
`OneWay.exists_mildlyHardOnAverage_timeBoundedNat`. -/
theorem OneWay.exists_mildlyHardOnAverageDet_timeBoundedNat
    {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ p : Polynomial ℕ, (∀ n, n + 1 ≤ p.eval n) ∧
      ∀ {t : ℕ → ℕ}, (∀ n, p.eval n ≤ t n) →
        MildlyHardOnAverageDet (timeBoundedNat t) := by
  obtain ⟨p, hp, h⟩ := hf.exists_mildlyHardOnAverage_timeBoundedNat
  exact ⟨p, hp, fun ht => (h ht).mildlyHardOnAverageDet⟩

/-- **Library corollary:** `ℕ∞`-valued `Kolmogorov.timeBounded` version of
`OneWay.exists_mildlyHardOnAverage_timeBoundedNat`. -/
theorem OneWay.exists_mildlyHardOnAverageENat_timeBounded
    {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ p : Polynomial ℕ, (∀ n, n + 1 ≤ p.eval n) ∧
      ∀ {t : ℕ → ℕ}, (∀ n, p.eval n ≤ t n) →
        MildlyHardOnAverageENat (timeBounded t) := by
  obtain ⟨G, α, hG⟩ := hf.exists_condEPPRG 2 3
  exact hG.exists_mildlyHardOnAverageENat_timeBounded le_rfl

/-- **[Liu and Pass, Theorem 3.1 (a) $\Rightarrow$ (c), §3, p. 9 of arXiv:2009.11514v1][LiuPass2020]
(existential M2a polynomial-threshold form, upper-rounded log window):**
If one-way functions exist, then for every $d \in \mathbb{N}$ there exists a polynomial
$p \in \mathbb{N}[X]$ with $p(n) \ge n + 1$ such that for every time bound $t(n) \ge p(n)$,
`timeBoundedNat t` is mildly hard on average to symmetrically approximate within
$d (\lfloor \log_2 n \rfloor + 1)$ (`d * (Nat.log 2 n + 1)`) against uniform strict PPT
heuristics. -/
theorem exists_mildlyHardOnAverageToApprox_log_succ_of_exists_oneWay
    (h : ∃ f : List Bool → List Bool, OneWay f) (d : ℕ) :
    ∃ p : Polynomial ℕ, (∀ n, n + 1 ≤ p.eval n) ∧
      ∀ {t : ℕ → ℕ}, (∀ n, p.eval n ≤ t n) →
        MildlyHardOnAverageToApprox
          (fun n => d * (Nat.log 2 n + 1)) (timeBoundedNat t) := by
  obtain ⟨f, hf⟩ := h
  exact hf.exists_mildlyHardOnAverageToApprox_timeBoundedNat_log_succ d

/-- **[Liu and Pass, Theorem 3.1 (a) $\Rightarrow$ (c), §3, p. 9 of arXiv:2009.11514v1][LiuPass2020]
(existential M2a polynomial-threshold form, ceiling log window):**
If one-way functions exist, then for every $d \in \mathbb{N}$ there exists a polynomial
$p \in \mathbb{N}[X]$ with $p(n) \ge n + 1$ such that for every time bound $t(n) \ge p(n)$,
`timeBoundedNat t` is mildly hard on average to symmetrically approximate within
$d \lceil \log_2 n \rceil$ (`d * Nat.clog 2 n`) against uniform strict PPT heuristics. -/
theorem exists_mildlyHardOnAverageToApprox_clog_of_exists_oneWay
    (h : ∃ f : List Bool → List Bool, OneWay f) (d : ℕ) :
    ∃ p : Polynomial ℕ, (∀ n, n + 1 ≤ p.eval n) ∧
      ∀ {t : ℕ → ℕ}, (∀ n, p.eval n ≤ t n) →
        MildlyHardOnAverageToApprox (fun n => d * Nat.clog 2 n) (timeBoundedNat t) := by
  obtain ⟨f, hf⟩ := h
  exact hf.exists_mildlyHardOnAverageToApprox_timeBoundedNat_clog d

/-- **[Liu and Pass, Theorem 3.1 (a) $\Rightarrow$ (c), §3, p. 9 of arXiv:2009.11514v1][LiuPass2020]
(existential M2a polynomial-threshold form, floor log window):**
If one-way functions exist, then for every $d \in \mathbb{N}$ there exists a polynomial
$p \in \mathbb{N}[X]$ with $p(n) \ge n + 1$ such that for every time bound $t(n) \ge p(n)$,
`timeBoundedNat t` is mildly hard on average to symmetrically approximate within
$d \lfloor \log_2 n \rfloor$ (`d * Nat.log 2 n`) against uniform strict PPT heuristics. -/
theorem exists_mildlyHardOnAverageToApprox_of_exists_oneWay
    (h : ∃ f : List Bool → List Bool, OneWay f) (d : ℕ) :
    ∃ p : Polynomial ℕ, (∀ n, n + 1 ≤ p.eval n) ∧
      ∀ {t : ℕ → ℕ}, (∀ n, p.eval n ≤ t n) →
        MildlyHardOnAverageToApprox (fun n => d * Nat.log 2 n) (timeBoundedNat t) := by
  obtain ⟨f, hf⟩ := h
  exact hf.exists_mildlyHardOnAverageToApprox_timeBoundedNat d

/-- **[Liu and Pass, Theorem 3.1 (a) $\Rightarrow$ (b), §3, p. 9 of arXiv:2009.11514v1][LiuPass2020]
(existential M2a polynomial-threshold form):**
If one-way functions exist, then there exists a polynomial $p \in \mathbb{N}[X]$ with
$p(n) \ge n + 1$ such that for every time bound $t(n) \ge p(n)$, `timeBoundedNat t` is mildly hard
on average against uniform strict PPT heuristics. -/
theorem exists_mildlyHardOnAverage_of_exists_oneWay
    (h : ∃ f : List Bool → List Bool, OneWay f) :
    ∃ p : Polynomial ℕ, (∀ n, n + 1 ≤ p.eval n) ∧
      ∀ {t : ℕ → ℕ}, (∀ n, p.eval n ≤ t n) →
        MildlyHardOnAverage (timeBoundedNat t) := by
  obtain ⟨f, hf⟩ := h
  exact hf.exists_mildlyHardOnAverage_timeBoundedNat

/-! ### Headline equivalences ([Liu and Pass, Theorem 3.1, §3, p. 9][LiuPass2020]) -/

/-- **[Liu and Pass, Theorem 3.1 (a) $\Leftrightarrow$ (b), §3, p. 9 of
arXiv:2009.11514v1][LiuPass2020]:**
One-way functions exist if and only if there exists a polynomial $p \in \mathbb{N}[X]$ with
$p(n) \ge n + 1$ for all $n$ (a sufficient clock hypothesis in the native model ensuring finite
$K^t$ via `timeBoundedNat_le_length_add`, where the source writes $t(n) > 0$) such that
`timeBoundedNat (fun n => p.eval n)` is mildly hard on average against uniform strict PPT
heuristics (`MildlyHardOnAverage`). -/
theorem exists_oneWay_iff_exists_mildlyHardOnAverage_timeBoundedNat :
    (∃ f : List Bool → List Bool, OneWay f) ↔
      (∃ p : Polynomial ℕ, (∀ n, n + 1 ≤ p.eval n) ∧
        MildlyHardOnAverage (timeBoundedNat fun n => p.eval n)) := by
  refine ⟨fun h => ?_, exists_oneWay_of_exists_mildlyHardOnAverage_timeBoundedNat⟩
  obtain ⟨p, hp, hhard⟩ := exists_mildlyHardOnAverage_of_exists_oneWay h
  exact ⟨p, hp, hhard fun _ => le_rfl⟩

/-- **`ℕ∞`-valued `Kolmogorov.timeBounded` corollary of Theorem 3.1 (a) $\Leftrightarrow$ (b):**
One-way functions exist if and only if there exists a polynomial $p \in \mathbb{N}[X]$ with
$p(n) \ge n + 1$ for all $n$ such that `timeBounded (fun n => p.eval n)` is mildly hard on
average against uniform strict PPT heuristics (`MildlyHardOnAverageENat`). -/
theorem exists_oneWay_iff_exists_mildlyHardOnAverageENat_timeBounded :
    (∃ f : List Bool → List Bool, OneWay f) ↔
      (∃ p : Polynomial ℕ, (∀ n, n + 1 ≤ p.eval n) ∧
        MildlyHardOnAverageENat (timeBounded fun n => p.eval n)) := by
  refine ⟨fun ⟨f, hf⟩ => ?_, exists_oneWay_of_exists_mildlyHardOnAverageENat_timeBounded⟩
  obtain ⟨p, hp, hhard⟩ := hf.exists_mildlyHardOnAverageENat_timeBounded
  exact ⟨p, hp, hhard fun _ => le_rfl⟩

/-- **[Liu and Pass, §3, p. 9 of arXiv:2009.11514v1][LiuPass2020]
(post-Theorem 3.1 threshold consequence, M2a polynomial-threshold form):**
One-way functions exist if and only if there exists a polynomial $p \in \mathbb{N}[X]$ with
$p(n) \ge n + 1$ for all $n$ such that for every time bound $t(n) \ge p(n)$, `timeBoundedNat t`
is mildly hard on average against uniform strict PPT heuristics (`MildlyHardOnAverage`). -/
theorem exists_oneWay_iff_exists_forall_mildlyHardOnAverage_timeBoundedNat :
    (∃ f : List Bool → List Bool, OneWay f) ↔
      (∃ p : Polynomial ℕ, (∀ n, n + 1 ≤ p.eval n) ∧
        ∀ {t : ℕ → ℕ}, (∀ n, p.eval n ≤ t n) →
          MildlyHardOnAverage (timeBoundedNat t)) := by
  refine ⟨exists_mildlyHardOnAverage_of_exists_oneWay, fun ⟨p, hp, hhard⟩ => ?_⟩
  exact exists_oneWay_of_exists_mildlyHardOnAverage_timeBoundedNat
    ⟨p, hp, hhard fun _ => le_rfl⟩

/-- **[Liu and Pass, Theorem 3.1 (a) $\Leftrightarrow$ (c), §3, p. 9 of
arXiv:2009.11514v1][LiuPass2020]
(M2a polynomial-threshold form, upper-rounded log window):**
One-way functions exist if and only if for every $d \in \mathbb{N}$ there exists a polynomial
$p \in \mathbb{N}[X]$ with $p(n) \ge n + 1$ for all $n$ such that for every time bound
$t(n) \ge p(n)$, `timeBoundedNat t` is mildly hard on average to symmetrically approximate within
$d (\lfloor \log_2 n \rfloor + 1)$ (`d * (Nat.log 2 n + 1)`) against uniform strict PPT heuristics
(`MildlyHardOnAverageToApprox`). -/
theorem exists_oneWay_iff_forall_exists_mildlyHardOnAverageToApprox_log_succ_timeBoundedNat :
    (∃ f : List Bool → List Bool, OneWay f) ↔
      (∀ d : ℕ, ∃ p : Polynomial ℕ, (∀ n, n + 1 ≤ p.eval n) ∧
        ∀ {t : ℕ → ℕ}, (∀ n, p.eval n ≤ t n) →
          MildlyHardOnAverageToApprox
            (fun n => d * (Nat.log 2 n + 1)) (timeBoundedNat t)) := by
  refine ⟨exists_mildlyHardOnAverageToApprox_log_succ_of_exists_oneWay, fun h => ?_⟩
  obtain ⟨p, hp, hhard⟩ := h 0
  exact exists_oneWay_of_exists_mildlyHardOnAverage_timeBoundedNat
    ⟨p, hp, (hhard fun _ => le_rfl).mildlyHardOnAverage⟩

/-- **[Liu and Pass, Theorem 3.1 (a) $\Leftrightarrow$ (c), §3, p. 9 of
arXiv:2009.11514v1][LiuPass2020]
(M2a polynomial-threshold form, ceiling log window):**
One-way functions exist if and only if for every $d \in \mathbb{N}$ there exists a polynomial
$p \in \mathbb{N}[X]$ with $p(n) \ge n + 1$ for all $n$ such that for every time bound
$t(n) \ge p(n)$, `timeBoundedNat t` is mildly hard on average to symmetrically approximate within
$d \lceil \log_2 n \rceil$ (`d * Nat.clog 2 n`) against uniform strict PPT heuristics
(`MildlyHardOnAverageToApprox`). -/
theorem exists_oneWay_iff_forall_exists_mildlyHardOnAverageToApprox_clog_timeBoundedNat :
    (∃ f : List Bool → List Bool, OneWay f) ↔
      (∀ d : ℕ, ∃ p : Polynomial ℕ, (∀ n, n + 1 ≤ p.eval n) ∧
        ∀ {t : ℕ → ℕ}, (∀ n, p.eval n ≤ t n) →
          MildlyHardOnAverageToApprox (fun n => d * Nat.clog 2 n) (timeBoundedNat t)) := by
  refine ⟨exists_mildlyHardOnAverageToApprox_clog_of_exists_oneWay, fun h => ?_⟩
  obtain ⟨p, hp, hhard⟩ := h 0
  exact exists_oneWay_of_exists_mildlyHardOnAverage_timeBoundedNat
    ⟨p, hp, (hhard fun _ => le_rfl).mildlyHardOnAverage⟩

/-- **[Liu and Pass, Theorem 3.1 (a) $\Leftrightarrow$ (c), §3, p. 9 of
arXiv:2009.11514v1][LiuPass2020]
(M2a polynomial-threshold form, floor log window):**
One-way functions exist if and only if for every $d \in \mathbb{N}$ there exists a polynomial
$p \in \mathbb{N}[X]$ with $p(n) \ge n + 1$ for all $n$ such that for every time bound
$t(n) \ge p(n)$, `timeBoundedNat t` is mildly hard on average to symmetrically approximate within
$d \lfloor \log_2 n \rfloor$ (`d * Nat.log 2 n`) against uniform strict PPT heuristics
(`MildlyHardOnAverageToApprox`). -/
theorem exists_oneWay_iff_forall_exists_mildlyHardOnAverageToApprox_timeBoundedNat :
    (∃ f : List Bool → List Bool, OneWay f) ↔
      (∀ d : ℕ, ∃ p : Polynomial ℕ, (∀ n, n + 1 ≤ p.eval n) ∧
        ∀ {t : ℕ → ℕ}, (∀ n, p.eval n ≤ t n) →
          MildlyHardOnAverageToApprox (fun n => d * Nat.log 2 n) (timeBoundedNat t)) := by
  refine ⟨exists_mildlyHardOnAverageToApprox_of_exists_oneWay, fun h => ?_⟩
  obtain ⟨p, hp, hhard⟩ := h 0
  exact exists_oneWay_of_exists_mildlyHardOnAverage_timeBoundedNat
    ⟨p, hp, (hhard fun _ => le_rfl).mildlyHardOnAverage⟩

end Cslib.Crypto
