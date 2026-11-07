/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.FPAUS
public import Complexity.Computability.Complexity.Classes.FPAUS.SelfReducible
public import Complexity.Computability.Complexity.Classes.FPRAS
public import Complexity.Languages.Probabilistic.Iteration
public import Complexity.Languages.Probabilistic.Repeat
import Complexity.Languages.Probabilistic.Concentration
import Complexity.Probability.PMF.Event

/-!
# Almost uniform sampling gives approximate counting for self-reducible families

For a self-reducible witness family (`Cslib.Complexity.SelfReducible`), an almost uniform sampler
yields a randomized approximate counter [Jerrum, Valiant and Vazirani][JerrumValiantVazirani1986],
[Sinclair, Lecture 4, Section 4.2.1][Sinclair2025]. Writing `x₀ = x` and
`x_{k+1} = child x_k b_k`, the count telescopes:

`|W x| = |W x₀| / |W x₁| · |W x₁| / |W x₂| ⋯ |W x_{ℓ-1}| / |W x_ℓ| · |W x_ℓ|`, with `ℓ = len x`.

Each ratio `|W x_{k+1}| / |W x_k|` is the probability that a uniform witness of `x_k` begins with
`b_k`, which the sampler estimates. Choosing `b_k` to be the more frequent first bit keeps that
ratio at least `1 / 4`, so additive sampling error becomes relative error. The last factor
`|W x_ℓ|` is `1` or `0`, decided by the base-case test.

`Cslib.Complexity.SelfReducible.estimate R S x p t` runs this with explicit constants, for
relative error `1 / p` and failure probability `2 ^ (-t)`:

* tolerance `M = 16 (ℓ + 1) (p + 1)`; the sampler is called with accuracy `q = M`, so each call
  has total-variation error at most `2 ^ (-M) ≤ 1 / M`;
* at each level, `N = (t + ℓ + 2) M ^ 2` samples for each of the two first bits, counting `c₀`
  and `c₁` (`Cslib.ProbComp.countTrue_average_deviation_pow` makes each empirical frequency
  `1 / M`-accurate except with probability `2 ^ (-(t + ℓ + 1))`);
* descend to the child with the larger count `c`, multiplying the estimate by `N / c`;
* the per-level relative error `8 / M` compounds to at most `1 / p` over `ℓ` levels, and the
  `2 ℓ` failure events have total probability at most `ℓ 2 ^ (-(t + ℓ)) ≤ 2 ^ (-t)`
  (`Cslib.ProbComp.iterate_failure_toReal_le_mul`).

The lecture notes analyse the product of the level estimators by its variance; here each level
is bounded separately by a deviation bound for empirical frequencies and the failures are summed,
which gives the constants above directly.

An instance without witnesses has only descendants without witnesses, so its estimate is `0`
with probability one, matching the exactness forced by relative error
(`Cslib.Complexity.ApproxWithin.num_eq_zero`).

## Main definitions

* `Cslib.Complexity.SelfReducible.estimate`: the sampling-to-counting estimator.

## Main results

* `Cslib.Complexity.SelfReducible.approxWithin_estimate`: its accuracy, assuming only the
  sampler's total-variation guarantee.
* `Cslib.Complexity.SelfReducible.estimate_eq_zero`: zero counts are exact.

## References

* [M. R. Jerrum, L. G. Valiant, V. V. Vazirani, *Random generation of combinatorial structures from
  a uniform distribution*][JerrumValiantVazirani1986]
* [A. Sinclair, *CS294 Partition Functions*, Lecture 4, Section 4.2.1][Sinclair2025]
-/

@[expose] public section

namespace Cslib.Complexity.SelfReducible

open Cslib.Probability Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {W : α → Finset (List Bool)}

/-! ### The estimator -/

/-- The inverse tolerance `M = 16 (ℓ + 1) (p + 1)` for witness length `ℓ` and relative error
`1 / p`. -/
def tolerance (ℓ p : ℕ) : ℕ := 16 * (ℓ + 1) * (p + 1)

/-- The number of samples per first bit and level, `N = (t + ℓ + 2) M ^ 2`. -/
def sampleCount (ℓ p t : ℕ) : ℕ := (t + ℓ + 1 + 1) * tolerance ℓ p ^ 2

/-- Whether a sampler output is a word beginning with `b`. -/
def startsWith (b : Bool) (o : Option (List Bool)) : Bool :=
  match b with
  | false => !(o.getD []).headD true
  | true => (o.getD []).headD false

theorem startsWith_eq_true_iff (b : Bool) (o : Option (List Bool)) :
    startsWith b o = true ↔ ∃ w, o = some w ∧ w.head? = some b := by
  rcases o with _ | ⟨_ | ⟨c, w⟩⟩ <;> cases b <;> try cases c
  all_goals simp [startsWith]

/-- The estimator state: the current instance, and the numerator and denominator of the running
ratio. -/
abbrev State (α : Type) := α × ℕ × ℕ

/-- One deterministic update from the counts `c₀`, `c₁` of the two first bits among `N` samples:
descend to the child with the larger count `c`, and multiply the ratio by `N / c`. -/
def next (R : SelfReducible enc W) (N : ℕ) (s : State α) (c₀ c₁ : ℕ) : State α :=
  (R.child s.1 (decide (c₀ < c₁)), s.2.1 * N, s.2.2 * max (max c₀ c₁) 1)

/-- One level of the estimator: count the samples beginning with each bit, then update. The
sampler is called on the current instance with accuracy `q = M`. -/
noncomputable def step (R : SelfReducible enc W) (S : α → ℕ → ProbComp (Option (List Bool)))
    (ℓ p t : ℕ) (s : State α) : ProbComp (State α) := do
  let c₀ ← OracleComp.countTrue (sampleCount ℓ p t)
    (startsWith false <$> S s.1 (tolerance ℓ p))
  (R.next (sampleCount ℓ p t) s c₀) <$> OracleComp.countTrue (sampleCount ℓ p t)
    (startsWith true <$> S s.1 (tolerance ℓ p))

/-- **The sampling-to-counting estimator** with relative error `1 / p` and failure probability
`2 ^ (-t)`: run `len x` levels from `(x, 1, 1)`, then return the ratio `num / den`, with the
numerator replaced by `0` when the final instance has no witness. -/
noncomputable def estimate (R : SelfReducible enc W) (S : α → ℕ → ProbComp (Option (List Bool)))
    (x : α) (p t : ℕ) : ProbComp (ℕ × ℕ) :=
  (fun s : State α => (if [] ∈ W s.1 then s.2.1 else 0, s.2.2)) <$>
    OracleComp.iterate (R.len x) (R.step S (R.len x) p t) (x, 1, 1)

/-! ### One level -/

theorem preimage_startsWith (b : Bool) :
    startsWith b ⁻¹' {true} = some '' {w : List Bool | w.head? = some b} := by
  ext o
  simp only [Set.mem_preimage, Set.mem_singleton_iff, startsWith_eq_true_iff, Set.mem_image,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, rfl, hw⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, rfl, hw⟩

/-- An almost uniform sampler's frequency of outputs beginning with `b` is within its tolerance
of the fraction of witnesses beginning with `b`. -/
theorem abs_eval_startsWith_sub_le {μ : ProbComp (Option (List Bool))} {V : Finset (List Bool)}
    {ε : ℝ} (hμ : TVWithin (ProbComp.eval μ) (uniformWitness V) ε) (hV : V.Nonempty) (b : Bool) :
    |(ProbComp.eval (startsWith b <$> μ) true).toReal -
      ((V.filter (fun w => w.head? = some b)).card : ℝ) / V.card| ≤ ε := by
  have h := hμ (some '' {w : List Bool | w.head? = some b})
  rw [uniformWitness_toOuterMeasure_some hV] at h
  rw [ProbComp.eval_map, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
    preimage_startsWith]
  convert h using 4

/-- Choosing the more frequent bit: with true fractions `π + π' = 1` estimated within `γ ≤ 1/8`
by `d ≥ d'`, the chosen fraction is at least `1 / 4` and is estimated within relative error
`4 γ` in both directions. -/
private theorem choose_real {π π' d d' γ : ℝ} (hsum : π + π' = 1) (hd : |d - π| ≤ γ)
    (hd' : |d' - π'| ≤ γ) (hle : d' ≤ d) (hγ : γ ≤ 1 / 8) :
    1 / 4 ≤ π ∧ (1 - 4 * γ) * π ≤ d ∧ (1 - 4 * γ) * d ≤ π := by
  rw [abs_le] at hd hd'
  have hπ : 1 / 4 ≤ π := by linarith
  refine ⟨hπ, ?_, ?_⟩ <;> nlinarith

/-- One level in counts: `c` and `c'` successes among `N` samples estimate the sampler's
frequencies within `1 / M`, which are within `1 / M` of the witness fractions `a / A` and
`a' / A`. If `c' ≤ c` then `a > 0`, `c > 0`, and `N a / (c A)` is within relative error `8 / M`. -/
private theorem level {N M a a' A c c' : ℕ} {P P' : ℝ} (hN : 0 < N) (hM : 16 ≤ M)
    (hA : A = a + a') (hApos : 0 < A)
    (hP : |P - (a : ℝ) / A| ≤ 1 / M) (hP' : |P' - (a' : ℝ) / A| ≤ 1 / M)
    (hc : |(c : ℝ) / N - P| < 1 / M) (hc' : |(c' : ℝ) / N - P'| < 1 / M) (hle : c' ≤ c) :
    0 < a ∧ 0 < c ∧ (1 - 8 / (M : ℝ)) * N * a ≤ c * A ∧
      (1 - 8 / (M : ℝ)) * c * A ≤ N * a := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hApos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hMR : (16 : ℝ) ≤ M := by exact_mod_cast hM
  have hγ : 2 / (M : ℝ) ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hd : |(c : ℝ) / N - a / A| ≤ 2 / M := by
    calc |(c : ℝ) / N - a / A| ≤ |(c : ℝ) / N - P| + |P - a / A| := abs_sub_le _ _ _
      _ ≤ 2 / M := by rw [show (2 : ℝ) / M = 1 / M + 1 / M by ring]; linarith
  have hd' : |(c' : ℝ) / N - a' / A| ≤ 2 / M := by
    calc |(c' : ℝ) / N - a' / A| ≤ |(c' : ℝ) / N - P'| + |P' - a' / A| := abs_sub_le _ _ _
      _ ≤ 2 / M := by rw [show (2 : ℝ) / M = 1 / M + 1 / M by ring]; linarith
  have hsum : (a : ℝ) / A + a' / A = 1 := by
    rw [← add_div, div_eq_one_iff_eq hAR.ne', hA]
    push_cast
    ring
  have hle' : (c' : ℝ) / N ≤ c / N := by gcongr
  obtain ⟨hπ, h1, h2⟩ := choose_real hsum hd hd' hle' hγ
  have h8 : 4 * (2 / (M : ℝ)) = 8 / M := by ring
  rw [h8] at h1 h2
  have hθ : (0 : ℝ) ≤ 1 - 8 / M := by
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h, Nat.cast_zero, zero_div] at hπ
      norm_num at hπ
    · exact h
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h, Nat.cast_zero, zero_div] at h1
      have : (0 : ℝ) < a / A := by positivity
      have h8M : 8 / (M : ℝ) ≤ 1 / 2 := by linarith
      nlinarith
    · exact h
  refine ⟨ha, hcpos, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right h1 (le_of_lt (mul_pos hNR hAR))
    rw [show (1 - 8 / (M : ℝ)) * (a / A) * (N * A) = (1 - 8 / M) * N * a by
      field_simp] at this
    rw [show (c : ℝ) / N * (N * A) = c * A by field_simp] at this
    exact this
  · have := mul_le_mul_of_nonneg_right h2 (le_of_lt (mul_pos hNR hAR))
    rw [show (1 - 8 / (M : ℝ)) * (c / N) * (N * A) = (1 - 8 / M) * c * A by
      field_simp] at this
    rw [show (a : ℝ) / A * (N * A) = N * a by field_simp] at this
    exact this

/-! ### The invariant -/

variable (R : SelfReducible enc W)

/-- The invariant after `i` levels on an instance with witnesses: the current instance is `i`
levels down, the current count is positive, and `num * |W y| / den` is within factor
`(1 - θ) ^ i` of `|W x|` in both directions, with `θ = 8 / M`. -/
def Good (x : α) (p i : ℕ) (s : State α) : Prop :=
  R.len s.1 + i = R.len x ∧ 0 < s.2.2 ∧ 0 < (W s.1).card ∧
    (1 - 8 / (tolerance (R.len x) p : ℝ)) ^ i * s.2.2 * (W x).card ≤
      s.2.1 * (W s.1).card ∧
    (1 - 8 / (tolerance (R.len x) p : ℝ)) ^ i * (s.2.1 * (W s.1).card) ≤ s.2.2 * (W x).card

/-- The invariant survives one deterministic update when the chosen child's count `a` and the
sample count `c` satisfy the two relative bounds. -/
private theorem good_update {x : α} {p i : ℕ} {s : State α} (hs : R.Good x p i s)
    (hlen : 0 < R.len s.1) (b : Bool) {N c : ℕ} (hc : 0 < c) (ha : 0 < (W (R.child s.1 b)).card)
    (hlo : (1 - 8 / (tolerance (R.len x) p : ℝ)) * N * (W (R.child s.1 b)).card ≤
      c * (W s.1).card)
    (hhi : (1 - 8 / (tolerance (R.len x) p : ℝ)) * c * (W s.1).card ≤
      N * (W (R.child s.1 b)).card) :
    R.Good x p (i + 1) (R.child s.1 b, s.2.1 * N, s.2.2 * c) := by
  obtain ⟨hl, hden, hW, h4, h5⟩ := hs
  set θ := 8 / (tolerance (R.len x) p : ℝ)
  have hM : (16 : ℝ) ≤ tolerance (R.len x) p := by
    unfold tolerance
    push_cast
    nlinarith [(Nat.cast_nonneg (R.len x) : (0 : ℝ) ≤ _), (Nat.cast_nonneg p : (0 : ℝ) ≤ _)]
  have hθ : 0 ≤ 1 - θ := by
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  have hpow : 0 ≤ (1 - θ) ^ i := pow_nonneg hθ i
  refine ⟨?_, Nat.mul_pos hden hc, ha, ?_, ?_⟩
  · rw [R.len_child s.1 hlen b]
    omega
  · push_cast
    calc (1 - θ) ^ (i + 1) * (s.2.2 * c) * (W x).card
        = c * ((1 - θ) ^ i * s.2.2 * (W x).card) * (1 - θ) := by ring
      _ ≤ c * (s.2.1 * (W s.1).card) * (1 - θ) := by gcongr
      _ = s.2.1 * ((1 - θ) * c * (W s.1).card) := by ring
      _ ≤ s.2.1 * (N * (W (R.child s.1 b)).card) := by gcongr
      _ = s.2.1 * N * (W (R.child s.1 b)).card := by ring
  · push_cast
    calc (1 - θ) ^ (i + 1) * (s.2.1 * N * (W (R.child s.1 b)).card)
        = (1 - θ) ^ i * s.2.1 * ((1 - θ) * N * (W (R.child s.1 b)).card) := by ring
      _ ≤ (1 - θ) ^ i * s.2.1 * (c * (W s.1).card) := by gcongr
      _ = c * ((1 - θ) ^ i * (s.2.1 * (W s.1).card)) := by ring
      _ ≤ c * (s.2.2 * (W x).card) := by gcongr
      _ = s.2.2 * c * (W x).card := by ring

/-- One level preserves the invariant when both empirical frequencies are `1 / M`-accurate and
the sampler is `1 / M`-close to uniform at the current instance. -/
private theorem good_next {x : α} {p t i : ℕ} {s : State α} (hi : i < R.len x)
    (hs : R.Good x p i s) {μ : ProbComp (Option (List Bool))}
    (hμ : TVWithin (ProbComp.eval μ) (uniformWitness (W s.1))
      (1 / (tolerance (R.len x) p : ℝ)))
    {c₀ c₁ : ℕ}
    (h₀ : |(c₀ : ℝ) / (sampleCount (R.len x) p t : ℕ) -
      (ProbComp.eval (startsWith false <$> μ) true).toReal| < 1 / (tolerance (R.len x) p : ℝ))
    (h₁ : |(c₁ : ℝ) / (sampleCount (R.len x) p t : ℕ) -
      (ProbComp.eval (startsWith true <$> μ) true).toReal| < 1 / (tolerance (R.len x) p : ℝ)) :
    R.Good x p (i + 1) (R.next (sampleCount (R.len x) p t) s c₀ c₁) := by
  have hlen : 0 < R.len s.1 := by have := hs.1; omega
  have hW := hs.2.2.1
  have hM : 16 ≤ tolerance (R.len x) p := by unfold tolerance; nlinarith
  have hN : 0 < sampleCount (R.len x) p t := by unfold sampleCount; positivity
  have hsplit := R.card_eq_add hlen
  have hne : (W s.1).Nonempty := Finset.card_pos.1 hW
  have hP₀ := abs_eval_startsWith_sub_le hμ hne false
  have hP₁ := abs_eval_startsWith_sub_le hμ hne true
  rw [R.card_filter_head hlen] at hP₀ hP₁
  unfold next
  by_cases hlt : c₀ < c₁
  · obtain ⟨ha, hc, hlo, hhi⟩ := level hN hM (hsplit.trans (Nat.add_comm _ _)) hW hP₁ hP₀ h₁ h₀
      hlt.le
    have hmax : max (max c₀ c₁) 1 = c₁ := by omega
    simp only [hlt, decide_true, hmax]
    exact R.good_update hs hlen true hc ha hlo hhi
  · obtain ⟨ha, hc, hlo, hhi⟩ := level hN hM hsplit hW hP₀ hP₁ h₀ h₁ (not_lt.1 hlt)
    have hmax : max (max c₀ c₁) 1 = c₀ := by omega
    simp only [hlt, decide_false, hmax]
    exact R.good_update hs hlen false hc ha hlo hhi

/-- Every supported result of one level is an update by counts at most `N`. -/
theorem mem_support_step {S : α → ℕ → ProbComp (Option (List Bool))} {ℓ p t : ℕ}
    {s s' : State α} (h : s' ∈ (ProbComp.eval (R.step S ℓ p t s)).support) :
    ∃ c₀ c₁, c₀ ≤ sampleCount ℓ p t ∧ c₁ ≤ sampleCount ℓ p t ∧
      s' = R.next (sampleCount ℓ p t) s c₀ c₁ := by
  rw [step, ProbComp.eval_bind, PMF.mem_support_bind_iff] at h
  obtain ⟨c₀, hc₀, h⟩ := h
  rw [ProbComp.eval_map, PMF.mem_support_map_iff] at h
  obtain ⟨c₁, hc₁, rfl⟩ := h
  exact ⟨c₀, c₁, ProbComp.countTrue_le _ _ hc₀, ProbComp.countTrue_le _ _ hc₁, rfl⟩

/-- **One level fails with probability at most `2 · 2 ^ (-(t + ℓ + 1))`**, from the invariant and
a `1 / M`-close sampler at the current instance. -/
private theorem step_failure {S : α → ℕ → ProbComp (Option (List Bool))} {x : α} {p t i : ℕ}
    (hi : i < R.len x) {s : State α} (hs : R.Good x p i s)
    (hS : TVWithin (ProbComp.eval (S s.1 (tolerance (R.len x) p))) (uniformWitness (W s.1))
      (1 / (tolerance (R.len x) p : ℝ))) :
    ((ProbComp.eval (R.step S (R.len x) p t s)).toOuterMeasure
      {s' | ¬ R.Good x p (i + 1) s'}).toReal ≤ 2 * (1 / 2 : ℝ) ^ (t + R.len x + 1) := by
  set M := tolerance (R.len x) p with hM_def
  set N := sampleCount (R.len x) p t with hN_def
  have hMpos : 0 < M := by rw [hM_def]; unfold tolerance; positivity
  set μ := S s.1 M
  set bad : Bool → Set ℕ := fun b => {c | 1 / (M : ℝ) ≤
    |(c : ℝ) / (N : ℕ) - (ProbComp.eval (startsWith b <$> μ) true).toReal|}
  have hbad (b : Bool) :
      ((ProbComp.eval (OracleComp.countTrue N (startsWith b <$> μ))).toOuterMeasure
        (bad b)).toReal ≤ (1 / 2 : ℝ) ^ (t + R.len x + 1) :=
    ProbComp.countTrue_average_deviation_pow (t + R.len x + 1) M hMpos (startsWith b <$> μ)
  have hbadE (b : Bool) :
      (ProbComp.eval (OracleComp.countTrue N (startsWith b <$> μ))).toOuterMeasure
        (bad b) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (t + R.len x + 1)) :=
    (ENNReal.le_ofReal_iff_toReal_le (PMF.toOuterMeasure_ne_top _ _) (by positivity)).2 (hbad b)
  have hle : (ProbComp.eval (R.step S (R.len x) p t s)).toOuterMeasure
      {s' | ¬ R.Good x p (i + 1) s'} ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ (t + R.len x + 1)) +
          ENNReal.ofReal ((1 / 2 : ℝ) ^ (t + R.len x + 1)) := by
    rw [step, ProbComp.eval_bind]
    have h := PMF.toOuterMeasure_bind_failure_le
      (ProbComp.eval (OracleComp.countTrue N (startsWith false <$> μ)))
      (fun c₀ => ProbComp.eval ((R.next N s c₀) <$>
        OracleComp.countTrue N (startsWith true <$> μ)))
      (bad false)ᶜ {s' | ¬ R.Good x p (i + 1) s'}
      (ENNReal.ofReal ((1 / 2 : ℝ) ^ (t + R.len x + 1))) (fun c₀ _ hc₀ => by
        rw [ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
        refine le_trans (MeasureTheory.measure_mono ?_) (hbadE true)
        intro c₁ hc₁
        by_contra hc₁'
        apply hc₁
        refine R.good_next hi hs hS ?_ ?_
        · simpa [bad] using hc₀
        · simpa [bad] using hc₁')
    rw [compl_compl] at h
    exact h.trans (add_le_add (hbadE false) le_rfl)
  have hreal := ENNReal.toReal_mono (by finiteness) hle
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity)] at hreal
  linarith

/-- At the last level the invariant gives the accuracy guarantee. -/
private theorem approxWithin_of_good {x : α} {p : ℕ} (hp : 0 < p) {s : State α}
    (hs : R.Good x p (R.len x) s) :
    ApproxWithin (W x).card p (if [] ∈ W s.1 then s.2.1 else 0) s.2.2 := by
  obtain ⟨hl, hden, hW, h4, h5⟩ := hs
  have hlen : R.len s.1 = 0 := by omega
  have hsing := R.eq_singleton_nil hlen hW
  have hmem : [] ∈ W s.1 := by rw [hsing]; exact Finset.mem_singleton_self _
  have hcard : (W s.1).card = 1 := by rw [hsing]; rfl
  rw [ite_eq_left hmem]
  rw [hcard, Nat.cast_one, mul_one] at h4 h5
  refine ⟨hden, ?_⟩
  set ℓ := R.len x
  set C : ℝ := ((W x).card : ℝ)
  set K := (1 - 8 / (tolerance ℓ p : ℝ)) ^ ℓ with hK_def
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hdenR : (0 : ℝ) < s.2.2 := by exact_mod_cast hden
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hnum : (0 : ℝ) ≤ s.2.1 := Nat.cast_nonneg _
  have hθ : 8 / (tolerance ℓ p : ℝ) = 1 / (2 * (ℓ + 1) * (p + 1)) := by
    unfold tolerance
    push_cast
    field_simp
    ring
  have hθ0 : (0 : ℝ) ≤ 1 / (2 * (ℓ + 1) * (p + 1)) := by positivity
  have hθ1 : 1 / (2 * ((ℓ : ℝ) + 1) * (p + 1)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ _), hpR]
  have hK1 : K ≤ 1 := by
    rw [hK_def, hθ]
    exact pow_le_one₀ (by linarith) (by linarith)
  have hbern : 1 + (ℓ : ℝ) * (-(1 / (2 * (ℓ + 1) * (p + 1)))) ≤ K := by
    rw [hK_def, hθ, sub_eq_add_neg]
    exact one_add_mul_le_pow (by linarith) ℓ
  have hKp : (p : ℝ) ≤ K * (p + 1) := by
    have hℓ : (ℓ : ℝ) * (1 / (2 * (ℓ + 1) * (p + 1))) * (p + 1) ≤ 1 := by
      rw [show (ℓ : ℝ) * (1 / (2 * (ℓ + 1) * (p + 1))) * (p + 1) = ℓ / (2 * (ℓ + 1)) by
        field_simp]
      rw [div_le_one (by positivity)]
      linarith
    nlinarith
  have hK0 : 0 ≤ K := by nlinarith
  rw [abs_sub_le_iff]
  constructor
  · -- `num / den ≤ C + C / p`
    rw [div_sub' hdenR.ne', div_le_div_iff₀ hdenR hpR]
    nlinarith
  · -- `C - C / p ≤ num / den`
    rw [sub_div' hdenR.ne', div_le_div_iff₀ hdenR hpR]
    have h1K : 0 ≤ 1 - (1 - K) * p := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.2 h4) hpR.le, mul_nonneg (mul_nonneg hC hdenR.le) h1K]

/-! ### Accuracy -/

/-- `2 ^ (-M) ≤ 1 / M`. -/
private theorem half_pow_le_inv (M : ℕ) (hM : 0 < M) : (1 / 2 : ℝ) ^ M ≤ 1 / M := by
  rw [one_div_pow, one_div_le_one_div (by positivity) (by exact_mod_cast hM)]
  exact_mod_cast (Nat.lt_two_pow_self).le

/-- **Zero counts are exact**: on an instance without witnesses the estimate is `0` with
probability one, for every sampler. -/
theorem estimate_eq_zero (S : α → ℕ → ProbComp (Option (List Bool))) {x : α}
    (hx : (W x).card = 0) (p t : ℕ) :
    ∀ out ∈ (ProbComp.eval (R.estimate S x p t)).support, out.1 = 0 ∧ 0 < out.2 := by
  intro out hout
  rw [estimate, ProbComp.eval_map, PMF.mem_support_map_iff] at hout
  obtain ⟨s, hs, rfl⟩ := hout
  have hinv := ProbComp.iterate_invariant (R.len x) (R.step S (R.len x) p t) (x, 1, 1)
    (fun i s => R.len s.1 + i = R.len x ∧ (W s.1).card = 0 ∧ 0 < s.2.2)
    ⟨by simp, hx, Nat.one_pos⟩ (fun i hi s hs s' hs' => by
      obtain ⟨hl, hW, hden⟩ := hs
      obtain ⟨c₀, c₁, -, -, rfl⟩ := R.mem_support_step hs'
      have hlen : 0 < R.len s.1 := by omega
      refine ⟨?_, R.card_child_eq_zero hlen hW _, Nat.mul_pos hden (by omega)⟩
      simp only [next]
      rw [R.len_child s.1 hlen]
      omega) s hs
  obtain ⟨-, hW, hden⟩ := hinv
  have hnil : [] ∉ W s.1 := fun h => by
    rw [Finset.card_eq_zero] at hW
    simp [hW] at h
  exact ⟨by simp [hnil], hden⟩

/-- **Accuracy of the sampling-to-counting estimator**: if `S x q` is within total-variation
distance `2 ^ (-q)` of uniform on `W x` for every `x` and `q`, then for `p > 0` the estimate is
within relative error `1 / p` of `|W x|` with probability at least `1 - 2 ^ (-t)`. -/
theorem approxWithin_estimate {S : α → ℕ → ProbComp (Option (List Bool))}
    (hS : ∀ x q, TVWithin (ProbComp.eval (S x q)) (uniformWitness (W x)) ((1 / 2 : ℝ) ^ q))
    (x : α) {p : ℕ} (hp : 0 < p) (t : ℕ) :
    1 - (1 / 2 : ℝ) ^ t ≤ ((ProbComp.eval (R.estimate S x p t)).toOuterMeasure
      {out | ApproxWithin (W x).card p out.1 out.2}).toReal := by
  rcases Nat.eq_zero_or_pos (W x).card with hx | hx
  · have hone : (ProbComp.eval (R.estimate S x p t)).toOuterMeasure
        {out | ApproxWithin (W x).card p out.1 out.2} = 1 := by
      rw [PMF.toOuterMeasure_apply_eq_one_iff]
      intro out hout
      obtain ⟨h1, h2⟩ := R.estimate_eq_zero S hx p t out hout
      simp [ApproxWithin, hx, h1, h2]
    rw [hone, ENNReal.toReal_one]
    linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) t]
  set ℓ := R.len x
  set M := tolerance ℓ p
  have hMpos : 0 < M := by unfold M tolerance; positivity
  have hS' : ∀ y, TVWithin (ProbComp.eval (S y M)) (uniformWitness (W y)) (1 / (M : ℝ)) :=
    fun y => (hS y M).mono (half_pow_le_inv M hMpos)
  have hfail := ProbComp.iterate_failure_toReal_le_mul ℓ (R.step S ℓ p t) (x, 1, 1)
    (R.Good x p) ⟨by simp, Nat.one_pos, hx, by simp, by simp⟩ (by positivity)
    (fun i hi s hs => R.step_failure hi hs (hS' s.1))
  have hℓ : (ℓ : ℝ) * (2 * (1 / 2 : ℝ) ^ (t + ℓ + 1)) ≤ (1 / 2 : ℝ) ^ t := by
    have h2 : (ℓ : ℝ) ≤ 2 ^ ℓ := by exact_mod_cast (Nat.lt_two_pow_self).le
    have : (ℓ : ℝ) * (2 * (1 / 2 : ℝ) ^ (t + ℓ + 1)) = (1 / 2 : ℝ) ^ t * (ℓ * (1 / 2) ^ ℓ) := by
      rw [pow_add, pow_add]
      ring
    rw [this]
    calc (1 / 2 : ℝ) ^ t * (ℓ * (1 / 2) ^ ℓ) ≤ (1 / 2 : ℝ) ^ t * 1 := by
          gcongr
          rw [one_div_pow, mul_one_div, div_le_one (by positivity)]
          exact h2
      _ = (1 / 2 : ℝ) ^ t := mul_one _
  rw [estimate, ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
  set μ := ProbComp.eval (OracleComp.iterate ℓ (R.step S ℓ p t) (x, 1, 1))
  set good := (fun s : State α => (if [] ∈ W s.1 then s.2.1 else 0, s.2.2)) ⁻¹'
    {out | ApproxWithin (W x).card p out.1 out.2}
  have hsub : goodᶜ ⊆ {s | ¬ R.Good x p ℓ s} := fun s hs hgood =>
    hs (R.approxWithin_of_good hp hgood)
  have hbad : (μ.toOuterMeasure goodᶜ).toReal ≤ (1 / 2 : ℝ) ^ t :=
    (ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top _ _) (MeasureTheory.measure_mono hsub)).trans
      (hfail.trans hℓ)
  have hsum := Probability.PMF.toOuterMeasure_toReal_add_compl μ good
  linarith

end Cslib.Complexity.SelfReducible
