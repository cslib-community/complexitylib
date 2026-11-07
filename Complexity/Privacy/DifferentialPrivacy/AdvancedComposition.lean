/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Privacy.DifferentialPrivacy.Composition
public import Complexity.Privacy.DifferentialPrivacy.PrivacyLoss

/-!
# Advanced composition

`k` adaptively chosen `(ε, δ)`-differentially private mechanisms are together
`(√(2k ln (1/δ')) ε + k ε (e^ε - 1), k δ + δ')`-private for every `δ' > 0`
(`DifferentiallyPrivate.advancedComposition`) [DworkRoth2014, Theorem 3.20]. For small `ε` the
privacy loss grows like `√k ε` instead of the `k ε` of basic composition
(`DifferentiallyPrivate.adaptiveComposition`).

The source proves the theorem through the KL divergence bound `ε (e^ε - 1)` and Azuma's
inequality. Here the proof bounds the moment generating function of the privacy loss in each
round (`lossMoment_le_exp`), multiplies the bounds along the transcript
(`lossMoment_transcriptWeight_le`) and applies Markov's inequality
(`tsum_indicator_le_lossMoment`). The per-round bound gives the known sharper term
`k ε tanh (ε / 2)` in place of `k ε (e^ε - 1)` (`DifferentiallyPrivate.advancedComposition_sqrt`).
For `δ > 0`, each round is replaced by `ε`-close sub-probability kernels that keep all but `δ` of
the mass (`exists_subKernel`); `k` rounds then lose at most `k δ` of the mass
(`one_le_tsum_transcriptWeight_add`).

The adaptive adversary of the source's composition experiment [DworkRoth2014, Definition 3.7],
which chooses in every round two adjacent inputs and a private mechanism from its coins and the
previous outputs, is covered by `DifferentiallyPrivate.advancedComposition_experiment`; the view
consists of the adversary's coins and all outputs, as in the source.

The source states the theorem for all `δ' ≥ 0`, reading `ln (1/0) = ∞`. Lean's `Real.log` has
`Real.log (1 / 0) = 0`, so the statements here assume `δ' > 0`.

## Main definitions

* `Cslib.Privacy.transcriptWeight`: the weight of a transcript under a sub-probability kernel.

## Main results

* `Cslib.Privacy.DifferentiallyPrivate.advancedComposition`: [DworkRoth2014, Theorem 3.20].
* `Cslib.Privacy.DifferentiallyPrivate.advancedComposition_sqrt`: the `tanh` refinement.
* `Cslib.Privacy.DifferentiallyPrivate.advancedComposition_tanh`: the form with a free slack
  parameter `a`, privacy `(k ε tanh (ε / 2) + a ε, exp (-a² / (2k)) + k δ)`.
* `Cslib.Privacy.DifferentiallyPrivate.advancedComposition_experiment`: the composition
  experiment against an adaptive, randomized adversary.
* `Cslib.Privacy.DifferentiallyPrivate.advancedComposition_of_target`: the per-round parameter
  of [DworkRoth2014, Corollary 3.21].
* `Cslib.Privacy.adaptiveComposition_toOuterMeasure_le`: the bound for one pair of inputs.

## References

* [DworkRoth2014]
-/

open scoped ENNReal

public section

namespace Cslib.Privacy

universe u v

section Transcript

variable {R : Type u}

/-- The weight of a transcript `l` (most recent output first) after `k` rounds of the kernel
`K`: the product of `K history r` over the rounds, and `0` unless `l` has length `k`. For a
probability kernel `K history = M history x` this is the mass function of
`adaptiveComposition M k x` (`adaptiveComposition_apply`). -/
noncomputable def transcriptWeight (K : List R → R → ℝ≥0∞) : ℕ → List R → ℝ≥0∞
  | 0, [] => 1
  | 0, _ :: _ => 0
  | _ + 1, [] => 0
  | k + 1, r :: h => transcriptWeight K k h * K h r

theorem transcriptWeight_ne_top {K : List R → R → ℝ≥0∞} (hK : ∀ h r, K h r ≠ ⊤) :
    ∀ k l, transcriptWeight K k l ≠ ⊤
  | 0, [] => ENNReal.one_ne_top
  | 0, _ :: _ => ENNReal.zero_ne_top
  | _ + 1, [] => ENNReal.zero_ne_top
  | k + 1, r :: h => ENNReal.mul_ne_top (transcriptWeight_ne_top hK k h) (hK h r)

private theorem tsum_list_eq_tsum_tsum_cons (f : List R → ℝ≥0∞) (hf : f [] = 0) :
    ∑' l, f l = ∑' h, ∑' r, f (r :: h) := by
  have hsupp : Function.support f ⊆ Set.range (fun p : R × List R => p.1 :: p.2) := by
    intro l hl
    cases l with
    | nil => exact absurd hf hl
    | cons r h => exact ⟨(r, h), rfl⟩
  rw [← (show Function.Injective (fun p : R × List R => p.1 :: p.2) from
    fun p q hpq => Prod.ext (List.cons.inj hpq).1 (List.cons.inj hpq).2).tsum_eq hsupp]
  refine (tsum_prod (f := fun r h => f (r :: h))).trans ?_
  rw [tsum_comm]

/-- The privacy-loss moment of `k + 1` rounds, conditioned on the first `k`. -/
theorem lossMoment_transcriptWeight_succ {K L : List R → R → ℝ≥0∞} (hL : ∀ h r, L h r ≠ ⊤)
    (t : ℝ) (ht : 0 ≤ t) (k : ℕ) :
    lossMoment t (transcriptWeight K (k + 1)) (transcriptWeight L (k + 1)) =
      ∑' h, transcriptWeight K k h * (transcriptWeight K k h / transcriptWeight L k h) ^ t *
        lossMoment t (K h) (L h) := by
  rw [lossMoment_def, tsum_list_eq_tsum_tsum_cons _ (by simp [transcriptWeight])]
  refine tsum_congr fun h => ?_
  rw [lossMoment_def, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun r => ?_
  simp only [transcriptWeight]
  rw [ENNReal.mul_div_mul_comm (Or.inr (hL h r)) (Or.inl (transcriptWeight_ne_top hL k h)),
    ENNReal.mul_rpow_of_nonneg _ _ ht]
  ring

/-- If every round has privacy-loss moment at most `B`, then `k` rounds have moment at most
`B ^ k`. -/
theorem lossMoment_transcriptWeight_le {K L : List R → R → ℝ≥0∞} (hL : ∀ h r, L h r ≠ ⊤)
    {t : ℝ} (ht : 0 ≤ t) {B : ℝ≥0∞} (hB : ∀ h, lossMoment t (K h) (L h) ≤ B) (k : ℕ) :
    lossMoment t (transcriptWeight K k) (transcriptWeight L k) ≤ B ^ k := by
  induction k with
  | zero =>
    rw [lossMoment_def, tsum_eq_single [] fun l hl => by cases l with
      | nil => exact absurd rfl hl
      | cons r h => simp [transcriptWeight]]
    simp [transcriptWeight]
  | succ k ih =>
    rw [lossMoment_transcriptWeight_succ hL t ht, pow_succ]
    calc ∑' h, transcriptWeight K k h * (transcriptWeight K k h / transcriptWeight L k h) ^ t *
          lossMoment t (K h) (L h)
        ≤ ∑' h, transcriptWeight K k h * (transcriptWeight K k h / transcriptWeight L k h) ^ t *
          B := tsum_le_tsum fun h => by gcongr; exact hB h
      _ = lossMoment t (transcriptWeight K k) (transcriptWeight L k) * B := by
          rw [ENNReal.tsum_mul_right, lossMoment_def]
      _ ≤ B ^ k * B := by gcongr

/-- The mass function of `k` rounds of adaptive composition is the transcript weight. -/
theorem adaptiveComposition_apply {D : Type v} (M : List R → D → PMF R) (k : ℕ) (x : D)
    (l : List R) :
    adaptiveComposition M k x l = transcriptWeight (fun h => M h x) k l := by
  induction k generalizing l with
  | zero =>
    rw [adaptiveComposition_zero]
    cases l with
    | nil => simp [transcriptWeight]
    | cons r h => simp [transcriptWeight]
  | succ k ih =>
    rw [adaptiveComposition_succ, PMF.bind_apply]
    cases l with
    | nil =>
      simp [transcriptWeight]
    | cons r h =>
      simp only [transcriptWeight]
      rw [tsum_eq_single h fun h' hh' => by
        rw [PMF.bind_apply]
        simp only [PMF.pure_apply, List.cons.injEq]
        simp [Ne.symm hh']]
      rw [PMF.bind_apply, tsum_eq_single r fun r' hr' => by
        simp [PMF.pure_apply, Ne.symm hr']]
      simp [ih]

/-- Transcript weights are monotone in the kernel. -/
theorem transcriptWeight_mono {K K' : List R → R → ℝ≥0∞} (hK : ∀ h r, K' h r ≤ K h r) :
    ∀ k l, transcriptWeight K' k l ≤ transcriptWeight K k l
  | 0, [] => le_rfl
  | 0, _ :: _ => le_rfl
  | _ + 1, [] => le_rfl
  | k + 1, r :: h => mul_le_mul' (transcriptWeight_mono hK k h) (hK h r)

/-- The empty transcript has weight one. -/
theorem tsum_transcriptWeight_zero (K : List R → R → ℝ≥0∞) :
    ∑' l, transcriptWeight K 0 l = 1 := by
  rw [tsum_eq_single [] fun l hl => by
    cases l with
    | nil => exact absurd rfl hl
    | cons r h => rfl]
  rfl

/-- The total weight after `k + 1` rounds. -/
theorem tsum_transcriptWeight_succ (K : List R → R → ℝ≥0∞) (k : ℕ) :
    ∑' l, transcriptWeight K (k + 1) l = ∑' h, transcriptWeight K k h * ∑' r, K h r := by
  rw [tsum_list_eq_tsum_tsum_cons _ rfl]
  refine tsum_congr fun h => ?_
  rw [← ENNReal.tsum_mul_left]
  rfl

/-- Sub-probability kernels give sub-probability transcript weights. -/
theorem tsum_transcriptWeight_le_one {K : List R → R → ℝ≥0∞} (hK : ∀ h, ∑' r, K h r ≤ 1) :
    ∀ k, ∑' l, transcriptWeight K k l ≤ 1
  | 0 => (tsum_transcriptWeight_zero K).le
  | k + 1 => by
    rw [tsum_transcriptWeight_succ]
    calc ∑' h, transcriptWeight K k h * ∑' r, K h r ≤ ∑' h, transcriptWeight K k h * 1 :=
          tsum_le_tsum fun h => mul_le_mul' le_rfl (hK h)
      _ ≤ 1 := by simpa only [mul_one] using tsum_transcriptWeight_le_one hK k

/-- Mass deficit: if every round of a sub-probability kernel keeps all but `δ` of the mass, then
`k` rounds keep all but `k δ`. -/
theorem one_le_tsum_transcriptWeight_add {K : List R → R → ℝ≥0∞} {δ : ℝ≥0∞}
    (hK : ∀ h, ∑' r, K h r ≤ 1) (hδ : ∀ h, 1 ≤ ∑' r, K h r + δ) :
    ∀ k : ℕ, 1 ≤ ∑' l, transcriptWeight K k l + k * δ
  | 0 => by rw [tsum_transcriptWeight_zero, Nat.cast_zero, zero_mul, add_zero]
  | k + 1 => by
    have ih := one_le_tsum_transcriptWeight_add hK hδ k
    calc (1 : ℝ≥0∞) ≤ ∑' l, transcriptWeight K k l + k * δ := ih
      _ = ∑' h, transcriptWeight K k h * 1 + k * δ := by simp only [mul_one]
      _ ≤ ∑' h, transcriptWeight K k h * (∑' r, K h r + δ) + k * δ := by
          gcongr with h
          exact hδ h
      _ = ∑' h, transcriptWeight K k h * ∑' r, K h r + (∑' h, transcriptWeight K k h) * δ +
            k * δ := by
          rw [← ENNReal.tsum_mul_right, ← tsum_add]
          simp only [mul_add]
      _ ≤ ∑' l, transcriptWeight K (k + 1) l + 1 * δ + k * δ := by
          rw [tsum_transcriptWeight_succ]
          gcongr
          exact tsum_transcriptWeight_le_one hK k
      _ = ∑' l, transcriptWeight K (k + 1) l + ((k + 1 : ℕ) : ℝ≥0∞) * δ := by
          push_cast
          ring

end Transcript

section Main

variable {R : Type u} {D : Type v}

/-- The core of advanced composition, for sub-probability kernels whose likelihood ratio lies in
`[e^{-ε}, e^ε]` in every round and whose first kernel has at most the mass of the second: for every
`a ≥ 0` and every event `S` of transcripts after `k` rounds,
`W_K(S) ≤ exp (k ε tanh (ε / 2) + a ε) · W_L(S) + exp (-a² / (2k))`. The moment bound of each round
(`lossMoment_le_exp` at `t = a / (k ε)`) multiplies along the transcript, and Markov's inequality
(`tsum_indicator_le_lossMoment`) converts the product into the event bound. -/
theorem tsum_indicator_transcriptWeight_le {K L : List R → R → ℝ≥0∞} {ε : ℝ} (hε : 0 ≤ ε)
    (hKL : ∀ h r, K h r ≤ ENNReal.ofReal (Real.exp ε) * L h r)
    (hLK : ∀ h r, L h r ≤ ENNReal.ofReal (Real.exp ε) * K h r)
    (hsum : ∀ h, ∑' r, K h r ≤ ∑' r, L h r) (hL1 : ∀ h, ∑' r, L h r ≤ 1)
    (k : ℕ) {a : ℝ} (ha : 0 ≤ a) (S : Set (List R)) :
    ∑' l, S.indicator (transcriptWeight K k) l ≤
      ENNReal.ofReal (Real.exp (k * ε * Real.tanh (ε / 2) + a * ε)) *
        ∑' l, S.indicator (transcriptWeight L k) l +
      ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * k)))) := by
  have hK1 : ∀ h, ∑' r, K h r ≤ 1 := fun h => (hsum h).trans (hL1 h)
  rcases hε.eq_or_lt with rfl | hε
  · have hKL' : K = L := funext fun h => funext fun r =>
      le_antisymm (by simpa using hKL h r) (by simpa using hLK h r)
    rw [hKL']
    simp only [mul_zero, zero_mul, add_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul]
    exact le_self_add
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Nat.cast_zero, mul_zero, div_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one]
    refine le_add_left ?_
    calc ∑' l, S.indicator (transcriptWeight K 0) l ≤ ∑' l, transcriptWeight K 0 l :=
          tsum_le_tsum fun l => Set.indicator_le_self _ _ l
      _ = 1 := tsum_transcriptWeight_zero K
  have hLfin : ∀ h r, L h r ≠ ⊤ := fun h r =>
    ne_top_of_le_ne_top ENNReal.one_ne_top ((le_tsum (L h) r).trans (hL1 h))
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have ht : 0 ≤ a / k / ε := div_nonneg (div_nonneg ha hk'.le) hε.le
  have hst : ε * (a / k / ε) = a / k := by field_simp
  have hround (h : List R) : lossMoment (a / k / ε) (K h) (L h) ≤
      ENNReal.ofReal (Real.exp (Real.tanh (ε / 2) * (a / k) + (a / k) ^ 2 / 2)) := by
    have := lossMoment_le_exp hε.le ht (hKL h) (hLK h) (hsum h)
      (ne_top_of_le_ne_top ENNReal.one_ne_top (hL1 h))
    rw [hst] at this
    exact this.trans ((mul_le_mul' le_rfl (hK1 h)).trans (mul_one _).le)
  have hmom := lossMoment_transcriptWeight_le hLfin ht hround k
  refine (tsum_indicator_le_lossMoment ht _ _ _ S).trans (add_le_add le_rfl ?_)
  refine (mul_le_mul' le_rfl hmom).trans ?_
  rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_nat_mul, ← Real.exp_add]
  refine ENNReal.ofReal_le_ofReal (le_of_eq (congrArg Real.exp ?_))
  field_simp
  ring

/-- Advanced composition for one pair of inputs. If, after every history, the round
distributions on `x` and on `y` have hockey-stick divergence at most `δ` at factor `e^ε` in both
directions, then for every `a ≥ 0` the transcripts of `k` rounds satisfy
`Pr_x[S] ≤ exp (k ε tanh (ε / 2) + a ε) · Pr_y[S] + exp (-a² / (2k)) + k δ`. -/
theorem adaptiveComposition_toOuterMeasure_le {M : List R → D → PMF R} {x y : D} {ε : ℝ}
    {δ : ℝ≥0∞} (hε : 0 ≤ ε)
    (hxy : ∀ h, ∑' r, (M h x r - ENNReal.ofReal (Real.exp ε) * M h y r) ≤ δ)
    (hyx : ∀ h, ∑' r, (M h y r - ENNReal.ofReal (Real.exp ε) * M h x r) ≤ δ)
    (k : ℕ) {a : ℝ} (ha : 0 ≤ a) (S : Set (List R)) :
    (adaptiveComposition M k x).toOuterMeasure S ≤
      ENNReal.ofReal (Real.exp (k * ε * Real.tanh (ε / 2) + a * ε)) *
        (adaptiveComposition M k y).toOuterMeasure S +
      (ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * k)))) + k * δ) := by
  have hc : 1 ≤ ENNReal.ofReal (Real.exp ε) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp hε)
  choose K L hKP hLQ hKL hLK hsum hmass using fun h => exists_subKernel (M h x) (M h y) hc
    (hxy h) (hyx h)
  have hL1 : ∀ h, ∑' r, L h r ≤ 1 := fun h =>
    (tsum_le_tsum (hLQ h)).trans (M h y).tsum_coe.le
  have hK1 : ∀ h, ∑' r, K h r ≤ 1 := fun h => (hsum h).trans (hL1 h)
  have hfun (z : D) : ⇑(adaptiveComposition M k z) = transcriptWeight (fun h => M h z) k :=
    funext (adaptiveComposition_apply M k z)
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, hfun x, hfun y]
  have hWK : ∀ l, transcriptWeight K k l ≤ transcriptWeight (fun h => M h x) k l :=
    transcriptWeight_mono hKP k
  have hWL : ∀ l, transcriptWeight L k l ≤ transcriptWeight (fun h => M h y) k l :=
    transcriptWeight_mono hLQ k
  have hone : ∑' l, transcriptWeight (fun h => M h x) k l = 1 := by
    rw [← hfun x]
    exact (adaptiveComposition M k x).tsum_coe
  -- the mass removed from the first experiment is at most `k δ`
  have hdef : ∑' l, (transcriptWeight (fun h => M h x) k l - transcriptWeight K k l) ≤ k * δ := by
    have h1 := one_le_tsum_transcriptWeight_add hK1 hmass k
    have h2 : ∑' l, (transcriptWeight (fun h => M h x) k l - transcriptWeight K k l) +
        ∑' l, transcriptWeight K k l = 1 := by
      rw [← tsum_add, ← hone]
      exact tsum_congr fun l => tsub_add_cancel_of_le (hWK l)
    have hfin : ∑' l, transcriptWeight K k l ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (tsum_transcriptWeight_le_one hK1 k)
    rw [← h2, add_comm (∑' l, transcriptWeight K k l) (k * δ)] at h1
    exact (ENNReal.add_le_add_iff_right hfin).mp h1
  calc ∑' l, S.indicator (transcriptWeight (fun h => M h x) k) l
      ≤ ∑' l, (S.indicator (transcriptWeight K k) l +
          (transcriptWeight (fun h => M h x) k l - transcriptWeight K k l)) := by
        refine tsum_le_tsum fun l => ?_
        by_cases hl : l ∈ S
        · simp only [Set.indicator_of_mem hl]
          exact le_add_tsub
        · simp only [Set.indicator_of_notMem hl, zero_add]
          exact zero_le
    _ = ∑' l, S.indicator (transcriptWeight K k) l +
          ∑' l, (transcriptWeight (fun h => M h x) k l - transcriptWeight K k l) := tsum_add
    _ ≤ (ENNReal.ofReal (Real.exp (k * ε * Real.tanh (ε / 2) + a * ε)) *
          ∑' l, S.indicator (transcriptWeight L k) l +
          ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * k))))) + k * δ :=
        add_le_add (tsum_indicator_transcriptWeight_le hε hKL hLK hsum hL1 k ha S) hdef
    _ ≤ ENNReal.ofReal (Real.exp (k * ε * Real.tanh (ε / 2) + a * ε)) *
          ∑' l, S.indicator (transcriptWeight (fun h => M h y) k) l +
          (ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * k)))) + k * δ) := by
        rw [add_assoc]
        gcongr with l
        exact hWL l

/-- Advanced composition with the slack parameter `a`: if every round is `(ε, δ)`-private for a
symmetric adjacency relation, `k` adaptive rounds are
`(k ε tanh (ε / 2) + a ε, exp (-a² / (2k)) + k δ)`-private. -/
theorem DifferentiallyPrivate.advancedComposition_tanh {Adj : D → D → Prop}
    (hAdj : ∀ ⦃x y⦄, Adj x y → Adj y x) {M : List R → D → PMF R} {ε : ℝ} {δ : ℝ≥0∞}
    (hε : 0 ≤ ε) (h : ∀ history, DifferentiallyPrivate Adj (M history) ε δ) (k : ℕ) {a : ℝ}
    (ha : 0 ≤ a) :
    DifferentiallyPrivate Adj (Privacy.adaptiveComposition M k)
      (k * ε * Real.tanh (ε / 2) + a * ε)
      (ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * k)))) + k * δ) :=
  fun _ _ hxy S => adaptiveComposition_toOuterMeasure_le hε
    (fun hist => DifferentiallyPrivate.iff_tsum_tsub_le.mp (h hist) hxy)
    (fun hist => DifferentiallyPrivate.iff_tsum_tsub_le.mp (h hist) (hAdj hxy)) k ha S

/-- Advanced composition with `tanh`: `k` adaptive rounds of `(ε, δ)`-private mechanisms are
`(√(2k ln (1/δ')) ε + k ε tanh (ε / 2), k δ + δ')`-private for every `δ' > 0`. Since
`tanh (ε / 2) ≤ e^ε - 1`, this sharpens [DworkRoth2014, Theorem 3.20]. -/
theorem DifferentiallyPrivate.advancedComposition_sqrt {Adj : D → D → Prop}
    (hAdj : ∀ ⦃x y⦄, Adj x y → Adj y x) {M : List R → D → PMF R} {ε : ℝ} {δ : ℝ≥0∞}
    (hε : 0 ≤ ε) (h : ∀ history, DifferentiallyPrivate Adj (M history) ε δ) (k : ℕ) {δ' : ℝ}
    (hδ' : 0 < δ') :
    DifferentiallyPrivate Adj (Privacy.adaptiveComposition M k)
      (Real.sqrt (2 * k * Real.log (1 / δ')) * ε + k * ε * Real.tanh (ε / 2))
      (k * δ + ENNReal.ofReal δ') := by
  rcases le_or_gt 1 δ' with hδ1 | hδ1
  · intro x y _ S
    refine (Probability.PMF.toOuterMeasure_le_one _ _).trans (le_add_left (le_add_left ?_))
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hδ1
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · intro x y _ S
    have h0 : Privacy.adaptiveComposition M 0 x = Privacy.adaptiveComposition M 0 y :=
      PMF.ext fun l => by
        rw [adaptiveComposition_zero, adaptiveComposition_zero]
    rw [h0]
    simp only [Nat.cast_zero, mul_zero, zero_mul, Real.sqrt_zero, add_zero, zero_add,
      Real.exp_zero, ENNReal.ofReal_one, one_mul]
    exact le_self_add
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hlog : 0 ≤ Real.log (1 / δ') := Real.log_nonneg (by rw [le_div_iff₀ hδ']; linarith)
  have := DifferentiallyPrivate.advancedComposition_tanh hAdj hε h k
    (Real.sqrt_nonneg (2 * k * Real.log (1 / δ')))
  rw [Real.sq_sqrt (by positivity)] at this
  have hδ : Real.exp (-(2 * k * Real.log (1 / δ') / (2 * k))) = δ' := by
    rw [show 2 * k * Real.log (1 / δ') / (2 * k) = Real.log (1 / δ') by field_simp,
      Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv]
  rw [hδ] at this
  exact this.mono (le_of_eq (by ring)) (le_of_eq (add_comm _ _))

/-- **Advanced composition** [DworkRoth2014, Theorem 3.20]: if every round is
`(ε, δ)`-private for a symmetric adjacency relation, then `k` adaptive rounds are
`(√(2k ln (1/δ')) ε + k ε (e^ε - 1), k δ + δ')`-private for every `δ' > 0`. -/
theorem DifferentiallyPrivate.advancedComposition {Adj : D → D → Prop}
    (hAdj : ∀ ⦃x y⦄, Adj x y → Adj y x) {M : List R → D → PMF R} {ε : ℝ} {δ : ℝ≥0∞}
    (hε : 0 ≤ ε) (h : ∀ history, DifferentiallyPrivate Adj (M history) ε δ) (k : ℕ) {δ' : ℝ}
    (hδ' : 0 < δ') :
    DifferentiallyPrivate Adj (Privacy.adaptiveComposition M k)
      (Real.sqrt (2 * k * Real.log (1 / δ')) * ε + k * ε * (Real.exp ε - 1))
      (k * δ + ENNReal.ofReal δ') := by
  refine (DifferentiallyPrivate.advancedComposition_sqrt hAdj hε h k hδ').mono ?_ le_rfl
  gcongr
  exact Real.tanh_div_two_le_exp_sub_one hε


/-- **Advanced composition against an adaptive adversary** [DworkRoth2014, Definition 3.7 and
Theorem 3.20]. In round `i` the adversary, knowing its coins `ω` and the outputs `history` of
the previous rounds, chooses two adjacent inputs `data ω history false`, `data ω history true`
and an `(ε, δ)`-private mechanism `mech ω history`; experiment `b` releases the output of that
mechanism on input `data ω history b`. The adversary's view, its coins and all `k` outputs, is
`(ε', k δ + δ')`-private as a function of `b` (adjacency `True` on `Bool`) with
`ε' = √(2k ln (1/δ')) ε + k ε (e^ε - 1)`. -/
theorem DifferentiallyPrivate.advancedComposition_experiment {D' : Type*} {Ω R : Type u}
    {Adj : D' → D' → Prop} (coins : PMF Ω) (data : Ω → List R → Bool → D')
    (mech : Ω → List R → D' → PMF R) {ε : ℝ} {δ : ℝ≥0∞} (hε : 0 ≤ ε)
    (hmech : ∀ ω history, DifferentiallyPrivate Adj (mech ω history) ε δ)
    (hdata : ∀ ω history, Adj (data ω history false) (data ω history true) ∧
      Adj (data ω history true) (data ω history false)) (k : ℕ) {δ' : ℝ} (hδ' : 0 < δ') :
    DifferentiallyPrivate (fun _ _ => True)
      (fun b : Bool => do
        let ω ← coins
        let view ← Privacy.adaptiveComposition
          (fun history b => mech ω history (data ω history b)) k b
        return (ω, view))
      (Real.sqrt (2 * k * Real.log (1 / δ')) * ε + k * ε * (Real.exp ε - 1))
      (k * δ + ENNReal.ofReal δ') := by
  have hε' : 0 ≤ Real.sqrt (2 * k * Real.log (1 / δ')) * ε + k * ε * (Real.exp ε - 1) :=
    add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hε)
      (mul_nonneg (mul_nonneg k.cast_nonneg hε) (by linarith [Real.one_le_exp hε]))
  have hcoins : DifferentiallyPrivate (fun _ _ => True) (fun _ : Bool => coins) 0 0 :=
    DifferentiallyPrivate.of_apply_le fun _ _ _ r => by simp
  have hview (ω : Ω) : DifferentiallyPrivate (fun _ _ => True)
      (Privacy.adaptiveComposition (fun history b => mech ω history (data ω history b)) k)
      (Real.sqrt (2 * k * Real.log (1 / δ')) * ε + k * ε * (Real.exp ε - 1))
      (k * δ + ENNReal.ofReal δ') := by
    have hne := DifferentiallyPrivate.advancedComposition (Adj := fun b b' : Bool => b ≠ b')
      (fun _ _ h => Ne.symm h)
      (M := fun history b => mech ω history (data ω history b)) hε
      (fun history => by
        intro b b' hbb' S
        cases b <;> cases b'
        · exact absurd rfl hbb'
        · exact hmech ω history (hdata ω history).1 S
        · exact hmech ω history (hdata ω history).2 S
        · exact absurd rfl hbb')
      k hδ'
    intro b b' _ S
    by_cases hbb' : b = b'
    · subst hbb'
      refine le_add_right (le_mul_of_one_le_left' ?_)
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (Real.one_le_exp hε')
    · exact hne hbb' S
  simpa only [zero_add] using DifferentiallyPrivate.bind_pair hcoins hview

/-- The per-round privacy parameter of [DworkRoth2014, Corollary 3.21]: if every round is
`(ε₀ / (2 √(2k ln (1/δ'))), δ)`-private, `k` adaptive rounds are `(ε₀, k δ + δ')`-private.
The source assumes `0 < ε₀ < 1`, and its proof uses `ε (e^ε - 1) ≤ ε²` (valid for small `ε`) and
needs `δ'` small compared with `ε₀`; here the hypothesis is `ε₀ ≤ 8 ln (1/δ')`, which holds
whenever `ε₀ ≤ 1` and `δ' ≤ e^{-1/8}`. -/
theorem DifferentiallyPrivate.advancedComposition_of_target {Adj : D → D → Prop}
    (hAdj : ∀ ⦃x y⦄, Adj x y → Adj y x) {M : List R → D → PMF R} {ε₀ : ℝ} {δ : ℝ≥0∞} (k : ℕ)
    {δ' : ℝ} (hε₀ : 0 ≤ ε₀) (hδ' : 0 < δ') (hε₀δ' : ε₀ ≤ 8 * Real.log (1 / δ'))
    (h : ∀ history, DifferentiallyPrivate Adj (M history)
      (ε₀ / (2 * Real.sqrt (2 * k * Real.log (1 / δ')))) δ) :
    DifferentiallyPrivate Adj (Privacy.adaptiveComposition M k) ε₀ (k * δ + ENNReal.ofReal δ') := by
  have hL : 0 ≤ Real.log (1 / δ') := by linarith
  have hsq : Real.sqrt (2 * k * Real.log (1 / δ')) ^ 2 = 2 * k * Real.log (1 / δ') :=
    Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ Real.sqrt (2 * k * Real.log (1 / δ')) := Real.sqrt_nonneg _
  have hε : 0 ≤ ε₀ / (2 * Real.sqrt (2 * k * Real.log (1 / δ'))) := by positivity
  have hcomp := DifferentiallyPrivate.advancedComposition_sqrt hAdj hε h k hδ'
  refine hcomp.mono ?_ le_rfl
  generalize Real.sqrt (2 * k * Real.log (1 / δ')) = s at hsq hs0 hε ⊢
  generalize hLdef : Real.log (1 / δ') = L at hsq hL hε₀δ'
  rcases hs0.eq_or_lt with rfl | hs
  · simp only [mul_zero, div_zero, zero_mul, add_zero, hε₀]
  have hk : (0 : ℝ) < k := by
    rcases (Nat.cast_nonneg (α := ℝ) k).eq_or_lt with h0 | h0
    · rw [← h0] at hsq; nlinarith
    · exact h0
  have hL0 : 0 < L := by
    rcases hL.eq_or_lt with h0 | h0
    · rw [← h0] at hsq; nlinarith
    · exact h0
  have he : 0 ≤ ε₀ / (2 * s) := by positivity
  have h1 : s * (ε₀ / (2 * s)) = ε₀ / 2 := by field_simp
  have h2 : k * (ε₀ / (2 * s)) * (ε₀ / (2 * s) / 2) = ε₀ ^ 2 / (16 * L) := by
    rw [show k * (ε₀ / (2 * s)) * (ε₀ / (2 * s) / 2) = k * ε₀ ^ 2 / (8 * s ^ 2) by ring, hsq]
    field_simp
    ring
  calc s * (ε₀ / (2 * s)) + k * (ε₀ / (2 * s)) * Real.tanh (ε₀ / (2 * s) / 2)
      ≤ s * (ε₀ / (2 * s)) + k * (ε₀ / (2 * s)) * (ε₀ / (2 * s) / 2) := by
        gcongr
        exact Real.tanh_le_self (by positivity)
    _ = ε₀ / 2 + ε₀ ^ 2 / (16 * L) := by rw [h1, h2]
    _ ≤ ε₀ := by
        rw [div_add_div _ _ two_ne_zero (by positivity), div_le_iff₀ (by positivity)]
        nlinarith

end Main

end Cslib.Privacy
