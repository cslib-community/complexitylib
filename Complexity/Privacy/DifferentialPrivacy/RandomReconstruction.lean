/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Privacy.DifferentialPrivacy.Reconstruction
public import Complexity.Foundations.Data.BitString.Sign
import Complexity.Foundations.Combinatorics.LittlewoodOfford
import Complexity.Probability.Chernoff

/-!
# Reconstruction from random `±1` queries

A database holds one secret sign per person, `d : ι → Bool`, read as `signVal (d i) ∈ {1, -1}`.
A `±1` query `v : ι → Bool` asks for `signDot v d = ∑ i, signVal (v i) * signVal (d i)`, the inner
product of the two sign vectors. Dwork and Roth's databases and queries live in `{-1, 1} ^ n`, and
`signVal` is the identification (`false ↦ 1`, `true ↦ -1`). For `m` queries `A : κ → ι → Bool`,
answers `y : κ → ℝ` are within `α` of the truth on at least a `1 / 2 + η` fraction of the queries
when `(1 / 2 + η) m ≤ #{j | |y j - signDot (A j) d| ≤ α}` (`AnswersWithin A y d α η`). The other
answers are arbitrary.

**Theorem ([DworkRoth2014, Theorem 8.2]).** Draw `m ≥ b n` uniformly random `±1` queries on `n`
rows. Except with probability at most `exp (-n (η b / 4 - ln 3))` over the queries, the following
holds for every database `d` and all answers within `α` on a `1 / 2 + η` fraction: the adversary
(`reconstructSigned`) recovers `d` in all but fewer than `((α + 1) / η) ^ 2` positions
(`toOuterMeasure_exists_le_hammingDist_reconstructSigned_le`). The adversary outputs any database
whose answers are also within `α` on a `1 / 2 + η` fraction; the true database is a candidate. The
good event depends only on the queries, so the guarantee holds against every curator, including
one that sees the queries before answering.

The proof follows Dwork and Roth. Two databases `c`, `d` that both fit the answers agree with them
on a common `2 η` fraction of the queries, where `|signDot v c - signDot v d| ≤ 2 α`. The difference
is `2 ∑ i, signVal (v i) z i` for the disagreement pattern `z : ι → SignType`. If `z` has at least
`k` nonzero entries, the Erdős–Littlewood–Offord bound
(`Combinatorics.LittlewoodOfford.card_filter_sum_bool_Ico_le_two_pow_div_sqrt`) bounds the chance
that a random query lands in this window by `(α + 1) / √(k + 1)`. That is at most `η` once
`k ≥ ((α + 1) / η) ^ 2`. Chernoff (`Probability.PMF.pi_sum_ge_one_add_mul_of_le_one`) bounds the
chance that a fixed such `z` survives `m` independent queries by `exp (-η m / 3)`. A union bound
over the `3 ^ n` patterns gives `3 ^ n exp (-η m / 3)` (`toOuterMeasure_reconstructionFails_le`).
That is at most Dwork and Roth's `exp (-n (η b / 4 - ln 3))`.

**The constant.** Dwork and Roth state `(2 α / η) ^ 2`.
* **For `α ≥ 1`** we have `α + 1 ≤ 2 α`, so `((α + 1) / η) ^ 2 ≤ (2 α / η) ^ 2`. Here the theorem
  above implies their statement.
* **For `α < 1`** their constant is false. At `α = 0` it would demand exact reconstruction.
  `exists_answersWithin_answersWithin_hammingDist_eq_two` shows that whatever the `m ≥ 10` queries
  on at least two rows, two databases at Hamming distance `2` can both answer a `1 / 2 + 1 / 5`
  fraction of them exactly with the same answers. The `+ 1` corrects the source's constant; it is
  not claimed as a new result. Dwork and Roth's application of their Lemma 8.3 drops the `+ 1` of
  its bound `(ℓ + 1) / √k`. A sum `∑ i, v_i z_i` over `k` nonzero terms has the parity of `k`,
  and the window `[-α, α]` holds at most `⌊α⌋ + 1` values of each parity. Even for `α < 1` it
  holds `0`, which such a sum hits with probability of order `1 / √k` when `k` is even.

**Differential privacy.** The consequence for differential privacy is a standard derivation,
following Dwork and Roth's remark that lower bounds for preventing blatant non-privacy apply to
every differentially private mechanism [DworkRoth2014, §8.1]. Fix queries `A` for which
reconstruction does not fail; they exist once `3 ln 3 · n < η m`
(`exists_not_reconstructionFails`). Let `M` be an `(ε, δ)`-private mechanism for Hamming adjacency
whose answers are within `α` on a `1 / 2 + η` fraction with probability at least `q` on every
database. Then `(1 + exp ε) (n - ((α + 1) / η) ^ 2) q ≤ n (exp ε + δ)`
(`DifferentiallyPrivate.mul_card_sub_mul_le_of_answersWithin`). With probability one this gives
`α + 1 ≥ η √(n (1 - δ) / (1 + exp ε))`
(`DifferentiallyPrivate.exists_forall_card_mul_one_sub_le_of_answersWithin`). So linearly many
`±1` queries cannot all be answered privately with error `o(√n)` on a `1 / 2 + η` fraction.

Scope: the adversary is not efficient, since it searches all `2 ^ n` databases. Dwork and Roth also
ignore efficiency here.

## Main definitions

* `Cslib.Privacy.signDot`: the answer to a `±1` query on a `±1` database.
* `Cslib.Privacy.AnswersWithin`: answers within `α` on at least a `1 / 2 + η` fraction of the
  queries.
* `Cslib.Privacy.ReconstructionFails`: two far-apart databases fit the same answers.
* `Cslib.Privacy.reconstructSigned`: the adversary of [DworkRoth2014, Theorem 8.2].

## Main results

* `Cslib.Privacy.toOuterMeasure_reconstructionFails_le`: random queries fail with probability at
  most `3 ^ n exp (-η m / 3)`.
* `Cslib.Privacy.hammingDist_reconstructSigned_lt`,
  `Cslib.Privacy.toOuterMeasure_exists_le_hammingDist_reconstructSigned_le`: reconstruction in all
  but `((α + 1) / η) ^ 2` positions [DworkRoth2014, Theorem 8.2].
* `Cslib.Privacy.exists_not_reconstructionFails`: good queries exist once `3 ln 3 · n < η m`.
* `Cslib.Privacy.DifferentiallyPrivate.mul_card_sub_mul_le_of_answersWithin`,
  `Cslib.Privacy.DifferentiallyPrivate.exists_forall_card_mul_one_sub_le_of_answersWithin`: private
  answers to linearly many `±1` queries have error `Ω(√n)`.
* `Cslib.Privacy.exists_answersWithin_answersWithin_hammingDist_eq_two`: the source's constant
  `(2 α / η) ^ 2` fails at `α = 0`.

## References

* [DworkRoth2014]
-/

open scoped ENNReal

public section

namespace Cslib.Privacy

open Finset BitString

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The answer to the `±1` query `v` on the database `d`, both read as sign vectors through
`signVal`: `∑ i, v_i d_i` [DworkRoth2014, §8.1]. -/
noncomputable def signDot (v d : ι → Bool) : ℝ :=
  ∑ i, signVal (v i) * signVal (d i)

/-- Unfolding `signDot`. -/
theorem signDot_apply (v d : ι → Bool) : signDot v d = ∑ i, signVal (v i) * signVal (d i) := by
  rw [signDot]

/-- The answers `y` to the `±1` queries `A` are within `α` of the true answers on `d` for at least
a `1 / 2 + η` fraction of the queries. The other answers are arbitrary. -/
def AnswersWithin (A : κ → ι → Bool) (y : κ → ℝ) (d : ι → Bool) (α η : ℝ) : Prop :=
  (1 / 2 + η) * Fintype.card κ ≤ #{j | |y j - signDot (A j) d| ≤ α}

/-- Unfolding `AnswersWithin`. -/
theorem answersWithin_iff {A : κ → ι → Bool} {y : κ → ℝ} {d : ι → Bool} {α η : ℝ} :
    AnswersWithin A y d α η ↔ (1 / 2 + η) * Fintype.card κ ≤ #{j | |y j - signDot (A j) d| ≤ α} :=
  Iff.rfl

/-- Exact answers are within any `α ≥ 0` on every query, so on a `1 / 2 + η` fraction whenever
`η ≤ 1 / 2`. -/
theorem answersWithin_signDot (A : κ → ι → Bool) (d : ι → Bool) {α η : ℝ} (hα : 0 ≤ α)
    (hη : η ≤ 1 / 2) : AnswersWithin A (fun j => signDot (A j) d) d α η := by
  rw [answersWithin_iff]
  simp only [sub_self, abs_zero, hα, filter_true, card_univ]
  have : (0 : ℝ) ≤ Fintype.card κ := Nat.cast_nonneg _
  nlinarith

/-! ### Anti-concentration and the bad event for one pattern -/

/-- The pattern of disagreement of `c` with `d`: `0` where they agree and the sign of `c`
elsewhere. -/
private noncomputable def diffPattern (c d : ι → Bool) : ι → SignType :=
  fun i => if c i = d i then 0 else if c i then -1 else 1

private theorem signDot_sub_signDot (v c d : ι → Bool) :
    signDot v c - signDot v d = 2 * ∑ i, signVal (v i) * (diffPattern c d i : ℝ) := by
  unfold signDot diffPattern
  rw [← sum_sub_distrib, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  cases c i <;> cases d i <;>
    simp only [signVal_true, signVal_false, ite_true, ite_false, Bool.false_eq_true,
      Bool.true_eq_false, SignType.coe_zero, SignType.coe_one, SignType.coe_neg, mul_zero,
      mul_one, mul_neg] <;> ring

private theorem card_ne_zero_diffPattern (c d : ι → Bool) :
    #{i | diffPattern c d i ≠ 0} = hammingDist c d := by
  unfold hammingDist diffPattern
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and]
  cases c i <;> cases d i <;> simp

/-- **Anti-concentration** (Erdős–Littlewood–Offord): for a pattern `z` with `k` nonzero
entries, at most a `(α + 1) / √(k + 1)` fraction of the queries `v` have
`|∑ i, v_i z_i| ≤ α`. The window `[-α, α]` is covered by `⌊α⌋ + 1` unit windows. -/
private theorem card_abs_sum_le [DecidableEq ι] (z : ι → SignType) {α : ℝ} (hα : 0 ≤ α) :
    (#{v : ι → Bool | |∑ i, signVal (v i) * (z i : ℝ)| ≤ α} : ℝ) ≤
      (α + 1) * 2 ^ Fintype.card ι / Real.sqrt (#{i | z i ≠ 0} + 1) := by
  classical
  set a : ι → ℝ := fun i => (z i : ℝ)
  set g : (ι → Bool) → ℝ := fun v => ∑ i, a i * (v i).toNat
  set Z := ∑ i, a i
  set N := ⌊α⌋₊ + 1
  set L := (Z - α) / 2
  have hN : α < N := by
    simp only [N, Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one α
  have hN' : (N : ℝ) ≤ α + 1 := by
    simp only [N, Nat.cast_add, Nat.cast_one]
    linarith [Nat.floor_le hα]
  have hsum : ∀ v : ι → Bool, ∑ i, signVal (v i) * a i = Z - 2 * g v := by
    intro v
    simp only [Z, g, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    cases v i
    · simp only [signVal_false, one_mul, Bool.toNat_false, Nat.cast_zero, mul_zero, sub_zero]
    · simp only [signVal_true, Bool.toNat_true, Nat.cast_one, mul_one]
      ring
  have hsub : (#{v : ι → Bool | |∑ i, signVal (v i) * (z i : ℝ)| ≤ α} : ℝ) ≤
      #{v : ι → Bool | (L + N) - (∑ _j ∈ range N, (1 : ℝ)) ≤ g v ∧ g v < L + N} := by
    have : ({v : ι → Bool | |∑ i, signVal (v i) * (z i : ℝ)| ≤ α} : Finset (ι → Bool)) ⊆
        ({v : ι → Bool | (L + N) - (∑ _j ∈ range N, (1 : ℝ)) ≤ g v ∧ g v < L + N} :
          Finset (ι → Bool)) := by
      intro v hv
      simp only [mem_filter, mem_univ, true_and] at hv ⊢
      have h := hsum v
      simp only [a] at h
      rw [h, abs_le] at hv
      rw [sum_const, card_range, nsmul_eq_mul, mul_one]
      constructor
      · simp only [L]
        linarith [hv.1, hv.2]
      · simp only [L]
        linarith [hv.1, hv.2]
    exact_mod_cast card_le_card this
  have hcover := Combinatorics.LittlewoodOfford.card_filter_Ico_sum_le g (range N) (fun _ => 1)
    (fun _ => 2 ^ Fintype.card ι / Real.sqrt (#{i | z i ≠ 0} + 1))
    (fun _ _ c => Combinatorics.LittlewoodOfford.card_filter_sum_bool_Ico_le_two_pow_div_sqrt a
      {i | z i ≠ 0} c fun i hi => by
        simp only [mem_filter, mem_univ, true_and] at hi
        simp only [a]
        revert hi
        cases z i <;> simp) (L + N)
  rw [sum_const, card_range, nsmul_eq_mul] at hcover hsub
  refine hsub.trans (hcover.trans ?_)
  rw [mul_div_assoc, sum_const, card_range, nsmul_eq_mul]
  gcongr

/-- For a pattern with at least `((α + 1) / η) ^ 2` nonzero entries, at most an `η` fraction of
the queries `v` have `|∑ i, v_i z_i| ≤ α`. -/
private theorem card_abs_sum_le_mul [DecidableEq ι] (z : ι → SignType) {α η : ℝ} (hα : 0 ≤ α)
    (hη : 0 < η) (hz : ((α + 1) / η) ^ 2 ≤ #{i | z i ≠ 0}) :
    (#{v : ι → Bool | |∑ i, signVal (v i) * (z i : ℝ)| ≤ α} : ℝ) ≤
      η * 2 ^ Fintype.card ι := by
  refine (card_abs_sum_le z hα).trans ?_
  have hsqrt : (α + 1) / η ≤ Real.sqrt (#{i | z i ≠ 0} + 1) :=
    Real.le_sqrt_of_sq_le (by linarith)
  have hpos : 0 < Real.sqrt (#{i | z i ≠ 0} + 1) := Real.sqrt_pos.2 (by positivity)
  rw [div_le_iff₀ hpos]
  rw [div_le_iff₀ hη] at hsqrt
  have h2 : (0 : ℝ) ≤ 2 ^ Fintype.card ι := by positivity
  nlinarith

/-- The event that the queries `A` fail to rule out the pattern `z`: on at least a `2 η`
fraction of them, `|∑ i, v_i z_i| ≤ α`. -/
private def PatternBad (A : κ → ι → Bool) (z : ι → SignType) (α η : ℝ) : Prop :=
  2 * η * Fintype.card κ ≤ #{j | |∑ i, signVal (A j i) * (z i : ℝ)| ≤ α}

/-- **Chernoff.** A pattern with at least `((α + 1) / η) ^ 2` nonzero entries survives `m`
independent uniformly random queries with probability at most `exp (-η m / 3)`. -/
private theorem toOuterMeasure_patternBad_le [DecidableEq ι] [DecidableEq κ] (z : ι → SignType)
    {α η : ℝ} (hα : 0 ≤ α) (hη : 0 < η) (hz : ((α + 1) / η) ^ 2 ≤ #{i | z i ≠ 0}) :
    (Probability.PMF.uniformOfFintype (κ → ι → Bool)).toOuterMeasure
        {A | PatternBad A z α η} ≤
      ENNReal.ofReal (Real.exp (-(η * Fintype.card κ / 3))) := by
  classical
  set bad : (ι → Bool) → Prop := fun v => |∑ i, signVal (v i) * (z i : ℝ)| ≤ α
  set score : κ → (ι → Bool) → ℝ := fun _ v => if bad v then 1 else 0
  have hscore : ∀ j v, v ∈ (Probability.PMF.uniformOfFintype (ι → Bool)).support →
      score j v ∈ Set.Icc (0 : ℝ) 1 := fun j v _ => by
    simp only [score]
    split_ifs <;> norm_num
  have hmean : ∑ j : κ, ∑ v, ((Probability.PMF.uniformOfFintype (ι → Bool)) v).toReal *
      score j v ≤ Fintype.card κ * η := by
    have hrow : ∑ v, ((Probability.PMF.uniformOfFintype (ι → Bool)) v).toReal *
        (if bad v then (1 : ℝ) else 0) ≤ η := by
      simp only [Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
        Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat, ENNReal.toReal_pow,
        ENNReal.toReal_ofNat, mul_ite, mul_one, mul_zero]
      rw [← sum_filter, sum_const, nsmul_eq_mul]
      have hc := card_abs_sum_le_mul z hα hη hz
      have h2 : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
      rw [← div_eq_mul_inv, div_le_iff₀ h2]
      simpa only [bad] using hc
    calc ∑ j : κ, ∑ v, ((Probability.PMF.uniformOfFintype (ι → Bool)) v).toReal * score j v
        ≤ ∑ _j : κ, η := sum_le_sum fun j _ => hrow
      _ = Fintype.card κ * η := by rw [sum_const, card_univ, nsmul_eq_mul]
  have h := Probability.PMF.pi_sum_ge_one_add_mul_of_le_one
    (fun _ : κ => Probability.PMF.uniformOfFintype (ι → Bool)) score hscore hmean
    zero_le_one le_rfl
  rw [Probability.PMF.pi_uniformOfFintype] at h
  have hset : {A : κ → ι → Bool | PatternBad A z α η} =
      {A | (1 + 1) * (Fintype.card κ * η) ≤ ∑ j, score j (A j)} := by
    ext A
    simp only [Set.mem_ofPred_eq, PatternBad, score, sum_boole]
    constructor <;> intro h' <;> linarith
  rw [hset]
  rw [ENNReal.le_ofReal_iff_toReal_le (Probability.PMF.toOuterMeasure_ne_top _ _)
    (Real.exp_pos _).le]
  refine h.trans (le_of_eq ?_)
  congr 1
  ring

/-- If two databases both answer at least a `1 / 2 + η` fraction of the queries to within `α`
with the same answers, the queries do not rule out their pattern of disagreement. -/
private theorem patternBad_diffPattern {A : κ → ι → Bool} {y : κ → ℝ} {c d : ι → Bool}
    {α η : ℝ} (hc : AnswersWithin A y c α η) (hd : AnswersWithin A y d α η) :
    PatternBad A (diffPattern c d) α η := by
  classical
  unfold AnswersWithin at hc hd
  unfold PatternBad
  set Sc : Finset κ := {j | |y j - signDot (A j) c| ≤ α}
  set Sd : Finset κ := {j | |y j - signDot (A j) d| ≤ α}
  have hinter : (#Sc : ℝ) + #Sd ≤ #(Sc ∩ Sd) + Fintype.card κ := by
    have h1 := card_union_add_card_inter Sc Sd
    have h2 : #(Sc ∪ Sd) ≤ Fintype.card κ := card_le_univ _
    have : #Sc + #Sd ≤ #(Sc ∩ Sd) + Fintype.card κ := by omega
    exact_mod_cast this
  have hsub : Sc ∩ Sd ⊆
      ({j | |∑ i, signVal (A j i) * (diffPattern c d i : ℝ)| ≤ α} : Finset κ) := by
    intro j hj
    simp only [Sc, Sd, mem_inter, mem_filter, mem_univ, true_and] at hj ⊢
    have h := signDot_sub_signDot (A j) c d
    simp only [abs_le] at hj ⊢
    constructor <;> nlinarith [hj.1.1, hj.1.2, hj.2.1, hj.2.2]
  have := card_le_card hsub
  have : (#(Sc ∩ Sd) : ℝ) ≤
      #{j | |∑ i, signVal (A j i) * (diffPattern c d i : ℝ)| ≤ α} := by exact_mod_cast this
  linarith

/-! ### The attack -/

/-- The queries `A` fail: two databases at Hamming distance at least `((α + 1) / η) ^ 2` both
answer at least a `1 / 2 + η` fraction of them to within `α`, with the same answers `y`. -/
def ReconstructionFails (A : κ → ι → Bool) (α η : ℝ) : Prop :=
  ∃ (y : κ → ℝ) (c d : ι → Bool), AnswersWithin A y c α η ∧ AnswersWithin A y d α η ∧
    ((α + 1) / η) ^ 2 ≤ hammingDist c d

private theorem three_pow_eq_ofReal_exp (n : ℕ) :
    (3 : ℝ≥0∞) ^ n = ENNReal.ofReal (Real.exp (n * Real.log 3)) := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat]

/-- **Random queries rarely fail** [DworkRoth2014, proof of Theorem 8.2]. For `m` uniformly random
`±1` queries on `n` rows, the queries fail with probability at most `3 ^ n exp (-η m / 3)`: a
Chernoff bound for each disagreement pattern and a union bound over the `3 ^ n` patterns. -/
theorem toOuterMeasure_reconstructionFails_le [DecidableEq ι] [DecidableEq κ] {α η : ℝ}
    (hα : 0 ≤ α) (hη : 0 < η) :
    (Probability.PMF.uniformOfFintype (κ → ι → Bool)).toOuterMeasure
        {A | ReconstructionFails A α η} ≤
      3 ^ Fintype.card ι * ENNReal.ofReal (Real.exp (-(η * Fintype.card κ / 3))) := by
  classical
  set E : (ι → SignType) → Set (κ → ι → Bool) := fun z =>
    {A | ((α + 1) / η) ^ 2 ≤ #{i | z i ≠ 0} ∧ PatternBad A z α η}
  have hcover : {A : κ → ι → Bool | ReconstructionFails A α η} ⊆ ⋃ z, E z := by
    rintro A ⟨y, c, d, hc, hd, hcd⟩
    refine Set.mem_iUnion.2 ⟨diffPattern c d, ?_, patternBad_diffPattern hc hd⟩
    rw [card_ne_zero_diffPattern]
    exact hcd
  have hE : ∀ z, (Probability.PMF.uniformOfFintype (κ → ι → Bool)).toOuterMeasure (E z) ≤
      ENNReal.ofReal (Real.exp (-(η * Fintype.card κ / 3))) := by
    intro z
    by_cases hz : ((α + 1) / η) ^ 2 ≤ #{i | z i ≠ 0}
    · exact ((Probability.PMF.uniformOfFintype _).toOuterMeasure.mono
        (show E z ⊆ {A | PatternBad A z α η} from fun A hA => hA.2)).trans
        (toOuterMeasure_patternBad_le z hα hη hz)
    · have : E z = ∅ := Set.eq_empty_of_forall_notMem fun A hA => hz hA.1
      rw [this, MeasureTheory.measure_empty]
      exact bot_le
  calc _ ≤ (Probability.PMF.uniformOfFintype (κ → ι → Bool)).toOuterMeasure (⋃ z, E z) :=
        (Probability.PMF.uniformOfFintype _).toOuterMeasure.mono hcover
    _ ≤ ∑ z, (Probability.PMF.uniformOfFintype (κ → ι → Bool)).toOuterMeasure (E z) :=
        MeasureTheory.measure_iUnion_fintype_le _ _
    _ ≤ ∑ _z : ι → SignType, ENNReal.ofReal (Real.exp (-(η * Fintype.card κ / 3))) :=
        sum_le_sum fun z _ => hE z
    _ = _ := by
        have h3 : Fintype.card SignType = 3 := by decide
        rw [sum_const, card_univ, Fintype.card_fun, h3, nsmul_eq_mul]
        norm_num

open Classical in
/-- The reconstruction adversary of [DworkRoth2014, Theorem 8.2]: given answers `y` to the
`±1` queries `A`, output a database that answers at least a `1 / 2 + η` fraction of them to within
`α`, if there is one (and the all-`false` database otherwise). It is not efficient: it searches all
databases. -/
noncomputable def reconstructSigned (A : κ → ι → Bool) (α η : ℝ) (y : κ → ℝ) : ι → Bool :=
  if h : ∃ c, AnswersWithin A y c α η then h.choose else fun _ => false

/-- On queries that do not fail, the adversary errs in fewer than `((α + 1) / η) ^ 2` positions
whenever the answers are within `α` on a `1 / 2 + η` fraction. -/
theorem hammingDist_reconstructSigned_lt {A : κ → ι → Bool} {α η : ℝ}
    (hA : ¬ ReconstructionFails A α η) {y : κ → ℝ} {d : ι → Bool}
    (hd : AnswersWithin A y d α η) :
    (hammingDist (reconstructSigned A α η y) d : ℝ) < ((α + 1) / η) ^ 2 := by
  have hex : ∃ c, AnswersWithin A y c α η := ⟨d, hd⟩
  rw [reconstructSigned, dite_eq_left hex]
  by_contra hfar
  exact hA ⟨y, hex.choose, d, hex.choose_spec, hd, not_lt.1 hfar⟩

/-- **[DworkRoth2014, Theorem 8.2].** Draw `m ≥ b n` uniformly random `±1` queries on `n` rows.
Except with probability at most `exp (-n (η b / 4 - ln 3))` over the queries, the following holds
for every database `d` and all answers `y` that are within `α` of the truth on at least a
`1 / 2 + η` fraction of the queries: the adversary's output differs from `d` in fewer than
`((α + 1) / η) ^ 2` positions. For `α ≥ 1` this implies Dwork and Roth's bound `(2 α / η) ^ 2`.
For `α < 1` their bound is false (`exists_answersWithin_answersWithin_hammingDist_eq_two`), and
`((α + 1) / η) ^ 2` corrects it. -/
theorem toOuterMeasure_exists_le_hammingDist_reconstructSigned_le [DecidableEq ι]
    [DecidableEq κ] {α η b : ℝ} (hα : 0 ≤ α) (hη : 0 < η)
    (hm : b * Fintype.card ι ≤ Fintype.card κ) :
    (Probability.PMF.uniformOfFintype (κ → ι → Bool)).toOuterMeasure
        {A | ∃ (d : ι → Bool) (y : κ → ℝ), AnswersWithin A y d α η ∧
          ((α + 1) / η) ^ 2 ≤ hammingDist (reconstructSigned A α η y) d} ≤
      ENNReal.ofReal (Real.exp (-(Fintype.card ι * (η * b / 4 - Real.log 3)))) := by
  refine ((Probability.PMF.uniformOfFintype _).toOuterMeasure.mono ?_).trans
    ((toOuterMeasure_reconstructionFails_le hα hη).trans ?_)
  · rintro A ⟨d, y, hd, hfar⟩
    by_contra hA
    exact absurd (hammingDist_reconstructSigned_lt hA hd) (not_lt.2 hfar)
  · rw [three_pow_eq_ofReal_exp, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have hηm : η * (b * Fintype.card ι) ≤ η * Fintype.card κ :=
      mul_le_mul_of_nonneg_left hm hη.le
    have hκ : (0 : ℝ) ≤ Fintype.card κ := Nat.cast_nonneg _
    nlinarith

/-- **Good queries exist.** If `3 ln 3 · n < η m`, some `m` queries on `n` rows do not fail: no two
databases at Hamming distance at least `((α + 1) / η) ^ 2` answer at least a `1 / 2 + η` fraction
of them to within `α` with the same answers. -/
theorem exists_not_reconstructionFails {α η : ℝ} (hα : 0 ≤ α) (hη : 0 < η)
    (hm : 3 * Real.log 3 * Fintype.card ι < η * Fintype.card κ) :
    ∃ A : κ → ι → Bool, ¬ ReconstructionFails A α η := by
  classical
  by_contra hall
  have hall' : ∀ A : κ → ι → Bool, ReconstructionFails A α η :=
    fun A => Classical.not_not.1 fun hA => hall ⟨A, hA⟩
  have h := toOuterMeasure_reconstructionFails_le (ι := ι) (κ := κ) hα hη
  have huniv : {A : κ → ι → Bool | ReconstructionFails A α η} = Set.univ :=
    Set.eq_univ_of_forall hall'
  rw [huniv, (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _)] at h
  rw [three_pow_eq_ofReal_exp, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
    ← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le, ← Real.exp_zero,
    Real.exp_le_exp] at h
  linarith

namespace DifferentiallyPrivate

variable {R : Type*} {M : (ι → Bool) → PMF R} {ε : ℝ} {δ : ℝ≥0∞}

/-- **Private answers to good `±1` queries are inaccurate.** Let `A` be queries that do not fail
(for example from `exists_not_reconstructionFails`), and let `M` be `(ε, δ)`-private for Hamming
adjacency on databases of `n` rows, with outputs from which `ans` reads answers to the queries.
If on every database the answers are within `α` on at least a `1 / 2 + η` fraction of the queries
with probability at least `q`, then `(1 + exp ε) (n - ((α + 1) / η) ^ 2) q ≤ n (exp ε + δ)`.
This combines the attack of [DworkRoth2014, Theorem 8.2] with
`DifferentiallyPrivate.mul_card_sub_mul_le` (a standard derivation; see [DworkRoth2014, §8.1]). -/
theorem mul_card_sub_mul_le_of_answersWithin (h : DifferentiallyPrivate HammingAdjacent M ε δ)
    (hδ : δ ≠ ⊤) {A : κ → ι → Bool} {α η : ℝ} (hA : ¬ ReconstructionFails A α η)
    (ans : R → κ → ℝ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : ∀ d, ENNReal.ofReal q ≤ (M d).toOuterMeasure {o | AnswersWithin A (ans o) d α η}) :
    (1 + Real.exp ε) * (Fintype.card ι - ((α + 1) / η) ^ 2) * q ≤
      Fintype.card ι * (Real.exp ε + δ.toReal) := by
  classical
  set t := ⌊((α + 1) / η) ^ 2⌋₊
  have hG := (h.map fun o => reconstructSigned A α η (ans o)).mul_card_sub_mul_le (t := t)
    (q := ENNReal.ofReal q)
    fun d => (hq d).trans (by
      rw [PMF.toOuterMeasure_map_apply]
      refine (M d).toOuterMeasure.mono fun o ho => ?_
      have := hammingDist_reconstructSigned_lt hA ho
      exact Nat.le_floor this.le)
  have hfin : ENNReal.ofReal (Real.exp ε) + δ ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨by simp, hδ⟩
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hfin) hG
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_add (by simp)
    ENNReal.ofReal_ne_top, ENNReal.toReal_add (by simp) hδ, ENNReal.toReal_ofReal hq0,
    ENNReal.toReal_ofReal (Real.exp_pos ε).le, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    ENNReal.toReal_one] at hreal
  refine le_trans ?_ hreal
  have hsub : (Fintype.card ι : ℝ) - ((α + 1) / η) ^ 2 ≤ ((Fintype.card ι - t : ℕ) : ℝ) := by
    have ht : (t : ℝ) ≤ ((α + 1) / η) ^ 2 := Nat.floor_le (by positivity)
    rcases le_total t (Fintype.card ι) with htn | htn
    · rw [Nat.cast_sub htn]
      linarith
    · rw [Nat.sub_eq_zero_of_le htn, Nat.cast_zero]
      have : (Fintype.card ι : ℝ) ≤ t := by exact_mod_cast htn
      linarith
  have h1 : (0 : ℝ) ≤ 1 + Real.exp ε := by positivity
  gcongr

/-- **Linearly many `±1` queries defeat private accuracy.** If `3 ln 3 · n < η m`, there are `m`
`±1` queries on databases of `n` rows with the following property. Every `(ε, δ)`-private
mechanism for Hamming adjacency whose answers are within `α` on at least a `1 / 2 + η` fraction of
the queries, with probability one on every database, satisfies
`n (1 - δ) ≤ ((α + 1) / η) ^ 2 (1 + exp ε)`. So `α + 1 ≥ η √(n (1 - δ) / (1 + exp ε))`, and error
`o(√n)` is impossible. This is a standard derivation from [DworkRoth2014, Theorem 8.2] (see
[DworkRoth2014, §8.1]). -/
theorem exists_forall_card_mul_one_sub_le_of_answersWithin {α η : ℝ} (hα : 0 ≤ α) (hη : 0 < η)
    (hm : 3 * Real.log 3 * Fintype.card ι < η * Fintype.card κ) :
    ∃ A : κ → ι → Bool, ∀ {R : Type*} (M : (ι → Bool) → PMF R) (ε : ℝ) (δ : ℝ≥0∞)
      (ans : R → κ → ℝ), DifferentiallyPrivate HammingAdjacent M ε δ → δ ≠ ⊤ →
      (∀ d, (M d).toOuterMeasure {o | AnswersWithin A (ans o) d α η} = 1) →
      Fintype.card ι * (1 - δ.toReal) ≤ ((α + 1) / η) ^ 2 * (1 + Real.exp ε) := by
  obtain ⟨A, hA⟩ := exists_not_reconstructionFails (ι := ι) (κ := κ) hα hη hm
  refine ⟨A, fun M ε δ ans h hδ hM => ?_⟩
  have := h.mul_card_sub_mul_le_of_answersWithin hδ hA ans zero_le_one fun d => by
    rw [hM d, ENNReal.ofReal_one]
  nlinarith [Real.exp_pos ε]

end DifferentiallyPrivate

/-! ### The constant for small `α` -/

/-- If `c` and `d` agree off `i₁ ≠ i₂`, the difference of their answers to `v` involves only those
two rows. -/
private theorem signDot_sub_signDot_eq_add {v c d : ι → Bool} {i₁ i₂ : ι} (hi : i₁ ≠ i₂)
    (h : ∀ i, i ≠ i₁ ∧ i ≠ i₂ → c i = d i) :
    signDot v c - signDot v d = signVal (v i₁) * (signVal (c i₁) - signVal (d i₁)) +
      signVal (v i₂) * (signVal (c i₂) - signVal (d i₂)) := by
  unfold signDot
  rw [← sum_sub_distrib, Fintype.sum_eq_add i₁ i₂ hi fun i hi' => by rw [h i hi', sub_self]]
  ring

/-- If `c` and `d` give the same answer on at least half of `m ≥ 10` queries, some answers are
exact for both on at least a `7 / 10` fraction: answer as `c`, except as `d` on half of the
remaining queries. -/
private theorem exists_answersWithin_zero_of_le_two_mul {A : κ → ι → Bool} {c d : ι → Bool}
    (hm : 10 ≤ Fintype.card κ)
    (hT : Fintype.card κ ≤ 2 * #{j | signDot (A j) c = signDot (A j) d}) :
    ∃ y : κ → ℝ, AnswersWithin A y c 0 (1 / 5) ∧ AnswersWithin A y d 0 (1 / 5) := by
  classical
  set T : Finset κ := {j | signDot (A j) c = signDot (A j) d} with hTdef
  obtain ⟨W, hWU, hW⟩ := exists_subset_card_eq (s := Tᶜ) (n := #Tᶜ / 2) (Nat.div_le_self _ _)
  set y : κ → ℝ := fun j => if j ∈ W then signDot (A j) d else signDot (A j) c with hy
  have hTc := card_compl T
  have hTm : #T ≤ Fintype.card κ := card_le_univ T
  refine ⟨y, ?_, ?_⟩
  · unfold AnswersWithin
    have hsub : Wᶜ ⊆ ({j | |y j - signDot (A j) c| ≤ 0} : Finset κ) := by
      intro j hj
      rw [mem_compl] at hj
      simp only [mem_filter, mem_univ, true_and, y, hj, ↓reduceIte, sub_self, abs_zero, le_refl]
    have h1 := card_le_card hsub
    rw [card_compl] at h1
    have h7 : 7 * Fintype.card κ ≤ 10 * #({j | |y j - signDot (A j) c| ≤ 0} : Finset κ) := by
      omega
    have h7' : (7 : ℝ) * Fintype.card κ ≤
        10 * #({j | |y j - signDot (A j) c| ≤ 0} : Finset κ) := by
      exact_mod_cast h7
    linarith
  · unfold AnswersWithin
    have hsub : T ∪ W ⊆ ({j | |y j - signDot (A j) d| ≤ 0} : Finset κ) := by
      intro j hj
      simp only [mem_filter, mem_univ, true_and]
      by_cases hjW : j ∈ W
      · simp only [y, hjW, ↓reduceIte, sub_self, abs_zero, le_refl]
      · have hjT : j ∈ T := (mem_union.1 hj).resolve_right hjW
        simp only [T, mem_filter, mem_univ, true_and] at hjT
        simp only [y, hjW, ↓reduceIte, hjT, sub_self, abs_zero, le_refl]
    have hdisj : Disjoint T W := disjoint_of_subset_right hWU disjoint_compl_right
    have h1 := card_le_card hsub
    rw [card_union_of_disjoint hdisj] at h1
    have h7 : 7 * Fintype.card κ ≤ 10 * #({j | |y j - signDot (A j) d| ≤ 0} : Finset κ) := by
      omega
    have h7' : (7 : ℝ) * Fintype.card κ ≤
        10 * #({j | |y j - signDot (A j) d| ≤ 0} : Finset κ) := by
      exact_mod_cast h7
    linarith

/-- **The constant `(2 α / η) ^ 2` of [DworkRoth2014, Theorem 8.2] fails at `α = 0`.** Whatever
the `m ≥ 10` queries on at least two rows, there are answers `y` and two databases at Hamming
distance `2` that both answer at least a `1 / 2 + 1 / 5` fraction of the queries exactly. So no
attack reconstructs to within `(2 · 0 / η) ^ 2 = 0` positions at `η = 1 / 5`, for any number of
queries. An additive term as in `((α + 1) / η) ^ 2` is needed. -/
theorem exists_answersWithin_answersWithin_hammingDist_eq_two {i₁ i₂ : ι}
    (hi : i₁ ≠ i₂) (A : κ → ι → Bool) (hm : 10 ≤ Fintype.card κ) :
    ∃ (y : κ → ℝ) (c d : ι → Bool), AnswersWithin A y c 0 (1 / 5) ∧
      AnswersWithin A y d 0 (1 / 5) ∧ hammingDist c d = 2 := by
  classical
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset κ))
    (fun j => A j i₁ = A j i₂)
  rw [card_univ] at hsplit
  by_cases hS : Fintype.card κ ≤ 2 * #{j | A j i₁ = A j i₂}
  · -- Where the two query bits agree, moving the one `true` from `i₁` to `i₂` keeps the answer.
    have hcd : ∀ i, i ≠ i₁ ∧ i ≠ i₂ →
        decide (i = i₁) = decide (i = i₂) := fun i h => by simp [h.1, h.2]
    have hsub : ({j | A j i₁ = A j i₂} : Finset κ) ⊆
        ({j | signDot (A j) (fun i => decide (i = i₁)) =
          signDot (A j) (fun i => decide (i = i₂))} : Finset κ) := by
      intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj ⊢
      rw [← sub_eq_zero, signDot_sub_signDot_eq_add hi hcd, hj]
      simp only [decide_true, hi, hi.symm, decide_false, signVal_true, signVal_false]
      ring
    obtain ⟨y, hc, hd⟩ := exists_answersWithin_zero_of_le_two_mul hm
      (hS.trans (Nat.mul_le_mul_left 2 (card_le_card hsub)))
    refine ⟨y, fun i => decide (i = i₁), fun i => decide (i = i₂), hc, hd, ?_⟩
    rw [hammingDist, card_eq_two]
    refine ⟨i₁, i₂, hi, ?_⟩
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    by_cases h1 : i = i₁ <;> by_cases h2 : i = i₂ <;> simp_all
  · -- Where they differ, flipping both rows keeps the answer.
    have hcd : ∀ i, i ≠ i₁ ∧ i ≠ i₂ →
        decide (i = i₁ ∨ i = i₂) = false := fun i h => by simp [h.1, h.2]
    have hsub : ({j | ¬ A j i₁ = A j i₂} : Finset κ) ⊆
        ({j | signDot (A j) (fun i => decide (i = i₁ ∨ i = i₂)) =
          signDot (A j) (fun _ => false)} : Finset κ) := by
      intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj ⊢
      rw [← sub_eq_zero, signDot_sub_signDot_eq_add hi hcd]
      simp only [true_or, or_true, decide_true, signVal_true, signVal_false]
      revert hj
      cases A j i₁ <;> cases A j i₂ <;> simp only [signVal_true, signVal_false] <;> norm_num
    obtain ⟨y, hc, hd⟩ := exists_answersWithin_zero_of_le_two_mul hm
      ((show Fintype.card κ ≤ 2 * #({j | ¬ A j i₁ = A j i₂} : Finset κ) by omega).trans
        (Nat.mul_le_mul_left 2 (card_le_card hsub)))
    refine ⟨y, fun i => decide (i = i₁ ∨ i = i₂), fun _ => false, hc, hd, ?_⟩
    rw [hammingDist, card_eq_two]
    refine ⟨i₁, i₂, hi, ?_⟩
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    by_cases h1 : i = i₁ <;> by_cases h2 : i = i₂ <;> simp_all

end Cslib.Privacy
