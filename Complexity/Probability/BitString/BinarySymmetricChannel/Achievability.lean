/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.BitString.BinarySymmetricChannel
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Order.Filter.AtTopBot.Defs
import Complexity.Foundations.Combinatorics.BinomialTail
import Complexity.Foundations.Data.BitString.Basic
import Complexity.Foundations.Data.Nat.Choose.Entropy
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Shannon's coding theorem for the binary symmetric channel: achievability

Random codes achieve every rate below the capacity `1 - h₂(p)` of the binary symmetric channel
`BSC_p`, for `0 ≤ p < 1 / 2`, where `h₂(p) = Real.binEntropy p / Real.log 2` is the binary entropy
in bits: the positive part of **Shannon's noisy-channel coding theorem** for `BSC_p`
[Shannon, Theorem 11][Shannon1948]
[Guruswami, Rudra and Sudan, Theorem 6.3.1(1)][GuruswamiRudraSudan2019].

The proof follows [Guruswami, Rudra and Sudan, Section 6.3.2][GuruswamiRudraSudan2019]. A nearest
codeword decoder errs on the message `m` only if the noise flips more than `r` bits, or some other
codeword lies within distance `r` of the received word. Over a uniformly random codebook the second
event has probability at most `(|M| - 1) |B(n, r)| / 2 ^ n` by the union bound, where
`|B(n, r)| = ∑_{j ≤ r} C(n, j)` is the volume of a Hamming ball. So the average error over random
codebooks and messages is at most `T + (|M| - 1) |B(n, r)| / 2 ^ n`, where `T` is the binomial
upper tail `∑_{r < k ≤ n} C(n, k) p ^ k (1 - p) ^ (n - k)`
(`Cslib.BitString.expect_expect_decodingError_le`). Some codebook with `2 K` codewords is at least
as good as the average, and by Markov's inequality at least `K` of its messages have error bound at
most twice the average; keeping them gives a code with `K` codewords whose *maximal* error is at
most `2 (T + (2 K - 1) |B(n, r)| / 2 ^ n)` for every nearest codeword decoder
(`Cslib.BitString.exists_code_decodingError_le`; Claim 6.3.3 of the source).

For the asymptotic statement take `r = ⌊ρ n⌋` with `p < ρ < 1 / 2` and `R < 1 - h₂(ρ)`.
Hoeffding's inequality bounds `T` by `exp (-2 (ρ - p) ^ 2 n)` and the entropy bound
`Cslib.sum_choose_le_exp_mul_binEntropy` bounds `|B(n, r)|` by `exp (n h(ρ))`, so codes with
`2 ^ ⌈R n⌉` codewords have maximal error at most `10 exp (-δ n)` for an explicit `δ > 0`
(`Cslib.BitString.exists_pos_forall_exists_code_decodingError_le_exp`) and hence at most any `ε > 0`
for all large `n` (`Cslib.BitString.eventually_exists_code_decodingError_le`).

The theorems cover nearest codeword (maximum-likelihood) decoders only. They prove the
achievability half of the theorem for `BSC_p`; the converse (rates above `1 - h₂(p)` fail), general
discrete memoryless channels and explicit or efficiently decodable capacity-achieving codes are not
formalized here.

## Main results

* `Cslib.BitString.expect_expect_decodingError_le`: the random-coding bound on the average error.
* `Cslib.BitString.exists_code_decodingError_le`: a code with small maximal error, for every length,
  size and radius.
* `Cslib.BitString.exists_pos_forall_exists_code_decodingError_le_exp`: achievability with an
  exponentially small maximal error.
* `Cslib.BitString.eventually_exists_code_decodingError_le`: achievability, asymptotic form.

## References

* [C. E. Shannon, *A Mathematical Theory of Communication*][Shannon1948]
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*][GuruswamiRudraSudan2019], draft of
  26 August 2025
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators unitInterval

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Type*}

/-! ### The random-coding argument -/

/-- The union bound for ball decoding at radius `r`: more than `r` bits flip, or the received word
falls within distance `r` of another codeword. -/
private noncomputable def ballBound [Fintype M] [DecidableEq M] (p : I) (r : ℕ)
    (E : M → ι → Bool) (m : M) : ℝ :=
  bernoulliAverage p (fun e : ι → Bool => if r < weight e then 1 else 0) +
    ∑ m' ∈ univ.erase m,
      bernoulliAverage p (fun e => if hammingDist (E m') (E m + e) ≤ r then 1 else 0)

/-- The probability of an event under the noise of `BSC_p` is nonnegative. -/
private theorem bernoulliAverage_ite_nonneg (p : I) (P : (ι → Bool) → Prop) [DecidablePred P] :
    0 ≤ bernoulliAverage p (fun e => if P e then (1 : ℝ) else 0) := by
  simpa only [bernoulliAverage_const] using bernoulliAverage_mono p.2.1 p.2.2
    (f := fun _ => 0) (g := fun e => if P e then (1 : ℝ) else 0)
    fun e => by split_ifs <;> norm_num

variable [Fintype M] [DecidableEq M]

private theorem ballBound_nonneg (p : I) (r : ℕ) (E : M → ι → Bool) (m : M) :
    0 ≤ ballBound p r E m :=
  add_nonneg (bernoulliAverage_ite_nonneg p _)
    (sum_nonneg fun _ _ => bernoulliAverage_ite_nonneg p _)

/-- A nearest decoder errs only if more than `r` bits flip or another codeword lies within
distance `r` of the received word. -/
private theorem decodingError_le_ballBound {E : M → ι → Bool} {D : (ι → Bool) → M}
    (hD : IsNearestDecoder E D) (p : I) (r : ℕ) (m : M) :
    decodingError p E D m ≤ ballBound p r E m := by
  rw [decodingError_eq_bernoulliAverage, ballBound, ← bernoulliAverage_sum,
    ← bernoulliAverage_add]
  refine bernoulliAverage_mono p.2.1 p.2.2 fun e => ?_
  have hnn : 0 ≤ ∑ m' ∈ univ.erase m,
      (if hammingDist (E m') (E m + e) ≤ r then (1 : ℝ) else 0) :=
    sum_nonneg fun _ _ => by split_ifs <;> norm_num
  by_cases hm : D (E m + e) ≠ m
  · rw [ite_eq_left hm]
    by_cases hw : r < weight e
    · rw [ite_eq_left hw]
      linarith
    · rw [ite_eq_right hw, zero_add]
      refine le_trans ?_ (single_le_sum (f := fun m' =>
        if hammingDist (E m') (E m + e) ≤ r then (1 : ℝ) else 0)
        (fun _ _ => by split_ifs <;> norm_num) (mem_erase.mpr ⟨hm, mem_univ _⟩))
      rw [ite_eq_left]
      calc hammingDist (E (D (E m + e))) (E m + e) ≤ hammingDist (E m) (E m + e) := hD _ _
        _ = weight e := by rw [hammingDist_eq_weight_add, BitString.add_cancel_left]
        _ ≤ r := not_lt.mp hw
  · rw [ite_eq_right hm]
    have : (0 : ℝ) ≤ if r < weight e then 1 else 0 := by split_ifs <;> norm_num
    linarith

/-- Passing to a subcode can only decrease the union bound. -/
private theorem ballBound_comp_le {K : Type*} [Fintype K] [DecidableEq K] (f : K ↪ M) (p : I)
    (r : ℕ) (E : M → ι → Bool) (k : K) :
    ballBound p r (E ∘ f) k ≤ ballBound p r E (f k) := by
  rw [ballBound, ballBound]
  gcongr
  simp only [Function.comp_apply]
  rw [← sum_map _ f (fun m' =>
    bernoulliAverage p (fun e => if hammingDist (E m') (E (f k) + e) ≤ r then 1 else 0))]
  refine sum_le_sum_of_subset_of_nonneg (fun m' hm' => ?_) fun m' _ _ => ?_
  · obtain ⟨k', hk', rfl⟩ := mem_map.mp hm'
    exact mem_erase.mpr ⟨fun h => (mem_erase.mp hk').1 (f.injective h), mem_univ _⟩
  · exact bernoulliAverage_ite_nonneg p _

/-- Summing a function of one codeword over all codebooks. -/
private theorem sum_comp_apply (m' : M) (f : (ι → Bool) → ℝ) :
    ∑ E : M → ι → Bool, f (E m') =
      (2 ^ Fintype.card ι) ^ (Fintype.card M - 1) * ∑ x, f x := by
  rw [← sum_fiberwise univ (fun E : M → ι → Bool => E m') (fun E => f (E m')), mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_congr rfl fun E hE => by rw [(mem_filter.mp hE).2], sum_const, nsmul_eq_mul]
  congr 1
  have h := Fintype.card_filter_piFinset_const (univ : Finset (ι → Bool)) m' x
  rw [Fintype.piFinset_univ, ite_eq_left (mem_univ _), card_univ, Fintype.card_fun,
    Fintype.card_bool] at h
  rw [h]
  push_cast
  rfl

/-- Over all codebooks, the codeword of `m' ≠ m` lies within distance `r` of `E m + e` exactly as
often as a uniformly random word lies in the ball of radius `r` about `0`. -/
private theorem sum_ite_hammingDist_le {m m' : M} (hm : m' ≠ m) (r : ℕ) (e : ι → Bool) :
    ∑ E : M → ι → Bool, (if hammingDist (E m') (E m + e) ≤ r then (1 : ℝ) else 0) =
      (2 ^ Fintype.card ι) ^ (Fintype.card M - 1) *
        ∑ j ∈ range (r + 1), ((Fintype.card ι).choose j : ℝ) := by
  -- translating the codeword of `m'` by `E m + e` permutes the codebooks
  let φ : (M → ι → Bool) → M → ι → Bool := fun E => Function.update E m' (E m' + (E m + e))
  have hφ : Function.Involutive φ := fun E => by
    simp only [φ, Function.update_self, Function.update_of_ne hm.symm, Function.update_idem,
      BitString.add_cancel_right, Function.update_eq_self]
  calc ∑ E : M → ι → Bool, (if hammingDist (E m') (E m + e) ≤ r then (1 : ℝ) else 0)
      = ∑ E : M → ι → Bool, (if weight (E m') ≤ r then (1 : ℝ) else 0) :=
        Fintype.sum_equiv (hφ.toPerm φ) _ _ fun E => by
          simp only [Function.Involutive.coe_toPerm, φ, Function.update_self,
            hammingDist_eq_weight_add]
    _ = (2 ^ Fintype.card ι) ^ (Fintype.card M - 1) *
          ∑ x : ι → Bool, (if weight x ≤ r then (1 : ℝ) else 0) :=
        sum_comp_apply m' fun x => if weight x ≤ r then (1 : ℝ) else 0
    _ = _ := by
        rw [sum_boole, card_filter_weight_le]
        push_cast
        rfl

/-- **The average union bound over all codebooks**: summing over the `(2 ^ n) ^ |M|` codebooks,
the second term contributes `(|M| - 1) |B(n, r)|` for each `2 ^ n` codebooks. -/
private theorem sum_ballBound (p : I) (r : ℕ) (m : M) :
    ∑ E : M → ι → Bool, ballBound p r E m =
      (2 ^ Fintype.card ι) ^ Fintype.card M *
          bernoulliAverage p (fun e : ι → Bool => if r < weight e then 1 else 0) +
        (Fintype.card M - 1 : ℕ) * (2 ^ Fintype.card ι) ^ (Fintype.card M - 1) *
          ∑ j ∈ range (r + 1), ((Fintype.card ι).choose j : ℝ) := by
  simp only [ballBound, sum_add_distrib]
  congr 1
  · rw [sum_const, card_univ, nsmul_eq_mul, Fintype.card_fun, Fintype.card_fun,
      Fintype.card_bool]
    push_cast
    rfl
  · rw [sum_comm]
    have h (m' : M) (hm' : m' ∈ univ.erase m) : ∑ E : M → ι → Bool, bernoulliAverage p
        (fun e => if hammingDist (E m') (E m + e) ≤ r then (1 : ℝ) else 0) =
        (2 ^ Fintype.card ι) ^ (Fintype.card M - 1) *
          ∑ j ∈ range (r + 1), ((Fintype.card ι).choose j : ℝ) := by
      rw [← bernoulliAverage_sum]
      exact (congrArg (bernoulliAverage p) (funext fun e =>
        sum_ite_hammingDist_le (mem_erase.mp hm').1 r e)).trans (bernoulliAverage_const _ _)
    rw [sum_congr rfl h, sum_const, card_erase_of_mem (mem_univ m), card_univ, nsmul_eq_mul,
      mul_assoc]

/-- Summed over all codebooks and messages, the union bound is
`|M| (T + (|M| - 1) |B(n, r)| / 2 ^ n)` per codebook. -/
private theorem sum_sum_ballBound [Nonempty M] (p : I) (r : ℕ) :
    ∑ E : M → ι → Bool, ∑ m, ballBound p r E m =
      ∑ _E : M → ι → Bool, Fintype.card M *
        (bernoulliAverage p (fun e : ι → Bool => if r < weight e then 1 else 0) +
          (Fintype.card M - 1 : ℕ) * (∑ j ∈ range (r + 1), ((Fintype.card ι).choose j : ℝ)) /
            2 ^ Fintype.card ι) := by
  rw [sum_comm, sum_congr rfl fun m _ => sum_ballBound p r m, sum_const, sum_const, card_univ,
    card_univ, nsmul_eq_mul, nsmul_eq_mul, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_bool]
  obtain ⟨N, hN⟩ := Nat.exists_eq_add_of_lt (Fintype.card_pos (α := M))
  rw [hN, zero_add, Nat.add_sub_cancel]
  have h2 : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  push_cast
  field_simp
  ring

/-- **Random coding**: some codebook has union bounds summing to at most
`|M| (T + (|M| - 1) |B(n, r)| / 2 ^ n)`, the average over all codebooks. -/
private theorem exists_sum_ballBound_le [Nonempty M] (p : I) (r : ℕ) :
    ∃ E : M → ι → Bool, ∑ m, ballBound p r E m ≤
      Fintype.card M * (bernoulliAverage p (fun e : ι → Bool => if r < weight e then 1 else 0) +
        (Fintype.card M - 1 : ℕ) * (∑ j ∈ range (r + 1), ((Fintype.card ι).choose j : ℝ)) /
          2 ^ Fintype.card ι) := by
  obtain ⟨E, -, hE⟩ :=
    exists_le_of_sum_le univ_nonempty (sum_sum_ballBound (ι := ι) (M := M) p r).le
  exact ⟨E, hE⟩

omit [DecidableEq ι] in
/-- **Achievability for the binary symmetric channel, finite form** (random coding with
expurgation) [Guruswami, Rudra and Sudan, Section 6.3.2 and Claim 6.3.3][GuruswamiRudraSudan2019]:
for every radius `r` there is a code with `K` codewords of length `n` on which every nearest
codeword decoder has *maximal* error probability at most `2 (T + (2 K - 1) |B(n, r)| / 2 ^ n)`,
where `T = ∑_{r < k ≤ n} C(n, k) p ^ k (1 - p) ^ (n - k)` is the probability that more than `r`
bits flip and `|B(n, r)| = ∑_{j ≤ r} C(n, j)` is the volume of a Hamming ball of radius `r`. -/
theorem exists_code_decodingError_le (p : I) (r K : ℕ) :
    ∃ E : Fin K → ι → Bool, ∀ D, IsNearestDecoder E D → ∀ k,
      decodingError p E D k ≤
        2 * (∑ j ∈ range (Fintype.card ι + 1) with r < j,
            ((Fintype.card ι).choose j : ℝ) * p ^ j * (1 - p) ^ (Fintype.card ι - j) +
          (2 * K - 1 : ℕ) * (∑ j ∈ range (r + 1), ((Fintype.card ι).choose j : ℝ)) /
            2 ^ Fintype.card ι) := by
  classical
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · exact ⟨Fin.elim0, fun _ _ k => k.elim0⟩
  have : Nonempty (Fin (2 * K)) := ⟨⟨0, by omega⟩⟩
  obtain ⟨E, hE⟩ := exists_sum_ballBound_le (ι := ι) (M := Fin (2 * K)) p r
  rw [bernoulliAverage_lt_weight, Fintype.card_fin] at hE
  set β : ℝ := ∑ j ∈ range (Fintype.card ι + 1) with r < j,
      ((Fintype.card ι).choose j : ℝ) * p ^ j * (1 - p) ^ (Fintype.card ι - j) +
    (2 * K - 1 : ℕ) * (∑ j ∈ range (r + 1), ((Fintype.card ι).choose j : ℝ)) /
      2 ^ Fintype.card ι with hβ
  have hp0 : (0 : ℝ) ≤ p := p.2.1
  have hp1 : (0 : ℝ) ≤ 1 - p := sub_nonneg.mpr p.2.2
  have hβ0 : 0 ≤ β := add_nonneg (sum_nonneg fun j _ => by positivity) (by positivity)
  -- Markov: at most `K` messages have union bound above `2 β`
  set B : Finset (Fin (2 * K)) := {m | 2 * β < ballBound p r E m} with hB
  have hBK : #B ≤ K := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 : ∑ m ∈ B, 2 * β < ∑ m ∈ B, ballBound p r E m :=
      sum_lt_sum_of_nonempty (card_pos.mp (by omega)) fun m hm => (mem_filter.mp hm).2
    have h2 : ∑ m ∈ B, ballBound p r E m ≤ ∑ m, ballBound p r E m :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) fun m _ _ => ballBound_nonneg p r E m
    rw [sum_const, nsmul_eq_mul] at h1
    have h3 : (K + 1 : ℝ) ≤ #B := by exact_mod_cast hlt
    push_cast at hE
    nlinarith
  set G : Finset (Fin (2 * K)) := {m | ballBound p r E m ≤ 2 * β} with hG
  have hGK : K ≤ #G := by
    have := card_filter_add_card_filter_not (s := univ) (fun m : Fin (2 * K) =>
      ballBound p r E m ≤ 2 * β)
    simp only [not_le, card_univ, Fintype.card_fin] at this
    rw [← hG, ← hB] at this
    omega
  obtain ⟨S, hSG, hS⟩ := exists_subset_card_eq hGK
  let f : Fin K ↪ Fin (2 * K) := (S.orderEmbOfFin hS).toEmbedding
  refine ⟨E ∘ f, fun D hD k => ?_⟩
  calc decodingError p (E ∘ f) D k ≤ ballBound p r (E ∘ f) k :=
        decodingError_le_ballBound hD p r k
    _ ≤ ballBound p r E (f k) := ballBound_comp_le f p r E k
    _ ≤ 2 * β := (mem_filter.mp (hSG (S.orderEmbOfFin_mem hS k))).2

/-- **The random-coding bound** [Guruswami, Rudra and Sudan, Section 6.3.2]
[GuruswamiRudraSudan2019]: over a uniformly random codebook `E : M → (ι → Bool)` and a uniformly
random message, the error probability of nearest codeword decoding averages at most
`T + (|M| - 1) |B(n, r)| / 2 ^ n`, where `T` is the probability that more than `r` bits flip. The
decoder `D E` may depend on the codebook. -/
theorem expect_expect_decodingError_le [Nonempty M] (p : I) (r : ℕ)
    (D : (M → ι → Bool) → (ι → Bool) → M) (hD : ∀ E, IsNearestDecoder E (D E)) :
    𝔼 E : M → ι → Bool, 𝔼 m, decodingError p E (D E) m ≤
      ∑ j ∈ range (Fintype.card ι + 1) with r < j,
          ((Fintype.card ι).choose j : ℝ) * p ^ j * (1 - p) ^ (Fintype.card ι - j) +
        (Fintype.card M - 1 : ℕ) * (∑ j ∈ range (r + 1), ((Fintype.card ι).choose j : ℝ)) /
          2 ^ Fintype.card ι := by
  rw [← bernoulliAverage_lt_weight]
  have hM : (Fintype.card M : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc 𝔼 E : M → ι → Bool, 𝔼 m, decodingError p E (D E) m
      ≤ 𝔼 E : M → ι → Bool, 𝔼 m, ballBound p r E m :=
        expect_le_expect fun E _ => expect_le_expect fun m _ =>
          decodingError_le_ballBound (hD E) p r m
    _ = 𝔼 _E : M → ι → Bool,
          (bernoulliAverage p (fun e : ι → Bool => if r < weight e then 1 else 0) +
            (Fintype.card M - 1 : ℕ) * (∑ j ∈ range (r + 1), ((Fintype.card ι).choose j : ℝ)) /
              2 ^ Fintype.card ι) := by
        rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
        congr 1
        simp only [Fintype.expect_eq_sum_div_card]
        rw [← Finset.sum_div, sum_sum_ballBound, ← mul_sum, mul_div_cancel_left₀ _ hM]
    _ = _ := expect_const univ_nonempty _

omit [DecidableEq ι] [Fintype M] [DecidableEq M] in
/-- **Hoeffding's bound on the number of flips**, in the form used below: if `p n ≤ ρ n < r + 1`,
more than `r` of the `n` bits flip with probability at most `exp (-2 (ρ - p) ^ 2 n)`. -/
private theorem sum_filter_lt_choose_mul_pow_le {n r : ℕ} (p : I) {ρ : ℝ} (hpρ : (p : ℝ) ≤ ρ)
    (hr : ρ * n < r + 1) :
    ∑ k ∈ range (n + 1) with r < k, (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) ≤
      Real.exp (-(2 * (ρ - p) ^ 2 * n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.zero_add, range_one, filter_singleton, ite_eq_right (Nat.not_lt_zero r), sum_empty]
    exact (Real.exp_pos _).le
  have hp0 : (0 : ℝ) ≤ p := p.2.1
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have ht : (ρ - p) * n ≤ (r + 1 : ℝ) - n * p := by linarith
  have h0 : 0 ≤ (ρ - p) * n := mul_nonneg (by linarith) hn'.le
  have h := bscNoise_toOuterMeasure_lt_weight_toReal_le (ι := Fin n) p
    (r := r) (by rw [Fintype.card_fin]; nlinarith)
  rw [bscNoise_toOuterMeasure_lt_weight_toReal, Fintype.card_fin] at h
  refine h.trans (Real.exp_le_exp.mpr ?_)
  rw [neg_mul, neg_div, neg_le_neg_iff, le_div_iff₀ hn']
  nlinarith [mul_le_mul ht ht h0 (h0.trans ht)]

open Filter Topology in
/-- **Shannon's noisy-channel coding theorem for the binary symmetric channel, achievability**
[Shannon, Theorem 11][Shannon1948]
[Guruswami, Rudra and Sudan, Theorem 6.3.1(1)][GuruswamiRudraSudan2019]:
let `0 ≤ p < 1 / 2` and let `R` be a rate below the capacity `1 - h₂(p)`, where
`h₂(p) = Real.binEntropy p / log 2` is the binary entropy in bits. There is `δ > 0` such that for
every length `n` some code with `2 ^ ⌈R n⌉₊` codewords of length `n` has maximal error probability
at most `10 exp (-δ n)` under every nearest-codeword (maximum-likelihood) decoder. -/
theorem exists_pos_forall_exists_code_decodingError_le_exp (p : I) (hp : (p : ℝ) < 1 / 2) {R : ℝ}
    (hR : R < 1 - Real.binEntropy p / Real.log 2) :
    ∃ δ > 0, ∀ n : ℕ, ∃ E : Fin (2 ^ ⌈R * n⌉₊) → BitString n, ∀ D, IsNearestDecoder E D →
      ∀ k, decodingError p E D k ≤ 10 * Real.exp (-(δ * n)) := by
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hp0 : (0 : ℝ) ≤ p := p.2.1
  -- work with a nonnegative rate
  have hcap : 0 < 1 - Real.binEntropy p / Real.log 2 := by
    have : Real.binEntropy p < Real.log 2 :=
      Real.binEntropy_lt_log_two.mpr (by norm_num at hp ⊢; exact hp.ne)
    rw [sub_pos, div_lt_one hL]
    exact this
  set R' := max R 0 with hR'
  have hR'cap : R' < 1 - Real.binEntropy p / Real.log 2 := max_lt hR hcap
  -- a radius fraction `ρ ∈ (p, 1 / 2)` still below capacity
  have hcont : Continuous fun x => 1 - Real.binEntropy x / Real.log 2 :=
    continuous_const.sub (Real.binEntropy_continuous.div_const _)
  have hev : ∀ᶠ x in 𝓝[>] (p : ℝ),
      R' < 1 - Real.binEntropy x / Real.log 2 ∧ x ∈ Set.Ioo (p : ℝ) (1 / 2) :=
    ((hcont.continuousAt.eventually (lt_mem_nhds hR'cap)).filter_mono nhdsWithin_le_nhds).and
      (Ioo_mem_nhdsGT hp)
  obtain ⟨ρ, hρR, hpρ, hρ⟩ := hev.exists
  have hδ₁ : 0 < 2 * (ρ - p) ^ 2 := by have : 0 < ρ - p := sub_pos.mpr hpρ; positivity
  have hδ₂ : 0 < (1 - R') * Real.log 2 - Real.binEntropy ρ := by
    have := (lt_sub_comm.mp hρR)
    rw [div_lt_iff₀ hL] at this
    linarith
  refine ⟨min (2 * (ρ - p) ^ 2) ((1 - R') * Real.log 2 - Real.binEntropy ρ), lt_min hδ₁ hδ₂,
    fun n => ?_⟩
  obtain ⟨E, hE⟩ := exists_code_decodingError_le (ι := Fin n) p ⌊ρ * n⌋₊ (2 ^ ⌈R * n⌉₊)
  refine ⟨E, fun D hD k => (hE D hD k).trans ?_⟩
  simp only [Fintype.card_fin]
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  -- the tail term
  have hT := sum_filter_lt_choose_mul_pow_le (n := n) (r := ⌊ρ * n⌋₊) p hpρ.le
    (Nat.lt_floor_add_one _)
  -- the volume term
  have hV := Cslib.sum_choose_le_exp_mul_binEntropy (n := n) (r := ⌊ρ * n⌋₊) (by linarith)
    hρ.le (Nat.floor_le (mul_nonneg (by linarith) hn))
  -- the number of codewords
  have hK : ((2 * 2 ^ ⌈R * n⌉₊ - 1 : ℕ) : ℝ) ≤ 4 * Real.exp (R' * n * Real.log 2) := by
    have h1 : ((2 * 2 ^ ⌈R * n⌉₊ - 1 : ℕ) : ℝ) ≤ 2 * 2 ^ ⌈R * n⌉₊ := by
      have : (2 * 2 ^ ⌈R * n⌉₊ - 1 : ℕ) ≤ 2 * 2 ^ ⌈R * n⌉₊ := Nat.sub_le _ _
      exact_mod_cast this
    have h2 : (⌈R * n⌉₊ : ℝ) ≤ R' * n + 1 := by
      have := Nat.ceil_lt_add_one (mul_nonneg (le_max_right R 0) hn)
      have h3 : ⌈R * n⌉₊ ≤ ⌈R' * n⌉₊ := Nat.ceil_mono (by nlinarith [le_max_left R 0])
      have : (⌈R * n⌉₊ : ℝ) ≤ ⌈R' * n⌉₊ := by exact_mod_cast h3
      linarith
    have h4 : (2 : ℝ) ^ ⌈R * n⌉₊ = Real.exp (⌈R * n⌉₊ * Real.log 2) := by
      rw [← Real.log_pow, Real.exp_log (by positivity)]
    have h5 : Real.exp (⌈R * n⌉₊ * Real.log 2) ≤ Real.exp ((R' * n + 1) * Real.log 2) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h2 hL.le)
    have h6 : Real.exp ((R' * n + 1) * Real.log 2) = 2 * Real.exp (R' * n * Real.log 2) := by
      rw [add_mul, one_mul, Real.exp_add, Real.exp_log two_pos, mul_comm]
    linarith
  have h2n : (2 : ℝ) ^ n = Real.exp (n * Real.log 2) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have hsecond : ((2 * 2 ^ ⌈R * n⌉₊ - 1 : ℕ) : ℝ) *
      (∑ j ∈ range (⌊ρ * n⌋₊ + 1), (n.choose j : ℝ)) / 2 ^ n ≤
        4 * Real.exp (-(((1 - R') * Real.log 2 - Real.binEntropy ρ) * n)) := by
    rw [div_le_iff₀ (by positivity), h2n]
    calc _ ≤ 4 * Real.exp (R' * n * Real.log 2) * Real.exp (n * Real.binEntropy ρ) :=
          mul_le_mul hK hV (sum_nonneg fun _ _ => by positivity) (by positivity)
      _ = 4 * Real.exp (-(((1 - R') * Real.log 2 - Real.binEntropy ρ) * n)) *
            Real.exp (n * Real.log 2) := by
          simp only [mul_assoc, ← Real.exp_add]
          congr 2
          ring
  have hd1 : Real.exp (-(2 * (ρ - p) ^ 2 * n)) ≤ Real.exp (-(min (2 * (ρ - p) ^ 2)
      ((1 - R') * Real.log 2 - Real.binEntropy ρ) * n)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left _ _) hn))
  have hd2 : Real.exp (-(((1 - R') * Real.log 2 - Real.binEntropy ρ) * n)) ≤
      Real.exp (-(min (2 * (ρ - p) ^ 2) ((1 - R') * Real.log 2 - Real.binEntropy ρ) * n)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right _ _) hn))
  linarith

open Filter Topology in
/-- **Shannon's noisy-channel coding theorem for the binary symmetric channel, achievability**,
in its asymptotic form: for `0 ≤ p < 1 / 2`, every rate `R < 1 - h₂(p)` and every `ε > 0`, for all
sufficiently large `n` some code with `2 ^ ⌈R n⌉₊` codewords of length `n` has maximal error
probability at most `ε` under every nearest-codeword decoder. -/
theorem eventually_exists_code_decodingError_le (p : I) (hp : (p : ℝ) < 1 / 2) {R : ℝ}
    (hR : R < 1 - Real.binEntropy p / Real.log 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ E : Fin (2 ^ ⌈R * n⌉₊) → BitString n, ∀ D, IsNearestDecoder E D →
      ∀ k, decodingError p E D k ≤ ε := by
  obtain ⟨δ, hδ, h⟩ := exists_pos_forall_exists_code_decodingError_le_exp p hp hR
  have hlim : Tendsto (fun n : ℕ => 10 * Real.exp (-(δ * n))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hδ)).const_mul 10
  filter_upwards [hlim.eventually (eventually_le_nhds hε)] with n hn
  obtain ⟨E, hE⟩ := h n
  exact ⟨E, fun D hD k => (hE D hD k).trans hn⟩


end Cslib.BitString
