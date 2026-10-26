/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.OneWay
public import Complexity.Crypto.Computational.PseudorandomGenerator
public import Complexity.Crypto.Negligible.Basic
import Complexity.Crypto.Computational.OneWayToPRG
import Complexity.Crypto.Computational.Stretch
import Complexity.Foundations.Data.BitString.ShortWords
import Complexity.Tactic.PolyTime
import Complexity.Tactic.PPT

/-!
# One-way functions from pseudorandom generators

An inverter for a generator `G` gives a test: on a word `y`, run the inverter and accept when
it returns a preimage of `y` (`PRGToOneWay.test`). On a generated word this test succeeds exactly
as often as the inverter wins the inversion game. On a uniform word of length `ℓ n` it can only
accept words in the image of `G` restricted to the seeds whose image has length `ℓ n`, so it
accepts with probability at most the number of those seeds divided by `2 ^ ℓ n`
(`PRGToOneWay.succProbability_uniformList_test_le`). When this fraction is negligible the
generator is therefore one-way (`PseudorandomGenerator.oneWay_of_card_le`).

When `ℓ n ≥ 2 n`, every such seed has length at most `ℓ n - n`, which gives the fraction
`2 ^ (1 - n)`, so every length-doubling generator is one-way (`PseudorandomGenerator.oneWay`).
The same holds when `ℓ` is injective and `2 ^ (n - ℓ n)` is negligible
(`PseudorandomGenerator.oneWay_of_injective`). A generator of arbitrary stretch is first truncated
to one bit of stretch and then amplified to stretch `n ↦ 2 n + 1`, so every pseudorandom generator
yields a one-way function (`PseudorandomGenerator.exists_oneWay`). With the converse
`OneWay.exists_pseudorandomGenerator` this shows that one-way functions exist if and only if
pseudorandom generators exist [HILL1999] (`exists_oneWay_iff_exists_pseudorandomGenerator`).

## Main definitions

* `Cslib.Crypto.PRGToOneWay.test`: the test accepting the words an inverter inverts.

## Main results

* `Cslib.Crypto.PseudorandomGenerator.oneWay_of_card_le`: a generator whose possible preimages of
  length-`ℓ n` words form a negligible fraction of `2 ^ ℓ n` is one-way.
* `Cslib.Crypto.PseudorandomGenerator.oneWay`: a pseudorandom generator with `2 n ≤ ℓ n` is
  one-way.
* `Cslib.Crypto.PseudorandomGenerator.oneWay_of_injective`: so is one with injective `ℓ` and
  negligible `2 ^ (n - ℓ n)`.
* `Cslib.Crypto.PseudorandomGenerator.exists_oneWay`: every pseudorandom generator yields a
  one-way function.
* `Cslib.Crypto.exists_oneWay_iff_exists_pseudorandomGenerator`: one-way functions exist if and
  only if pseudorandom generators exist.

## References

* [J. Håstad, R. Impagliazzo, L. Levin, M. Luby,
  *A Pseudorandom Generator from Any One-Way Function*][HILL1999]
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM Finset
open scoped NNReal ENNReal

namespace PRGToOneWay

/-- The test built from an inverter: on a word `y`, run the inverter and accept when it returns a
preimage of `y` under the generator. -/
def test (generator : List Bool → List Bool) (adversary : Inverter) :
    Distinguisher := fun n word => do
  let preimage ← adversary n word
  return generator preimage == word

/-- The test is PPT when the generator is polynomial time and the inverter is PPT. -/
@[program_certificate]
theorem isPPT_test {generator : List Bool → List Bool} {adversary : Inverter}
    (hgenerator : ComputableInPolyTime generator encBits encBits)
    (hadversary : IsPPT encBits adversary) :
    IsPPT encBool (test generator adversary) := by
  unfold test
  ppt

/-- On generated words the test is exactly the inversion game. -/
theorem inversionGame_eq_prgRealGame (generator : List Bool → List Bool) (adversary : Inverter)
    (n : ℕ) :
    inversionGame generator adversary n = prgRealGame generator (test generator adversary) n :=
  rfl

/-- **The ideal game.** If every word whose image has length `ℓ n` lies in a finite set `P` with
`|P| ≤ ε 2 ^ ℓ n`, the test accepts a uniform word of length `ℓ n` with probability at most `ε`:
it can only accept words of `G '' P`. -/
theorem succProbability_uniformList_test_le {generator : List Bool → List Bool} {ℓ : ℕ → ℕ}
    (hlen : ∀ word, (generator word).length = ℓ word.length) (adversary : Inverter) (n : ℕ)
    (P : Finset (List Bool)) (hP : ∀ x : List Bool, ℓ x.length = ℓ n → x ∈ P) (ε : ℝ≥0)
    (hε : (#P : ℝ≥0) ≤ ε * 2 ^ ℓ n) :
    Game.succProbability
      (distinguishingGame (BitString.uniformList (ℓ n)) (test generator adversary n)) ≤ ε := by
  classical
  set T := P.image generator
  have hle (r : Fin (ℓ n) → Bool) :
      ProbComp.eval (test generator adversary n (List.ofFn r)) true ≤
        if List.ofFn r ∈ T then 1 else 0 := by
    split_ifs with hr
    · exact PMF.coe_le_one _ _
    simp only [test, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_apply, PMF.pure_apply]
    refine le_of_eq (ENNReal.tsum_eq_zero.2 fun x => ?_)
    have hne : generator x ≠ List.ofFn r := fun hx => hr <| mem_image.2
      ⟨x, hP x (by rw [← hlen x, hx, List.length_ofFn]), hx⟩
    simp [hne]
  have hgame : distinguishingGame (BitString.uniformList (ℓ n)) (test generator adversary n) true ≤
      ((2 : ℝ≥0∞) ^ ℓ n)⁻¹ * (#T : ℝ≥0∞) := by
    rw [distinguishingGame, PMF.monad_bind_eq_bind, BitString.uniformList, PMF.bind_map,
      PMF.bind_apply, tsum_fintype]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Function.comp_apply]
    push_cast
    calc ∑ r : Fin (ℓ n) → Bool, ((2 : ℝ≥0∞) ^ ℓ n)⁻¹ *
          ProbComp.eval (test generator adversary n (List.ofFn r)) true
        ≤ ∑ r : Fin (ℓ n) → Bool, ((2 : ℝ≥0∞) ^ ℓ n)⁻¹ * (if List.ofFn r ∈ T then 1 else 0) :=
          sum_le_sum fun r _ => by gcongr; exact hle r
      _ = ((2 : ℝ≥0∞) ^ ℓ n)⁻¹ * (#{r : Fin (ℓ n) → Bool | List.ofFn r ∈ T} : ℝ≥0∞) := by
          rw [← mul_sum, sum_boole]
      _ ≤ ((2 : ℝ≥0∞) ^ ℓ n)⁻¹ * (#T : ℝ≥0∞) := by
          gcongr
          exact card_le_card_of_injOn List.ofFn (fun r hr => by simpa using hr)
            fun r _ s _ h => List.ofFn_injective h
  have hT : (#T : ℝ≥0) ≤ ε * 2 ^ ℓ n :=
    (by exact_mod_cast card_image_le : (#T : ℝ≥0) ≤ #P).trans hε
  have hfin : distinguishingGame (BitString.uniformList (ℓ n)) (test generator adversary n) true ≤
      (ε : ℝ≥0∞) := by
    refine hgame.trans ?_
    rw [ENNReal.inv_mul_le_iff (by positivity) (by simp), mul_comm]
    exact_mod_cast hT
  exact (ENNReal.toNNReal_mono ENNReal.coe_ne_top hfin).trans_eq (ENNReal.toNNReal_coe _)

end PRGToOneWay

open PRGToOneWay

/-- A pseudorandom generator is one-way when, for a negligible `ε`, the words whose image has
length `ℓ n` lie in a set of at most `ε n 2 ^ ℓ n` words: an inverter succeeding on generated
words would give a test accepting generated words much more often than uniform ones. -/
theorem PseudorandomGenerator.oneWay_of_card_le {generator : List Bool → List Bool} {ℓ : ℕ → ℕ}
    (hgenerator : PseudorandomGenerator generator ℓ) {ε : ℕ → ℝ≥0} (hε : Negligible ε)
    (P : ℕ → Finset (List Bool)) (hP : ∀ n (x : List Bool), ℓ x.length = ℓ n → x ∈ P n)
    (hcard : ∀ n, (#(P n) : ℝ≥0) ≤ ε n * 2 ^ ℓ n) : OneWay generator := by
  refine OneWay.of_inversion_negligible hgenerator.polyTime fun adversary hadversary => ?_
  have hind := hgenerator.indistinguishable (test generator adversary)
    (isPPT_test hgenerator.polyTime hadversary)
  refine negligible_of_le (hind.add_fun hε) fun n => ?_
  rw [inversionGame_eq_prgRealGame, eval_prgRealGame]
  exact ((NNReal.le_add_nndist _ _).trans_eq (add_comm _ _)).trans <| by
    gcongr
    exact succProbability_uniformList_test_le hgenerator.length_eq adversary n (P n) (hP n)
      (ε n) (hcard n)

/-- **Length-doubling pseudorandom generators are one-way.** If `2 n ≤ ℓ n` for all `n`, a
pseudorandom generator with output length `ℓ` is a one-way function: the seeds whose image has
length `ℓ n` have length at most `ℓ n - n`, so a uniform word of length `ℓ n` is in the image with
probability at most `2 ^ (1 - n)`. -/
theorem PseudorandomGenerator.oneWay {generator : List Bool → List Bool} {ℓ : ℕ → ℕ}
    (hgenerator : PseudorandomGenerator generator ℓ) (hℓ : ∀ n, 2 * n ≤ ℓ n) :
    OneWay generator := by
  have hε : Negligible fun n => (1 / 2 : ℝ≥0) ^ n + (1 / 2) ^ n :=
    (negligible_geometric (by norm_num)).add (negligible_geometric (by norm_num))
  refine hgenerator.oneWay_of_card_le hε
    (fun n => BitString.shortWords (ℓ n - n)) (fun n x hx => BitString.mem_shortWords.2 ?_)
    fun n => ?_
  · have := hℓ x.length
    have := hℓ n
    omega
  · have h : ((1 / 2 : ℝ≥0) ^ n + (1 / 2) ^ n) * 2 ^ ℓ n = 2 ^ (ℓ n - n + 1) := by
      obtain ⟨k, hk⟩ : ∃ k, ℓ n = k + n := ⟨ℓ n - n, by have := hℓ n; omega⟩
      rw [hk, Nat.add_sub_cancel, pow_add, pow_succ, one_div_pow]
      field_simp
      ring
    rw [h]
    exact_mod_cast (BitString.card_shortWords_lt _).le

/-- A pseudorandom generator whose output length `ℓ` is injective and whose gap `2 ^ (n - ℓ n)` is
negligible is one-way: the seeds whose image has length `ℓ n` are then exactly those of length
`n`. This covers stretches such as `ℓ n = n + (Nat.log 2 n + 1) ^ 2`, which is strictly
increasing and eventually below `2 n`. -/
theorem PseudorandomGenerator.oneWay_of_injective {generator : List Bool → List Bool}
    {ℓ : ℕ → ℕ} (hgenerator : PseudorandomGenerator generator ℓ) (hinj : Function.Injective ℓ)
    (hgap : Negligible fun n => (1 / 2 : ℝ≥0) ^ (ℓ n - n)) : OneWay generator := by
  classical
  refine hgenerator.oneWay_of_card_le hgap
    (fun n => univ.image (List.ofFn : (Fin n → Bool) → _)) (fun n x hx => ?_) fun n => ?_
  · obtain rfl : x.length = n := hinj hx
    exact mem_image.2 ⟨x.get, mem_univ _, List.ofFn_get x⟩
  · have h : (1 / 2 : ℝ≥0) ^ (ℓ n - n) * 2 ^ ℓ n = 2 ^ n := by
      obtain ⟨k, hk⟩ : ∃ k, ℓ n = k + n := ⟨ℓ n - n, by have := hgenerator.stretch n; omega⟩
      rw [hk, Nat.add_sub_cancel, pow_add, one_div_pow]
      field_simp
    rw [h]
    exact_mod_cast card_image_le.trans (by simp)

/-- **Every pseudorandom generator yields a one-way function.** Truncate the generator to one bit
of stretch, amplify it to stretch `n ↦ 2 n + 1`, and apply `PseudorandomGenerator.oneWay`. -/
theorem PseudorandomGenerator.exists_oneWay {generator : List Bool → List Bool} {ℓ : ℕ → ℕ}
    (hgenerator : PseudorandomGenerator generator ℓ) : ∃ f : List Bool → List Bool, OneWay f := by
  have h1 := hgenerator.truncate (fun n => n + 1) (by polytime) hgenerator.stretch
    fun n => Nat.lt_succ_self n
  have h2 := h1.amplify (fun n => 2 * n + 1) (by polytime) fun n => by omega
  exact ⟨_, h2.oneWay fun n => by omega⟩

/-- **One-way functions exist if and only if pseudorandom generators exist** [HILL1999]. The
forward direction is `OneWay.exists_pseudorandomGenerator`, the converse
`PseudorandomGenerator.exists_oneWay`. -/
theorem exists_oneWay_iff_exists_pseudorandomGenerator :
    (∃ f : List Bool → List Bool, OneWay f) ↔
      ∃ (generator : List Bool → List Bool) (ℓ : ℕ → ℕ), PseudorandomGenerator generator ℓ :=
  ⟨fun ⟨_, hf⟩ => let ⟨generator, hgenerator⟩ := hf.exists_pseudorandomGenerator
    ⟨generator, _, hgenerator⟩,
   fun ⟨_, _, hgenerator⟩ => hgenerator.exists_oneWay⟩

end Cslib.Crypto
