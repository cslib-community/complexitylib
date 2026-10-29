/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Computability.Circuit.Boolean.Braverman.Resilience
import Complexity.Computability.Circuit.FanIn
import ComplexityTests.BravermanFooling

/-!
# Resilient functions under bounded independence

Both sides of the definitions of coalition influence and resilience, and clients of
[Chattopadhyay–Zuckerman, Theorem 4.1][ChattopadhyayZuckerman2019] for `OR` of the first two of
`K + 2` bits under the even-parity distribution on `K + 2` bits, which is `(K + 1)`-wise but not
`(K + 2)`-wise independent (`ComplexityTests.BravermanFooling`).

**Caveat.** The influence of a coalition `Q` under a distribution depends only on the marginal of
the distribution outside `Q` (`Cslib.BitString.isUndetermined_congr`). The marginal of the
even-parity distribution on any `K + 1` of its `K + 2` bits is uniform, so for `Q = {0}` its
influence equals the uniform influence exactly. Moreover the circuit reads only two bits, which
every distribution of independence at least two sees as uniform. These tests therefore check that
the statements apply, with nonvacuous hypotheses, to a distribution that is not uniform; they do not
exercise a case in which non-uniformity reaches the circuit, which needs a circuit reading more
bits than the (astronomical) independence.
-/

namespace ComplexityTests.BravermanResilience

open Finset Function Cslib Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean
  Cslib.Circuits.Boolean.Braverman Cslib.Probability ComplexityTests.BravermanFooling
open scoped BigOperators

/-! ### The definitions, on both sides -/

/-- Parity of three bits is undetermined everywhere by the bits other than the first. -/
theorem isUndetermined_parity₃ (x : Fin 3 → Bool) :
    IsUndetermined {0} (fun x : Fin 3 → Bool => x 0 ^^ x 1 ^^ x 2) x := by
  rw [isUndetermined_singleton_iff, update_self, update_of_ne (by decide : (1 : Fin 3) ≠ 0),
    update_of_ne (by decide : (2 : Fin 3) ≠ 0)]
  have key : ∀ a b c : Bool, (!a ^^ b ^^ c) ≠ (a ^^ b ^^ c) := by decide
  exact key _ _ _

-- Parity of three bits is not `(1, 1 / 2)`-resilient: one bit decides it.
example : ¬IsResilient 1 (1 / 2) fun x : Fin 3 → Bool => x 0 ^^ x 1 ^^ x 2 := fun h => by
  have h0 := h {0} (card_singleton 0)
  rw [coalitionInfluence_eq_one_of_forall _ isUndetermined_parity₃] at h0
  norm_num at h0

/-! ### `OR` of two bits -/

variable {K : ℕ}

/-- The one-gate circuit computing `OR` of the first two of `K + 2` bits. -/
abbrev or₂ (K : ℕ) : Circuit Unbounded.signature (K + 2) 1 :=
  Circuit.oneGate (.or 2) ![0, 1]

theorem eval_or₂ (x : Fin (K + 2) → Bool) :
    (or₂ K).eval Unbounded.interpretation x 0 = (x 0 || x 1) := by
  simp [Fin.exists_fin_two]

theorem monotone_or₂ : Monotone fun x => (or₂ K).eval Unbounded.interpretation x 0 := by
  intro x y hxy
  simp only [eval_or₂]
  have key : ∀ a b c e : Bool, a ≤ c → b ≤ e → (a || b) ≤ (c || e) := by decide
  exact key _ _ _ _ (hxy 0) (hxy 1)

theorem fanInAtMost_or₂ : (or₂ K).FanInAtMost (2 ^ 3 - 1) :=
  (Circuit.fanInAtMost_oneGate _ _ _).2 (by decide)

/-- A uniformly random bit has sign `0` on average. -/
theorem expect_signVal (k : Fin (K + 2)) : 𝔼 x : Fin (K + 2) → Bool, signVal (x k) = 0 := by
  simp only [← chi_singleton, expect_chi, singleton_ne_empty, ↓reduceIte]

/-- Two distinct uniformly random bits have uncorrelated signs. -/
theorem expect_signVal_mul_signVal :
    𝔼 x : Fin (K + 2) → Bool, signVal (x 0) * signVal (x 1) = 0 := by
  simp only [← chi_singleton, ← chi_union (disjoint_singleton.2 zero_ne_one), expect_chi,
    union_eq_empty, singleton_ne_empty, false_and, ↓reduceIte]

/-- Under the uniform distribution, `OR` of two bits is true with probability `3 / 4`. -/
theorem expect_bitVal_or₂ :
    𝔼 x : Fin (K + 2) → Bool, bitVal ℝ ((or₂ K).eval Unbounded.interpretation x 0) = 3 / 4 := by
  have h (x : Fin (K + 2) → Bool) : bitVal ℝ ((or₂ K).eval Unbounded.interpretation x 0) =
      3 / 4 - signVal (x 0) / 4 - signVal (x 1) / 4 - signVal (x 0) * signVal (x 1) / 4 := by
    rw [eval_or₂]
    cases x 0 <;> cases x 1 <;> norm_num
  simp only [h, expect_sub_distrib, ← expect_div, expect_signVal, expect_signVal_mul_signVal,
    expect_const univ_nonempty]
  norm_num

/-- A bit is `false` with probability `1 / 2`. -/
theorem expect_ite_eq_false (k : Fin (K + 2)) :
    𝔼 x : Fin (K + 2) → Bool, (if x k = false then (1 : ℝ) else 0) = 1 / 2 := by
  have h (x : Fin (K + 2) → Bool) : (if x k = false then (1 : ℝ) else 0) =
      1 / 2 + signVal (x k) / 2 := by
    cases x k <;> norm_num
  simp only [h, expect_add_distrib, ← expect_div, expect_signVal, expect_const univ_nonempty]
  norm_num

/-- **The uniform influence of the first bit on `OR` of two bits**, through the influence of
`Cslib.BitString.influence`: the first bit decides `OR` when the second is `false`. -/
theorem coalitionInfluence_or₂ :
    coalitionInfluence (Cslib.Probability.PMF.uniformOfFintype _) {0}
      (fun x => (or₂ K).eval Unbounded.interpretation x 0) = 1 / 2 := by
  rw [coalitionInfluence_singleton, influence_signVal, ← expect_ite_eq_false 1]
  refine expect_congr rfl fun x _ => ?_
  simp only [eval_or₂, update_self, update_of_ne (zero_ne_one (α := Fin (K + 2))).symm]
  cases x 0 <;> cases x 1 <;> rfl

/-- Flipping a bit other than the second changes `OR` of two bits only if the second is `false`. -/
theorem eq_false_of_isUndetermined_or₂ {j : Fin (K + 2)} (hj : j ≠ 1) {x : Fin (K + 2) → Bool}
    (h : IsUndetermined {j} (fun x => (or₂ K).eval Unbounded.interpretation x 0) x) :
    x 1 = false := by
  rw [isUndetermined_singleton_iff] at h
  simp only [eval_or₂, update_of_ne hj.symm] at h
  revert h
  cases x 1 <;> simp

/-- Flipping the second bit changes `OR` of two bits only if the first is `false`. -/
theorem eq_false_of_isUndetermined_or₂_one {x : Fin (K + 2) → Bool}
    (h : IsUndetermined {1} (fun x => (or₂ K).eval Unbounded.interpretation x 0) x) :
    x 0 = false := by
  rw [isUndetermined_singleton_iff] at h
  simp only [eval_or₂, update_of_ne (zero_ne_one (α := Fin (K + 2)))] at h
  revert h
  cases x 0 <;> simp

/-- `OR` of two bits is `(1, 1 / 2)`-resilient. -/
theorem isResilient_or₂ :
    IsResilient 1 (1 / 2) fun x => (or₂ K).eval Unbounded.interpretation x 0 := by
  intro Q hQ
  obtain ⟨j, rfl⟩ := card_eq_one.1 hQ
  rw [coalitionInfluence_uniformOfFintype]
  obtain ⟨k, hk⟩ : ∃ k : Fin (K + 2), ∀ x : Fin (K + 2) → Bool,
      IsUndetermined {j} (fun x => (or₂ K).eval Unbounded.interpretation x 0) x → x k = false := by
    by_cases hj : j = 1
    · subst hj
      exact ⟨0, fun x => eq_false_of_isUndetermined_or₂_one⟩
    · exact ⟨1, fun x => eq_false_of_isUndetermined_or₂ hj⟩
  rw [← expect_ite_eq_false k]
  refine expect_le_expect fun x _ => ?_
  split_ifs with h h'
  · exact le_rfl
  · exact absurd (hk x h) h'
  · norm_num
  · exact le_rfl

-- `OR` of two bits is not `(2, 1 / 2)`-resilient: two bits decide it.
example : ¬IsResilient 2 (1 / 2) fun x => (or₂ K).eval Unbounded.interpretation x 0 := fun h => by
  have h0 : (0 : Fin (K + 2)) ∈ ({0, 1} : Finset (Fin (K + 2))) := mem_insert_self _ _
  have h1 : (1 : Fin (K + 2)) ∈ ({0, 1} : Finset (Fin (K + 2))) :=
    mem_insert_of_mem (mem_singleton_self _)
  have hu (x : Fin (K + 2) → Bool) :
      IsUndetermined {0, 1} (fun x => (or₂ K).eval Unbounded.interpretation x 0) x := by
    rw [isUndetermined_iff_of_monotone monotone_or₂, eval_or₂, eval_or₂,
      piecewise_eq_of_mem _ _ _ h0, piecewise_eq_of_mem _ _ _ h1, piecewise_eq_of_mem _ _ _ h0,
      piecewise_eq_of_mem _ _ _ h1]
    exact ⟨rfl, rfl⟩
  have h01 := h {0, 1} (card_pair zero_ne_one)
  rw [coalitionInfluence_eq_one_of_forall _ hu] at h01
  norm_num at h01

/-! ### Theorem 4.1 of Chattopadhyay and Zuckerman -/

-- The bias part, closed form: for every `K + 1 ≥ 192 ^ 41`, `OR` of two bits is true with
-- probability within `1 / 4 + 1 / 8` of `1 / 2` under the even-parity distribution on `K + 2`
-- bits, as it is within `1 / 4` under the uniform distribution.
example (hK : 192 ^ 41 ≤ K + 1) :
    |∑ x, (evenParity (K + 2) x).toReal * bitVal ℝ ((or₂ K).eval Unbounded.interpretation x 0) -
      1 / 2| ≤ 1 / 4 + 1 / 2 ^ 3 :=
  abs_sum_bitVal_sub_half_le_of_isKWiseIndependent (d := 1) (by norm_num) _ fanInAtMost_or₂
    (by rw [Circuit.size_oneGate]; norm_num) (Circuit.depth_oneGate _ _).le
    (by rw [expect_bitVal_or₂]; norm_num) (by norm_num at hK ⊢; exact hK)
    (isKWiseIndependent_evenParity (K + 1))

-- The influence part for one coalition, sharp form: for every `K + 1 ≥ independence 4 3`, the
-- first bit has influence at most `1 / 2 + 1 / 8` on `OR` of two bits under the even-parity
-- distribution on `K + 2` bits, as it has influence `1 / 2` under the uniform distribution.
example (hK : independence 4 3 ≤ K + 1) :
    coalitionInfluence (evenParity (K + 2)) {0}
      (fun x => (or₂ K).eval Unbounded.interpretation x 0) ≤ 1 / 2 + 1 / 2 ^ 3 :=
  coalitionInfluence_le_of_independence_le (d := 1) (by norm_num) _ monotone_or₂ fanInAtMost_or₂
    (by rw [Circuit.size_oneGate]; norm_num) (Circuit.depth_oneGate _ _).le {0}
    coalitionInfluence_or₂.le hK (isKWiseIndependent_evenParity (K + 1))

/-- Resilience, closed form: for every `t ≥ 192 ^ 122`, `OR` of two bits is `t`-independent
`(1, 1 / 2 + 1 / 8)`-resilient. -/
theorem isKWiseResilient_or₂ {t : ℕ} (ht : 192 ^ 122 ≤ t) :
    IsKWiseResilient t 1 (1 / 2 + 1 / 2 ^ 3) fun x => (or₂ K).eval Unbounded.interpretation x 0 :=
  isKWiseResilient_of_isResilient (d := 1) (by norm_num) _ monotone_or₂ fanInAtMost_or₂
    (by rw [Circuit.size_oneGate]; norm_num) (Circuit.depth_oneGate _ _).le isResilient_or₂
    (by norm_num at ht ⊢; exact ht)

-- In particular under the even-parity distribution on `K + 2` bits.
example (hK : 192 ^ 122 ≤ K + 1) :
    coalitionInfluence (evenParity (K + 2)) {0}
      (fun x => (or₂ K).eval Unbounded.interpretation x 0) ≤ 1 / 2 + 1 / 2 ^ 3 :=
  isKWiseResilient_or₂ hK {0} (card_singleton 0) _ (isKWiseIndependent_evenParity (K + 1))

/-! ### Two blocks of even parity

The uniform distribution on the strings of `2 K + 2` bits whose two halves of `K + 1` bits both
have even parity is `K`-wise independent. Unlike the even-parity distribution, its marginal
outside `Q = {0}` is not uniform: it has bias one at the second half
(`bias_parityPair_second`). The circuit `or₂` still reads only two bits, so the caveat of the
module docstring applies. -/

/-- The first half of `2 K + 2` positions. -/
abbrev firstHalf (K : ℕ) : Finset (Fin (2 * K + 2)) :=
  Iio ⟨K + 1, by omega⟩

/-- The strings of `2 K + 2` bits whose two halves have even parity. -/
abbrev ParityPair (K : ℕ) : AddSubgroup (Fin (2 * K + 2) → Bool) :=
  ((parityOnAddMonoidHom (firstHalf K)).prod (parityOnAddMonoidHom (firstHalf K)ᶜ)).ker

/-- The uniform distribution on `ParityPair K`. -/
noncomputable def parityPair (K : ℕ) : PMF (Fin (2 * K + 2) → Bool) :=
  (PMF.uniformOfFintype (ParityPair K)).map Subtype.val

theorem mem_parityPair_iff {x : Fin (2 * K + 2) → Bool} :
    x ∈ ParityPair K ↔ parityOn (firstHalf K) x = false ∧ parityOn (firstHalf K)ᶜ x = false := by
  rw [AddMonoidHom.mem_ker, AddMonoidHom.prod_apply, parityOnAddMonoidHom_apply,
    parityOnAddMonoidHom_apply, Prod.mk_eq_zero]
  rfl

theorem card_firstHalf : #(firstHalf K) = K + 1 :=
  Fin.card_Iio _

theorem card_compl_firstHalf : #(firstHalf K)ᶜ = K + 1 := by
  rw [card_compl, Fintype.card_fin, card_firstHalf]
  omega

/-- The parity of a single bit set to `c` at `j`, on a set `S`. -/
theorem parityOn_single (S : Finset (Fin (2 * K + 2))) (j : Fin (2 * K + 2)) (c : Bool) :
    parityOn S (Pi.single j c) = if j ∈ S then c else false := by
  rw [parityOn_eq_sum, sum_pi_single']
  rfl

/-- Any `K` of the `2 K + 2` bits of a `ParityPair K` string can be prescribed: a free position in
each half fixes its parity. -/
theorem surjective_restrict_parityPair (T : Finset (Fin (2 * K + 2))) (hT : #T ≤ K) :
    Function.Surjective fun x : ParityPair K => T.restrict ((ParityPair K).subtype x) := by
  intro y
  obtain ⟨j₁, hj₁, hj₁T⟩ := exists_mem_notMem_of_card_lt_card (s := T) (t := firstHalf K)
    (by rw [card_firstHalf]; omega)
  obtain ⟨j₂, hj₂, hj₂T⟩ := exists_mem_notMem_of_card_lt_card (s := T) (t := (firstHalf K)ᶜ)
    (by rw [card_compl_firstHalf]; omega)
  have hj₂' : j₂ ∉ firstHalf K := mem_compl.1 hj₂
  have hj₁' : j₁ ∉ (firstHalf K)ᶜ := fun h => mem_compl.1 h hj₁
  set x₀ : Fin (2 * K + 2) → Bool := fun i => if h : i ∈ T then y ⟨i, h⟩ else false
  refine ⟨⟨x₀ + Pi.single j₁ (parityOn (firstHalf K) x₀) +
    Pi.single j₂ (parityOn (firstHalf K)ᶜ x₀), ?_⟩, ?_⟩
  · rw [mem_parityPair_iff, parityOn_add, parityOn_add, parityOn_add, parityOn_add,
      parityOn_single, parityOn_single, parityOn_single, parityOn_single, ite_eq_left hj₁,
      ite_eq_right hj₂', ite_eq_right hj₁', ite_eq_left hj₂]
    constructor
    · cases parityOn (firstHalf K) x₀ <;> rfl
    · cases parityOn (firstHalf K)ᶜ x₀ <;> rfl
  · funext ⟨i, hi⟩
    have h₁ : i ≠ j₁ := fun h => hj₁T (h ▸ hi)
    have h₂ : i ≠ j₂ := fun h => hj₂T (h ▸ hi)
    simp [x₀, hi, h₁, h₂]

/-- The distribution `parityPair K` is `K`-wise independent. -/
theorem isKWiseIndependent_parityPair (K : ℕ) : IsKWiseIndependent K (parityPair K) :=
  (isKWiseIndependentHash_of_surjective _ surjective_restrict_parityPair).isKWiseIndependent_map

/-- The distribution `parityPair K` has bias one at the second half, which avoids position `0`:
its marginal outside `{0}` is not uniform. -/
theorem bias_parityPair_second (K : ℕ) : bias (parityPair K) (firstHalf K)ᶜ = 1 := by
  have h (x : ParityPair K) : parityOn (firstHalf K)ᶜ (x : Fin (2 * K + 2) → Bool) = false :=
    (mem_parityPair_iff.1 x.2).2
  rw [parityPair, bias_uniformOfFintype_map]
  simp only [chi_eq_signVal_parityOn, h, signVal_false]
  exact Fintype.expect_const 1

-- For every `K ≥ 192 ^ 122`, the first bit has influence at most `1 / 2 + 1 / 8` on `OR` of two
-- bits under `parityPair K`.
example (hK : 192 ^ 122 ≤ K) :
    coalitionInfluence (parityPair K) {0}
      (fun x => (or₂ (2 * K)).eval Unbounded.interpretation x 0) ≤ 1 / 2 + 1 / 2 ^ 3 :=
  isKWiseResilient_or₂ hK {0} (card_singleton 0) _ (isKWiseIndependent_parityPair K)

end ComplexityTests.BravermanResilience
