/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Computability.Circuit.Boolean.Braverman.Fooling
import Complexity.Computability.Circuit.Pi
import Complexity.Foundations.BooleanAnalysis.FourierBitVal
import Complexity.Probability.PMF.Expect

/-!
# Polylogarithmic independence fools AC⁰

Concrete clients of Braverman's theorem under a distribution that is not uniform: the uniform
distribution on the strings of `K + 1` bits with even parity, a sample of which is `K` uniform bits
followed by their parity. It is `K`-wise but not `(K + 1)`-wise independent. The tests apply the
witness form of the one-sided argument with a nontrivial witness, Fourier truncation of a single
bit, and both forms of Braverman's theorem to `AND` of three bits, for every `K` at least the
required independence. The even-parity distribution is shared with the tests of the Braverman
abstract.
-/

namespace ComplexityTests.BravermanFooling

open Finset Cslib Cslib.BitString Cslib.Probability Cslib.Circuits Cslib.Circuits.Boolean
  Cslib.Circuits.Boolean.Braverman
open scoped BigOperators

/-! ### The even-parity distribution -/

/-- The strings of even parity: the kernel of the parity of all bits. -/
abbrev EvenParity (n : ℕ) : AddSubgroup (Fin n → Bool) :=
  (parityOnAddMonoidHom univ).ker

/-- The uniform distribution on the strings of `n` bits with even parity. -/
noncomputable def evenParity (n : ℕ) : PMF (Fin n → Bool) :=
  (PMF.uniformOfFintype (EvenParity n)).map Subtype.val

/-- Any `K` of the `K + 1` bits of an even-parity string can be prescribed: a coordinate outside
them fixes the parity. -/
theorem surjective_restrict_evenParity {K : ℕ} (T : Finset (Fin (K + 1))) (hT : #T ≤ K) :
    Function.Surjective fun x : EvenParity (K + 1) =>
      T.restrict ((EvenParity (K + 1)).subtype x) := by
  intro y
  obtain ⟨j, -, hj⟩ := exists_mem_notMem_of_card_lt_card (s := T) (t := univ)
    (by rw [card_univ, Fintype.card_fin]; omega)
  set x₀ : Fin (K + 1) → Bool := fun i => if h : i ∈ T then y ⟨i, h⟩ else false
  refine ⟨⟨x₀ + Pi.single j (parityOn univ x₀), ?_⟩, ?_⟩
  · rw [AddMonoidHom.mem_ker, parityOnAddMonoidHom_apply, parityOn_add,
      parityOn_eq_sum univ (Pi.single _ _), sum_pi_single', ite_eq_left (mem_univ j)]
    cases parityOn univ x₀ <;> rfl
  · funext ⟨i, hi⟩
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    simp [x₀, hi, hij]

/-- The values of a uniformly random even-parity string at any `K` of its `K + 1` positions are
independent and uniform. -/
theorem isKWiseIndependentHash_evenParity (K : ℕ) :
    IsKWiseIndependentHash K fun x : EvenParity (K + 1) => (EvenParity (K + 1)).subtype x :=
  isKWiseIndependentHash_of_surjective _ surjective_restrict_evenParity

/-- The even-parity distribution on `K + 1` bits is `K`-wise independent. -/
theorem isKWiseIndependent_evenParity (K : ℕ) : IsKWiseIndependent K (evenParity (K + 1)) :=
  (isKWiseIndependentHash_evenParity K).isKWiseIndependent_map

/-- The even-parity distribution has bias one at the set of all positions. -/
theorem bias_evenParity_univ (n : ℕ) : bias (evenParity n) univ = 1 := by
  have h (x : EvenParity n) : parityOn univ (x : Fin n → Bool) = false := AddMonoidHom.mem_ker.1 x.2
  rw [evenParity, bias_uniformOfFintype_map]
  simp only [chi_eq_signVal_parityOn, h, signVal_false]
  exact Fintype.expect_const 1

/-- The even-parity distribution on `K + 1` bits is not `(K + 1)`-wise independent. -/
theorem not_isKWiseIndependent_evenParity (K : ℕ) :
    ¬IsKWiseIndependent (K + 1) (evenParity (K + 1)) := fun h => by
  have h' := h univ univ_nonempty (by rw [card_univ, Fintype.card_fin])
  rw [bias_evenParity_univ, abs_one] at h'
  exact absurd h' (by norm_num)

/-! ### Clients -/

/-- The first three of seven positions. -/
private abbrev T₃ : Finset (Fin 7) := {0, 1, 2}

/-- `AND` of the first three of seven bits, through its monomial. -/
private theorem bitVal_and₃ (x : Fin 7 → Bool) :
    bitVal ℝ (x 0 && x 1 && x 2) = monomial ℝ T₃ x := by
  rw [monomial_apply]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> simp [h0, h1, h2]

/-- Under the `6`-wise independent even-parity distribution on seven bits, as under the uniform
distribution, the first three bits are all true with probability `1 / 8`. -/
private theorem sum_evenParity_mul_monomial :
    ∑ x, (evenParity 7 x).toReal * monomial ℝ T₃ x = 1 / 8 := by
  rw [evenParity, Cslib.Probability.PMF.sum_map_mul]
  have h := (isKWiseIndependentHash_evenParity 6).expect_prod (T := T₃) (by decide)
    fun _ b => bitVal ℝ b
  rw [Fintype.expect_eq_sum_div_card, sum_div] at h
  simp only [Fintype.expect_bool, bitVal, prod_const] at h
  simp only [Cslib.Probability.PMF.uniformOfFintype_apply, monomial]
  convert h using 1
  · refine sum_congr rfl fun s _ => ?_
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, inv_mul_eq_div]
    rfl
  · norm_num

-- The witness form of Braverman's argument with a nontrivial witness, under the `6`-wise
-- independent even-parity distribution on seven bits: `AND` of the first four bits is
-- approximated by `0` off the witness `E = x₀ ∧ x₁ ∧ x₂`, which has probability `1 / 8` and is
-- exactly a monomial of degree `3`. The error is `4 / 8 + 2 (0 + 1)² · 0 = 1 / 2`.
example : Fools (evenParity 7) (4 * (1 / 8) + 2 * (0 + 1) ^ 2 * 0)
    fun x => bitVal ℝ (x 0 && x 1 && x 2 && x 3) := by
  have hX := isKWiseIndependent_evenParity 6
  have hU : 𝔼 x : Fin 7 → Bool, monomial ℝ T₃ x = 1 / 8 := by
    rw [← hX.sum_mul_eq_expect_of_mem_lowDegree (monomial_mem_lowDegree (by decide))]
    exact sum_evenParity_mul_monomial
  refine hX.fools_bitVal_of_witness (E := fun x => x 0 && x 1 && x 2) (f := fun _ => 0)
    (e := monomial ℝ T₃) (D := 0) (t := 3) (const_mem_lowDegree 0 0)
    (monomial_mem_lowDegree (by decide)) (by norm_num) (fun x hx => ?_) (fun _ => by simp)
    ?_ ?_ ?_
  · simp [hx]
  · simp only [bitVal_and₃]
    exact sum_evenParity_mul_monomial.le
  · simp only [bitVal_and₃]
    exact hU.le
  · simp only [bitVal_and₃, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.expect_const_zero, le_refl]

-- Fourier truncation of the first bit at level `0` leaves its weight above level `0`.
example : ∃ g ∈ lowDegree ℝ (Fin 3) 0, 𝔼 x : Fin 3 → Bool, (bitVal ℝ (x 0) - g x) ^ 2 =
    (∑ S with 0 < #S, fourierCoeff (fun x : Fin 3 → Bool => signVal (x 0)) S ^ 2) / 4 :=
  exists_mem_lowDegree_expect_sq_bitVal_sub_eq (fun x => x 0) 0

/-- The one-gate circuit computing `AND` of the first three of `n ≥ 3` bits. -/
abbrev and3 {n : ℕ} (h : 3 ≤ n) : Circuit Unbounded.signature n 1 :=
  Circuit.oneGate (.and 3) (Fin.castLE h)

/-- `AND` of three bits has fan-in `3`. -/
theorem and3_fanInAtMost {n : ℕ} (h : 3 ≤ n) : (and3 h).FanInAtMost (2 ^ 2 - 1) :=
  ⟨trivial, le_rfl⟩

-- Braverman's theorem for `AND` of the first three of `K + 1` bits, with `q = 2` and depth `1`:
-- for every `K ≥ 128 ^ 41`, the even-parity distribution on `K + 1` bits, which is `K`-wise but
-- not `(K + 1)`-wise independent, `1 / 4`-fools it.
example (K : ℕ) (hK : 128 ^ 41 ≤ K) :
    Fools (evenParity (K + 1)) (1 / 2 ^ 2) fun x =>
      bitVal ℝ ((and3 (Nat.succ_le_succ ((by norm_num : 2 ≤ 128 ^ 41).trans hK))).eval
        Unbounded.interpretation x 0) :=
  fools_of_isKWiseIndependent (d := 1) (q := 2) (by norm_num) _ (and3_fanInAtMost _)
    (by rw [Circuit.size_oneGate]; norm_num) (Circuit.depth_oneGate _ _).le
    (by norm_num at hK ⊢; exact hK) (isKWiseIndependent_evenParity K)

-- The sharp form: `independence 1 2`-wise independence suffices.
example (K : ℕ) (hK : independence 1 2 ≤ K) :
    Fools (evenParity (K + 1)) (1 / 2 ^ 2) fun x =>
      bitVal ℝ ((and3 (Nat.succ_le_succ
        ((by norm_num [independence, level] : 2 ≤ independence 1 2).trans hK))).eval
        Unbounded.interpretation x 0) :=
  fools_of_independence_le (d := 1) (q := 2) (by norm_num) _ (and3_fanInAtMost _)
    (by rw [Circuit.size_oneGate]; norm_num) (Circuit.depth_oneGate _ _).le hK
    (isKWiseIndependent_evenParity K)

end ComplexityTests.BravermanFooling
