/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.WeightedThreshold.SharedBottom
public import Complexity.Foundations.Data.BitString.Parity
public import Complexity.Foundations.Data.BitString.Threshold
public import Complexity.Probability.SmallBias
import Complexity.Foundations.Data.BitString.Discriminator
import Complexity.Probability.SmallBias.Correlation
import Complexity.Probability.SmallBias.Powering

/-!
# The Kane–Williams depth-three function: gate, wire and correlation bounds

Kane and Williams ([KaneWilliams2016], `arXiv:1511.07860v1`, Section 6) replace the multiplexer in
Andreev's function by a code with small bias. The `n + k * ℓ` inputs are a message
`x ∈ {0,1}^n` and `k` blocks of `ℓ` bits; with `z ∈ {0,1}^k` the block parities and rows
`r : BitString k → BitString n`, the value is `B(x, a) = ⟨r_z, x⟩` (`kaneWilliamsB`,
[KaneWilliams2016], Definition 6.1, whose rows form a small-bias set as in their Proposition 2
and Corollary 6.1). For `δ`-biased rows, at most `1 / (γ ^ 2 - δ)` messages have a word
`z ↦ ⟨r_z, x⟩` with correlation `γ` with any fixed word
(`Cslib.BitString.card_le_abs_sum_signVal_mul_signVal_dotProduct_mul_le`, an explicit form of
[KaneWilliams2016], Lemma 6.1).

## Headline bounds

Take, as Kane and Williams do, a message of `n` bits and `n` block bits, here `k = 16 p` blocks of
`ℓ` bits with `n = 16 p ℓ ≤ 2 ^ p` (they take `k = 16 log₂ n`), and `2 ^ (-7 p)`-biased rows, which
the powering construction provides (`exists_isSmallBias_kaneWilliamsRows`). Let
`R = 272 p ^ 2 + 54 p + 3` and `R' = 272 p ^ 2 + 57 p + 3`.

* **Worst case** (`size_ge_of_threshold_eval_eq_kaneWilliamsB_balanced`,
  `wireCount_ge_of_threshold_eval_eq_kaneWilliamsB_balanced`): if an unweighted threshold gate of
  fan-in `t ≤ n ^ 3 / 4` over the outputs of a depth-two weighted threshold circuit `c` computes
  the function, then `n (n - R) ≤ 4864 p ^ 2 * c.size * √(2 n)` and
  `n √n (n - R) ≤ 19456 p ^ 2 √p * c.wireCount`.
* **Average case** (`card_eval_eq_kaneWilliamsB_le_balanced_size`,
  `card_eval_eq_kaneWilliamsB_le_balanced_wireCount`): if `n > R'`, a depth-two weighted
  threshold circuit `c` agrees with the function on at most a
  `1 / 2 + 2 ^ (-3 p) + 2432 p ^ 2 * c.size * √(2 n) / (n (n - R'))`, respectively
  `1 / 2 + 2 ^ (-3 p) + 9728 p ^ 2 √p * c.wireCount / (n √n (n - R'))`, fraction of the inputs.

For `p ≥ 9` and `ℓ = ⌊2 ^ p / (16 p)⌋`, `2 ^ (p - 1) < n ≤ 2 ^ p`, so `p = ⌈log₂ n⌉`. The bounds
then say that `MAJ ∘ THR ∘ THR` circuits computing the function need `Ω(n ^ (3 / 2) / log² n)` gates
and `Ω(n ^ (5 / 2) / log^(5/2) n)` wires, one logarithmic factor more than the
`Ω(n ^ (3 / 2) / log³ n)` gates and `Ω(n ^ (5 / 2) / log^(7/2) n)` wires of [KaneWilliams2016],
Theorem 1.3, and that a depth-two circuit with `s` gates agrees with the function on at most a
`1 / 2 + O(s log² n / n ^ (3 / 2)) + n ^ (-3)` fraction of the inputs. Kane and Williams state no
average-case bound for this function. These improvements are original. All endpoints are explicit
finite inequalities, not formal asymptotic statements.

## The argument

Kane and Williams first fix a message that is bad for *all* small depth-two circuits
([KaneWilliams2016], Corollary 6.2), counting arbitrary threshold circuits at `Θ(k ^ 2)` bits per
bottom gate. Here the circuit is fixed first; this change of quantifiers and its consequences below
are original. A block restriction `(σ, w)` leaves one live input per block, keeps the message `x`
of `w`, and shifts the block parities by the residual parities `c`, so the restricted function is
`u ↦ ⟨r_{u + c}, x⟩` (`kaneWilliamsB_embedUpdate`). The restricted circuit lies in
`IsDepthTwoOverWeights (W σ) q`, where the weight vectors `W σ` depend only on the circuit and
`σ`, and `q` counts the surviving bottom gates. For `q ≤ Q` and `#(W σ) < M`, these classes and the
`2 ^ k` translations number at most
`C = ℓ ^ k * 2 ^ k * ((2 ^ k + 1) * M) ^ Q * (2 ^ k + 1) ^ (Q + k + 1)`, that is
`O(Q (k + log M) + k ^ 2)` bits, so at most `C / (γ ^ 2 - δ)` messages are bad for the circuit.
The expected number of survivors is at most `4 (1 / ℓ) c.size √(n + k ℓ)` or
`4 c.wireCount (1 / ℓ) √(1 / ℓ)` (the repaired restriction lemmas, [KaneWilliams2016], Lemmas 1.1
and 3.1), and Markov's inequality bounds the restrictions with more than `Q` survivors.

* **Average case**: a depth-two circuit agrees with `B` on at most a
  `(1 + γ) / 2 + C / ((γ ^ 2 - δ) 2 ^ n) + (expected survivors) / (Q + 1)` fraction of the inputs
  (`card_eval_eq_kaneWilliamsB_le_of_depth_le_two_size`,
  `card_eval_eq_kaneWilliamsB_le_of_depth_le_two_wireCount`).
* **Worst case**: let the `t` outputs of a depth-two circuit, sharing their bottom gates, feed an
  unweighted threshold gate `threshold t θ` (for instance majority) that computes `B`. On a
  restriction with a good message and at most `Q` survivors, every output has correlation below
  `γ`, while the discriminator lemma (`Cslib.sub_le_sum_sum_signVal_mul_of_threshold_eq`) needs
  a total correlation of `1 - (t + 1) δ`. Hence
  `1 ≤ C / ((γ ^ 2 - δ) 2 ^ n) + (expected survivors) / (Q + 1)` whenever
  `t γ + (t + 1) δ < 1` (`one_le_of_threshold_eval_eq_kaneWilliamsB_size`,
  `one_le_of_threshold_eval_eq_kaneWilliamsB_wireCount`).

With `k = 16 p`, `γ = 2 ^ (-3 p)`, `δ = 2 ^ (-7 p)` and `n, ℓ ≤ 2 ^ p`, the largest `Q` with
`(36 p + 2) Q + R ≤ n` makes the counting term at most `1 / 2`. This gives, for any block length
`ℓ`, `ℓ (n - R) ≤ 304 p * c.size * √(n + 16 p ℓ)` and `ℓ √ℓ (n - R) ≤ 304 p * c.wireCount` for top
fan-in `t ≤ 2 ^ (3 p) / 4` (`size_ge_of_threshold_eval_eq_kaneWilliamsB_of_le_two_pow`,
`wireCount_ge_of_threshold_eval_eq_kaneWilliamsB_of_le_two_pow`), and agreement at most
`1 / 2 + 2 ^ (-3 p) + 152 p * c.size * √(n + 16 p ℓ) / (ℓ (n - R'))`, respectively
`1 / 2 + 2 ^ (-3 p) + 152 p * c.wireCount / (ℓ √ℓ (n - R'))`
(`card_eval_eq_kaneWilliamsB_le_of_le_two_pow_size`,
`card_eval_eq_kaneWilliamsB_le_of_le_two_pow_wireCount`). The balanced bounds above are the case
`n = 16 p ℓ`.

## Model and limitations

A `MAJ ∘ THR ∘ THR` circuit is modeled as a depth-two weighted threshold circuit
`c : Circuit signature N t` together with an unweighted threshold gate `threshold t θ` over its
`t` outputs; it has `c.size + 1` gates and `c.wireCount + t` wires, and the bounds count only
`c.size` and `c.wireCount`. The outputs share their bottom gates; an output may be an input wire,
and outputs may repeat, so `t` counts the top gate's wires with multiplicity. The top gate must be
unweighted, and its fan-in enters the hypotheses: `t ≤ n ^ 3 / 4` in the balanced bounds. In the
`MAJ ∘ THR ∘ THR` circuits of [KaneWilliams2016], Theorem 1.3, the fan-in of the top gate is at
most the number of gates. The bounds hold for every list of `δ`-biased rows. The powering rows
exist for all parameters, but neither they nor the function are certified here to be computable in
polynomial time, as Kane and Williams state for their construction.

## Main definitions

* `Cslib.Circuits.Boolean.kaneWilliamsB`: the Kane–Williams function, with its input layout
  `Cslib.Circuits.Boolean.kaneWilliamsMessage` and `Cslib.Circuits.Boolean.kaneWilliamsParities`.
* `WeightedThreshold.kaneWilliamsLiveVar`, `WeightedThreshold.kaneWilliamsResidualParities`:
  block restrictions.

## Main results

* `WeightedThreshold.size_ge_of_threshold_eval_eq_kaneWilliamsB_balanced`,
  `WeightedThreshold.wireCount_ge_of_threshold_eval_eq_kaneWilliamsB_balanced`: the worst-case
  gate and wire bounds for `n = 16 p ℓ`.
* `WeightedThreshold.card_eval_eq_kaneWilliamsB_le_balanced_size`,
  `WeightedThreshold.card_eval_eq_kaneWilliamsB_le_balanced_wireCount`: the average-case bounds
  for `n = 16 p ℓ`.
* `WeightedThreshold.size_ge_of_threshold_eval_eq_kaneWilliamsB_of_le_two_pow`,
  `WeightedThreshold.card_eval_eq_kaneWilliamsB_le_of_le_two_pow_size` and their wire versions:
  the same bounds for any block length `ℓ ≤ 2 ^ p`.
* `WeightedThreshold.card_eval_eq_kaneWilliamsB_le_of_depth_le_two_size`,
  `WeightedThreshold.one_le_of_threshold_eval_eq_kaneWilliamsB_size` and their `wireCount`
  versions: bounds for all parameters, with a free survivor budget `Q`.
* `WeightedThreshold.card_eval_eq_kaneWilliamsB_le_of_unforced_mean_le`,
  `WeightedThreshold.one_le_of_threshold_eq_kaneWilliamsB_of_unforced_mean_le`: the average-case
  and worst-case cores, for functions that collapse under block restrictions.
* `WeightedThreshold.kaneWilliamsB_embedUpdate`: the restricted function.
* `WeightedThreshold.exists_isSmallBias_kaneWilliamsRows`: rows exist.

## References

* [D. M. Kane and R. Williams, *Super-Linear Gate and Super-Quadratic Wire Lower Bounds for
  Depth-Two and Depth-Three Threshold Circuits*][KaneWilliams2016], `arXiv:1511.07860v1`,
  Theorem 1.3, Lemmas 1.1 and 3.1, and Section 6: Proposition 2, Corollaries 6.1 and 6.2,
  Lemma 6.1 and Definition 6.1
* [N. Alon, O. Goldreich, J. Håstad, R. Peralta, *Simple constructions of almost `k`-wise
  independent random variables*][AlonGoldreichHastadPeralta1992]
* [A. Hajnal, W. Maass, P. Pudlák, M. Szegedy, G. Turán, *Threshold circuits of bounded
  depth*][HMPST1993]
-/
public section

namespace Cslib.Circuits.Boolean

open BitString Finset

/-! ### The function and its input layout -/

/-- The `i`-th message coordinate among the `n + k * ℓ` inputs of the Kane–Williams function. -/
@[expose] def kaneWilliamsMessageIndex (n k ℓ : ℕ) (i : Fin n) : Fin (n + k * ℓ) :=
  Fin.castAdd (k * ℓ) i

/-- The `t`-th variable of the `j`-th parity block among the `n + k * ℓ` inputs of the
Kane–Williams function. -/
@[expose] def kaneWilliamsBlockVar (n k ℓ : ℕ) (j : Fin k) (t : Fin ℓ) : Fin (n + k * ℓ) :=
  Fin.natAdd n (finProdFinEquiv (j, t))

/-- The message `x`: the first `n` of the `n + k * ℓ` inputs. -/
@[expose] def kaneWilliamsMessage (n k ℓ : ℕ) (y : BitString (n + k * ℓ)) : BitString n :=
  fun i => y (kaneWilliamsMessageIndex n k ℓ i)

/-- The block parities `z`: the parities of the `k` blocks of `ℓ` inputs after the message. -/
@[expose] def kaneWilliamsParities (n k ℓ : ℕ) (y : BitString (n + k * ℓ)) : BitString k :=
  fun j => parity ℓ fun t => y (kaneWilliamsBlockVar n k ℓ j t)

/-- **The Kane–Williams function** `B(x, a) = ⟨r_z, x⟩` on `n + k * ℓ` bits, for a list of rows
`r : BitString k → BitString n` ([KaneWilliams2016], `arXiv:1511.07860v1`, Definition 6.1): the
first `n` bits are a message `x`, the remaining `k * ℓ` bits form `k` blocks of `ℓ` bits whose
parities form `z : BitString k`, and the value is the inner product modulo two of the row `r z`
with `x`. Kane and Williams take the rows of an `ε`-biased set, `ℓ = n / k` and `k = 16 log₂ n`. -/
@[expose] def kaneWilliamsB {n k : ℕ} (r : BitString k → BitString n) (ℓ : ℕ) :
    BooleanFunction (n + k * ℓ) :=
  fun y => r (kaneWilliamsParities n k ℓ y) ⬝ᵥ kaneWilliamsMessage n k ℓ y

/-- The block variables are jointly injective in the block and the slot. -/
theorem kaneWilliamsBlockVar_joint_injective (n k ℓ : ℕ) (j₁ : Fin k) (t₁ : Fin ℓ)
    (j₂ : Fin k) (t₂ : Fin ℓ)
    (h : kaneWilliamsBlockVar n k ℓ j₁ t₁ = kaneWilliamsBlockVar n k ℓ j₂ t₂) :
    j₁ = j₂ ∧ t₁ = t₂ :=
  Prod.ext_iff.mp (finProdFinEquiv.injective (Fin.natAdd_injective (k * ℓ) n h))

/-- No message coordinate is a block variable. -/
theorem kaneWilliamsMessageIndex_ne_blockVar (n k ℓ : ℕ) (i : Fin n) (j : Fin k) (t : Fin ℓ) :
    kaneWilliamsMessageIndex n k ℓ i ≠ kaneWilliamsBlockVar n k ℓ j t := fun h => by
  have hval := congrArg Fin.val h
  simp only [kaneWilliamsMessageIndex, kaneWilliamsBlockVar, Fin.val_castAdd,
    Fin.val_natAdd] at hval
  omega

/-- The message of an input is the first component of its split into message and blocks. -/
theorem kaneWilliamsMessage_eq_fst (n k ℓ : ℕ) (y : BitString (n + k * ℓ)) :
    kaneWilliamsMessage n k ℓ y = ((Fin.appendEquiv n (k * ℓ)).symm y).1 := by
  funext i
  conv_lhs => rw [← (Fin.appendEquiv n (k * ℓ)).apply_symm_apply y]
  simp [kaneWilliamsMessage, kaneWilliamsMessageIndex, Fin.appendEquiv]

/-- Each message is the message of `2 ^ (k * ℓ)` inputs:
`#{y | kaneWilliamsMessage n k ℓ y ∈ S} = #S * 2 ^ (k * ℓ)`. -/
theorem card_filter_kaneWilliamsMessage_mem (n k ℓ : ℕ) (S : Finset (BitString n)) :
    #{y : BitString (n + k * ℓ) | kaneWilliamsMessage n k ℓ y ∈ S} = #S * 2 ^ (k * ℓ) := by
  classical
  calc #{y : BitString (n + k * ℓ) | kaneWilliamsMessage n k ℓ y ∈ S}
      = #(S ×ˢ (univ : Finset (BitString (k * ℓ)))) :=
        card_equiv (Fin.appendEquiv n (k * ℓ)).symm fun y => by
          simp [kaneWilliamsMessage_eq_fst]
    _ = #S * 2 ^ (k * ℓ) := by
        rw [card_product, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

end Cslib.Circuits.Boolean

namespace Cslib.Circuits.Boolean.WeightedThreshold

open BitString Finset Probability Cslib.Combinatorics.LittlewoodOfford

/-! ### Block restrictions of the Kane–Williams function -/

/-- The live coordinate `kaneWilliamsBlockVar n k ℓ j (σ j)` of block `j` chosen by
`σ : Fin k → Fin ℓ`. -/
@[expose] def kaneWilliamsLiveVar (n k ℓ : ℕ) (σ : Fin k → Fin ℓ) (j : Fin k) : Fin (n + k * ℓ) :=
  kaneWilliamsBlockVar n k ℓ j (σ j)

/-- For every block selection, the live coordinates are distinct. -/
theorem kaneWilliamsLiveVar_injective (n k ℓ : ℕ) (σ : Fin k → Fin ℓ) :
    Function.Injective (kaneWilliamsLiveVar n k ℓ σ) :=
  fun j₁ j₂ h => (kaneWilliamsBlockVar_joint_injective n k ℓ j₁ (σ j₁) j₂ (σ j₂) h).1

/-- The live coordinates of `σ` form `blockLiveSet (kaneWilliamsBlockVar n k ℓ) σ`. -/
theorem univ_image_kaneWilliamsLiveVar_eq_blockLiveSet (n k ℓ : ℕ) (σ : Fin k → Fin ℓ) :
    univ.image (kaneWilliamsLiveVar n k ℓ σ) = blockLiveSet (kaneWilliamsBlockVar n k ℓ) σ :=
  rfl

/-- The `k`-bit vector of residual block parities of `w` outside the live slots `σ j`. -/
@[expose] def kaneWilliamsResidualParities (n k ℓ : ℕ) (σ : Fin k → Fin ℓ)
    (w : BitString (n + k * ℓ)) : BitString k :=
  fun j => parityOn (univ.erase (σ j)) fun t => w (kaneWilliamsBlockVar n k ℓ j t)

/-- Updating the live coordinates leaves the message unchanged. -/
theorem kaneWilliamsMessage_embedUpdate (n k ℓ : ℕ) (σ : Fin k → Fin ℓ)
    (w : BitString (n + k * ℓ)) (u : BitString k) :
    kaneWilliamsMessage n k ℓ (embedUpdate (kaneWilliamsLiveVar n k ℓ σ) w u) =
      kaneWilliamsMessage n k ℓ w := by
  funext i
  refine embedUpdate_of_notMem w u ?_
  simp only [mem_image, mem_univ, true_and, not_exists]
  exact fun j hj => kaneWilliamsMessageIndex_ne_blockVar n k ℓ i j (σ j) hj.symm

/-- Updating the live coordinates with `u` shifts the block parities by `u`. -/
theorem kaneWilliamsParities_embedUpdate (n k ℓ : ℕ) (σ : Fin k → Fin ℓ)
    (w : BitString (n + k * ℓ)) (u : BitString k) :
    kaneWilliamsParities n k ℓ (embedUpdate (kaneWilliamsLiveVar n k ℓ σ) w u) =
      u + kaneWilliamsResidualParities n k ℓ σ w := by
  funext j
  change parityOn univ
      (fun t => embedUpdate (kaneWilliamsLiveVar n k ℓ σ) w u (kaneWilliamsBlockVar n k ℓ j t)) =
    (u j ^^ kaneWilliamsResidualParities n k ℓ σ w j)
  rw [parityOn_eq_xor_erase (mem_univ (σ j))]
  congr 1
  · exact embedUpdate_emb (kaneWilliamsLiveVar_injective n k ℓ σ) w u j
  · refine parityOn_congr fun t ht => embedUpdate_of_notMem w u ?_
    simp only [mem_image, mem_univ, true_and, not_exists]
    intro j' hj'
    obtain ⟨rfl, h2⟩ := kaneWilliamsBlockVar_joint_injective n k ℓ j' (σ j') j t hj'
    exact (mem_erase.mp ht).1 h2.symm

/-- Along `u ↦ embedUpdate (kaneWilliamsLiveVar n k ℓ σ) w u`, the Kane–Williams function reads
the row `r (u + c)` for the residual parities `c` of `w`. -/
theorem kaneWilliamsB_embedUpdate {n k : ℕ} (r : BitString k → BitString n) (ℓ : ℕ)
    (σ : Fin k → Fin ℓ) (w : BitString (n + k * ℓ)) (u : BitString k) :
    kaneWilliamsB r ℓ (embedUpdate (kaneWilliamsLiveVar n k ℓ σ) w u) =
      r (u + kaneWilliamsResidualParities n k ℓ σ w) ⬝ᵥ kaneWilliamsMessage n k ℓ w := by
  rw [kaneWilliamsB, kaneWilliamsParities_embedUpdate, kaneWilliamsMessage_embedUpdate]

/-! ### Messages correlated with a restricted circuit -/

section Core

variable {n k ℓ : ℕ}

/-- Twice the agreement of two Boolean functions is `|Z|` plus their sign correlation. -/
private theorem two_mul_card_eq_add_sum_signVal {Z : Type*} [Fintype Z] (f g : Z → Bool) :
    2 * (#{z | f z = g z} : ℝ) = Fintype.card Z + ∑ z, signVal (f z) * signVal (g z) := by
  classical
  have h (z : Z) : signVal (f z) * signVal (g z) = 2 * (if f z = g z then 1 else 0) - 1 := by
    rw [signVal_mul_signVal]; split_ifs <;> norm_num
  rw [sum_congr rfl fun z _ => h z, sum_sub_distrib, ← mul_sum, sum_boole, sum_const, card_univ,
    nsmul_eq_mul, mul_one]
  ring

/-- Translating the first argument of a sign correlation translates the second. -/
private theorem sum_signVal_add_eq (h F : BitString k → Bool) (c : BitString k) :
    ∑ u, signVal (h (u + c)) * signVal (F u) = ∑ u, signVal (h u) * signVal (F (u + c)) := by
  have hcc : c + c = 0 := funext fun i => BooleanRing.add_self (c i)
  refine Fintype.sum_equiv (Equiv.addRight c) _ _ fun u => ?_
  simp only [Equiv.coe_addRight, add_assoc, hcc, add_zero]

/-- **Markov's inequality** for counts: at most `(∑ U) / (Q + 1)` points have `U > Q`. -/
private theorem add_one_mul_card_filter_lt_le {α : Type*} (s : Finset α) (U : α → ℕ) (Q : ℕ) :
    ((Q : ℝ) + 1) * #{a ∈ s | Q < U a} ≤ ∑ a ∈ s, (U a : ℝ) := by
  classical
  calc ((Q : ℝ) + 1) * #{a ∈ s | Q < U a} = #{a ∈ s | Q < U a} • ((Q : ℝ) + 1) := by
        rw [nsmul_eq_mul, mul_comm]
    _ ≤ ∑ a ∈ s with Q < U a, (U a : ℝ) := card_nsmul_le_sum _ _ _ fun a ha => by
        exact_mod_cast Nat.succ_le_of_lt (mem_filter.mp ha).2
    _ ≤ ∑ a ∈ s, (U a : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => Nat.cast_nonneg _

open scoped Classical in
/-- The messages `x` whose word `u ↦ r u ⬝ᵥ x` has sign correlation at least `γ 2 ^ k` in absolute
value with a translate `u ↦ h (u + c)` of a function `h` in `IsDepthTwoOverWeights (W σ) Q`, for
some block selection `σ`. -/
private noncomputable def badMessages (r : BitString k → BitString n)
    (W : (Fin k → Fin ℓ) → Finset (Fin k → ℝ)) (Q : ℕ) (γ : ℝ) : Finset (BitString n) :=
  univ.filter fun x => ∃ σ : Fin k → Fin ℓ, ∃ c : BitString k, ∃ h : BitString k → Bool,
    IsDepthTwoOverWeights (W σ) Q h ∧
      γ * 2 ^ k ≤ |∑ u, signVal (h (u + c)) * signVal (r u ⬝ᵥ x)|

/-- **Few messages are bad**: the fixed weight vectors of the restricted circuits leave at most
`ℓ ^ k * 2 ^ k * ((2 ^ k + 1) * M) ^ Q * (2 ^ k + 1) ^ (Q + k + 1)` restricted functions and
translations, and each correlates with at most `1 / (γ ^ 2 - δ)` words. -/
private theorem card_badMessages_mul_le {r : BitString k → BitString n} {δ γ : ℝ} (hδ : 0 ≤ δ)
    (hγ : 0 ≤ γ) (hr : IsSmallBias δ ((PMF.uniformOfFintype (BitString k)).map r))
    (W : (Fin k → Fin ℓ) → Finset (Fin k → ℝ)) {M : ℕ} (hM : ∀ σ, #(W σ) + 1 ≤ M) (Q : ℕ) :
    (#(badMessages r W Q γ) : ℝ) * (γ ^ 2 - δ) ≤
      (ℓ : ℝ) ^ k * 2 ^ k * ((((2 ^ k + 1) * M) ^ Q * (2 ^ k + 1) ^ (Q + k + 1) : ℕ) : ℝ) := by
  classical
  rcases le_or_gt (γ ^ 2 - δ) 0 with hneg | hpos
  · exact (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hneg).trans (by positivity)
  set C : ℕ := ((2 ^ k + 1) * M) ^ Q * (2 ^ k + 1) ^ (Q + k + 1) with hC
  let H : (Fin k → Fin ℓ) → Finset (BitString k → Bool) := fun σ =>
    univ.filter (IsDepthTwoOverWeights (W σ) Q)
  let L : (BitString k → Bool) → BitString k → Finset (BitString n) := fun h c =>
    univ.filter fun x => γ * Fintype.card (BitString k) ≤
      |∑ u, signVal (h (u + c)) * signVal (r u ⬝ᵥ x)|
  have hcardZ : (Fintype.card (BitString k) : ℝ) = 2 ^ k := by simp
  have hsub : badMessages r W Q γ ⊆
      univ.biUnion fun σ => univ.biUnion fun c => (H σ).biUnion fun h => L h c := by
    intro x hx
    obtain ⟨σ, c, h, hh, hcorr⟩ := (mem_filter.mp hx).2
    refine mem_biUnion.mpr ⟨σ, mem_univ σ, mem_biUnion.mpr ⟨c, mem_univ c,
      mem_biUnion.mpr ⟨h, mem_filter.mpr ⟨mem_univ h, hh⟩, mem_filter.mpr ⟨mem_univ x, ?_⟩⟩⟩⟩
    rw [hcardZ]
    exact hcorr
  have hL (h : BitString k → Bool) (c : BitString k) : (#(L h c) : ℝ) * (γ ^ 2 - δ) ≤ 1 :=
    card_le_abs_sum_signVal_mul_signVal_dotProduct_mul_le hδ hγ hr fun u => h (u + c)
  have hH (σ : Fin k → Fin ℓ) : (#(H σ) : ℝ) ≤ C := by
    have hcount := card_isDepthTwoOverWeights_le (κ := Fin k) (W σ) Q
    rw [Fintype.card_fin] at hcount
    exact_mod_cast hcount.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left
      (Nat.mul_le_mul_left _ ((min_le_left _ _).trans (hM σ))) Q))
  have hcard : (#(badMessages r W Q γ) : ℝ) ≤ ∑ σ, ∑ c, ∑ h ∈ H σ, (#(L h c) : ℝ) := by
    exact_mod_cast (card_le_card hsub).trans (card_biUnion_le.trans (sum_le_sum fun σ _ =>
      card_biUnion_le.trans (sum_le_sum fun c _ => card_biUnion_le)))
  calc (#(badMessages r W Q γ) : ℝ) * (γ ^ 2 - δ)
      ≤ (∑ σ, ∑ c, ∑ h ∈ H σ, (#(L h c) : ℝ)) * (γ ^ 2 - δ) :=
        mul_le_mul_of_nonneg_right hcard hpos.le
    _ = ∑ σ, ∑ c, ∑ h ∈ H σ, (#(L h c) : ℝ) * (γ ^ 2 - δ) := by simp only [sum_mul]
    _ ≤ ∑ σ : Fin k → Fin ℓ, ∑ _c : BitString k, ∑ _h ∈ H σ, (1 : ℝ) :=
        sum_le_sum fun σ _ => sum_le_sum fun c _ => sum_le_sum fun h _ => hL h c
    _ ≤ ∑ _σ : Fin k → Fin ℓ, ∑ _c : BitString k, (C : ℝ) :=
        sum_le_sum fun σ _ => sum_le_sum fun _ _ => by rw [sum_const, nsmul_one]; exact hH σ
    _ = (ℓ : ℝ) ^ k * 2 ^ k * (C : ℝ) := by
        simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
          nsmul_eq_mul]
        push_cast
        ring

/-- The zero message is bad: its word is constantly `false`, like the constant function. -/
private theorem zero_mem_badMessages (r : BitString k → BitString n) (hℓ : 0 < ℓ)
    (W : (Fin k → Fin ℓ) → Finset (Fin k → ℝ)) (Q : ℕ) {γ : ℝ} (hγ1 : γ ≤ 1) :
    0 ∈ badMessages r W Q γ := by
  classical
  refine mem_filter.mpr ⟨mem_univ _, fun _ => ⟨0, hℓ⟩, 0, fun _ => false,
    isDepthTwoOverWeights_const _ Q false, ?_⟩
  have h0 : signVal (0 : Bool) = 1 := rfl
  simp only [dotProduct_zero, signVal_false, h0, mul_one, sum_const, card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rw [abs_of_nonneg (by positivity)]
  nlinarith [(by positivity : (0 : ℝ) < 2 ^ k)]

/-- The bad messages occupy at most a `#bad / 2 ^ n` fraction of the inputs, bounded by the
counting term. -/
private theorem card_filter_badMessages_le {r : BitString k → BitString n} {δ γ : ℝ}
    (hδ : 0 ≤ δ) (hγ : 0 ≤ γ) (hγδ : δ < γ ^ 2)
    (hr : IsSmallBias δ ((PMF.uniformOfFintype (BitString k)).map r))
    (W : (Fin k → Fin ℓ) → Finset (Fin k → ℝ)) {M : ℕ} (hM : ∀ σ, #(W σ) + 1 ≤ M) (Q : ℕ) :
    (#{w : BitString (n + k * ℓ) | kaneWilliamsMessage n k ℓ w ∈ badMessages r W Q γ} : ℝ) ≤
      2 ^ (n + k * ℓ) * ((ℓ : ℝ) ^ k * 2 ^ k *
        ((((2 ^ k + 1) * M) ^ Q * (2 ^ k + 1) ^ (Q + k + 1) : ℕ) : ℝ) /
          ((γ ^ 2 - δ) * 2 ^ n)) := by
  have hbad := card_badMessages_mul_le (ℓ := ℓ) hδ hγ hr W hM Q
  have hpos : 0 < γ ^ 2 - δ := sub_pos.mpr hγδ
  rw [card_filter_kaneWilliamsMessage_mem]
  push_cast
  rw [pow_add, mul_div_assoc', le_div_iff₀ (by positivity)]
  calc (#(badMessages r W Q γ) : ℝ) * 2 ^ (k * ℓ) * ((γ ^ 2 - δ) * 2 ^ n)
      = (#(badMessages r W Q γ) : ℝ) * (γ ^ 2 - δ) * (2 ^ n * 2 ^ (k * ℓ)) := by ring
    _ ≤ (ℓ : ℝ) ^ k * 2 ^ k * ((((2 ^ k + 1) * M) ^ Q * (2 ^ k + 1) ^ (Q + k + 1) : ℕ) : ℝ) *
        (2 ^ n * 2 ^ (k * ℓ)) := mul_le_mul_of_nonneg_right (by exact_mod_cast hbad) (by positivity)
    _ = _ := by push_cast; ring

/-- On a block restriction with message `x = kaneWilliamsMessage n k ℓ w` and residual parities `c`,
twice the agreement of `h` with the Kane–Williams function is `2 ^ k` plus the sign correlation of
the translate `u ↦ h (u + c)` with the word of `x`. -/
private theorem two_mul_card_agree_eq {r : BitString k → BitString n} (σ : Fin k → Fin ℓ)
    (w : BitString (n + k * ℓ)) (h : BitString k → Bool) :
    2 * (#{u : BitString k | h u =
        kaneWilliamsB r ℓ (embedUpdate (kaneWilliamsLiveVar n k ℓ σ) w u)} : ℝ) =
      2 ^ k + ∑ u, signVal (h (u + kaneWilliamsResidualParities n k ℓ σ w)) *
        signVal (r u ⬝ᵥ kaneWilliamsMessage n k ℓ w) := by
  simp_rw [kaneWilliamsB_embedUpdate]
  rw [two_mul_card_eq_add_sum_signVal, sum_signVal_add_eq]
  simp

/-- **Average-case core** (original): let `f` collapse, under every block restriction `(σ, w)`, to
a function in `IsDepthTwoOverWeights (W σ) (U σ w)` with `#(W σ) < M`, and let the mean of `U` be
at most `B`. If the rows `r` are `δ`-biased and `δ < γ ^ 2`, then for every `Q`, `f` agrees with
the Kane–Williams function on at most a `(1 + γ) / 2 + C / ((γ ^ 2 - δ) 2 ^ n) + B / (Q + 1)`
fraction of the inputs, where
`C = ℓ ^ k * 2 ^ k * ((2 ^ k + 1) * M) ^ Q * (2 ^ k + 1) ^ (Q + k + 1)`. The terms bound the
correlation on a restriction with at most `Q` survivors, the bad messages, and the restrictions
with more survivors (Markov's inequality). -/
theorem card_eval_eq_kaneWilliamsB_le_of_unforced_mean_le (hℓ : 0 < ℓ)
    {r : BitString k → BitString n} {δ γ : ℝ} (hδ : 0 ≤ δ) (hγ : 0 ≤ γ) (hγδ : δ < γ ^ 2)
    (hr : IsSmallBias δ ((PMF.uniformOfFintype (BitString k)).map r))
    (f : BitString (n + k * ℓ) → Bool) (W : (Fin k → Fin ℓ) → Finset (Fin k → ℝ)) {M : ℕ}
    (hM : ∀ σ, #(W σ) + 1 ≤ M) (U : (Fin k → Fin ℓ) → BitString (n + k * ℓ) → ℕ)
    (hU : ∀ σ w, IsDepthTwoOverWeights (W σ) (U σ w)
      fun u => f (embedUpdate (kaneWilliamsLiveVar n k ℓ σ) w u))
    {B : ℝ} (hmean : (∑ σ : Fin k → Fin ℓ, ∑ w : BitString (n + k * ℓ), (U σ w : ℝ)) ≤
      (Fintype.card (Fin k → Fin ℓ) : ℝ) * 2 ^ (n + k * ℓ) * B) (Q : ℕ) :
    (#{y | f y = kaneWilliamsB r ℓ y} : ℝ) ≤ 2 ^ (n + k * ℓ) * ((1 + γ) / 2 +
      (ℓ : ℝ) ^ k * 2 ^ k * ((((2 ^ k + 1) * M) ^ Q * (2 ^ k + 1) ^ (Q + k + 1) : ℕ) : ℝ) /
        ((γ ^ 2 - δ) * 2 ^ n) + B / (Q + 1)) := by
  classical
  set bad := badMessages r W Q γ with hbad
  set CT : ℝ := (ℓ : ℝ) ^ k * 2 ^ k *
    ((((2 ^ k + 1) * M) ^ Q * (2 ^ k + 1) ^ (Q + k + 1) : ℕ) : ℝ) / ((γ ^ 2 - δ) * 2 ^ n)
  set N : ℝ := 2 ^ (n + k * ℓ) with hN
  set A : ℝ := (#{y | f y = kaneWilliamsB r ℓ y} : ℝ) with hA
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  -- the agreement on each restriction
  have hpt (σ : Fin k → Fin ℓ) (w : BitString (n + k * ℓ)) :
      (#{u : BitString k | f (embedUpdate (kaneWilliamsLiveVar n k ℓ σ) w u) =
        kaneWilliamsB r ℓ (embedUpdate (kaneWilliamsLiveVar n k ℓ σ) w u)} : ℝ) ≤
      2 ^ k * ((1 + γ) / 2) + 2 ^ k * (if kaneWilliamsMessage n k ℓ w ∈ bad then 1 else 0) +
        2 ^ k * (if Q < U σ w then 1 else 0) := by
    have hle : (#{u : BitString k | f (embedUpdate (kaneWilliamsLiveVar n k ℓ σ) w u) =
        kaneWilliamsB r ℓ (embedUpdate (kaneWilliamsLiveVar n k ℓ σ) w u)} : ℝ) ≤ 2 ^ k := by
      exact_mod_cast (card_le_univ _).trans_eq (by simp)
    have hγ2 : 0 ≤ 2 ^ k * ((1 + γ) / 2) := by positivity
    by_cases hb : kaneWilliamsMessage n k ℓ w ∈ bad
    · have : (0 : ℝ) ≤ 2 ^ k * (if Q < U σ w then 1 else 0) := by positivity
      simp only [hb, ↓reduceIte]
      linarith
    by_cases hq : Q < U σ w
    · simp only [hq, ↓reduceIte]
      have : (0 : ℝ) ≤ 2 ^ k * (if kaneWilliamsMessage n k ℓ w ∈ bad then 1 else 0) := by
        positivity
      linarith
    simp only [hb, hq, ↓reduceIte, mul_zero, add_zero]
    have hh : IsDepthTwoOverWeights (W σ) Q
        fun u => f (embedUpdate (kaneWilliamsLiveVar n k ℓ σ) w u) :=
      (hU σ w).mono (not_lt.mp hq)
    have hcorr : |∑ u, signVal (f (embedUpdate (kaneWilliamsLiveVar n k ℓ σ) w
        (u + kaneWilliamsResidualParities n k ℓ σ w))) *
          signVal (r u ⬝ᵥ kaneWilliamsMessage n k ℓ w)| < γ * 2 ^ k := by
      by_contra hge
      exact hb (mem_filter.mpr ⟨mem_univ _, σ, _, _, hh, not_lt.mp hge⟩)
    have hagree := two_mul_card_agree_eq (r := r) σ w
      fun u => f (embedUpdate (kaneWilliamsLiveVar n k ℓ σ) w u)
    nlinarith [le_abs_self (∑ u, signVal (f (embedUpdate (kaneWilliamsLiveVar n k ℓ σ) w
        (u + kaneWilliamsResidualParities n k ℓ σ w))) *
          signVal (r u ⬝ᵥ kaneWilliamsMessage n k ℓ w))]
  -- summing over the fixed values, for each block selection
  have hbadw : (#{w : BitString (n + k * ℓ) | kaneWilliamsMessage n k ℓ w ∈ bad} : ℝ) ≤
      N * CT := card_filter_badMessages_le hδ hγ hγδ hr W hM Q
  have hσ (σ : Fin k → Fin ℓ) : 2 ^ k * A ≤ N * (2 ^ k * ((1 + γ) / 2)) +
      2 ^ k * (N * CT) + 2 ^ k * (#{w : BitString (n + k * ℓ) | Q < U σ w} : ℝ) := by
    have hsum := sum_card_filter_embedUpdate (kaneWilliamsLiveVar_injective n k ℓ σ)
      fun y => f y = kaneWilliamsB r ℓ y
    rw [Fintype.card_fin] at hsum
    have hA' : 2 ^ k * A = ∑ w : BitString (n + k * ℓ),
        (#{u : BitString k | f (embedUpdate (kaneWilliamsLiveVar n k ℓ σ) w u) =
          kaneWilliamsB r ℓ (embedUpdate (kaneWilliamsLiveVar n k ℓ σ) w u)} : ℝ) := by
      rw [hA]; exact_mod_cast hsum.symm
    rw [hA']
    refine (sum_le_sum fun w _ => hpt σ w).trans ?_
    rw [sum_add_distrib, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← mul_sum,
      ← mul_sum, sum_boole, sum_boole]
    have hcardN : (Fintype.card (BitString (n + k * ℓ)) : ℝ) = N := by rw [hN]; simp
    rw [hcardN]
    nlinarith
  -- summing over the block selections, with Markov's inequality for the survivors
  set S : ℝ := (Fintype.card (Fin k → Fin ℓ) : ℝ) with hS
  have hS0 : 0 < S := by
    rw [hS, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]; positivity
  have hmarkov : ((Q : ℝ) + 1) * ∑ σ : Fin k → Fin ℓ, (#{w : BitString (n + k * ℓ) | Q < U σ w} : ℝ)
      ≤ S * N * B := by
    rw [mul_sum]
    exact (sum_le_sum fun σ _ => add_one_mul_card_filter_lt_le univ (U σ) Q).trans hmean
  have hsumσ := sum_le_sum fun σ (_ : σ ∈ (univ : Finset (Fin k → Fin ℓ))) => hσ σ
  rw [sum_const, card_univ, nsmul_eq_mul, sum_add_distrib, sum_add_distrib, sum_const, sum_const,
    card_univ, nsmul_eq_mul, nsmul_eq_mul, ← mul_sum, ← hS] at hsumσ
  have hQ : (0 : ℝ) < Q + 1 := by positivity
  have hmarkov' : (∑ σ : Fin k → Fin ℓ, (#{w : BitString (n + k * ℓ) | Q < U σ w} : ℝ)) ≤
      S * N * (B / (Q + 1)) := by
    rw [mul_div_assoc', le_div_iff₀ hQ]; linarith
  have hkey : S * (2 ^ k * A) ≤ S * (2 ^ k * (N * ((1 + γ) / 2 + CT + B / (Q + 1)))) := by
    have := mul_le_mul_of_nonneg_left hmarkov' h2k.le
    nlinarith
  exact le_of_mul_le_mul_left (le_of_mul_le_mul_left hkey hS0) h2k

/-- **Worst-case core** (original; [KaneWilliams2016], `arXiv:1511.07860v1`, Theorem 1.3 fixes the
message first): let `v` be `t` votes whose unweighted threshold vote `threshold t θ (v y)`
computes the Kane–Williams function, and let every vote collapse, under every block restriction
`(σ, w)`, to a function in `IsDepthTwoOverWeights (W σ) (U σ w)`, one count `U σ w` for all votes,
with `#(W σ) < M` and the mean of `U` at most `B`. If the rows are `δ`-biased, `0 ≤ γ ≤ 1`,
`δ < γ ^ 2` and `t γ + (t + 1) δ < 1`, then every `Q` satisfies
`1 ≤ C / ((γ ^ 2 - δ) 2 ^ n) + B / (Q + 1)` with `C` as in
`card_eval_eq_kaneWilliamsB_le_of_unforced_mean_le`. Otherwise some restriction has a good
message and at most `Q` survivors; there every vote has correlation below `γ` with the restricted
function, while the discriminator lemma needs a total correlation of `1 - (t + 1) δ`. -/
theorem one_le_of_threshold_eq_kaneWilliamsB_of_unforced_mean_le {t : ℕ} (hℓ : 0 < ℓ)
    {r : BitString k → BitString n} {δ γ : ℝ} (hδ : 0 ≤ δ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hγδ : δ < γ ^ 2) (htγδ : t * γ + (t + 1) * δ < 1)
    (hr : IsSmallBias δ ((PMF.uniformOfFintype (BitString k)).map r))
    (v : BitString (n + k * ℓ) → BitString t) {θ : ℕ}
    (hv : ∀ y, threshold t θ (v y) = kaneWilliamsB r ℓ y)
    (W : (Fin k → Fin ℓ) → Finset (Fin k → ℝ)) {M : ℕ} (hM : ∀ σ, #(W σ) + 1 ≤ M)
    (U : (Fin k → Fin ℓ) → BitString (n + k * ℓ) → ℕ)
    (hU : ∀ σ w o, IsDepthTwoOverWeights (W σ) (U σ w)
      fun u => v (embedUpdate (kaneWilliamsLiveVar n k ℓ σ) w u) o)
    {B : ℝ} (hmean : (∑ σ : Fin k → Fin ℓ, ∑ w : BitString (n + k * ℓ), (U σ w : ℝ)) ≤
      (Fintype.card (Fin k → Fin ℓ) : ℝ) * 2 ^ (n + k * ℓ) * B) (Q : ℕ) :
    1 ≤ (ℓ : ℝ) ^ k * 2 ^ k * ((((2 ^ k + 1) * M) ^ Q * (2 ^ k + 1) ^ (Q + k + 1) : ℕ) : ℝ) /
        ((γ ^ 2 - δ) * 2 ^ n) + B / (Q + 1) := by
  classical
  set bad := badMessages r W Q γ with hbad
  set CT : ℝ := (ℓ : ℝ) ^ k * 2 ^ k *
    ((((2 ^ k + 1) * M) ^ Q * (2 ^ k + 1) ^ (Q + k + 1) : ℕ) : ℝ) / ((γ ^ 2 - δ) * 2 ^ n)
  set N : ℝ := 2 ^ (n + k * ℓ) with hN
  set S : ℝ := (Fintype.card (Fin k → Fin ℓ) : ℝ) with hS
  have hS0 : 0 < S := by
    rw [hS, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]; positivity
  have hN0 : 0 < N := by positivity
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hcardZ : (Fintype.card (BitString k) : ℝ) = 2 ^ k := by simp
  by_contra hlt
  push Not at hlt
  -- some restriction has a good message and at most `Q` survivors
  obtain ⟨σ, w, hgood, hq⟩ : ∃ σ w, kaneWilliamsMessage n k ℓ w ∉ bad ∧ U σ w ≤ Q := by
    by_contra hno
    push Not at hno
    have hcover (σ : Fin k → Fin ℓ) : N ≤
        (#{w : BitString (n + k * ℓ) | kaneWilliamsMessage n k ℓ w ∈ bad} : ℝ) +
          #{w : BitString (n + k * ℓ) | Q < U σ w} := by
      have hsub : (univ : Finset (BitString (n + k * ℓ))) ⊆
          (univ.filter fun w => kaneWilliamsMessage n k ℓ w ∈ bad) ∪
            univ.filter fun w => Q < U σ w := fun w _ => by
        by_cases hb : kaneWilliamsMessage n k ℓ w ∈ bad
        · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ w, hb⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ w, hno σ w hb⟩)
      have hcard := (card_le_card hsub).trans (card_union_le _ _)
      rw [card_univ] at hcard
      have hcardN : (Fintype.card (BitString (n + k * ℓ)) : ℝ) = N := by rw [hN]; simp
      rw [← hcardN]
      exact_mod_cast hcard
    have hbadw : (#{w : BitString (n + k * ℓ) | kaneWilliamsMessage n k ℓ w ∈ bad} : ℝ) ≤
        N * CT := card_filter_badMessages_le hδ hγ hγδ hr W hM Q
    have hQ : (0 : ℝ) < Q + 1 := by positivity
    have hmarkov : ((Q : ℝ) + 1) *
        ∑ σ : Fin k → Fin ℓ, (#{w : BitString (n + k * ℓ) | Q < U σ w} : ℝ) ≤ S * N * B := by
      rw [mul_sum]
      exact (sum_le_sum fun σ _ => add_one_mul_card_filter_lt_le univ (U σ) Q).trans hmean
    have hsumσ := sum_le_sum fun σ (_ : σ ∈ (univ : Finset (Fin k → Fin ℓ))) => hcover σ
    rw [sum_const, card_univ, nsmul_eq_mul, sum_add_distrib, sum_const, card_univ,
      nsmul_eq_mul, ← hS] at hsumσ
    have hmarkov' : (∑ σ : Fin k → Fin ℓ, (#{w : BitString (n + k * ℓ) | Q < U σ w} : ℝ)) ≤
        S * N * (B / (Q + 1)) := by
      rw [mul_div_assoc', le_div_iff₀ hQ]; linarith
    have hkey : S * N * 1 ≤ S * N * (CT + B / (Q + 1)) := by
      nlinarith [mul_le_mul_of_nonneg_left hbadw hS0.le]
    have := le_of_mul_le_mul_left hkey (mul_pos hS0 hN0)
    linarith
  set x := kaneWilliamsMessage n k ℓ w with hx
  set c := kaneWilliamsResidualParities n k ℓ σ w with hc
  have hx0 : x ≠ 0 := fun h0 => hgood (h0 ▸ zero_mem_badMessages r hℓ W Q hγ1)
  have hcc : c + c = 0 := funext fun i => BooleanRing.add_self (c i)
  -- on the restriction, the translated votes compute the word of `x`
  set V : BitString k → BitString t :=
    fun u => v (embedUpdate (kaneWilliamsLiveVar n k ℓ σ) w (u + c)) with hVdef
  have hV (u : BitString k) : threshold t θ (V u) = r u ⬝ᵥ x := by
    rw [hVdef, hv, kaneWilliamsB_embedUpdate, add_assoc, hcc, add_zero]
  have hdisc := sub_le_sum_sum_signVal_mul_of_threshold_eq V (fun u => r u ⬝ᵥ x) hV
  rw [hcardZ] at hdisc
  -- the word of `x ≠ 0` is nearly balanced
  have hbal : |∑ u, signVal (r u ⬝ᵥ x)| ≤ δ * 2 ^ k := by
    have h := abs_sum_signVal_dotProduct_le hr hx0
    rwa [hcardZ] at h
  -- every restricted vote has correlation below `γ`
  have hsmall (o : Fin t) : ∑ u, signVal (V u o) * signVal (r u ⬝ᵥ x) ≤ γ * 2 ^ k := by
    have hh : IsDepthTwoOverWeights (W σ) Q
        fun u => v (embedUpdate (kaneWilliamsLiveVar n k ℓ σ) w u) o := (hU σ w o).mono hq
    by_contra hgt
    push Not at hgt
    exact hgood (mem_filter.mpr ⟨mem_univ _, σ, c, _, hh, hgt.le.trans (le_abs_self _)⟩)
  have hsum : ∑ o, ∑ u, signVal (V u o) * signVal (r u ⬝ᵥ x) ≤ t * (γ * 2 ^ k) := by
    refine (sum_le_sum fun o _ => hsmall o).trans ?_
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have ht0 : (0 : ℝ) ≤ t + 1 := by positivity
  have hcomb : 2 ^ k * (1 - (t + 1) * δ) ≤ 2 ^ k * (t * γ) := by
    nlinarith [mul_le_mul_of_nonneg_left hbal ht0]
  have := le_of_mul_le_mul_left hcomb h2k
  linarith

/-! ### Average case: depth-two circuits correlate weakly with the function -/

/-- **Average-case gate bound**: a depth-two weighted threshold circuit `c` agrees with the
Kane–Williams function of `δ`-biased rows on at most a
`(1 + γ) / 2 + ℓ ^ k * 2 ^ k * ((2 ^ k + 1) * (c.size + 1)) ^ Q * (2 ^ k + 1) ^ (Q + k + 1) /
((γ ^ 2 - δ) 2 ^ n) + 4 * (1 / ℓ) * c.size * √(n + k ℓ) / (Q + 1)` fraction of the inputs, for
every `Q` and `δ < γ ^ 2`. -/
theorem card_eval_eq_kaneWilliamsB_le_of_depth_le_two_size (hℓ : 0 < ℓ)
    {r : BitString k → BitString n} {δ γ : ℝ} (hδ : 0 ≤ δ) (hγ : 0 ≤ γ) (hγδ : δ < γ ^ 2)
    (hr : IsSmallBias δ ((PMF.uniformOfFintype (BitString k)).map r))
    (c : Circuit signature (n + k * ℓ) 1) (hd : c.depth ≤ 2) (o : Fin 1) (Q : ℕ) :
    (#{y | c.eval interpretation y o = kaneWilliamsB r ℓ y} : ℝ) ≤ 2 ^ (n + k * ℓ) *
      ((1 + γ) / 2 + (ℓ : ℝ) ^ k * 2 ^ k *
        ((((2 ^ k + 1) * (c.size + 1)) ^ Q * (2 ^ k + 1) ^ (Q + k + 1) : ℕ) : ℝ) /
          ((γ ^ 2 - δ) * 2 ^ n) +
        4 * (1 / (ℓ : ℝ)) * c.size * Real.sqrt ((n + k * ℓ : ℕ) : ℝ) / (Q + 1)) := by
  classical
  refine card_eval_eq_kaneWilliamsB_le_of_unforced_mean_le hℓ hδ hγ hγδ hr
    (fun y => c.eval interpretation y o)
    (fun σ => circuitLiveWeights c o (kaneWilliamsLiveVar n k ℓ σ))
    (fun σ => Nat.add_le_add_right (card_circuitLiveWeights_le_size c o _) 1)
    (fun σ w => circuitUnforcedConstCount c o (blockLiveSet (kaneWilliamsBlockVar n k ℓ) σ) w)
    (fun σ w => by
      rw [← univ_image_kaneWilliamsLiveVar_eq_blockLiveSet]
      exact isDepthTwoOverWeights_eval_embedUpdate_const c hd o
        (kaneWilliamsLiveVar_injective n k ℓ σ) w) ?_ Q
  simpa [Fintype.card_fin] using sum_circuitUnforcedConstCount_blockLiveSet_le c o
    (kaneWilliamsBlockVar n k ℓ) (kaneWilliamsBlockVar_joint_injective n k ℓ)

/-- **Average-case wire bound**: as `card_eval_eq_kaneWilliamsB_le_of_depth_le_two_size`, with
`c.wireCount` in the counting term and the survivor term
`4 * c.wireCount * (1 / ℓ) * √(1 / ℓ) / (Q + 1)`. -/
theorem card_eval_eq_kaneWilliamsB_le_of_depth_le_two_wireCount (hℓ : 0 < ℓ)
    {r : BitString k → BitString n} {δ γ : ℝ} (hδ : 0 ≤ δ) (hγ : 0 ≤ γ) (hγδ : δ < γ ^ 2)
    (hr : IsSmallBias δ ((PMF.uniformOfFintype (BitString k)).map r))
    (c : Circuit signature (n + k * ℓ) 1) (hd : c.depth ≤ 2) (o : Fin 1) (Q : ℕ) :
    (#{y | c.eval interpretation y o = kaneWilliamsB r ℓ y} : ℝ) ≤ 2 ^ (n + k * ℓ) *
      ((1 + γ) / 2 + (ℓ : ℝ) ^ k * 2 ^ k *
        ((((2 ^ k + 1) * (c.wireCount + 1)) ^ Q * (2 ^ k + 1) ^ (Q + k + 1) : ℕ) : ℝ) /
          ((γ ^ 2 - δ) * 2 ^ n) +
        4 * (c.wireCount : ℝ) * (1 / (ℓ : ℝ)) * Real.sqrt (1 / (ℓ : ℝ)) / (Q + 1)) := by
  classical
  refine card_eval_eq_kaneWilliamsB_le_of_unforced_mean_le hℓ hδ hγ hγδ hr
    (fun y => c.eval interpretation y o)
    (fun σ => circuitLiveWeights c o (kaneWilliamsLiveVar n k ℓ σ))
    (fun σ => Nat.add_le_add_right (card_circuitLiveWeights_le_wireCount c o _) 1)
    (fun σ w => circuitUnforcedAtMostOneCount c o (blockLiveSet (kaneWilliamsBlockVar n k ℓ) σ) w)
    (fun σ w => by
      rw [← univ_image_kaneWilliamsLiveVar_eq_blockLiveSet]
      exact isDepthTwoOverWeights_eval_embedUpdate c hd o
        (kaneWilliamsLiveVar_injective n k ℓ σ) w) ?_ Q
  simpa [Fintype.card_fin] using sum_circuitUnforcedAtMostOneCount_blockLiveSet_le c o
    (kaneWilliamsBlockVar n k ℓ) (kaneWilliamsBlockVar_joint_injective n k ℓ)

/-! ### Worst case: unweighted threshold votes of depth-two circuits -/

/-- **Worst-case gate bound**: suppose the `t` outputs of a depth-two weighted threshold circuit
`c`, which share their bottom gates, feed an unweighted threshold gate `threshold t θ` (for
instance majority) that computes the Kane–Williams function of `δ`-biased rows. If `0 ≤ γ ≤ 1`,
`δ < γ ^ 2` and `t γ + (t + 1) δ < 1`, then every `Q` satisfies
`1 ≤ ℓ ^ k * 2 ^ k * ((2 ^ k + 1) * (c.size + 1)) ^ Q * (2 ^ k + 1) ^ (Q + k + 1) /
((γ ^ 2 - δ) 2 ^ n) + 4 * (1 / ℓ) * c.size * √(n + k ℓ) / (Q + 1)`. -/
theorem one_le_of_threshold_eval_eq_kaneWilliamsB_size {t : ℕ} (hℓ : 0 < ℓ)
    {r : BitString k → BitString n} {δ γ : ℝ} (hδ : 0 ≤ δ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hγδ : δ < γ ^ 2) (htγδ : t * γ + (t + 1) * δ < 1)
    (hr : IsSmallBias δ ((PMF.uniformOfFintype (BitString k)).map r))
    (c : Circuit signature (n + k * ℓ) t) (hd : c.depth ≤ 2) (θ : ℕ)
    (hc : ∀ y, threshold t θ (c.eval interpretation y) = kaneWilliamsB r ℓ y) (Q : ℕ) :
    1 ≤ (ℓ : ℝ) ^ k * 2 ^ k *
        ((((2 ^ k + 1) * (c.size + 1)) ^ Q * (2 ^ k + 1) ^ (Q + k + 1) : ℕ) : ℝ) /
          ((γ ^ 2 - δ) * 2 ^ n) +
        4 * (1 / (ℓ : ℝ)) * c.size * Real.sqrt ((n + k * ℓ : ℕ) : ℝ) / (Q + 1) := by
  classical
  refine one_le_of_threshold_eq_kaneWilliamsB_of_unforced_mean_le hℓ hδ hγ hγ1 hγδ htγδ hr
    (c.eval interpretation) hc
    (fun σ => circuitBottomWeights c (kaneWilliamsLiveVar n k ℓ σ))
    (fun σ => Nat.add_le_add_right
      ((card_circuitBottomWeights_le c _).trans (card_circuitBottomGates_le_size c)) 1)
    (fun σ w => circuitBottomUnforcedConstCount c (blockLiveSet (kaneWilliamsBlockVar n k ℓ) σ) w)
    (fun σ w o => by
      rw [← univ_image_kaneWilliamsLiveVar_eq_blockLiveSet]
      exact isDepthTwoOverWeights_eval_embedUpdate_circuitBottom_const c hd
        (kaneWilliamsLiveVar_injective n k ℓ σ) w o) ?_ Q
  simpa [Fintype.card_fin] using sum_circuitBottomUnforcedConstCount_blockLiveSet_le c
    (kaneWilliamsBlockVar n k ℓ) (kaneWilliamsBlockVar_joint_injective n k ℓ)

/-- **Worst-case wire bound**: as `one_le_of_threshold_eval_eq_kaneWilliamsB_size`, with
`c.wireCount` in the counting term and the survivor term
`4 * c.wireCount * (1 / ℓ) * √(1 / ℓ) / (Q + 1)`. The top gate's `t` wires are not counted. -/
theorem one_le_of_threshold_eval_eq_kaneWilliamsB_wireCount {t : ℕ} (hℓ : 0 < ℓ)
    {r : BitString k → BitString n} {δ γ : ℝ} (hδ : 0 ≤ δ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hγδ : δ < γ ^ 2) (htγδ : t * γ + (t + 1) * δ < 1)
    (hr : IsSmallBias δ ((PMF.uniformOfFintype (BitString k)).map r))
    (c : Circuit signature (n + k * ℓ) t) (hd : c.depth ≤ 2) (θ : ℕ)
    (hc : ∀ y, threshold t θ (c.eval interpretation y) = kaneWilliamsB r ℓ y) (Q : ℕ) :
    1 ≤ (ℓ : ℝ) ^ k * 2 ^ k *
        ((((2 ^ k + 1) * (c.wireCount + 1)) ^ Q * (2 ^ k + 1) ^ (Q + k + 1) : ℕ) : ℝ) /
          ((γ ^ 2 - δ) * 2 ^ n) +
        4 * (c.wireCount : ℝ) * (1 / (ℓ : ℝ)) * Real.sqrt (1 / (ℓ : ℝ)) / (Q + 1) := by
  classical
  refine one_le_of_threshold_eq_kaneWilliamsB_of_unforced_mean_le hℓ hδ hγ hγ1 hγδ htγδ hr
    (c.eval interpretation) hc
    (fun σ => circuitBottomWeights c (kaneWilliamsLiveVar n k ℓ σ))
    (fun σ => Nat.add_le_add_right
      ((card_circuitBottomWeights_le c _).trans (card_circuitBottomGates_le_wireCount c)) 1)
    (fun σ w =>
      circuitBottomUnforcedAtMostOneCount c (blockLiveSet (kaneWilliamsBlockVar n k ℓ) σ) w)
    (fun σ w o => by
      rw [← univ_image_kaneWilliamsLiveVar_eq_blockLiveSet]
      exact isDepthTwoOverWeights_eval_embedUpdate_circuitBottom c hd
        (kaneWilliamsLiveVar_injective n k ℓ σ) w o) ?_ Q
  simpa [Fintype.card_fin] using sum_circuitBottomUnforcedAtMostOneCount_blockLiveSet_le c
    (kaneWilliamsBlockVar n k ℓ) (kaneWilliamsBlockVar_joint_injective n k ℓ)

end Core

/-! ### Concrete parameters: `16 p` blocks and rows of bias `2 ^ (-7 p)` -/

section Concrete

variable {p n ℓ : ℕ}

/-- At `k = 16 p`, `γ = 2 ^ (-3 p)`, `δ = 2 ^ (-7 p)`, `ℓ ≤ 2 ^ p` and `M ≤ 2 ^ (4 p)`, the
counting term is at most `2 ^ ((36 p + 2) Q + 272 p ^ 2 + 54 p + 2) / 2 ^ n`. -/
private theorem countTerm_le (hp : 1 ≤ p) (hℓp : ℓ ≤ 2 ^ p) {M : ℕ} (hM : M ≤ 2 ^ (4 * p))
    (Q : ℕ) :
    (ℓ : ℝ) ^ (16 * p) * 2 ^ (16 * p) *
        ((((2 ^ (16 * p) + 1) * M) ^ Q * (2 ^ (16 * p) + 1) ^ (Q + 16 * p + 1) : ℕ) : ℝ) /
          ((((1 / 2 : ℝ) ^ (3 * p)) ^ 2 - (1 / 2) ^ (7 * p)) * 2 ^ n) ≤
      2 ^ ((36 * p + 2) * Q + 272 * p ^ 2 + 54 * p + 2) / 2 ^ n := by
  have h2 : 2 ^ (16 * p) + 1 ≤ 2 ^ (16 * p + 1) := by
    rw [pow_succ]; have := Nat.one_le_two_pow (n := 16 * p); omega
  have hnat : ℓ ^ (16 * p) * 2 ^ (16 * p) *
      (((2 ^ (16 * p) + 1) * M) ^ Q * (2 ^ (16 * p) + 1) ^ (Q + 16 * p + 1)) ≤
      2 ^ ((36 * p + 2) * Q + 272 * p ^ 2 + 48 * p + 1) := by
    calc ℓ ^ (16 * p) * 2 ^ (16 * p) *
          (((2 ^ (16 * p) + 1) * M) ^ Q * (2 ^ (16 * p) + 1) ^ (Q + 16 * p + 1))
        ≤ (2 ^ p) ^ (16 * p) * 2 ^ (16 * p) *
          ((2 ^ (16 * p + 1) * 2 ^ (4 * p)) ^ Q * (2 ^ (16 * p + 1)) ^ (Q + 16 * p + 1)) := by
          gcongr
      _ = 2 ^ ((36 * p + 2) * Q + 272 * p ^ 2 + 48 * p + 1) := by ring
  have hnat' : (ℓ : ℝ) ^ (16 * p) * 2 ^ (16 * p) *
      ((((2 ^ (16 * p) + 1) * M) ^ Q * (2 ^ (16 * p) + 1) ^ (Q + 16 * p + 1) : ℕ) : ℝ) ≤
      2 ^ ((36 * p + 2) * Q + 272 * p ^ 2 + 48 * p + 1) := by
    exact_mod_cast hnat
  have hden : (1 / 2 : ℝ) ^ (6 * p + 1) ≤ ((1 / 2 : ℝ) ^ (3 * p)) ^ 2 - (1 / 2) ^ (7 * p) := by
    have h7 : (1 / 2 : ℝ) ^ (7 * p) ≤ (1 / 2) ^ (6 * p + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h6 : ((1 / 2 : ℝ) ^ (3 * p)) ^ 2 = 2 * (1 / 2) ^ (6 * p + 1) := by
      rw [← pow_mul, pow_succ]; ring_nf
    linarith
  have hpos : (0 : ℝ) < (1 / 2) ^ (6 * p + 1) := by positivity
  calc (ℓ : ℝ) ^ (16 * p) * 2 ^ (16 * p) *
        ((((2 ^ (16 * p) + 1) * M) ^ Q * (2 ^ (16 * p) + 1) ^ (Q + 16 * p + 1) : ℕ) : ℝ) /
          ((((1 / 2 : ℝ) ^ (3 * p)) ^ 2 - (1 / 2) ^ (7 * p)) * 2 ^ n)
      ≤ 2 ^ ((36 * p + 2) * Q + 272 * p ^ 2 + 48 * p + 1) /
          ((1 / 2 : ℝ) ^ (6 * p + 1) * 2 ^ n) := by
        refine div_le_div₀ (by positivity) hnat' (by positivity) ?_
        exact mul_le_mul_of_nonneg_right hden (by positivity)
    _ = 2 ^ ((36 * p + 2) * Q + 272 * p ^ 2 + 54 * p + 2) / 2 ^ n := by
        rw [one_div_pow, div_mul_eq_mul_div, one_mul, div_div_eq_mul_div, ← pow_add]
        congr 2
        ring

/-- Under `4 t ≤ 2 ^ (3 p)`, the parameters `γ = 2 ^ (-3 p)` and `δ = 2 ^ (-7 p)` satisfy the
discriminator condition `t γ + (t + 1) δ < 1`. -/
private theorem discriminator_condition (hp : 1 ≤ p) {t : ℕ} (ht : 4 * t ≤ 2 ^ (3 * p)) :
    (t : ℝ) * (1 / 2) ^ (3 * p) + (t + 1) * (1 / 2) ^ (7 * p) < 1 := by
  set a : ℝ := (1 / 2) ^ (3 * p) with ha
  have ha0 : 0 < a := by positivity
  have ha8 : a ≤ 1 / 8 := by
    calc a ≤ (1 / 2) ^ 3 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 8 := by norm_num
  have hta : (t : ℝ) * a ≤ 1 / 4 := by
    have hcast : (4 : ℝ) * t ≤ 2 ^ (3 * p) := by exact_mod_cast ht
    rw [ha, one_div_pow, ← div_eq_mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  have h7 : (1 / 2 : ℝ) ^ (7 * p) ≤ a ^ 2 := by
    rw [ha, ← pow_mul]; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have : ((t : ℝ) + 1) * (1 / 2) ^ (7 * p) ≤ ((t : ℝ) + 1) * a ^ 2 :=
    mul_le_mul_of_nonneg_left h7 (by positivity)
  nlinarith

/-- The parameters `γ = 2 ^ (-3 p)` and `δ = 2 ^ (-7 p)` satisfy `δ < γ ^ 2`. -/
private theorem bias_lt_sq (hp : 1 ≤ p) :
    (1 / 2 : ℝ) ^ (7 * p) < ((1 / 2 : ℝ) ^ (3 * p)) ^ 2 := by
  rw [← pow_mul]
  exact pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (by omega)

/-- If `E + j ≤ n`, then `2 ^ E / 2 ^ n ≤ (1 / 2) ^ j`. -/
private theorem two_pow_div_two_pow_le {E j : ℕ} (h : E + j ≤ n) :
    (2 : ℝ) ^ E / 2 ^ n ≤ (1 / 2) ^ j := by
  rw [div_le_iff₀ (by positivity), one_div_pow, div_mul_eq_mul_div, one_mul,
    le_div_iff₀ (by positivity), ← pow_add]
  exact pow_le_pow_right₀ (by norm_num) h

/-- The survivor budget `Q = (n - R) / (36 p + 2)` satisfies `(36 p + 2) Q + R ≤ n` and
`n - R ≤ (36 p + 2) (Q + 1)`. -/
private theorem exists_survivorBudget {R : ℕ} (hR : R ≤ n) :
    ∃ Q : ℕ, (36 * p + 2) * Q + R ≤ n ∧ (n : ℝ) - R ≤ (36 * p + 2) * (Q + 1) := by
  refine ⟨(n - R) / (36 * p + 2), ?_, ?_⟩
  · have := Nat.mul_div_le (n - R) (36 * p + 2)
    omega
  · have h := (Nat.lt_mul_div_succ (n - R) (by omega : 0 < 36 * p + 2)).le
    have h' : ((n - R : ℕ) : ℝ) ≤ ((36 * p + 2) * ((n - R) / (36 * p + 2) + 1) : ℕ) := by
      exact_mod_cast h
    rw [Nat.cast_sub hR] at h'
    push_cast at h'
    exact h'

/-- **`MAJ ∘ THR ∘ THR` gate lower bound** at `k = 16 p` blocks (original, improving
[KaneWilliams2016], `arXiv:1511.07860v1`, Theorem 1.3 by one logarithmic factor): let the rows
`r : BitString (16 p) → BitString n` be `2 ^ (-7 p)`-biased (such rows exist,
`exists_isSmallBias_kaneWilliamsRows`), `n, ℓ ≤ 2 ^ p`, and let an unweighted threshold gate of
fan-in `t ≤ 2 ^ (3 p) / 4` over the outputs of a depth-two weighted threshold circuit `c` compute
the Kane–Williams function. Then `ℓ (n - 272 p ^ 2 - 54 p - 3) ≤ 304 p * c.size * √(n + 16 p ℓ)`.
With `p = ⌈log₂ n⌉` and `ℓ = n / (16 p)` this is `c.size = Ω(n ^ (3 / 2) / log² n)`. -/
theorem size_ge_of_threshold_eval_eq_kaneWilliamsB_of_le_two_pow {t : ℕ} (hp : 1 ≤ p)
    (hn : n ≤ 2 ^ p) (hℓ : 0 < ℓ) (hℓp : ℓ ≤ 2 ^ p) (ht : 4 * t ≤ 2 ^ (3 * p))
    {r : BitString (16 * p) → BitString n}
    (hr : IsSmallBias ((1 / 2) ^ (7 * p)) ((PMF.uniformOfFintype (BitString (16 * p))).map r))
    (c : Circuit signature (n + 16 * p * ℓ) t) (hd : c.depth ≤ 2) (θ : ℕ)
    (hc : ∀ y, threshold t θ (c.eval interpretation y) = kaneWilliamsB r ℓ y) :
    (ℓ : ℝ) * (n - (272 * p ^ 2 + 54 * p + 3)) ≤
      304 * p * c.size * Real.sqrt ((n + 16 * p * ℓ : ℕ) : ℝ) := by
  set S : ℝ := Real.sqrt ((n + 16 * p * ℓ : ℕ) : ℝ) with hS
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hS1 : (1 : ℝ) ≤ S :=
    Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ n + 16 * p * ℓ by nlinarith))
  have hℓ' : (ℓ : ℝ) ≤ 2 ^ p := by exact_mod_cast hℓp
  have hn' : (n : ℝ) ≤ 2 ^ p := by exact_mod_cast hn
  have hsize0 : (0 : ℝ) ≤ c.size := Nat.cast_nonneg _
  -- the bound is trivial for short messages
  by_cases hnR : n < 272 * p ^ 2 + 54 * p + 3
  · have hneg : (n : ℝ) - (272 * p ^ 2 + 54 * p + 3) ≤ 0 := by
      have : (n : ℝ) < ((272 * p ^ 2 + 54 * p + 3 : ℕ) : ℝ) := by exact_mod_cast hnR
      push_cast at this
      linarith
    exact (mul_nonpos_of_nonneg_of_nonpos hℓ0.le hneg).trans (by positivity)
  push Not at hnR
  have hlhs : (ℓ : ℝ) * (n - (272 * p ^ 2 + 54 * p + 3)) ≤ 2 ^ p * 2 ^ p :=
    mul_le_mul hℓ' (by linarith [(by positivity : (0 : ℝ) ≤ 272 * p ^ 2 + 54 * p + 3)])
      (by have : ((272 * p ^ 2 + 54 * p + 3 : ℕ) : ℝ) ≤ n := by exact_mod_cast hnR
          push_cast at this; linarith) (by positivity)
  -- and for circuits with more than `2 ^ (4 p)` gates
  by_cases hM : 2 ^ (4 * p) < c.size + 1
  · have hs : (2 : ℝ) ^ (4 * p) ≤ c.size := by exact_mod_cast (show 2 ^ (4 * p) ≤ c.size by omega)
    have hpow : (2 : ℝ) ^ p * 2 ^ p ≤ 2 ^ (4 * p) := by
      rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    calc (ℓ : ℝ) * (n - (272 * p ^ 2 + 54 * p + 3)) ≤ c.size := (hlhs.trans hpow).trans hs
      _ ≤ c.size * S := le_mul_of_one_le_right hsize0 hS1
      _ ≤ 304 * p * (c.size * S) := le_mul_of_one_le_left (by positivity) (by linarith)
      _ = 304 * p * c.size * S := by ring
  push Not at hM
  -- choose the survivor budget `Q` as large as the counting allows
  obtain ⟨Q, hQ1, hQ2⟩ := exists_survivorBudget (p := p) hnR
  push_cast at hQ2
  have hmain := one_le_of_threshold_eval_eq_kaneWilliamsB_size hℓ (by positivity) (by positivity)
    (pow_le_one₀ (by norm_num) (by norm_num)) (bias_lt_sq hp) (discriminator_condition hp ht)
    hr c hd θ hc Q
  have hCT := (countTerm_le (n := n) hp hℓp hM Q).trans
    (two_pow_div_two_pow_le (j := 1) (by omega))
  rw [pow_one] at hCT
  -- so many survivors are expected: `(Q + 1) ℓ ≤ 8 c.size √N`
  have hB : (Q + 1 : ℝ) * ℓ ≤ 8 * c.size * S := by
    have h1 : (1 / 2 : ℝ) ≤ 4 * (1 / (ℓ : ℝ)) * c.size * S / (Q + 1) := by linarith
    rw [le_div_iff₀ (by positivity)] at h1
    have h2 : 4 * (1 / (ℓ : ℝ)) * c.size * S * ℓ = 4 * c.size * S := by field_simp
    nlinarith
  calc (ℓ : ℝ) * (n - (272 * p ^ 2 + 54 * p + 3)) ≤ ℓ * ((36 * p + 2) * (Q + 1)) :=
        mul_le_mul_of_nonneg_left hQ2 hℓ0.le
    _ = (36 * p + 2) * ((Q + 1 : ℝ) * ℓ) := by ring
    _ ≤ (36 * p + 2) * (8 * c.size * S) := mul_le_mul_of_nonneg_left hB (by positivity)
    _ = (288 * p + 16) * (c.size * S) := by ring
    _ ≤ 304 * p * (c.size * S) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 304 * p * c.size * S := by ring

/-- **`MAJ ∘ THR ∘ THR` wire lower bound** at `k = 16 p` blocks (original, improving
[KaneWilliams2016], `arXiv:1511.07860v1`, Theorem 1.3 by one logarithmic factor): under the
hypotheses of `size_ge_of_threshold_eval_eq_kaneWilliamsB_of_le_two_pow`,
`ℓ √ℓ (n - 272 p ^ 2 - 54 p - 3) ≤ 304 p * c.wireCount`. The `t` wires of the top gate are not
counted. With `p = ⌈log₂ n⌉` and `ℓ = n / (16 p)` this is
`c.wireCount = Ω(n ^ (5 / 2) / log^(5/2) n)`. -/
theorem wireCount_ge_of_threshold_eval_eq_kaneWilliamsB_of_le_two_pow {t : ℕ} (hp : 1 ≤ p)
    (hn : n ≤ 2 ^ p) (hℓ : 0 < ℓ) (hℓp : ℓ ≤ 2 ^ p) (ht : 4 * t ≤ 2 ^ (3 * p))
    {r : BitString (16 * p) → BitString n}
    (hr : IsSmallBias ((1 / 2) ^ (7 * p)) ((PMF.uniformOfFintype (BitString (16 * p))).map r))
    (c : Circuit signature (n + 16 * p * ℓ) t) (hd : c.depth ≤ 2) (θ : ℕ)
    (hc : ∀ y, threshold t θ (c.eval interpretation y) = kaneWilliamsB r ℓ y) :
    (ℓ : ℝ) * Real.sqrt ℓ * (n - (272 * p ^ 2 + 54 * p + 3)) ≤ 304 * p * c.wireCount := by
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hℓ' : (ℓ : ℝ) ≤ 2 ^ p := by exact_mod_cast hℓp
  have hn' : (n : ℝ) ≤ 2 ^ p := by exact_mod_cast hn
  have hsℓ : Real.sqrt ℓ ≤ ℓ := (Real.sqrt_le_left hℓ0.le).mpr (by nlinarith)
  have hsℓ0 : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ0
  have hw0 : (0 : ℝ) ≤ c.wireCount := Nat.cast_nonneg _
  by_cases hnR : n < 272 * p ^ 2 + 54 * p + 3
  · have hneg : (n : ℝ) - (272 * p ^ 2 + 54 * p + 3) ≤ 0 := by
      have : (n : ℝ) < ((272 * p ^ 2 + 54 * p + 3 : ℕ) : ℝ) := by exact_mod_cast hnR
      push_cast at this
      linarith
    exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg).trans (by positivity)
  push Not at hnR
  have hlhs : (ℓ : ℝ) * Real.sqrt ℓ * (n - (272 * p ^ 2 + 54 * p + 3)) ≤
      2 ^ p * 2 ^ p * 2 ^ p :=
    mul_le_mul (mul_le_mul hℓ' (hsℓ.trans hℓ') hsℓ0.le (by positivity))
      (by linarith [(by positivity : (0 : ℝ) ≤ 272 * p ^ 2 + 54 * p + 3)])
      (by have : ((272 * p ^ 2 + 54 * p + 3 : ℕ) : ℝ) ≤ n := by exact_mod_cast hnR
          push_cast at this; linarith) (by positivity)
  by_cases hM : 2 ^ (4 * p) < c.wireCount + 1
  · have hs : (2 : ℝ) ^ (4 * p) ≤ c.wireCount := by
      exact_mod_cast (show 2 ^ (4 * p) ≤ c.wireCount by omega)
    have hpow : (2 : ℝ) ^ p * 2 ^ p * 2 ^ p ≤ 2 ^ (4 * p) := by
      rw [← pow_add, ← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    calc (ℓ : ℝ) * Real.sqrt ℓ * (n - (272 * p ^ 2 + 54 * p + 3)) ≤ c.wireCount :=
          (hlhs.trans hpow).trans hs
      _ ≤ 304 * p * c.wireCount := le_mul_of_one_le_left hw0 (by linarith)
  push Not at hM
  obtain ⟨Q, hQ1, hQ2⟩ := exists_survivorBudget (p := p) hnR
  push_cast at hQ2
  have hmain := one_le_of_threshold_eval_eq_kaneWilliamsB_wireCount hℓ (by positivity)
    (by positivity) (pow_le_one₀ (by norm_num) (by norm_num)) (bias_lt_sq hp)
    (discriminator_condition hp ht) hr c hd θ hc Q
  have hCT := (countTerm_le (n := n) hp hℓp hM Q).trans
    (two_pow_div_two_pow_le (j := 1) (by omega))
  rw [pow_one] at hCT
  have hB : (Q + 1 : ℝ) * (ℓ * Real.sqrt ℓ) ≤ 8 * c.wireCount := by
    have h1 : (1 / 2 : ℝ) ≤ 4 * (c.wireCount : ℝ) * (1 / (ℓ : ℝ)) * Real.sqrt (1 / (ℓ : ℝ)) /
        (Q + 1) := by linarith
    rw [le_div_iff₀ (by positivity)] at h1
    have h2 : 4 * (c.wireCount : ℝ) * (1 / (ℓ : ℝ)) * Real.sqrt (1 / (ℓ : ℝ)) *
        (ℓ * Real.sqrt ℓ) = 4 * c.wireCount := by
      rw [Real.sqrt_div' _ hℓ0.le, Real.sqrt_one]
      field_simp
    nlinarith [mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ ℓ * Real.sqrt ℓ)]
  calc (ℓ : ℝ) * Real.sqrt ℓ * (n - (272 * p ^ 2 + 54 * p + 3)) ≤
        ℓ * Real.sqrt ℓ * ((36 * p + 2) * (Q + 1)) :=
        mul_le_mul_of_nonneg_left hQ2 (by positivity)
    _ = (36 * p + 2) * ((Q + 1 : ℝ) * (ℓ * Real.sqrt ℓ)) := by ring
    _ ≤ (36 * p + 2) * (8 * c.wireCount) := mul_le_mul_of_nonneg_left hB (by positivity)
    _ = (288 * p + 16) * c.wireCount := by ring
    _ ≤ 304 * p * c.wireCount := mul_le_mul_of_nonneg_right (by linarith) hw0

/-- **Average-case gate bound** at `k = 16 p` blocks (original; [KaneWilliams2016] state no
average-case bound for this function): under `2 ^ (-7 p)`-biased rows, `n, ℓ ≤ 2 ^ p` and
`n > 272 p ^ 2 + 57 p + 3`, a depth-two weighted threshold circuit agrees with the Kane–Williams
function on at most a
`1 / 2 + 2 ^ (-3 p) + 152 p * c.size * √(n + 16 p ℓ) / (ℓ (n - 272 p ^ 2 - 57 p - 3))`
fraction of the inputs. With `p = ⌈log₂ n⌉` and `ℓ = n / (16 p)` this is
`1 / 2 + O(c.size log² n / n ^ (3 / 2)) + n ^ (-3)`. -/
theorem card_eval_eq_kaneWilliamsB_le_of_le_two_pow_size (hp : 1 ≤ p) (hn : n ≤ 2 ^ p)
    (hℓ : 0 < ℓ) (hℓp : ℓ ≤ 2 ^ p) (hnR : 272 * p ^ 2 + 57 * p + 3 < n)
    {r : BitString (16 * p) → BitString n}
    (hr : IsSmallBias ((1 / 2) ^ (7 * p)) ((PMF.uniformOfFintype (BitString (16 * p))).map r))
    (c : Circuit signature (n + 16 * p * ℓ) 1) (hd : c.depth ≤ 2) (o : Fin 1) :
    (#{y | c.eval interpretation y o = kaneWilliamsB r ℓ y} : ℝ) ≤ 2 ^ (n + 16 * p * ℓ) *
      (1 / 2 + (1 / 2) ^ (3 * p) + 152 * p * c.size * Real.sqrt ((n + 16 * p * ℓ : ℕ) : ℝ) /
        (ℓ * (n - (272 * p ^ 2 + 57 * p + 3)))) := by
  classical
  set S : ℝ := Real.sqrt ((n + 16 * p * ℓ : ℕ) : ℝ) with hS
  set D : ℝ := (n : ℝ) - (272 * p ^ 2 + 57 * p + 3) with hDdef
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hℓ' : (ℓ : ℝ) ≤ 2 ^ p := by exact_mod_cast hℓp
  have hn' : (n : ℝ) ≤ 2 ^ p := by exact_mod_cast hn
  have hS1 : (1 : ℝ) ≤ S :=
    Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ n + 16 * p * ℓ by omega))
  have hsize0 : (0 : ℝ) ≤ c.size := Nat.cast_nonneg _
  have hD : 0 < D := by
    have : ((272 * p ^ 2 + 57 * p + 3 : ℕ) : ℝ) < n := by exact_mod_cast hnR
    push_cast at this
    linarith
  have hall : (#{y | c.eval interpretation y o = kaneWilliamsB r ℓ y} : ℝ) ≤
      2 ^ (n + 16 * p * ℓ) := by
    exact_mod_cast (card_le_univ _).trans_eq (by simp)
  have h3 : (0 : ℝ) ≤ (1 / 2) ^ (3 * p) := by positivity
  by_cases hM : 2 ^ (4 * p) < c.size + 1
  · -- a circuit with more than `2 ^ (4 p)` gates makes the bound trivial
    have hs : (2 : ℝ) ^ (4 * p) ≤ c.size := by exact_mod_cast (show 2 ^ (4 * p) ≤ c.size by omega)
    have hpow : (2 : ℝ) ^ p * 2 ^ p ≤ 2 ^ (4 * p) := by
      rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hden : (ℓ : ℝ) * D ≤ 2 ^ p * 2 ^ p :=
      mul_le_mul hℓ' (by linarith [(by positivity : (0 : ℝ) ≤ 272 * p ^ 2 + 57 * p + 3)])
        hD.le (by positivity)
    have hterm : 1 ≤ 152 * p * c.size * S / (ℓ * D) := by
      rw [le_div_iff₀ (by positivity), one_mul]
      calc (ℓ : ℝ) * D ≤ c.size := (hden.trans hpow).trans hs
        _ ≤ c.size * S := le_mul_of_one_le_right hsize0 hS1
        _ ≤ 152 * p * (c.size * S) := le_mul_of_one_le_left (by positivity) (by linarith)
        _ = 152 * p * c.size * S := by ring
    exact hall.trans (le_mul_of_one_le_right (by positivity) (by linarith))
  push Not at hM
  obtain ⟨Q, hQ1, hQ2⟩ := exists_survivorBudget (p := p) hnR.le
  push_cast at hQ2
  have hmain := card_eval_eq_kaneWilliamsB_le_of_depth_le_two_size hℓ (by positivity)
    (by positivity) (bias_lt_sq hp) hr c hd o Q
  have hCT := (countTerm_le (n := n) hp hℓp hM Q).trans
    (two_pow_div_two_pow_le (j := 3 * p + 1) (by omega))
  have hγ : (1 + (1 / 2 : ℝ) ^ (3 * p)) / 2 + (1 / 2) ^ (3 * p + 1) =
      1 / 2 + (1 / 2) ^ (3 * p) := by
    rw [pow_succ]; ring
  -- the survivor term
  have hsurv : 4 * (1 / (ℓ : ℝ)) * c.size * S / (Q + 1) ≤ 152 * p * c.size * S / (ℓ * D) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hkey : 4 * (1 / (ℓ : ℝ)) * c.size * S * (ℓ * D) = 4 * (c.size * S) * D := by
      field_simp
    rw [hkey]
    calc 4 * (c.size * S) * D ≤ 4 * (c.size * S) * ((36 * p + 2) * (Q + 1)) :=
          mul_le_mul_of_nonneg_left hQ2 (by positivity)
      _ = (144 * p + 8) * ((c.size * S) * (Q + 1)) := by ring
      _ ≤ 152 * p * ((c.size * S) * (Q + 1)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 152 * p * c.size * S * (Q + 1) := by ring
  refine hmain.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  linarith

/-- **Average-case wire bound** at `k = 16 p` blocks (original): under the hypotheses of
`card_eval_eq_kaneWilliamsB_le_of_le_two_pow_size`, a depth-two weighted threshold circuit agrees
with the Kane–Williams function on at most a
`1 / 2 + 2 ^ (-3 p) + 152 p * c.wireCount / (ℓ √ℓ (n - 272 p ^ 2 - 57 p - 3))` fraction of the
inputs; with `p = ⌈log₂ n⌉` and `ℓ = n / (16 p)` this is
`1 / 2 + O(c.wireCount log^(5/2) n / n ^ (5 / 2)) + n ^ (-3)`. -/
theorem card_eval_eq_kaneWilliamsB_le_of_le_two_pow_wireCount (hp : 1 ≤ p) (hn : n ≤ 2 ^ p)
    (hℓ : 0 < ℓ) (hℓp : ℓ ≤ 2 ^ p) (hnR : 272 * p ^ 2 + 57 * p + 3 < n)
    {r : BitString (16 * p) → BitString n}
    (hr : IsSmallBias ((1 / 2) ^ (7 * p)) ((PMF.uniformOfFintype (BitString (16 * p))).map r))
    (c : Circuit signature (n + 16 * p * ℓ) 1) (hd : c.depth ≤ 2) (o : Fin 1) :
    (#{y | c.eval interpretation y o = kaneWilliamsB r ℓ y} : ℝ) ≤ 2 ^ (n + 16 * p * ℓ) *
      (1 / 2 + (1 / 2) ^ (3 * p) + 152 * p * c.wireCount /
        (ℓ * Real.sqrt ℓ * (n - (272 * p ^ 2 + 57 * p + 3)))) := by
  classical
  set D : ℝ := (n : ℝ) - (272 * p ^ 2 + 57 * p + 3) with hDdef
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hℓ' : (ℓ : ℝ) ≤ 2 ^ p := by exact_mod_cast hℓp
  have hn' : (n : ℝ) ≤ 2 ^ p := by exact_mod_cast hn
  have hsℓ : Real.sqrt ℓ ≤ ℓ := (Real.sqrt_le_left hℓ0.le).mpr (by nlinarith)
  have hsℓ0 : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ0
  have hw0 : (0 : ℝ) ≤ c.wireCount := Nat.cast_nonneg _
  have hD : 0 < D := by
    have : ((272 * p ^ 2 + 57 * p + 3 : ℕ) : ℝ) < n := by exact_mod_cast hnR
    push_cast at this
    linarith
  have hall : (#{y | c.eval interpretation y o = kaneWilliamsB r ℓ y} : ℝ) ≤
      2 ^ (n + 16 * p * ℓ) := by
    exact_mod_cast (card_le_univ _).trans_eq (by simp)
  have h3 : (0 : ℝ) ≤ (1 / 2) ^ (3 * p) := by positivity
  by_cases hM : 2 ^ (4 * p) < c.wireCount + 1
  · have hs : (2 : ℝ) ^ (4 * p) ≤ c.wireCount := by
      exact_mod_cast (show 2 ^ (4 * p) ≤ c.wireCount by omega)
    have hpow : (2 : ℝ) ^ p * 2 ^ p * 2 ^ p ≤ 2 ^ (4 * p) := by
      rw [← pow_add, ← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hden : (ℓ : ℝ) * Real.sqrt ℓ * D ≤ 2 ^ p * 2 ^ p * 2 ^ p :=
      mul_le_mul (mul_le_mul hℓ' (hsℓ.trans hℓ') hsℓ0.le (by positivity))
        (by linarith [(by positivity : (0 : ℝ) ≤ 272 * p ^ 2 + 57 * p + 3)]) hD.le
        (by positivity)
    have hterm : 1 ≤ 152 * p * c.wireCount / (ℓ * Real.sqrt ℓ * D) := by
      rw [le_div_iff₀ (by positivity), one_mul]
      calc (ℓ : ℝ) * Real.sqrt ℓ * D ≤ c.wireCount := (hden.trans hpow).trans hs
        _ ≤ 152 * p * c.wireCount := le_mul_of_one_le_left hw0 (by linarith)
    exact hall.trans (le_mul_of_one_le_right (by positivity) (by linarith))
  push Not at hM
  obtain ⟨Q, hQ1, hQ2⟩ := exists_survivorBudget (p := p) hnR.le
  push_cast at hQ2
  have hmain := card_eval_eq_kaneWilliamsB_le_of_depth_le_two_wireCount hℓ (by positivity)
    (by positivity) (bias_lt_sq hp) hr c hd o Q
  have hCT := (countTerm_le (n := n) hp hℓp hM Q).trans
    (two_pow_div_two_pow_le (j := 3 * p + 1) (by omega))
  have hγ : (1 + (1 / 2 : ℝ) ^ (3 * p)) / 2 + (1 / 2) ^ (3 * p + 1) =
      1 / 2 + (1 / 2) ^ (3 * p) := by
    rw [pow_succ]; ring
  have hsurv : 4 * (c.wireCount : ℝ) * (1 / (ℓ : ℝ)) * Real.sqrt (1 / (ℓ : ℝ)) / (Q + 1) ≤
      152 * p * c.wireCount / (ℓ * Real.sqrt ℓ * D) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hkey : 4 * (c.wireCount : ℝ) * (1 / (ℓ : ℝ)) * Real.sqrt (1 / (ℓ : ℝ)) *
        (ℓ * Real.sqrt ℓ * D) = 4 * c.wireCount * D := by
      rw [Real.sqrt_div' _ hℓ0.le, Real.sqrt_one]
      field_simp
    rw [hkey]
    calc 4 * (c.wireCount : ℝ) * D ≤ 4 * (c.wireCount : ℝ) * ((36 * p + 2) * (Q + 1)) :=
          mul_le_mul_of_nonneg_left hQ2 (by positivity)
      _ = (144 * p + 8) * ((c.wireCount : ℝ) * (Q + 1)) := by ring
      _ ≤ 152 * p * ((c.wireCount : ℝ) * (Q + 1)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 152 * p * c.wireCount * (Q + 1) := by ring
  refine hmain.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  linarith

/-! ### The balanced function on `2 n` inputs -/

/-- In the balanced case `n = 16 p ℓ ≤ 2 ^ p`, also `ℓ ≤ 2 ^ p`. -/
private theorem le_two_pow_of_balanced (hp : 1 ≤ p) (hnℓ : n = 16 * p * ℓ) (hn : n ≤ 2 ^ p) :
    ℓ ≤ 2 ^ p :=
  calc ℓ ≤ 16 * p * ℓ := Nat.le_mul_of_pos_left ℓ (by omega)
    _ = n := hnℓ.symm
    _ ≤ 2 ^ p := hn

/-- In the balanced case `n = 16 p ℓ`, `√n = 4 √p √ℓ`. -/
private theorem sqrt_balanced (hnℓ : n = 16 * p * ℓ) :
    Real.sqrt n = 4 * Real.sqrt p * Real.sqrt ℓ := by
  have h16 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hnℓ, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat,
    Real.sqrt_mul (show (0 : ℝ) ≤ 16 * p by positivity),
    Real.sqrt_mul (show (0 : ℝ) ≤ 16 by norm_num), h16]

/-- **`MAJ ∘ THR ∘ THR` gate lower bound for the balanced function** (original, improving
[KaneWilliams2016], `arXiv:1511.07860v1`, Theorem 1.3 from `Ω(n ^ (3 / 2) / log³ n)` to
`Ω(n ^ (3 / 2) / log² n)` gates): as in [KaneWilliams2016], Definition 6.1, let the message and
the block bits have `n` bits each, here `k = 16 p` blocks of `ℓ` bits with `n = 16 p ℓ ≤ 2 ^ p`,
and let the rows be `2 ^ (-7 p)`-biased (such rows exist, `exists_isSmallBias_kaneWilliamsRows`).
If an unweighted threshold gate of fan-in `t ≤ n ^ 3 / 4` over the outputs of a depth-two weighted
threshold circuit `c` computes the Kane–Williams function, then
`n (n - 272 p ^ 2 - 54 p - 3) ≤ 4864 p ^ 2 * c.size * √(2 n)`.
For `p ≥ 9` and `ℓ = ⌊2 ^ p / (16 p)⌋`, `2 ^ (p - 1) < n ≤ 2 ^ p`, so `p = ⌈log₂ n⌉` and
`c.size ≥ (1 - o(1)) n ^ (3 / 2) / (4864 √2 log₂² n)`. -/
theorem size_ge_of_threshold_eval_eq_kaneWilliamsB_balanced {t : ℕ} (hp : 1 ≤ p)
    (hnℓ : n = 16 * p * ℓ) (hn : n ≤ 2 ^ p) (ht : 4 * t ≤ n ^ 3)
    {r : BitString (16 * p) → BitString n}
    (hr : IsSmallBias ((1 / 2) ^ (7 * p)) ((PMF.uniformOfFintype (BitString (16 * p))).map r))
    (c : Circuit signature (n + 16 * p * ℓ) t) (hd : c.depth ≤ 2) (θ : ℕ)
    (hc : ∀ y, threshold t θ (c.eval interpretation y) = kaneWilliamsB r ℓ y) :
    (n : ℝ) * (n - (272 * p ^ 2 + 54 * p + 3)) ≤
      4864 * p ^ 2 * c.size * Real.sqrt (2 * n) := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · have hn0 : n = 0 := by simpa using hnℓ
    subst hn0
    simp only [Nat.cast_zero, zero_mul]
    positivity
  have ht' : 4 * t ≤ 2 ^ (3 * p) := ht.trans (by rw [pow_mul']; exact Nat.pow_le_pow_left hn 3)
  have h := size_ge_of_threshold_eval_eq_kaneWilliamsB_of_le_two_pow hp hn hℓ
    (le_two_pow_of_balanced hp hnℓ hn) ht' hr c hd θ hc
  have hN : ((n + 16 * p * ℓ : ℕ) : ℝ) = 2 * n := by rw [← hnℓ]; push_cast; ring
  rw [hN] at h
  have hn' : (n : ℝ) = 16 * p * ℓ := by exact_mod_cast hnℓ
  calc (n : ℝ) * (n - (272 * p ^ 2 + 54 * p + 3)) =
        16 * p * (ℓ * (n - (272 * p ^ 2 + 54 * p + 3))) := by nth_rewrite 1 [hn']; ring
    _ ≤ 16 * p * (304 * p * c.size * Real.sqrt (2 * n)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 4864 * p ^ 2 * c.size * Real.sqrt (2 * n) := by ring

/-- **`MAJ ∘ THR ∘ THR` wire lower bound for the balanced function** (original, improving
[KaneWilliams2016], `arXiv:1511.07860v1`, Theorem 1.3 from `Ω(n ^ (5 / 2) / log^(7/2) n)` to
`Ω(n ^ (5 / 2) / log^(5/2) n)` wires): under the hypotheses of
`size_ge_of_threshold_eval_eq_kaneWilliamsB_balanced`,
`n √n (n - 272 p ^ 2 - 54 p - 3) ≤ 19456 p ^ 2 √p * c.wireCount`. The `t` wires of the top gate
are not counted. -/
theorem wireCount_ge_of_threshold_eval_eq_kaneWilliamsB_balanced {t : ℕ} (hp : 1 ≤ p)
    (hnℓ : n = 16 * p * ℓ) (hn : n ≤ 2 ^ p) (ht : 4 * t ≤ n ^ 3)
    {r : BitString (16 * p) → BitString n}
    (hr : IsSmallBias ((1 / 2) ^ (7 * p)) ((PMF.uniformOfFintype (BitString (16 * p))).map r))
    (c : Circuit signature (n + 16 * p * ℓ) t) (hd : c.depth ≤ 2) (θ : ℕ)
    (hc : ∀ y, threshold t θ (c.eval interpretation y) = kaneWilliamsB r ℓ y) :
    (n : ℝ) * Real.sqrt n * (n - (272 * p ^ 2 + 54 * p + 3)) ≤
      19456 * p ^ 2 * Real.sqrt p * c.wireCount := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · have hn0 : n = 0 := by simpa using hnℓ
    subst hn0
    simp only [Nat.cast_zero, zero_mul]
    positivity
  have ht' : 4 * t ≤ 2 ^ (3 * p) := ht.trans (by rw [pow_mul']; exact Nat.pow_le_pow_left hn 3)
  have h := wireCount_ge_of_threshold_eval_eq_kaneWilliamsB_of_le_two_pow hp hn hℓ
    (le_two_pow_of_balanced hp hnℓ hn) ht' hr c hd θ hc
  have hn' : (n : ℝ) = 16 * p * ℓ := by exact_mod_cast hnℓ
  rw [sqrt_balanced hnℓ]
  calc (n : ℝ) * (4 * Real.sqrt p * Real.sqrt ℓ) * (n - (272 * p ^ 2 + 54 * p + 3)) =
        64 * p * Real.sqrt p * (ℓ * Real.sqrt ℓ * (n - (272 * p ^ 2 + 54 * p + 3))) := by
        nth_rewrite 1 [hn']; ring
    _ ≤ 64 * p * Real.sqrt p * (304 * p * c.wireCount) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 19456 * p ^ 2 * Real.sqrt p * c.wireCount := by ring

/-- **Average-case gate bound for the balanced function** (original; [KaneWilliams2016] state no
average-case bound for this function): with `n = 16 p ℓ ≤ 2 ^ p`, `2 ^ (-7 p)`-biased rows and
`n > 272 p ^ 2 + 57 p + 3`, a depth-two weighted threshold circuit agrees with the Kane–Williams
function on at most a
`1 / 2 + 2 ^ (-3 p) + 2432 p ^ 2 * c.size * √(2 n) / (n (n - 272 p ^ 2 - 57 p - 3))` fraction of
the `2 ^ (2 n)` inputs. With `p = ⌈log₂ n⌉` this is
`1 / 2 + O(c.size log² n / n ^ (3 / 2)) + n ^ (-3)`. -/
theorem card_eval_eq_kaneWilliamsB_le_balanced_size (hp : 1 ≤ p) (hnℓ : n = 16 * p * ℓ)
    (hn : n ≤ 2 ^ p) (hnR : 272 * p ^ 2 + 57 * p + 3 < n)
    {r : BitString (16 * p) → BitString n}
    (hr : IsSmallBias ((1 / 2) ^ (7 * p)) ((PMF.uniformOfFintype (BitString (16 * p))).map r))
    (c : Circuit signature (n + 16 * p * ℓ) 1) (hd : c.depth ≤ 2) (o : Fin 1) :
    (#{y | c.eval interpretation y o = kaneWilliamsB r ℓ y} : ℝ) ≤ 2 ^ (2 * n) *
      (1 / 2 + (1 / 2) ^ (3 * p) + 2432 * p ^ 2 * c.size * Real.sqrt (2 * n) /
        (n * (n - (272 * p ^ 2 + 57 * p + 3)))) := by
  have hℓ : 0 < ℓ := Nat.pos_of_ne_zero fun h0 => by subst h0; omega
  have h := card_eval_eq_kaneWilliamsB_le_of_le_two_pow_size hp hn hℓ
    (le_two_pow_of_balanced hp hnℓ hn) hnR hr c hd o
  have h2n : n + 16 * p * ℓ = 2 * n := by omega
  have hpow : (2 : ℝ) ^ (n + 16 * p * ℓ) = 2 ^ (2 * n) := by rw [h2n]
  have hN : ((n + 16 * p * ℓ : ℕ) : ℝ) = 2 * n := by rw [h2n]; push_cast; ring
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hD : (0 : ℝ) < n - (272 * p ^ 2 + 57 * p + 3) := by
    have : ((272 * p ^ 2 + 57 * p + 3 : ℕ) : ℝ) < n := by exact_mod_cast hnR
    push_cast at this
    linarith
  have hn' : (n : ℝ) = 16 * p * ℓ := by exact_mod_cast hnℓ
  have hfrac : 152 * p * c.size * Real.sqrt ((n + 16 * p * ℓ : ℕ) : ℝ) /
      (ℓ * (n - (272 * p ^ 2 + 57 * p + 3))) =
      2432 * p ^ 2 * c.size * Real.sqrt (2 * n) / (n * (n - (272 * p ^ 2 + 57 * p + 3))) := by
    rw [hN, div_eq_div_iff (mul_pos hℓ0 hD).ne' (mul_pos hn0 hD).ne', hn']
    ring
  rwa [hpow, hfrac] at h

/-- **Average-case wire bound for the balanced function** (original): under the hypotheses of
`card_eval_eq_kaneWilliamsB_le_balanced_size`, a depth-two weighted threshold circuit agrees with
the Kane–Williams function on at most a
`1 / 2 + 2 ^ (-3 p) + 9728 p ^ 2 √p * c.wireCount / (n √n (n - 272 p ^ 2 - 57 p - 3))` fraction
of the inputs, that is, `1 / 2 + O(c.wireCount log^(5/2) n / n ^ (5 / 2)) + n ^ (-3)`. -/
theorem card_eval_eq_kaneWilliamsB_le_balanced_wireCount (hp : 1 ≤ p) (hnℓ : n = 16 * p * ℓ)
    (hn : n ≤ 2 ^ p) (hnR : 272 * p ^ 2 + 57 * p + 3 < n)
    {r : BitString (16 * p) → BitString n}
    (hr : IsSmallBias ((1 / 2) ^ (7 * p)) ((PMF.uniformOfFintype (BitString (16 * p))).map r))
    (c : Circuit signature (n + 16 * p * ℓ) 1) (hd : c.depth ≤ 2) (o : Fin 1) :
    (#{y | c.eval interpretation y o = kaneWilliamsB r ℓ y} : ℝ) ≤ 2 ^ (2 * n) *
      (1 / 2 + (1 / 2) ^ (3 * p) + 9728 * p ^ 2 * Real.sqrt p * c.wireCount /
        (n * Real.sqrt n * (n - (272 * p ^ 2 + 57 * p + 3)))) := by
  have hℓ : 0 < ℓ := Nat.pos_of_ne_zero fun h0 => by subst h0; omega
  have h := card_eval_eq_kaneWilliamsB_le_of_le_two_pow_wireCount hp hn hℓ
    (le_two_pow_of_balanced hp hnℓ hn) hnR hr c hd o
  have h2n : n + 16 * p * ℓ = 2 * n := by omega
  have hpow : (2 : ℝ) ^ (n + 16 * p * ℓ) = 2 ^ (2 * n) := by rw [h2n]
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hD : (0 : ℝ) < n - (272 * p ^ 2 + 57 * p + 3) := by
    have : ((272 * p ^ 2 + 57 * p + 3 : ℕ) : ℝ) < n := by exact_mod_cast hnR
    push_cast at this
    linarith
  have hsℓ : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ0
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hn' : (n : ℝ) = 16 * p * ℓ := by exact_mod_cast hnℓ
  have hfrac : 152 * p * c.wireCount / (ℓ * Real.sqrt ℓ * (n - (272 * p ^ 2 + 57 * p + 3))) =
      9728 * p ^ 2 * Real.sqrt p * c.wireCount /
        (n * Real.sqrt n * (n - (272 * p ^ 2 + 57 * p + 3))) := by
    have hden : (0 : ℝ) < n * (4 * Real.sqrt p * Real.sqrt ℓ) * (n - (272 * p ^ 2 + 57 * p + 3)) :=
      mul_pos (mul_pos (by rw [hn']; positivity) (by positivity)) hD
    rw [sqrt_balanced hnℓ, div_eq_div_iff (mul_pos (mul_pos hℓ0 hsℓ) hD).ne' hden.ne', hn']
    ring
  rwa [hpow, hfrac] at h

/-- **Rows exist**: for `p ≥ 1` and `n ≤ 2 ^ p` there are `2 ^ (-7 p)`-biased rows
`r : BitString (16 p) → BitString n`, namely the powering construction of
[Alon, Goldreich, Håstad and Peralta][AlonGoldreichHastadPeralta1992] over a field with
`2 ^ (8 p)` elements (`Cslib.BitString.exists_isSmallBias_uniformOfFintype_map`), whose bias is at
most `(n - 1) / 2 ^ (8 p)`. Its efficient computation is not certified here. -/
theorem exists_isSmallBias_kaneWilliamsRows (hp : 1 ≤ p) (hn : n ≤ 2 ^ p) :
    ∃ r : BitString (16 * p) → BitString n,
      IsSmallBias ((1 / 2) ^ (7 * p)) ((PMF.uniformOfFintype (BitString (16 * p))).map r) := by
  obtain ⟨g, hg⟩ := exists_isSmallBias_uniformOfFintype_map n (m := 8 * p) (by omega)
  let e : BitString (16 * p) ≃ BitString (2 * (8 * p)) :=
    Equiv.arrowCongr (finCongr (by ring)) (Equiv.refl Bool)
  refine ⟨g ∘ e, ?_⟩
  rw [← PMF.map_comp, PMF.uniformOfFintype_map_equiv]
  refine hg.mono ?_
  have hn1 : ((n - 1 : ℕ) : ℝ) ≤ 2 ^ p := by exact_mod_cast (Nat.sub_le n 1).trans hn
  rw [one_div_pow, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  calc ((n - 1 : ℕ) : ℝ) * 2 ^ (7 * p) ≤ 2 ^ p * 2 ^ (7 * p) :=
        mul_le_mul_of_nonneg_right hn1 (by positivity)
    _ = 2 ^ (8 * p) := by rw [← pow_add]; ring_nf

end Concrete

end Cslib.Circuits.Boolean.WeightedThreshold
