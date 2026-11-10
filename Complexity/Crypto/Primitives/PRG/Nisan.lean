/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.BranchingProgram.ReadOnce
public import Complexity.Probability.PairwiseIndependentHash
public import Cslib.Crypto.Primitives.PRG.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Complexity.Crypto.Primitives.PRG.NisanWigderson.Sampling
import Complexity.Foundations.Data.Finset.Expect
import Complexity.Foundations.Data.List.FoldlIdx
import Complexity.Probability.PairwiseIndependentHash.Mixing
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Nisan's generator for read-once branching programs

Nisan's generator [Nisan1992] stretches a seed consisting of a block `x : X` and `k` seeds
`h₁, …, h_k` of a pairwise independent family `h i : X → X` into `2 ^ k` blocks
(`Cslib.Crypto.PRG.Nisan.blocks`):

`G₀(x) = x`, `G_{k+1}(x; h₁, …, h_{k+1}) = G_k(x; h₂, …, h_{k+1}) ++ G_k(h₁ x; h₂, …, h_{k+1})`.

So block `b = (b₁ … b_k)` in binary is `h_k^{b_k} (⋯ (h₂^{b₂} (h₁^{b₁} x)))`, the first seed
choosing the most significant bit and acting first. The recursion peels off the first hash seed;
presentations that peel off the last one, `G_k(x; h₁, …, h_k) = G_{k-1}(x; h₁, …, h_{k-1}) ++
G_{k-1}(h_k x; h₁, …, h_{k-1})`, define the same generator on the reversed tuple of hash seeds
`(h_k, …, h₁)`, which is uniform exactly when `(h₁, …, h_k)` is. For every read-once branching
program of width `w` and length `2 ^ k` over the alphabet `X`, its acceptance probabilities on the
output of the generator, for a uniform seed, and on uniform words differ by at most
`(2 ^ k - 1) w / (2 √|X|)` (`Cslib.Crypto.PRG.Nisan.abs_dens_eval_blocks_sub_le`), and the same
holds for every time-dependent transition function `δ` with `w` states, run as the indexed fold
`List.foldlIdx δ` (`Cslib.Crypto.PRG.Nisan.abs_dens_foldlIdx_blocks_sub_le`).
As a generator (`Cslib.Crypto.PRG.Nisan.generator`), it is secure against the tests computed by
read-once branching programs of width `w` (`Cslib.Crypto.PRG.IsReadOnceTest`) with that error
(`Cslib.Crypto.PRG.Nisan.secure_generator`). With `X` the bit strings of length `n` and the
Toeplitz hash family, seeds of `O(n k)` bits fool programs on `2 ^ k n` bits
(`Complexity.Crypto.Primitives.PRG.Nisan.Bits`): for width `w`, length `R` and error `ε` this is
the seed length `O(log (w R / ε) log R)` of Nisan's theorem [Arora and Barak, Theorem
16.48][AroraBarak07], [Vadhan, Section 8.2.1][Vadhan2012]; in this parametrized form it is the
seed length of [Hatami and Hoza, Theorem 3.8][HatamiHoza2024], which the remark after that theorem
attributes to Nisan as well.

## Proof

For a fixed sequence of hash seeds, the run of the program from time `t` on the `2 ^ k` blocks
generated from a uniform `x` is a random walk on the states; let `G_t` be its transition matrix and
`U_t` the transition matrix of the run on `2 ^ k` uniform letters. For every probability vector `π`
on the states, the expected `ℓ¹` error `𝔼 ‖π (G_t - U_t)‖₁` over the hash seeds is at most
`(2 ^ k - 1) w / √|X|`, by induction on `k`. For `k + 1`, the run splits into two halves of `2 ^ k`
blocks, generated from `x` and from `h₁ x` with the same seeds `h₂, …, h_{k+1}`. With these fixed,
the event that the first half moves `u` to `m` and the event that the second half moves `m` to `v`
are sets `A` and `B` of blocks, and the hash mixing lemma
(`Cslib.Probability.IsPairwiseIndependentHash.expect_abs_dens_filter_apply_mem_sub_le`) shows that
`h₁` correlates the two halves of the run by at most `√(μ(A) μ(B) / |X|)` on average. By
Cauchy–Schwarz these terms sum to at most `w / √|X|` over the pairs `(m, v)`. The errors of the
two halves are bounded by induction: the second with the start distribution `π U_t`, since the
first half then has distribution exactly `π U_t`. Acceptance probabilities differ by at most half
the `ℓ¹` distance of the final-state distributions. This is Nisan's hashing argument [Nisan1992],
in expectation form. Unlike [Hatami and Hoza, Section 3.2][HatamiHoza2024], which iterates a
derandomized product through the Impagliazzo–Nisan–Wigderson generator, the two halves here reuse
the same hash seeds, so the induction runs over all start distributions with the lower seeds fixed.

## Main definitions

* `Cslib.Crypto.PRG.Nisan.blocks`: the `2 ^ k` blocks of Nisan's generator.
* `Cslib.Crypto.PRG.Nisan.generator`: Nisan's generator, as a generator.
* `Cslib.Crypto.PRG.IsReadOnceTest`: the tests computed by read-once branching programs of
  width `w`.

## Main results

* `Cslib.Crypto.PRG.Nisan.abs_dens_foldlIdx_blocks_sub_le`: Nisan's generator fools time-dependent
  transition functions with `w` states.
* `Cslib.Crypto.PRG.Nisan.abs_dens_eval_blocks_sub_le`: Nisan's generator fools read-once branching
  programs of width `w`.
* `Cslib.Crypto.PRG.Nisan.secure_generator`: it is secure against read-once branching programs.

## References

* [N. Nisan, *Pseudorandom generators for space-bounded computation*][Nisan1992]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak07], Section 16.7
* [P. Hatami, W. Hoza, *Paradigms for Unconditional Pseudorandom Generators*][HatamiHoza2024]
* [S. Vadhan, *Pseudorandomness*][Vadhan2012], Section 8.2.1
-/

@[expose] public section

namespace Cslib.Crypto.PRG

open Cslib.BranchingPrograms

/-- The tests on words of length `L` over `X` computed by read-once branching programs of width
`w`, that is with the states `Fin w`. As admissible adversaries of
`Cslib.Crypto.PRG.Generator.Secure`, they express security against computations of length `L` with
`log w` bits of memory reading their input once, in order. -/
def IsReadOnceTest {L : ℕ} {X : Type*} (w : ℕ) (adversary : Adversary (Fin L → X)) : Prop :=
  ∃ P : ReadOnceProgram L (Fin w) X, adversary = fun x => PMF.pure (P.eval x)

namespace Nisan

open Cslib.Probability Finset
open scoped BigOperators NNReal

variable {ι X S : Type*}

/-! ### The generator -/

/-- The `2 ^ k` blocks of Nisan's generator with the hash family `h`, on the block `x` and the
hash seeds `hs`: one block `x` for `k = 0`, and for `k + 1` the blocks for `x` followed by the
blocks for `h (hs 0) x`, both with the seeds `hs 1, …, hs k`. -/
def blocks (h : ι → X → X) : (k : ℕ) → X → (Fin k → ι) → Fin (2 ^ k) → X
  | 0, x, _ => fun _ => x
  | k + 1, x, hs => fun j =>
    Fin.append (blocks h k x (Fin.tail hs)) (blocks h k (h (hs 0) x) (Fin.tail hs))
      (j.cast (by rw [pow_succ, mul_two]))

@[simp] theorem blocks_zero (h : ι → X → X) (x : X) (hs : Fin 0 → ι) (j : Fin (2 ^ 0)) :
    blocks h 0 x hs j = x :=
  rfl

/-- The blocks for `k + 1` hash seeds are the blocks for `x` followed by those for `h (hs 0) x`,
with the remaining seeds. -/
theorem ofFn_blocks_succ (h : ι → X → X) (k : ℕ) (x : X) (hs : Fin (k + 1) → ι) :
    List.ofFn (blocks h (k + 1) x hs) =
      List.ofFn (blocks h k x (Fin.tail hs)) ++
        List.ofFn (blocks h k (h (hs 0) x) (Fin.tail hs)) := by
  rw [List.ofFn_congr (by rw [pow_succ, mul_two] : 2 ^ (k + 1) = 2 ^ k + 2 ^ k), ←
    List.ofFn_fin_append]
  simp only [blocks, Fin.cast_cast, Fin.cast_eq_self]

/-- Nisan's generator with the hash family `h` and `k` hash seeds: the seed is a block and `k` hash
seeds, the output is `2 ^ k` blocks. -/
def generator (h : ι → X → X) (k : ℕ) : Generator (X × (Fin k → ι)) (Fin (2 ^ k) → X) :=
  ⟨fun z => blocks h k z.1 z.2⟩

@[simp] theorem generator_apply (h : ι → X → X) (k : ℕ) (z : X × (Fin k → ι)) :
    generator h k z = blocks h k z.1 z.2 :=
  rfl

/-! ### Transition probabilities -/

section Probability

variable [DecidableEq S]

/-- The probability that the run `r ω` of a uniformly random `ω` ends in the state `s'`. -/
private noncomputable def prob {Ω : Type*} [Fintype Ω] (r : Ω → S) (s' : S) : ℝ :=
  dens {ω | r ω = s'}

private theorem prob_eq_expect {Ω : Type*} [Fintype Ω] (r : Ω → S) (s' : S) :
    prob r s' = 𝔼 ω, if r ω = s' then 1 else 0 :=
  (Fintype.expect_boole _).symm

private theorem prob_nonneg {Ω : Type*} [Fintype Ω] (r : Ω → S) (s' : S) : 0 ≤ prob r s' := by
  unfold prob
  positivity

variable [Fintype S]

/-- Expectations of functions of the end state are averages over the end states. -/
private theorem expect_comp_eq_sum {Ω : Type*} [Fintype Ω] (r : Ω → S) (f : S → ℝ) :
    𝔼 ω, f (r ω) = ∑ s', prob r s' * f s' := by
  simp only [prob_eq_expect, expect_mul]
  rw [← expect_sum_comm]
  refine expect_congr rfl fun ω _ => ?_
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]

private theorem sum_prob {Ω : Type*} [Fintype Ω] [Nonempty Ω] (r : Ω → S) :
    ∑ s', prob r s' = 1 := by
  simpa only [mul_one, Fintype.expect_const] using (expect_comp_eq_sum r fun _ => 1).symm

/-- The probability that `n` uniform letters move `s` to `s'` from time `t`. -/
private noncomputable def uniP [Fintype X] (δ : ℕ → S → X → S) (t n : ℕ) (s s' : S) : ℝ :=
  prob (fun u : Fin n → X => (List.ofFn u).foldlIdx δ s t) s'

/-- The probability that the blocks of Nisan's generator, with the hash seeds `hs` and a uniform
block, move `s` to `s'` from time `t`. -/
private noncomputable def genP [Fintype X] (h : ι → X → X) (δ : ℕ → S → X → S) (t k : ℕ)
    (hs : Fin k → ι) (s s' : S) : ℝ :=
  prob (fun x : X => (List.ofFn (blocks h k x hs)).foldlIdx δ s t) s'

/-- **Chapman–Kolmogorov**: `a + b` uniform letters are `a` uniform letters followed by `b`
independent uniform letters. -/
private theorem uniP_add [Fintype X] (δ : ℕ → S → X → S) (t a b : ℕ) (s s'' : S) :
    uniP δ t (a + b) s s'' = ∑ s', uniP δ t a s s' * uniP δ (t + a) b s' s'' := by
  rw [uniP, prob_eq_expect, ← Fintype.expect_equiv (Fin.appendEquiv a b)
    (fun p => if (List.ofFn (Fin.append p.1 p.2)).foldlIdx δ s t = s'' then (1 : ℝ) else 0) _
    fun _ => rfl, Fintype.expect_prod_type]
  simp only [List.ofFn_fin_append, List.foldlIdx_append, List.length_ofFn]
  rw [expect_comp_eq_sum (fun u₁ : Fin a → X => (List.ofFn u₁).foldlIdx δ s t)
    (fun s' => 𝔼 u₂ : Fin b → X,
      if (List.ofFn u₂).foldlIdx δ s' (t + a) = s'' then (1 : ℝ) else 0)]
  simp only [uniP, prob_eq_expect]

private theorem uniP_two_pow_succ [Fintype X] (δ : ℕ → S → X → S) (t k : ℕ) (s s'' : S) :
    uniP δ t (2 ^ (k + 1)) s s'' =
      ∑ s', uniP δ t (2 ^ k) s s' * uniP δ (t + 2 ^ k) (2 ^ k) s' s'' := by
  rw [pow_succ, mul_two, uniP_add]

omit [Fintype S] in
/-- With no hash seeds, the generator outputs one uniform letter. -/
private theorem genP_zero [Fintype X] (h : ι → X → X) (δ : ℕ → S → X → S) (t : ℕ)
    (hs : Fin 0 → ι) (s s' : S) : genP h δ t 0 hs s s' = uniP δ t (2 ^ 0) s s' := by
  let e : X ≃ (Fin (2 ^ 0) → X) :=
    { toFun := fun x _ => x
      invFun := fun u => u ⟨0, Nat.one_pos⟩
      left_inv := fun _ => rfl
      right_inv := fun u => funext fun j => congrArg u (Fin.ext (Nat.lt_one_iff.1 j.2).symm) }
  rw [genP, uniP, prob_eq_expect, prob_eq_expect]
  exact Fintype.expect_equiv e _ _ fun _ => rfl

/-- A probability split according to the state at an intermediate time. -/
private theorem dens_filter_comp {Ω : Type*} [Fintype Ω] (r : Ω → S) (g : S → Ω → Prop)
    [∀ s ω, Decidable (g s ω)] :
    (dens {ω | g (r ω) ω} : ℝ) = ∑ s', (dens {ω | r ω = s' ∧ g s' ω} : ℝ) := by
  simp only [← Fintype.expect_boole]
  rw [← expect_sum_comm]
  refine expect_congr rfl fun ω _ => ?_
  simp only [ite_and, sum_ite_eq, mem_univ, ite_true]

/-- **Splitting a generated run**: with the first seed `i` and the remaining seeds `hs`, the run on
the generated blocks splits at the intermediate state into the run on the blocks for `x` and the
run on the blocks for `h i x`. -/
private theorem genP_succ [Fintype X] (h : ι → X → X) (δ : ℕ → S → X → S) (t k : ℕ) (i : ι)
    (hs : Fin k → ι) (s s'' : S) :
    genP h δ t (k + 1) (Fin.cons i hs) s s'' =
      ∑ s', (dens {x | (List.ofFn (blocks h k x hs)).foldlIdx δ s t = s' ∧
        (List.ofFn (blocks h k (h i x) hs)).foldlIdx δ s' (t + 2 ^ k) = s''} : ℝ) := by
  rw [genP, prob]
  simp only [ofFn_blocks_succ, Fin.tail_cons, Fin.cons_zero, List.foldlIdx_append, List.length_ofFn]
  exact dens_filter_comp (fun x => (List.ofFn (blocks h k x hs)).foldlIdx δ s t)
    (fun s' x => (List.ofFn (blocks h k (h i x) hs)).foldlIdx δ s' (t + 2 ^ k) = s'')

/-! ### The junction bound -/

omit [DecidableEq S] in
/-- `∑ √(a s) ≤ √|S|` for a probability vector `a`. -/
private theorem sum_sqrt_le (a : S → ℝ) (ha : ∀ s, 0 ≤ a s) (ha1 : ∑ s, a s = 1) :
    ∑ s, √(a s) ≤ √(Fintype.card S) := by
  have := Real.sum_sqrt_mul_sqrt_le univ (fun _ => zero_le_one) ha
  simpa only [Real.sqrt_one, one_mul, sum_const, card_univ, nsmul_eq_mul, mul_one, ha1] using this

omit [DecidableEq S] in
/-- **The junction bound for rectangles**: for families of sets `A s s'` and `B s' s''` of total
density `1` in `s'` and in `s''`, a random member `h i` of a pairwise independent family mixes the
rectangles `A s s' × B s' s''` up to a total error of `w / √|X|`, for every start distribution
`π`. -/
private theorem expect_sum_abs_filter_le [Fintype ι] [Fintype X] [DecidableEq X]
    {h : ι → X → X} (hh : IsPairwiseIndependentHash h) (A B : S → S → Finset X) (π : S → ℝ)
    (hπ : ∀ s, 0 ≤ π s) (hπ1 : ∑ s, π s = 1) (hA : ∀ s, ∑ s', ((A s s').dens : ℝ) = 1)
    (hB : ∀ s', ∑ s'', ((B s' s'').dens : ℝ) = 1) :
    𝔼 i, ∑ s'', |∑ s, π s * ∑ s', ((dens {x ∈ A s s' | h i x ∈ B s' s''} : ℝ) -
      (A s s').dens * (B s' s'').dens)| ≤ Fintype.card S / √(Fintype.card X) := by
  have hrow (s : S) : ∑ s', ∑ s'', √((A s s').dens * (B s' s'').dens / Fintype.card X) ≤
      Fintype.card S / √(Fintype.card X) := by
    calc ∑ s', ∑ s'', √((A s s').dens * (B s' s'').dens / Fintype.card X)
        = (∑ s', √((A s s').dens) * ∑ s'', √((B s' s'').dens)) / √(Fintype.card X) := by
          rw [sum_div]
          refine sum_congr rfl fun s' _ => ?_
          rw [mul_sum, sum_div]
          refine sum_congr rfl fun s'' _ => ?_
          rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity)]
      _ ≤ (∑ s', √((A s s').dens) * √(Fintype.card S)) / √(Fintype.card X) := by
          gcongr with s' _
          exact sum_sqrt_le _ (fun _ => by positivity) (hB s')
      _ ≤ (√(Fintype.card S) * √(Fintype.card S)) / √(Fintype.card X) := by
          rw [← sum_mul]
          gcongr
          exact sum_sqrt_le _ (fun _ => by positivity) (hA s)
      _ = Fintype.card S / √(Fintype.card X) := by
          rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]
  calc 𝔼 i, ∑ s'', |∑ s, π s * ∑ s', ((dens {x ∈ A s s' | h i x ∈ B s' s''} : ℝ) -
        (A s s').dens * (B s' s'').dens)|
      ≤ 𝔼 i, ∑ s'', ∑ s, ∑ s', π s * |(dens {x ∈ A s s' | h i x ∈ B s' s''} : ℝ) -
          (A s s').dens * (B s' s'').dens| := by
        refine expect_le_expect fun i _ => sum_le_sum fun s'' _ => ?_
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun s _ => ?_)
        rw [abs_mul, abs_of_nonneg (hπ s), ← mul_sum]
        exact mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (hπ s)
    _ = ∑ s, ∑ s', ∑ s'', π s * 𝔼 i, |(dens {x ∈ A s s' | h i x ∈ B s' s''} : ℝ) -
          (A s s').dens * (B s' s'').dens| := by
        simp only [expect_sum_comm, ← mul_expect]
        exact sum_comm.trans (sum_congr rfl fun s _ => sum_comm)
    _ ≤ ∑ s, ∑ s', ∑ s'', π s * √((A s s').dens * (B s' s'').dens / Fintype.card X) :=
        sum_le_sum fun s _ => sum_le_sum fun s' _ => sum_le_sum fun s'' _ =>
          mul_le_mul_of_nonneg_left (hh.expect_abs_dens_filter_apply_mem_sub_le _ _) (hπ s)
    _ ≤ ∑ s, π s * (Fintype.card S / √(Fintype.card X)) := by
        refine sum_le_sum fun s _ => ?_
        simp only [← mul_sum]
        exact mul_le_mul_of_nonneg_left (hrow s) (hπ s)
    _ = Fintype.card S / √(Fintype.card X) := by
        rw [← sum_mul, hπ1, one_mul]

/-- **The junction bound**: a random member of a pairwise independent family correlates two runs,
one from `s` on `x` and one from the intermediate state on `h i x`, by at most `w / √|X|` in total,
for every start distribution `π`. -/
private theorem expect_junction_le [Fintype ι] [Fintype X] [Nonempty X] [DecidableEq X]
    {h : ι → X → X} (hh : IsPairwiseIndependentHash h) (r₁ r₂ : S → X → S) (π : S → ℝ)
    (hπ : ∀ s, 0 ≤ π s) (hπ1 : ∑ s, π s = 1) :
    𝔼 i, ∑ s'', |∑ s, π s * ∑ s', ((dens {x | r₁ s x = s' ∧ r₂ s' (h i x) = s''} : ℝ) -
      prob (r₁ s) s' * prob (r₂ s') s'')| ≤ Fintype.card S / √(Fintype.card X) := by
  have hboth (i : ι) (s s' s'' : S) :
      ({x | r₁ s x = s' ∧ r₂ s' (h i x) = s''} : Finset X) =
        {x ∈ ({x | r₁ s x = s'} : Finset X) | h i x ∈ ({y | r₂ s' y = s''} : Finset X)} := by
    ext x
    simp only [mem_filter, mem_univ, true_and]
  simp only [hboth]
  exact expect_sum_abs_filter_le hh (fun s s' => {x | r₁ s x = s'})
    (fun s' s'' => {y | r₂ s' y = s''}) π hπ hπ1 (fun s => sum_prob (r₁ s))
    fun s' => sum_prob (r₂ s')

/-! ### The induction -/

omit [DecidableEq S] in
/-- The algebra of one step of the induction: the error of the composed run splits into the error
of the first half, the error of the second half from the distribution `π U₁`, and the correlation
of the two halves. -/
private theorem sum_abs_step_le (π : S → ℝ) (G₁ U₁ G₂ U₂ : S → S → ℝ)
    (C : S → S → S → ℝ) (hG₂ : ∀ s' s'', 0 ≤ G₂ s' s'') (hG₂1 : ∀ s', ∑ s'', G₂ s' s'' = 1) :
    ∑ s'', |∑ s, π s * (∑ s', C s s' s'' - ∑ s', U₁ s s' * U₂ s' s'')| ≤
      ∑ s', |∑ s, π s * (G₁ s s' - U₁ s s')| +
        ∑ s'', |∑ s', (∑ s, π s * U₁ s s') * (G₂ s' s'' - U₂ s' s'')| +
        ∑ s'', |∑ s, π s * ∑ s', (C s s' s'' - G₁ s s' * G₂ s' s'')| := by
  have key (s'' : S) : ∑ s, π s * (∑ s', C s s' s'' - ∑ s', U₁ s s' * U₂ s' s'') =
      ∑ s', (∑ s, π s * (G₁ s s' - U₁ s s')) * G₂ s' s'' +
        ∑ s', (∑ s, π s * U₁ s s') * (G₂ s' s'' - U₂ s' s'') +
        ∑ s, π s * ∑ s', (C s s' s'' - G₁ s s' * G₂ s' s'') := by
    simp only [sum_mul, mul_sum]
    rw [sum_comm (s := univ) (t := univ) (f := fun s' s => π s * (G₁ s s' - U₁ s s') * G₂ s' s''),
      sum_comm (s := univ) (t := univ)
        (f := fun s' s => π s * U₁ s s' * (G₂ s' s'' - U₂ s' s'')),
      ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun s _ => ?_
    rw [← sum_sub_distrib, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun s' _ => ?_
    ring
  calc ∑ s'', |∑ s, π s * (∑ s', C s s' s'' - ∑ s', U₁ s s' * U₂ s' s'')|
      ≤ ∑ s'', (∑ s', |∑ s, π s * (G₁ s s' - U₁ s s')| * G₂ s' s'' +
          |∑ s', (∑ s, π s * U₁ s s') * (G₂ s' s'' - U₂ s' s'')| +
          |∑ s, π s * ∑ s', (C s s' s'' - G₁ s s' * G₂ s' s'')|) := by
        refine sum_le_sum fun s'' _ => ?_
        rw [key]
        have h₁ : |∑ s', (∑ s, π s * (G₁ s s' - U₁ s s')) * G₂ s' s''| ≤
            ∑ s', |∑ s, π s * (G₁ s s' - U₁ s s')| * G₂ s' s'' :=
          (abs_sum_le_sum_abs _ _).trans_eq
            (sum_congr rfl fun s' _ => by rw [abs_mul, abs_of_nonneg (hG₂ s' s'')])
        exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add h₁ le_rfl))
          le_rfl)
    _ = _ := by
        rw [sum_add_distrib, sum_add_distrib, sum_comm]
        congr 2
        refine sum_congr rfl fun s' _ => ?_
        rw [← mul_sum, hG₂1, mul_one]

/-- The induction step of `expect_sum_abs_le`. -/
private theorem expect_sum_abs_succ_le [Fintype ι] [Fintype X] [Nonempty X] [DecidableEq X]
    {h : ι → X → X} (hh : IsPairwiseIndependentHash h) (δ : ℕ → S → X → S) (k : ℕ)
    (ih : ∀ (t : ℕ) (π : S → ℝ), (∀ s, 0 ≤ π s) → ∑ s, π s = 1 →
      𝔼 hs : Fin k → ι, ∑ s', |∑ s, π s * (genP h δ t k hs s s' - uniP δ t (2 ^ k) s s')| ≤
        (2 ^ k - 1) * (Fintype.card S / √(Fintype.card X)))
    (t : ℕ) (π : S → ℝ) (hπ : ∀ s, 0 ≤ π s) (hπ1 : ∑ s, π s = 1) :
    𝔼 hs : Fin (k + 1) → ι, ∑ s'',
        |∑ s, π s * (genP h δ t (k + 1) hs s s'' - uniP δ t (2 ^ (k + 1)) s s'')| ≤
      (2 ^ (k + 1) - 1) * (Fintype.card S / √(Fintype.card X)) := by
  have : Nonempty ι := hh.nonempty (Classical.arbitrary X) (Classical.arbitrary X)
  have hρ : ∀ s', 0 ≤ ∑ s, π s * uniP δ t (2 ^ k) s s' := fun s' =>
    sum_nonneg fun s _ => mul_nonneg (hπ s) (prob_nonneg _ _)
  have hρ1 : ∑ s', ∑ s, π s * uniP δ t (2 ^ k) s s' = 1 := by
    rw [sum_comm]
    simp only [← mul_sum, uniP, sum_prob, mul_one, hπ1]
  have ih₁ := ih t π hπ hπ1
  have ih₂ := ih (t + 2 ^ k) (fun s' => ∑ s, π s * uniP δ t (2 ^ k) s s') hρ hρ1
  have hJ (hs : Fin k → ι) := expect_junction_le hh
    (fun s x => (List.ofFn (blocks h k x hs)).foldlIdx δ s t)
    (fun s' y => (List.ofFn (blocks h k y hs)).foldlIdx δ s' (t + 2 ^ k)) π hπ hπ1
  rw [Fin.expect_univ_cons, expect_comm]
  calc 𝔼 hs : Fin k → ι, 𝔼 i, ∑ s'', |∑ s, π s *
        (genP h δ t (k + 1) (Fin.cons i hs) s s'' - uniP δ t (2 ^ (k + 1)) s s'')|
      ≤ 𝔼 hs : Fin k → ι, 𝔼 i : ι,
          (∑ s', |∑ s, π s * (genP h δ t k hs s s' - uniP δ t (2 ^ k) s s')| +
            ∑ s'', |∑ s', (∑ s, π s * uniP δ t (2 ^ k) s s') *
              (genP h δ (t + 2 ^ k) k hs s' s'' - uniP δ (t + 2 ^ k) (2 ^ k) s' s'')| +
            ∑ s'', |∑ s, π s * ∑ s',
              ((dens {x | (List.ofFn (blocks h k x hs)).foldlIdx δ s t = s' ∧
                  (List.ofFn (blocks h k (h i x) hs)).foldlIdx δ s' (t + 2 ^ k) = s''} : ℝ) -
                genP h δ t k hs s s' * genP h δ (t + 2 ^ k) k hs s' s'')|) := by
        refine expect_le_expect fun hs _ => expect_le_expect fun i _ => ?_
        simp only [genP_succ, uniP_two_pow_succ]
        exact sum_abs_step_le π (genP h δ t k hs) (uniP δ t (2 ^ k))
          (genP h δ (t + 2 ^ k) k hs) (uniP δ (t + 2 ^ k) (2 ^ k))
          (fun s s' s'' => (dens {x | (List.ofFn (blocks h k x hs)).foldlIdx δ s t = s' ∧
            (List.ofFn (blocks h k (h i x) hs)).foldlIdx δ s' (t + 2 ^ k) = s''} : ℝ))
          (fun _ _ => prob_nonneg _ _) fun _ => sum_prob _
    _ = 𝔼 hs : Fin k → ι,
            ∑ s', |∑ s, π s * (genP h δ t k hs s s' - uniP δ t (2 ^ k) s s')| +
          𝔼 hs : Fin k → ι, ∑ s'', |∑ s', (∑ s, π s * uniP δ t (2 ^ k) s s') *
            (genP h δ (t + 2 ^ k) k hs s' s'' - uniP δ (t + 2 ^ k) (2 ^ k) s' s'')| +
          𝔼 hs : Fin k → ι, 𝔼 i, ∑ s'', |∑ s, π s * ∑ s',
            ((dens {x | (List.ofFn (blocks h k x hs)).foldlIdx δ s t = s' ∧
                (List.ofFn (blocks h k (h i x) hs)).foldlIdx δ s' (t + 2 ^ k) = s''} : ℝ) -
              genP h δ t k hs s s' * genP h δ (t + 2 ^ k) k hs s' s'')| := by
        simp only [expect_add_distrib, Fintype.expect_const]
    _ ≤ (2 ^ k - 1) * (Fintype.card S / √(Fintype.card X)) +
          (2 ^ k - 1) * (Fintype.card S / √(Fintype.card X)) +
          Fintype.card S / √(Fintype.card X) := by
        gcongr
        exact (expect_le_expect fun hs _ => hJ hs).trans_eq (Fintype.expect_const _)
    _ = (2 ^ (k + 1) - 1) * (Fintype.card S / √(Fintype.card X)) := by ring

/-- **The error bound in `ℓ¹`**: for every start distribution `π` and time `t`, the transition
probabilities of the run on the generated blocks, for a uniform block, have expected `ℓ¹` error
at most `(2 ^ k - 1) w / √|X|` over the hash seeds, relative to `2 ^ k` uniform letters. -/
private theorem expect_sum_abs_le [Fintype ι] [Fintype X] [Nonempty X] [DecidableEq X]
    {h : ι → X → X} (hh : IsPairwiseIndependentHash h) (δ : ℕ → S → X → S) (k : ℕ) :
    ∀ (t : ℕ) (π : S → ℝ), (∀ s, 0 ≤ π s) → ∑ s, π s = 1 →
      𝔼 hs : Fin k → ι, ∑ s', |∑ s, π s * (genP h δ t k hs s s' - uniP δ t (2 ^ k) s s')| ≤
        (2 ^ k - 1) * (Fintype.card S / √(Fintype.card X)) := by
  induction k with
  | zero =>
    intro t π _ _
    simp only [genP_zero, sub_self, mul_zero, sum_const_zero, abs_zero, expect_const_zero,
      pow_zero, zero_mul, le_refl]
  | succ k ih => exact expect_sum_abs_succ_le hh δ k ih

end Probability

/-! ### Fooling read-once branching programs -/

/-- An acceptance probability differs from another, with the same total mass, by at most half
the `ℓ¹` distance. -/
private theorem abs_sum_mul_boole_le [Fintype S] (d : S → ℝ) (hd : ∑ s, d s = 0) (F : S → Bool) :
    |∑ s, d s * (if F s = true then 1 else 0)| ≤ (∑ s, |d s|) / 2 := by
  have hsplit := sum_filter_add_sum_filter_not univ (fun s => F s = true) d
  have habs := sum_filter_add_sum_filter_not univ (fun s => F s = true) fun s => |d s|
  have h₁ := abs_sum_le_sum_abs d (univ.filter fun s => F s = true)
  have h₂ := abs_sum_le_sum_abs d (univ.filter fun s => ¬F s = true)
  rw [hd] at hsplit
  have hneg : ∑ s ∈ univ.filter (fun s => ¬F s = true), d s =
      -∑ s ∈ univ.filter (fun s => F s = true), d s := by linarith
  rw [hneg, abs_neg] at h₂
  simp only [mul_boole, ← sum_filter]
  linarith

/-- **Nisan's generator fools time-dependent transition functions** [Nisan1992]: for a pairwise
independent family `h i : X → X`, every transition function `δ` with states `S`, start state `s₀`
and accepting states `F`, the probability that the run on the `2 ^ k` blocks of Nisan's generator
with a uniform seed accepts differs from the probability that the run on `2 ^ k` uniform letters
accepts by at most `(2 ^ k - 1) |S| / (2 √|X|)`. -/
theorem abs_dens_foldlIdx_blocks_sub_le [Fintype ι] [Fintype X] [DecidableEq X] [Fintype S]
    {h : ι → X → X} (hh : IsPairwiseIndependentHash h) (δ : ℕ → S → X → S) (s₀ : S)
    (F : S → Bool) (k : ℕ) :
    |(dens {z : X × (Fin k → ι) | F ((List.ofFn (blocks h k z.1 z.2)).foldlIdx δ s₀) = true} :
        ℝ) - dens {u : Fin (2 ^ k) → X | F ((List.ofFn u).foldlIdx δ s₀) = true}| ≤
      (2 ^ k - 1) * Fintype.card S / (2 * √(Fintype.card X)) := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · have : IsEmpty (Fin (2 ^ k) → X) := ⟨fun u => IsEmpty.false (u ⟨0, by positivity⟩)⟩
    simp [dens, Fintype.card_eq_zero]
  have : Nonempty ι := hh.nonempty (Classical.arbitrary X) (Classical.arbitrary X)
  have hπ : ∀ s, 0 ≤ (fun s => if s₀ = s then (1 : ℝ) else 0) s := fun s => by
    dsimp only
    split_ifs <;> norm_num
  have hπ1 : ∑ s, (fun s => if s₀ = s then (1 : ℝ) else 0) s = 1 := by
    simp only [sum_ite_eq, mem_univ, ite_true]
  have hbound := expect_sum_abs_le hh δ k 0 _ hπ hπ1
  simp only [boole_mul, sum_ite_eq, mem_univ, ite_true] at hbound
  have hgen : (dens {z : X × (Fin k → ι) |
      F ((List.ofFn (blocks h k z.1 z.2)).foldlIdx δ s₀) = true} : ℝ) =
      𝔼 hs : Fin k → ι, ∑ s', genP h δ 0 k hs s₀ s' * (if F s' = true then 1 else 0) := by
    rw [← Fintype.expect_boole, Fintype.expect_prod_type, expect_comm]
    refine expect_congr rfl fun hs _ => ?_
    exact expect_comp_eq_sum (fun x => (List.ofFn (blocks h k x hs)).foldlIdx δ s₀)
      fun s' => if F s' = true then 1 else 0
  have huni : (dens {u : Fin (2 ^ k) → X | F ((List.ofFn u).foldlIdx δ s₀) = true} : ℝ) =
      𝔼 _hs : Fin k → ι, ∑ s', uniP δ 0 (2 ^ k) s₀ s' * (if F s' = true then 1 else 0) := by
    rw [Fintype.expect_const, ← Fintype.expect_boole]
    exact expect_comp_eq_sum (fun u : Fin (2 ^ k) → X => (List.ofFn u).foldlIdx δ s₀)
      fun s' => if F s' = true then 1 else 0
  rw [hgen, huni, ← expect_sub_distrib]
  calc |𝔼 hs : Fin k → ι, (∑ s', genP h δ 0 k hs s₀ s' * (if F s' = true then 1 else 0) -
        ∑ s', uniP δ 0 (2 ^ k) s₀ s' * (if F s' = true then 1 else 0))|
      ≤ 𝔼 hs : Fin k → ι, (∑ s', |genP h δ 0 k hs s₀ s' - uniP δ 0 (2 ^ k) s₀ s'|) / 2 := by
        refine (abs_expect_le _ _).trans (expect_le_expect fun hs _ => ?_)
        rw [← sum_sub_distrib]
        simp only [← sub_mul]
        refine abs_sum_mul_boole_le _ ?_ F
        rw [sum_sub_distrib]
        simp only [genP, uniP, sum_prob, sub_self]
    _ ≤ (2 ^ k - 1) * (Fintype.card S / √(Fintype.card X)) / 2 := by
        rw [← expect_div]
        gcongr
    _ = (2 ^ k - 1) * Fintype.card S / (2 * √(Fintype.card X)) := by
        rw [mul_div_assoc', div_div, mul_comm (√_) 2]

/-- **Nisan's generator fools read-once branching programs** [Nisan1992]: for a pairwise independent
family `h i : X → X` and every read-once branching program `P` of length `2 ^ k` over `X` with
states `S`, the probability that `P` accepts the output of Nisan's generator on a uniform seed
differs from the probability that it accepts a uniform word by at most
`(2 ^ k - 1) |S| / (2 √|X|)`. -/
theorem abs_dens_eval_blocks_sub_le [Fintype ι] [Fintype X] [DecidableEq X] [Fintype S]
    {h : ι → X → X} (hh : IsPairwiseIndependentHash h) (k : ℕ) (P : ReadOnceProgram (2 ^ k) S X) :
    |(dens {z : X × (Fin k → ι) | P.eval (blocks h k z.1 z.2) = true} : ℝ) -
        dens {u : Fin (2 ^ k) → X | P.eval u = true}| ≤
      (2 ^ k - 1) * Fintype.card S / (2 * √(Fintype.card X)) := by
  simp only [ReadOnceProgram.eval, ReadOnceProgram.finalState_eq]
  exact abs_dens_foldlIdx_blocks_sub_le hh P.stepAt P.start P.accept k

/-- **Nisan's generator is secure against read-once branching programs** [Nisan1992]: for a
pairwise independent family `h i : X → X`, no read-once branching program of width `w` and length
`2 ^ k` distinguishes the output of Nisan's generator with `k` hash seeds from a uniform word with
advantage more than `(2 ^ k - 1) w / (2 √|X|)`. -/
theorem secure_generator [Fintype ι] [Nonempty ι] [Fintype X] [Nonempty X] [DecidableEq X]
    {h : ι → X → X} (hh : IsPairwiseIndependentHash h) (k w : ℕ) :
    (generator h k).Secure (IsReadOnceTest w)
      ((2 ^ k - 1) * w / (2 * NNReal.sqrt (Fintype.card X))) := by
  rintro _ ⟨P, rfl⟩
  rw [Generator.advantage, Generator.toReal_realExperiment_pure,
    Generator.toReal_idealExperiment_pure]
  have hk : (1 : ℝ≥0) ≤ 2 ^ k := one_le_pow₀ one_le_two
  have := abs_dens_eval_blocks_sub_le hh k P
  rw [Fintype.card_fin] at this
  simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_sub hk, NNReal.coe_pow, NNReal.coe_ofNat,
    NNReal.coe_one, NNReal.coe_natCast, Real.coe_sqrt]
  exact this

end Nisan

end Cslib.Crypto.PRG
