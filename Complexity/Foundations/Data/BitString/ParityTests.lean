/-
Copyright (c) 2026 Samuel Schlesinger, Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Data.BitString.Weight
public import Mathlib.Data.Matrix.Mul
import Complexity.Foundations.Data.BitString.Parity.DotProduct
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Greedy selection of random parity tests

A *test list* `γ = ((e₁, c₁), …, (e_P, c_P))` of `P` pairs of an index `eⱼ < m` and a bit `cⱼ`
represents the test row `testRow γ` over `𝔽₂`, whose coordinate `e` is the sum of the bits `cⱼ`
with `eⱼ = e` (`Cslib.BitString.testRow`). The row rejects a bit string `z` when its parity
`testRow γ ⬝ᵥ z = Σⱼ cⱼ z_{eⱼ}` (`Cslib.BitString.testParity`) is `true`.

If `z` is nonzero with at least `m / P` ones, then at least a quarter of the `(2m) ^ P` lists reject
`z` (`Cslib.BitString.pow_le_four_mul_card_testParity_eq_true`). Exactly
`2 ^ (P - 1) (m ^ P - (m - weight z) ^ P)` lists do: for indices that hit a one of `z`, the parity
is the parity of the coefficients on a nonempty set, which is balanced
(`Cslib.card_filter_parityOn_eq`); and `(1 - 1/P) ^ P ≤ e⁻¹ < 1/2`.

Averaging then gives a deterministic procedure [OpenAI2026ETH, Lemma 6.2]. Given points `x`
with *violation vectors* `v x`, a list of rows *accepts* `x` when every row has parity zero on
`v x`. Starting from rows after which every accepted point with a nonzero violation vector has at
least `m / P` violations, append `3 n` rows `testRow γ`, each minimizing the number of accepted
points. Each step keeps at most three quarters of the accepted points with nonzero violation
vectors, so with at most `2 ^ n` points the final rows accept exactly the points whose violation
vector is zero (`Cslib.BitString.numPassing_greedy`). The procedure only compares counts of
accepted points, which exceed the unknown number of zero-violation points by the number of
accepted bad points (`Cslib.BitString.numPassing_eq`).

## Main definitions

* `Cslib.BitString.testRow`, `Cslib.BitString.testParity`: the row of a test list and its parity.
* `Cslib.BitString.PassesTests`, `Cslib.BitString.numPassing`: acceptance by a list of rows, and
  the number of accepted points.

## Main results

* `Cslib.BitString.weight_testRow_le`: a test row of list length `P` has Hamming weight at most `P`.
* `Cslib.BitString.two_mul_card_testParity_eq_true`: the exact number of rejecting lists.
* `Cslib.BitString.pow_le_four_mul_card_testParity_eq_true`: a quarter of the lists reject.
* `Cslib.BitString.four_mul_card_accept_le_of_forall_le`: a minimizing list accepts at most three
  quarters of a set of such vectors.
* `Cslib.BitString.numPassing_greedy`: the greedy procedure after `3 n` rounds.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §6.2
-/

@[expose] public section

namespace Cslib.BitString

open Finset

variable {m P : ℕ}

/-! ### Test lists -/

/-- The parity of the test list `γ = ((eⱼ, cⱼ))ⱼ` on the bit string `z`: `Σⱼ cⱼ z_{eⱼ}`. -/
def testParity (γ : Fin P → Fin m × Bool) (z : Fin m → Bool) : Bool :=
  ∑ j, (γ j).2 * z (γ j).1

/-- The test row of a list: coordinate `e` is the sum of the bits `cⱼ` with `eⱼ = e`. -/
def testRow (γ : Fin P → Fin m × Bool) : Fin m → Bool :=
  fun e => ∑ j, if (γ j).1 = e then (γ j).2 else 0

/-- The parity of a list is the inner product of its row with the bit string. -/
theorem testRow_dotProduct (γ : Fin P → Fin m × Bool) (z : Fin m → Bool) :
    testRow γ ⬝ᵥ z = testParity γ z := by
  simp only [testRow, dotProduct, testParity, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq]

/-- A test row built from a list `γ` of `P` index-bit pairs has Hamming weight at most `P`. -/
theorem weight_testRow_le (γ : Fin P → Fin m × Bool) : weight (testRow γ) ≤ P := by
  have hsub :
      ({e : Fin m | testRow γ e = true} : Finset (Fin m)) ⊆
        univ.image fun j : Fin P => (γ j).1 := by
    intro e he
    rw [mem_filter] at he
    have hne : (∑ j : Fin P, if (γ j).1 = e then (γ j).2 else 0) ≠ 0 := by
      rw [← testRow, he.2]
      decide
    obtain ⟨j, -, hj⟩ := exists_ne_zero_of_sum_ne_zero hne
    have hje : (γ j).1 = e := by
      by_contra h
      simp only [h, ↓reduceIte] at hj
      exact hj rfl
    exact mem_image.mpr ⟨j, mem_univ j, hje⟩
  calc weight (testRow γ)
      = #{e : Fin m | testRow γ e = true} := rfl
    _ ≤ #(univ.image fun j : Fin P => (γ j).1) := card_le_card hsub
    _ ≤ #(univ : Finset (Fin P)) := card_image_le
    _ = P := by simp only [card_univ, Fintype.card_fin]

/-- Exactly half of the coefficient strings have inner product `true` with a nonzero string: the
inner product with `w` is the parity on the support of `w` (`dotProduct_eq_parityOn`), which is
balanced (`Cslib.card_filter_parityOn_eq`). -/
theorem two_mul_card_dotProduct_eq_true {w : Fin P → Bool} {j : Fin P} (hj : w j = true) :
    2 * #{c : Fin P → Bool | c ⬝ᵥ w = true} = 2 ^ P := by
  simp only [dotProduct_eq_parityOn]
  rw [card_filter_parityOn_eq ⟨j, by simpa using hj⟩, Fintype.card_fin, ← pow_succ']
  congr 1
  have := j.pos
  omega

/-- For fixed indices, the number of coefficient strings whose list rejects `z`. -/
private theorem two_mul_card_coeff (z : Fin m → Bool) (e : Fin P → Fin m) :
    2 * #{c : Fin P → Bool | c ⬝ᵥ (fun j => z (e j)) = true} =
      if ∃ j, z (e j) = true then 2 ^ P else 0 := by
  split_ifs with h
  · obtain ⟨j, hj⟩ := h
    exact two_mul_card_dotProduct_eq_true (w := fun i => z (e i)) hj
  · simp only [not_exists, Bool.not_eq_true] at h
    have h0 : (fun j => z (e j)) = 0 := funext h
    rw [h0]
    simp only [dotProduct_zero]
    change 2 * #{c : Fin P → Bool | false = true} = 0
    simp

/-- **The exact number of rejecting lists**: `2 ^ (P - 1) (m ^ P - (m - weight z) ^ P)`, written
without division. -/
theorem two_mul_card_testParity_eq_true (z : Fin m → Bool) :
    2 * #{γ : Fin P → Fin m × Bool | testParity γ z = true} =
      2 ^ P * (m ^ P - #{i | z i = false} ^ P) := by
  have h1 : #{γ : Fin P → Fin m × Bool | testParity γ z = true} =
      ∑ e : Fin P → Fin m, #{c : Fin P → Bool | c ⬝ᵥ (fun j => z (e j)) = true} := by
    rw [card_filter, ← (Equiv.arrowProdEquivProdArrow (Fin P) (fun _ => Fin m)
      (fun _ => Bool)).symm.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [card_filter]
    rfl
  rw [h1, Finset.mul_sum]
  simp only [two_mul_card_coeff, Finset.sum_ite, sum_const_zero, add_zero, sum_const,
    smul_eq_mul]
  rw [mul_comm]
  congr 1
  have hc := card_filter_add_card_filter_not (s := (univ : Finset (Fin P → Fin m)))
    (p := fun e => ∃ j, z (e j) = true)
  have h0 : #{e : Fin P → Fin m | ¬ ∃ j, z (e j) = true} = #{i | z i = false} ^ P := by
    rw [← Fintype.card_piFinset_const]
    congr 1
    ext e
    simp [Fintype.mem_piFinset]
  rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, h0] at hc
  omega

/-- If `t₀ P ≤ m (P - 1)` with `P ≥ 1`, then `2 t₀ ^ P ≤ m ^ P`, since
`(1 - 1/P) ^ P ≤ e⁻¹ < 1/2`. -/
private theorem two_mul_pow_le_pow {m t₀ P : ℕ} (hP : 1 ≤ P) (ht₀ : t₀ * P ≤ m * (P - 1)) :
    2 * t₀ ^ P ≤ m ^ P := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain rfl : t₀ = 0 := by
      rcases Nat.eq_zero_or_pos t₀ with h | h
      · exact h
      · simp only [zero_mul, nonpos_iff_eq_zero, mul_eq_zero] at ht₀; omega
    simp [Nat.pos_iff_ne_zero.mp hP]
  have hPr : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hPpos : (0 : ℝ) < P := by linarith
  have hle : (t₀ : ℝ) ≤ m * (1 - 1 / P) := by
    have h' : ((t₀ * P : ℕ) : ℝ) ≤ ((m * (P - 1) : ℕ) : ℝ) := by exact_mod_cast ht₀
    push_cast [Nat.cast_sub hP] at h'
    rw [show (m : ℝ) * (1 - 1 / P) = m * (P - 1) / P by field_simp, le_div_iff₀ hPpos]
    exact h'
  have h1 : (t₀ : ℝ) ^ P ≤ (m : ℝ) ^ P * (1 - 1 / P) ^ P := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hle P
  have h2 : (m : ℝ) ^ P * (1 - 1 / P) ^ P < (m : ℝ) ^ P * (1 / 2) :=
    mul_lt_mul_of_pos_left ((Real.one_sub_div_pow_le_exp_neg hPr).trans_lt
      Real.exp_neg_one_lt_half) (by positivity)
  have : (2 : ℝ) * (t₀ : ℝ) ^ P < (m : ℝ) ^ P := by linarith
  exact_mod_cast this.le

/-- **A quarter of the lists reject** a bit string with at least `m / P` ones. -/
theorem pow_le_four_mul_card_testParity_eq_true (z : Fin m → Bool) (hP : 1 ≤ P)
    (hz : m ≤ P * weight z) :
    (2 * m) ^ P ≤ 4 * #{γ : Fin P → Fin m × Bool | testParity γ z = true} := by
  have hc := two_mul_card_testParity_eq_true (P := P) z
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin m)))
    (p := fun i => z i = false)
  rw [card_univ, Fintype.card_fin] at hsplit
  have hw : #{i | ¬ z i = false} = weight z := by
    simp only [Bool.not_eq_false]; rfl
  rw [hw] at hsplit
  set t₀ := #{i | z i = false}
  have ht₀ : t₀ * P ≤ m * (P - 1) := by
    have h : t₀ * P + m ≤ m * P := by
      calc t₀ * P + m ≤ t₀ * P + P * weight z := by omega
        _ = (t₀ + weight z) * P := by ring
        _ = m * P := by rw [hsplit]
    have e : m * P = m * (P - 1) + m := by
      rw [← Nat.mul_succ]
      congr 1
      omega
    omega
  have hkey := two_mul_pow_le_pow hP ht₀
  have hle : t₀ ^ P ≤ m ^ P := Nat.pow_le_pow_left (by omega) P
  have : 2 ^ P * m ^ P ≤ 2 * (2 ^ P * (m ^ P - t₀ ^ P)) := by
    rw [Nat.mul_sub, Nat.mul_sub]
    have h2 : 2 ^ P * t₀ ^ P * 2 ≤ 2 ^ P * m ^ P := by
      calc 2 ^ P * t₀ ^ P * 2 = 2 ^ P * (2 * t₀ ^ P) := by ring
        _ ≤ 2 ^ P * m ^ P := Nat.mul_le_mul_left _ hkey
    have h3 : 2 ^ P * t₀ ^ P ≤ 2 ^ P * m ^ P := Nat.mul_le_mul_left _ hle
    omega
  rw [mul_pow]
  omega

/-! ### Averaging and iteration -/

/-- **Averaging.** A list minimizing the number of accepted strings accepts at most three quarters
of a set of nonzero bit strings, each with at least `m / P` ones. -/
theorem four_mul_card_accept_le_of_forall_le {ι : Type*} (S : Finset ι) (z : ι → Fin m → Bool)
    (hP : 1 ≤ P) (hz₀ : ∀ x ∈ S, z x ≠ 0) (hz : ∀ x ∈ S, m ≤ P * weight (z x))
    (γ : Fin P → Fin m × Bool)
    (hγ : ∀ γ' : Fin P → Fin m × Bool,
      #{x ∈ S | testParity γ (z x) = false} ≤ #{x ∈ S | testParity γ' (z x) = false}) :
    4 * #{x ∈ S | testParity γ (z x) = false} ≤ 3 * #S := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  have hm : 0 < m := by
    by_contra h
    obtain rfl : m = 0 := by omega
    exact hz₀ x₀ hx₀ (funext fun i => i.elim0)
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  set N := Fintype.card (Fin P → Fin m × Bool) with hN
  have hNpos : 0 < N := Fintype.card_pos
  have hNval : N = (2 * m) ^ P := by
    rw [hN, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
      Fintype.card_fin, mul_comm]
  -- each string is accepted by at most three quarters of the lists
  have hB : ∀ x ∈ S, 4 * #{γ' : Fin P → Fin m × Bool | testParity γ' (z x) = false} ≤ 3 * N := by
    intro x hx
    have hrej := pow_le_four_mul_card_testParity_eq_true (z x) hP (hz x hx)
    have hsplit := card_filter_add_card_filter_not
      (s := (univ : Finset (Fin P → Fin m × Bool))) (p := fun γ' => testParity γ' (z x) = true)
    simp only [Bool.not_eq_true] at hsplit
    rw [card_univ, ← hN] at hsplit
    rw [← hNval] at hrej
    omega
  -- double counting
  have hA : ∑ γ' : Fin P → Fin m × Bool, #{x ∈ S | testParity γ' (z x) = false} =
      ∑ x ∈ S, #{γ' : Fin P → Fin m × Bool | testParity γ' (z x) = false} := by
    simp only [card_filter]
    exact Finset.sum_comm
  have hsum : 4 * ∑ γ' : Fin P → Fin m × Bool, #{x ∈ S | testParity γ' (z x) = false} ≤
      3 * #S * N := by
    rw [hA, Finset.mul_sum]
    calc ∑ x ∈ S, 4 * #{γ' : Fin P → Fin m × Bool | testParity γ' (z x) = false}
        ≤ ∑ _x ∈ S, 3 * N := Finset.sum_le_sum hB
      _ = 3 * #S * N := by rw [sum_const, smul_eq_mul]; ring
  have hmin : N * #{x ∈ S | testParity γ (z x) = false} ≤
      ∑ γ' : Fin P → Fin m × Bool, #{x ∈ S | testParity γ' (z x) = false} := by
    have := Finset.card_nsmul_le_sum (univ : Finset (Fin P → Fin m × Bool))
      (fun γ' => #{x ∈ S | testParity γ' (z x) = false}) _ (fun γ' _ => hγ γ')
    rwa [card_univ, smul_eq_mul] at this
  have : N * (4 * #{x ∈ S | testParity γ (z x) = false}) ≤ N * (3 * #S) := by
    nlinarith
  exact Nat.le_of_mul_le_mul_left this hNpos

/-- **Iteration.** A sequence of naturals that starts at most `2 ^ n`, with `n ≥ 1`, and shrinks
by a factor of at least `3/4` at each step vanishes after `3 n` steps, since
`(3/4) ^ (3n) 2 ^ n = (27/32) ^ n < 1`. -/
theorem eq_zero_of_four_mul_le_three_mul (D : ℕ → ℕ) {n : ℕ} (hn : 1 ≤ n) (h₀ : D 0 ≤ 2 ^ n)
    (hstep : ∀ i, 4 * D (i + 1) ≤ 3 * D i) : D (3 * n) = 0 := by
  have hpow : ∀ i, 4 ^ i * D i ≤ 3 ^ i * D 0 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc 4 ^ (i + 1) * D (i + 1) = 4 ^ i * (4 * D (i + 1)) := by ring
        _ ≤ 4 ^ i * (3 * D i) := Nat.mul_le_mul_left _ (hstep i)
        _ = 3 * (4 ^ i * D i) := by ring
        _ ≤ 3 * (3 ^ i * D 0) := Nat.mul_le_mul_left _ ih
        _ = 3 ^ (i + 1) * D 0 := by ring
  have e₃ : 3 ^ (3 * n) = 27 ^ n := by rw [pow_mul]; norm_num
  have e₄ : 4 ^ (3 * n) = 64 ^ n := by rw [pow_mul]; norm_num
  have h₁ : 3 ^ (3 * n) * D 0 ≤ 54 ^ n := by
    calc 3 ^ (3 * n) * D 0 ≤ 27 ^ n * 2 ^ n := by
          rw [e₃]; exact Nat.mul_le_mul_left _ h₀
      _ = 54 ^ n := by rw [← mul_pow]; norm_num
  have h₂ : 54 ^ n < 4 ^ (3 * n) := by
    rw [e₄]; exact Nat.pow_lt_pow_left (by norm_num) (by omega)
  by_contra hD
  have := Nat.le_mul_of_pos_right (4 ^ (3 * n)) (Nat.pos_of_ne_zero hD)
  have := hpow (3 * n)
  omega

/-! ### The greedy procedure -/

variable {X : Type*}

/-- The rows `A` accept the point `x`: every row has parity zero on its violation vector. -/
def PassesTests (v : X → Fin m → Bool) (A : List (Fin m → Bool)) (x : X) : Prop :=
  ∀ h ∈ A, h ⬝ᵥ v x = false

instance (v : X → Fin m → Bool) (A : List (Fin m → Bool)) : DecidablePred (PassesTests v A) :=
  fun _ => List.decidableBAll _ _

theorem passesTests_append_singleton (v : X → Fin m → Bool) (A : List (Fin m → Bool))
    (h : Fin m → Bool) (x : X) :
    PassesTests v (A ++ [h]) x ↔ PassesTests v A x ∧ h ⬝ᵥ v x = false := by
  simp [PassesTests, or_imp, forall_and]

variable [Fintype X]

/-- `N(A)`: the number of points accepted by the rows `A`. -/
def numPassing (v : X → Fin m → Bool) (A : List (Fin m → Bool)) : ℕ :=
  #{x | PassesTests v A x}

/-- `N(A) = #F + D(A)`: every point with zero violation vector is accepted, so the number of
accepted points is the number of such points plus the number of accepted points with a nonzero
violation vector. -/
theorem numPassing_eq (v : X → Fin m → Bool) (A : List (Fin m → Bool)) :
    numPassing v A = #{x | v x = 0} + #{x | PassesTests v A x ∧ v x ≠ 0} := by
  rw [numPassing, ← card_filter_add_card_filter_not (s := {x | PassesTests v A x})
    (p := fun x => v x = 0), filter_filter, filter_filter]
  congr 2
  ext x
  simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
  intro hx h _
  rw [hx, dotProduct_zero]
  rfl

/-- **Greedy selection of parity tests** [OpenAI2026ETH, Lemma 6.2]. Suppose that after the
initial rows `A 0`, every accepted point with a nonzero violation vector has at least `m / P`
violations, and that there are at most `2 ^ n` points, with `n ≥ 1`. Append rows
`A (i + 1) = A i ++ [testRow (γ i)]`, where each list `γ i` minimizes the number of accepted
points among all lists. Then after `3 n` rounds the rows accept exactly the points with zero
violation vector. -/
theorem numPassing_greedy (v : X → Fin m → Bool) {n : ℕ} (hn : 1 ≤ n)
    (hX : Fintype.card X ≤ 2 ^ n) (hP : 1 ≤ P) (A : ℕ → List (Fin m → Bool))
    (hinit : ∀ x, PassesTests v (A 0) x → v x ≠ 0 → m ≤ P * weight (v x))
    (γ : ℕ → Fin P → Fin m × Bool) (hA : ∀ i, A (i + 1) = A i ++ [testRow (γ i)])
    (hγ : ∀ i (γ' : Fin P → Fin m × Bool),
      numPassing v (A i ++ [testRow (γ i)]) ≤ numPassing v (A i ++ [testRow γ'])) :
    numPassing v (A (3 * n)) = #{x | v x = 0} := by
  set D : ℕ → ℕ := fun i => #{x | PassesTests v (A i) x ∧ v x ≠ 0} with hD
  have hpre : ∀ i x, PassesTests v (A i) x → PassesTests v (A 0) x := by
    intro i
    induction i with
    | zero => exact fun _ h => h
    | succ i ih => intro x h; rw [hA, passesTests_append_singleton] at h; exact ih x h.1
  have hstep : ∀ i, 4 * D (i + 1) ≤ 3 * D i := by
    intro i
    set S := ({x | PassesTests v (A i) x ∧ v x ≠ 0} : Finset X)
    have hcount : ∀ γ' : Fin P → Fin m × Bool,
        #{x | PassesTests v (A i ++ [testRow γ']) x ∧ v x ≠ 0} =
          #{x ∈ S | testParity γ' (v x) = false} := fun γ' => by
      congr 1
      ext x
      simp only [S, mem_filter, mem_univ, true_and, passesTests_append_singleton,
        testRow_dotProduct]
      tauto
    have hmin : ∀ γ' : Fin P → Fin m × Bool,
        #{x ∈ S | testParity (γ i) (v x) = false} ≤ #{x ∈ S | testParity γ' (v x) = false} := by
      intro γ'
      have := hγ i γ'
      rw [numPassing_eq, numPassing_eq, hcount, hcount] at this
      omega
    have := four_mul_card_accept_le_of_forall_le S v hP
      (fun x hx => (mem_filter.mp hx).2.2)
      (fun x hx => hinit x (hpre i x (mem_filter.mp hx).2.1) (mem_filter.mp hx).2.2) (γ i) hmin
    simp only [hD, hA, ← hcount] at this ⊢
    exact this
  have h₀ : D 0 ≤ 2 ^ n := (card_le_univ _).trans hX
  have hfin := eq_zero_of_four_mul_le_three_mul D hn h₀ hstep
  rw [numPassing_eq]
  simp only [hD] at hfin
  rw [hfin, add_zero]

end Cslib.BitString
