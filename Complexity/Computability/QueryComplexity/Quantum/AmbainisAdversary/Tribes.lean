/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.Quantum.AmbainisAdversary
public import Complexity.Foundations.BooleanAnalysis.Tribes
public import Complexity.Foundations.Data.BitString.Sign
import Complexity.Foundations.Quantum.Measurement.Overlap

/-!
# Tribes and the `AND` of `OR`s by the adversary method

Split `s w` bits into `s` blocks of `w` bits, bit `i` of block `j` being bit
`finProdFinEquiv (j, i)`. The `AND` of `OR`s is true when every block contains a true bit, and
Tribes (`Cslib.BitString.tribes`, an `OR` of `AND`s) is true when some block is all true. The
two functions are De Morgan duals.

[Ambainis2002], Theorem 4, shows that the `AND` of `√N` `OR`s of `√N` bits takes `Ω(√N)` quantum
queries, whereas the `√bs(f)` lower bounds of the hybrid and polynomial methods give only
`Ω(N^{1/4})` for it, since its block sensitivity is `Θ(√N)`. The relation is that of single bit
flips between the inputs with exactly one true bit in every block and those with one all-false
block and exactly one true bit in every other block. An input of the first kind has `w` neighbors
of the second, and an input of the second kind has `s` neighbors of the first
(`Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_of_neighbors`). So an algorithm computing the `AND` of
`OR`s with error `ε ≤ 1/2` has `(1 - 2√(ε(1-ε))) √(w s) ≤ 2T`
(`Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_of_forall_exists`), which is Theorem 4 when
`w = s = √N`. The same bound holds for Tribes
(`Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_of_tribes`). At error `1/3` both give
`w s ≤ 1296 T²`.

Both bounds require correctness only under the promise that every block has at most one true bit
(for the `AND` of `OR`s) or at most one false bit (for Tribes), so they hold for the promise
problems as well. The constants are those of this proof. The source states `Ω(√N)`.

## Main results

* `Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_of_forall_exists`: the `AND` of `OR`s,
  `(1 - 2√(ε(1-ε))) √(w s) ≤ 2T`.
* `Cslib.Quantum.mul_le_mul_sq_of_forall_exists`: the `AND` of `OR`s, `w s ≤ 1296 T²` at error
  `1/3`.
* `Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_of_tribes`: Tribes, `(1 - 2√(ε(1-ε))) √(w s) ≤ 2T`.
* `Cslib.Quantum.mul_le_mul_sq_of_tribes`: Tribes, `w s ≤ 1296 T²` at error `1/3`.

## References

* [A. Ambainis, *Quantum lower bounds by quantum arguments*][Ambainis2002]
-/

public section

namespace Cslib.Quantum

open Finset Function BitString

variable {W : Type*} [Fintype W] {w s : ℕ}

/-- The number of bits of block `j` of `x` equal to `b`. -/
private noncomputable def blockCount (b : Bool) (x : BitString (s * w)) (j : Fin s) : ℕ :=
  #{i | x (finProdFinEquiv (j, i)) = b}

/-- Changing a bit of one block leaves the counts of the other blocks unchanged. -/
private theorem blockCount_update_of_ne (b : Bool) (x : BitString (s * w)) {j j' : Fin s}
    (hj : j' ≠ j) (i : Fin w) (v : Bool) :
    blockCount b (update x (finProdFinEquiv (j, i)) v) j' = blockCount b x j' := by
  unfold blockCount
  congr 1
  refine filter_congr fun i' _ => ?_
  rw [update_of_ne]
  intro h
  exact hj (congrArg Prod.fst (finProdFinEquiv.injective h))

/-- Setting a bit to `b` in a block without bits equal to `b` leaves exactly one. -/
private theorem blockCount_update_of_eq_zero (b : Bool) {x : BitString (s * w)} {j : Fin s}
    (hx : blockCount b x j = 0) (i : Fin w) :
    blockCount b (update x (finProdFinEquiv (j, i)) b) j = 1 := by
  unfold blockCount at hx ⊢
  rw [card_eq_one]
  refine ⟨i, eq_singleton_iff_unique_mem.2 ⟨by simp, fun i' hi' => ?_⟩⟩
  by_contra hne
  have hi'' := (mem_filter.1 hi').2
  rw [update_of_ne fun h => hne (congrArg Prod.snd (finProdFinEquiv.injective h))] at hi''
  exact (filter_eq_empty_iff.1 (card_eq_zero.1 hx)) (mem_univ i') hi''

/-- Flipping the only bit equal to `b` in a block leaves none. -/
private theorem blockCount_update_of_eq_one (b : Bool) {x : BitString (s * w)} {j : Fin s}
    {i : Fin w} (hx : blockCount b x j = 1) (hi : x (finProdFinEquiv (j, i)) = b) :
    blockCount b (update x (finProdFinEquiv (j, i)) (!x (finProdFinEquiv (j, i)))) j = 0 := by
  unfold blockCount at hx ⊢
  obtain ⟨i₀, hi₀⟩ := card_eq_one.1 hx
  have hii : i = i₀ := mem_singleton.1 (hi₀ ▸ mem_filter.2 ⟨mem_univ i, hi⟩)
  refine card_eq_zero.2 (filter_eq_empty_iff.2 fun i' _ hi' => ?_)
  by_cases h : i' = i
  · subst h
    rw [update_self, hi] at hi'
    cases b <;> simp at hi'
  · rw [update_of_ne fun h' => h (congrArg Prod.snd (finProdFinEquiv.injective h'))] at hi'
    have := mem_singleton.1 (hi₀ ▸ mem_filter.2 ⟨mem_univ i', hi'⟩)
    exact h (this.trans hii.symm)

/-- **The block relation of [Ambainis2002], Theorem 4**: let a `T`-query algorithm with a unit
initial state end in states with overlap at most `δ` on every input `x` that has a block without
bits equal to `b` and exactly one in each other block, and every input `y` with exactly one bit
equal to `b` in every block. Then `(1 - δ) √(w s) ≤ 2T`. -/
private theorem one_sub_mul_sqrt_le_two_mul_of_blockCount (b : Bool)
    (U : ℕ → State (s * w) W →ₗᵢ[ℂ] State (s * w) W) {ψ₀ : State (s * w) W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) {δ : ℝ}
    (hδ : ∀ x y : BitString (s * w), (∀ j, blockCount b x j ≤ 1) →
      (∃ j, blockCount b x j = 0) → (∀ j, blockCount b y j = 1) →
      ‖inner ℂ (run U ψ₀ x T) (run U ψ₀ y T)‖ ≤ δ) :
    (1 - δ) * √(w * s) ≤ 2 * T := by
  classical
  rcases Nat.eq_zero_or_pos w with hw | hw
  · subst hw
    simp
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    simp
  set A : Finset (BitString (s * w)) :=
    {x | ∃ j₀, blockCount b x j₀ = 0 ∧ ∀ j ≠ j₀, blockCount b x j = 1}
  set B : Finset (BitString (s * w)) := {y | ∀ j, blockCount b y j = 1}
  -- a witness: block `0` has no bit equal to `b`, every other block has its bit `0` equal to `b`
  have hA : A.Nonempty := by
    let j₀ : Fin s := ⟨0, hs⟩
    let i₀ : Fin w := ⟨0, hw⟩
    let x : BitString (s * w) := fun k =>
      if (finProdFinEquiv.symm k).1 ≠ j₀ ∧ (finProdFinEquiv.symm k).2 = i₀ then b else !b
    have hx (j : Fin s) (i : Fin w) :
        x (finProdFinEquiv (j, i)) = if j ≠ j₀ ∧ i = i₀ then b else !b := by
      simp only [x, Equiv.symm_apply_apply]
    refine ⟨x, mem_filter.2 ⟨mem_univ _, j₀, ?_, fun j hj => ?_⟩⟩
    · refine card_eq_zero.2 (filter_eq_empty_iff.2 fun i _ => ?_)
      rw [hx, ite_eq_right fun h => h.1 rfl]
      cases b <;> decide
    · refine card_eq_one.2 ⟨i₀, eq_singleton_iff_unique_mem.2 ⟨?_, fun i hi => ?_⟩⟩
      · exact mem_filter.2 ⟨mem_univ _, by rw [hx, ite_eq_left ⟨hj, rfl⟩]⟩
      · have hi' := (mem_filter.1 hi).2
        by_contra hne
        rw [hx, ite_eq_right fun h => hne h.2] at hi'
        cases b <;> simp at hi'
  have hm : ∀ x ∈ A, w ≤ #{k | update x k (!x k) ∈ B} := by
    intro x hx
    obtain ⟨j₀, h0, h1⟩ := (mem_filter.1 hx).2
    have hfalse : ∀ i, x (finProdFinEquiv (j₀, i)) = !b := fun i => by
      have := filter_eq_empty_iff.1 (card_eq_zero.1 h0) (mem_univ i)
      cases hb : b <;> cases hx : x (finProdFinEquiv (j₀, i)) <;> simp_all
    calc w = #(univ : Finset (Fin w)) := by rw [card_univ, Fintype.card_fin]
      _ ≤ _ := card_le_card_of_injOn (fun i => finProdFinEquiv (j₀, i)) (fun i _ => ?_)
          fun i _ i' _ h => congrArg Prod.snd (finProdFinEquiv.injective h)
    refine mem_filter.2 ⟨mem_univ _, mem_filter.2 ⟨mem_univ _, fun j => ?_⟩⟩
    rw [hfalse i, Bool.not_not]
    by_cases hj : j = j₀
    · subst hj
      exact blockCount_update_of_eq_zero b h0 i
    · rw [blockCount_update_of_ne b x hj]
      exact h1 j hj
  have hm' : ∀ y ∈ B, s ≤ #{k | update y k (!y k) ∈ A} := by
    intro y hy
    have h1 : ∀ j, blockCount b y j = 1 := (mem_filter.1 hy).2
    -- the bit of block `j` equal to `b`
    have hex : ∀ j, ∃ i, y (finProdFinEquiv (j, i)) = b := fun j => by
      obtain ⟨i, hi⟩ := card_eq_one.1 (h1 j)
      exact ⟨i, (mem_filter.1 (hi ▸ mem_singleton_self i : i ∈ _)).2⟩
    choose g hg using hex
    calc s = #(univ : Finset (Fin s)) := by rw [card_univ, Fintype.card_fin]
      _ ≤ _ := card_le_card_of_injOn (fun j => finProdFinEquiv (j, g j)) (fun j _ => ?_)
          fun j _ j' _ h => congrArg Prod.fst (finProdFinEquiv.injective h)
    refine mem_filter.2 ⟨mem_univ _, mem_filter.2 ⟨mem_univ _, j,
      blockCount_update_of_eq_one b (h1 j) (hg j), fun j' hj' => ?_⟩⟩
    rw [blockCount_update_of_ne b y hj']
    exact h1 j'
  refine one_sub_mul_sqrt_le_two_mul_of_neighbors U hψ₀ T hA (fun x hx k hk => ?_) hm hm'
  obtain ⟨j₀, h0, h1⟩ := (mem_filter.1 hx).2
  refine hδ x _ (fun j => ?_) ⟨j₀, h0⟩ (mem_filter.1 hk).2
  by_cases hj : j = j₀
  · rw [hj, h0]
    exact zero_le_one
  · exact (h1 j hj).le

/-- **Tribes takes `Ω(√(w s))` queries**, the De Morgan dual of [Ambainis2002], Theorem 4: if a
`T`-query algorithm with a unit initial state accepts, by an outcome in `S`, every input `x` in
which every tribe has at most one false bit with probability within `ε ≤ 1/2` of
`Tribes_{w,s}(x)`, then `(1 - 2√(ε(1-ε))) √(w s) ≤ 2T`. -/
theorem one_sub_mul_sqrt_le_two_mul_of_tribes
    (U : ℕ → State (s * w) W →ₗᵢ[ℂ] State (s * w) W) {ψ₀ : State (s * w) W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) (S : Finset (Fin (s * w) × Bool × W)) {ε : ℝ}
    (h : ∀ x : BitString (s * w), (∀ j, #{i | x (finProdFinEquiv (j, i)) = false} ≤ 1) →
      |measureProb (run U ψ₀ x T) S - bitVal ℝ (tribes w s x)| ≤ ε) (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) * √(w * s) ≤ 2 * T := by
  refine one_sub_mul_sqrt_le_two_mul_of_blockCount false U hψ₀ T fun x y hx hx0 hy => ?_
  obtain ⟨j₀, h0⟩ := hx0
  have htx : tribes w s x = true := tribes_eq_true_iff.2 ⟨j₀, fun i => by
    have := filter_eq_empty_iff.1 (card_eq_zero.1 h0) (mem_univ i)
    simpa using this⟩
  have hty : tribes w s y = false := by
    by_contra hne
    obtain ⟨j, hj⟩ := tribes_eq_true_iff.1 (Bool.not_eq_false _ ▸ hne)
    have := hy j
    unfold blockCount at this
    rw [card_eq_zero.2 (filter_eq_empty_iff.2 fun i _ => by simp [hj i])] at this
    exact zero_ne_one this
  have hx' := (abs_le.1 (h x hx)).1
  have hy' := (abs_le.1 (h y fun j => (hy j).le)).2
  rw [htx, bitVal_true] at hx'
  rw [hty, bitVal_false] at hy'
  exact norm_inner_le_two_mul_sqrt_of_measureProb (by rw [norm_run, hψ₀]) (by rw [norm_run, hψ₀])
    (by linarith) (by linarith) hε

/-- **The `AND` of `OR`s takes `Ω(√(w s))` queries** [Ambainis2002], Theorem 4: if a `T`-query
algorithm with a unit initial state accepts, by an outcome in `S`, every input `x` in which every
block has at most one true bit with probability within `ε ≤ 1/2` of the `AND` over the `s` blocks
of the `OR` of their `w` bits, then `(1 - 2√(ε(1-ε))) √(w s) ≤ 2T`. Theorem 4 is the case
`w = s = √N`. -/
theorem one_sub_mul_sqrt_le_two_mul_of_forall_exists
    (U : ℕ → State (s * w) W →ₗᵢ[ℂ] State (s * w) W) {ψ₀ : State (s * w) W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) (S : Finset (Fin (s * w) × Bool × W)) {ε : ℝ}
    (h : ∀ x : BitString (s * w), (∀ j, #{i | x (finProdFinEquiv (j, i)) = true} ≤ 1) →
      |measureProb (run U ψ₀ x T) S -
        bitVal ℝ (decide (∀ j : Fin s, ∃ i : Fin w, x (finProdFinEquiv (j, i)) = true))| ≤ ε)
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) * √(w * s) ≤ 2 * T := by
  refine one_sub_mul_sqrt_le_two_mul_of_blockCount true U hψ₀ T fun x y hx hx0 hy => ?_
  obtain ⟨j₀, h0⟩ := hx0
  have hfx : decide (∀ j : Fin s, ∃ i : Fin w, x (finProdFinEquiv (j, i)) = true) = false := by
    refine decide_eq_false fun hall => ?_
    obtain ⟨i, hi⟩ := hall j₀
    exact filter_eq_empty_iff.1 (card_eq_zero.1 h0) (mem_univ i) hi
  have hfy : decide (∀ j : Fin s, ∃ i : Fin w, y (finProdFinEquiv (j, i)) = true) = true := by
    refine decide_eq_true fun j => ?_
    obtain ⟨i, hi⟩ := card_eq_one.1 (hy j)
    exact ⟨i, (mem_filter.1 (hi ▸ mem_singleton_self i : i ∈ _)).2⟩
  have hx' := (abs_le.1 (h x hx)).2
  have hy' := (abs_le.1 (h y fun j => (hy j).le)).1
  rw [hfx, bitVal_false] at hx'
  rw [hfy, bitVal_true] at hy'
  rw [norm_inner_symm]
  exact norm_inner_le_two_mul_sqrt_of_measureProb (by rw [norm_run, hψ₀]) (by rw [norm_run, hψ₀])
    (by linarith) (by linarith) hε

/-- From `(1 - 2√(2/9)) √(w s) ≤ 2T` to `w s ≤ 1296 T²`. -/
private theorem mul_le_mul_sq_of_one_sub_mul_sqrt_le {T : ℕ}
    (h : (1 - 2 * √((1 / 3 : ℝ) * (1 - 1 / 3))) * √(w * s) ≤ 2 * T) : w * s ≤ 1296 * T ^ 2 := by
  -- `2√(2/9) ≤ 17/18`, since `8/9 = 288/324 ≤ 289/324`
  have hsqrt : √((1 / 3 : ℝ) * (1 - 1 / 3)) ≤ 17 / 36 :=
    (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have h0 : 0 ≤ √((w : ℝ) * s) := Real.sqrt_nonneg _
  have h36 : √((w : ℝ) * s) ≤ 36 * T := by nlinarith
  have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ w * s)
  have : (w : ℝ) * s ≤ 1296 * T ^ 2 := by nlinarith
  exact_mod_cast this

/-- **Tribes at error `1/3`**: if a `T`-query algorithm with a unit initial state accepts, by an
outcome in `S`, every input `x` in which every tribe has at most one false bit with probability
within `1/3` of `Tribes_{w,s}(x)`, then `w s ≤ 1296 T²`. -/
theorem mul_le_mul_sq_of_tribes
    (U : ℕ → State (s * w) W →ₗᵢ[ℂ] State (s * w) W) {ψ₀ : State (s * w) W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) (S : Finset (Fin (s * w) × Bool × W))
    (h : ∀ x : BitString (s * w), (∀ j, #{i | x (finProdFinEquiv (j, i)) = false} ≤ 1) →
      |measureProb (run U ψ₀ x T) S - bitVal ℝ (tribes w s x)| ≤ 1 / 3) :
    w * s ≤ 1296 * T ^ 2 :=
  mul_le_mul_sq_of_one_sub_mul_sqrt_le
    (one_sub_mul_sqrt_le_two_mul_of_tribes U hψ₀ T S h (by norm_num))

/-- **The `AND` of `OR`s at error `1/3`** [Ambainis2002], Theorem 4: if a `T`-query algorithm
with a unit initial state accepts, by an outcome in `S`, every input `x` in which every block has
at most one true bit with probability within `1/3` of the `AND` over the `s` blocks of the `OR` of
their `w` bits, then `w s ≤ 1296 T²`. -/
theorem mul_le_mul_sq_of_forall_exists
    (U : ℕ → State (s * w) W →ₗᵢ[ℂ] State (s * w) W) {ψ₀ : State (s * w) W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) (S : Finset (Fin (s * w) × Bool × W))
    (h : ∀ x : BitString (s * w), (∀ j, #{i | x (finProdFinEquiv (j, i)) = true} ≤ 1) →
      |measureProb (run U ψ₀ x T) S -
        bitVal ℝ (decide (∀ j : Fin s, ∃ i : Fin w, x (finProdFinEquiv (j, i)) = true))| ≤ 1 / 3) :
    w * s ≤ 1296 * T ^ 2 :=
  mul_le_mul_sq_of_one_sub_mul_sqrt_le
    (one_sub_mul_sqrt_le_two_mul_of_forall_exists U hψ₀ T S h (by norm_num))

end Cslib.Quantum
