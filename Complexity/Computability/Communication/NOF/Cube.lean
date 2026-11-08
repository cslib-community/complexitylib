/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Communication.NOF.Discrepancy
public import Mathlib.Data.Finset.Piecewise
import Complexity.Foundations.Data.Finset.ExpectResample
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.Positivity

/-!
# The cube bound on multiparty discrepancy

Two inputs `a, b : ∀ i, X i` span a *cube* with `2 ^ k` corners `S.piecewise b a`, for `S` a set of
players: the input that agrees with `b` on the players of `S` and with `a` on the others. The *cube
expectation* `E(f)` of `f : (∀ i, X i) → Bool` is the average over independent uniform `a` and `b`
of the product of the signs `(-1) ^ f` at the corners (`NOF.cubeExpectation`). The cube bound
says that with `k ≥ 1` players the discrepancy of `f` under the uniform distribution satisfies
`disc(f) ^ (2 ^ k) ≤ E(f)` (`NOF.discrepancy_uniformOfFintype_pow_le`). This is the BNS–Chung
criterion [BabaiNisanSzegedy1992][Chung1990], in the proof of Raz [Raz2000]; see also
[Jukna, Section 5.6][Jukna2012]. So to bound the discrepancy, and
with it the communication complexity of `f` (`NOF.PublicCoin.two_mul_le_two_pow_mul_discrepancy`),
it suffices to compute the cube expectation.

The proof is `k` applications of the Cauchy–Schwarz inequality, one per player
(`NOF.pow_expect_mul_prod_le`). A cylinder intersection's indicator is the product over players `i`
of a function `g i` of what player `i` sees, so `g i` does not depend on `x i`. Resampling `x i`
(`Fintype.expect_expect_update_pi`) and applying Cauchy–Schwarz removes `g i` at the cost of
squaring, and duplicates `x i` into the two coordinates `a i`, `b i` of the cube.

## Main definitions

* `Cslib.Communication.NOF.cubeExpectation`: the cube expectation of a Boolean function.

## Main results

* `Cslib.Communication.NOF.pow_expect_mul_prod_le`: the cube lemma, for any set of players and real
  functions.
* `Cslib.Communication.NOF.discrepancy_uniformOfFintype_pow_le`: the cube bound
  `disc(f) ^ (2 ^ k) ≤ E(f)`.

## References

* [L. Babai, N. Nisan and M. Szegedy, *Multiparty protocols, pseudorandom generators for logspace,
  and time-space trade-offs*][BabaiNisanSzegedy1992]
* [F. R. K. Chung, *Quasi-random classes of hypergraphs*][Chung1990]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
* [R. Raz, *The BNS–Chung criterion for multi-party communication complexity*][Raz2000]
-/

@[expose] public section

namespace Cslib.Communication.NOF

open Finset Function BitString Probability
open scoped BigOperators

universe u v

variable {ι : Type u} {X : ι → Type v}

section Cube

variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)]

omit [Fintype ι] [∀ i, Fintype (X i)] in
private theorem piecewise_update_update {S : Finset ι} {j : ι} (hj : j ∉ S) (a b : ∀ i, X i)
    (c d : X j) : S.piecewise (update b j d) (update a j c) = update (S.piecewise b a) j c := by
  funext i
  by_cases hij : i = j
  · subst hij
    simp [hj]
  · by_cases hi : i ∈ S <;> simp [hi, hij]

omit [Fintype ι] [∀ i, Fintype (X i)] in
private theorem piecewise_insert_update_update {S : Finset ι} {j : ι} (hj : j ∉ S) (a b : ∀ i, X i)
    (c d : X j) :
    (insert j S).piecewise (update b j d) (update a j c) = update (S.piecewise b a) j d := by
  rw [piecewise_insert, piecewise_update_update hj, update_idem, update_self]

/-- Resampling player `j`'s part of both corners of a cube: averaging over `c, d` the products
over the subcubes `S ⊆ T`, with `x j` set to `c` and to `d`, is the average over the cube with
`j ∉ T` added. -/
private theorem expect_expect_prod_update_eq {T : Finset ι} {j : ι} (hj : j ∉ T)
    (F : (∀ i, X i) → ℝ) :
    𝔼 c : X j, 𝔼 d : X j, 𝔼 a, 𝔼 b, ∏ S ∈ T.powerset,
        (F (update (S.piecewise b a) j c) * F (update (S.piecewise b a) j d)) =
      𝔼 a, 𝔼 b, ∏ S ∈ (insert j T).powerset, F (S.piecewise b a) := by
  symm
  calc _ = 𝔼 a, 𝔼 c : X j, 𝔼 b, 𝔼 d : X j, ∏ S ∈ (insert j T).powerset,
        F (S.piecewise (update b j d) (update a j c)) := by
        rw [← Fintype.expect_expect_update_pi _ j]
        refine Finset.expect_congr rfl fun a _ => Finset.expect_congr rfl fun c _ => ?_
        exact (Fintype.expect_expect_update_pi _ j).symm
    _ = 𝔼 c : X j, 𝔼 d : X j, 𝔼 a, 𝔼 b, ∏ S ∈ (insert j T).powerset,
        F (S.piecewise (update b j d) (update a j c)) := by
        rw [Finset.expect_comm]
        refine Finset.expect_congr rfl fun c _ => ?_
        rw [Finset.expect_congr rfl fun a _ => Finset.expect_comm _ _ _, Finset.expect_comm]
    _ = _ := by
        refine Finset.expect_congr rfl fun c _ => Finset.expect_congr rfl fun d _ => ?_
        refine Finset.expect_congr rfl fun a _ => Finset.expect_congr rfl fun b _ => ?_
        rw [prod_powerset_insert hj, ← prod_mul_distrib]
        refine prod_congr rfl fun S hS => ?_
        have hjS : j ∉ S := fun h => hj (mem_powerset.mp hS h)
        rw [piecewise_update_update hjS, piecewise_insert_update_update hjS]

/-- **The cube lemma**: the correlation of `F` with a product of bounded functions `g i`, each not
depending on `x i`, over the players `i ∈ T`, is controlled by the averages of products of `F`
over the `2 ^ |T|` corners `S.piecewise b a`, `S ⊆ T`, of a random cube. -/
theorem pow_expect_mul_prod_le (T : Finset ι) (F : (∀ i, X i) → ℝ)
    (g : ι → (∀ i, X i) → ℝ) (hg : ∀ i ∈ T, ∀ x (e : X i), g i (update x i e) = g i x)
    (hg1 : ∀ i ∈ T, ∀ x, |g i x| ≤ 1) :
    (𝔼 x, F x * ∏ i ∈ T, g i x) ^ (2 ^ #T) ≤
      𝔼 a, 𝔼 b, ∏ S ∈ T.powerset, F (S.piecewise b a) := by
  induction T using Finset.induction_on generalizing F g with
  | empty =>
    rcases isEmpty_or_nonempty (∀ i, X i) with h | h
    · simp
    · simp
  | @insert j T hj ih =>
    rw [card_insert_of_notMem hj, pow_succ', pow_mul]
    -- Resample player `j`'s part, on which `g j` does not depend.
    have hres : 𝔼 x, F x * ∏ i ∈ insert j T, g i x =
        𝔼 x, g j x * 𝔼 c : X j, F (update x j c) * ∏ i ∈ T, g i (update x j c) := by
      rw [← Fintype.expect_expect_update_pi _ j]
      refine Finset.expect_congr rfl fun x _ => ?_
      rw [Finset.mul_expect]
      refine Finset.expect_congr rfl fun c _ => ?_
      rw [prod_insert hj, hg j (mem_insert_self j T) x c]
      ring
    -- Cauchy–Schwarz, with `g j ^ 2 ≤ 1`.
    have hcs : (𝔼 x, F x * ∏ i ∈ insert j T, g i x) ^ 2 ≤
        𝔼 x, (𝔼 c : X j, F (update x j c) * ∏ i ∈ T, g i (update x j c)) ^ 2 := by
      rw [hres]
      refine (expect_mul_sq_le_sq_mul_sq _ _ _).trans ?_
      refine mul_le_of_le_one_left (Finset.expect_nonneg fun _ _ => sq_nonneg _) ?_
      rcases isEmpty_or_nonempty (∀ i, X i) with h | h
      · simp
      · refine Finset.expect_le Finset.univ_nonempty fun x _ => ?_
        rw [← sq_abs]
        exact pow_le_one₀ (abs_nonneg _) (hg1 j (mem_insert_self j T) x)
    -- Expanding the square over two independent copies `c`, `d` of player `j`'s part.
    have hexp : 𝔼 x, (𝔼 c : X j, F (update x j c) * ∏ i ∈ T, g i (update x j c)) ^ 2 =
        𝔼 c : X j, 𝔼 d : X j, 𝔼 x, (F (update x j c) * F (update x j d)) *
          ∏ i ∈ T, (g i (update x j c) * g i (update x j d)) := by
      calc _ = 𝔼 x, 𝔼 c : X j, 𝔼 d : X j, (F (update x j c) * F (update x j d)) *
            ∏ i ∈ T, (g i (update x j c) * g i (update x j d)) := by
            refine Finset.expect_congr rfl fun x _ => ?_
            rw [sq, Fintype.expect_mul_expect]
            refine Finset.expect_congr rfl fun c _ => Finset.expect_congr rfl fun d _ => ?_
            rw [prod_mul_distrib]
            ring
        _ = 𝔼 c : X j, 𝔼 x, 𝔼 d : X j, (F (update x j c) * F (update x j d)) *
            ∏ i ∈ T, (g i (update x j c) * g i (update x j d)) := Finset.expect_comm _ _ _
        _ = _ := Finset.expect_congr rfl fun c _ => Finset.expect_comm _ _ _
    -- The induction hypothesis, for the pair `F (x[j := c]) F (x[j := d])` and the functions
    -- `g i (x[j := c]) g i (x[j := d])`.
    have hih : ∀ c d : X j,
        (𝔼 x, (F (update x j c) * F (update x j d)) *
          ∏ i ∈ T, (g i (update x j c) * g i (update x j d))) ^ (2 ^ #T) ≤
        𝔼 a, 𝔼 b, ∏ S ∈ T.powerset,
          (F (update (S.piecewise b a) j c) * F (update (S.piecewise b a) j d)) := by
      intro c d
      refine ih (fun x => F (update x j c) * F (update x j d))
        (fun i x => g i (update x j c) * g i (update x j d)) (fun i hi x e => ?_)
        (fun i hi x => ?_)
      · by_cases hij : i = j
        · subst hij
          simp only [update_idem]
        · rw [update_comm hij e c x, update_comm hij e d x, hg i (mem_insert_of_mem hi),
            hg i (mem_insert_of_mem hi)]
      · rw [abs_mul]
        have h1 := hg1 i (mem_insert_of_mem hi)
        exact (mul_le_mul (h1 _) (h1 _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
    calc ((𝔼 x, F x * ∏ i ∈ insert j T, g i x) ^ 2) ^ (2 ^ #T)
        ≤ (𝔼 c : X j, 𝔼 d : X j, 𝔼 x, (F (update x j c) * F (update x j d)) *
            ∏ i ∈ T, (g i (update x j c) * g i (update x j d))) ^ (2 ^ #T) := by
          rw [← hexp]
          exact pow_le_pow_left₀ (sq_nonneg _) hcs _
      _ ≤ 𝔼 c : X j, 𝔼 d : X j, (𝔼 x, (F (update x j c) * F (update x j d)) *
            ∏ i ∈ T, (g i (update x j c) * g i (update x j d))) ^ (2 ^ #T) := by
          refine (pow_two_pow_expect_le_expect_pow_two_pow _ _ _).trans ?_
          exact Finset.expect_le_expect fun c _ => pow_two_pow_expect_le_expect_pow_two_pow _ _ _
      _ ≤ 𝔼 c : X j, 𝔼 d : X j, 𝔼 a, 𝔼 b, ∏ S ∈ T.powerset,
            (F (update (S.piecewise b a) j c) * F (update (S.piecewise b a) j d)) :=
          Finset.expect_le_expect fun c _ => Finset.expect_le_expect fun d _ => hih c d
      _ = _ := expect_expect_prod_update_eq hj F

/-- The *cube expectation* of `f : (∀ i, X i) → Bool`: the average, over two independent uniform
inputs `a` and `b`, of the product of the signs `(-1) ^ f` at the `2 ^ k` corners
`S.piecewise b a` of the cube they span (taking `b i` for `i ∈ S` and `a i` otherwise). -/
noncomputable def cubeExpectation (f : (∀ i, X i) → Bool) : ℝ :=
  𝔼 a, 𝔼 b, ∏ S : Finset ι, signVal (f (S.piecewise b a))

/-- **The cube bound**, the BNS–Chung criterion [BabaiNisanSzegedy1992][Chung1990] in the proof of
Raz [Raz2000]: with at least one player, the
discrepancy of `f` under the uniform distribution satisfies `disc(f) ^ (2 ^ k) ≤ E(f)`, for `k` the
number of players and `E(f)` the cube expectation. With no players the only cylinder intersection
is the set of all inputs, and the bound fails for the constant `true`. -/
theorem discrepancy_uniformOfFintype_pow_le [Nonempty ι] [∀ i, Nonempty (X i)]
    (f : (∀ i, X i) → Bool) :
    discrepancy (PMF.uniformOfFintype (∀ i, X i)) f ^ (2 ^ Fintype.card ι) ≤
      cubeExpectation f := by
  obtain ⟨φ, hφ⟩ := exists_abs_sum_eq_discrepancy (PMF.uniformOfFintype (∀ i, X i)) f
  rw [← hφ, (Nat.even_pow' Fintype.card_ne_zero |>.mpr even_two).pow_abs]
  -- The signed sum over the cylinder intersection, as an average of `f`'s sign against the
  -- product of the players' indicators.
  have hsum : ∑ x with x ∈ cylinderIntersection φ,
        ((PMF.uniformOfFintype (∀ i, X i)) x).toReal * signVal (f x) =
      𝔼 x, signVal (f x) * ∏ i, (if φ i (view i x) = true then (1 : ℝ) else 0) := by
    rw [Fintype.expect_eq_sum_div_card, sum_div, sum_filter]
    refine sum_congr rfl fun x _ => ?_
    simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    by_cases hx : x ∈ cylinderIntersection φ
    · rw [ite_eq_left hx, prod_eq_one fun i _ => ite_eq_left (mem_cylinderIntersection.mp hx i)]
      ring
    · rw [ite_eq_right hx]
      obtain ⟨i, hi⟩ := not_forall.mp (mem_cylinderIntersection.not.mp hx)
      rw [prod_eq_zero (mem_univ i) (ite_eq_right hi)]
      ring
  rw [hsum]
  have h := pow_expect_mul_prod_le univ (fun x => signVal (f x))
    (fun i x => if φ i (view i x) = true then (1 : ℝ) else 0)
    (fun i _ x e => by rw [view_update_self]) (fun i _ x => by split_ifs <;> simp)
  rw [card_univ, powerset_univ] at h
  exact h

end Cube

end Cslib.Communication.NOF
