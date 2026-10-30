/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.Product
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Independent draws from a distribution

`Cslib.Probability.PMF.iid μ k` draws `k` independent samples from `μ`, one coordinate at a time.
A tuple has the product of the masses of its coordinates (`iid_apply`), as for the product
`Cslib.Probability.PMF.pi`, but unlike `pi` it needs no finiteness of the sample space, so it
applies to distributions on infinite types such as the public-coin protocols of communication
complexity. Applying a function to each sample gives independent samples of the image
(`iid_map`), and on finite types the draws form the product distribution (`iid_eq_pi`).

The *majority tail bound* (`iid_card_ge_le`): among `2 r` independent bits, each `true` with
probability `q ≤ ε ≤ 1 / 2`, at least `r` are `true` with probability at most
`(4 ε (1 - ε)) ^ r`. Each outcome with `t ≥ r` true bits has probability
`q ^ t (1 - q) ^ (2 r - t) ≤ (q (1 - q)) ^ r`, and there are at most `4 ^ r` outcomes. The counting
form `Cslib.card_filter_card_filter_le_le` (majority votes over a uniform sample space) and the
Chernoff bounds `Cslib.Probability.PMF.pi_sum_ge_le_exp` (for finite products) give related tail
bounds.

## Main definitions

* `Cslib.Probability.PMF.iid`: independent draws from a distribution.

## Main results

* `Cslib.Probability.PMF.iid_apply`, `Cslib.Probability.PMF.mem_support_iid_iff`: masses and
  support.
* `Cslib.Probability.PMF.iid_map`, `Cslib.Probability.PMF.iid_eq_pi`: images and finite products.
* `Cslib.Probability.PMF.iid_card_ge_le`: the majority tail bound.

## References

* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
-/

@[expose] public section

namespace Cslib.Probability.PMF

variable {α β : Type*}

/-- `k` independent draws from `μ`, as a tuple: draw the first coordinate, then the others. -/
noncomputable def iid (μ : PMF α) : (k : ℕ) → PMF (Fin k → α)
  | 0 => PMF.pure Fin.elim0
  | k + 1 => do
      let a ← μ
      (iid μ k).map (Fin.cons a)

/-- A tuple of independent draws has the product of the masses of its coordinates. -/
@[simp] theorem iid_apply (μ : PMF α) : ∀ {k : ℕ} (v : Fin k → α), iid μ k v = ∏ i, μ (v i)
  | 0, v => by
    rw [iid, Fin.prod_univ_zero, Subsingleton.elim v Fin.elim0, PMF.pure_apply_self]
  | k + 1, v => by
    rw [iid, monad_bind_eq_bind, PMF.bind_apply, Fin.prod_univ_succ, tsum_eq_single (v 0)]
    · rw [PMF.map_apply, tsum_eq_single (Fin.tail v), iid_apply μ (Fin.tail v)]
      · simp [Fin.cons_self_tail, Fin.tail]
      · intro w hw
        simp only [ite_eq_right_iff]
        intro h
        exact absurd (by rw [h, Fin.tail_cons]) hw
    · intro a ha
      rw [PMF.map_apply, tsum_eq_zero_iff.mpr, mul_zero]
      intro w
      simp only [ite_eq_right_iff]
      intro h
      exact absurd (by rw [h, Fin.cons_zero]) ha

/-- A tuple can be drawn exactly when each of its coordinates can. -/
theorem mem_support_iid_iff (μ : PMF α) {k : ℕ} (v : Fin k → α) :
    v ∈ (iid μ k).support ↔ ∀ i, v i ∈ μ.support := by
  simp only [PMF.mem_support_iff, iid_apply, Finset.prod_ne_zero_iff, Finset.mem_univ,
    forall_const]

/-- Applying a function to each coordinate of independent draws gives independent draws of the
image. -/
theorem iid_map (μ : PMF α) (g : α → β) (k : ℕ) :
    iid (μ.map g) k = (iid μ k).map (fun v i => g (v i)) := by
  induction k with
  | zero =>
    rw [iid, iid, PMF.pure_map]
    congr 1
    funext i
    exact i.elim0
  | succ k ih =>
    rw [iid, iid]
    simp only [monad_bind_eq_bind, PMF.map_bind, PMF.bind_map, ih]
    congr 1
    funext a
    rw [Function.comp_apply, PMF.map_comp, PMF.map_comp]
    congr 1
    funext v i
    induction i using Fin.cases <;> rfl

/-- On a finite type, independent draws form the product distribution `pi`. -/
theorem iid_eq_pi [Finite α] (μ : PMF α) (k : ℕ) : iid μ k = pi (fun _ : Fin k => μ) := by
  ext v
  rw [iid_apply, pi_apply]

/-- If `0 ≤ a ≤ b`, `r ≤ t` and `t + u = 2 r`, then `a ^ t b ^ u ≤ (a b) ^ r`. -/
private theorem pow_mul_pow_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {r t u : ℕ} (ht : r ≤ t)
    (htu : t + u = 2 * r) : a ^ t * b ^ u ≤ (a * b) ^ r := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
  obtain rfl : r = u + d := by omega
  have hb : 0 ≤ b := ha.trans hab
  calc a ^ (u + d + d) * b ^ u = a ^ u * a ^ d * b ^ u * a ^ d := by ring
    _ ≤ a ^ u * a ^ d * b ^ u * b ^ d :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab d)
          (mul_nonneg (mul_nonneg (pow_nonneg ha _) (pow_nonneg ha _)) (pow_nonneg hb _))
    _ = (a * b) ^ (u + d) := by ring

/-- **The majority tail bound**: among `2 r` independent bits that are each `true` with
probability at most `ε ≤ 1 / 2`, at least `r` are `true` with probability at most
`(4 ε (1 - ε)) ^ r`. -/
theorem iid_card_ge_le {q : PMF Bool} {ε : ℝ}
    (hq : (q true).toReal ≤ ε) (hε : ε ≤ 1 / 2) (r : ℕ) :
    ((iid q (2 * r)).toOuterMeasure {v | r ≤ (Finset.univ.filter fun i => v i = true).card}).toReal
      ≤ (4 * ε * (1 - ε)) ^ r := by
  classical
  set a := (q true).toReal
  set b := (q false).toReal
  have hab : a + b = 1 := toReal_true_add_toReal_false q
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hab' : a ≤ b := by linarith
  -- Each outcome with at least `r` true bits has probability at most `(a b) ^ r`.
  have hterm (v : Fin (2 * r) → Bool) (hv : r ≤ (Finset.univ.filter fun i => v i = true).card) :
      ∏ i, (q (v i)).toReal ≤ (a * b) ^ r := by
    have hprod : ∏ i, (q (v i)).toReal = ∏ i, (if v i = true then a else b) :=
      Finset.prod_congr rfl fun i _ => by cases v i <;> rfl
    have hcard := Finset.card_filter_add_card_filter_not (s := Finset.univ) fun i => v i = true
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    rw [hprod, Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    exact pow_mul_pow_le ha hab' hv hcard
  rw [toOuterMeasure_apply_toReal]
  calc _ ≤ ∑ _v : Fin (2 * r) → Bool, (a * b) ^ r := by
        refine Finset.sum_le_sum fun v _ => ?_
        split_ifs with hv
        · rw [iid_apply, ENNReal.toReal_prod]
          exact hterm v hv
        · positivity
    _ = (4 * (a * b)) ^ r := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, nsmul_eq_mul, mul_pow, pow_mul]
        norm_num [mul_pow]
    _ ≤ (4 * ε * (1 - ε)) ^ r := by
        refine pow_le_pow_left₀ (by positivity) ?_ r
        have hb : b = 1 - a := by linarith
        rw [hb]
        nlinarith

end Cslib.Probability.PMF
