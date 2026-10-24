/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.ShallowSymmetric.ShiftTest
public import Complexity.Foundations.Combinatorics.FiniteCover
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Small covers by shifted distinctness tests

Explicit finite bounds for the covering argument of
[Lecomte and Ramakrishnan, Sections 3 and 4][LecomteRamakrishnan2026]. A test accepting at least a
`1/q` fraction of the seeds at every valid input has a cover of size `q * (n + 1)` when there are at
most `2^n` valid inputs, by the union bound (`Cslib.exists_cover_of_density`). We sample all
shift vectors and reject those with the wrong sum, rather than sampling only sum-compatible vectors
as in the paper. The resulting density `k! / k^k` still gives the required exponential bound, using
`k^k ≤ 3^k * k!`.

## Main results

* `Cslib.Circuits.Boolean.ShallowSymmetric.exists_shiftTest_cover`,
  `Cslib.Circuits.Boolean.ShallowSymmetric.exists_simultaneous_shiftTest_cover`: small covers by
  shifted tests.

## References

* [V. Lecomte, P. Ramakrishnan, *Optimal Shallow Circuits for Majority*][LecomteRamakrishnan2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.ShallowSymmetric

/-- A convenient elementary form of the factorial estimate; no asymptotics. -/
private theorem pow_self_le_three_pow_mul_factorial (k : ℕ) :
    k ^ k ≤ 3 ^ k * k.factorial := by
  have h := Real.pow_div_factorial_le_exp (x := (k : ℝ)) (by positivity) k
  have he : Real.exp (k : ℝ) ≤ (3 : ℝ) ^ k := by
    calc
      Real.exp (k : ℝ) = Real.exp 1 ^ k := by
        rw [← Real.exp_nat_mul, mul_one]
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hn := (div_le_iff₀ hf).mp (h.trans he)
  exact_mod_cast hn

/-- The shifted tests cover any `2^n` valid weight vectors using at most
`3^|G| * (n+1)` tests. -/
theorem exists_shiftTest_cover {G W : Type*} [Fintype G] [AddCommGroup G]
    [Fintype W] (t : G) (w : W → G → G) (n : ℕ)
    (hcard : Fintype.card W ≤ 2 ^ n) (hw : ∀ x, ∑ i, w x i = t) :
    ∃ tests : Fin (3 ^ Fintype.card G * (n + 1)) → (G → G),
      ∀ x, ∃ j, ShiftTest t (w x) (tests j) := by
  classical
  apply exists_cover_of_density (fun s x => ShiftTest t (w x) s) _ n (by positivity) hcard
  intro x
  rw [← Nat.card_eq_fintype_card (α := {s : G → G // ShiftTest t (w x) s}),
    card_acceptingShifts _ (hw x), Fintype.card_fun]
  exact pow_self_le_three_pow_mul_factorial _

/-- Independent residue tests can be covered simultaneously, with an exponent
equal to the sum of the group sizes. -/
theorem exists_simultaneous_shiftTest_cover {ι W : Type*} [Fintype ι] [Fintype W]
    {G : ι → Type*} [∀ i, Fintype (G i)] [∀ i, AddCommGroup (G i)]
    (t : (i : ι) → G i) (w : W → (i : ι) → G i → G i) (n : ℕ)
    (hcard : Fintype.card W ≤ 2 ^ n) (hw : ∀ x i, ∑ a, w x i a = t i) :
    ∃ tests : Fin (3 ^ (∑ i, Fintype.card (G i)) * (n + 1)) →
        ((i : ι) → G i → G i),
      ∀ x, ∃ j, ∀ i, ShiftTest (t i) (w x i) (tests j i) := by
  classical
  apply exists_cover_of_density (fun (s : (i : ι) → G i → G i) x =>
    ∀ i, ShiftTest (t i) (w x i) (s i)) _ n
    (by positivity) hcard
  intro x
  have hc : Fintype.card {s : (i : ι) → G i → G i //
      ∀ i, ShiftTest (t i) (w x i) (s i)} =
      ∏ i, (Fintype.card (G i)).factorial := by
    rw [Fintype.card_congr (Equiv.subtypePiEquivPi
      (p := fun i s => ShiftTest (t i) (w x i) s)), Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Nat.card_eq_fintype_card, card_acceptingShifts _ (hw x i)]
  rw [hc, Fintype.card_pi, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  intro i _
  simpa using pow_self_le_three_pow_mul_factorial (Fintype.card (G i))

end Cslib.Circuits.Boolean.ShallowSymmetric
