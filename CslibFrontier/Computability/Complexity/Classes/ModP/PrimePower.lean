/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ModP
public import Mathlib.Algebra.IsPrimePow
import CslibFrontier.Computability.Complexity.Classes.SharpP.Choose
import CslibFrontier.Foundations.Data.Nat.Choose.PrimePowerDvd
import Mathlib.Data.Nat.Prime.Pow

/-!
# Prime-power moduli collapse to their prime

For a prime `p` and `e ≥ 1`, `ModP (p ^ e) = ModP p` [Beigel and Gill, Theorem 30][BeigelGill1992]
(`Cslib.Complexity.ModP_prime_pow`). So prime-power moduli inherit the prime-modulus closure
under complement, intersection and union, and `coModP (p ^ e) = ModP (p ^ e)`.

The inclusion `ModP p ⊆ ModP (p ^ e)` is the divisor case
[Beigel and Gill, Proposition 29][BeigelGill1992] (`Cslib.Complexity.ModP_subset_ModP_of_dvd`):
for `k = j h ≠ 0`, `f a % j ≠ 0` exactly when `(h f a) % k ≠ 0`. For the reverse inclusion,
`p ^ e` divides `f a` exactly when `p` divides `C(f a, p ^ i)` for every `i < e`
(`Nat.pow_dvd_iff_forall_dvd_choose`, from Lucas's theorem; this is the digit criterion of
[Beigel and Gill, Corollary 20][BeigelGill1992]). Each `C(f a, p ^ i)` is a #P
count (`Cslib.Complexity.SharpP.choose_mem`), so a language in `ModP (p ^ e)` is a union of `e`
languages in `ModP p`, and prime-modulus union closure (`Cslib.Complexity.union_mem_ModP`)
finishes. Beigel and Gill induct on `e` and split off one digit at a time; here all `e` digit
languages are taken at once.

## Main results

* `Cslib.Complexity.ModP_subset_ModP_of_dvd`: `j ∣ k ≠ 0` gives `ModP j ⊆ ModP k`.
* `Cslib.Complexity.ModP_prime_pow`: `ModP (p ^ e) = ModP p` for prime `p` and `e ≠ 0`.
* `Cslib.Complexity.ModP_eq_ModP_minFac`, `Cslib.Complexity.ModP_two_pow`: the same collapse for
  `IsPrimePow k`, and `ModP (2 ^ e) = ParityP`.
* `Cslib.Complexity.ModP.booleanSubalgebraOfIsPrimePow`,
  `Cslib.Complexity.compl_mem_ModP_of_isPrimePow`, `Cslib.Complexity.inter_mem_ModP_of_isPrimePow`,
  `Cslib.Complexity.union_mem_ModP_of_isPrimePow`, `Cslib.Complexity.coModP_eq_ModP_of_isPrimePow`:
  prime-power closure.

## References

* [R. Beigel, J. Gill, *Counting classes: thresholds, parity, mods, and fewness*][BeigelGill1992]
-/

public section

namespace Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool} {A B : Set α} {k : ℕ}

/-- A divisor's modular class is contained in the multiple's, for a nonzero multiple
[Beigel and Gill, Proposition 29][BeigelGill1992]: multiply the count by `k / j`. The proof uses
`k ≠ 0`; at `k = 0` the statement would place every `ModP j` inside `ModP 0 = NP`. -/
theorem ModP_subset_ModP_of_dvd {j : ℕ} (hjk : j ∣ k) (hk : k ≠ 0) :
    ModP j enc ⊆ ModP k enc := by
  obtain ⟨h, rfl⟩ := hjk
  have hh : h ≠ 0 := right_ne_zero_of_mul hk
  rintro A ⟨f, hf, hA⟩
  refine ⟨f * (h : α → ℕ), SharpP.mul_mem hf (SharpP.natCast_mem h), fun a => ?_⟩
  rw [hA a, Pi.mul_apply, Pi.natCast_apply, Nat.cast_id, Nat.mul_mod_mul_right]
  simp [hh]

/-- **Prime-power moduli collapse to their prime** [Beigel and Gill, Theorem 30][BeigelGill1992]:
`ModP (p ^ e) = ModP p` for prime `p` and `e ≥ 1`. A count is nonzero modulo `p ^ e` exactly when
one of the `#P` counts `C(f a, p ^ i)`, `i < e`, is nonzero modulo `p`. -/
theorem ModP_prime_pow {p : ℕ} (hp : p.Prime) {e : ℕ} (he : e ≠ 0) :
    ModP (p ^ e) enc = ModP p enc := by
  refine subset_antisymm (fun A hA => ?_)
    (ModP_subset_ModP_of_dvd (dvd_pow_self p he) (pow_ne_zero e hp.ne_zero))
  obtain ⟨f, hf, hA⟩ := hA
  -- the union of the first `n` digit languages
  have hunion (n : ℕ) : {a | ∃ i < n, (f a).choose (p ^ i) % p ≠ 0} ∈ ModP p enc := by
    induction n with
    | zero => simpa using P_subset_ModP hp.two_le empty_mem_P
    | succ n ih =>
      have hn : {a | (f a).choose (p ^ n) % p ≠ 0} ∈ ModP p enc :=
        ⟨_, SharpP.choose_mem hf (.const (p ^ n)), fun _ => Iff.rfl⟩
      convert union_mem_ModP hp ih hn using 1
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_union, Nat.exists_lt_succ_right]
  convert hunion e using 1
  ext a
  rw [hA a, Set.mem_ofPred_eq, ne_eq, ← Nat.dvd_iff_mod_eq_zero,
    Nat.pow_dvd_iff_forall_dvd_choose hp]
  simp only [Nat.dvd_iff_mod_eq_zero, not_forall, exists_prop]

/-- For a prime power `k`, `ModP k` is the class of its prime `k.minFac`. -/
theorem ModP_eq_ModP_minFac (hk : IsPrimePow k) : ModP k enc = ModP k.minFac enc := by
  obtain ⟨p, e, hp, he, rfl⟩ := (isPrimePow_nat_iff k).mp hk
  rw [Nat.pow_minFac he.ne', hp.minFac_eq, ModP_prime_pow hp he.ne']

/-- Every power-of-two modulus defines parity: `ModP (2 ^ e) = ParityP` for `e ≥ 1`. -/
theorem ModP_two_pow {e : ℕ} (he : e ≠ 0) : ModP (2 ^ e) enc = ParityP enc :=
  (ModP_prime_pow Nat.prime_two he).trans ModP_two

/-- For a prime power `k`, `ModP k` as a Boolean subalgebra of `Set α`, with carrier
`ModP k enc` (the Boolean subalgebra of the prime `k.minFac`). -/
@[expose]
def ModP.booleanSubalgebraOfIsPrimePow (hk : IsPrimePow k) (enc : α ↪ List Bool) :
    BooleanSubalgebra (Set α) :=
  (ModP.booleanSubalgebra (Nat.minFac_prime hk.ne_one) enc).copy (ModP k enc)
    (ModP_eq_ModP_minFac hk)

@[simp]
theorem ModP.coe_booleanSubalgebraOfIsPrimePow (hk : IsPrimePow k) :
    (ModP.booleanSubalgebraOfIsPrimePow hk enc : Set (Set α)) = ModP k enc := rfl

@[simp]
theorem ModP.mem_booleanSubalgebraOfIsPrimePow (hk : IsPrimePow k) :
    A ∈ ModP.booleanSubalgebraOfIsPrimePow hk enc ↔ A ∈ ModP k enc := Iff.rfl

/-- Prime-power-modulus complement closure. -/
theorem compl_mem_ModP_of_isPrimePow (hk : IsPrimePow k) (hA : A ∈ ModP k enc) :
    Aᶜ ∈ ModP k enc :=
  (ModP.booleanSubalgebraOfIsPrimePow hk enc).compl_mem hA

/-- Prime-power-modulus intersection closure. -/
theorem inter_mem_ModP_of_isPrimePow (hk : IsPrimePow k) (hA : A ∈ ModP k enc)
    (hB : B ∈ ModP k enc) : A ∩ B ∈ ModP k enc :=
  (ModP.booleanSubalgebraOfIsPrimePow hk enc).inf_mem hA hB

/-- Prime-power-modulus union closure. -/
theorem union_mem_ModP_of_isPrimePow (hk : IsPrimePow k) (hA : A ∈ ModP k enc)
    (hB : B ∈ ModP k enc) : A ∪ B ∈ ModP k enc :=
  (ModP.booleanSubalgebraOfIsPrimePow hk enc).sup_mem hA hB

/-- For prime-power moduli, complement closure identifies the two modular classes. -/
theorem coModP_eq_ModP_of_isPrimePow (hk : IsPrimePow k) : coModP k enc = ModP k enc := by
  ext A
  constructor
  · intro h
    simpa using compl_mem_ModP_of_isPrimePow hk h
  · exact compl_mem_ModP_of_isPrimePow hk

end Cslib.Complexity
