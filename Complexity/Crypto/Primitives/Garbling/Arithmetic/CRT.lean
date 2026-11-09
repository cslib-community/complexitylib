/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Crypto.Primitives.Garbling.Arithmetic.ConstantDivision
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# CRT reconstruction inside a prime-power ring

Li and Liu [LiLiu2024] garble arithmetic over `ℤ/N` for `N = ∏ i, m i` with pairwise coprime
moduli `m i` (typically prime powers) channel by channel, through the Chinese remainder theorem.
Their bit decomposition for `ℤ/N` merges the channels with CRT constants in a linear
bit-composition gate, followed by an exact remainder by `N`. With the standard CRT coefficients
`c i = M i * (M i⁻¹ mod m i)`, `M i = N / m i`, the residues `x % m i` determine `x mod N` as the
public linear combination `∑ i, c i * (x % m i)` reduced modulo `N` (`crtSum_modEq`).

The combination is computed in a larger ring `ℤ/p^(2k+1)` with `N ^ 2 ≤ p ^ k`. It does not wrap
around there: each coefficient is below `N` (`crtCoeff_lt`) and the residues add up to at most
`N - 1` (`sum_sub_one_le_prod_sub_one`), so the combination is at most `(N - 1) ^ 2`
(`crtSum_le_sq`). The exact remainder gadget of `ConstantDivision` then recovers `x mod N` in the
ring (`constMod_crtSum`).

## Main definitions

* `Cslib.Crypto.Garbling.Arithmetic.crtCoeff`: the CRT coefficient of a channel.
* `Cslib.Crypto.Garbling.Arithmetic.crtSum`: the linear combination of the channel residues.

## Main results

* `Cslib.Crypto.Garbling.Arithmetic.crtSum_modEq`: the combination is `x` modulo `N`.
* `Cslib.Crypto.Garbling.Arithmetic.crtSum_le_sq`: the combination is at most `(N - 1) ^ 2`.
* `Cslib.Crypto.Garbling.Arithmetic.constMod_crtSum`: reconstruction of `x mod N` in
  `ℤ/p^(2k+1)` from the channel residues of `x`.

## References

* [H. Li, T. Liu, *How to Garble Mixed Circuits that Combine Boolean and Arithmetic
  Computations*][LiLiu2024]
-/

public section

namespace Cslib.Crypto.Garbling.Arithmetic

open Function

variable {s : ℕ} (m : Fin s → ℕ)

/-- The CRT coefficient of channel `i`: `M * (M⁻¹ mod m i)` for `M = (∏ j, m j) / m i`. -/
@[expose] def crtCoeff (i : Fin s) : ℕ :=
  (∏ j, m j) / m i * ((((∏ j, m j) / m i : ℕ) : ZMod (m i))⁻¹).val

/-- The CRT combination `∑ i, crtCoeff m i * (x % m i)` of the channel residues of `x`. -/
@[expose] def crtSum (x : ℕ) : ℕ := ∑ i, crtCoeff m i * (x % m i)

variable {m}

/-- The product of the other moduli. -/
private theorem prod_div_eq (hm : ∀ i, 0 < m i) (i : Fin s) :
    (∏ j, m j) / m i = ∏ j ∈ Finset.univ.erase i, m j :=
  Nat.div_eq_of_eq_mul_left (hm i) (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm

private theorem prod_div_mul (hm : ∀ i, 0 < m i) (i : Fin s) :
    (∏ j, m j) / m i * m i = ∏ j, m j := by
  rw [prod_div_eq hm]
  exact Finset.prod_erase_mul _ _ (Finset.mem_univ i)

/-- Each CRT coefficient is below `N = ∏ i, m i`. -/
theorem crtCoeff_lt (hm : ∀ i, 0 < m i) (i : Fin s) : crtCoeff m i < ∏ j, m j := by
  have : NeZero (m i) := ⟨(hm i).ne'⟩
  have hv := ZMod.val_lt ((((∏ j, m j) / m i : ℕ) : ZMod (m i))⁻¹)
  have hM : 0 < (∏ j, m j) / m i := by
    rw [prod_div_eq hm]
    exact Finset.prod_pos fun j _ => hm j
  calc crtCoeff m i < (∏ j, m j) / m i * m i := Nat.mul_lt_mul_of_pos_left hv hM
    _ = ∏ j, m j := prod_div_mul hm i

/-- In channel `j`, the coefficient of channel `i` is `1` if `i = j` and `0` otherwise. -/
theorem crtCoeff_cast (hm : ∀ i, 0 < m i) (hco : Pairwise (Nat.Coprime on m)) (i j : Fin s) :
    (crtCoeff m i : ZMod (m j)) = if i = j then 1 else 0 := by
  split_ifs with hij
  · subst hij
    have : NeZero (m i) := ⟨(hm i).ne'⟩
    have hcop : Nat.Coprime ((∏ j, m j) / m i) (m i) := by
      rw [prod_div_eq hm]
      exact Nat.Coprime.prod_left fun j hj => hco (Finset.ne_of_mem_erase hj)
    rw [crtCoeff, Nat.cast_mul, ZMod.natCast_zmod_val]
    exact ZMod.coe_mul_inv_eq_one _ hcop
  · rw [crtCoeff, Nat.cast_mul, (ZMod.natCast_eq_zero_iff _ _).mpr, zero_mul]
    rw [prod_div_eq hm]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)

/-- **CRT reconstruction**: the combination of the residues of `x` is `x` modulo `∏ i, m i`. -/
theorem crtSum_modEq (hm : ∀ i, 0 < m i) (hco : Pairwise (Nat.Coprime on m)) (x : ℕ) :
    crtSum m x ≡ x [MOD ∏ i, m i] := by
  have hchan (j : Fin s) : crtSum m x ≡ x [MOD m j] := by
    rw [← ZMod.natCast_eq_natCast_iff, crtSum]
    push_cast
    simp only [crtCoeff_cast hm hco, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, ZMod.natCast_mod]
  have hint : (∏ i, (m i : ℤ)) ∣ (x : ℤ) - crtSum m x :=
    Fintype.prod_dvd_of_coprime (fun i j hij => Nat.Coprime.isCoprime (hco hij))
      fun j => (Nat.modEq_iff_dvd.mp (hchan j))
  rw [Nat.modEq_iff_dvd]
  exact_mod_cast hint

/-- Residues are at most their moduli minus one, and these bounds add up to at most
`∏ i, m i - 1`. -/
theorem sum_sub_one_le_prod_sub_one (hm : ∀ i, 0 < m i) :
    ∑ i, (m i - 1) ≤ ∏ i, m i - 1 := by
  suffices h : ∀ t : Finset (Fin s), ∑ i ∈ t, (m i - 1) ≤ ∏ i ∈ t, m i - 1 from h _
  intro t
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hP : 0 < ∏ i ∈ t, m i := Finset.prod_pos fun j _ => hm j
    have ha' := hm a
    have key : m a + ∏ i ∈ t, m i ≤ m a * ∏ i ∈ t, m i + 1 := by nlinarith
    omega

/-- **No wrap-around**: the CRT combination of the residues of any `x` is at most
`(N - 1) ^ 2` for `N = ∏ i, m i`. -/
theorem crtSum_le_sq (hm : ∀ i, 0 < m i) (x : ℕ) : crtSum m x ≤ (∏ i, m i - 1) ^ 2 := by
  set N := ∏ i, m i
  calc crtSum m x ≤ ∑ i, (N - 1) * (m i - 1) := by
        refine Finset.sum_le_sum fun i _ => Nat.mul_le_mul ?_ ?_
        · have := crtCoeff_lt hm i
          omega
        · have := Nat.mod_lt x (hm i)
          omega
    _ = (N - 1) * ∑ i, (m i - 1) := (Finset.mul_sum _ _ _).symm
    _ ≤ (N - 1) * (N - 1) := Nat.mul_le_mul_left _ (sum_sub_one_le_prod_sub_one hm)
    _ = (N - 1) ^ 2 := (sq _).symm

/-- **Reconstruction in `ℤ/p^(2k+1)`**: if `(∏ i, m i) ^ 2 ≤ p ^ k`, the remainder gadget
`constMod` applied to the CRT combination of the residues of `x` returns `x mod ∏ i, m i`. -/
theorem constMod_crtSum (hm : ∀ i, 0 < m i) (hco : Pairwise (Nat.Coprime on m)) {p k : ℕ}
    (hp : 1 < p) (hN : (∏ i, m i) ^ 2 ≤ p ^ k) (x : ℕ) :
    constMod p k (∏ i, m i) (crtSum m x : ZMod (p ^ (2 * k + 1))) =
      ((x % ∏ i, m i : ℕ) : ZMod (p ^ (2 * k + 1))) := by
  have hN0 : 0 < ∏ i, m i := Finset.prod_pos fun j _ => hm j
  have : NeZero (p ^ (2 * k + 1)) := ⟨(pow_pos (by omega) _).ne'⟩
  have hlt : crtSum m x < p ^ k := by
    have h1 := crtSum_le_sq hm x
    have h2 : (∏ i, m i - 1) ^ 2 < (∏ i, m i) ^ 2 := Nat.pow_lt_pow_left (by omega) two_ne_zero
    omega
  have hk : p ^ k ≤ p ^ (2 * k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hval : (crtSum m x : ZMod (p ^ (2 * k + 1))).val = crtSum m x := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hlt.trans_le hk)]
  have hx : (crtSum m x : ZMod (p ^ (2 * k + 1))).val < p ^ k := by rw [hval]; exact hlt
  rw [constMod_eq_mod hp hN0 hx, hval]
  exact congrArg Nat.cast (crtSum_modEq hm hco x)

end Cslib.Crypto.Garbling.Arithmetic
