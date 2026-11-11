/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ShallowSymmetric.Construction
public import CslibFrontier.Foundations.Data.BitString.Threshold
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import CslibFrontier.Computability.Circuit.Boolean.ShallowSymmetric.Bounds
import CslibFrontier.Computability.Circuit.Boolean.ShallowSymmetric.Moduli
import CslibFrontier.Foundations.Data.Nat.Power
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-!
# Shallow circuits for symmetric functions

**The theorem of Lecomte and Ramakrishnan**
[Lecomte and Ramakrishnan, Theorems 1 and 2][LecomteRamakrishnan2026]: for every depth `d ≥ 2` there
is a constant `C` such that every symmetric Boolean function of `n` bits (one depending only on the
number of true bits, `BooleanFunction.IsSymmetric`), majority among them, has alternating formulas
of depth `d` with at most `2 ^ (C n ^ (1 / (d - 1)))` AND and OR gates
(`AltFormula.exists_of_isSymmetric`), so circuits over the unbounded fan-in basis of AND/OR depth
`d` with at most `n` more gates (`Unbounded.exists_circuit_of_isSymmetric`). For depth three this is
`2 ^ (C √n)`. The exponent is optimal for majority, by Korten's top-down bounds for alternating
formulas (`AltFormula.two_rpow_lt_size_of_eval_eq_majority`) and for circuits of AND/OR depth `d`
(`Unbounded.two_rpow_lt_add_size_of_computes_majority`).

The proof is by induction on the depth: at depth `d + 2`, symmetric functions of at most
`k ^ (d + 1)` bits have alternating formulas with `2 ^ (C_d k)` gates
(`exists_symmetric_altFormula`), and depth two is a normal form. For the step to depth `d + 3` and
`n ≤ k ^ (d + 2)` bits, a symmetric function is an OR over the accepted weights `t` of the
exact-weight tests `#x = t`. Choose `d + 2` pairwise coprime moduli `mᵢ` between `k` and `C k`
with product above `n` (`exists_moduli`), and split the inputs into the `mᵢ` residue classes modulo
each `mᵢ`. The weight is `t` exactly when, modulo each `mᵢ`, the class weights sum to `t`; that
holds exactly when some shifts `s`, summing to `∑ a - t`, make the shifted class weights pairwise
distinct (`ShiftTest`), and a random shift works with probability at least `3 ^ (-mᵢ)`, so
`3 ^ ∑ mᵢ (n + 1)` shifts cover every input of weight `t` (`exists_simultaneous_shiftTest_cover`).
Each shifted comparison of two class weights is a symmetric function of their bits after negating
one class, on `2 (n / mᵢ + 1) ≤ (4 k) ^ (d + 1)` bits, so it has `2 ^ (C_d · 4 k)` gates at depth
`d + 2` by induction (`exists_pairComparison`), and the comparisons of one test merge into one
gate layer.

## Main results

* `Cslib.Circuits.Boolean.AltFormula.exists_of_isSymmetric_nat`,
  `Cslib.Circuits.Boolean.AltFormula.exists_of_isSymmetric`: the theorem of Lecomte and
  Ramakrishnan, for alternating formulas.
* `Cslib.Circuits.Boolean.Unbounded.exists_circuit_of_isSymmetric`: the same for circuits over the
  unbounded fan-in basis.
* `Cslib.Circuits.Boolean.AltFormula.exists_of_isSymmetric_depth_three`,
  `Cslib.Circuits.Boolean.AltFormula.exists_majority`: depth three, and majority.

## References

* [V. Lecomte, P. Ramakrishnan, *Optimal Shallow Circuits for Majority*][LecomteRamakrishnan2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Finset ShallowSymmetric BitString BooleanFunction

variable {n : ℕ}

namespace ShallowSymmetric

/-- **The depth induction**: at depth `d + 2`, every symmetric function of at most `k ^ (d + 1)`
bits has alternating formulas with either root operation of size at most `2 ^ (C k)`. -/
theorem exists_symmetric_altFormula (d : ℕ) :
    ∃ C : ℕ, ∀ n k : ℕ, 1 ≤ k → n ≤ k ^ (d + 1) →
      ∀ (a : ℕ → Bool) (op : AltOp),
        ∃ f : AltFormula n (d + 2), AltFormula.size f ≤ 2 ^ (C * k) ∧
          ∀ x, AltFormula.eval op f x = a (weight x) := by
  induction d with
  | zero =>
    refine ⟨2, fun n k hk hn a op => ?_⟩
    obtain ⟨f, hs, he⟩ := AltFormula.exists_depth_two (fun x => a (weight x)) op
    refine ⟨f, hs.trans ?_, he⟩
    have h : 2 ^ n ≤ 2 ^ (1 * k) := Nat.pow_le_pow_right (by omega) (by simpa using hn)
    simpa using Nat.add_le_two_pow_add_add_one_mul hk h (show 1 ≤ 2 ^ (0 * k) by simp)
  | succ d ih =>
    obtain ⟨A, hA⟩ := ih
    obtain ⟨C, hC, hmod⟩ := exists_moduli (d + 2)
    refine ⟨2 * ((d + 2) * C) + 2 * (d + 2) + ((d + 2) + 2 * C + 2) + 4 * A + 8,
      fun n k hk hn a op => ?_⟩
    obtain ⟨m, hcop, hgt, hle⟩ := hmod k hk
    let (i : Fin (d + 2)) : NeZero (m i) := ⟨by have := hgt i; omega⟩
    have hnprod : n < ∏ i, m i := hn.trans_lt (pow_lt_prod_moduli (by omega) m hgt)
    have hsmall (l : ℕ) (hl : l ≤ (4 * k) ^ (d + 1)) (b : ℕ → Bool) :
        ∃ f : AltFormula l (d + 2), AltFormula.size f ≤ 2 ^ ((4 * A) * k) ∧
          ∀ x, AltFormula.eval .and f x = b (weight x) := by
      simpa only [show A * (4 * k) = (4 * A) * k by ring] using hA l (4 * k) (by omega) hl b .and
    obtain ⟨f, hs, he⟩ := exists_symmetric_altFormula_succ m hcop hnprod hsmall
      (fun i => pair_size_bound hk hn (hgt i).le) a op
    refine ⟨f, hs.trans ?_, he⟩
    apply construction_size_bound hk
    · calc n ≤ k ^ (d + 2) := hn
        _ ≤ (2 ^ k) ^ (d + 2) := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
        _ = _ := by rw [← pow_mul, Nat.mul_comm]
    · calc ∑ i, m i ≤ ∑ _i : Fin (d + 2), C * k := sum_le_sum fun i _ => hle i
        _ = _ := by simp [Nat.mul_assoc]
    · exact sum_sq_moduli_bound hk m hle
    · exact le_rfl

private theorem nthRoot_le_rpow (r n : ℕ) (hr : r ≠ 0) :
    (Nat.nthRoot r n : ℝ) ≤ (n : ℝ) ^ ((r : ℝ)⁻¹) := by
  have h : (Nat.nthRoot r n : ℝ) ^ r ≤ (n : ℝ) := by
    exact_mod_cast Nat.pow_nthRoot_le (n := r) (a := n) (Or.inl hr)
  have h' := Real.rpow_le_rpow (by positivity) h (show 0 ≤ (r : ℝ)⁻¹ by positivity)
  rwa [Real.pow_rpow_inv_natCast (by positivity) hr] at h'

end ShallowSymmetric

namespace AltFormula

/-- **The theorem of Lecomte and Ramakrishnan**
[Lecomte and Ramakrishnan, Theorem 1][LecomteRamakrishnan2026], with an integer root: for every
depth `d ≥ 2` there is a constant `C` such that every symmetric function of `n` bits has alternating
formulas of depth `d`, with either root operation, with at most `2 ^ (C (⌊n ^ (1 / (d - 1))⌋ + 1))`
AND and OR gates. -/
theorem exists_of_isSymmetric_nat {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℕ, ∀ (n : ℕ) (f : BitString n → Bool), IsSymmetric f → ∀ op : AltOp,
      ∃ g : AltFormula n d, size g ≤ 2 ^ (C * (Nat.nthRoot (d - 1) n + 1)) ∧
        ∀ x, eval op g x = f x := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  obtain ⟨C, hC⟩ := exists_symmetric_altFormula e
  refine ⟨C, fun n f hf op => ?_⟩
  obtain ⟨a, ha⟩ := hf.exists_eq_comp_weight
  obtain ⟨g, hs, he⟩ := hC n (Nat.nthRoot (e + 1) n + 1) (by omega)
    (Nat.lt_pow_nthRoot_add_one (by omega) n).le a op
  exact ⟨g, by simpa only [show e + 2 - 1 = e + 1 by omega] using hs, fun x => (he x).trans (ha x)⟩

/-- **The theorem of Lecomte and Ramakrishnan**
[Lecomte and Ramakrishnan, Theorem 1][LecomteRamakrishnan2026]: for every depth `d ≥ 2` there is a
constant `C` such that every symmetric function of `n ≥ 1` bits has alternating formulas of depth
`d`, with either root operation, with at most `2 ^ (C n ^ (1 / (d - 1)))` AND and OR gates. -/
theorem exists_of_isSymmetric {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ f : BitString n → Bool, IsSymmetric f → ∀ op : AltOp,
      ∃ g : AltFormula n d, (size g : ℝ) ≤ 2 ^ (C * (n : ℝ) ^ ((d - 1 : ℕ) : ℝ)⁻¹) ∧
        ∀ x, eval op g x = f x := by
  obtain ⟨C, hC⟩ := exists_of_isSymmetric_nat hd
  refine ⟨2 * C + 1, by positivity, fun n hn f hf op => ?_⟩
  obtain ⟨g, hs, he⟩ := hC n f hf op
  refine ⟨g, ?_, he⟩
  have hroot := nthRoot_le_rpow (d - 1) n (by omega)
  have hone : 1 ≤ (n : ℝ) ^ ((d - 1 : ℕ) : ℝ)⁻¹ :=
    Real.one_le_rpow (by exact_mod_cast hn) (by positivity)
  calc (size g : ℝ) ≤ (2 : ℝ) ^ (C * (Nat.nthRoot (d - 1) n + 1)) := by exact_mod_cast hs
    _ = (2 : ℝ) ^ ((C : ℝ) * ((Nat.nthRoot (d - 1) n : ℝ) + 1)) := by
        rw [← Real.rpow_natCast]
        push_cast
        rfl
    _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        nlinarith [show (0 : ℝ) ≤ (C : ℝ) from Nat.cast_nonneg C]

/-- **Depth three** [Lecomte and Ramakrishnan, Theorem 2][LecomteRamakrishnan2026]: symmetric
functions of `n ≥ 1` bits have alternating formulas of depth three with at most `2 ^ (C √n)` gates.
-/
theorem exists_of_isSymmetric_depth_three :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ f : BitString n → Bool, IsSymmetric f → ∀ op : AltOp,
      ∃ g : AltFormula n 3, (size g : ℝ) ≤ 2 ^ (C * √(n : ℝ)) ∧ ∀ x, eval op g x = f x := by
  simpa [Real.sqrt_eq_rpow] using exists_of_isSymmetric (d := 3) (by omega)

/-- Majority of `n ≥ 1` bits has alternating formulas of depth `d ≥ 2` with at most
`2 ^ (C n ^ (1 / (d - 1)))` gates. -/
theorem exists_majority {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ op : AltOp,
      ∃ g : AltFormula n d, (size g : ℝ) ≤ 2 ^ (C * (n : ℝ) ^ ((d - 1 : ℕ) : ℝ)⁻¹) ∧
        ∀ x, eval op g x = majority n x := by
  obtain ⟨C, hC, h⟩ := exists_of_isSymmetric hd
  exact ⟨C, hC, fun n hn => h n hn _ isSymmetric_majority⟩

end AltFormula

/-- **The theorem of Lecomte and Ramakrishnan, for circuits** [LecomteRamakrishnan2026]: for every
`d ≥ 2` there is a constant `C` such that every symmetric function of `n ≥ 1` bits has circuits over
the unbounded fan-in basis of AND/OR depth at most `d`, and of depth at most `d + 1` counting
negations, with at most `2 ^ (C n ^ (1 / (d - 1))) + n` gates. -/
theorem Unbounded.exists_circuit_of_isSymmetric {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ f : BitString n → Bool, IsSymmetric f →
      ∃ c : Circuit Unbounded.signature n 1, c.Computes Unbounded.interpretation (single f) ∧
        c.depthWith Unbounded.andOrCost ≤ d ∧ c.depth ≤ d + 1 ∧
          (c.size : ℝ) ≤ 2 ^ (C * (n : ℝ) ^ ((d - 1 : ℕ) : ℝ)⁻¹) + n := by
  obtain ⟨C, hC, h⟩ := AltFormula.exists_of_isSymmetric hd
  refine ⟨C, hC, fun n hn f hf => ?_⟩
  obtain ⟨g, hs, he⟩ := h n hn f hf .or
  obtain ⟨c, hc, hdepthWith, hdepth, hsize⟩ := AltFormula.exists_circuit .or g
  refine ⟨c, ?_, hdepthWith, hdepth, ?_⟩
  · rwa [show AltFormula.eval .or g = f from funext he] at hc
  · rw [hsize]
    push_cast
    linarith

end Cslib.Circuits.Boolean
