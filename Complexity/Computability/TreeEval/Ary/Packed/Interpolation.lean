/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Reader.Arith
public import Mathlib.LinearAlgebra.Lagrange
import Complexity.Foundations.FieldTheory.Finite.Basic

/-!
# Modular Lagrange basis evaluation

A Lagrange basis weight for the alphabet `0, …, s-1` is evaluated by a counter and a single
modular accumulator. Inverses use the existing Fermat power routine. This executable procedure
does not materialize a list of alphabet symbols or polynomial coefficients.

## Main definitions

* `Cslib.TreeEval.Ary.Packed.basisFactor`: one factor, omitting the diagonal symbol.
* `Cslib.TreeEval.Ary.Packed.basisStep`: one counter step.
* `Cslib.TreeEval.Ary.Packed.basisWeight`: the complete basis weight.

## Main results

* `Cslib.TreeEval.Ary.Packed.cast_basisWeight`: correctness over a prime field.
* `Cslib.TreeEval.Ary.Packed.basisWeight_lt`: the result remains a reduced residue.

## References

* [R. Williams, *Simulating Time With Square-Root Space*][Williams2025], Appendix A,
  equation (6). The executable prime-field realization is an original implementation of the
  finite-grid Lagrange factors used by that extension.
-/

@[expose] public section

namespace Cslib.TreeEval.Ary.Packed

open Reader

/-- One factor of a Lagrange basis weight, with the diagonal factor replaced by one.
`unitInv p (v-1)` inverts the nonzero residue `v` when `p` is prime. -/
def basisFactor (p a j x : ℕ) : ℕ :=
  if j = a then 1 % p else
    mulMod p (addMod p x (negMod p j))
      (unitInv p (addMod p a (negMod p j) - 1))

/-- The parameter `(p,a,x)`, counter and accumulator used by basis evaluation. The zero-modulus
branch makes every noninitial accumulator bounded even on malformed parameters. -/
def basisStep (s : (ℕ × ℕ × ℕ) × ℕ × ℕ) : (ℕ × ℕ × ℕ) × ℕ × ℕ :=
  (s.1, s.2.1 + 1,
    if s.1.1 = 0 then 0 else mulMod s.1.1 s.2.2
      (basisFactor s.1.1 s.1.2.1 s.2.1 s.1.2.2))

/-- Evaluate the basis weight by exactly `s` counter steps. -/
def basisWeight (p s a x : ℕ) : ℕ :=
  (basisStep^[s] ((p, a, x), 0, 1 % p)).2.2

/-- The counter enumerates the alphabet without storing its elements. -/
theorem iterate_basisStep_counter (p a x : ℕ) (n : ℕ) :
    (basisStep^[n] ((p, a, x), 0, 1 % p)).1 = (p, a, x) ∧
      (basisStep^[n] ((p, a, x), 0, 1 % p)).2.1 = n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    simp [basisStep, ih.1, ih.2]

/-- Every intermediate accumulator fits within the modulus plus one, including malformed
zero-modulus inputs and the initial accumulator. -/
theorem basisWeight_le (p n a x : ℕ) : basisWeight p n a x ≤ p + 1 := by
  cases n with
  | zero => exact (Nat.mod_le _ _).trans (by omega)
  | succ n =>
    rw [basisWeight, Function.iterate_succ_apply']
    have hp := (iterate_basisStep_counter p a x n).1
    simp only [basisStep, hp]
    split_ifs with hz
    · omega
    · exact (Nat.mod_lt _ (Nat.pos_of_ne_zero hz)).le.trans (by omega)

/-- A positive modulus keeps the initial and every subsequent accumulator reduced. -/
theorem basisWeight_lt {p : ℕ} (hp : 0 < p) (n a x : ℕ) : basisWeight p n a x < p := by
  cases n with
  | zero => exact Nat.mod_lt _ hp
  | succ n =>
    rw [basisWeight, Function.iterate_succ_apply']
    have hpar := (iterate_basisStep_counter p a x n).1
    simp only [basisStep, hpar, hp.ne', ↓reduceIte]
    exact Nat.mod_lt _ hp

variable {p : ℕ} [Fact p.Prime]

private theorem cast_unitInv_residue {v : ℕ} (hv : 0 < v) (hvp : v < p) :
    ((unitInv p (v - 1) : ℕ) : ZMod p) = (v : ZMod p)⁻¹ := by
  have hne : (v : ZMod p) ≠ 0 := by
    intro h
    have := congrArg ZMod.val h
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hvp, ZMod.val_zero] at this
    omega
  rw [unitInv, cast_powMod, Nat.sub_add_cancel hv]
  exact ZMod.pow_card_sub_two_eq_inv hne

/-- A scalar factor agrees with the corresponding field quotient on the alphabet. -/
theorem cast_basisFactor {a j : ℕ} (ha : a < p) (hj : j < p) (x : ℕ) :
    ((basisFactor p a j x : ℕ) : ZMod p) =
      if j = a then 1 else ((x : ZMod p) - j) * ((a : ZMod p) - j)⁻¹ := by
  by_cases hja : j = a
  · simp [basisFactor, hja]
  · have hne : (a : ZMod p) ≠ (j : ZMod p) := by
      intro heq
      have heq' := congrArg ZMod.val heq
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hj] at heq'
      exact hja heq'.symm
    have hdlt : addMod p a (negMod p j) < p := Nat.mod_lt _ (Fact.out : p.Prime).pos
    have hdpos : 0 < addMod p a (negMod p j) := by
      by_contra hn
      have hz : addMod p a (negMod p j) = 0 := by omega
      have hcast := congrArg (fun n : ℕ => (n : ZMod p)) hz
      simp only [cast_addMod, cast_negMod, Nat.cast_zero] at hcast
      exact hne (eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hcast))
    rw [basisFactor, ite_eq_right hja, cast_mulMod, cast_addMod, cast_negMod,
      cast_unitInv_residue hdpos hdlt, cast_addMod, cast_negMod, ite_eq_right hja]
    simp only [sub_eq_add_neg]

private theorem cast_basisWeight_prod {s a : ℕ} (ha : a < p) (hs : s ≤ p) (x : ℕ) :
    ((basisWeight p s a x : ℕ) : ZMod p) =
      ∏ j ∈ Finset.range s,
        if j = a then 1 else ((x : ZMod p) - j) * ((a : ZMod p) - j)⁻¹ := by
  induction s with
  | zero => simp [basisWeight]
  | succ s ih =>
    have hpar := (iterate_basisStep_counter p a x s).1
    have hcounter := (iterate_basisStep_counter p a x s).2
    rw [basisWeight, Function.iterate_succ_apply']
    simp only [basisStep, hpar, hcounter, (Fact.out : p.Prime).ne_zero, ↓reduceIte,
      cast_mulMod, Finset.prod_range_succ]
    change ((basisWeight p s a x : ℕ) : ZMod p) * _ = _
    rw [ih (by omega), cast_basisFactor ha (by omega)]

/-- The counter procedure evaluates the finite-grid Lagrange basis polynomial. Correctness
requires the whole alphabet to embed in the prime field, not merely the chosen symbol. -/
theorem cast_basisWeight {s : ℕ} (hs : s ≤ p) (a : Fin s) (x : ℕ) :
    ((basisWeight p s a x : ℕ) : ZMod p) =
      (Lagrange.basis Finset.univ (fun j : Fin s => (j.val : ZMod p)) a).eval (x : ZMod p) := by
  rw [cast_basisWeight_prod (a.isLt.trans_le hs) hs]
  rw [Lagrange.basis, Polynomial.eval_prod]
  rw [Finset.prod_range]
  calc
    (∏ j : Fin s, if (j : ℕ) = a.val then (1 : ZMod p)
      else ((x : ZMod p) - j.val) * ((a.val : ZMod p) - j.val)⁻¹) =
        ∏ j ∈ Finset.univ.erase a,
          if (j : ℕ) = a.val then (1 : ZMod p)
          else ((x : ZMod p) - j.val) * ((a.val : ZMod p) - j.val)⁻¹ := by
      symm
      apply Finset.prod_subset (Finset.erase_subset a Finset.univ)
      intro j _ hj
      have heq : j = a := by simpa only [Finset.mem_erase, Finset.mem_univ,
        and_true, not_not] using hj
      subst j
      simp
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j hj
      have hne : (j : ℕ) ≠ a.val := fun heq =>
        (Finset.mem_erase.mp hj).1 (Fin.ext heq)
      simp [hne, Lagrange.basisDivisor, mul_comm]

end Cslib.TreeEval.Ary.Packed
