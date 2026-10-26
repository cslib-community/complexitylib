/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Smolensky.Approximation
public import Complexity.Foundations.Combinatorics.CentralBinomial
public import Complexity.Foundations.BooleanAnalysis.LowDegreeParity
public import Mathlib.Algebra.Field.ZMod
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# The Razborov–Smolensky lower bound

**Parity is not in AC⁰[p]** for every odd prime `p` (`parity_notMem_AC0Mod`): constant-depth,
polynomial-size circuits of negations, unbounded fan-in conjunctions and disjunctions, and `MOD_p`
gates do not compute parity [Razborov1987], [Smolensky1987]. The finite form is a size–depth
tradeoff (`two_mul_two_pow_le_size_of_computes_parity`): a circuit of depth `d` computing the
parity of `n` bits has size at least `2 ^ ℓ · 2 / 5` whenever `100 (((p - 1) ℓ) ^ d + 1)² ≤ n + 1`,
so size `2 ^ Ω(n ^ (1 / (2 d)))` for fixed `d` and `p`.

The circuit agrees with a function of degree at most `((p - 1) ℓ) ^ d` over `ZMod p` (or any
commutative ring of characteristic `p`) on all but `size · 2 ^ n / 2 ^ ℓ` inputs
(`exists_lowDegree_approx`), while such a function agrees with parity on at most `6 / 10` of the
inputs (`BitString.card_agree_parity_le`, `ten_mul_card_filter_card_le_le`).

## Main definitions

* `Cslib.Circuits.Boolean.Smolensky.invertibleTwo`: `2` is invertible in `ZMod p` for an odd prime
  `p`.

## Main results

* `Cslib.Circuits.Boolean.Smolensky.two_mul_two_pow_le_size_of_computes_parity`: the tradeoff.
* `Cslib.Circuits.Boolean.Smolensky.parity_notMem_AC0Mod`: parity is not in AC⁰[p].

## References

* [A. A. Razborov, *Lower bounds on the size of bounded depth circuits over a complete basis with
  logical addition*][Razborov1987]
* [R. Smolensky, *Algebraic methods in the theory of lower bounds for Boolean circuit
  complexity*][Smolensky1987]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Smolensky

open Finset BitString

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

/-- `2` is invertible in `ZMod p` for an odd prime `p`. -/
@[instance_reducible] def invertibleTwo (hp2 : p ≠ 2) : Invertible (2 : ZMod p) :=
  invertibleOfNonzero fun h => hp2 <| (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1
    ((ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h))

/-- **The Razborov–Smolensky size–depth tradeoff.** A circuit of the AC⁰[p] basis of depth `d`
computing the parity of `n` bits, for an odd prime `p`, has size at least `2 ^ ℓ · 2 / 5` whenever
`100 (((p - 1) ℓ) ^ d + 1)² ≤ n + 1`. -/
theorem two_mul_two_pow_le_size_of_computes_parity (hp2 : p ≠ 2)
    {C : Circuit Unbounded.extSignature n 1}
    (hC : C.Computes (Unbounded.extInterpretation (modGate p)) (single (parity n))) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ)
    (hn : 100 * (((p - 1) * ℓ) ^ C.depth + 1) ^ 2 ≤ n + 1) : 2 * 2 ^ ℓ ≤ 5 * C.size := by
  classical
  let _ := invertibleTwo hp2
  obtain ⟨Q, hQ, herr⟩ := exists_lowDegree_approx (R := ZMod p) hℓ C
  have heval : ∀ x, C.eval (Unbounded.extInterpretation (modGate p)) x 0 = parity n x := fun x =>
    congrFun (hC x) 0
  simp only [heval] at herr
  set A := univ.filter fun x => Q x = bitVal (ZMod p) (parity n x)
  set E := univ.filter fun x => Q x ≠ bitVal (ZMod p) (parity n x)
  have htotal : #A + #E = 2 ^ n := by
    rw [card_filter_add_card_filter_not, card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin]
  have hA : 10 * #A ≤ 6 * 2 ^ n :=
    (Nat.mul_le_mul_left 10 (card_agree_parity_le hQ)).trans (ten_mul_card_filter_card_le_le n _ hn)
  -- so the errors are at least `4 / 10` of the inputs
  have hE : 4 * 2 ^ n ≤ 10 * #E := by omega
  have h : 2 * 2 ^ n * (2 * 2 ^ ℓ) ≤ 2 * 2 ^ n * (5 * C.size) := by
    calc 2 * 2 ^ n * (2 * 2 ^ ℓ) = 4 * 2 ^ n * 2 ^ ℓ := by ring
      _ ≤ 10 * #E * 2 ^ ℓ := Nat.mul_le_mul_right _ hE
      _ = 10 * (#E * 2 ^ ℓ) := by ring
      _ ≤ 10 * (C.size * 2 ^ n) := Nat.mul_le_mul_left _ herr
      _ = 2 * 2 ^ n * (5 * C.size) := by ring
  exact Nat.le_of_mul_le_mul_left h (by positivity)

/-- **Parity is not in AC⁰[p]** for an odd prime `p` (Razborov–Smolensky). -/
theorem parity_notMem_AC0Mod (hp2 : p ≠ 2) : Language.ofSlices parity ∉ AC0Mod p := by
  intro h
  obtain ⟨d, size, hsize, hC⟩ := ConstDepth.mem_iff.1 h
  have hp1 := hp.out.two_le
  -- the size bound at the lengths `100 (((p - 1) ℓ) ^ d + 1)² - 1` is a polynomial in `ℓ`
  have hpoly : PolynomiallyBounded fun ℓ => 5 * size (100 * (((p - 1) * ℓ) ^ d + 1) ^ 2) :=
    PolynomiallyBounded.mul (by fun_prop) (hsize.comp (by fun_prop))
  obtain ⟨ℓ, hlt, hℓ⟩ := (hpoly.eventually_lt_two_pow.and (Filter.eventually_ge_atTop 1)).exists
  obtain ⟨C, hCc, hCd, hCs⟩ := hC (100 * (((p - 1) * ℓ) ^ d + 1) ^ 2)
  rw [Language.slice_ofSlices] at hCc
  have hbase : 1 ≤ (p - 1) * ℓ := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have h := two_mul_two_pow_le_size_of_computes_parity hp2 hCc hℓ (by
    have := Nat.pow_le_pow_right hbase hCd
    have := Nat.pow_le_pow_left (Nat.add_le_add_right this 1) 2
    omega)
  have : 5 * C.size ≤ 5 * size (100 * (((p - 1) * ℓ) ^ d + 1) ^ 2) := Nat.mul_le_mul_left 5 hCs
  omega

end Cslib.Circuits.Boolean.Smolensky
