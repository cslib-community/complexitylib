/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.MatrixProduct
public import CslibFrontier.Computability.Circuit.Arithmetic.WordPolynomial
public import CslibFrontier.Foundations.Data.List.OfFnPad
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A homogeneous depth-five circuit for `IMM`

Over every commutative semiring and for every `n ≥ 2`, the iterated matrix multiplication
polynomial `IMM_{n,n}` has a syntactically homogeneous `ΣΠΣΠΣ` circuit of size at most
`n ^ (√n + 4)`. This is the block construction of [OpenAI, §6][OpenAI2026DepthFive]. With the
lower bound `n ^ (√n / 400)` over fields of characteristic zero it shows that the size is
`n ^ Θ(√n)`.

Split the `n` generic matrices into `r` consecutive blocks of at most `t` matrices each. Every
entry of the product of a block of `ℓ` matrices is a sum of `n ^ (ℓ - 1)` monomials of degree
`ℓ`, one for each choice of the internal indices, so the product of the blocks is a product of
`r` matrices whose entries are sums of monomials, and
`Cslib.Circuits.DepthFive.exists_circuit_list_prod` applies.

Here `t = Nat.sqrt n + 1` and `r = (n + t - 1) / t`, so that `n ≤ r * t`. To group the product
into blocks of exactly `t` factors, the `n` matrices are padded by identity matrices to `r * t`
matrices. A padded factor contributes the indicator that an index path does not move, which is a
coefficient of the middle sums. The circuit has `r * n ^ (t + 1)` lower product gates,
`r * n ^ 2` middle sum gates and `n ^ (r + 1)` upper product gates. The source counts
`n ^ (r - 1)` upper products and also counts leaves and bottom sums; both counts are at most
`n ^ (√n + 4)`.

## Main results

* `Cslib.Circuits.DepthFive.exists_circuit_imm_of_le_mul`: the circuit for any block length.
* `Cslib.Circuits.DepthFive.exists_circuit_size_le_rpow`: size at most `n ^ (√n + 4)`.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §6 (unrefereed preprint)
-/

public section

namespace Cslib.Circuits.DepthFive

open MvPolynomial Cslib.Circuits.Arithmetic

variable {K : Type*} [CommSemiring K] {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- The product along an index path `Q` of a block of `t` matrices, the `i`-th being the generic
matrix of layer `j * t + i` if that layer exists and the identity otherwise: the monomial of the
existing layers, times the indicator that `Q` does not move in the padded layers. -/
private theorem prod_block_apply (t j : ℕ) (Q : Fin (t + 1) → Fin n) :
    ∏ i : Fin t, (if hi : j * t + i < n then immMatrix K n n ⟨j * t + i, hi⟩ else 1)
        (Q i.castSucc) (Q i.succ) =
      C (if ∀ i : Fin t, ¬ j * t + i < n → Q i.castSucc = Q i.succ then 1 else 0) *
        ∏ k : Fin (min t (n - j * t)),
          X ((⟨j * t + k, by have := k.2; omega⟩ : Fin n),
            Q ⟨k, by have := k.2; omega⟩, Q ⟨k + 1, by have := k.2; omega⟩) := by
  have key (i : Fin t) :
      (if hi : j * t + i < n then immMatrix K n n ⟨j * t + i, hi⟩ else 1)
          (Q i.castSucc) (Q i.succ) =
        (if hi : (i : ℕ) < min t (n - j * t) then
          X ((⟨j * t + i, by omega⟩ : Fin n), Q ⟨i, by omega⟩, Q ⟨i + 1, by omega⟩) else 1) *
        C (if ¬ j * t + i < n → Q i.castSucc = Q i.succ then (1 : K) else 0) := by
    by_cases hi : j * t + i < n
    · have hi' : (i : ℕ) < min t (n - j * t) := by have := i.2; omega
      simp only [hi, hi', ↓reduceDIte, not_true_eq_false, IsEmpty.forall_iff, ↓reduceIte,
        map_one, mul_one]
      rfl
    · have hi' : ¬ (i : ℕ) < min t (n - j * t) := by omega
      simp [hi, hi', Matrix.one_apply]
  simp_rw [key]
  rw [Finset.prod_mul_distrib, ← List.prod_ofFn,
    List.prod_ofFn_dite_lt (Nat.min_le_left _ _) (fun k : Fin (min t (n - j * t)) =>
      (X ((⟨j * t + k, by have := k.2; omega⟩ : Fin n),
        Q ⟨k, by have := k.2; omega⟩, Q ⟨k + 1, by have := k.2; omega⟩) : MvPolynomial _ K)),
    List.prod_ofFn, ← map_prod, Finset.prod_ite_zero, mul_comm]
  simp

/-- `IMM_{n,n}` has a homogeneous depth-five circuit with `r * n ^ (t + 1)` lower product gates,
`r * n ^ 2` middle sum gates and `n ^ (r + 1)` upper product gates, for every block length `t`
and number of blocks `r` with `n ≤ r * t`. -/
theorem exists_circuit_imm_of_le_mul (K : Type*) [CommSemiring K] {n : ℕ} [NeZero n] {r t : ℕ}
    (h : n ≤ r * t) :
    ∃ d : Circuit K (Fin n × Fin n × Fin n),
      d.polynomial = imm K n n ∧ d.size = r * n ^ (t + 1) + r * n ^ 2 + n ^ (r + 1) := by
  classical
  obtain ⟨d, hd, hs⟩ := exists_circuit_list_prod (K := K) (ν := n) (r := r)
    (Λ := Fin (t + 1) → Fin n) (fun j => min t (n - j * t))
    (fun j a b Q => if Q 0 = a ∧ Q (Fin.last t) = b then
      (if ∀ i : Fin t, ¬ (j : ℕ) * t + i < n → Q i.castSucc = Q i.succ then 1 else 0) else 0)
    (fun j Q k => ((⟨j * t + k, by have := k.2; omega⟩ : Fin n),
      Q ⟨k, by have := k.2; omega⟩, Q ⟨k + 1, by have := k.2; omega⟩))
  refine ⟨d, hd.trans ?_, by simpa using hs⟩
  rw [imm, ← List.prod_ofFn_dite_lt h (immMatrix K n n), List.ofFn_mul, List.prod_flatten,
    List.map_ofFn]
  refine congrArg (fun L : List (Matrix (Fin n) (Fin n) _) => L.prod 0 0)
    (congrArg List.ofFn (funext fun j => Matrix.ext fun a b => ?_))
  simp only [Function.comp_apply, Matrix.of_apply, Matrix.list_prod_ofFn_apply]
  refine Finset.sum_congr rfl fun Q _ => ?_
  rw [prod_block_apply]
  split_ifs <;> simp

/-- The gate count of the block construction with `t = Nat.sqrt n + 1` is at most
`n ^ (Nat.sqrt n + 4)`. -/
private theorem count_le {n : ℕ} (hn : 2 ≤ n) :
    (n + (n.sqrt + 1) - 1) / (n.sqrt + 1) * n ^ (n.sqrt + 1 + 1) +
        (n + (n.sqrt + 1) - 1) / (n.sqrt + 1) * n ^ 2 +
        n ^ ((n + (n.sqrt + 1) - 1) / (n.sqrt + 1) + 1) ≤ n ^ (n.sqrt + 4) := by
  set s := n.sqrt
  set r := (n + (s + 1) - 1) / (s + 1)
  have hs : 1 ≤ s := Nat.sqrt_pos.2 (by omega)
  have hlt : n < (s + 1) * (s + 1) := Nat.lt_succ_sqrt n
  have hle : s * s ≤ n := Nat.sqrt_le n
  have hr : r ≤ s + 1 := by
    have e : n + (s + 1) - 1 = n + s := by omega
    refine Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul (by omega)).2 ?_)
    rw [e]
    nlinarith
  have hsn : s + 1 ≤ n := by nlinarith
  have hn0 : 0 < n := by omega
  have h₁ : r * n ^ (s + 1 + 1) ≤ n ^ (s + 3) := by
    calc r * n ^ (s + 1 + 1) ≤ n * n ^ (s + 2) := Nat.mul_le_mul_right _ (hr.trans hsn)
      _ = n ^ (s + 3) := by ring
  have h₂ : r * n ^ 2 ≤ n ^ (s + 2) := by
    calc r * n ^ 2 ≤ n * n ^ 2 := Nat.mul_le_mul_right _ (hr.trans hsn)
      _ = n ^ 3 := by ring
      _ ≤ n ^ (s + 2) := Nat.pow_le_pow_right hn0 (by omega)
  have h₃ : n ^ (r + 1) ≤ n ^ (s + 2) := Nat.pow_le_pow_right hn0 (by omega)
  calc r * n ^ (s + 1 + 1) + r * n ^ 2 + n ^ (r + 1)
      ≤ n ^ (s + 3) + n ^ (s + 2) + n ^ (s + 2) := by omega
    _ = n ^ (s + 3) + 2 * n ^ (s + 2) := by ring
    _ ≤ n ^ (s + 3) + n * n ^ (s + 2) := by gcongr
    _ = 2 * n ^ (s + 3) := by ring
    _ ≤ n * n ^ (s + 3) := by gcongr
    _ = n ^ (s + 4) := by ring

/-- **Homogeneous depth-five upper bound for `IMM`.** Over every commutative semiring and for
every `n ≥ 2`, some syntactically homogeneous `ΣΠΣΠΣ` circuit computing `IMM_{n,n}` has size at
most `n ^ (√n + 4)`. -/
theorem exists_circuit_size_le_rpow (K : Type*) [CommSemiring K] {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) :
    ∃ d : Circuit K (Fin n × Fin n × Fin n),
      d.polynomial = imm K n n ∧ (d.size : ℝ) ≤ (n : ℝ) ^ (√(n : ℝ) + 4) := by
  have hmul : n ≤ (n + (n.sqrt + 1) - 1) / (n.sqrt + 1) * (n.sqrt + 1) := by
    have e : n + (n.sqrt + 1) - 1 = n + n.sqrt := by omega
    have h₁ := Nat.div_add_mod (n + n.sqrt) (n.sqrt + 1)
    have h₂ := Nat.mod_lt (n + n.sqrt) (by omega : 0 < n.sqrt + 1)
    rw [e]
    linarith
  obtain ⟨d, hd, hs⟩ := exists_circuit_imm_of_le_mul K hmul
  refine ⟨d, hd, ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  calc (d.size : ℝ) ≤ ((n ^ (n.sqrt + 4) : ℕ) : ℝ) := by
        rw [hs]; exact_mod_cast count_le hn
    _ = (n : ℝ) ^ ((n.sqrt : ℝ) + 4) := by
        rw [Nat.cast_pow, ← Real.rpow_natCast]; congr 1; push_cast; ring
    _ ≤ (n : ℝ) ^ (√(n : ℝ) + 4) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [Real.nat_sqrt_le_real_sqrt (a := n)])

end Cslib.Circuits.DepthFive
