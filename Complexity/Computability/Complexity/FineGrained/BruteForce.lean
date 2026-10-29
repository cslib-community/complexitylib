/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.Assignment
public import Complexity.Computability.Complexity.FineGrained.ExhaustiveSearch
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Exhaustive search for satisfiability

Exhaustive search decides `SAT` by trying the `2 ^ n` numbered assignments of the `n` distinct
variables of a formula (`Cslib.Logic.PL.CNF.satisfiable_iff_exists_bitsAssignment`). By
`Cslib.Complexity.DecidableInExpTime.of_exhaustiveSearch`, iterating the polynomial-time evaluation
step (`Cslib.Complexity.computableInPolyTime_eval_bitsAssignment`) `2 ^ n` times decides `SAT`, and
every `k`-SAT, within time `2 ^ n` times a polynomial in the length of the encoded formula
(`Cslib.Complexity.SAT_decidableInExpTime_one`, `Cslib.Complexity.KSAT_decidableInExpTime_one`).

## Main definitions

* `Cslib.Complexity.BruteForce.search`: exhaustive search.

## Main results

* `Cslib.Complexity.exists_le_mul_two_pow_of_polyBounded`: combining `2 ^ μ a + 1` rounds of a
  polynomial with a polynomial into `2 ^ μ a` times a polynomial.
* `Cslib.Complexity.BruteForce.search_eq_true_iff`: exhaustive search decides `SAT`.
* `Cslib.Complexity.SAT_decidableInExpTime_one`, `Cslib.Complexity.KSAT_decidableInExpTime_one`:
  `SAT` and `k`-SAT are decidable within time `2 ^ n` times a polynomial.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 2.3][AroraBarak09]
* [R. Impagliazzo, R. Paturi, *On the complexity of k-SAT*][ImpagliazzoPaturi2001]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Exponential bounds -/

/-- A bound by `2 ^ μ a + 1` rounds of a polynomial, plus a polynomial, is a bound by `2 ^ μ a`
times a polynomial. -/
theorem exists_le_mul_two_pow_of_polyBounded {α : Type*} {size μ T P Q : α → ℕ}
    (hP : PolyBounded size P) (hQ : PolyBounded size Q)
    (hT : ∀ a, T a ≤ (2 ^ μ a + 1) * P a + Q a) :
    ∃ c e, ∀ a, T a ≤ c * 2 ^ μ a * (size a + 1) ^ e := by
  obtain ⟨c₁, d₁, hP⟩ := hP.exists_le
  obtain ⟨c₂, d₂, hQ⟩ := hQ.exists_le
  refine ⟨2 * c₁ + c₂, d₁ + d₂, fun a => (hT a).trans ?_⟩
  have h₁ : (size a + 1) ^ d₁ ≤ (size a + 1) ^ (d₁ + d₂) :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_right _ _)
  have h₂ : (size a + 1) ^ d₂ ≤ (size a + 1) ^ (d₁ + d₂) :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_left _ _)
  have hN : 1 ≤ 2 ^ μ a := Nat.one_le_two_pow
  have hP' := (hP a).trans (Nat.mul_le_mul_left c₁ h₁)
  have hQ' := (hQ a).trans (Nat.mul_le_mul_left c₂ h₂)
  generalize (size a + 1) ^ (d₁ + d₂) = M at *
  generalize 2 ^ μ a = N at *
  have : (N + 1) * P a ≤ 2 * N * (c₁ * M) :=
    (Nat.mul_le_mul (show N + 1 ≤ 2 * N by omega) hP').trans (le_of_eq (by ring))
  have : Q a ≤ N * (c₂ * M) := hQ'.trans (Nat.le_mul_of_pos_left _ (by omega))
  nlinarith

namespace BruteForce

/-! ### The search -/

/-- **Exhaustive search**: try the `2 ^ n` assignments numbered by `i < 2 ^ n` on the `n` distinct
variables of the formula. -/
def search (φ : CNF ℕ) : Bool :=
  (List.range (2 ^ φ.distinctVars.length)).any fun i => φ.eval (bitsAssignment φ.distinctVars i)

/-- **Exhaustive search decides `SAT`.** -/
theorem search_eq_true_iff (φ : CNF ℕ) : search φ = true ↔ φ ∈ SAT := by
  rw [search, mem_SAT,
    CNF.satisfiable_iff_exists_bitsAssignment fun v hv => CNF.mem_distinctVars.mpr hv]
  simp

end BruteForce

open ComputableInPolyTime in
/-- **`SAT` by exhaustive search**: `SAT` is decidable within time `2 ^ n` times a polynomial in the
length of the encoded formula, on formulas with `n` variables. -/
theorem SAT_decidableInExpTime_one : DecidableInExpTime SAT encCNF CNF.numVars 1 := by
  have hB : DecidableInExpTime
      {p : (CNF ℕ × List ℕ) × ℕ | p.1.1.eval (bitsAssignment p.1.2 p.2) = true}
      (encPair (encPair encCNF (encList encNat)) encNat) (fun _ => 0) 0 :=
    .of_computableInPolyTime computableInPolyTime_eval_bitsAssignment (fun _ => Iff.rfl)
  have hf : ComputableInPolyTime
      (fun q : CNF ℕ × ℕ => ((q.1, q.1.distinctVars), q.2))
      (encPair encCNF encNat) (encPair (encPair encCNF (encList encNat)) encNat) := by
    have := SAT.computableInPolyTime_distinctVars
    fun_prop
  have hν : ComputableInPolyTime CNF.numVars encCNF encUnary := by
    have := SAT.computableInPolyTime_distinctVars
    have heq : (CNF.numVars : CNF ℕ → ℕ) = fun φ => φ.distinctVars.length := by
      funext φ; exact φ.length_distinctVars.symm
    rw [heq]
    fun_prop
  have hfA (φ : CNF ℕ) : φ ∈ SAT ↔ ∃ r < 2 ^ φ.numVars,
      ((φ, φ.distinctVars), r) ∈
        {p : (CNF ℕ × List ℕ) × ℕ | p.1.1.eval (bitsAssignment p.1.2 p.2) = true} := by
    rw [mem_SAT, ← φ.length_distinctVars,
      CNF.satisfiable_iff_exists_bitsAssignment fun v hv => CNF.mem_distinctVars.mpr hv]
    rfl
  simpa using hB.of_exhaustiveSearch hf hν hfA (c := 0) (fun _ _ => Nat.zero_le _)
    (M := 1) (K := 0) (fun φ => by simp) le_rfl

open ComputableInPolyTime in
/-- Checking that every clause has at most `k` literals is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_all_length_le (k : ℕ) :
    ComputableInPolyTime (fun φ : CNF ℕ => φ.all fun c => decide (c.length ≤ k)) encCNF
      encBool := by
  unfold encCNF
  fun_prop

/-- `k`-SAT is `SAT` restricted to the formulas whose clauses have at most `k` literals. -/
theorem KSAT_eq_inter (k : ℕ) {B : Set (CNF ℕ)} (hB : KSAT k ⊆ B) (hBSAT : B ⊆ SAT) :
    KSAT k = {φ | (φ.all fun c => decide (c.length ≤ k)) = true} ∩ B := by
  ext φ
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, List.all_eq_true, decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1, hB h⟩, fun h => ⟨h.1, hBSAT h.2⟩⟩

/-- **`k`-SAT by exhaustive search**: `k`-SAT is decidable within time `2 ^ n` times a polynomial
in the length of the encoded formula, on formulas with `n` variables. -/
theorem KSAT_decidableInExpTime_one (k : ℕ) : DecidableInExpTime (KSAT k) encCNF CNF.numVars 1 := by
  rw [KSAT_eq_inter k (KSAT_subset_SAT k) le_rfl]
  exact SAT_decidableInExpTime_one.inter (computableInPolyTime_all_length_le k) zero_le_one

end Cslib.Complexity
