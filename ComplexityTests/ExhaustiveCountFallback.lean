/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module

public import Complexity.Init
public import Complexity.Computability.GenericRAM.Native.ExhaustiveCountFallback
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Tactic.PolyTime

/-!
# Kernel-checked tests for `Cslib.GenericRAM.ExhaustiveCountFallback`

Concrete `decide` regression tests and end-to-end finite-threshold guard-fallback absorption
instantiations for `countSystemExhaustive`, `countCNFExhaustive`, and the `NativeCertificate.branch`
constant-absorption combinators.
-/

@[expose] public section

namespace ComplexityTests.ExhaustiveCountFallback

open Cslib.BitString Cslib.Complexity Cslib.GenericRAM
open Cslib.GenericRAM.ExhaustiveCountFallback Cslib.Logic.PL Turing.MultiTapeTM

/-! ### 1. Sparse `𝔽₂` Polynomial System Counter (`countSystemExhaustive`) -/

/-- Canonical sparse `𝔽₂` system on `{0, 2}` (`x₀ + x₂ = 0` and `x₀ x₂ = 0`), forcing
`x₀ = x₂ = 0`. -/
def sysZeroTwo : List (List (List ℕ)) := [[[0], [2]], [[0, 2]]]

-- Empty system `[] ↦ 2 ^ n`, contradictory constant equation `[[]]` (`1 = 0`), single quadratic
-- equation `x₀ x₂ = 0` on `{0, 2}`, `sysZeroTwo`, and streaming prefix state at `j = 6`.
example :
    countSystemExhaustive (0, []) = 1 ∧
      countSystemExhaustive (3, []) = 8 ∧
      countSystemExhaustive (4, []) = 16 ∧
      countSystemExhaustive (0, [[[]]]) = 0 ∧
      countSystemExhaustive (3, [[[]]]) = 0 ∧
      countSystemExhaustive (4, [[[0, 2]], [[]]]) = 0 ∧
      countSystemExhaustive (3, [[[0, 2]]]) = 6 ∧
      countSystemExhaustive (4, [[[0, 2]]]) = 12 ∧
      countSystemExhaustive (4, [[[0, 2]]]) = 2 * countSystemExhaustive (3, [[[0, 2]]]) ∧
      countSystemExhaustive (3, sysZeroTwo) = 2 ∧
      countSystemExhaustive (4, sysZeroTwo) = 4 ∧
      (countSystemPrefix (3, [[[0, 2]]]) 6).2.2.1 = (3, [[[0, 2]]]) ∧
      (countSystemPrefix (3, [[[0, 2]]]) 6).2.2.2 = 5 ∧
      (countSystemPrefix (3, [[[0, 2]]]) 6).2.2.2 ≤ 6 := by decide

-- Exact agreement with `Cslib.BitString.commonZeroCount` on `n = 4` with variables `{0, 2}`.
example :
    countSystemExhaustive (4, sysZeroTwo) =
      commonZeroCount (Finset.univ : Finset (Fin sysZeroTwo.length))
        (fun i : Fin sysZeroTwo.length => equationToFinset 4 sysZeroTwo[i]) := by
  apply countSystemExhaustive_eq_commonZeroCount
  unfold sysZeroTwo IsCanonicalEquation IsCanonicalMonomial
  decide

/-! ### 2. Declared-Variable `CNF` Model Counter (`countCNFExhaustive`) -/

/-- Equivalence `x₀ ↔ x₂` using only variables `{0, 2}` (`numVars = 2`, `modelCount = 2`):
declaring `n = 3` (unused `{1}`) doubles to `4`; declaring `n = 4` (unused `{1, 3}`) gives `8`. -/
def eqvZeroTwo : CNF ℕ := [[(0, true), (2, false)], [(0, false), (2, true)]]

-- Empty formula `[] ↦ 2 ^ n`, unsatisfiable clauses, `eqvZeroTwo`, concrete agreement with
-- `CNF.modelCountOn φ (Finset.range n)`, out-of-range variable boundary, and `countCNFPrefix`.
example :
    countCNFExhaustive (0, []) = 1 ∧
      countCNFExhaustive (3, []) = 8 ∧
      countCNFExhaustive (4, []) = 16 ∧
      countCNFExhaustive (0, [[]]) = 0 ∧
      countCNFExhaustive (4, [[]]) = 0 ∧
      countCNFExhaustive (3, [[(1, true)], [(1, false)]]) = 0 ∧
      eqvZeroTwo.modelCount = 2 ∧
      countCNFExhaustive (3, eqvZeroTwo) = 4 ∧
      countCNFExhaustive (4, eqvZeroTwo) = 8 ∧
      countCNFExhaustive (4, eqvZeroTwo) = 2 * countCNFExhaustive (3, eqvZeroTwo) ∧
      countCNFExhaustive (0, []) = CNF.modelCountOn ([] : CNF ℕ) (Finset.range 0) ∧
      countCNFExhaustive (3, eqvZeroTwo) = eqvZeroTwo.modelCountOn (Finset.range 3) ∧
      countCNFExhaustive (4, eqvZeroTwo) = eqvZeroTwo.modelCountOn (Finset.range 4) ∧
      countCNFExhaustive (2, [[(5, true)]]) = 0 ∧
      countCNFExhaustive (2, [[(5, false)]]) = 4 ∧
      (countCNFPrefix (4, eqvZeroTwo) 7).2.2.1 = (4, eqvZeroTwo) ∧
      (countCNFPrefix (4, eqvZeroTwo) 7).2.2.2 ≤ 7 := by decide

/-! ### 3. Guarded-Fallback Combinator & Constant Absorption Across `n < 3` vs `n ≥ 3` -/

/-- Threshold guard `ok3 (n, φ) := decide (3 ≤ n)`, returning `false` iff `n < 3` (`N₀ = 3`). -/
def ok3 (x : ℕ × CNF ℕ) : Bool := decide (3 ≤ x.1)

/-- Demo fast branch on `n ≥ 3`: returns `2 ^ n` on the empty formula `[]` and `0` otherwise. -/
def fastBranchDemo (x : ℕ × CNF ℕ) : ℕ :=
  if x.2.isEmpty then 2 ^ x.1 else 0

/-- Combined demo target running `fastBranchDemo` for `n ≥ 3` and `countCNFExhaustive` for
`n < 3`. -/
def targetDemo (x : ℕ × CNF ℕ) : ℕ :=
  if ok3 x then fastBranchDemo x else countCNFExhaustive x

-- Concrete checks across threshold `n = 0, 1, 2` (`ok3 = false`, running `countCNFExhaustive`)
-- and `n = 3, 4` (`ok3 = true`, running `fastBranchDemo`).
example :
    targetDemo (0, []) = 1 ∧
      targetDemo (1, [[(0, true)]]) = 1 ∧
      targetDemo (2, [[(0, true)]]) = 2 ∧
      targetDemo (2, [[(0, true)], [(0, false)]]) = 0 ∧
      targetDemo (3, []) = countCNFExhaustive (3, []) ∧
      targetDemo (4, []) = countCNFExhaustive (4, []) ∧
      targetDemo (3, [[]]) = countCNFExhaustive (3, [[]]) ∧
      targetDemo (4, eqvZeroTwo) = 0 := by decide

theorem computableInPolyTime_ok3 :
    ComputableInPolyTime ok3 (encPair encUnary encCNF) encBool := by
  unfold ok3 encCNF
  polytime

theorem computableInPolyTime_isEmptyCNF :
    ComputableInPolyTime (fun x : ℕ × CNF ℕ => x.2.isEmpty) (encPair encUnary encCNF) encBool := by
  have heq : (fun x : ℕ × CNF ℕ => x.2.isEmpty) = fun x => decide (x.2.length = 0) := by
    funext x
    cases x.2 <;> rfl
  rw [heq]
  unfold encCNF
  polytime

/-- Polynomial-time `NativeCertificate` for `fastBranchDemo`. -/
noncomputable def fastBranchDemoCert :
    NativeCertificate fastBranchDemo (encPair encUnary encCNF) encNat :=
  NativeCertificate.branch
    (NativeCertificate.ofPolyTime computableInPolyTime_isEmptyCNF)
    (BooleanFold.clock.comp (NativeCertificate.linear (ComputableInO.fst encUnary encCNF)))
    (NativeCertificate.const 0)

theorem fastBranchDemoCert_isPolynomial : fastBranchDemoCert.IsPolynomial := by
  apply NativeCertificate.branch_isPolynomial
  · exact NativeCertificate.ofPolyTime_isPolynomial computableInPolyTime_isEmptyCNF
  · refine ⟨(PolyBounded.self.add .self).mono fun x => ?_,
        (PolyBounded.self.add .self).mono fun x => ?_⟩ <;>
    · simp only [NativeCertificate.comp_time, NativeCertificate.comp_space,
        NativeCertificate.linear_time, NativeCertificate.linear_space, BooleanFold.clock,
        length_encPair, encUnary_apply, List.length_replicate]
      omega
  · exact NativeCertificate.const_isPolynomial 0

/-- End-to-end instantiation of `computableInO_of_guarded_fallback` across `n < 3` vs `n ≥ 3`:
combining `fastBranchDemoCert` with `countCNFExhaustiveCertificate` absorbs the `2 ^ n` exhaustive
search on `n < 3` into a polynomial time and polynomial workspace `ComputableInO` bound. -/
theorem targetDemo_computableInO_absorbed :
    ∃ C d : ℕ, ∃ S : ℕ × CNF ℕ → ℕ,
      PolyBounded (fun x => (encPair encUnary encCNF x).length) S ∧
      ComputableInO targetDemo (encPair encUnary encCNF) encNat
        (fun x => fastBranchDemoCert.time x + C * ((encPair encUnary encCNF x).length + 1) ^ d)
        S := by
  obtain ⟨P_ex, Q_ex, hP, hQ, hT_ex⟩ := exists_countCNFExhaustive_time_le
  exact computableInO_of_guarded_fallback (μ := Prod.fst) (N₀ := 3)
    computableInPolyTime_ok3 fastBranchDemoCert countCNFExhaustiveCertificate
    (fun x hx => by simp only [targetDemo, hx, ↓reduceIte])
    (fun x hx => by simp only [targetDemo, hx, Bool.false_eq_true, ↓reduceIte])
    fastBranchDemoCert_isPolynomial.2
    polyBounded_countCNFExhaustive_space
    (fun x hx => by
      simp only [ok3, decide_eq_false_iff_not] at hx
      omega)
    hP hQ (fun _ _ => le_rfl) (fun x _ => hT_ex x)

/-- End-to-end instantiation of `exists_real_exp_bound_of_guarded_fallback` with subexponential
exponent `E x = √n`: the `n < 3` exhaustive search is absorbed into `(|x| + 1) ^ e * 2 ^ √n`
while keeping polynomial workspace. -/
theorem targetDemo_subexp_absorbed :
    ∃ e : ℕ, ∃ S : ℕ × CNF ℕ → ℕ,
      PolyBounded (fun x => (encPair encUnary encCNF x).length) S ∧
      ComputableInO targetDemo (encPair encUnary encCNF) encNat
        (fun x => ((encPair encUnary encCNF x).length + 1) ^ e *
          ⌈(2 : ℝ) ^ Real.sqrt (x.1 : ℝ)⌉₊) S := by
  obtain ⟨P_ex, Q_ex, hP, hQ, hT_ex⟩ := exists_countCNFExhaustive_time_le
  obtain ⟨C_f, d_f, hfast_time⟩ := fastBranchDemoCert_isPolynomial.1.exists_le
  obtain ⟨_, e, S, hS, _, hcomp⟩ :=
    exists_real_exp_bound_of_guarded_fallback (f := targetDemo) (μ := Prod.fst)
      (E := fun x : ℕ × CNF ℕ => Real.sqrt (x.1 : ℝ)) (N₀ := 3) (C_f := C_f) (d_f := d_f)
      computableInPolyTime_ok3 fastBranchDemoCert countCNFExhaustiveCertificate
      (fun x hx => by simp only [targetDemo, hx, ↓reduceIte])
      (fun x hx => by simp only [targetDemo, hx, Bool.false_eq_true, ↓reduceIte])
      fastBranchDemoCert_isPolynomial.2
      polyBounded_countCNFExhaustive_space
      (fun x hx => by
        simp only [ok3, decide_eq_false_iff_not] at hx
        omega)
      hP hQ (fun _ => Real.sqrt_nonneg _)
      (fun x _ => by
        have h1 : (fastBranchDemoCert.time x : ℝ) ≤
            (C_f : ℝ) * ((encPair encUnary encCNF x).length + 1 : ℝ) ^ d_f := by
          exact_mod_cast hfast_time x
        have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ Real.sqrt (x.1 : ℝ) :=
          Real.one_le_rpow (by norm_num) (Real.sqrt_nonneg _)
        calc (fastBranchDemoCert.time x : ℝ)
            ≤ (C_f : ℝ) * ((encPair encUnary encCNF x).length + 1 : ℝ) ^ d_f * 1 := by
              rw [mul_one]; exact h1
          _ ≤ (C_f : ℝ) * ((encPair encUnary encCNF x).length + 1 : ℝ) ^ d_f *
                (2 : ℝ) ^ Real.sqrt (x.1 : ℝ) :=
              mul_le_mul_of_nonneg_left h2 (by positivity))
      (fun x _ => hT_ex x)
  exact ⟨e, S, hS, hcomp⟩

end ComplexityTests.ExhaustiveCountFallback
