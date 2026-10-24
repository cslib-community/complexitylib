/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.FineGrained.OrthogonalVectors

/-!
# Tests: the exponential time hypotheses

Numbers of variables and `k`-SAT on concrete formulas; numbered assignments; exhaustive search on
satisfiable and unsatisfiable formulas, including a formula with no clauses and one with an empty
clause; concrete instances of the orthogonal vectors problem, with vectors of different lengths and
empty sides; the split-and-list reduction on concrete formulas, against satisfiability; the
non-vacuity of the time bounds and exponents; and the axioms of the headline theorems.
-/

namespace ComplexityTests.FineGrained

open Cslib Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-- `(x₀ ∨ ¬x₁) ∧ (x₁ ∨ ¬x₀) ∧ x₂`. -/
private def φ₁ : CNF ℕ := [[(0, true), (1, false)], [(1, true), (0, false)], [(2, true)]]

/-- `x₀ ∧ ¬x₀`. -/
private def φ₂ : CNF ℕ := [[(0, true)], [(0, false)]]

/-! ### Variables and `k`-SAT -/

example : φ₁.numVars = 3 := by decide

example : φ₁.distinctVars = [0, 1, 2] := by decide

/-- Repeated variables count once; variables are numbered arbitrarily. -/
example : CNF.numVars ([[(7, true), (7, false)], [(100, true)]] : CNF ℕ) = 2 := by decide

example : CNF.numVars ([] : CNF ℕ) = 0 := rfl

example : φ₁ ∈ KSAT 2 := ⟨by decide, fun _ => true, rfl⟩

example : φ₁ ∉ KSAT 1 := fun h => absurd (h.1 _ List.mem_cons_self) (by decide)

example : φ₂ ∉ KSAT 3 := fun ⟨_, σ, hσ⟩ => by
  cases h : σ 0 <;> simp [φ₂, h] at hσ

example : KSAT 3 = ThreeSAT := KSAT_three

/-! ### Numbered assignments and exhaustive search -/

/-- `2 = 0b10`: the variable at position `1` is true, the one at position `0` false. -/
example : bitsAssignment [3, 7] 2 7 = true := by decide

example : bitsAssignment [3, 7] 2 3 = false := by decide

example : BruteForce.search φ₁ = true := by decide

example : BruteForce.search φ₂ = false := by decide

/-- The formula with no clauses is satisfiable, and the empty clause is not. -/
example : BruteForce.search [] = true := by decide

example : BruteForce.search [[]] = false := by decide

example : φ₂ ∉ SAT := fun h => absurd ((BruteForce.search_eq_true_iff φ₂).mpr h) (by decide)

/-! ### Orthogonal vectors -/

example : ([[true, false]], [[false, true]]) ∈ OV := by decide

example : ([[true, true]], [[true, false], [false, true]]) ∉ OV := by decide

/-- Missing coordinates count as `false`. -/
example : ([[true]], [[false, true]]) ∈ OV := by decide

/-- An empty side has no orthogonal pair. -/
example : (([], [[false]]) : List (List Bool) × List (List Bool)) ∉ OV := by decide

example : OV.dim ([[true, false, true]], [[false]]) = 3 := rfl

/-! ### The split-and-list reduction -/

/-- `x₀`: no variable in the first half, one in the second. -/
example : toOV [[(0, true)]] = ([[true]], [[true], [false]]) := by decide

example : toOV [[(0, true)]] ∈ OV := by decide

example : toOV φ₁ ∈ OV := by decide

example : toOV φ₂ ∉ OV := by decide

example : (toOV φ₁).1.length = 2 ∧ (toOV φ₁).2.length = 4 := by decide

/-- The reduction agrees with satisfiability. -/
example : φ₁ ∈ SAT := (toOV_mem_OV_iff φ₁).mp (by decide)

example (φ : CNF ℕ) : OV.dim (toOV φ) ≤ φ.length := OV.dim_toOV_le φ

/-! ### Non-vacuity -/

/-- Exhaustive search: every exponent set contains `1`. -/
example (k : ℕ) : DecidableInExpTime (KSAT k) encCNF CNF.numVars 1 :=
  KSAT_decidableInExpTime_one k

example : 0 ≤ satExponent 3 ∧ satExponent 3 ≤ 1 := ⟨satExponent_nonneg 3, satExponent_le_one 3⟩

example : satExponent 3 ≤ satExponent 4 := satExponent_mono (by norm_num)

/-- A trivial problem is decidable within linear time, in either form. -/
example : DecidableInTimeO (∅ : Set (CNF ℕ)) encCNF fun φ => (encCNF φ).length :=
  DecidableInTimeO.of_computableInO (.of_tidy (ComputableTidilyInO.const false)) (by simp) fun _ =>
    le_rfl

example : (∅ : Set (CNF ℕ)) ∈ DTIME encCNF id :=
  mem_DTIME_iff_decidableInTimeO.mpr
    (DecidableInTimeO.of_computableInO (.of_tidy (ComputableTidilyInO.const false)) (by simp)
      fun _ => le_rfl)

/-- The hypotheses in terms of the exponents. -/
example : ETH ↔ 0 < satExponent 3 := ETH_iff_satExponent_pos

example : SETH ↔ Filter.Tendsto satExponent Filter.atTop (nhds 1) := SETH_iff_tendsto

example : SETH → OVH := OVH_of_SETH

example (h : ¬DecidableInSubexpTime ThreeSAT encCNF List.length) : ETH :=
  ETH_of_not_decidableInSubexpTime_length h

/-! ### Axioms -/

/--
info: 'Cslib.Complexity.mem_DTIME_iff_decidableInTimeO' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_DTIME_iff_decidableInTimeO

/--
info: 'Cslib.Complexity.BruteForce.search_eq_true_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.BruteForce.search_eq_true_iff

/--
info: 'Cslib.Complexity.BruteForce.exists_computableInO_search' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.BruteForce.exists_computableInO_search

/--
info: 'Cslib.Complexity.KSAT_decidableInExpTime_one' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.KSAT_decidableInExpTime_one

/--
info: 'Cslib.Complexity.satExponent_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.satExponent_mono

/--
info: 'Cslib.Complexity.ETH_iff_satExponent_pos' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ETH_iff_satExponent_pos

/--
info: 'Cslib.Complexity.SETH_iff_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SETH_iff_tendsto

/--
info: 'Cslib.Complexity.ETH_of_not_decidableInSubexpTime_length' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ETH_of_not_decidableInSubexpTime_length

/--
info: 'Cslib.Complexity.toOV_mem_OV_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.toOV_mem_OV_iff

/--
info: 'Cslib.Complexity.exists_computableInO_toOV' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.exists_computableInO_toOV

/--
info: 'Cslib.Complexity.DecidableInTimeO.decidableInExpTime_SAT' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.DecidableInTimeO.decidableInExpTime_SAT

/--
info: 'Cslib.Complexity.OVH_of_SETH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.OVH_of_SETH

end ComplexityTests.FineGrained
