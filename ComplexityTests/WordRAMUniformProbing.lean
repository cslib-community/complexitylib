/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.UniformProbing
public import Complexity.DataStructure.Dictionary.WordRAM.UniformProbing

/-!
# Tests for Uniform Probing (`Lean.UniformProbing` and `WordRAM.Dictionary.UniformProbing`)

This test file verifies:
1. Concrete open-addressed probing behavior (`tableGet`, `tableInsert`, `runTable`, `probeCount`)
   under primary-slot collisions and in-place updates, together with the textbook expected-probe
   bounds (`≤ m / (m - n) ≤ 2` for unsuccessful lookups by [CLRS2009], third edition, Theorem 11.6
   and Corollary 11.7, pp. 274–276, and for fixed-key successful lookups via the insertion-cost
   identity and intermediate bound from the proof of Theorem 11.8, p. 276) and lazy random-oracle
   equivalence in `Cslib.DataStructure.Dictionary.UniformProbing`.
2. Concrete parameter values, full-cycle stride permutations, pathwise Word-RAM execution
   (`opCode_execWithin`), composable `StateTransitionImpl` certificates over `Basis.exact` and
   `Basis.standard`, end-to-end multi-operation expected complexity (`seq_expected_amortized`)
   charging $O_{c_{\exp}}(1)$ per operation (`expectedOpCharge c_exp`), linear space bound
   (`space_le`), and expected-step transfer (`expect_idealProbeSteps_le`) in
   `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing`.
-/

public section

namespace ComplexityTests.WordRAMUniformProbing

open Cslib
open Cslib.DataStructure Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.UniformProbing
open Cslib.DataStructure.Dictionary.WordRAM.UniformProbing
open Cslib.Probability
open Cslib.WordRAM
open scoped ENNReal

/-! ## Part 1: Pure Textbook Uniform Probing (`Cslib.DataStructure.Dictionary.UniformProbing`) -/

/-- A concrete permutation family on `U = 4` keys and `m = 4` slots where keys `0` and `1` both
start at slot `0`, and key `1` swaps slots `1` and `3`. -/
def testPermFamily : Fin 4 → Equiv.Perm (Fin 4)
  | ⟨0, _⟩ => Equiv.refl (Fin 4)
  | ⟨1, _⟩ => Equiv.swap (1 : Fin 4) (3 : Fin 4)
  | _ => Equiv.refl (Fin 4)

/-- Concrete trace of `tableInsert`, `tableGet`, and `probeCount` under a primary-slot collision
and an in-place overwrite at full capacity `n_max = 2`. -/
theorem test_pure_collision_and_overwrite :
    let hm : 0 < 4 := by decide
    let T₀ := emptyTable 4 4
    let u₀ : Fin 4 := ⟨0, by decide⟩
    let u₁ : Fin 4 := ⟨1, by decide⟩
    let u₂ : Fin 4 := ⟨2, by decide⟩
    let T₁ := tableInsert hm testPermFamily T₀ u₀ 10
    let T₂ := tableInsert hm testPermFamily T₁ u₁ 20
    let T₃ := tableInsert hm testPermFamily T₂ u₁ 99
    -- Initial empty table lookup misses in 1 probe:
    tableGet hm testPermFamily T₀ u₀ = none ∧
    probeCount T₀ u₀ (testPermFamily u₀) = 1 ∧
    -- First insertion lands at primary slot 0 in 1 probe:
    T₁ ⟨0, by decide⟩ = some (u₀, 10) ∧
    probeCount T₁ u₀ (testPermFamily u₀) = 1 ∧
    -- Colliding key u₁ probes slot 0 (occupied by u₀) and lands at testPermFamily u₁ 1 = 3:
    probeCount T₁ u₁ (testPermFamily u₁) = 2 ∧
    T₂ ⟨3, by decide⟩ = some (u₁, 20) ∧
    tableGet hm testPermFamily T₂ u₀ = some 10 ∧
    tableGet hm testPermFamily T₂ u₁ = some 20 ∧
    tableGet hm testPermFamily T₂ u₂ = none ∧
    -- In-place overwrite of u₁ updates slot 3 to 99 and preserves probeCount = 2:
    T₃ ⟨3, by decide⟩ = some (u₁, 99) ∧
    tableGet hm testPermFamily T₃ u₁ = some 99 ∧
    probeCount T₃ u₁ (testPermFamily u₁) = 2 := by
  decide

/-- Concrete instantiation of the textbook expected-probe bounds (`≤ 2`) for both unsuccessful
lookups (`[CLRS2009]`, third edition, Theorem 11.6 / Corollary 11.7, pp. 274–276) and fixed-key
successful lookups (via the insertion-cost identity and intermediate bound from the proof of
Theorem 11.8, p. 276) on a table of `m = 8` slots with `U = 16` keys and capacity `n_max = 4`. -/
theorem test_expected_probes_le_two
    (ops₁ ops₂ : List (Dictionary.Op 16))
    (u u_abs : Fin 16) (v₀ : ℕ)
    (hvh : (Dictionary.spec 16 100 4).ValidHistory (Dictionary.empty 16)
      (ops₁ ++ (.insert u v₀ :: ops₂)))
    (hu₁ : ((Dictionary.spec 16 100 4).run (Dictionary.empty 16) ops₁).1 u = none)
    (habs :
      ((Dictionary.spec 16 100 4).run (Dictionary.empty 16)
        (ops₁ ++ (.insert u v₀ :: ops₂))).1 u_abs = none) :
    let hm : 0 < 8 := by decide
    let ops := ops₁ ++ (.insert u v₀ :: ops₂)
    let μ := PMF.uniformOfFintype (Fin 16 → Equiv.Perm (Fin 8))
    (∑' π : Fin 16 → Equiv.Perm (Fin 8),
      μ π * (probeCount (runTable hm π ops) u (π u) : ℝ≥0∞)) ≤ 2 ∧
    (∑' π : Fin 16 → Equiv.Perm (Fin 8),
      μ π * (probeCount (runTable hm π ops) u_abs (π u_abs) : ℝ≥0∞)) ≤ 2 := by
  have hm : 0 < 8 := by decide
  have h2m : 2 * 4 ≤ 8 := by decide
  exact ⟨expect_probeCount_of_mem_dom_le_two hm h2m hvh hu₁,
    expect_probeCount_of_eq_none_le_two hm h2m hvh habs⟩

/-- Concrete instantiation of the lazy random-oracle equivalence for uniform probing on `U = 16`
keys and `m = 8` slots. -/
theorem test_lazy_random_oracle_equiv
    (prog : OracleComp (fun _ : Fin 16 => Equiv.Perm (Fin 8)) Bool) :
    (do
      let π ← PMF.uniformOfFintype (Fin 16 → Equiv.Perm (Fin 8))
      OracleComp.interpret (fun u => PMF.pure (π u)) prog) =
      ((OracleComp.interpret
        (Cslib.RandomOracle.answer (fun _ : Fin 16 => PMF.uniformOfFintype (Equiv.Perm (Fin 8))))
        prog).run (fun _ => none)).map Prod.fst :=
  uniform_interpret_eq_lazy_perm prog

/-! ## Part 2: Word-RAM Realization (`Cslib.DataStructure.Dictionary.WordRAM.UniformProbing`) -/

/-- Verify concrete table dimension parameters at `c_exp = 2`, `n_max = 2`. -/
theorem test_wordram_params :
    bucketBits 2 = 7 ∧
    numBuckets 2 = 128 ∧
    numChars 2 = 4 ∧
    tupleLen 2 = 32 ∧
    charBits 2 = 1 ∧
    singleTabSpace 2 2 = 320 ∧
    slotOffset 2 2 = 640 ∧
    space 2 2 = 1024 ∧
    space 2 2 ≤ spaceFactor 2 * (2 + 1) ∧
    setupSteps 2 2 = 3230 ∧
    hashEvalSteps 2 = 3811 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    space_le 2 2, by decide, by decide⟩

/-- For every seed `θ : Seed 2 2` and key `u : Fin 16`, `probePerm θ u` is a bijection on the `128`
table slots, and its `0`-th probe slot is `primaryHash θ u`. -/
theorem test_wordram_probePerm_bijective (θ : Seed 2 2) (u : Fin 16) :
    Function.Bijective (probePerm θ u) ∧
    probePerm θ u ⟨0, by decide⟩ = primaryHash θ u :=
  ⟨(probePerm θ u).bijective, probePerm_zero θ u⟩

/-- Concrete admissible operation sequence on `U = 16`, `V = 100`, `n_max = 2` exercising fresh
insertions up to full capacity `n_max = 2`, an in-place overwrite at full capacity, successful
lookups, and an unsuccessful lookup of an absent key. -/
def testOps : List (Dictionary.Op 16) :=
  [ .insert ⟨3, by decide⟩ 42,
    .insert ⟨11, by decide⟩ 77,
    .insert ⟨3, by decide⟩ 88,
    .get ⟨3, by decide⟩,
    .get ⟨11, by decide⟩,
    .get ⟨5, by decide⟩ ]

theorem testOps_validHistory :
    (Dictionary.spec 16 100 2).ValidHistory (Dictionary.empty 16) testOps := by
  dsimp only [testOps, Cslib.DataStructure.StateTransitionSpec.ValidHistory, Dictionary.spec]
  decide

/-- Concrete instantiation of the `Basis.exact` and `Basis.standard` `StateTransitionImpl`
certificates
and end-to-end `seq_expected_amortized` bound at `w = 64`, `base = 16`, `c_exp = 2`, `U = 16`,
`V = 100`, `n_max = 2`. -/
theorem test_wordram_seq_expected_amortized :
    have hS : Fits 64 (16 + space 2 2) := by decide
    have hU_fit : ∀ u : Fin 16, Fits 64 u.val := fun u => by fin_cases u <;> decide
    have hV : Fits 64 100 := by decide
    have hU : 16 ≤ max 2 4 ^ 2 := by decide
    let x₀ : Data 16 := (⟨fun _ => 0, fun _ => 0⟩ : Data 16).set regV 16
    ∃ (ν₀ ν_final : PMF (Seed 2 2 × Data 16)) (T_ops : ℝ≥0∞),
      ExecCodeDist 64 (subroutineCode 2 2).initFresh x₀ (ν₀.map Prod.snd)
        (impl (V := 100) hS hU_fit hV hU).initTime ∧
      (impl (V := 100) hS hU_fit hV hU).ExecStepsOfFn (Dictionary.empty 16) testOps ν₀
        ν_final T_ops ∧
      (∀ θ, (ν_final.map Prod.fst) θ ≤ seedLaw 2 2 θ) ∧
      (∀ p ∈ ν_final.support,
        Rep 64 16 2 16 100 2 p.1
          ((Dictionary.spec 16 100 2).run (Dictionary.empty 16) testOps).1 p.2) ∧
      (impl (V := 100) hS hU_fit hV hU).initTime + T_ops ≤
        (3 + setupSteps 2 2 : ℝ≥0∞) +
          ((Dictionary.spec 16 100 2).totalCost (fun _ _ => expectedOpCharge 2)
            (Dictionary.empty 16) testOps : ℝ≥0∞) := by
  have hS : Fits 64 (16 + space 2 2) := by decide
  have hU_fit : ∀ u : Fin 16, Fits 64 u.val := fun u => by fin_cases u <;> decide
  have hV : Fits 64 100 := by decide
  have hU : 16 ≤ max 2 4 ^ 2 := by decide
  let x₀ : Data 16 := (⟨fun _ => 0, fun _ => 0⟩ : Data 16).set regV 16
  have hx₀ : x₀.Bounded 64 := by
    refine ⟨fun i => ?_, fun a => ?_⟩
    · fin_cases i <;> decide
    · change Fits 64 0
      exact fits_zero 64
  have hfr : x₀.regs regV = 16 := rfl
  have hz : ∀ a ∈ (Block.mk 16 (space 2 2)).footprint, x₀.mem a = 0 := fun _ _ => rfl
  exact seq_expected_amortized (V := 100) hS hU_fit hV hU testOps hx₀ hfr hz testOps_validHistory

/-- Concrete instantiation of the standard-basis (`Basis.standard`) certificate and ideal
uniform-probing expected-step bound (`≤ 3845` steps) at `c_exp = 2`, `U = 16`, `n_max = 2`. -/
theorem test_wordram_standard_and_collision_bounds :
    have hS : Fits 64 (16 + space 2 2) := by decide
    have hU_fit : ∀ u : Fin 16, Fits 64 u.val := fun u => by fin_cases u <;> decide
    have hV : Fits 64 100 := by decide
    have hU : 16 ≤ max 2 4 ^ 2 := by decide
    (implStandard (V := 100) hS hU_fit hV hU).space = 1024 ∧
    ∀ (T : Fin (numBuckets 2) → Option (Fin 16 × ℕ)) (u : Fin 16),
      (otherOccupiedSlots T u).card ≤ 2 →
      (∑' π : Equiv.Perm (Fin (numBuckets 2)),
        (PMF.uniformOfFintype (Equiv.Perm (Fin (numBuckets 2)))) π *
          ((13 * probeCount T u π + hashEvalSteps 2 + 8 : ℕ) : ℝ≥0∞)) ≤ 3845 := by
  refine ⟨by decide, fun T u hcard => ?_⟩
  have h := expect_idealProbeSteps_le (c_exp := 2) T u hcard
  have heq : (hashEvalSteps 2 + 34 : ℝ≥0∞) = 3845 := by
    have hc : hashEvalSteps 2 = 3811 := by decide
    rw [hc]
    norm_num
  rwa [heq] at h

end ComplexityTests.WordRAMUniformProbing
