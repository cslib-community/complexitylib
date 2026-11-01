/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.WordRAM.Dictionary.CuckooHashing

/-!
# Pagh–Rodler Cuckoo Hashing on the Randomized Word RAM — Test Suite

Verifies the API surface, multi-step eviction replay lemmas, unconditional
`isCuckooHashFamily_tableBits` (`C_walk = 3`, `C_reh = 4` for all `n_max : ℕ` whenever
`U ≤ max n_max 4 ^ c_exp`), $O_{c_{\exp}}(1)$ operation charges (`expectedOpCharge c_exp`),
$O_{c_{\exp}}(n_{\max} + 1)$ space (`space_le`), `SubroutineDS`, and end-to-end expected-amortized
execution (`cuckoo_seq_expected_amortized`) of
`Cslib.Algorithms.WordRAM.Dictionary.CuckooHashing`.
-/

@[expose] public section

namespace ComplexityTests.WordRAMCuckooHashing

open Cslib Cslib.WordRAM Cslib.WordRAM.Randomized
open Cslib.Algorithms.Lean
open Cslib.Algorithms.WordRAM.Dictionary.CuckooHashing
open scoped ENNReal

/-! ## 1. Parameter scale, unconditional hash-family certificate, and eviction chain checks -/

example : tableBits 2 = 7 := by decide
example : tableSize 2 = 128 := by decide
example : maxEvictions 2 = 18 := by decide
example (n_max : ℕ) : max (4 * n_max) 4 ≤ tableSize n_max := four_mul_max_le_tableSize n_max
example (n_max : ℕ) : 32 * max n_max 4 ≤ tableSize n_max := thirtyTwo_mul_max_le_tableSize n_max
example (c_exp n_max : ℕ) : space c_exp n_max ≤ spaceFactor c_exp * (n_max + 1) :=
  space_le c_exp n_max
example {c_exp U n_max : ℕ} (hU : U ≤ max n_max 4 ^ c_exp) :
    IsCuckooHashFamily c_exp U n_max (tableBits n_max) (maxEvictions n_max) 3 4 :=
  isCuckooHashFamily_tableBits hU
example {c_exp n_max U : ℕ} (hU : U ≤ max n_max 4 ^ c_exp)
    (s : Dictionary.State U) (o : Dictionary.Op U) :
    charge c_exp n_max U 3 4 s o ≤ expectedOpCharge c_exp s o :=
  charge_le_expectedOpCharge hU s o

/-- Hash functions on `U = 16`, `m = 16` (`n_max = 4`) where keys `1, 2, 3` collide at bucket `0`
in `T₁` and keys `1, 2` collide at bucket `5` in `T₂`, forcing a multi-step eviction chain across
`T₁` and `T₂` on sequential insertion. -/
def testH1 (u : Fin 16) : Fin 16 :=
  if u.val = 1 ∨ u.val = 2 ∨ u.val = 3 then ⟨0, by decide⟩ else ⟨u.val, u.isLt⟩

def testH2 (u : Fin 16) : Fin 16 :=
  if u.val = 1 then ⟨5, by decide⟩
  else if u.val = 2 then ⟨5, by decide⟩
  else ⟨(u.val + 7) % 16, Nat.mod_lt _ (by decide)⟩

/-- Inserting `[1, 2, 3]` under `(testH1, testH2)` triggers displacement from `T₁[0]` to `T₂[5]`
and back to `T₁[0]`/`T₂`, and `lookupEntry` recovers every key with its insertion index. -/
example :
    (pureReplay testH1 testH2 (maxEvictions 4)
      [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]).map
      (fun tbl =>
        (lookupEntry testH1 testH2 tbl ⟨1, by decide⟩,
         lookupEntry testH1 testH2 tbl ⟨2, by decide⟩,
         lookupEntry testH1 testH2 tbl ⟨3, by decide⟩,
         lookupEntry testH1 testH2 tbl ⟨4, by decide⟩)) =
    some (some ⟨⟨1, by decide⟩, 0⟩, some ⟨⟨2, by decide⟩, 1⟩,
          some ⟨⟨3, by decide⟩, 2⟩, none) :=
  rfl

/-! ## 2. Concrete non-vacuous `SubroutineDS` instantiation (`w = 64`, `c_exp = 2`, `n_max = 10`) -/

/-- Concrete unconditional `IsCuckooHashFamily` instance at `c_exp = 2`, `n_max = 10`, `U = 16`
with `C_walk = 3`, `C_reh = 4`. -/
theorem instCuckooHashFamily_2_16_10 :
    IsCuckooHashFamily 2 16 10 (tableBits 10) (maxEvictions 10) 3 4 :=
  isCuckooHashFamily_tableBits (by decide)

theorem hw_64_16_10 : 2 * Probability.trinomialDeg 16 (tableBits 10) ≤ 64 := by
  have hle := Probability.trinomialDeg_le_three_mul 16 (tableBits 10)
  have hval : 3 * max (Nat.clog 2 (max 16 2)) (max (tableBits 10) 1) = 27 := by decide
  omega

theorem hfit_end_64_2_10 : Fits 64 (0 + space 2 10) := by
  have hle := space_le 2 10
  have hfac : spaceFactor 2 * (10 + 1) < 2 ^ 64 := by decide
  exact lt_of_le_of_lt (by omega) hfac

/-- Concrete `Basis.exact` randomized `SubroutineDS` certificate for cuckoo hashing at `w = 64`,
`base = 0`, `n_max = 10`, `U = 16`, `V = 256` for any exponent `c_exp` with `16 ≤ 10 ^ c_exp`
(e.g. `c_exp = 2`). -/
noncomputable def instSubroutineDS (c_exp : ℕ) (hU : 16 ≤ max 10 4 ^ c_exp)
    (hfit_end : Fits 64 (0 + space c_exp 10)) :
    Randomized.SubroutineDS (cuckooCode c_exp 10) (Dictionary.spec 16 256 10)
      64 0 ![10, 16] (Dictionary.empty 16) :=
  subroutineDS 64 0 c_exp 10 16 256 hU
    hw_64_16_10 hfit_end (by decide) (by decide) (by decide)

/-- Concrete `Basis.standard` randomized `SubroutineDS` certificate for cuckoo hashing at
`c_exp = 2`, `n_max = 10`, `U = 16`, `V = 256`. -/
noncomputable def instSubroutineDSStandard :
    Randomized.SubroutineDS (cuckooCode 2 10).toStandard (Dictionary.spec 16 256 10)
      64 0 ![10, 16] (Dictionary.empty 16) :=
  subroutineDSStandard 64 0 2 10 16 256 (by decide)
    hw_64_16_10 hfit_end_64_2_10 (by decide) (by decide) (by decide)

/-- Sample valid operation sequence exercising multi-key insertion (`⟨3, _⟩` and `⟨11, _⟩`),
hit lookups, in-place value overwrite, and absent-key miss lookup at capacity `n_max = 10`. -/
def sampleOps : List (Dictionary.Op 16) :=
  [ .insert ⟨3, by decide⟩ 42,
    .insert ⟨11, by decide⟩ 17,
    .get ⟨3, by decide⟩,
    .get ⟨11, by decide⟩,
    .insert ⟨3, by decide⟩ 99,
    .get ⟨3, by decide⟩,
    .get ⟨7, by decide⟩ ]

theorem sampleOps_validHistory :
    (Dictionary.spec 16 256 10).ValidHistory (Dictionary.empty 16) sampleOps := by
  refine ⟨⟨Or.inl ?_, by decide⟩, ⟨Or.inl ?_, by decide⟩,
    trivial, trivial, ⟨Or.inr ?_, by decide⟩, trivial, trivial, trivial⟩
  · simp [Dictionary.dom_empty]
  · simp [Dictionary.dom_insert, Dictionary.dom_empty]
  · simp

/-- Concrete end-to-end expected-amortized execution of `sampleOps` from `Data.init` with runtime
parameters `(n_max, U) = (10, 16)` in registers `3` and `4`. -/
theorem inst_cuckoo_seq_expected_amortized (c_exp : ℕ)
    (hU : 16 ≤ max 10 4 ^ c_exp) (hfit_end : Fits 64 (0 + space c_exp 10)) :
    let x₀ : Data 19 := ((Data.init [] : Data 19).set 3 10).set 4 16
    let C := instSubroutineDS c_exp hU hfit_end
    ∃ (ν₀ ν_final : PMF (Seed c_exp 10 16 (tableBits 10) × Data 19)) (T_ops : ℝ≥0∞),
      ExecCodeDist 64 (cuckooCode c_exp 10).initFresh x₀ (ν₀.map Prod.snd) C.initTime ∧
      C.ExecStepsOfFn (Dictionary.empty 16) sampleOps ν₀ ν_final T_ops ∧
      (∀ θ, (ν_final.map Prod.fst) θ ≤ 2 * seedLaw c_exp 10 16 (tableBits 10) θ) ∧
      (∀ p ∈ ν_final.support,
        Rep 64 0 c_exp 10 16 256
          ((Dictionary.spec 16 256 10).run (Dictionary.empty 16) sampleOps).1 p.2) ∧
      C.initTime + T_ops ≤
        C.initTime +
          ((Dictionary.spec 16 256 10).totalCost (expectedOpCharge c_exp)
            (Dictionary.empty 16) sampleOps : ℝ≥0∞) := by
  intro x₀ C
  have hx₀ : x₀.Bounded 64 := by
    refine ((Data.Bounded.init (by simp [InputFits])).set (by decide)).set (by decide)
  exact cuckoo_seq_expected_amortized 64 0 c_exp 10 16 256 hU
    hw_64_16_10 hfit_end (by decide) (by decide) (by decide)
    sampleOps hx₀ rfl rfl rfl (fun a _ => by simp +decide [x₀, Data.init, Data.set])
    sampleOps_validHistory

/-- Non-vacuous specialization of `inst_cuckoo_seq_expected_amortized` at `c_exp = 2`: all
hypotheses (`16 ≤ max 10 4 ^ 2` and `Fits 64 (0 + space 2 10)`) hold unconditionally. -/
theorem inst_cuckoo_seq_expected_amortized_nonvacuous :
    ∃ c_exp : ℕ, 16 ≤ max 10 4 ^ c_exp ∧ Fits 64 (0 + space c_exp 10) :=
  ⟨2, by decide, hfit_end_64_2_10⟩

end ComplexityTests.WordRAMCuckooHashing
