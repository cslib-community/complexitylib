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

Verifies the API surface, hash-family independence and multi-step eviction replay lemmas,
non-vacuity of `IsCuckooHashFamily` (`n_max ≤ 2`, `C_walk = 1`, `C_reh = 0`) and `SubroutineDS`,
and end-to-end expected-amortized execution (`cuckoo_seq_expected_amortized`) of
`Cslib.Algorithms.WordRAM.Dictionary.CuckooHashing`.
-/

@[expose] public section

namespace ComplexityTests.WordRAMCuckooHashing

open Cslib Cslib.WordRAM Cslib.WordRAM.Randomized
open Cslib.Algorithms.Lean
open Cslib.Algorithms.WordRAM.Dictionary.CuckooHashing
open scoped ENNReal

/-! ## 1. Parameter scale, k-wise independence, and multi-key eviction chain checks -/

example : tableBits 2 = 3 := by decide
example : tableSize 2 = 8 := by decide
example : maxEvictions 2 = 18 := by decide
example (n_max : ℕ) : max (4 * n_max) 4 ≤ tableSize n_max := four_mul_max_le_tableSize n_max
example (U M : ℕ) : Probability.IsKWiseIndependentHash 7 (evalHash1 (U := U) (M := M)) :=
  isKWiseIndependentHash_evalHash1 U M
example (U M : ℕ) : Probability.IsKWiseIndependentHash 7 (evalHash2 (U := U) (M := M)) :=
  isKWiseIndependentHash_evalHash2 U M

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

/-! ## 2. Concrete non-vacuous `SubroutineDS` instantiation (`w = 64`, `n_max = 2`, `U = 16`) -/

/-- Concrete unconditional `IsCuckooHashFamily` instance at `n_max = 2`, `U = 16` with
`C_walk = 1`, `C_reh = 0`. -/
theorem instCuckooHashFamily_16_2 :
    IsCuckooHashFamily 16 2 (tableBits 2) (maxEvictions 2) 1 0 :=
  isCuckooHashFamily_le_two 16 (le_refl 2) (by decide)

theorem hw_64_16_2 : 2 * Probability.trinomialDeg 16 (tableBits 2) ≤ 64 := by
  have hle := Probability.trinomialDeg_le_three_mul 16 (tableBits 2)
  have hval : 3 * max (Nat.clog 2 (max 16 2)) (max (tableBits 2) 1) = 12 := by decide
  omega

/-- Concrete `Basis.exact` randomized `SubroutineDS` certificate for cuckoo hashing at `w = 64`,
`base = 0`, `n_max = 2`, `U = 16`, `V = 256`. -/
noncomputable def instSubroutineDS :
    Randomized.SubroutineDS cuckooCode (Dictionary.spec 16 256 2)
      64 0 ![2, 16] (Dictionary.empty 16) :=
  subroutineDS 64 0 2 16 256 1 0 instCuckooHashFamily_16_2
    hw_64_16_2 (by decide) (by decide) (by decide) (by decide)

/-- Concrete `Basis.standard` randomized `SubroutineDS` certificate for cuckoo hashing. -/
noncomputable def instSubroutineDSStandard :
    Randomized.SubroutineDS cuckooCode.toStandard (Dictionary.spec 16 256 2)
      64 0 ![2, 16] (Dictionary.empty 16) :=
  subroutineDSStandard 64 0 2 16 256 1 0 instCuckooHashFamily_16_2
    hw_64_16_2 (by decide) (by decide) (by decide) (by decide)

/-- Sample valid operation sequence exercising multi-key insertion (`⟨3, _⟩` and `⟨11, _⟩`),
hit lookups, in-place value overwrite at full capacity `n_max = 2`, and absent-key miss lookup. -/
def sampleOps : List (Dictionary.Op 16) :=
  [ .insert ⟨3, by decide⟩ 42,
    .insert ⟨11, by decide⟩ 17,
    .get ⟨3, by decide⟩,
    .get ⟨11, by decide⟩,
    .insert ⟨3, by decide⟩ 99,
    .get ⟨3, by decide⟩,
    .get ⟨7, by decide⟩ ]

theorem sampleOps_validHistory :
    (Dictionary.spec 16 256 2).ValidHistory (Dictionary.empty 16) sampleOps := by
  refine ⟨⟨Or.inl ?_, by decide⟩, ⟨Or.inl ?_, by decide⟩,
    trivial, trivial, ⟨Or.inr ?_, by decide⟩, trivial, trivial, trivial⟩
  · simp [Dictionary.dom_empty]
  · simp [Dictionary.spec, Dictionary.dom_insert, Dictionary.dom_empty]
  · simp [Dictionary.spec]

/-- Concrete end-to-end expected-amortized execution of `sampleOps` from `Data.init` with runtime
parameters `(n_max, U) = (2, 16)` in registers `3` and `4`. -/
theorem inst_cuckoo_seq_expected_amortized :
    let x₀ : Data 19 := ((Data.init [] : Data 19).set 3 2).set 4 16
    let C := instSubroutineDS
    ∃ (ν₀ ν_final : PMF (Seed 16 (tableBits 2) × Data 19)) (T_ops : ℝ≥0∞),
      ExecCodeDist 64 cuckooCode.initFresh x₀ (ν₀.map Prod.snd) C.initTime ∧
      C.ExecSteps (Dictionary.empty 16) sampleOps ν₀ ν_final T_ops ∧
      (∀ θ, (ν_final.map Prod.fst) θ ≤ 2 * seedLaw 16 (tableBits 2) θ) ∧
      (∀ p ∈ ν_final.support,
        Rep 64 0 2 16 256 ((Dictionary.spec 16 256 2).run (Dictionary.empty 16) sampleOps).1
          p.2) ∧
      C.initTime + T_ops ≤
        C.initTime +
          ((Dictionary.spec 16 256 2).totalCost (charge 2 16 1 0)
            (Dictionary.empty 16) sampleOps : ℝ≥0∞) := by
  intro x₀ C
  have hx₀ : x₀.Bounded 64 := by
    refine ((Data.Bounded.init (by simp [InputFits])).set (by decide)).set (by decide)
  exact cuckoo_seq_expected_amortized 64 0 2 16 256 1 0 instCuckooHashFamily_16_2
    hw_64_16_2 (by decide) (by decide) (by decide) (by decide)
    sampleOps hx₀ rfl rfl rfl (fun a _ => by simp +decide [x₀, Data.init, Data.set])
    sampleOps_validHistory

end ComplexityTests.WordRAMCuckooHashing
