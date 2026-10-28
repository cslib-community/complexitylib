/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Computability.Complexity.Classes.SharpP.Lowness
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

@[expose] public section

namespace Cslib.Complexity.SharpPLownessTests

open Turing.MultiTapeTM

/-! ### Nonvacuous concrete oracle in `UP ∩ coUP`, `FewP`, and `SPP` -/

/-- A nontrivial oracle language accepting bit strings whose first bit is `true`. -/
def headTrue : Set (List Bool) := {w | w.headD false = true}

theorem true_singleton_mem_headTrue : [true] ∈ headTrue := rfl

theorem nil_notMem_headTrue : [] ∉ headTrue := by simp [headTrue]

theorem headTrue_mem_P : headTrue ∈ P encBits :=
  ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩

theorem headTrue_mem_UP : headTrue ∈ UP encBits :=
  P_subset_UP headTrue_mem_P

theorem headTrue_mem_coUP : headTrue ∈ coUP encBits :=
  P_subset_coUP headTrue_mem_P

theorem headTrue_mem_FewP : headTrue ∈ FewP encBits :=
  UP_subset_FewP headTrue_mem_UP

theorem headTrue_mem_SPP : headTrue ∈ SPP encBits :=
  UP_subset_SPP headTrue_mem_UP

/-! ### Concrete `#P` and `GapP` precomposition with `FP^(UP ∩ coUP)` -/

theorem oracleId_computableInPolyTimeWithOracle :
    ComputableInPolyTimeWithOracle headTrue (fun w : List Bool => w) encBits encBits :=
  ComputableInPolyTime.id'.computableInPolyTimeWithOracle headTrue

example : ((fun _ : List Bool => (1 : ℕ)) ∘ fun w : List Bool => w) ∈ SharpP encBits :=
  SharpP.comp_mem_of_computableInPolyTimeWithOracle headTrue_mem_UP headTrue_mem_coUP
    oracleId_computableInPolyTimeWithOracle SharpP.one_mem

example : ((fun _ : List Bool => (1 : ℤ)) ∘ fun w : List Bool => w) ∈ GapP encBits :=
  GapP.comp_mem_of_computableInPolyTimeWithOracle headTrue_mem_UP headTrue_mem_coUP
    oracleId_computableInPolyTimeWithOracle GapP.one_mem

/-! ### Concrete `#P`, `UP`, `FewP`, `US`, `SBP`, `SPP`, and `ModP` lowness checks -/

open Classical in
example : (fun q => if q ∈ headTrue then 1 else 0) + (fun _ => 2) ∈ SharpP encBits :=
  SharpPWithOracle_eq_SharpP_of_mem_UP_of_mem_coUP headTrue_mem_UP headTrue_mem_coUP encBits ▸
    SharpPWithOracle.add_mem (indicator_mem_SharpPWithOracle_self headTrue)
      (SharpPWithOracle.natCast_mem 2)

open Classical in
example : (fun q => if q ∈ headTrue then 1 else 0) * (fun _ => 2) ∈ SharpP encBits :=
  (SharpPWithOracle_eq_SharpP_iff.mpr ⟨headTrue_mem_UP, headTrue_mem_coUP⟩) ▸
    SharpPWithOracle.mul_mem (indicator_mem_SharpPWithOracle_self headTrue)
      (SharpPWithOracle.natCast_mem 2)

example : UPWithOracle headTrue encBits = UP encBits ∧
    coUPWithOracle headTrue encBits = coUP encBits ∧
    UPWithOracle headTrue encBits ∩ coUPWithOracle headTrue encBits =
      UP encBits ∩ coUP encBits ∧
    FewPWithOracle headTrue encBits = FewP encBits ∧
    USWithOracle headTrue encBits = US encBits ∧
    SBPWithFixedTarget headTrue encBits = SBP encBits :=
  ⟨UPWithOracle_eq_UP_of_mem_UP_of_mem_coUP headTrue_mem_UP headTrue_mem_coUP encBits,
    coUPWithOracle_eq_coUP_of_mem_UP_of_mem_coUP headTrue_mem_UP headTrue_mem_coUP encBits,
    UPWithOracle_inter_coUPWithOracle_eq_iff.mpr ⟨headTrue_mem_UP, headTrue_mem_coUP⟩,
    FewPWithOracle_eq_FewP_of_mem_UP_of_mem_coUP headTrue_mem_UP headTrue_mem_coUP encBits,
    USWithOracle_eq_US_of_mem_UP_of_mem_coUP headTrue_mem_UP headTrue_mem_coUP encBits,
    SBPWithFixedTarget_eq_SBP_of_mem_UP_of_mem_coUP headTrue_mem_UP headTrue_mem_coUP encBits⟩

open Classical in
example : (fun q => if q ∈ headTrue then (1 : ℤ) else 0) ∈ GapP encBits ∧
    SPPWithOracle headTrue encBits = SPP encBits ∧
    ParityPWithOracle headTrue encBits = ParityP encBits :=
  ⟨(GapPWithOracle_eq_GapP_iff.mpr headTrue_mem_SPP) ▸
      indicator_mem_GapPWithOracle_self headTrue,
    SPPWithOracle_eq_SPP_iff.mpr headTrue_mem_SPP,
    ParityPWithOracle_eq_ParityP_of_mem_SPP headTrue_mem_SPP encBits⟩

example : ModPWithOracle 5 headTrue encBits = ModP 5 encBits ∧
    ParityPWithOracle headTrue encBits = ParityP encBits :=
  ⟨ModPWithOracle_eq_ModP_of_mem_FewP (by decide) headTrue_mem_FewP encBits,
    ParityPWithOracle_eq_ParityP_of_mem_FewP headTrue_mem_FewP encBits⟩

open Classical in
example : ∃ f ∈ SharpPWithOracle headTrue encBits,
    ∀ q, (f q : ℤ) % 3 = (if q ∈ headTrue then (1 : ℤ) else 0) % 3 :=
  GapPWithOracle.exists_SharpPWithOracle_emod (indicator_mem_GapPWithOracle_self headTrue)
    (by decide)

open Classical in
example : headTrue ∈ ModP 3 encBits :=
  ModPWithOracle_eq_ModP_of_mem_SPP (k := 3) (by decide) headTrue_mem_SPP encBits ▸
    (mem_ModPWithOracle_iff_exists_GapPWithOracle (by decide)).mpr
      ⟨fun q => if q ∈ headTrue then (1 : ℤ) else 0,
        indicator_mem_GapPWithOracle_self headTrue,
        fun q => by by_cases hq : q ∈ headTrue <;> simp [hq]⟩

open Classical in
example : headTrueᶜ ∈ coModP 3 encBits :=
  coModPWithOracle_eq_coModP_of_mem_SPP (k := 3) (by decide) headTrue_mem_SPP encBits ▸
    (mem_coModPWithOracle_iff_exists_GapPWithOracle (by decide)).mpr
      ⟨fun q => if q ∈ headTrue then (1 : ℤ) else 0,
        indicator_mem_GapPWithOracle_self headTrue,
        fun q => by by_cases hq : q ∈ headTrue <;> simp [hq]⟩

end Cslib.Complexity.SharpPLownessTests
