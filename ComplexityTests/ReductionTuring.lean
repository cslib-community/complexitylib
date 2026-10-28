/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Reduction.Turing

/-!
# Polynomial-time Turing reduction unit tests

Tests for `PolyTimeTuringReducible` and hardness transfer:
* Prefixing bits gives many-one and Turing reductions.
* Reflexivity and complementation.
* NP-hardness transfer applied to `SAT`.
-/

open Cslib.Complexity
open Turing.MultiTapeTM

namespace ComplexityTests.ReductionTuring

variable (B : Set (List Bool))

/-- Prefixing `true` is a many-one reduction, hence a Turing reduction. -/
example : PolyTimeTuringReducible encBits encBits {w | true :: w ∈ B} B :=
  (show PolyTimeReducible encBits encBits {w | true :: w ∈ B} B from
    ⟨fun w => true :: w, by fun_prop, fun _ => Iff.rfl⟩).polyTimeTuringReducible

/-- Prefixing `false` is a many-one reduction, hence a Turing reduction. -/
example : PolyTimeTuringReducible encBits encBits {w | false :: w ∈ B} B :=
  (show PolyTimeReducible encBits encBits {w | false :: w ∈ B} B from
    ⟨fun w => false :: w, by fun_prop, fun _ => Iff.rfl⟩).polyTimeTuringReducible

/-- Every language Turing-reduces to itself. -/
example : PolyTimeTuringReducible encBits encBits B B :=
  PolyTimeTuringReducible.refl encBits B

/-- The complement `Bᶜ` Turing-reduces to `B`. -/
example : PolyTimeTuringReducible encBits encBits Bᶜ B :=
  PolyTimeTuringReducible.compl_self encBits B

/-- Composing a reduction with membership in `P` transfers membership. -/
example (hB : B ∈ P encBits) : {w | true :: w ∈ B} ∈ P encBits :=
  (show PolyTimeTuringReducible encBits encBits {w | true :: w ∈ B} B from
    (show PolyTimeReducible encBits encBits {w | true :: w ∈ B} B from
      ⟨fun w => true :: w, by fun_prop, fun _ => Iff.rfl⟩).polyTimeTuringReducible).mem_P hB

/-- Complemented language membership in `P` via Turing reduction. -/
example (hB : B ∈ P encBits) : Bᶜ ∈ P encBits :=
  (PolyTimeTuringReducible.compl_self encBits B).mem_P hB

/-- Turing NP-hardness transfer: if `SAT` Turing-reduces to `B ∈ P`, then `P = NP`. -/
example (h : PolyTimeTuringReducible encCNF encBits SAT B) (hB : B ∈ P encBits) :
    P encBits = NP encBits :=
  NPHard.P_eq_NP_of_turing_mem_P CookLevin.SAT_npHard h hB

/-- Turing NP-hardness transfer to NP ∩ coNP: if `SAT` Turing-reduces to `B ∈ NP ∩ coNP`,
then `NP = coNP`. -/
example (h : PolyTimeTuringReducible encCNF encBits SAT B)
    (hB_np : B ∈ NP encBits) (hB_conp : B ∈ coNP encBits) :
    NP encBits = coNP encBits :=
  NPHard.NP_eq_coNP_of_turing_mem_NP_inter_coNP CookLevin.SAT_npHard h hB_np hB_conp

/-- Turing PP-hardness transfer: if a PP-hard language Turing-reduces to `B ∈ P`, then `P = PP`. -/
example (L : Set (List Bool)) (hL : PolyTimeHard PP encBits L)
    (h : PolyTimeTuringReducible encBits encBits L B) (hB : B ∈ P encBits) :
    P encBits = PP encBits :=
  hL.P_eq_PP_of_turing_mem_P h hB

end ComplexityTests.ReductionTuring
