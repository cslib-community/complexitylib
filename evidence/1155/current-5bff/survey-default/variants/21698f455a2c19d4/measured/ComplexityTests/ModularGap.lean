/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.ModP.GapP
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List


import Diag1155.Measure
/-! Composite moduli, signed gaps, and the boundary modulus one. -/


diag1155_install
namespace ComplexityTests.ModularGap

open Cslib.Complexity Turing.MultiTapeTM

private theorem head_mem_SPP : {w : List Bool | w.headD false = true} ∈ SPP encBits :=
  UP_subset_SPP (P_subset_UP ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩)

example : {w : List Bool | w.headD false = true} ∈ ModP 6 encBits :=
  SPP_subset_ModP (by decide) head_mem_SPP

example : {w : List Bool | w.headD false = true} ∈ coModP 6 encBits :=
  SPP_subset_coModP (by decide) head_mem_SPP

example : {w : List Bool | w.headD false = true} ∈ ParityP encBits :=
  SPP_subset_ParityP head_mem_SPP

/-- A negative gap has a nonzero residue modulo six on every input, including the empty word. -/
example : (Set.univ : Set (List Bool)) ∈ ModP 6 encBits :=
  (mem_ModP_iff_exists_GapP (by decide)).mpr
    ⟨-1, GapP.neg_mem GapP.one_mem, fun _ => by norm_num⟩

/-- The signed characterization remains valid at one, where all residues are zero. -/
example : (Set.univ : Set (List Bool)) ∈ coModP 1 encBits :=
  (mem_coModP_iff_exists_GapP (by decide)).mpr
    ⟨-1, GapP.neg_mem GapP.one_mem, fun _ => by norm_num⟩

example : ∃ f ∈ SharpP encBits, ∀ w : List Bool, (f w : ℤ) % 6 = (-1 : ℤ) % 6 :=
  GapP.exists_SharpP_emod (GapP.neg_mem GapP.one_mem) (by decide)

end ComplexityTests.ModularGap
