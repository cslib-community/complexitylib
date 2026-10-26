/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.BooleanHierarchy.PH
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List


import Diag1155.Measure
/-! Clients of the Boolean hierarchy's connection to PH. -/

namespace ComplexityTests.BooleanHierarchyPH

open Cslib.Complexity Turing.MultiTapeTM

private theorem head_mem_NP : {w : List Bool | w.headD false = true} ∈ NP encBits :=
  ⟨0, fun x => x.1.headD false, by fun_prop, fun _ => by simp⟩

private theorem tail_mem_NP : {w : List Bool | w.tail.headD false = true} ∈ NP encBits :=
  ⟨0, fun x => x.1.tail.headD false, by fun_prop, fun _ => by simp⟩

private theorem head_not_tail_mem_DP :
    {w : List Bool | w.headD false = true} \ {w | w.tail.headD false = true} ∈ DP encBits :=
  mem_DP_iff_diff.mpr ⟨_, head_mem_NP, _, tail_mem_NP, rfl⟩

/-- A concrete difference of two distinct nonconstant languages reaches both second levels. -/
example : {w : List Bool | w.headD false = true} \ {w | w.tail.headD false = true} ∈
    SigmaP 2 encBits ∩ PiP 2 encBits :=
  DP_subset_SigmaP_two_inter_PiP_two head_not_tail_mem_DP

example : ({w : List Bool | w.headD false = true} \ {w | w.tail.headD false = true})ᶜ ∈
    SigmaP 2 encBits ∩ PiP 2 encBits :=
  coDP_subset_SigmaP_two_inter_PiP_two (by simpa only [coDP, Set.mem_ofPred_eq, compl_compl]
    using head_not_tail_mem_DP)

example : BooleanHierarchy encBits ⊆ PH encBits :=
  BooleanHierarchy_subset NP_subset_PH (fun _ hA _ hB => diff_mem_PH hA hB)

example : {w : List Bool | w.headD false = true} ∈ BooleanHierarchy encBits :=
  NP_subset_BooleanHierarchy head_mem_NP

end ComplexityTests.BooleanHierarchyPH
