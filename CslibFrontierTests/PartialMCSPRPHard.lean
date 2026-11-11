/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.MCSP.PartialHardness.Reduction

/-!
# Tests for the NP-hardness of partial MCSP under randomized reductions

1. With the parameters of `exists_hard_params`, `GapCMMSA` reduces to partial MCSP.
2. Every `NP` problem reduces to partial MCSP, with the threshold in unary and in binary.
3. With `PartialMCSP.mem_NP_encBinary`, partial MCSP with the binary threshold reduces to itself
   with the unary threshold.
4. The conditional consequences for `BPP` and `coRP`.
-/

public section

namespace CslibFrontierTests.PartialMCSPRPHard

open Cslib Cslib.Complexity Cslib.Complexity.PromiseProblem Cslib.PartialMCSP

/-! ### The reduction from `GapCMMSA` -/

/-- The parameters of `exists_hard_params` meet the hypotheses of the reduction at `P = 1`. -/
example : ∃ Δ g, RPReducible CMMSAInstance.encoding enc (GapCMMSA Δ g 1) (ofSet PartialMCSP) := by
  obtain ⟨Δ, k, δ₀, g, hk, hδ₀, hδ₀', hkδ, hg, -⟩ := FromCMMSA.exists_hard_params
  exact ⟨Δ, g, rpReducible_GapCMMSA_PartialMCSP one_pos hk hδ₀ hδ₀' hkδ (by norm_num; linarith)⟩

/-! ### Hardness for `NP` -/

example {α : Type} {encA : α ↪ List Bool} (A : Set α) (hA : A ∈ NP encA) :
    RPReducible encA enc (ofSet A) (ofSet PartialMCSP) :=
  rpHard A hA

example {α : Type} {encA : α ↪ List Bool} (A : Set α) (hA : A ∈ NP encA) :
    RPReducible encA encBinary (ofSet A) (ofSet PartialMCSP) :=
  rpHard_encBinary A hA

/-- Partial MCSP is in `NP`, so it reduces to itself; the binary threshold encoding reduces to the
unary one. -/
example : RPReducible encBinary enc (ofSet PartialMCSP) (ofSet PartialMCSP) :=
  rpHard _ mem_NP_encBinary

/-! ### Conditional consequences -/

example {α : Type} {encA : α ↪ List Bool} (h : PartialMCSP ∈ BPP enc) : NP encA ⊆ BPP encA :=
  NP_subset_BPP_of_mem_BPP h

example {α : Type} {encA : α ↪ List Bool} (h : PartialMCSP ∈ coRP enc) : NP encA ⊆ coRP encA :=
  NP_subset_coRP_of_mem_coRP h

end CslibFrontierTests.PartialMCSPRPHard
