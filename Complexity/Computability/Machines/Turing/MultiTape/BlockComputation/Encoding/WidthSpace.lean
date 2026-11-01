/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.Encoding
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatSize

/-!
# Native block-value width initialization

The encoded value width is computed from the actual binary block width. Machine tape and finite
control counts are fixed parameters. No block-sized intermediate word is allocated.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.Encoding

open MultiTapeTM MultiTapeTM.ComputableInSpace

/-- Compute the complete block-value width in space linear in the actual binary block width. -/
theorem width_inSpace (k s : ℕ) : ComputableInSpace (width k s) encNat encNat
    (fun b => (encNat b).length) := by
  have hid : ComputableInSpace (fun b : ℕ => b) encNat encNat
      (fun b => (encNat b).length) := of_inO (ComputableInO.of_eq (f := id) fun _ => rfl)
  have hconst (n : ℕ) : ComputableInSpace (fun _ : ℕ => n) encNat encNat
      (fun b => (encNat b).length) := budget_const n (.refl _)
  have hsize := budget_comp_linear natSize hid
  have hwindow := budget_natMul (hconst k)
    (budget_natMul (hconst 3) (budget_natMul hid (hconst 2)))
  exact (budget_natSucc (budget_natAdd (hconst (s + 1).size)
    (budget_natAdd (budget_natMul (hconst (k + 1)) hsize)
      (budget_natAdd (hconst 2) hwindow)))).of_enc_eq fun _ => rfl

end Turing.MultiTapePTM.BlockComputation.Encoding
