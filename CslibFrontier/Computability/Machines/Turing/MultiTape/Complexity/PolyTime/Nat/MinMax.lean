/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Binary minimum and maximum by comparison

Extract the existing comparison/branch machines from the Add/XNOR balance
consumer so binary scalar folds can reuse them at the machine layer.

## Main results

* `ComputableInPolyTime.binary_min`, `ComputableInPolyTime.binary_max`:
  binary selection with charged comparison and branch costs.
-/

public section
namespace Turing.MultiTapeTM

/-- Binary minimum uses the existing comparison and conditional machines. -/
@[fun_prop] theorem ComputableInPolyTime.binary_min : ComputableInPolyTime
    (fun q : ℕ × ℕ => min q.1 q.2) (encPair encNat encNat) encNat := by
  have choose : ComputableTidilyInPolyTime (fun q : ℕ × ℕ => decide (q.1 ≤ q.2))
      (encPair encNat encNat) encBool := by
    apply ComputableTidilyInPolyTime.binary_le' <;> fun_prop
  exact .of_tidy ((choose.cond (.fst _ _) (.snd _ _)).of_enc_eq (fun q => by
    by_cases h : q.1 ≤ q.2 <;> simp [h, Nat.min_def]))

/-- Binary maximum uses the same comparison and the opposite branch order. -/
@[fun_prop] theorem ComputableInPolyTime.binary_max : ComputableInPolyTime
    (fun q : ℕ × ℕ => max q.1 q.2) (encPair encNat encNat) encNat := by
  have choose : ComputableTidilyInPolyTime (fun q : ℕ × ℕ => decide (q.1 ≤ q.2))
      (encPair encNat encNat) encBool := by
    apply ComputableTidilyInPolyTime.binary_le' <;> fun_prop
  exact .of_tidy ((choose.cond (.snd _ _) (.fst _ _)).of_enc_eq (fun q => by
    by_cases h : q.1 ≤ q.2 <;> simp [h, Nat.max_def]))

end Turing.MultiTapeTM
