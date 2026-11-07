/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import Complexity.Foundations.Data.Nat.Radix

/-!
# Fixed tuples of radix registers

The number of registers and their enumeration are fixed independently of the input. Packing and
reading a fixed digit therefore require only finitely many binary additions, multiplications,
divisions and remainders. The radix itself remains an ordinary binary argument.

The pure operations and their recovery/capacity results live in `Cslib.Radix`, in the module
`Complexity.Foundations.Data.Nat.Radix`.

## Main results

* `Turing.MultiTapeNTM.ConfigurationGraph.digit_inSpace`: fixed-position digit extraction.
* `Turing.MultiTapeNTM.ConfigurationGraph.component_inSpace`: finite-tuple component extraction.
* `Turing.MultiTapeNTM.ConfigurationGraph.pack_inSpace`: finite-tuple packing.
-/

@[expose] public section

namespace Turing.MultiTapeNTM.ConfigurationGraph

variable {ι : Type} [Fintype ι]

open MultiTapeTM ComputableInSpace

/-- Reading a fixed digit uses linear space in the binary radix and packed value. -/
theorem digit_inSpace (i : ℕ) :
    ComputableInSpace (fun p : ℕ × ℕ => Cslib.Radix.digit p.1 p.2 i)
      (encPair encNat encNat) encNat fun p => (encPair encNat encNat p).length := by
  induction i with
  | zero => exact budget_natMod (snd _ _) (fst _ _)
  | succ i ih =>
    exact budget_comp_linear ih
      (budget_prod (fst _ _) (budget_natDiv (snd _ _) (fst _ _)))

/-- Reading any one fixed component is a native deterministic linear-space routine. -/
theorem component_inSpace (i : ι) :
    ComputableInSpace (fun p : ℕ × ℕ => Cslib.Radix.component p.1 p.2 i)
      (encPair encNat encNat) encNat fun p => (encPair encNat encNat p).length :=
  digit_inSpace (Fintype.equivFin ι i).val

/-- Packing a fixed tuple of computed components preserves a common space budget. -/
theorem pack_inSpace {α : Type} {enc : α ↪ List Bool} {S : α → ℕ} {B : α → ℕ}
    {f : α → ι → ℕ} (hB : ComputableInSpace B enc encNat S)
    (hf : ∀ i, ComputableInSpace (fun a => f a i) enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => Cslib.Radix.pack (B a) (f a)) enc encNat S := by
  have hlist : ∀ l : List ι, ComputableInSpace
      (fun a => Nat.ofDigits (B a) (l.map (f a))) enc encNat S := by
    intro l
    induction l with
    | nil => exact budget_const 0 hin
    | cons i l ih => exact budget_natAdd (hf i) (budget_natMul hB ih)
  exact hlist (List.ofFn (Fintype.equivFin ι).symm) |>.of_enc_eq fun a => by
    simp [Cslib.Radix.pack, List.map_ofFn, Function.comp_def]

end Turing.MultiTapeNTM.ConfigurationGraph
