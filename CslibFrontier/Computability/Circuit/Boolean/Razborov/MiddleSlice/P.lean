/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Razborov.MiddleSlice
public import CslibFrontier.Computability.Complexity.Classes.P.Slices
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt
import CslibFrontier.Foundations.Data.BitString.List

/-!
# The middle slice is in P: `P ⊄ AC⁰[2]`

The middle slice `Cslib.Circuits.Boolean.Razborov.middleSlice`, which is not in AC⁰[2]
(`Cslib.Circuits.Boolean.Razborov.middleSlice_notMem_AC0Mod_two`), is in `P`: a multi-tape Turing
machine counts the true bits and compares with `n - sliceLevel n`, computed in unary from the
length `n` (`middleSlice_mem_P`). This separates `P` from AC⁰[2]
(`exists_mem_P_notMem_AC0Mod_two`) [Razborov1987].

The `P` side is kept apart from the lower bound so that clients of the lower bound alone, such as
`Cslib.Circuits.Boolean.Smolensky.majority_notMem_AC0Mod`, do not import the polynomial-time Turing
machine library.

## Main results

* `Cslib.Circuits.Boolean.Razborov.middleSlice_mem_P`: the middle slice is in `P`.
* `Cslib.Circuits.Boolean.Razborov.exists_mem_P_notMem_AC0Mod_two`: `P ⊄ AC⁰[2]`.

## References

* [A. A. Razborov, *Lower bounds on the size of bounded depth circuits over a complete basis with
  logical addition*][Razborov1987]
-/

public section

namespace Cslib.Circuits.Boolean.Razborov

open BitString Cslib.Complexity Turing.MultiTapeTM

/-- The list evaluator of the middle slice: count the true bits and compare with
`n - sliceLevel n`, where `n` is the length. -/
private theorem middleSlice_ofList (x : List Bool) :
    middleSlice x.length (ofList x.length x) =
      decide (x.count true = x.length - ((x.length + 1) / 2 - Nat.sqrt (x.length + 1) / 10)) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, middleSlice_eq_true_iff, ← count_true_ofFn,
    ofFn_ofList rfl, sliceLevel_eq]

/-- **The middle slice is in `P`**: count the true bits in unary and compare with
`n - sliceLevel n`, computed in unary from the length `n` (the square root in binary). -/
theorem middleSlice_mem_P : (Language.ofSlices middleSlice : Set (List Bool)) ∈ P encBits := by
  refine ofSlices_mem_P ?_
  simp only [middleSlice_ofList]
  have hlen : ComputableInPolyTime (fun x : List Bool => x.length) encBits encUnary :=
    ComputableInPolyTime.length_bits
  have hsucc : ComputableInPolyTime (fun x : List Bool => x.length + 1) encBits encUnary :=
    ComputableInPolyTime.unary_add' hlen (.const 1)
  have hsqrt : ComputableInPolyTime (fun x : List Bool => Nat.sqrt (x.length + 1)) encBits
      encUnary :=
    ComputableInPolyTime.binary_to_unary_bounded
      (ComputableInPolyTime.binary_sqrt' (ComputableInPolyTime.unary_to_binary.comp hsucc)) hsucc
      fun x => Nat.sqrt_le_self _
  have hgap : ComputableInPolyTime (fun x : List Bool => Nat.sqrt (x.length + 1) / 10) encBits
      encUnary :=
    ComputableInPolyTime.unary_div' hsqrt (.const 10)
  have hlevel : ComputableInPolyTime
      (fun x : List Bool => (x.length + 1) / 2 - Nat.sqrt (x.length + 1) / 10) encBits encUnary :=
    ComputableInPolyTime.unary_sub' (ComputableInPolyTime.unary_div' hsucc (.const 2)) hgap
  have hcount : ComputableInPolyTime (fun x : List Bool => x.count true) encBits encUnary :=
    ComputableInPolyTime.bitsCountWithInput ComputableInPolyTime.id' (.const true)
  exact ComputableInPolyTime.unary_eq' hcount (ComputableInPolyTime.unary_sub' hlen hlevel)

/-- **Unconditional separation `P ⊄ AC⁰[2]`**: the middle slice is in `P` and not in AC⁰[2]
[Razborov1987]. `Cslib.Circuits.Boolean.exists_mem_P_notMem_AC0Mod` combines it with parity for odd
primes, giving `P ⊄ AC⁰[p]` for every prime `p`. -/
theorem exists_mem_P_notMem_AC0Mod_two :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ P encBits ∧ L ∉ AC0Mod 2 :=
  ⟨_, middleSlice_mem_P, middleSlice_notMem_AC0Mod_two⟩

end Cslib.Circuits.Boolean.Razborov
