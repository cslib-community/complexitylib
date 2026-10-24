/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Foundations.Data.BitString.List
public import Cslib.Computability.Languages.Slice
import Mathlib.Data.List.GetD

/-!
# Languages given by their slices, in P

A Boolean family `f : ∀ n, BitString n → Bool` determines the language `Language.ofSlices f` of bit
lists `x` with `f x.length x = true`. Reading `x` through `BitString.ofList`, the language is in
`Cslib.Complexity.P encBits` exactly when its list evaluator
`fun x => f x.length (BitString.ofList x.length x)` is computable in polynomial time.

## Main results

* `Cslib.Complexity.mem_ofSlices_iff`, `Cslib.Complexity.ofSlices_eq_setOf_ofList`: membership in
  `Language.ofSlices f` via `BitString.ofList`.
* `Cslib.Complexity.ofSlices_mem_P_iff`: `Language.ofSlices f ∈ P encBits` if and only if its list
  evaluator is computable in polynomial time.
* `Cslib.Complexity.ofSlices_mem_P`: the sufficient direction.
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- Membership of a bit list `x` in `Language.ofSlices f` in terms of `BitString.ofList`. -/
theorem mem_ofSlices_iff (f : ∀ n, BitString n → Bool) (x : List Bool) :
    x ∈ Language.ofSlices f ↔ f x.length (BitString.ofList x.length x) = true := by
  change f x.length (fun i => x[i]) = true ↔ f x.length (BitString.ofList x.length x) = true
  congr! 2
  funext i
  rw [BitString.ofList, List.getD_eq_getElem _ _ i.2, Fin.getElem_fin]

/-- For any Boolean family `f : ∀ N, BitString N → Bool`, `Language.ofSlices f` as a set of bit
lists is `{x | f x.length (BitString.ofList x.length x) = true}`. -/
theorem ofSlices_eq_setOf_ofList (f : ∀ N, BitString N → Bool) :
    (Language.ofSlices f : Set (List Bool)) =
      {x : List Bool | f x.length (BitString.ofList x.length x) = true} :=
  Set.ext fun x => mem_ofSlices_iff f x

/-- If `fun x => f x.length (BitString.ofList x.length x)` is computable in polynomial time, then
`Language.ofSlices f` belongs to `P encBits`. -/
theorem ofSlices_mem_P {f : ∀ n, BitString n → Bool}
    (hf : ComputableInPolyTime
      (fun x : List Bool => f x.length (BitString.ofList x.length x)) encBits encBool) :
    (Language.ofSlices f : Set (List Bool)) ∈ P encBits := by
  exact ⟨_, hf, mem_ofSlices_iff f⟩

/-- **`Language.ofSlices f` is in `P`** if and only if its list evaluator
`fun x => f x.length (BitString.ofList x.length x)` is computable in polynomial time. -/
theorem ofSlices_mem_P_iff {f : ∀ N, BitString N → Bool} :
    (Language.ofSlices f : Set (List Bool)) ∈ P encBits ↔
      ComputableInPolyTime
        (fun x : List Bool => f x.length (BitString.ofList x.length x)) encBits encBool := by
  constructor
  · rintro ⟨g, hg, hiff⟩
    have heq : (fun x : List Bool => f x.length (BitString.ofList x.length x)) = g := by
      funext x
      exact Bool.eq_iff_iff.mpr ((mem_ofSlices_iff f x).symm.trans (hiff x))
    exact heq ▸ hg
  · exact ofSlices_mem_P

end Cslib.Complexity
