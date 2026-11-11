/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.BitString
public import Mathlib.Data.Fintype.Pi
import CslibFrontier.Foundations.Data.Fintype.AgreeOn

/-!
# Words agreeing off a set of positions

The words `ι → Bool` agreeing with a word `x` outside a set `F` of positions are free exactly on
`F`, so there are `2 ^ |F|` of them (`BitString.card_filter_forall_notMem_eq`). This is the case
`β = Bool`, `P = Fᶜ` of `Fintype.card_filter_forall_mem_eq`.

## Main results

* `Cslib.BitString.card_filter_forall_notMem_eq`: the words agreeing with `x` outside `F` number
  `2 ^ |F|`.
-/

public section

namespace Cslib.BitString

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The words agreeing with `x` outside `F` number `2 ^ |F|`. -/
theorem card_filter_forall_notMem_eq (F : Finset ι) (x : ι → Bool)
    [DecidablePred fun y : ι → Bool => ∀ i ∉ F, y i = x i] :
    #{y : ι → Bool | ∀ i ∉ F, y i = x i} = 2 ^ #F := by
  calc #{y : ι → Bool | ∀ i ∉ F, y i = x i} = #{y : ι → Bool | ∀ i ∈ Fᶜ, y i = x i} :=
        congrArg card (filter_congr fun y _ => by simp only [mem_compl])
    _ = 2 ^ #F := by rw [Fintype.card_filter_forall_mem_eq, Fintype.card_bool, compl_compl]

end Cslib.BitString
