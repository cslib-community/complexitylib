/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.AWPP
import Complexity.Computability.Complexity.Classes.AWPP.Closure
import Complexity.Computability.Complexity.Classes.AWPP.WPP
import Complexity.Computability.Complexity.Classes.SBP
import Complexity.Computability.Complexity.Classes.SharpP.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! Concrete approximate-counting witnesses, including boundary and padding cases. -/

namespace ComplexityTests.ApproximateCounting

open Cslib Cslib.Complexity Turing.MultiTapeTM

private theorem head_mem_P : {w : List Bool | w.headD false = true} ∈ P encBits :=
  ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩

/-- Ratios 3/4 and 1/4 exercise both approximate cases, not only exact characteristic gaps. -/
private theorem head_mem_AWPP : {w : List Bool | w.headD false = true} ∈ AWPP encBits := by
  have hf : ComputableInPolyTime
      (fun w : List Bool => if w.headD false then (3 : ℤ) else 1) encBits encIntBin := by
    fun_prop
  refine ⟨_, mem_GapP_of_polyTime hf, 2, fun w => ?_⟩
  simp only [Set.mem_ofPred_eq]
  cases w.headD false <;> norm_num

example : {w : List Bool | w.headD false = true}ᶜ ∈ AWPP encBits :=
  compl_mem_AWPP head_mem_AWPP

example : {w : List Bool | w.headD false = true} ∈ PP encBits :=
  AWPP_subset_PP head_mem_AWPP

example : {w : List Bool | w.headD false = true} ∈ AWPP encBits :=
  SPP_subset_AWPP (UP_subset_SPP (P_subset_UP head_mem_P))

example : {w : List Bool | w.headD false = true} ∈ AWPP encBits :=
  BPP_subset_AWPP (P_subset_BPP head_mem_P)

/-- A length-dependent, exponentially large numerator and denominator. -/
private theorem head_mem_AWPP_exp : {w : List Bool | w.headD false = true} ∈ AWPP encBits := by
  have hf : ComputableInPolyTime
      (fun w : List Bool => if w.headD false then (2 : ℤ) ^ w.length else 0)
      encBits encIntBin := by fun_prop
  refine ⟨_, mem_GapP_of_polyTime hf, Polynomial.X, fun w => ?_⟩
  have hp : 0 ≤ (2 : ℤ) ^ w.length := by positivity
  cases h : w.headD false <;> simp only [encBits_apply, Polynomial.eval_X, h,
    Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq]
  all_goals constructor <;> simp_all

private theorem tail_reduces_head : PolyTimeReducible encBits encBits
    {w : List Bool | w.tail.headD false = true} {w | w.headD false = true} :=
  ⟨List.tail, by fun_prop, fun _ => Iff.rfl⟩

example : {w : List Bool | w.tail.headD false = true} ∈ AWPP encBits :=
  tail_reduces_head.mem_AWPP head_mem_AWPP_exp

/-- Zero thresholds are allowed on members, even with a zero accepting count. -/
private theorem univ_mem_SBP_zero : (Set.univ : Set (List Bool)) ∈ SBP encBits :=
  ⟨0, SharpP.zero_mem, fun _ => 0, .const 0, fun _ => by simp⟩

example : (Set.univ : Set (List Bool)) ∈ PP encBits := SBP_subset_PP univ_mem_SBP_zero

example : ∃ f ∈ SharpP encBits, ∃ k : List Bool → ℕ,
    ComputableInPolyTime k encBits encNat ∧ (∀ w, 0 < k w) ∧
    ∀ w, (w ∈ (Set.univ : Set (List Bool)) → k w ≤ f w) ∧
      (w ∉ (Set.univ : Set (List Bool)) → 2 * f w < k w) :=
  mem_SBP_iff_exists_pos_threshold.mp univ_mem_SBP_zero

/-- A nonmember may have a positive count: one is strictly less than 3/2. -/
example : (∅ : Set (List Bool)) ∈ SBP encBits :=
  ⟨1, SharpP.one_mem, fun _ => 3, .const 3, fun _ => by simp⟩

private theorem head_mem_SBP : {w : List Bool | w.headD false = true} ∈ SBP encBits := by
  have hf : ComputableInPolyTime
      (fun w : List Bool => if w.headD false then 2 ^ w.length else 0) encBits encNat := by
    fun_prop
  refine ⟨_, mem_SharpP_of_polyTime hf, fun w => 2 ^ w.length, by fun_prop, fun w => ?_⟩
  have hp : 0 < 2 ^ w.length := by positivity
  simp only [Set.mem_ofPred_eq]
  cases w.headD false <;> simp [hp]

example : {w : List Bool | w.headD false = true} ∈ SBP encBits :=
  NP_subset_SBP (UP_subset_NP (P_subset_UP head_mem_P))

example : {w : List Bool | w.headD false = true} ∈ SBP encBits :=
  BPP_subset_SBP (P_subset_BPP head_mem_P)

example : {w : List Bool | w.headD false = true} ∈ PP encBits :=
  SBP_subset_PP head_mem_SBP

example : {w : List Bool | w.headD false = true} ∪ {w | w.tail.headD false = true} ∈
    SBP encBits := union_mem_SBP head_mem_SBP (tail_reduces_head.mem_SBP head_mem_SBP)

example : {w : List Bool | w.headD false = true} ∪ Set.univ ∈ SBP encBits :=
  union_mem_SBP head_mem_SBP univ_mem_SBP_zero

/-- A negative, non-dyadic target tests the WPP normalization away from powers of two. -/
private theorem head_mem_WPP_negative : {w : List Bool | w.headD false = true} ∈
    WPP encBits := by
  let f (w : List Bool) : ℤ := -(3 * 2 ^ w.length)
  have hf : ComputableInPolyTime f encBits encIntBin := by dsimp [f]; fun_prop
  have hg : ComputableInPolyTime
      (fun w : List Bool => if w.headD false then f w else 0) encBits encIntBin := by fun_prop
  have hn (w : List Bool) : f w ≠ 0 := by simp [f]
  refine ⟨_, mem_GapP_of_polyTime hg, f, hf, hn, fun w => ?_, fun w => ?_⟩
  · cases w.headD false <;> simp
  · simp only [Set.mem_ofPred_eq]
    cases w.headD false <;> simp [(hn w).symm]

example : {w : List Bool | w.headD false = true} ∈ AWPP encBits :=
  WPP_subset_AWPP head_mem_WPP_negative

example : {w : List Bool | w.headD false = true} ∈ AWPP encBits :=
  LWPP_subset_AWPP (SPP_subset_LWPP (UP_subset_SPP (P_subset_UP head_mem_P)))

example : ∃ g ∈ GapP encBits, ∃ p : Polynomial ℕ, ∀ w : List Bool,
    (0 ≤ g w ∧ g w ≤ (2 : ℤ) ^ p.eval w.length) ∧
    (w.headD false = true → 7 * (2 : ℤ) ^ p.eval w.length ≤ 8 * g w) ∧
    (w.headD false ≠ true → 8 * g w ≤ (2 : ℤ) ^ p.eval w.length) :=
  exists_AWPP_gap_eighth head_mem_AWPP

example : {w : List Bool | w.headD false = true} ∩ {w | w.tail.headD false = true} ∈
    AWPP encBits := inter_mem_AWPP head_mem_AWPP (tail_reduces_head.mem_AWPP head_mem_AWPP_exp)

example : {w : List Bool | w.headD false = true} ∪ {w | w.headD false = true}ᶜ ∈
    AWPP encBits := union_mem_AWPP head_mem_AWPP (compl_mem_AWPP head_mem_AWPP)

example : {w : List Bool | w.headD false = true} \ {w | w.tail.headD false = true} ∈
    AWPP encBits := diff_mem_AWPP head_mem_AWPP (tail_reduces_head.mem_AWPP head_mem_AWPP)

open scoped symmDiff in
example : {w : List Bool | w.headD false = true} ∆ {w | w.tail.headD false = true} ∈
    AWPP encBits := symmDiff_mem_AWPP head_mem_AWPP (tail_reduces_head.mem_AWPP head_mem_AWPP)

/-- At repetition count `3`, the soundness gap is `2 ^ 3 = 8`. -/
example : ∃ f ∈ SharpP encBits, ∃ k : List Bool → ℕ,
    ComputableInPolyTime k encBits encNat ∧ (∀ w, 0 < k w) ∧ ∀ w,
      (w.headD false = true → k w ≤ f w) ∧ (w.headD false ≠ true → 2 ^ 3 * f w < k w) :=
  exists_SBP_gap_pow head_mem_SBP (by decide : 0 < 3)

example : {w : List Bool | w.headD false = true} ∩ {w | w.tail.headD false = true} ∈
    SBP encBits := inter_mem_SBP_of_mem_BPP head_mem_SBP
      (P_subset_BPP ⟨fun w => w.tail.headD false, by fun_prop, fun _ => Iff.rfl⟩)

example : (Set.univ : Set (List Bool)) ∩ {w | w.headD false = true} ∈ SBP encBits :=
  inter_mem_SBP_of_mem_BPP univ_mem_SBP_zero (P_subset_BPP head_mem_P)

end ComplexityTests.ApproximateCounting
