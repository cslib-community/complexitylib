/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.HardCore.Set
import CslibFrontier.Computability.Circuit.Boolean.Hierarchy
import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Foundations.Data.BitString.Parity

/-! Impagliazzo's hard-core lemma in set form: a concrete hard-core set, a function with no
hard-core set, the measure-to-set rounding run end to end on parity with a satisfied counting
condition, and the parameters of the set form of the lemma. -/

namespace ComplexityTests.HardCoreSet

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Finset

/-! ### A concrete hard-core set and a function without one -/

/-- Against circuits without gates, which compute coordinate projections, all inputs form a
hard-core set of density `1` and advantage `0` for parity on two bits, read off from the indicator
measure. -/
example : IsHardCoreSet (parity 2) 0 1 0 univ := by
  refine isHardCoreSet_iff_isHardCoreMeasure.mpr
    ⟨fun _ => ⟨by split_ifs <;> norm_num, by split_ifs <;> norm_num⟩, by norm_num, fun g hg => ?_⟩
  have hproj : ∃ i, g = fun x => x i := by
    by_contra! h
    exact absurd (one_le_complexity_single (I := interpretation) h) (by omega)
  obtain ⟨i, rfl⟩ := hproj
  have hcount : ∀ i : Fin 2, #{x : BitString 2 | x i = parity 2 x} = 2 := by decide
  simp only [mem_univ, ite_true, sum_const, card_univ, nsmul_eq_mul, mul_one, hcount i,
    BitString.card]
  norm_num

/-- A constant function has no hard-core set of positive density with advantage below `1 / 2`
against circuits with one gate: the constant itself agrees with it everywhere. -/
example {n s : ℕ} (hs : 1 ≤ s) {δ ε : ℝ} (hδ : 0 < δ) (hε : ε < 1 / 2)
    (H : Finset (BitString n)) : ¬IsHardCoreSet (fun _ : BitString n => false) s δ ε H := by
  intro h
  have hg := h.card_agree_le (fun _ => false) (by rw [complexity_const]; exact hs)
  rw [filter_true_of_mem fun _ _ => rfl] at hg
  have hpos : (0 : ℝ) < #H := lt_of_lt_of_le (by positivity) h.mul_two_pow_le_card
  nlinarith

/-! ### Rounding a hard-core measure of parity -/

/-- A coordinate projection agrees with parity on thirteen bits on exactly half of the inputs. -/
theorem card_proj_eq_parity (i : Fin 13) :
    #{x : BitString 13 | x i = parity 13 x} = 2 ^ 12 := by
  have hne : (univ.erase i).Nonempty := by
    rw [← card_pos, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
    norm_num
  have hset : (univ.filter fun x : BitString 13 => x i = parity 13 x) =
      univ.filter fun x => parityOn (univ.erase i) x = false := by
    refine filter_congr fun x _ => ?_
    rw [parity, parityOn_eq_xor_erase (mem_univ i)]
    cases x i <;> cases parityOn (univ.erase i) x <;> decide
  rw [hset, card_filter_parityOn_eq hne, Fintype.card_fin]

/-- The constant measure `1 / 2` is a hard-core measure of density `1 / 2` and advantage `0` for
parity on thirteen bits against circuits without gates. -/
theorem isHardCoreMeasure_parity :
    IsHardCoreMeasure (parity 13) 0 (1 / 2) 0 fun _ => 1 / 2 := by
  refine ⟨fun _ => ⟨by norm_num, by norm_num⟩, by norm_num, fun g hg => ?_⟩
  have hproj : ∃ i, g = fun x => x i := by
    by_contra! h
    exact absurd (one_le_complexity_single (I := interpretation) h) (by omega)
  obtain ⟨i, rfl⟩ := hproj
  simp only [sum_const, card_univ, nsmul_eq_mul, card_proj_eq_parity i, BitString.card]
  norm_num

/-- The rounding theorem applies to this measure: there are at most `13` functions without gates,
and `14 exp (-16) < 1`, so parity on thirteen bits has a hard-core set with at least `2 ^ 12`
elements against circuits without gates, with advantage `2 γ = 1 / 4` for `γ = 1 / 8`. -/
example : ∃ H, IsHardCoreSet (parity 13) 0 (1 / 2) (0 + 2 * (1 / 8)) H := by
  refine isHardCoreMeasure_parity.exists_isHardCoreSet (by norm_num) (by norm_num) le_rfl
    (by norm_num) (by norm_num) ?_
  have hC : (#(Boolean.computableFunctions 13 0) : ℝ) ≤ 13 := by
    have h := card_computableFunctions_mul_factorial_le 13 0
    norm_num at h
    exact_mod_cast h
  have hexp : (17 : ℝ) < Real.exp 16 := by
    have h := Real.add_one_lt_exp (x := 16) (by norm_num)
    linarith
  have harg : -2 * (1 / 8 * (1 / 2) * (1 - 1 / 2) : ℝ) ^ 2 * 2 ^ 13 = -16 := by norm_num
  rw [harg, Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos 16)]
  linarith

/-! ### The parameters of the set form -/

/-- With `δ = 1 / 2`, `ε = 1 / 8`, `γ = 1 / 16` and eighty-six rounds (`3 ε² δ² 86 = 129 / 128`),
hardness for size `86 s + 15138` and the counting condition give a hard-core set of at least
`2 ^ n / 2` inputs against size `s` with advantage `1 / 4`. -/
example {n s : ℕ} (f : BooleanFunction n)
    (hf : ∀ g : BooleanFunction n, complexity interpretation (single g) ≤ 86 * s + 15138 →
      (#{x | g x = f x} : ℝ) / 2 ^ n ≤ 1 - 1 / 2)
    (hcount : (#(Boolean.computableFunctions n s) + 1) *
      Real.exp (-2 * (1 / 16 * (1 / 2) * (1 - 1 / 2)) ^ 2 * 2 ^ n) < 1) :
    ∃ H, IsHardCoreSet f s (1 / 2) (1 / 8 + 2 * (1 / 16)) H :=
  exists_isHardCoreSet (T := 86) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hf hcount

end ComplexityTests.HardCoreSet
