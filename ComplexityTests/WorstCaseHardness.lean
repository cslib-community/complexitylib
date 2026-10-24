/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.HardnessAmplification.WorstCase
import Complexity.Computability.Circuit.Boolean.NaturalProof
import Complexity.Computability.Complexity.Classes.BPP.WorstCaseHardness
import Mathlib.FieldTheory.Finite.GaloisField

/-! Worst-case to average-case reconstruction: the parameter hypotheses of the reconstruction
theorem are jointly satisfiable, over a field of `2 ^ 35` elements, with the encoding itself as the
predictor, for a function on one bit and for a function on `256` bits (Reed–Muller degree `256`);
such fields, encodings and embeddings exist; the explicit binary fields have the right size; the
hardness transfer applies to a language that is hard by counting, and the membership of the
encoding in `E` applies to a language in `P` (the two hypotheses of the derandomization theorem
are separately satisfiable; jointly they are open); and named axiom guards for the headline
theorems of the development. -/

namespace ComplexityTests.WorstCaseHardness

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Code Cslib.HardnessEncoding Finset Filter

/-- Fields of `2 ^ 35` elements exist. -/
example : ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ 35 := by
  refine ⟨GaloisField 2 35, inferInstance, Fintype.ofFinite _, ?_⟩
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card 2 35 (by norm_num)

/-- A field of `2 ^ 35` elements has an encoding by `35` bits and contains a copy of
`BitString 1`. -/
example {F : Type*} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ 35) :
    Nonempty (F ≃ BitString 35) ∧ Nonempty (BitString 1 ↪ F) := by
  refine ⟨⟨Fintype.equivOfCardEq (by simp [hF, BitString])⟩,
    Function.Embedding.nonempty_of_card_le (by simp [hF, BitString])⟩

/-- **The reconstruction theorem is not vacuous.** Over a field of `2 ^ 35` elements, with
`K = 11` masks, Sudan parameter `D = 2 ^ 18 + 1` and majority trees of depth `0`, the parameter
hypotheses hold for a function on one bit, with the encoding itself as a predictor agreeing on all
inputs (`ε = 1 / 4`). -/
example {F : Type*} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ 35)
    (enc : F ≃ BitString 35) (h : BitString 1 ↪ F) (f : BooleanFunction (1 * 1)) :
    complexity interpretation (single f) ≤
      reconstructionCost 35 1 1 (2 ^ 18 + 1) 11 0
        (complexity interpretation (single (hardnessEncode enc h f))) (Fintype.card F)
        #(Sudan.monomials (1 * (2 ^ 1 - 1)) (2 ^ 18 + 1)) := by
  refine complexity_le_of_agree_hardnessEncode enc h f le_rfl (ε := 1 / 4) (by norm_num) ?_
    (by norm_num) ?_ (by norm_num) ?_ ?_ ?_ (by norm_num)
  · have : (#{y | hardnessEncode enc h f y = hardnessEncode enc h f y} : ℝ) =
        2 ^ (1 * 35 + 35) := by
      rw [filter_true_of_mem (fun _ _ => rfl), card_univ, BitString.card, Nat.cast_pow,
        Nat.cast_ofNat]
    rw [this]
    norm_num
  · norm_num
  · rw [hF]
    have := Sudan.add_one_mul_add_two_le_two_mul_mul_card_monomials (w := 1) le_rfl (2 ^ 18 + 1)
    norm_num at this ⊢
    omega
  · rw [hF]
    norm_num
  · rw [hF]
    norm_num

-- The hypotheses mention `2 ^ (256 * 35 + 35)` and `2 ^ 22`; `norm_num` evaluates these powers,
-- whose exponents exceed the default threshold of `256`.
set_option exponentiation.threshold 10000 in
/-- **A larger instance.** The parameter hypotheses also hold for a function on `256` bits read as
`m = 256` blocks of one bit, so that the Reed–Muller degree is `d = 256`, over a field of `2 ^ 35`
elements, with `K = 9` masks, Sudan parameter `D = 2 ^ 22`, majority trees of depth `8` and the
encoding itself as a predictor (`ε = 1 / 2`). -/
example {F : Type*} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ 35)
    (enc : F ≃ BitString 35) (h : BitString 1 ↪ F) (f : BooleanFunction (256 * 1)) :
    complexity interpretation (single f) ≤
      reconstructionCost 35 1 256 (2 ^ 22) 9 8
        (complexity interpretation (single (hardnessEncode enc h f))) (Fintype.card F)
        #(Sudan.monomials (256 * (2 ^ 1 - 1)) (2 ^ 22)) := by
  refine complexity_le_of_agree_hardnessEncode enc h f le_rfl (ε := 1 / 2) (by norm_num) ?_
    (by norm_num) ?_ (by norm_num) ?_ ?_ ?_ (by norm_num)
  · have : (#{y | hardnessEncode enc h f y = hardnessEncode enc h f y} : ℝ) =
        2 ^ (256 * 35 + 35) := by
      rw [filter_true_of_mem (fun _ _ => rfl), card_univ, BitString.card, Nat.cast_pow,
        Nat.cast_ofNat]
    rw [this, show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num, one_mul]
  · norm_num
  · rw [hF]
    have := Sudan.add_one_mul_add_two_le_two_mul_mul_card_monomials
      (w := 256 * (2 ^ 1 - 1)) (by norm_num) (2 ^ 22)
    norm_num at this ⊢
    omega
  · rw [hF]
    norm_num
  · rw [hF]
    norm_num

/-! ### Milestone 2: the explicit field, membership in `E` and the hardness transfer -/

/-- The explicit binary field of degree `4` has `16` elements. -/
example : Fintype.card (BinaryField 4) = 16 := BinaryField.card (by norm_num)

/-- **Membership in `E` applies**: the encoding of a problem in `P` (the explicit affine
disperser) is in `E`. -/
example (M : ℕ) : (encodedLanguage
    {x : List Bool | AffineDisperser.explicitDisperser x.length
      (BitString.ofList x.length x) = true} M : Set (List Bool)) ∈
    Complexity.E Turing.MultiTapeTM.encBits :=
  HardnessEncoding.encodedLanguage_mem_E
    (Complexity.P_subset_E AffineDisperser.setOf_explicitDisperser_mem_P) M

/-- `5 n ≤ 2 ^ (n / 2)` for all large `n`. -/
private theorem eventually_five_mul_le : ∀ᶠ n : ℕ in atTop,
    (5 * n : ℝ) ≤ (2 : ℝ) ^ ((1 / 2 : ℝ) * n) := by
  have hr : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h := tendsto_pow_const_div_const_pow_of_one_lt 1 hr
  filter_upwards [h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 5))] with n hn
  have hpos : (0 : ℝ) < Real.sqrt 2 ^ n := by positivity
  rw [pow_one, div_lt_iff₀ hpos] at hn
  have hsq : Real.sqrt 2 ^ n = (2 : ℝ) ^ ((1 / 2 : ℝ) * n) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rw [← hsq]
  linarith

/-- **The hardness transfer is not vacuous**: some language needs `2 ^ (n / 2)` gates at all
large lengths, by counting circuits, so its encoded language is average-case hard at all large
lengths. Whether some language in `E` is that hard is open. -/
example : ∃ L : Language Bool, ∀ᶠ N in atTop,
    IsAverageCaseHard (encodedSlice L (blockFactor (1 / 2)) N)
      (2 ^ (N / hardnessDivisor (1 / 2))) := by
  classical
  have hex : ∀ n, 16 ≤ n → ∃ f : BooleanFunction n,
      2 ^ n / (5 * n) < complexity interpretation (single f) := fun n hn => by
    have h := two_pow_two_pow_le_two_mul_ncard_setOf_lt_complexity hn
    have hne : {f : BooleanFunction n |
        2 ^ n / (5 * n) < complexity interpretation (single f)}.ncard ≠ 0 := by
      intro h0
      rw [h0] at h
      have : 0 < 2 ^ 2 ^ n := by positivity
      omega
    exact Set.nonempty_of_ncard_ne_zero hne
  let F : ∀ n, BooleanFunction n := fun n =>
    if h : 16 ≤ n then (hex n h).choose else fun _ => false
  refine ⟨Language.ofSlices F, eventually_isAverageCaseHard_encodedSlice (by norm_num) ?_⟩
  filter_upwards [eventually_five_mul_le, eventually_ge_atTop 16] with n hn h16
  rw [Language.slice_ofSlices]
  have hF := (hex n h16).choose_spec
  have hFn : F n = (hex n h16).choose := by simp only [F, dite_eq_left h16]
  rw [hFn]
  -- `2 ^ (n / 2) ≤ 2 ^ n / (5 n) < ⌊2 ^ n / (5 n)⌋ + 1 ≤ complexity`
  set q := 2 ^ n / (5 * n)
  have hq : 2 ^ n < (q + 1) * (5 * n) := by
    have := Nat.lt_div_mul_add (a := 2 ^ n) (b := 5 * n) (by omega)
    rw [add_mul, one_mul]
    exact this
  have hq' : (2 : ℝ) ^ n < ((q + 1 : ℕ) : ℝ) * (5 * n) := by exact_mod_cast hq
  have hc : ((q + 1 : ℕ) : ℝ) ≤ complexity interpretation (single (hex n h16).choose) := by
    exact_mod_cast hF
  have hsplit : (2 : ℝ) ^ n = (2 : ℝ) ^ ((1 / 2 : ℝ) * n) * (2 : ℝ) ^ ((1 / 2 : ℝ) * n) := by
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_natCast]
    congr 1
    ring
  have h5 : (0 : ℝ) < 5 * n := by
    have : (16 : ℝ) ≤ n := by exact_mod_cast h16
    linarith
  have hpow : (0 : ℝ) < (2 : ℝ) ^ ((1 / 2 : ℝ) * n) := by positivity
  have key : (2 : ℝ) ^ ((1 / 2 : ℝ) * n) * (5 * n) ≤ ((q + 1 : ℕ) : ℝ) * (5 * n) := by
    nlinarith
  exact (le_of_mul_le_mul_right key h5).trans hc

/-! ### Axioms -/

/--
info: 'Cslib.Circuits.Boolean.complexity_le_of_agree_hardnessEncode' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.complexity_le_of_agree_hardnessEncode

/--
info: 'Cslib.Circuits.Boolean.complexity_le_pow_of_agree_hardnessEncode' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.complexity_le_pow_of_agree_hardnessEncode

/--
info: 'Cslib.Circuits.Boolean.reconstructionCost_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.reconstructionCost_le

/--
info: 'Cslib.Circuits.Boolean.exists_glPredictor_agree' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.exists_glPredictor_agree

/--
info: 'Cslib.Code.exists_card_lineListDecode_ne_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Code.exists_card_lineListDecode_ne_le

/--
info: 'Cslib.Code.card_hintDecode_ne_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Code.card_hintDecode_ne_le

/--
info: 'Cslib.exists_forall_majTree_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.exists_forall_majTree_eq

/--
info: 'Cslib.LinearAlgebra.kernelVec_ne_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.LinearAlgebra.kernelVec_ne_zero

/--
info: 'Cslib.Circuits.Synthesis.bitBlast' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Synthesis.bitBlast

/--
info: 'Cslib.Crypto.GoldreichLevin.exists_card_candidate_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GoldreichLevin.exists_card_candidate_eq

/--
info: 'Cslib.Complexity.P_eq_BPP_of_eventually_two_pow_le_complexity' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.P_eq_BPP_of_eventually_two_pow_le_complexity

/--
info: 'Cslib.HardnessEncoding.encodedLanguage_mem_E' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.HardnessEncoding.encodedLanguage_mem_E

/--
info: 'Cslib.HardnessEncoding.encodedProgram_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.HardnessEncoding.encodedProgram_eq

/--
info: 'Cslib.HardnessEncoding.computableInPolyTime_paddedProgram' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.HardnessEncoding.computableInPolyTime_paddedProgram

/--
info: 'Cslib.HardnessEncoding.eventually_isAverageCaseHard_encodedSlice' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.HardnessEncoding.eventually_isAverageCaseHard_encodedSlice

/--
info: 'Cslib.HardnessEncoding.isMulTable_fieldTable' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.HardnessEncoding.isMulTable_fieldTable

/--
info: 'Cslib.Complexity.BPP_subset_P_of_eventually_two_pow_le_complexity' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.BPP_subset_P_of_eventually_two_pow_le_complexity

/--
info: 'Cslib.Complexity.setOf_mem_E_of_computableInPolyTime_pad' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.setOf_mem_E_of_computableInPolyTime_pad

/--
info: 'Cslib.BinaryField.card' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BinaryField.card

end ComplexityTests.WorstCaseHardness
