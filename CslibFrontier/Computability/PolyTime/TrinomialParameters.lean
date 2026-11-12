/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.TrinomialArithmetic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Search
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog

/-!
# Uniform selection of trinomial hashing parameters

The universe size is binary and the requested output width is unary. Bounded search runs over
the target bit length, never over the universe or the finite field. Binary powers used by the
search have polynomial bit length; the selected limb width can then be returned in unary using
its proved linear bound.
-/

public section

namespace Cslib.Probability

/-- The selected exponent is at most the supplied target width. -/
theorem trinomialStepAux_le (B : ℕ) : trinomialStepAux B ≤ B := by
  induction B using Nat.strong_induction_on with
  | ind B ih =>
    rw [trinomialStepAux]
    split_ifs with h
    · omega
    · have := ih ((B + 2) / 3) (by omega)
      omega

/-- Bounded search computes exactly the recursively selected exponent. -/
theorem trinomialStepAux_eq_findGreatest (B : ℕ) :
    trinomialStepAux B = if B ≤ 2 then 0 else
      Nat.findGreatest (fun i => 2 * 3 ^ i < B) B + 1 := by
  split_ifs with h
  · rw [trinomialStepAux, ite_eq_left h]
  · obtain ⟨ht, hp⟩ := two_mul_three_pow_pred_lt_of_two_lt (by omega : 2 < B)
    have hf : Nat.findGreatest (fun i => 2 * 3 ^ i < B) B = trinomialStepAux B - 1 := by
      apply Nat.findGreatest_eq_iff.mpr
      refine ⟨by have := trinomialStepAux_le B; omega, fun _ => hp, ?_⟩
      intro n hn _
      have ht' : trinomialStepAux B ≤ n := by omega
      have hpow := Nat.pow_le_pow_right (by omega : 0 < 3) ht'
      have hbound := le_two_mul_three_pow_trinomialStepAux B
      omega
    rw [hf]
    omega

end Cslib.Probability

namespace Cslib.TrinomialArithmetic

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-- Exact exponent selection is polynomial-time on a unary target bit length. -/
theorem computableInPolyTime_stepAux :
    ComputableInPolyTime Probability.trinomialStepAux encUnary encUnary := by
  have hpred : ComputableInPolyTime
      (fun p : ℕ × ℕ => decide (2 * 3 ^ p.2 < p.1))
      (encPair encUnary encUnary) encBool :=
    binary_lt' (binary_mul' (const 2) (binary_pow' (const 3) (snd _ _)))
      (unary_to_binary.comp (fst _ _))
  have hsearch := findGreatest (bound := id) (predicate := fun B i => 2 * 3 ^ i < B) id' hpred
  have hcond : ComputableInPolyTime (fun B : ℕ => decide (B ≤ 2)) encUnary encBool :=
    binary_le.comp (unary_to_binary.prod (const 2))
  convert ite hcond (const 0) (unary_add' hsearch (const 1)) using 1
  funext B
  simp only [Probability.trinomialStepAux_eq_findGreatest, decide_eq_true_eq, id_eq]

/-- The selected limb width is returned in unary under its linear bound. -/
theorem computableInPolyTime_limbAux :
    ComputableInPolyTime (fun B => 3 ^ Probability.trinomialStepAux B) encUnary encUnary := by
  have hmax : ComputableInPolyTime (fun B : ℕ => max B 1) encUnary encUnary :=
    (of_tidy ComputableTidilyInPolyTime.unary_max).comp (id'.prod (const 1))
  apply binary_to_unary_bounded (binary_pow' (const 3) computableInPolyTime_stepAux)
    (unary_mul' (const 3) hmax)
  intro B
  have := Probability.two_mul_three_pow_trinomialStepAux_le B
  omega

/-- Target-width selection is polynomial-time in a binary universe size and unary output width. -/
theorem computableInPolyTime_target {α : Type} {enc : α ↪ List Bool} {U bits : α → ℕ}
    (hU : ComputableInPolyTime U enc encNat)
    (hbits : ComputableInPolyTime bits enc encUnary) :
    ComputableInPolyTime (fun x => Probability.trinomialTargetBits (U x) (bits x))
      enc encUnary := by
  have hmaxU : ComputableInPolyTime (fun x => max (U x) 2) enc encNat := by
    simpa only [max_def, decide_eq_true_eq, Function.comp_apply] using
      ite (binary_le.comp (hU.prod (const 2))) (const 2) hU
  have hmax := of_tidy ComputableTidilyInPolyTime.unary_max
  exact hmax.comp ((binary_clog_two.comp hmaxU).prod
    (hmax.comp (hbits.prod (const 1))))

/-- The exact selected limb width is computed in unary, from a binary universe size. -/
theorem computableInPolyTime_limb {α : Type} {enc : α ↪ List Bool} {U bits : α → ℕ}
    (hU : ComputableInPolyTime U enc encNat)
    (hbits : ComputableInPolyTime bits enc encUnary) :
    ComputableInPolyTime (fun x => 3 ^ Probability.trinomialStep (U x) (bits x))
      enc encUnary :=
  computableInPolyTime_limbAux.comp (computableInPolyTime_target hU hbits)

/-- Universe, output width, coefficients, and key for automatic field selection. -/
structure SelectedInput where
  /-- Cardinality of the key universe, encoded in binary. -/
  universeSize : ℕ
  /-- Number of output bits retained, encoded in unary. -/
  outputBits : ℕ
  /-- Constant coefficient. -/
  c0 : ℕ
  /-- Linear coefficient. -/
  c1 : ℕ
  /-- Quadratic coefficient. -/
  c2 : ℕ
  /-- Cubic coefficient. -/
  c3 : ℕ
  /-- Evaluation key as a binary polynomial code. -/
  key : ℕ

/-- Only the output width is unary; universe, coefficients, and key are binary. -/
enc_structure encSelectedInput : SelectedInput where
  universeSize : encNat, outputBits : encUnary, c0 : encNat, c1 : encNat,
  c2 : encNat, c3 : encNat, key : encNat

/-- Select the field and evaluate the original four-coefficient family. -/
@[expose] def runSelected (p : SelectedInput) : ℕ :=
  hash4 (3 ^ Probability.trinomialStep p.universeSize p.outputBits) p.outputBits
    p.c0 p.c1 p.c2 p.c3 p.key

/-- One native polynomial-time machine performs parameter selection and hash evaluation. -/
theorem computableInPolyTime_runSelected :
    ComputableInPolyTime runSelected encSelectedInput encNat := by
  unfold runSelected
  apply computableInPolyTime_hash4
  · apply computableInPolyTime_limb <;> fun_prop
  all_goals fun_prop

/-- The uniform native evaluator computes the exact short-seed family, for every valid seed/key. -/
theorem runSelected_eq (U bits : ℕ)
    (c : Fin 4 → Fin (2 ^ Probability.trinomialDeg U bits)) (u : Fin U) :
    runSelected ⟨U, bits, (c 0).val, (c 1).val, (c 2).val, (c 3).val, u.val⟩ =
      (Probability.trinomialPolyHash (Probability.trinomialStep U bits) 4 U bits c u).val := by
  exact hash4_eq _ U bits c u (u.isLt.trans_le (Probability.le_two_pow_trinomialDeg U bits))

/-- A valid selected hash input has length linear in the target bit width, including framing,
all four seed coefficients, the binary universe size, and the evaluation key. -/
theorem length_encSelectedInput_le (U bits : ℕ)
    (c : Fin 4 → Fin (2 ^ Probability.trinomialDeg U bits)) (u : Fin U) :
    (encSelectedInput ⟨U, bits, (c 0).val, (c 1).val, (c 2).val, (c 3).val,
      u.val⟩).length ≤ 39 * Probability.trinomialTargetBits U bits + 8 := by
  have hU := Probability.le_two_pow_trinomialDeg U bits
  have hpos : 0 < 2 ^ Probability.trinomialDeg U bits := by positivity
  have hUlen : (encNat U).length ≤ Probability.trinomialDeg U bits + 1 :=
    length_encNat_le_of_lt_two_pow (by rw [pow_succ]; omega)
  have hclen (i : Fin 4) : (encNat (c i).val).length ≤ Probability.trinomialDeg U bits :=
    length_encNat_le_of_lt_two_pow (c i).isLt
  have hulen : (encNat u.val).length ≤ Probability.trinomialDeg U bits :=
    length_encNat_le_of_lt_two_pow (u.isLt.trans_le hU)
  have hbits := Probability.le_trinomialDeg U bits
  have hdeg := Probability.trinomialDeg_le_three_mul U bits
  simp only [encSelectedInput_apply, length_encPair, encUnary_apply, List.length_replicate]
  have h0 := hclen 0
  have h1 := hclen 1
  have h2 := hclen 2
  have h3 := hclen 3
  unfold Probability.trinomialTargetBits
  omega

end Cslib.TrinomialArithmetic
