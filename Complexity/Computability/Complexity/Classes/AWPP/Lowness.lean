/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.AWPP
public import Complexity.Computability.Complexity.Classes.PP.Oracle
import Complexity.Computability.Complexity.Classes.AWPP.OracleWeights
import Complexity.Computability.Complexity.Classes.Oracle.Deterministic
import Complexity.Computability.Complexity.Classes.PP.Characterization
import Complexity.Computability.Complexity.Classes.SharpP.Aggregation
import Complexity.Computability.Complexity.Classes.SharpP.WeightedReplay
import Complexity.Computability.Complexity.Classes.SharpP.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Mathlib.Tactic.Linarith

/-!
# AWPP is low for PP

An AWPP oracle adds no power to the strict-majority verifier class `PPWithOracle`
[Fenner2003]. The simulation weights guessed adaptive oracle replies by amplified GapP
numerators. Amplification depends on the original input, and all queries use a common dyadic
denominator. Polynomial-time native replay and uniform GapP products and sums certify the
resulting ordinary GapP function.

PP-lowness was established by Li (1993); see [Fenner, Fortnow, Kurtz and Li][FennerEtAl2003],
Section 6.1. The constant-error AWPP characterization and amplification used here follow
[Fenner][Fenner2003].

## Main definitions

The verifier classes `AWPP`, `PP`, and `PPWithOracle` are imported from their defining modules.

## Main results

* `PPWithOracle_eq_PP_of_mem_AWPP`: every AWPP language is low for PP.

The result uses the existing strict polynomial-time adaptive word-oracle verifier model; it does
not add a separate characterization by probabilistic oracle machines. Exact majority ties
reject in both classes.

## References

* [S. Fenner, L. Fortnow, S. Kurtz, L. Li, *An Oracle Builder's Toolkit*][FennerEtAl2003],
  Section 6.1.
* [S. Fenner, *PP-Lowness and a Simple Definition of AWPP*][Fenner2003]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing (MultiTapePTM)
open _root_.Turing.MultiTapeTM
  (ComputableTidilyInPolyTime encBits encBits_apply encBool_apply encPair encUnary length_encPair)
open _root_.Turing.MultiTapeMachine (FiniteConfig)
open _root_.Turing.MultiTapePTM (replyStep)
open Probability.AdaptiveWeights Finset

variable {α : Type} {enc : α ↪ List Bool} {A : Set (List Bool)}

private theorem answerStep_take_iterate {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Unit) (g : List Bool → Bool)
    (input : List Bool) (T n : ℕ) (hn : n ≤ T) :
    (machine.answerStep (fun q => [g (q.2.take T)]))^[n]
        (FiniteConfig.init machine.initial input) =
      (machine.answerStep (fun q => [g q.2]))^[n]
        (FiniteConfig.init machine.initial input) := by
  have hspace (i : ℕ) : FiniteConfig.SpaceBound input.length i 1
      ((machine.answerStep (fun q => [g q.2]))^[i]
        (FiniteConfig.init machine.initial input)) := by
    induction i with
    | zero => exact FiniteConfig.spaceBound_init _ _ _
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact machine.spaceBound_answerStep g ih
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega)]
    rw [machine.answerStep_bit (fun w => g (w.take T)), machine.answerStep_bit g]
    rw [List.take_of_length_le ((machine.length_pendingRequest_le (hspace n)).trans (by omega))]

private theorem weightedReplay_error {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Unit)
    (input : α → List Bool) (T R : α → ℕ) (H : α × List Bool → ℤ)
    (a : α) (e : ℕ)
    (hw : ∀ w,
      let D := (2 : ℤ) ^ R a
      (0 ≤ H (a, w) ∧ H (a, w) ≤ D) ∧
        (w.take (T a) ∈ A → (2 : ℤ) ^ e * (D - H (a, w)) ≤ D) ∧
        (w.take (T a) ∉ A → (2 : ℤ) ^ e * H (a, w) ≤ D)) :
    (2 : ℤ) ^ e * |weightedReplay machine input T R H a -
      (2 : ℤ) ^ (R a * T a) * (if (OracleComp.interpret (m := Id) (languageOracle A)
        (machine.run (pure false) (fun op word => OracleComp.query (op, word))
          (T a) (input a))).headD false then 1 else 0)| ≤
      (T a : ℤ) * (2 : ℤ) ^ (R a * T a) := by
  classical
  let g : List Bool → Bool := fun w => decide (w ∈ A)
  let D : ℤ := 2 ^ R a
  let p := fun cfg =>
    if (machine.pendingQuery cfg).isSome then H (a, machine.pendingRequest cfg) else 0
  let answer := fun cfg => if (machine.pendingQuery cfg).isSome then
    g ((machine.pendingRequest cfg).take (T a)) else false
  have hp : ∀ cfg, 0 ≤ p cfg ∧ p cfg ≤ D := by
    intro cfg
    dsimp only [p]
    split
    · exact (hw _).1
    · exact ⟨le_rfl, by dsimp [D]; positivity⟩
  have he : ∀ cfg, (2 : ℤ) ^ e * branchWeight D p cfg (!(answer cfg)) ≤ D := by
    intro cfg
    by_cases hq : (machine.pendingQuery cfg).isSome
    · by_cases ha : (machine.pendingRequest cfg).take (T a) ∈ A
      · simpa [branchWeight, p, answer, g, hq, ha] using (hw _).2.1 ha
      · simpa [branchWeight, p, answer, g, hq, ha] using (hw _).2.2 ha
    · simpa [branchWeight, p, answer, hq] using (show 0 ≤ D by dsimp [D]; positivity)
  have hstep : (fun cfg => machine.replyStep cfg (answer cfg)) =
      machine.answerStep (fun q => [g (q.2.take (T a))]) := by
    funext cfg
    rw [machine.answerStep_bit (fun w => g (w.take (T a))) cfg]
    by_cases hq : (machine.pendingQuery cfg).isSome <;> simp [replyStep, answer, hq]
  have h := acceptWeight_error machine.replyStep (fun cfg => cfg.tapes.output.headD false)
    answer (show 0 ≤ D by dsimp [D]; positivity) (show 0 ≤ (2 : ℤ) ^ e by positivity)
    hp he (T a) (FiniteConfig.init machine.initial (input a))
  rw [hstep, answerStep_take_iterate machine g (input a) (T a) (T a) le_rfl] at h
  have hout := machine.interpret_run_pure_false (languageOracle A) (T a) (input a)
  change OracleComp.interpret (m := Id) (languageOracle A) _ =
    ((machine.answerStep (fun q => [g q.2]))^[T a]
      (FiniteConfig.init machine.initial (input a))).tapes.output at hout
  simpa only [weightedReplay, p, D, ← pow_mul, hout] using h

private theorem positive_gap_iff {S C B E : ℤ} (hE : 0 < E)
    (herr : 16 * |S - C * E| ≤ E) :
    0 < 4 * S - (2 * B + 1) * E ↔ B < 2 * C := by
  have hupper := le_abs_self (S - C * E)
  have hlower := neg_le_abs (S - C * E)
  constructor
  · intro hpos
    by_contra hn
    have hle : 2 * C ≤ B := by omega
    have hmul := mul_le_mul_of_nonneg_right hle hE.le
    nlinarith
  · intro hgt
    have hle : B + 1 ≤ 2 * C := by omega
    have hmul := mul_le_mul_of_nonneg_right hle hE.le
    nlinarith

/-- Every AWPP language is low for strict-majority polynomial-time oracle verifiers. -/
theorem PPWithOracle_eq_PP_of_mem_AWPP (hA : A ∈ AWPP encBits) (enc : α ↪ List Bool) :
    PPWithOracle A enc = PP enc := by
  classical
  apply Set.Subset.antisymm ?_ (PP_subset_PPWithOracle A enc)
  rintro L ⟨p, V, ⟨program, hprogram, hV⟩, hL⟩
  obtain ⟨k, m, machine, c, d, hrun⟩ :=
    Probability.IsOraclePPTOn.exists_fin_run_pure_false hprogram
  let r : α → ℕ := fun a => p.eval (enc a).length
  let T : α → ℕ := fun a => c * (2 * (enc a).length + 1 + r a + 1) ^ d
  have hr : ComputableTidilyInPolyTime r enc encUnary := by dsimp [r]; fun_prop
  have hT : ComputableTidilyInPolyTime T enc encUnary := by dsimp [T]; fun_prop
  let e : α → ℕ := fun a => r a + T a + 4
  have he : ComputableTidilyInPolyTime e enc encUnary := by dsimp [e]; fun_prop
  obtain ⟨H, hH, R, hR, hweights⟩ := exists_AWPP_queryWeights hA (.of_tidy hT) (.of_tidy he)
  have hR := hR.tidy
  let input : α × List Bool → List Bool := encPair enc encBits
  let T' : α × List Bool → ℕ := fun x => T x.1
  let R' : α × List Bool → ℕ := fun x => R x.1
  let H' : (α × List Bool) × List Bool → ℤ := fun x => H (x.1.1, x.2)
  let F := weightedReplay machine input T' R' H'
  have hF : F ∈ GapP (encPair enc encBits) := by
    apply GapP.weightedReplay_mem machine
    · dsimp [input]; fun_prop
    · dsimp [T']; fun_prop
    · dsimp [R']; fun_prop
    · exact GapP.comp_mem hH (.of_tidy (by fun_prop))
  let S : α → ℤ := fun a => ∑ w : Fin (r a) → Bool, F (a, List.ofFn w)
  have hS : S ∈ GapP enc := GapP.sum_bits_mem hF (.of_tidy hr)
  let E : α → ℤ := fun a => 2 ^ (R a * T a)
  have hE : E ∈ GapP enc := mem_GapP_of_polyTime (.of_tidy (by dsimp [E]; fun_prop))
  have hcoef : (fun a => 2 * (2 : ℤ) ^ r a + 1) ∈ GapP enc :=
    mem_GapP_of_polyTime (.of_tidy (by fun_prop))
  apply mem_PP_iff_exists_GapP.mpr
  refine ⟨fun a => 4 * S a - (2 * (2 : ℤ) ^ r a + 1) * E a,
    GapP.sub_mem' (GapP.mul_mem (mem_GapP_of_polyTime (.of_tidy (by fun_prop))) hS)
      (GapP.mul_mem hcoef hE), fun a => ?_⟩
  have herror (w : Fin (r a) → Bool) : (2 : ℤ) ^ (r a + T a + 4) *
      |F (a, List.ofFn w) - E a * (if V (a, List.ofFn w) then 1 else 0)| ≤
        (T a : ℤ) * E a := by
    have hw := weightedReplay_error machine input T' R' H' (a, List.ofFn w) (e a)
      (hweights a)
    have hclock : T a = c * ((encPair enc encBits (a, List.ofFn w)).length + 1) ^ d := by
      simp only [T, length_encPair, encBits_apply, List.length_ofFn]
    have hout := hrun (a, List.ofFn w) (languageOracle A)
    rw [hV] at hout
    simp only [input, T', R', H', F, E, e, hclock, hout, encBool_apply,
      List.headD_cons] at hw ⊢
    exact hw
  have hbatch := sum_error (show 0 ≤ E a by dsimp [E]; positivity)
    (fun w : Fin (r a) → Bool => F (a, List.ofFn w)) (fun w => V (a, List.ofFn w)) herror
  have hcount : (∑ w : Fin (r a) → Bool, if V (a, List.ofFn w) then (1 : ℤ) else 0) =
      acceptCount V a (r a) := by
    simp only [acceptCount, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [hcount, mul_comm (E a)] at hbatch
  rw [hL a]
  have hpos := positive_gap_iff (B := (2 : ℤ) ^ r a)
    (show 0 < E a by dsimp [E]; positivity) hbatch
  exact_mod_cast hpos.symm

end Cslib.Complexity
