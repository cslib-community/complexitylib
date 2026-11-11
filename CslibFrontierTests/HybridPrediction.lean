/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Circuit.Boolean.CountingBound
public import CslibFrontier.Foundations.Combinatorics.HybridPrediction
public import CslibFrontier.Foundations.Combinatorics.WeightedTail
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Tests for the hybrid prediction lemma, the weighted tail and the circuit counting bound. -/

public section

namespace CslibFrontierTests.HybridPrediction

open Cslib Finset Function

/-! Two channels carrying their inputs, decoded from the first channel alone. The lemma's
hypotheses hold, and it returns a predictor for one of the channels. -/

example : ∃ (t : Fin 2) (base : Fin 2 → Bool × Bool) (y₀ : Bool),
    Fintype.card Bool * 3 ≤
      4 * #{z : Bool | y₀ + ((update base t (z, y₀) 0).2 + (update base t (z, y₀) 0).1) = z} :=
  exists_card_add_decode_update_eq (Z := fun _ => Bool) (fun _ z => z)
    (fun p => (p 0).2 + (p 0).1) fun z b => by
      change z 0 + b + z 0 = b
      cases z 0 <;> cases b <;> rfl

/-! The form a client uses: the guess agrees with the channel on a `1 / 2 + 1 / (2 T)` fraction
of its inputs. -/

example {T : ℕ} {Z : Fin T → Type} [∀ t, Fintype (Z t)] [∀ t, Nonempty (Z t)]
    (E : ∀ t, Z t → Bool) (D : (∀ t, Z t × Bool) → Bool)
    (hD : ∀ (z : ∀ t, Z t) b, D (fun t => (z t, E t (z t) + b)) = b) :
    ∃ (t : Fin T) (base : ∀ t, Z t × Bool) (y₀ : Bool),
      (1 / 2 + 1 / (2 * T) : ℝ) * Fintype.card (Z t) ≤
        #{z : Z t | y₀ + D (update base t (z, y₀)) = E t z} := by
  obtain ⟨t, base, y₀, h⟩ := exists_card_add_decode_update_eq E D hD
  refine ⟨t, base, y₀, ?_⟩
  have hT' : (0 : ℝ) < T := by exact_mod_cast t.pos
  have h' : (Fintype.card (Z t) : ℝ) * (T + 1) ≤
      2 * T * #{z : Z t | y₀ + D (update base t (z, y₀)) = E t z} := by exact_mod_cast h
  have he : (1 / 2 + 1 / (2 * T) : ℝ) * Fintype.card (Z t) =
      Fintype.card (Z t) * (T + 1) / (2 * T) := by
    field_simp
  rw [he, div_le_iff₀ (by positivity)]
  linarith

/-! Two fair coins: at most one of the four outcomes shows two heads. -/

example : #{f : Fin 2 → Bool | 2 ≤ #({i | f i ∈ ({true} : Finset Bool)} : Finset (Fin 2))} ≤ 1 :=
  (card_filter_pi_le_sum_prod (fun _ => {true}) fun S => 2 ≤ #S).trans (by decide)

/-! Three fair coins, each of weight `log 2`: all three come up heads (total weight `3 log 2`) on
at most `2 ^ 3 e^(-3 log 2) 8 = 8` of the `8` outcomes, which is the trivial bound. -/

example : (#{f : Fin 3 → Bool |
      3 * Real.log 2 ≤ ∑ i with f i ∈ ({true} : Finset Bool), Real.log 2} : ℝ) ≤
    2 ^ 3 * Real.exp (-(3 * Real.log 2)) * 8 := by
  have h := card_filter_le_sum_weight_le (fun _ : Fin 3 => ({true} : Finset Bool))
    (fun _ => Real.log 2) (fun _ => by
      rw [Real.exp_neg, Real.exp_log two_pos]
      norm_num) (3 * Real.log 2)
  simpa using h

/-! The circuit counting bound is unchanged by the move out of `FormulaMagnification`. -/

example : Circuits.Boolean.computableFunctionsLogBound 2 3 = 36 := by decide

example (n s : ℕ) : (Circuits.Boolean.computableFunctions n s).card ≤
    2 ^ ((s + 1) * (2 * (n + s + 1) + 3)) :=
  (Circuits.Boolean.card_computableFunctions_le_two_pow n s).trans
    (Nat.pow_le_pow_right (by decide) (Circuits.Boolean.computableFunctionsLogBound_le_poly n s))

end CslibFrontierTests.HybridPrediction
