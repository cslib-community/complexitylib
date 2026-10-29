/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.WeightedThreshold.Activity

/-! Exact Hamming-ball counts and gate-activity bounds, including empty gate sets. -/

open Cslib Cslib.Circuits Cslib.BitString Finset

namespace ThresholdActivity

-- Independent finite counts at zero, partial, and oversized radii.
example : #{x : Fin 3 → Bool | weight x ≤ 0} = 1 := by decide
example : #{x : Fin 3 → Bool | weight x ≤ 1} = 4 := by decide
example : #{x : Fin 3 → Bool | weight x ≤ 5} = 8 := by decide

example {ι : Type*} [Fintype ι] [DecidableEq ι] :
    #{x : ι → Bool | weight x ≤ 0} = 1 := by
  rw [card_filter_weight_le]
  simp

example (e : ℕ) : #{x : Fin 0 → Bool | weight x ≤ e} = 1 := by
  simp [weight]

-- The image bound collapses repeated constant words to at most one image element.
example : ((univ : Finset (Fin 3)).image (fun _ => fun _ : Fin 2 => false)).card = 1 := by
  apply le_antisymm
  · have h := card_image_le_sum_choose (univ : Finset (Fin 3))
      (fun _ => fun _ : Fin 2 => false) (e := 0) (fun _ _ => by simp [weight])
    simpa using h
  · exact Finset.card_pos.mpr (univ_nonempty.image _)

-- Empty families still satisfy the image bound, including zero-dimensional words.
example (e : ℕ) : ((∅ : Finset Bool).image (fun _ => fun _ : Fin 0 => false)).card ≤
    ∑ j ∈ range (e + 1), Nat.choose 0 j :=
  card_image_le_sum_choose _ _ (fun _ h => False.elim (notMem_empty _ h))

example (f : Bool → Fin 2 → Bool) : (univ.image f).card ≤ 4 := by
  have h := card_image_le_sum_choose (univ : Finset Bool) f (e := 5) fun x _ =>
    (weight_le (f x)).trans (by decide)
  simpa [sum_range_succ, Nat.choose] using h

-- Coordinate restriction needs injectivity: repeating a true bit can increase weight.
example (x : Fin 3 → Bool) :
    weight ((x ∘ Fin.castAdd 1 : Fin 2 → Bool) ∘ Fin.castAdd 1 : Fin 1 → Bool) ≤ weight x :=
  (weight_comp_le _ (Fin.castAdd_injective 1 1)).trans
    (weight_comp_le x (Fin.castAdd_injective 2 1))

example : weight ((fun _ : Fin 1 => true) ∘ (fun _ : Fin 2 => 0)) >
    weight (fun _ : Fin 1 => true) := by decide

open Boolean.WeightedThreshold

private def trueGate : Program signature 0 1 :=
  Program.empty.gate ⟨⟨0, Fin.elim0, 0⟩, Fin.elim0⟩

-- An active gate-only computation has zero input-reading activity.
private theorem trueGate_eval (x : Fin 0 → Bool) :
    trueGate.eval interpretation x 0 = true := by
  change (Program.empty.gate _).eval interpretation x (Fin.last 0) = true
  rw [Program.eval_gate_last]
  norm_num [Line.eval, interpretation]

private theorem inputActivity_trueGate : inputActivity trueGate = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa [inputGates] using inputActivity_le_card trueGate

-- Total activity includes the active nullary gate that input-reading activity excludes.
private theorem gateActivity_trueGate : gateActivity trueGate = 1 := by
  apply Nat.le_antisymm (gateActivity_le trueGate)
  have h := (gateActivity_le_iff trueGate).mp le_rfl Fin.elim0
  simpa [weight_eq_sum_toNat, trueGate_eval] using h

example : inputActivity trueGate < gateActivity trueGate := by
  rw [inputActivity_trueGate, gateActivity_trueGate]
  decide

-- No gates gives activity zero and exactly one empty transcript, at every input length.
example (n : ℕ) :
    inputActivity (Program.empty : Program signature n 0) = 0 ∧
      gateActivity (Program.empty : Program signature n 0) = 0 := by
  refine ⟨Nat.eq_zero_of_le_zero ?_, Nat.eq_zero_of_le_zero (gateActivity_le Program.empty)⟩
  simpa [inputGates] using inputActivity_le_card (Program.empty : Program signature n 0)

example (n : ℕ) :
    (attainableTranscripts (Program.empty : Program signature n 0)).card = 1 := by
  classical
  have h : attainableTranscripts (Program.empty : Program signature n 0) =
      {transcript Program.empty (fun _ => false)} := by
    ext z
    simp only [mem_attainableTranscripts, mem_singleton]
    constructor
    · rintro ⟨x, rfl⟩
      exact Subsingleton.elim _ _
    · rintro rfl
      exact ⟨fun _ => false, rfl⟩
  rw [h, card_singleton]

-- Bounds use only direct-input gates, so a gate-only program has at most one input transcript.
example : (attainableTranscripts trueGate).card = 1 := by
  apply le_antisymm
  · have h := card_attainableTranscripts_le_sum_choose_of_le trueGate
      (show inputActivity trueGate ≤ 0 by rw [inputActivity_trueGate])
    simpa using h
  · exact Finset.card_pos.mpr ⟨transcript trueGate Fin.elim0, by simp [mem_attainableTranscripts]⟩

-- Combining the binomial transcript bound with `inputActivity_le_card` and `card_filter_weight_le`
-- bounds the number of attainable transcripts by `2 ^ (inputGates p).card`.
example {n g : ℕ} (p : Program signature n g) :
    (attainableTranscripts p).card ≤ 2 ^ (inputGates p).card := by
  refine (card_attainableTranscripts_le_sum_choose_of_le p (inputActivity_le_card p)).trans ?_
  rw [← Fintype.card_coe (inputGates p), ← card_filter_weight_le]
  exact (card_le_univ _).trans_eq (by simp)

example {n g : ℕ} (p : Program signature n g) : inputActivity p ≤ g :=
  (inputActivity_le_gateActivity p).trans (gateActivity_le p)

-- Evaluate the combined transcript bound on the gate-only fixture: no input-reading gates.
example : (attainableTranscripts trueGate).card ≤ 1 := by
  have h := card_attainableTranscripts_le_sum_choose_of_le trueGate
    (inputActivity_le_card trueGate)
  have hbound : (attainableTranscripts trueGate).card ≤ 2 ^ (inputGates trueGate).card := by
    refine h.trans ?_
    rw [← Fintype.card_coe (inputGates trueGate), ← card_filter_weight_le]
    exact (card_le_univ _).trans_eq (by simp)
  simpa [inputGates] using hbound

example : inputActivity trueGate ≤ 1 :=
  (inputActivity_le_gateActivity trueGate).trans (gateActivity_le trueGate)

-- The radius exceeds the fixture's zero input-reading gates; the binomial sum is still one.
example : (attainableTranscripts trueGate).card ≤
    ∑ j ∈ range ((inputGates trueGate).card + 4), (inputGates trueGate).card.choose j := by
  apply card_attainableTranscripts_le_sum_choose_of_le
  exact (inputActivity_le_card trueGate).trans (Nat.le_add_right _ 3)

end ThresholdActivity
