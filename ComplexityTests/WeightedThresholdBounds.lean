/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.WeightedThreshold.Activation
import Complexity.Computability.Circuit.Boolean.WeightedThreshold.Components
import Complexity.Computability.Circuit.Boolean.WeightedThreshold.InnerProduct
import Complexity.Computability.Circuit.Boolean.WeightedThreshold.Menus
import Complexity.Computability.Circuit.Boolean.WeightedThreshold.PendingBias
import Complexity.Computability.Circuit.Boolean.WeightedThreshold.Potential
import Complexity.Computability.Circuit.Boolean.WeightedThreshold.ScalarActivity
import Complexity.Computability.Circuit.Boolean.WeightedThreshold.SupportBound
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FinCases

/-! Tests for mixed-activation, cut, component, block-excess, direction-menu,
pending-bias, shifted-baseline activity, scalar query-activity, Cover enumerative coding,
unambiguous cell, and quadratic-potential unique-sink representations of weighted threshold
circuits. -/

open Cslib Cslib.Circuits Cslib.Circuits.Boolean.WeightedThreshold

-- A one-input threshold program and circuit computing negation.
private def readInput : Program signature 1 1 :=
  Program.empty.gate ⟨⟨1, fun _ => 1, 1⟩, fun _ => .input 0⟩

private def negatePrior : Program signature 1 2 :=
  readInput.gate ⟨⟨1, fun _ => -1, 0⟩, fun _ => .gate 0⟩

private theorem negatePrior_eval (x : Fin 1 → Bool) :
    negatePrior.eval interpretation x 1 = !x 0 := by
  have hread : negatePrior.eval interpretation x 0 = x 0 := by
    change readInput.eval interpretation x (Fin.last 0) = x 0
    rw [readInput, Program.eval_gate_last]
    cases hx : x 0 <;> simp [Line.eval, interpretation, hx]
  change (readInput.gate _).eval interpretation x (Fin.last 1) = !x 0
  rw [Program.eval_gate_last]
  change decide ((0 : ℝ) ≤ ∑ _ : Fin 1, (-1 : ℝ) *
    (negatePrior.eval interpretation x 0).toNat) = !x 0
  rw [hread]
  cases x 0 <;> simp

private def negateCircuit : Circuit signature 1 1 := ⟨negatePrior, fun _ => .gate 1⟩

private theorem negateCircuit_eval (x : Fin 1 → Bool) :
    negateCircuit.eval interpretation x 0 = !x 0 :=
  negatePrior_eval x

private theorem oneBit_rectangleFree (f : (Fin 1 → Bool) → Bool) (b : Bool) :
    Frontier.RectangleFree {x | f x = b} 2 := by
  apply Frontier.rectangleFree_iff.mpr
  intro X A B _
  by_cases h : (0 : Fin 1) ∈ X
  · right
    have hX : X = Set.univ := by ext i; fin_cases i; simp [h]
    subst X
    have : B.ncard ≤ 1 := by simpa using Set.ncard_le_ncard (Set.subset_univ B)
    omega
  · left
    have hX : X = ∅ := by ext i; fin_cases i; simp [h]
    subst X
    have : A.ncard ≤ 1 := by simpa using Set.ncard_le_ncard (Set.subset_univ A)
    omega

-- Weighted threshold circuits translate into `activationSignature` via `mapOp`.
example (x : Fin 1 → Bool) :
    (negateCircuit.mapOp ofWeightedThreshold).eval activationInterpretation x =
      negateCircuit.eval interpretation x :=
  Circuit.eval_mapOp _ _

-- C4: Mixed-activation program and circuit bounds.
private def constActivationCircuit : Circuit activationSignature 1 1 :=
  ⟨Program.empty.gate ⟨⟨1, fun _ => 1, fun _ => false⟩, fun _ => .input 0⟩, fun _ => .gate 0⟩

private theorem constActivationCircuit_eval (x : Fin 1 → Bool) :
    constActivationCircuit.eval activationInterpretation x 0 = false := by
  change (Program.empty.gate _).eval activationInterpretation x (Fin.last 0) = false
  rw [Program.eval_gate_last]
  rfl

private theorem constActivation_changes (j : Fin constActivationCircuit.size) :
    ChangesAtMost (constActivationCircuit.program.lines j).op.activate 0 := by
  fin_cases j
  change ChangesAtMost (fun _ : ℝ => false) 0
  exact ChangesAtMost.const false

example :
    2 ^ 1 < 4 * 2 ^ 2 *
      ∏ _ ∈ activationInputGates constActivationCircuit.program, max 1 (4 * 0) :=
  circuit_two_pow_lt_of_activations constActivationCircuit ⟨(0 : Fin 1), rfl⟩
    (fun _ => 0) (fun j _ => constActivation_changes j)
    constActivationCircuit_eval (oneBit_rectangleFree _)

-- Cut and balanced-cut bounds on `negateCircuit`.
example (U : Finset (Fin 1)) :
    U.card < (Finset.univ.filter fun j =>
      (inputSupport negateCircuit.program j ∩ U).Nonempty).card + 1 ∨
    Uᶜ.card < (Finset.univ.filter fun j =>
      (inputSupport negateCircuit.program j ∩ Uᶜ).Nonempty).card + 1 :=
  circuit_lt_of_split negateCircuit ⟨(1 : Fin 2), rfl⟩ negateCircuit_eval
    (oneBit_rectangleFree _) U (k := 1) le_rfl

example : 1 ≤ 2 * ((inputGates negateCircuit.program).card + 1) :=
  circuit_le_two_mul_add negateCircuit ⟨(1 : Fin 2), rfl⟩ negateCircuit_eval
    (oneBit_rectangleFree _) (k := 1) le_rfl

-- The support bound applies to a concrete circuit with one input-reading gate and one
-- input-free gate. The zero incidence cutoff is allowed: it fixes the read input.
example : (1 : ℝ) ≤ (2 * (1 - (1 / 2 : ℝ) ^ 1) + 1) *
    (inputGates negateCircuit.program).card + 2 + Real.sqrt 2 := by
  have h := circuit_le_of_inputSupport_card_le negateCircuit ⟨(1 : Fin 2), rfl⟩
    negateCircuit_eval (oneBit_rectangleFree _)
    (d := 1) (fun gate => (Finset.card_le_univ _).trans (by decide)) 0 (k := 1) le_rfl
  simpa using h

-- The sharper incidence bound permits cutoff zero as well, including the empty residual
-- input type and a gate whose original input support is empty.
example : (2 : ℝ) < 9 * (inputGates negateCircuit.program).card +
    3 * (Nat.log 2 (1 + (inputGates negateCircuit.program).card) : ℝ) + 7 := by
  have h := circuit_two_mul_lt_of_inputSupport_card_le_three
    negateCircuit ⟨(1 : Fin 2), rfl⟩ negateCircuit_eval (oneBit_rectangleFree _)
    (fun gate => (Finset.card_le_univ _).trans (by decide)) 0 (k := 1) le_rfl
  norm_num at h ⊢
  linarith

-- Fixing every input makes the residual-coordinate type empty; the original circuit
-- and its rectangle-free output are still valid inputs to the incidence theorem.
example : (1 : ℝ) ≤ 2 * (1 - (1 / 2 : ℝ) ^ 1) *
    (inputGates negateCircuit.program).card + 3 + Real.sqrt 2 := by
  have h := le_inputGates_of_bounded_incidence negateCircuit.program (fun z => z (1 : Fin 2))
    negatePrior_eval (oneBit_rectangleFree _)
    (d := 1) (fun gate => (Finset.card_le_univ _).trans (by decide)) Finset.univ 0
    (by simp) (k := 1) le_rfl
  norm_num at h ⊢
  linarith

-- C5: Fan-in-two component bound on `negateCircuit`.
private theorem negateCircuit_support_le_two (j : Fin negateCircuit.size) :
    (inputSupport negateCircuit.program j).card ≤ 2 :=
  le_trans (Finset.card_le_univ _) (by decide)

example : 1 < (inputGates negateCircuit.program).card + 2 * 1 :=
  circuit_lt_of_inputSupport_card_le_two negateCircuit ⟨(1 : Fin 2), rfl⟩
    negateCircuit_eval (oneBit_rectangleFree _) negateCircuit_support_le_two (L := 1) le_rfl

-- C6: Block-excess bound on `negateCircuit` with a single singleton block `{0}` and `F = ∅`.
example : 1 < (∅ : Finset (Fin 1)).card + (inputGates negateCircuit.program).card + 1 + 2 * 1 := by
  refine circuit_lt_of_blocks negateCircuit ⟨(1 : Fin 2), rfl⟩ negateCircuit_eval
    (oneBit_rectangleFree _) ∅ {({0} : Finset (Fin 1))} ?_ ?_ ?_ ?_ 1 ?_ (k := 1) le_rfl
  · simp [Set.PairwiseDisjoint]
  · intro i _
    fin_cases i
    exact ⟨{0}, Finset.mem_singleton_self _, Finset.mem_singleton_self _⟩
  · intro b hb
    simp [Finset.mem_singleton.mp hb]
  · intro j
    right
    refine ⟨{0}, Finset.mem_singleton_self _, ?_⟩
    intro i _
    fin_cases i
    exact Finset.mem_singleton_self _
  · intro b hb
    rw [Finset.mem_singleton.mp hb, Finset.card_singleton]
    omega

-- Shifted-baseline activity and Corollary 3.3 rectangle-density bounds.
example (vIn : inputGates negateCircuit.program → Bool) (vGate : Fin 2 → Bool) :
    inputActivityFrom negateCircuit.program 0 = inputActivity negateCircuit.program ∧
    gateActivityFrom negateCircuit.program 0 = gateActivity negateCircuit.program ∧
    (attainableTranscripts negateCircuit.program).card ≤
      ∑ j ∈ Finset.range (inputActivityFrom negateCircuit.program vIn + 1),
        (inputGates negateCircuit.program).card.choose j ∧
    (attainableTranscripts negateCircuit.program).card ≤
      ∑ j ∈ Finset.range (gateActivityFrom negateCircuit.program vGate + 1), Nat.choose 2 j :=
  ⟨inputActivityFrom_zero negateCircuit.program,
   gateActivityFrom_zero negateCircuit.program,
   card_attainableTranscripts_le_sum_choose_inputActivityFrom negateCircuit.program vIn,
   card_attainableTranscripts_le_sum_choose_gateActivityFrom negateCircuit.program vGate⟩

example (v : inputGates (Program.empty : Program signature 0 0) → Bool) :
    (Finset.univ : Finset (Fin 0 → Bool)).card *
      (Finset.univ : Finset (Fin 0 → Bool)).card ≤
      1 * (∑ j ∈ Finset.range (inputActivityFrom (Program.empty : Program signature 0 0) v + 1),
        (inputGates (Program.empty : Program signature 0 0)).card.choose j) ^ 2 := by
  refine card_mul_le_mul_sum_choose_inputActivityFrom_sq Program.empty
    (finSumFinEquiv : Fin 0 ⊕ Fin 0 ≃ Fin 0).symm v Finset.univ Finset.univ
    Finset.univ_nonempty Finset.univ_nonempty (fun _ => false) (M := 1) ?_
  intro A' hA' B' hB' _ _
  have hA1 : A'.card ≤ (Finset.univ : Finset (Fin 0 → Bool)).card := Finset.card_le_card hA'
  have hB1 : B'.card ≤ (Finset.univ : Finset (Fin 0 → Bool)).card := Finset.card_le_card hB'
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.pow_zero] at hA1 hB1
  exact Nat.mul_le_mul hA1 hB1

example (v : inputGates (Program.empty : Program signature 0 0) → Bool) :
    1 ≤ (∑ j ∈ Finset.range (inputActivityFrom (Program.empty : Program signature 0 0) v + 1),
      (inputGates (Program.empty : Program signature 0 0)).card.choose j) ^ 2 :=
  two_pow_le_sum_choose_inputActivityFrom_sq_of_dotProduct Program.empty
    (finSumFinEquiv : Fin 0 ⊕ Fin 0 ≃ Fin 0).symm v (fun _ => false)
    (fun _ _ => by simp [dotProduct, Bool.zero_eq_false])

example (v : Fin 0 → Bool) :
    1 ≤ (∑ j ∈ Finset.range (gateActivityFrom (Program.empty : Program signature 0 0) v + 1),
      Nat.choose 0 j) ^ 2 :=
  two_pow_le_sum_choose_gateActivityFrom_sq_of_dotProduct Program.empty
    (finSumFinEquiv : Fin 0 ⊕ Fin 0 ≃ Fin 0).symm v (fun _ => false)
    (fun _ _ => by simp [dotProduct, Bool.zero_eq_false])

-- Concrete pending-bias simulation and state-space bounds on `negatePrior`.
private theorem negatePrior_gateWeight_one_zero : gateWeight negatePrior 1 0 = -1 := by
  change lineWeight (negatePrior.lines (Fin.last 1)) (.gate 0) = -1
  rw [negatePrior, Program.lines_gate_last]
  change (∑ a : Fin 1 with (Wire.gate 0 : Wire 1 2) = Wire.gate 0, (-1 : ℝ)) = -1
  simp

private theorem negatePrior_inputWeight_one (a : Fin 1) : inputWeight negatePrior 1 a = 0 := by
  fin_cases a
  change lineWeight (negatePrior.lines (Fin.last 1)) (.input 0) = 0
  rw [negatePrior, Program.lines_gate_last]
  simp [lineWeight, Wire.Renaming.castSucc]

example (x : Fin 1 → Bool) :
    negatePrior.eval interpretation x 1 =
      decide (gateThreshold negatePrior 1 ≤
        (∑ a : Fin 1, inputWeight negatePrior 1 a * (x a).toNat) +
          pendingBiasTrace negatePrior x 1 ⟨0, by decide⟩) ∧
    (pendingBiasStates negatePrior 1).card ≤ 2 ^ 1 :=
  ⟨eval_eq_decide_pendingBiasTrace negatePrior x 1,
   card_pendingBiasStates_le_two_pow negatePrior 1⟩

example : (pendingBiasStates negatePrior 1).card ≤ 1 + 1 := by
  refine card_pendingBiasStates_le_add_one_of_row_const negatePrior 1 (fun _ => -1) ?_
  intro i j
  fin_cases i
  fin_cases j
  exact negatePrior_gateWeight_one_zero

example :
    (pendingBiasStates negatePrior 1).card ≤
      (1 + 1 * 1) ^ (Finset.univ : Finset (Fin 1)).card := by
  refine card_pendingBiasStates_le_pow_intWeight negatePrior 1 1 Finset.univ
    (fun _ _ h => funext fun i => h i (Finset.mem_univ i)) (fun _ _ => -1) ?_ (fun _ _ _ => le_rfl)
  intro i _ j
  fin_cases i
  fin_cases j
  simpa using negatePrior_gateWeight_one_zero

example : (Finset.univ.image (intSummary (fun (_ : Fin 1) (_ : Fin 1) => (-1 : ℤ)))).card ≤
    (1 + Fintype.card (Fin 1) * 1) ^ 1 :=
  card_intSummary_le_pow (fun (_ : Fin 1) (_ : Fin 1) => (-1 : ℤ)) (fun _ _ => le_rfl)

example :
    (Finset.univ.image (fun (x : Fin 1 → Bool) (_ : Unit) => !x 0)).card ≤
      (Finset.univ.image (fun x : Fin 1 → Bool => x 0)).card := by
  refine card_rows_le_card_summaries (X := Fin 1 → Bool) (Y := Unit) (α := Bool)
    negatePrior (fun x _ => x) (fun z => z 1) (fun x _ => !x 0)
    (fun x : Fin 1 → Bool => x 0) (fun x _ => negatePrior_eval x) ?_
  intro x₁ x₂ _ h
  have hx : x₁ = x₂ := funext fun i => by fin_cases i; exact h
  rw [hx]

example :
    (Finset.univ.image (fun (x : Fin 1 → Bool) (_ : Unit) => !x 0)).card ≤
      (pendingBiasStates negatePrior 1).card := by
  refine card_rows_le_card_pendingBiasStates_of_phased (X := Fin 1 → Bool) (Y := Unit)
    negatePrior (fun x _ => x) (fun z => z 1)
    (fun x _ => !x 0) 1 () (fun x _ => negatePrior_eval x) (fun _ _ _ _ => rfl) ?_ ?_
  · intro i x₁ x₂ _
    fin_cases i
    change inputSummary negatePrior x₁ 1 = inputSummary negatePrior x₂ 1
    simp [inputSummary, negatePrior_inputWeight_one]
  · intro z₁ z₂ h
    exact h ⟨0, by decide⟩

-- Direction-menu bounds (Theorem 7.3 and Corollary 7.4) on `negateCircuit`.
example :
    2 ^ 1 < 4 * 2 ^ 2 * ∏ a : Fin negateCircuit.size,
      min (4 ^ (directionGates negateCircuit.program id a).card)
        (max 1 (4 * directionMenuSum negateCircuit.program id a)) :=
  circuit_two_pow_lt_of_directionMenus negateCircuit ⟨(1 : Fin 2), rfl⟩ id
    (inputWeight negateCircuit.program) (fun _ => 1)
    (fun _ _ => (one_smul ℝ _).symm)
    negateCircuit_eval (oneBit_rectangleFree _)

example :
    2 ^ 1 < 4 * 2 ^ 2 * ∏ a : Fin negateCircuit.size,
      min (4 ^ (directionGates negateCircuit.program id a).card)
        (max 1 (4 * ((directionGates negateCircuit.program id a).card * 2 ^ 2))) :=
  circuit_two_pow_lt_of_directionMenus_fanIn negateCircuit ⟨(1 : Fin 2), rfl⟩ id
    (inputWeight negateCircuit.program) (fun _ => 1)
    (fun _ _ => (one_smul ℝ _).symm) 2
    (fun _ _ => le_trans (Finset.card_le_univ _) (by decide))
    negateCircuit_eval (oneBit_rectangleFree _)

-- Single-direction bounded integer internal weights on `readInput`.
private theorem readInput_eval (x : Fin 1 → Bool) :
    readInput.eval interpretation x 0 = x 0 := by
  change readInput.eval interpretation x (Fin.last 0) = x 0
  rw [readInput, Program.eval_gate_last]
  cases hx : x 0 <;> simp [Line.eval, interpretation, hx]

example :
    2 ^ 1 < 4 * 2 ^ 2 * max 1 (4 * ((inputGates readInput).card * (1 + (1 - 1) * 0))) := by
  refine two_pow_lt_of_direction_intWeight readInput (fun z => z 0)
    (inputWeight readInput 0) (fun _ => 1) ?_ 0 (fun _ _ => 0) ?_ ?_
    readInput_eval (oneBit_rectangleFree _)
  · intro gate _
    fin_cases gate
    exact (one_smul ℝ _).symm
  · intro gate _ j
    fin_cases gate
    fin_cases j
    simpa using gateWeight_eq_zero_of_le readInput 0 0 le_rfl
  · intro gate _ j hj
    fin_cases gate
    exact False.elim (Nat.not_lt_zero _ hj)

/-! ### Scalar query-activity run capacity and Cover enumerative coding -/

private theorem negatePrior_along (j : Fin 2) :
    ∃ c : ℝ, inputWeight negatePrior j = c • (fun _ : Fin 1 => (1 : ℝ)) :=
  ⟨inputWeight negatePrior j 0, funext fun i => by fin_cases i; simp⟩

example :
    PiecesAtMost (scalarTranscript negatePrior (fun _ => 1))
      (attainableTranscripts negatePrior).card ∧
    ChangesAtMost (scalarReadout negatePrior (fun _ => 1) (fun z => z 1))
      ((attainableTranscripts negatePrior).card - 1) ∧
    2 ^ 1 < 16 * 2 ^ 2 *
      (∑ j ∈ Finset.range (inputActivity negateCircuit.program + 1),
        (inputGates negateCircuit.program).card.choose j) ∧
    2 ^ 1 < 16 * 2 ^ 2 *
      (∑ j ∈ Finset.range (gateActivity negateCircuit.program + 1),
        negateCircuit.size.choose j) :=
  ⟨piecesAtMost_scalarTranscript negatePrior (fun _ => 1) negatePrior_along,
   changesAtMost_scalarReadout negatePrior (fun _ => 1) negatePrior_along (fun z => z 1),
   circuit_two_pow_lt_mul_sum_choose_of_direction negateCircuit ⟨(1 : Fin 2), rfl⟩
     (fun _ => 1) negatePrior_along negateCircuit_eval (oneBit_rectangleFree _),
   circuit_two_pow_lt_mul_sum_choose_gateActivity_of_direction negateCircuit ⟨(1 : Fin 2), rfl⟩
     (fun _ => 1) negatePrior_along negateCircuit_eval (oneBit_rectangleFree _)⟩

example (z : Fin 3 → Bool) (t : ℕ) (ht : t < BitString.ballSize 3 2) :
    BitString.coverDecode 3 3 (BitString.coverRank 3 z) = z ∧
    BitString.coverRank 2 (BitString.coverDecode 3 2 t) = t ∧
    BitString.weight (BitString.coverDecode 3 2 t) ≤ 2 :=
  ⟨BitString.coverDecode_coverRank z (BitString.weight_le_length z),
   BitString.coverRank_coverDecode ht,
   BitString.weight_coverDecode_le 3 2 t⟩

/-! ### Unambiguous transcript cells and quadratic-potential unique sinks -/

-- Concrete 2-gate strict-margin program on 1 input: gate 0 copies `x 0` with score `2 x_0 - 1`,
-- and gate 1 negates gate 0 with score `-2 z_0 + 1` (`|Q_0| = |Q_1| = 1`).
private def sampleStrictMarginProgram : StrictMarginProgram 1 2 where
  inputWeight i _ := if i = 0 then 2 else 0
  gateWeight i j := if i = 1 ∧ j = 0 then -2 else 0
  threshold i := if i = 0 then 1 else -1
  gateWeight_eq_zero_of_le i j hij := by
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
  one_le_abs_score x z i := by
    fin_cases i <;> simp
    · cases x 0 <;> norm_num
    · cases z 0 <;> norm_num

private theorem sampleStrictMarginProgram_abs_score_le_one (x : Fin 1 → Bool) (z : Fin 2 → Bool)
    (i : Fin 2) :
    |sampleStrictMarginProgram.score x z i| ≤ 1 := by
  fin_cases i <;>
    simp [StrictMarginProgram.score, StrictMarginProgram.inputSum, StrictMarginProgram.internalSum,
      sampleStrictMarginProgram]
  · cases x 0 <;> norm_num
  · cases z 0 <;> norm_num

example (U : Finset (Fin 1)) (fixed : Finset (Fin 2)) (val : Fin 2 → Bool)
    (x : Fin 1 → Bool) (z : Fin 2 → Bool) :
    (sampleStrictMarginProgram.inTranscriptCell x z ↔ z = sampleStrictMarginProgram.eval x) ∧
    (∃! z' : Fin 2 → Bool, sampleStrictMarginProgram.inTranscriptCell x z') ∧
    (sampleStrictMarginProgram.inTranscriptCell x z ↔
      ∀ i : Fin 2,
        sampleStrictMarginProgram.rightDemand U z x i ≤
          sampleStrictMarginProgram.leftSupply U z x i) ∧
    (sampleStrictMarginProgram.ilpValid (fun _ => 1) x z ↔ z = sampleStrictMarginProgram.eval x) ∧
    (sampleStrictMarginProgram.IsSinkOnFace fixed val x z ↔
      z = sampleStrictMarginProgram.faceEval fixed val x) ∧
    (sampleStrictMarginProgram.IsSinkOnFace ∅ (fun _ => false) x z ↔
      z = sampleStrictMarginProgram.eval x) ∧
    sampleStrictMarginProgram.sweep fixed val x z 2 =
      sampleStrictMarginProgram.faceEval fixed val x :=
  ⟨sampleStrictMarginProgram.inTranscriptCell_iff_eq_eval x z,
   sampleStrictMarginProgram.existsUnique_inTranscriptCell x,
   sampleStrictMarginProgram.inTranscriptCell_iff_dominance U x z,
   sampleStrictMarginProgram.ilpValid_iff_eq_eval (sampleStrictMarginProgram_abs_score_le_one x z),
   sampleStrictMarginProgram.isSinkOnFace_iff_eq_faceEval fixed val x z,
   sampleStrictMarginProgram.isSink_iff_eq_eval x z,
   sampleStrictMarginProgram.sweep_eq_faceEval fixed val x z⟩

example (i : Fin 2) :
    sampleStrictMarginProgram.priority i ≤ (2 + 1) ^ (2 - 1 - i.val) := by
  refine sampleStrictMarginProgram.priority_le_pow (by norm_num) ?_ i
  intro j k hkj
  fin_cases j <;> fin_cases k <;> simp [sampleStrictMarginProgram]
