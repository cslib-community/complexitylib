/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.WeightedThreshold

/-!
# Unambiguous transcript cells and quadratic-potential unique-sink representations

Every straight-line threshold program in strict unit-margin normal form (`StrictMarginProgram`),
where each gate `i` has score
`Q_i(x, z) = ∑ a, a_{i, a} x_a + ∑ j < i, b_{i, j} z_j - θ_i` with `|Q_i(x, z)| ≥ 1` on all
Boolean assignments and outputs `true` iff `0 < Q_i(x, z)`, admits two exact characterizations of
its gate transcript (`StrictMarginProgram.eval`):

1. **Unambiguous cells, coordinatewise dominance, and unique-extension ILP** (Section 10 of
   `[ThresholdCircuitRepresentations2026]`):
   For a putative transcript `z : Fin g → Bool` with sign `σ_i = boolSign (z i) ∈ {-1, 1}`, the
   consistency cell predicate `∀ i, 1 ≤ σ_i * Q_i(x, z)` holds if and only if `z = P.eval x`
   (`inTranscriptCell_iff_eq_eval`). The cells therefore partition the input cube (`∃! z,
   P.inTranscriptCell x z`, `existsUnique_inTranscriptCell`). Across any input split `U`, cell
   membership is equivalent to coordinatewise dominance `rightDemand ≤ leftSupply` in dimension `g`
   (`inTranscriptCell_iff_dominance`), and given upper bounds `|Q_i(x, z)| ≤ M_i`, to the linear
   inequalities `1 - (M_i + 1)(1 - z_i) ≤ Q_i(x, z) ≤ -1 + (M_i + 1) z_i` (`ilpValid_iff_eq_eval`).

2. **Quadratic Boolean potential and unique sinks on cube faces** (Section 11, Theorem 11.1 of
   `[ThresholdCircuitRepresentations2026]`):
   Defining positive priorities backwards by `λ_i = 1 + ∑_{j > i} λ_j |b_{j, i}|` (`priority`) and
   the quadratic Boolean energy `E_x(z) = - ∑_i λ_i z_i Q_i(x, z)` (`energy`), flipping coordinate
   `i` from `false` to `true` changes `E_x` by
   `-λ_i Q_i(x, z) - ∑_{j > i} λ_j b_{j, i} z_j` (`energy_update_true_sub_false`). Because the
   later-gate sum has magnitude at most `λ_i - 1` while `|λ_i Q_i(x, z)| ≥ λ_i`, the
   energy-decreasing direction of every cube edge at coordinate `i` agrees strictly (by at least
   `1`) with gate `i`'s local threshold rule (`energy_le_update_not_iff`). Consequently, on every
   subcube face `(fixed, val)`, there is a unique sink under single-coordinate flips, equal to the
   face-restricted topological evaluation (`isSinkOnFace_iff_eq_faceEval`,
   `existsUnique_isSinkOnFace`), and a topological sweep reaches it in `g` coordinate steps
   (`sweep_eq_faceEval`).

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.boolSign`: `{false, true} → {-1, 1} ⊂ ℝ`.
* `Cslib.Circuits.Boolean.WeightedThreshold.StrictMarginProgram`: straight-line threshold program
  with strictly lower-triangular gate weights and unit score margin `|Q_i(x, z)| ≥ 1`.
* `Cslib.Circuits.Boolean.WeightedThreshold.StrictMarginProgram.inputSum`, `.internalSum`,
  `.score`, `.faceStep`, `.sweep`, `.faceEval`, `.eval`, `.ofProgram`: gate sums and scores,
  topological coordinate sweep, face evaluation, full evaluation, and conversion from `Program`.
* `Cslib.Circuits.Boolean.WeightedThreshold.StrictMarginProgram.inTranscriptCell`, `.leftSupply`,
  `.rightDemand`, `.ilpValid`: transcript cell, split-dominance vectors, and ILP inequalities.
* `Cslib.Circuits.Boolean.WeightedThreshold.StrictMarginProgram.priority`, `.energy`,
  `.IsSinkOnFace`: backwards positive priorities, quadratic Boolean energy, and cube-face sinks.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.StrictMarginProgram.existsUnique_ilpValid`:
  unique valid ILP transcript.
* `Cslib.Circuits.Boolean.WeightedThreshold.StrictMarginProgram.sum_inTranscriptCell_ite`:
  disjoint-support indicator expansion recovering the output bit.
* `Cslib.Circuits.Boolean.WeightedThreshold.StrictMarginProgram.inTranscriptCell_iff_eq_eval`,
  `.existsUnique_inTranscriptCell`: unambiguous transcript cell characterization and partition.
* `Cslib.Circuits.Boolean.WeightedThreshold.StrictMarginProgram.inTranscriptCell_iff_dominance`,
  `.ilpValid_iff_eq_eval`: coordinatewise dominance and unique-extension ILP characterizations.
* `Cslib.Circuits.Boolean.WeightedThreshold.StrictMarginProgram.energy_update_true_sub_false`:
  exact coordinate-flip energy difference (equation (27)).
* `Cslib.Circuits.Boolean.WeightedThreshold.StrictMarginProgram.isSinkOnFace_iff_eq_faceEval`,
  `.existsUnique_isSinkOnFace`, `.isSink_iff_eq_eval`: unique sink on every cube face and on the
  whole cube (Theorem 11.1).
* `Cslib.Circuits.Boolean.WeightedThreshold.StrictMarginProgram.sweep_eq_faceEval`,
  `.energy_sweep_le`: topological coordinate sweep reaches the unique sink in `g` steps with
  nonincreasing energy when started on the face.
* `Cslib.Circuits.Boolean.WeightedThreshold.StrictMarginProgram.priority_le_pow`: exponential upper
  bound `λ_i ≤ (W + 1) ^ (g - 1 - i)` under weight bound `|b_{j, i}| ≤ W`.

## References

* [*Threshold Circuits as Decision Trees and Finite-State Programs*, Sections 10 and 11]
  [ThresholdCircuitRepresentations2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset

variable {n g : ℕ}

/-- Sign `2 z - 1 ∈ {-1, 1}` of a Boolean bit `z`. -/
def boolSign (b : Bool) : ℝ :=
  if b then 1 else -1

/-- The sign of `true` is `1`. -/
@[simp]
theorem boolSign_true : boolSign true = 1 := rfl

/-- The sign of `false` is `-1`. -/
@[simp]
theorem boolSign_false : boolSign false = -1 := rfl

/-- For any Boolean `b`, `boolSign b = 2 * b.toNat - 1`. -/
theorem boolSign_eq_two_mul_toNat_sub_one (b : Bool) :
    boolSign b = 2 * (b.toNat : ℝ) - 1 := by
  cases b <;> norm_num

/-- The absolute value of `boolSign b` is `1`. -/
@[simp]
theorem abs_boolSign (b : Bool) : |boolSign b| = 1 := by
  cases b <;> norm_num

/-- A straight-line threshold program on `n` Boolean inputs with `g` gates in strict unit-margin
normal form (Sections 10–11 of `[ThresholdCircuitRepresentations2026]`): gate `i` has score
`Q_i(x, z) = ∑ a, inputWeight i a * x_a + ∑ j, gateWeight i j * z_j - threshold i` with
`gateWeight i j = 0` for `i ≤ j` and `|Q_i(x, z)| ≥ 1` on every Boolean `(x, z)`. -/
structure StrictMarginProgram (n g : ℕ) where
  /-- Direct input weights `a_i` for gate `i`. -/
  inputWeight : Fin g → Fin n → ℝ
  /-- Strictly lower-triangular internal gate weights `b_{i, j}` (`0` for `i ≤ j`). -/
  gateWeight : Fin g → Fin g → ℝ
  /-- Threshold `θ_i` for gate `i`. -/
  threshold : Fin g → ℝ
  /-- Strict lower triangularity of `gateWeight`. -/
  gateWeight_eq_zero_of_le : ∀ i j : Fin g, i ≤ j → gateWeight i j = 0
  /-- Unit margin `|Q_i(x, z)| ≥ 1` on all Boolean inputs and transcripts. -/
  one_le_abs_score : ∀ (x : Fin n → Bool) (z : Fin g → Bool) (i : Fin g),
    1 ≤ |(∑ a : Fin n, inputWeight i a * (x a).toNat) +
      (∑ j : Fin g, gateWeight i j * (z j).toNat) - threshold i|

namespace StrictMarginProgram

variable (P : StrictMarginProgram n g)

/-- Direct input contribution `∑ a, a_{i, a} x_a` at gate `i`. -/
def inputSum (i : Fin g) (x : Fin n → Bool) : ℝ :=
  ∑ a : Fin n, P.inputWeight i a * (x a).toNat

/-- Internal gate contribution `∑ j, b_{i, j} z_j` at gate `i`. -/
def internalSum (i : Fin g) (z : Fin g → Bool) : ℝ :=
  ∑ j : Fin g, P.gateWeight i j * (z j).toNat

/-- Score `Q_i(x, z) = inputSum i x + internalSum i z - threshold i` at gate `i`. -/
def score (x : Fin n → Bool) (z : Fin g → Bool) (i : Fin g) : ℝ :=
  P.inputSum i x + P.internalSum i z - P.threshold i

/-- Every gate score has absolute value at least `1`. -/
private theorem one_le_abs_score' (x : Fin n → Bool) (z : Fin g → Bool) (i : Fin g) :
    1 ≤ |P.score x z i| :=
  P.one_le_abs_score x z i

/-- Every gate score is either at most `-1` or at least `1`. -/
private theorem score_le_neg_one_or_one_le (x : Fin n → Bool) (z : Fin g → Bool) (i : Fin g) :
    P.score x z i ≤ -1 ∨ 1 ≤ P.score x z i := by
  have h := P.one_le_abs_score' x z i
  rcases le_total 0 (P.score x z i) with h0 | h0
  · right
    rwa [abs_of_nonneg h0] at h
  · left
    rw [abs_of_nonpos h0] at h
    linarith

/-- No gate score vanishes. -/
theorem score_ne_zero (x : Fin n → Bool) (z : Fin g → Bool) (i : Fin g) :
    P.score x z i ≠ 0 := by
  rcases P.score_le_neg_one_or_one_le x z i with h | h <;> linarith

/-- By the unit margin, `0 < Q_i(x, z)` is equivalent to `1 ≤ Q_i(x, z)`. -/
theorem pos_score_iff_one_le (x : Fin n → Bool) (z : Fin g → Bool) (i : Fin g) :
    0 < P.score x z i ↔ 1 ≤ P.score x z i := by
  rcases P.score_le_neg_one_or_one_le x z i with h | h
  · exact ⟨fun hpos => by linarith, fun h1 => by linarith⟩
  · exact ⟨fun _ => h, fun _ => by linarith⟩

/-- By the unit margin, `0 < Q_i(x, z)` is equivalent to `0 ≤ Q_i(x, z)`. -/
theorem pos_score_iff_nonneg (x : Fin n → Bool) (z : Fin g → Bool) (i : Fin g) :
    0 < P.score x z i ↔ 0 ≤ P.score x z i := by
  rcases P.score_le_neg_one_or_one_le x z i with h | h
  · exact ⟨fun hpos => by linarith, fun h0 => by linarith⟩
  · exact ⟨fun _ => by linarith, fun _ => by linarith⟩

/-- Gate `i`'s internal sum depends only on earlier coordinates `j < i`. -/
theorem internalSum_congr_lt {z₁ z₂ : Fin g → Bool} {i : Fin g}
    (h : ∀ j : Fin g, j < i → z₁ j = z₂ j) :
    P.internalSum i z₁ = P.internalSum i z₂ := by
  apply sum_congr rfl
  intro j _
  by_cases hji : j < i
  · rw [h j hji]
  · rw [P.gateWeight_eq_zero_of_le i j (le_of_not_gt hji)]
    ring

/-- Gate `i`'s score depends only on earlier coordinates `j < i`. -/
theorem score_congr_lt (x : Fin n → Bool) {z₁ z₂ : Fin g → Bool} {i : Fin g}
    (h : ∀ j : Fin g, j < i → z₁ j = z₂ j) :
    P.score x z₁ i = P.score x z₂ i := by
  simp only [score, P.internalSum_congr_lt h]

/-- Updating coordinate `j ≥ i` leaves gate `i`'s score unchanged. -/
private theorem score_update_of_le (x : Fin n → Bool) (z : Fin g → Bool) {i j : Fin g}
    (hij : i ≤ j) (b : Bool) :
    P.score x (Function.update z j b) i = P.score x z i :=
  P.score_congr_lt x fun _ hki => Function.update_of_ne (ne_of_lt (lt_of_lt_of_le hki hij)) b z

/-! ### Topological coordinate sweep and face evaluation -/

/-- Single-coordinate update at gate `i` on the subcube face `(fixed, val)`: assign `val i` if
`i ∈ fixed`, and the local threshold rule `decide (0 < P.score x z i)` otherwise. -/
noncomputable def faceStep (fixed : Finset (Fin g)) (val : Fin g → Bool) (x : Fin n → Bool)
    (z : Fin g → Bool) (i : Fin g) : Fin g → Bool :=
  Function.update z i (if i ∈ fixed then val i else decide (0 < P.score x z i))

/-- Topological sweep of the first `k` coordinates on the subcube face `(fixed, val)`, starting
from `z`. -/
noncomputable def sweep (fixed : Finset (Fin g)) (val : Fin g → Bool) (x : Fin n → Bool)
    (z : Fin g → Bool) : ℕ → (Fin g → Bool)
  | 0 => z
  | k + 1 =>
    if hk : k < g then P.faceStep fixed val x (sweep fixed val x z k) ⟨k, hk⟩
    else sweep fixed val x z k

/-- Zero steps of `sweep` leave the initial assignment `z` unchanged. -/
@[simp]
theorem sweep_zero (fixed : Finset (Fin g)) (val : Fin g → Bool) (x : Fin n → Bool)
    (z : Fin g → Bool) :
    P.sweep fixed val x z 0 = z := rfl

private theorem sweep_succ (fixed : Finset (Fin g)) (val : Fin g → Bool) (x : Fin n → Bool)
    (z : Fin g → Bool) (k : ℕ) :
    P.sweep fixed val x z (k + 1) =
      if hk : k < g then P.faceStep fixed val x (P.sweep fixed val x z k) ⟨k, hk⟩
      else P.sweep fixed val x z k := rfl

/-- Once coordinate `i` has been swept at step `i + 1`, later sweep steps leave it unchanged. -/
private theorem sweep_eq_of_lt (fixed : Finset (Fin g)) (val : Fin g → Bool) (x : Fin n → Bool)
    (z : Fin g → Bool) {i : Fin g} {k : ℕ} (hik : i.val < k) :
    P.sweep fixed val x z k i = P.sweep fixed val x z (i.val + 1) i := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hik) with rfl | hlt
    · rfl
    · rw [P.sweep_succ]
      split_ifs with hk
      · rw [faceStep, Function.update_of_ne (Fin.ne_of_val_ne (ne_of_lt hlt)), ih hlt]
      · exact ih hlt

/-- At step `i + 1`, coordinate `i` is set according to the face rule on the state after `i`
steps. -/
private theorem sweep_succ_self (fixed : Finset (Fin g)) (val : Fin g → Bool) (x : Fin n → Bool)
    (z : Fin g → Bool) (i : Fin g) :
    P.sweep fixed val x z (i.val + 1) i =
      if i ∈ fixed then val i else decide (0 < P.score x (P.sweep fixed val x z i.val) i) := by
  simp only [P.sweep_succ, i.isLt, ↓reduceDIte, faceStep, Fin.eta, Function.update_self]

/-- After `g` sweep steps from any initial assignment `z`, every coordinate `i` satisfies the
face-restricted gate equation. -/
theorem sweep_apply (fixed : Finset (Fin g)) (val : Fin g → Bool) (x : Fin n → Bool)
    (z : Fin g → Bool) (i : Fin g) :
    P.sweep fixed val x z g i =
      if i ∈ fixed then val i else decide (0 < P.score x (P.sweep fixed val x z g) i) := by
  rw [P.sweep_eq_of_lt fixed val x z i.isLt, P.sweep_succ_self]
  congr 1
  rw [P.score_congr_lt x fun j hji => ?_]
  rw [P.sweep_eq_of_lt fixed val x z hji, P.sweep_eq_of_lt fixed val x z j.isLt]

/-- Face-restricted topological evaluation on `(fixed, val)`, fixing `z_i = val i` for `i ∈ fixed`
and evaluating free gates in topological order. -/
noncomputable def faceEval (fixed : Finset (Fin g)) (val : Fin g → Bool) (x : Fin n → Bool) :
    Fin g → Bool :=
  P.sweep fixed val x val g

/-- Full topological gate evaluation `P.eval x : Fin g → Bool` (the face with `fixed = ∅`). -/
noncomputable def eval (x : Fin n → Bool) : Fin g → Bool :=
  P.faceEval ∅ (fun _ => false) x

/-- At coordinate `i`, `faceEval` returns `val i` if `i ∈ fixed` and the threshold decision at
`faceEval` otherwise. -/
theorem faceEval_apply (fixed : Finset (Fin g)) (val : Fin g → Bool) (x : Fin n → Bool)
    (i : Fin g) :
    P.faceEval fixed val x i =
      if i ∈ fixed then val i else decide (0 < P.score x (P.faceEval fixed val x) i) :=
  P.sweep_apply fixed val x val i

/-- On a fixed coordinate `i ∈ fixed`, `faceEval` evaluates to `val i`. -/
@[simp]
theorem faceEval_of_mem {fixed : Finset (Fin g)} {val : Fin g → Bool} {x : Fin n → Bool}
    {i : Fin g} (hi : i ∈ fixed) :
    P.faceEval fixed val x i = val i := by
  rw [P.faceEval_apply]
  split_ifs
  rfl

/-- On a free coordinate `i ∉ fixed`, `faceEval` satisfies gate `i`'s local threshold equation. -/
@[simp]
theorem faceEval_of_notMem {fixed : Finset (Fin g)} {val : Fin g → Bool} {x : Fin n → Bool}
    {i : Fin g} (hi : i ∉ fixed) :
    P.faceEval fixed val x i = decide (0 < P.score x (P.faceEval fixed val x) i) := by
  rw [P.faceEval_apply]
  split_ifs
  rfl

/-- Every gate of `P.eval x` equals `decide (0 < P.score x (P.eval x) i)`. -/
theorem eval_eq (x : Fin n → Bool) (i : Fin g) :
    P.eval x i = decide (0 < P.score x (P.eval x) i) :=
  P.faceEval_of_notMem (notMem_empty i)

/-- `P.faceEval fixed val x` is the unique assignment agreeing with `val` on `fixed` and satisfying
every free gate's threshold rule. -/
theorem eq_faceEval_iff (fixed : Finset (Fin g)) (val : Fin g → Bool) (x : Fin n → Bool)
    (z : Fin g → Bool) :
    z = P.faceEval fixed val x ↔
      (∀ i ∈ fixed, z i = val i) ∧ ∀ i ∉ fixed, z i = decide (0 < P.score x z i) := by
  constructor
  · rintro rfl
    exact ⟨fun _ hi => P.faceEval_of_mem hi, fun _ hi => P.faceEval_of_notMem hi⟩
  · rintro ⟨hfix, hfree⟩
    funext i
    induction i using Fin.strong_induction_on with
    | h i ih =>
      by_cases hi : i ∈ fixed
      · rw [hfix i hi, P.faceEval_of_mem hi]
      · rw [hfree i hi, P.faceEval_of_notMem hi, P.score_congr_lt x ih]

/-- A full `g`-step topological sweep from any starting assignment `z` reaches
`P.faceEval fixed val x`. -/
@[simp]
theorem sweep_eq_faceEval (fixed : Finset (Fin g)) (val : Fin g → Bool) (x : Fin n → Bool)
    (z : Fin g → Bool) :
    P.sweep fixed val x z g = P.faceEval fixed val x := by
  rw [P.eq_faceEval_iff]
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rw [P.sweep_apply]
    split_ifs
    rfl
  · rw [P.sweep_apply]
    split_ifs
    rfl

/-- With no fixed coordinates, `P.faceEval ∅ val x` equals `P.eval x`. -/
@[simp]
theorem faceEval_empty_eq_eval (val : Fin g → Bool) (x : Fin n → Bool) :
    P.faceEval ∅ val x = P.eval x := by
  rw [eval, eq_comm, P.eq_faceEval_iff]
  exact ⟨fun _ hi => (notMem_empty _ hi).elim, fun i _ => P.faceEval_of_notMem (notMem_empty i)⟩

/-- A full `g`-step topological sweep with no fixed coordinates reaches `P.eval x`. -/
theorem sweep_empty_eq_eval (val : Fin g → Bool) (x : Fin n → Bool) (z : Fin g → Bool) :
    P.sweep ∅ val x z g = P.eval x := by
  rw [P.sweep_eq_faceEval, P.faceEval_empty_eq_eval]

/-- Construct a `StrictMarginProgram` from a `Program signature n g` whose gates satisfy the unit
margin condition. -/
def ofProgram (p : Program signature n g)
    (hmargin : ∀ (x : Fin n → Bool) (z : Fin g → Bool) (i : Fin g),
      1 ≤ |(∑ a : Fin n, WeightedThreshold.inputWeight p i a * (x a).toNat) +
        (∑ j : Fin g, WeightedThreshold.gateWeight p i j * (z j).toNat) -
        (p.lines i).op.threshold|) :
    StrictMarginProgram n g where
  inputWeight := WeightedThreshold.inputWeight p
  gateWeight := WeightedThreshold.gateWeight p
  threshold i := (p.lines i).op.threshold
  gateWeight_eq_zero_of_le := WeightedThreshold.gateWeight_eq_zero_of_le p
  one_le_abs_score := hmargin

/-- Evaluation of `ofProgram p hmargin` agrees with `p.eval interpretation`. -/
@[simp]
theorem eval_ofProgram (p : Program signature n g)
    (hmargin : ∀ (x : Fin n → Bool) (z : Fin g → Bool) (i : Fin g),
      1 ≤ |(∑ a : Fin n, WeightedThreshold.inputWeight p i a * (x a).toNat) +
        (∑ j : Fin g, WeightedThreshold.gateWeight p i j * (z j).toNat) -
        (p.lines i).op.threshold|)
    (x : Fin n → Bool) :
    (ofProgram p hmargin).eval x = p.eval interpretation x := by
  symm
  rw [eval, eq_faceEval_iff]
  refine ⟨fun _ hi => (notMem_empty _ hi).elim, fun i _ => ?_⟩
  rw [eval_gate_eq, Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff,
    (ofProgram p hmargin).pos_score_iff_nonneg]
  simp [ofProgram, score, inputSum, internalSum, sub_nonneg]

/-! ### Section 10: Unambiguous cells, coordinatewise dominance, and unique-extension ILP -/

/-- Consistency cell predicate `x ∈ P_z` (equation (23)): `(2 z_i - 1) Q_i(x, z) ≥ 1` for every
gate `i`. -/
def inTranscriptCell (x : Fin n → Bool) (z : Fin g → Bool) : Prop :=
  ∀ i : Fin g, 1 ≤ boolSign (z i) * P.score x z i

/-- By the unit margin, `1 ≤ boolSign (z i) * P.score x z i` holds iff `z i` agrees with gate `i`'s
threshold decision. -/
theorem one_le_boolSign_mul_score_iff {x : Fin n → Bool} {z : Fin g → Bool} {i : Fin g} :
    1 ≤ boolSign (z i) * P.score x z i ↔ z i = decide (0 < P.score x z i) := by
  rcases P.score_le_neg_one_or_one_le x z i with hle | hge <;> cases hzi : z i <;>
    simp only [boolSign_false, boolSign_true, one_mul, neg_mul, Bool.false_eq, Bool.true_eq,
      decide_eq_false_iff_not, decide_eq_true_iff, not_lt]
  · exact ⟨fun _ => by linarith, fun _ => by linarith⟩
  · exact ⟨fun h => by linarith, fun h => by linarith⟩
  · exact ⟨fun h => by linarith, fun h => by linarith⟩
  · exact ⟨fun _ => by linarith, fun _ => by linarith⟩

/-- **Unambiguous cell theorem**: `x` belongs to the consistency cell of `z` if and only if `z` is
the unique circuit transcript `P.eval x`. -/
theorem inTranscriptCell_iff_eq_eval (x : Fin n → Bool) (z : Fin g → Bool) :
    P.inTranscriptCell x z ↔ z = P.eval x := by
  simp only [inTranscriptCell, P.one_le_boolSign_mul_score_iff]
  rw [eval, P.eq_faceEval_iff]
  simp

/-- The consistency cells `{P_z}_{z : Fin g → Bool}` partition the input cube: every input `x`
belongs to the cell of a unique transcript `z`. -/
theorem existsUnique_inTranscriptCell (x : Fin n → Bool) :
    ∃! z : Fin g → Bool, P.inTranscriptCell x z := by
  refine ⟨P.eval x, (P.inTranscriptCell_iff_eq_eval x _).mpr rfl, fun z hz => ?_⟩
  exact (P.inTranscriptCell_iff_eq_eval x z).mp hz

/-- **Disjoint-support indicator expansion** (equation (24)): summing the cell indicators over all
transcripts with `z out = true` recovers the output bit `(P.eval x out).toNat`. -/
theorem sum_inTranscriptCell_ite (x : Fin n → Bool) [DecidablePred (P.inTranscriptCell x)]
    (out : Fin g) :
    (∑ z : Fin g → Bool, if P.inTranscriptCell x z ∧ z out = true then (1 : ℕ) else 0) =
      (P.eval x out).toNat := by
  have hcongr : ∀ z : Fin g → Bool,
      (if P.inTranscriptCell x z ∧ z out = true then (1 : ℕ) else 0) =
        if z = P.eval x then (P.eval x out).toNat else 0 := by
    intro z
    by_cases hz : z = P.eval x
    · subst hz
      have hcell : P.inTranscriptCell x (P.eval x) := (P.inTranscriptCell_iff_eq_eval x _).mpr rfl
      cases P.eval x out <;> simp [hcell]
    · have hnot : ¬ P.inTranscriptCell x z := by
        rwa [P.inTranscriptCell_iff_eq_eval]
      simp [hz, hnot]
  simp [hcongr]

/-- Left-half supply vector `α_z(u)_i = σ_i ∑_{a ∈ U} a_{i, a} x_a` for an input split `U`. -/
def leftSupply (U : Finset (Fin n)) (z : Fin g → Bool) (x : Fin n → Bool) (i : Fin g) : ℝ :=
  boolSign (z i) * ∑ a ∈ U, P.inputWeight i a * (x a).toNat

/-- Right-half demand vector `β_z(v)_i = 1 - σ_i (∑_{a ∈ Uᶜ} a_{i, a} x_a + internalSum i z - θ_i)`
for an input split `U`. -/
def rightDemand (U : Finset (Fin n)) (z : Fin g → Bool) (x : Fin n → Bool) (i : Fin g) : ℝ :=
  1 - boolSign (z i) *
    ((∑ a ∈ Uᶜ, P.inputWeight i a * (x a).toNat) + P.internalSum i z - P.threshold i)

/-- **Coordinatewise dominance characterization**: across any input split `U`, `x` belongs to the
consistency cell of `z` iff `rightDemand U z x i ≤ leftSupply U z x i` for every gate `i`. -/
theorem inTranscriptCell_iff_dominance (U : Finset (Fin n)) (x : Fin n → Bool)
    (z : Fin g → Bool) :
    P.inTranscriptCell x z ↔ ∀ i : Fin g, P.rightDemand U z x i ≤ P.leftSupply U z x i := by
  refine forall_congr' fun i => ?_
  have hsplit : P.inputSum i x =
      (∑ a ∈ U, P.inputWeight i a * (x a).toNat) +
        ∑ a ∈ Uᶜ, P.inputWeight i a * (x a).toNat := by
    simpa [inputSum] using (sum_add_sum_compl U fun a => P.inputWeight i a * (x a).toNat).symm
  simp only [rightDemand, leftSupply, score, hsplit]
  constructor <;> intro h <;> linarith

/-- Linear inequalities of the unique-extension integer linear program (equation (25)) with score
upper bounds `M : Fin g → ℝ`. -/
def ilpValid (M : Fin g → ℝ) (x : Fin n → Bool) (z : Fin g → Bool) : Prop :=
  ∀ i : Fin g,
    1 - (M i + 1) * (1 - (z i).toNat) ≤ P.score x z i ∧
      P.score x z i ≤ -1 + (M i + 1) * (z i).toNat

/-- Given score bounds `|P.score x z i| ≤ M i`, the ILP inequalities at gate `i` are equivalent to
`1 ≤ boolSign (z i) * P.score x z i`. -/
theorem ilpValid_gate_iff {M : Fin g → ℝ} {x : Fin n → Bool} {z : Fin g → Bool} {i : Fin g}
    (hM : |P.score x z i| ≤ M i) :
    (1 - (M i + 1) * (1 - (z i).toNat) ≤ P.score x z i ∧
      P.score x z i ≤ -1 + (M i + 1) * (z i).toNat) ↔
      1 ≤ boolSign (z i) * P.score x z i := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hM
  cases z i <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.cast_zero, Nat.cast_one,
    sub_zero, sub_self, mul_zero, mul_one, add_zero, boolSign_false, boolSign_true, one_mul,
    neg_mul] <;> constructor <;> intro h
  · linarith
  · exact ⟨by linarith, by linarith⟩
  · exact h.1
  · exact ⟨h, by linarith⟩

/-- **Unique-extension ILP theorem** (equation (25)): when `|P.score x z i| ≤ M i` for every gate
`i`, `P.ilpValid M x z` holds if and only if `z = P.eval x`. -/
theorem ilpValid_iff_eq_eval {M : Fin g → ℝ} {x : Fin n → Bool} {z : Fin g → Bool}
    (hM : ∀ i : Fin g, |P.score x z i| ≤ M i) :
    P.ilpValid M x z ↔ z = P.eval x := by
  rw [← P.inTranscriptCell_iff_eq_eval]
  exact forall_congr' fun i => P.ilpValid_gate_iff (hM i)

/-- Every input `x` has a unique transcript `z` satisfying `P.ilpValid M x z`. -/
theorem existsUnique_ilpValid {M : Fin g → ℝ} {x : Fin n → Bool}
    (hM : ∀ (z : Fin g → Bool) (i : Fin g), |P.score x z i| ≤ M i) :
    ∃! z : Fin g → Bool, P.ilpValid M x z := by
  refine ⟨P.eval x, (P.ilpValid_iff_eq_eval (hM _)).mpr rfl, fun z hz => ?_⟩
  exact (P.ilpValid_iff_eq_eval (hM z)).mp hz

/-! ### Section 11: Backwards priorities, quadratic Boolean energy, and unique sinks -/

/-- Backwards positive priority `λ_i = 1 + ∑_{j > i} λ_j |b_{j, i}|`. -/
def priority (i : Fin g) : ℝ :=
  1 + ∑ j ∈ univ.attach,
    if _ : i < j.1 then priority j.1 * |P.gateWeight j.1 i| else 0
termination_by g - 1 - i.val
decreasing_by
  have := j.1.isLt
  omega

/-- Unfolding equation for the backwards priority `P.priority i`. -/
private theorem priority_eq (i : Fin g) :
    P.priority i = 1 + ∑ j : Fin g, if i < j then P.priority j * |P.gateWeight j i| else 0 := by
  rw [priority]
  congr 1
  exact sum_attach univ fun j => if i < j then P.priority j * |P.gateWeight j i| else 0

/-- Every gate priority is at least `1`. -/
private theorem one_le_priority (i : Fin g) : 1 ≤ P.priority i := by
  suffices ∀ k : ℕ, ∀ i : Fin g, g - 1 - i.val = k → 1 ≤ P.priority i from this _ i rfl
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro i hik
    rw [P.priority_eq]
    suffices 0 ≤ ∑ j : Fin g, if i < j then P.priority j * |P.gateWeight j i| else 0 by linarith
    apply sum_nonneg
    intro j _
    split_ifs with hij
    · have hj : 1 ≤ P.priority j := ih (g - 1 - j.val) (by have := j.isLt; omega) j rfl
      exact mul_nonneg (by linarith) (abs_nonneg _)
    · exact le_rfl

/-- Every gate priority is strictly positive. -/
theorem priority_pos (i : Fin g) : 0 < P.priority i :=
  lt_of_lt_of_le zero_lt_one (P.one_le_priority i)

/-- The total contribution of later gates `j > i` to coordinate `i`'s flip difference has magnitude
at most `P.priority i - 1`. -/
private theorem abs_sum_later_le_priority_sub_one (z : Fin g → Bool) (i : Fin g) :
    |∑ j : Fin g, if i < j then P.priority j * P.gateWeight j i * (z j).toNat else 0| ≤
      P.priority i - 1 := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hle : (∑ j : Fin g, |if i < j then P.priority j * P.gateWeight j i * (z j).toNat else 0|) ≤
      ∑ j : Fin g, if i < j then P.priority j * |P.gateWeight j i| else 0 := by
    apply sum_le_sum
    intro j _
    split_ifs with hij
    · rw [abs_mul, abs_mul, abs_of_pos (P.priority_pos j)]
      have hz : |((z j).toNat : ℝ)| ≤ 1 := by cases z j <;> norm_num
      exact mul_le_of_le_one_right (mul_nonneg (le_of_lt (P.priority_pos j)) (abs_nonneg _)) hz
    · simp
  linarith [P.priority_eq i]

private theorem one_add_mul_sum_geom (W : ℝ) (m : ℕ) :
    1 + W * (∑ k ∈ range m, (W + 1) ^ k) = (W + 1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, mul_add, ← add_assoc, ih, pow_succ]
    ring

/-- If `|b_{j, i}| ≤ W` for all `i < j`, then `P.priority i ≤ (W + 1) ^ (g - 1 - i)`. -/
theorem priority_le_pow {W : ℝ} (hW0 : 0 ≤ W)
    (hW : ∀ j i : Fin g, i < j → |P.gateWeight j i| ≤ W) (i : Fin g) :
    P.priority i ≤ (W + 1) ^ (g - 1 - i.val) := by
  suffices ∀ m : ℕ, ∀ i : Fin g, g - 1 - i.val = m → P.priority i ≤ (W + 1) ^ m from this _ i rfl
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro i him
    rw [P.priority_eq, ← one_add_mul_sum_geom W m]
    have hsum : (∑ j : Fin g, if i < j then P.priority j * |P.gateWeight j i| else 0) ≤
        ∑ j ∈ univ.filter (fun j : Fin g => i < j), W * (W + 1) ^ (g - 1 - j.val) := by
      rw [← sum_filter]
      apply sum_le_sum
      intro j hj
      have hij : i < j := (mem_filter.mp hj).2
      have hjp : P.priority j ≤ (W + 1) ^ (g - 1 - j.val) :=
        ih (g - 1 - j.val) (by have := j.isLt; omega) j rfl
      calc P.priority j * |P.gateWeight j i|
          ≤ (W + 1) ^ (g - 1 - j.val) * W :=
            mul_le_mul hjp (hW j i hij) (abs_nonneg _) (pow_nonneg (by linarith) _)
        _ = W * (W + 1) ^ (g - 1 - j.val) := mul_comm _ _
    let f : Fin g → ℕ := fun j => g - 1 - j.val
    have hmaps : ∀ j ∈ univ.filter (fun j : Fin g => i < j), f j ∈ range m := by
      intro j hj
      have hij : i < j := (mem_filter.mp hj).2
      simp only [f, mem_range]
      have := j.isLt
      omega
    have hinj_on : Set.InjOn f (univ.filter fun j : Fin g => i < j) := by
      intro j₁ _ j₂ _ heq
      have h₁ := j₁.isLt
      have h₂ := j₂.isLt
      simp only [f] at heq
      exact Fin.ext (by omega)
    have hinj : (∑ j ∈ univ.filter (fun j : Fin g => i < j), W * (W + 1) ^ f j) ≤
        W * ∑ k ∈ range m, (W + 1) ^ k := by
      calc (∑ j ∈ univ.filter (fun j : Fin g => i < j), W * (W + 1) ^ f j)
          = ∑ k ∈ (univ.filter (fun j : Fin g => i < j)).image f, W * (W + 1) ^ k :=
            (sum_image (f := fun k => W * (W + 1) ^ k) hinj_on).symm
        _ ≤ ∑ k ∈ range m, W * (W + 1) ^ k := by
            apply sum_le_sum_of_subset_of_nonneg (image_subset_iff.mpr hmaps)
            intro k _ _
            exact mul_nonneg hW0 (pow_nonneg (by linarith) _)
        _ = W * ∑ k ∈ range m, (W + 1) ^ k := (mul_sum _ _ _).symm
    exact add_le_add_right (hsum.trans hinj) 1

/-- Quadratic Boolean energy `E_x(z) = - ∑ i, λ_i z_i Q_i(x, z)` (equation (26)). -/
def energy (x : Fin n → Bool) (z : Fin g → Bool) : ℝ :=
  - ∑ i : Fin g, P.priority i * (z i).toNat * P.score x z i

private theorem internalSum_update_true_sub_false (z : Fin g → Bool) (j i : Fin g) :
    P.internalSum j (Function.update z i true) - P.internalSum j (Function.update z i false) =
      P.gateWeight j i := by
  simp only [internalSum, ← sum_sub_distrib, ← mul_sub]
  rw [← add_sum_erase _ _ (mem_univ i)]
  have hzero : ∑ k ∈ univ.erase i, P.gateWeight j k *
      (((Function.update z i true k).toNat : ℝ) - (Function.update z i false k).toNat) = 0 := by
    apply sum_eq_zero
    intro k hk
    have hki : k ≠ i := ne_of_mem_erase hk
    simp [Function.update_of_ne hki]
  rw [hzero, add_zero]
  simp

private theorem score_update_true_sub_false (x : Fin n → Bool) (z : Fin g → Bool) (j i : Fin g) :
    P.score x (Function.update z i true) j - P.score x (Function.update z i false) j =
      P.gateWeight j i := by
  have := P.internalSum_update_true_sub_false z j i
  simp only [score]
  linarith

/-- **Coordinate-flip energy identity** (equation (27)): changing `z_i` from `false` to `true`
changes `P.energy x` by `-λ_i Q_i(x, z) - ∑_{j > i} λ_j b_{j, i} z_j`. -/
theorem energy_update_true_sub_false (x : Fin n → Bool) (z : Fin g → Bool) (i : Fin g) :
    P.energy x (Function.update z i true) - P.energy x (Function.update z i false) =
      - P.priority i * P.score x z i -
        ∑ j : Fin g, if i < j then P.priority j * P.gateWeight j i * (z j).toNat else 0 := by
  have hsum : (∑ j : Fin g, P.priority j * ((Function.update z i true j).toNat : ℝ) *
        P.score x (Function.update z i true) j) -
      (∑ j : Fin g, P.priority j * ((Function.update z i false j).toNat : ℝ) *
        P.score x (Function.update z i false) j) =
      P.priority i * P.score x z i +
        ∑ j : Fin g, if i < j then P.priority j * P.gateWeight j i * (z j).toNat else 0 := by
    rw [← sum_sub_distrib, ← add_sum_erase _ _ (mem_univ i),
      ← add_sum_erase _
        (fun j => if i < j then P.priority j * P.gateWeight j i * (z j).toNat else 0)
        (mem_univ i)]
    have hi : P.priority i * ((Function.update z i true i).toNat : ℝ) *
          P.score x (Function.update z i true) i -
        P.priority i * ((Function.update z i false i).toNat : ℝ) *
          P.score x (Function.update z i false) i =
        P.priority i * P.score x z i := by
      rw [P.score_update_of_le x z le_rfl true, P.score_update_of_le x z le_rfl false]
      simp
    have hrest : (∑ j ∈ univ.erase i,
        (P.priority j * ((Function.update z i true j).toNat : ℝ) *
            P.score x (Function.update z i true) j -
          P.priority j * ((Function.update z i false j).toNat : ℝ) *
            P.score x (Function.update z i false) j)) =
        ∑ j ∈ univ.erase i,
          if i < j then P.priority j * P.gateWeight j i * (z j).toNat else 0 := by
      apply sum_congr rfl
      intro j hj
      have hji : j ≠ i := ne_of_mem_erase hj
      rw [Function.update_of_ne hji, Function.update_of_ne hji, ← mul_sub,
        P.score_update_true_sub_false x z j i]
      split_ifs with hij
      · ring
      · rw [P.gateWeight_eq_zero_of_le j i (le_of_not_gt hij)]
        ring
    rw [hi, hrest]
    simp
  unfold energy
  linarith

/-- When `0 < P.score x z i`, setting `z_i = true` decreases the energy by at least `1` relative to
`z_i = false`. -/
private theorem energy_update_true_add_one_le_false {x : Fin n → Bool} {z : Fin g → Bool}
    {i : Fin g}
    (h : 0 < P.score x z i) :
    P.energy x (Function.update z i true) + 1 ≤ P.energy x (Function.update z i false) := by
  have h1 : 1 ≤ P.score x z i := (P.pos_score_iff_one_le x z i).mp h
  have hp : P.priority i ≤ P.priority i * P.score x z i :=
    le_mul_of_one_le_right (le_of_lt (P.priority_pos i)) h1
  have hlat := (abs_le.mp (P.abs_sum_later_le_priority_sub_one z i)).1
  have hdiff := P.energy_update_true_sub_false x z i
  linarith

/-- When `¬ (0 < P.score x z i)`, setting `z_i = false` decreases the energy by at least `1`
relative to `z_i = true`. -/
private theorem energy_update_false_add_one_le_true {x : Fin n → Bool} {z : Fin g → Bool}
    {i : Fin g}
    (h : ¬ 0 < P.score x z i) :
    P.energy x (Function.update z i false) + 1 ≤ P.energy x (Function.update z i true) := by
  have h1 : P.score x z i ≤ -1 :=
    (P.score_le_neg_one_or_one_le x z i).resolve_right fun hge => h (by linarith)
  have hp : P.priority i * P.score x z i ≤ - P.priority i := by
    have := mul_le_mul_of_nonneg_left h1 (le_of_lt (P.priority_pos i))
    linarith
  have hlat := (abs_le.mp (P.abs_sum_later_le_priority_sub_one z i)).2
  have hdiff := P.energy_update_true_sub_false x z i
  linarith

/-- Flipping coordinate `i` does not decrease `P.energy x` if and only if `z i` already satisfies
gate `i`'s local threshold rule. -/
theorem energy_le_update_not_iff (x : Fin n → Bool) (z : Fin g → Bool) (i : Fin g) :
    P.energy x z ≤ P.energy x (Function.update z i (!(z i))) ↔
      z i = decide (0 < P.score x z i) := by
  by_cases hpos : 0 < P.score x z i
  · have hstep := P.energy_update_true_add_one_le_false hpos
    cases hzi : z i
    · have h0 : P.energy x (Function.update z i false) = P.energy x z := by
        rw [← hzi, Function.update_eq_self]
      rw [decide_eq_true hpos]
      exact ⟨fun hle => by simp only [Bool.not_false] at hle; linarith, fun h => Bool.noConfusion h⟩
    · have h1 : P.energy x (Function.update z i true) = P.energy x z := by
        rw [← hzi, Function.update_eq_self]
      rw [decide_eq_true hpos]
      exact ⟨fun _ => rfl, fun _ => by simp only [Bool.not_true]; linarith⟩
  · have hstep := P.energy_update_false_add_one_le_true hpos
    cases hzi : z i
    · have h0 : P.energy x (Function.update z i false) = P.energy x z := by
        rw [← hzi, Function.update_eq_self]
      rw [decide_eq_false hpos]
      exact ⟨fun _ => rfl, fun _ => by simp only [Bool.not_false]; linarith⟩
    · have h1 : P.energy x (Function.update z i true) = P.energy x z := by
        rw [← hzi, Function.update_eq_self]
      rw [decide_eq_false hpos]
      exact ⟨fun hle => by simp only [Bool.not_true] at hle; linarith, fun h => Bool.noConfusion h⟩

/-- Flipping coordinate `i` strictly decreases `P.energy x` if and only if `z i` violates gate
`i`'s local threshold rule. -/
theorem energy_update_not_lt_iff (x : Fin n → Bool) (z : Fin g → Bool) (i : Fin g) :
    P.energy x (Function.update z i (!(z i))) < P.energy x z ↔
      z i ≠ decide (0 < P.score x z i) := by
  rw [← not_le, P.energy_le_update_not_iff]

/-- `z` is a sink on the cube face `(fixed, val)` if `z` agrees with `val` on `fixed` and no
single free-coordinate flip strictly decreases `P.energy x`. -/
def IsSinkOnFace (fixed : Finset (Fin g)) (val : Fin g → Bool) (x : Fin n → Bool)
    (z : Fin g → Bool) : Prop :=
  (∀ i ∈ fixed, z i = val i) ∧
    ∀ i ∉ fixed, P.energy x z ≤ P.energy x (Function.update z i (!(z i)))

/-- **Theorem 11.1 (Unique sink on every cube face)**: `z` is a sink on the subcube face
`(fixed, val)` if and only if `z = P.faceEval fixed val x`. -/
theorem isSinkOnFace_iff_eq_faceEval (fixed : Finset (Fin g)) (val : Fin g → Bool)
    (x : Fin n → Bool) (z : Fin g → Bool) :
    P.IsSinkOnFace fixed val x z ↔ z = P.faceEval fixed val x := by
  simp only [IsSinkOnFace, P.energy_le_update_not_iff, ← P.eq_faceEval_iff]

/-- Every subcube face `(fixed, val)` has a unique sink under `P.energy x`. -/
theorem existsUnique_isSinkOnFace (fixed : Finset (Fin g)) (val : Fin g → Bool)
    (x : Fin n → Bool) :
    ∃! z : Fin g → Bool, P.IsSinkOnFace fixed val x z := by
  refine ⟨P.faceEval fixed val x, (P.isSinkOnFace_iff_eq_faceEval fixed val x _).mpr rfl,
    fun z hz => ?_⟩
  exact (P.isSinkOnFace_iff_eq_faceEval fixed val x z).mp hz

/-- **Unique sink on the whole cube**: on the unrestricted cube (`fixed = ∅`), `z` is a sink under
`P.energy x` if and only if `z` is the circuit transcript `P.eval x`. -/
theorem isSink_iff_eq_eval (x : Fin n → Bool) (z : Fin g → Bool) :
    P.IsSinkOnFace ∅ (fun _ => false) x z ↔ z = P.eval x :=
  P.isSinkOnFace_iff_eq_faceEval ∅ (fun _ => false) x z

/-- Updating coordinate `i` via `P.faceStep fixed val x` does not increase `P.energy x` whenever
`z` already agrees with `val` at `i` if `i ∈ fixed`. -/
private theorem energy_faceStep_le {fixed : Finset (Fin g)} {val : Fin g → Bool} {x : Fin n → Bool}
    {z : Fin g → Bool} {i : Fin g} (hfix : i ∈ fixed → z i = val i) :
    P.energy x (P.faceStep fixed val x z i) ≤ P.energy x z := by
  unfold faceStep
  split_ifs with hi
  · rw [← hfix hi, Function.update_eq_self]
  · by_cases hpos : 0 < P.score x z i
    · rw [decide_eq_true hpos]
      cases hzi : z i
      · have hstep := P.energy_update_true_add_one_le_false hpos
        have h0 : P.energy x (Function.update z i false) = P.energy x z := by
          rw [← hzi, Function.update_eq_self]
        linarith
      · have h1 : Function.update z i true = z := by rw [← hzi, Function.update_eq_self]
        rw [h1]
    · rw [decide_eq_false hpos]
      cases hzi : z i
      · have h0 : Function.update z i false = z := by rw [← hzi, Function.update_eq_self]
        rw [h0]
      · have hstep := P.energy_update_false_add_one_le_true hpos
        have h1 : P.energy x (Function.update z i true) = P.energy x z := by
          rw [← hzi, Function.update_eq_self]
        linarith

/-- Sweeping preserves agreement with `val` on `fixed`. -/
theorem sweep_mem_fixed {fixed : Finset (Fin g)} {val : Fin g → Bool} {x : Fin n → Bool}
    {z : Fin g → Bool} (hfix : ∀ i ∈ fixed, z i = val i) (k : ℕ) {i : Fin g} (hi : i ∈ fixed) :
    P.sweep fixed val x z k i = val i := by
  induction k with
  | zero => exact hfix i hi
  | succ k ih =>
    rw [P.sweep_succ]
    split_ifs with hk
    · unfold faceStep
      by_cases hik : i = ⟨k, hk⟩
      · subst hik
        simp [hi]
      · rw [Function.update_of_ne hik, ih]
    · exact ih

/-- Starting from any assignment `z` on the face `(fixed, val)`, the topological coordinate sweep
monotonically decreases (or preserves) `P.energy x` at every step. -/
theorem energy_sweep_le {fixed : Finset (Fin g)} {val : Fin g → Bool} {x : Fin n → Bool}
    {z : Fin g → Bool} (hfix : ∀ i ∈ fixed, z i = val i) (k : ℕ) :
    P.energy x (P.sweep fixed val x z k) ≤ P.energy x z := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [P.sweep_succ]
    split_ifs with hk
    · exact (P.energy_faceStep_le fun hi => P.sweep_mem_fixed hfix k hi).trans ih
    · exact ih

end StrictMarginProgram

end Cslib.Circuits.Boolean.WeightedThreshold
