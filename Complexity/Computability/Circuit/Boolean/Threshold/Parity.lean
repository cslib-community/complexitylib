/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.ConstDepth
public import Complexity.Computability.Circuit.Boolean.Threshold
public import Complexity.Computability.Circuit.Simulation
public import Complexity.Foundations.Data.BitString.Parity.Weight
import Mathlib.Algebra.BigOperators.Fin

/-!
# Parity in depth two with threshold gates

Every symmetric function has threshold circuits of depth two and linear size
[Hajnal et al., Proposition 2.1][HMPST1993]. For parity, alternating signs give such a circuit with
`n + 1` threshold gates. On `n` bits, let `g_j`, for `j < n`, be the threshold gate "at least
`j + 1` of the bits are true". If `w` of the bits are true, `g_j` is true exactly when `j < w`.
Negating `g_j` for every odd `j`, exactly `n / 2 + w % 2` of the `n` signed values are true
(`Threshold.weight_signedLayer`), so the threshold gate "at least `n / 2 + 1` of them are true"
computes the parity of `w`.

This circuit (`Threshold.parityCircuit`) has `n + 1` threshold gates and threshold depth two, the
`n / 2` negations being free; with them it has `n + n / 2 + 1` gates and depth three
(`Threshold.exists_computes_parity`). So parity has threshold circuits of polynomial size and
constant depth (`Threshold.parity_mem_constDepth`), and is in TC⁰
(`Cslib.Circuits.Boolean.parity_mem_TC0`).

## Main definitions

* `Cslib.Circuits.Boolean.Threshold.negIf`,
  `Cslib.Circuits.Boolean.Threshold.signedLayerGate`,
  `Cslib.Circuits.Boolean.Threshold.parityCircuit`: the depth-two threshold circuit for parity.

## Main results

* `Cslib.Circuits.Boolean.Threshold.exists_computes_parity`: the parity of `n` bits has a circuit
  of `n + 1` threshold gates and threshold depth two.
* `Cslib.Circuits.Boolean.Threshold.parity_mem_constDepth`: parity has threshold circuits of
  polynomial size and constant depth.

## References

* [A. Hajnal, W. Maass, P. Pudlák, M. Szegedy, G. Turán, *Threshold circuits of bounded
  depth*][HMPST1993]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Threshold

open Finset BitString

variable {n : ℕ}

/-- A negation if `b` is `true`, and no gate otherwise. -/
def negIf : Bool → Circuit signature 1 1
  | true => Circuit.oneGate (σ := signature) .not id
  | false => Circuit.id signature 1

/-- Evaluating `negIf b` XORs the input bit with `b`. -/
@[simp] theorem eval_negIf (b : Bool) (y : Fin 1 → Bool) (o : Fin 1) :
    (negIf b).eval interpretation y o = (b ^^ y 0) := by
  cases b
  · simp [negIf, Subsingleton.elim o 0]
  · simp [negIf]

private theorem cost_program_negIf (b : Bool) : (negIf b).program.cost thresholdCost = 0 := by
  cases b <;> rfl

/-- The gate count of `negIf b` is `b.toNat`. -/
@[simp] theorem size_negIf (b : Bool) : (negIf b).size = b.toNat := by
  cases b <;> rfl

/-- Under `thresholdCost`, `negIf b` has weighted depth `0`. -/
@[simp] theorem depthWith_negIf (b : Bool) : (negIf b).depthWith thresholdCost = 0 := by
  cases b <;> simp [negIf]

/-- The unweighted depth of `negIf b` is at most `1`. -/
theorem depth_negIf_le (b : Bool) : (negIf b).depth ≤ 1 := by
  cases b <;> simp [negIf]

/-- The `j`-th input of the output gate of `parityCircuit n`: the threshold gate "at least `j + 1`
of the `n` bits are true", negated when `j` is odd. -/
def signedLayerGate (n : ℕ) (j : Fin n) : Circuit signature n 1 :=
  (negIf (decide (j.val % 2 = 1))).comp
    (Circuit.oneGate (σ := signature) (.threshold n (j + 1)) id)

/-- **The depth-two threshold circuit for parity**: the threshold gate "at least `n / 2 + 1` of
them are true" on the signed layer gates `signedLayerGate n j`. -/
def parityCircuit (n : ℕ) : Circuit signature n 1 :=
  (Circuit.oneGate (σ := signature) (.threshold n (n / 2 + 1)) id).comp
    (Circuit.pi (signedLayerGate n))

/-- Evaluating `signedLayerGate n j` on `x` returns `threshold n (j + 1) x` negated when `j` is
odd. -/
theorem eval_signedLayerGate (j : Fin n) (x : BitString n) :
    (signedLayerGate n j).eval interpretation x 0 =
      (decide (j.val % 2 = 1) ^^ threshold n (j + 1) x) := by
  simp [signedLayerGate]

/-- Among the signed layer values `(j % 2 = 1) ^^ (j < w)` for `j < n`, exactly `n / 2 + w % 2`
are true when `w ≤ n`. -/
private theorem sum_signed_toNat (n w : ℕ) :
    ∑ j ∈ range n, (decide (j % 2 = 1) ^^ decide (j + 1 ≤ w)).toNat =
      if w ≤ n then n / 2 + w % 2 else (n + 1) / 2 := by
  induction n with
  | zero => by_cases hw : w = 0 <;> simp [hw]
  | succ n ih =>
    rw [sum_range_succ, ih]
    by_cases h₁ : n % 2 = 1 <;> by_cases h₂ : n + 1 ≤ w <;>
      simp only [h₁, h₂, decide_true, decide_false, Bool.xor_true, Bool.xor_false, Bool.not_true,
        Bool.not_false, Bool.toNat_true, Bool.toNat_false] <;> split_ifs <;> omega

/-- If `w` of the bits are true, exactly `n / 2 + w % 2` of the signed layer values are true. -/
theorem weight_signedLayer (x : BitString n) :
    weight (fun j : Fin n => decide (j.val % 2 = 1) ^^ threshold n (j + 1) x) =
      n / 2 + weight x % 2 := by
  have h := weight_le_length x
  rw [weight_eq_sum_toNat]
  simp only [threshold_apply]
  rw [Fin.sum_univ_eq_sum_range (fun j => (decide (j % 2 = 1) ^^ decide (j + 1 ≤ weight x)).toNat),
    sum_signed_toNat, ite_eq_left h]

/-- The circuit computes parity. -/
theorem computes_parityCircuit : (parityCircuit n).Computes interpretation (single (parity n)) := by
  intro x
  funext o
  simp only [parityCircuit, Circuit.eval_comp, Circuit.eval_oneGate, Circuit.eval_pi,
    interpretation_threshold, id, single_apply, eval_signedLayerGate]
  rw [threshold_apply, weight_signedLayer, parity_eq_decide_weight]
  rcases Nat.mod_two_eq_zero_or_one (weight x) with h | h <;> simp [h]

/-- The circuit has `n + 1` threshold gates. -/
theorem cost_parityCircuit : (parityCircuit n).program.cost thresholdCost = n + 1 := by
  have (j : Fin n) : (signedLayerGate n j).program.cost thresholdCost = 1 := by
    rw [signedLayerGate, Circuit.cost_program_comp, Circuit.cost_program_oneGate,
      cost_program_negIf, thresholdCost_threshold]
  rw [parityCircuit, Circuit.cost_program_comp, Circuit.cost_program_pi,
    Circuit.cost_program_oneGate, thresholdCost_threshold]
  simp [this]

/-- The odd numbers below `n` are `n / 2`. -/
private theorem sum_range_toNat_mod_two (n : ℕ) :
    ∑ j ∈ range n, (decide (j % 2 = 1)).toNat = n / 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sum_range_succ, ih]
    by_cases h : n % 2 = 1 <;> simp only [h, decide_true, decide_false, Bool.toNat_true,
      Bool.toNat_false] <;> omega

/-- The circuit has `n + 1` threshold gates and `n / 2` negations. -/
theorem size_parityCircuit : (parityCircuit n).size = n + n / 2 + 1 := by
  simp only [parityCircuit, signedLayerGate, Circuit.size_comp, Circuit.size_pi,
    Circuit.size_oneGate, size_negIf, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one]
  rw [Fin.sum_univ_eq_sum_range (fun j => (decide (j % 2 = 1)).toNat), sum_range_toNat_mod_two]

/-- The circuit has threshold depth two: negations are free. -/
theorem depthWith_parityCircuit_le : (parityCircuit n).depthWith thresholdCost ≤ 2 := by
  have (j : Fin n) : (signedLayerGate n j).depthWith thresholdCost ≤ 1 :=
    (Circuit.depthWith_comp_le _ _ _).trans (by simp)
  refine (Circuit.depthWith_comp_le _ _ _).trans ?_
  have := Circuit.depthWith_pi_le thresholdCost (signedLayerGate n) this
  simp only [Circuit.depthWith_oneGate, thresholdCost_threshold]
  omega

/-- The circuit has depth three, counting the negations. -/
theorem depth_parityCircuit_le : (parityCircuit n).depth ≤ 3 := by
  have (j : Fin n) : (signedLayerGate n j).depth ≤ 2 :=
    (Circuit.depth_comp_le _ _).trans (by simpa using depth_negIf_le _)
  refine (Circuit.depth_comp_le _ _).trans ?_
  have := Circuit.depth_pi_le (signedLayerGate n) this
  simp only [Circuit.depth_oneGate]
  omega

/-- **Parity in depth two**: the parity of `n` bits has a circuit of `n + 1` threshold gates and
threshold depth two, with `n / 2` negations, so of `n + n / 2 + 1` gates and depth three in all.
Every symmetric function has threshold circuits of depth two and linear size
[Hajnal et al., Proposition 2.1][HMPST1993]. -/
theorem exists_computes_parity (n : ℕ) :
    ∃ C : Circuit signature n 1, C.Computes interpretation (single (parity n)) ∧
      C.program.cost thresholdCost = n + 1 ∧ C.depthWith thresholdCost ≤ 2 ∧
      C.size = n + n / 2 + 1 ∧ C.depth ≤ 3 :=
  ⟨parityCircuit n, computes_parityCircuit, cost_parityCircuit, depthWith_parityCircuit_le,
    size_parityCircuit, depth_parityCircuit_le⟩

/-- **Parity has threshold circuits of polynomial size and constant depth.** -/
theorem parity_mem_constDepth : Language.ofSlices parity ∈ ConstDepth interpretation :=
  ConstDepth.mem_iff.2 ⟨3, fun n => 2 * n + 1, by fun_prop, fun n =>
    ⟨parityCircuit n, by rw [Language.slice_ofSlices]; exact computes_parityCircuit,
      depth_parityCircuit_le, by rw [size_parityCircuit]; beta_reduce; omega⟩⟩

end Cslib.Circuits.Boolean.Threshold
