/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Approximation
public import Cslib.Computability.Circuit.Complexity
public import Mathlib.Basic.Real.Basic
public import Mathlib.InformationTheory.Hamming
import CslibFrontier.Computability.Circuit.Simulation

/-!
# The approximation method in Hamming terms

A local approximation scheme (`Cslib.Circuits.Approximation.Scheme`) evaluates a circuit in an
approximate interpretation and decodes each approximate value `a` as a function `decode a` on the
samples. When correctness of a decoded value implies equality, the exceptions charged to the gates
measure how far the decoded output of a circuit is from the function the circuit computes:

* a circuit computing `f` on the samples has a decoded output `f̃` with
  `d_H(f, f̃) ≤ ∑_gates errorCost(gate)`, the sum of the local errors of its gates
  (`Cslib.Circuits.Approximation.Scheme.hammingDist_le_sum_errorCost`);
* hence the **lower-bound principle**: if every gate errs on at most `δ` samples and `f` is at
  Hamming distance at least `ε` from every decoded approximate value, then `ε ≤ δ C(f)`, so
  `C(f) ≥ ε / δ` for `δ > 0`
  (`Cslib.Circuits.Approximation.Scheme.le_mul_complexity_of_le_hammingDist`), and the same with
  the failures of a one-sided correctness relation in place of the Hamming distance
  (`Cslib.Circuits.Approximation.Scheme.le_mul_complexity`).

Weighting the samples by `μ ≥ 0`, for instance a probability distribution, the union bound over
the gates bounds the weight of the samples on which the approximate output fails by the sum of
per-gate bounds on the weights of the gates' exceptions
(`Cslib.Circuits.Approximation.Scheme.sum_failures_le`), with the weighted lower-bound principle
as a consequence (`Cslib.Circuits.Approximation.Scheme.le_mul_complexity_of_le_sum_failures`).

This is a reformulation of the classical method of approximations
[Jukna, Chapter 9][Jukna2012] in the language of the Hamming distance, not a new lower-bound
technique, and the known limitations of the method of approximations apply to it unchanged.

## Main results

* `Cslib.Circuits.Approximation.Scheme.hammingDist_le_cost`,
  `Cslib.Circuits.Approximation.Scheme.hammingDist_le_sum_errorCost`: the decoded output is within
  the total local error of the target.
* `Cslib.Circuits.Approximation.Scheme.le_mul_size`: every circuit computing the target has
  `ε ≤ δ s` for its number `s` of gates.
* `Cslib.Circuits.Approximation.Scheme.le_mul_complexity`,
  `Cslib.Circuits.Approximation.Scheme.le_mul_complexity_of_le_hammingDist`: the lower-bound
  principle `ε ≤ δ C(f)`.
* `Cslib.Circuits.Approximation.Scheme.sum_programExceptions_le`,
  `Cslib.Circuits.Approximation.Scheme.sum_failures_le`: the weighted union bound.
* `Cslib.Circuits.Approximation.Scheme.le_mul_complexity_of_le_sum_failures`: the weighted
  lower-bound principle.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

public section

namespace Cslib.Circuits.Approximation.Scheme

open Finset

variable {σ : Signature} {U A Sample : Type*} {n : ℕ}
  {exact : Interpretation σ U} {approx : Interpretation σ A} {decode : A → Sample → U}
  {exactInput : Sample → Fin n → U} {approxInput : Fin n → A}
  (S : Scheme exact approx decode exactInput approxInput)

/-! ### Lower bounds from failures -/

section Failures

variable [DecidableRel S.relation]

/-- If every operation errs on at most `δ` samples and every approximate value fails on at least
`ε` of the samples, then every circuit computing `target` on the samples has `ε ≤ δ s` for its
number `s` of gates, that is, at least `ε / δ` gates when `δ > 0`. -/
theorem le_mul_size (samples : Finset Sample) (C : Circuit σ n 1) {target : Sample → U}
    (hC : ∀ s ∈ samples, C.eval exact (exactInput s) 0 = target s) {δ ε : ℕ}
    (hδ : ∀ op, S.errorCost op ≤ δ) (hε : ∀ a, ε ≤ #(S.failures samples a target)) :
    ε ≤ δ * C.size :=
  (hε _).trans ((S.card_failures_le_cost samples C hC).trans (C.program.cost_le_mul hδ))

/-- **The lower-bound principle of the approximation method**: if every operation errs on at most
`δ` samples and every approximate value fails on at least `ε` of the samples for `f`, then
`ε ≤ δ C(f)`, that is, `C(f) ≥ ε / δ` when `δ > 0`. -/
theorem le_mul_complexity [exact.IsComplete] (samples : Finset Sample) (f : (Fin n → U) → U)
    {δ ε : ℕ} (hδ : ∀ op, S.errorCost op ≤ δ)
    (hε : ∀ a, ε ≤ #(S.failures samples a fun s => f (exactInput s))) :
    ε ≤ δ * complexity exact (single f) := by
  obtain ⟨C, hC, hsize⟩ := exists_computes_size_eq_complexity (I := exact) (f := single f)
  rw [← hsize]
  exact S.le_mul_size samples C (fun s _ => congrFun (hC (exactInput s)) 0) hδ hε

end Failures

/-! ### The Hamming distance -/

section Hamming

variable [Fintype Sample] [DecidableEq U]

/-- When correctness implies equality, the decoded approximate output of a circuit computing
`target` differs from `target` on at most as many samples as the total cost of its gates. -/
theorem hammingDist_le_cost (hrel : ∀ {u v}, S.relation u v → u = v) (C : Circuit σ n 1)
    {target : Sample → U} (hC : ∀ s, C.eval exact (exactInput s) 0 = target s) :
    hammingDist target (decode (C.eval approx approxInput 0)) ≤ C.program.cost S.errorCost := by
  classical
  refine (card_le_card fun s hs => ?_).trans (S.card_failures_le_cost univ C fun s _ => hC s)
  exact S.mem_failures.2 ⟨mem_univ s, fun h => (mem_filter.1 hs).2 (hrel h)⟩

/-- **The decoded output is within the total local error of the target**: when correctness
implies equality, a circuit computing `f` has a decoded approximate output `f̃` with
`d_H(f, f̃) ≤ ∑_gates errorCost(gate)`. -/
theorem hammingDist_le_sum_errorCost (hrel : ∀ {u v}, S.relation u v → u = v)
    (C : Circuit σ n 1) {target : Sample → U}
    (hC : ∀ s, C.eval exact (exactInput s) 0 = target s) :
    hammingDist target (decode (C.eval approx approxInput 0)) ≤
      ∑ k, S.errorCost (C.program.lines k).op :=
  (S.hammingDist_le_cost hrel C hC).trans_eq (C.program.cost_eq_sum S.errorCost)

/-- **The lower-bound principle in Hamming terms**: when correctness implies equality, if every
operation errs on at most `δ` samples and `f` is at Hamming distance at least `ε` from every
decoded approximate value, then `ε ≤ δ C(f)`, that is, `C(f) ≥ ε / δ` when `δ > 0`. -/
theorem le_mul_complexity_of_le_hammingDist [exact.IsComplete]
    (hrel : ∀ {u v}, S.relation u v → u = v) (f : (Fin n → U) → U) {δ ε : ℕ}
    (hδ : ∀ op, S.errorCost op ≤ δ)
    (hε : ∀ a, ε ≤ hammingDist (fun s => f (exactInput s)) (decode a)) :
    ε ≤ δ * complexity exact (single f) := by
  obtain ⟨C, hC, hsize⟩ := exists_computes_size_eq_complexity (I := exact) (f := single f)
  rw [← hsize]
  exact (hε _).trans ((S.hammingDist_le_cost hrel C fun s => congrFun (hC (exactInput s)) 0).trans
    (C.program.cost_le_mul hδ))

end Hamming

/-! ### Weighted samples -/

section Weighted

variable {μ : Sample → ℝ} {w : σ.Op → ℝ}

/-- **The weighted union bound over the gates**: if the exceptions of every operation weigh at
most `w op`, then the exceptions of all gates of a program weigh at most the sum of `w` over its
gates. -/
theorem sum_programExceptions_le [DecidableEq Sample] (hμ : ∀ s, 0 ≤ μ s)
    (hw : ∀ op a, ∑ s ∈ S.exceptions op a, μ s ≤ w op) {g : ℕ} (p : Program σ n g) :
    ∑ s ∈ S.programExceptions p, μ s ≤ ∑ k, w (p.lines k).op := by
  induction p with
  | empty => simp
  | gate p line ih =>
    rw [programExceptions_gate, Fin.sum_univ_castSucc]
    simp only [Program.lines_gate_last, Program.lines_gate_castSucc, Line.mapWires_op]
    have hunion := sum_union_inter (s₁ := S.programExceptions p)
      (s₂ := S.exceptions line.op (p.trace approx approxInput ∘ line.wires)) (f := μ)
    have hinter := sum_nonneg fun s (_ : s ∈ S.programExceptions p ∩
      S.exceptions line.op (p.trace approx approxInput ∘ line.wires)) => hμ s
    linarith [hw line.op (p.trace approx approxInput ∘ line.wires)]

variable [DecidableRel S.relation]

/-- **The weighted approximation method.** If the exceptions of every operation weigh at most
`w op`, then the samples on which the approximate output of a circuit computing `target` fails
weigh at most the sum of `w` over its gates. For a probability distribution `μ`, this bounds the
probability of failure. -/
theorem sum_failures_le (hμ : ∀ s, 0 ≤ μ s) (hw : ∀ op a, ∑ s ∈ S.exceptions op a, μ s ≤ w op)
    (samples : Finset Sample) (C : Circuit σ n 1) {target : Sample → U}
    (hC : ∀ s ∈ samples, C.eval exact (exactInput s) 0 = target s) :
    ∑ s ∈ S.failures samples (C.eval approx approxInput 0) target, μ s ≤
      ∑ k, w (C.program.lines k).op := by
  classical
  exact (sum_le_sum_of_subset_of_nonneg (S.failures_subset_programExceptions samples C hC)
    fun s _ _ => hμ s).trans (S.sum_programExceptions_le hμ hw C.program)

/-- **The weighted lower-bound principle**: if the exceptions of every operation weigh at most
`δ` and every approximate value fails for `f` on samples of total weight at least `ε`, then
`ε ≤ δ C(f)`, that is, `C(f) ≥ ε / δ` when `δ > 0`. -/
theorem le_mul_complexity_of_le_sum_failures [exact.IsComplete] (hμ : ∀ s, 0 ≤ μ s)
    (samples : Finset Sample) (f : (Fin n → U) → U) {δ ε : ℝ}
    (hδ : ∀ op a, ∑ s ∈ S.exceptions op a, μ s ≤ δ)
    (hε : ∀ a, ε ≤ ∑ s ∈ S.failures samples a (fun s => f (exactInput s)), μ s) :
    ε ≤ δ * complexity exact (single f) := by
  obtain ⟨C, hC, hsize⟩ := exists_computes_size_eq_complexity (I := exact) (f := single f)
  have h := (hε _).trans
    (S.sum_failures_le hμ hδ samples C fun s _ => congrFun (hC (exactInput s)) 0)
  rwa [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hsize, mul_comm] at h

end Weighted

end Cslib.Circuits.Approximation.Scheme
