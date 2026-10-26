/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Communication.Distributional
public import Complexity.Computability.Communication.Rectangle
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF
import Mathlib.Tactic.Linarith

/-!
# The corruption bound

Let `ν` be a distribution on the pairs of inputs and `z` an output. The function `f` is
`(α, δ)`-*corrupted* on `z` under `ν` when every rectangle is corrupted by inputs on which `f` is
not `z`: their `ν`-mass is at least `α` times the mass of the inputs on which `f` is `z`, up to `δ`
(`Corrupted`) [Razborov1992]. A protocol answering `z` on a leaf rectangle errs on its corrupted
part. Summing over the leaves labelled `z` (`Protocol.sum_filter_run_le_mul`), a protocol sending
`c` bits and erring with probability `err` on inputs drawn from `ν` has
`α (ν(f⁻¹(z)) - err) ≤ err + 2 ^ c δ` (`Corrupted.mul_sub_distributionalError_le`). So when `δ` is
small, protocols with small error need many bits, with public coins too
(`Corrupted.mul_sub_le_of_ecomplexityFun_le`, by Yao's principle). Unlike the discrepancy bound,
the corruption bound constrains only the rectangles on which `f` is mostly `z`, so it applies to
functions such as disjointness that have large monochromatic rectangles of another value, which
make their discrepancy large [Kushilevitz and Nisan][KushilevitzNisan1997].

## Main definitions

* `Cslib.Communication.Corrupted`: rectangles are corrupted.

## Main results

* `Cslib.Communication.Corrupted.mul_sub_distributionalError_le`: the corruption bound for
  deterministic protocols.
* `Cslib.Communication.Corrupted.mul_sub_le_of_distributionalComplexity_le`,
  `Cslib.Communication.Corrupted.mul_sub_le_of_ecomplexityFun_le`: the corruption bound on
  distributional and public-coin complexity.

## References

* [A. A. Razborov, *On the distributional complexity of disjointness*][Razborov1992]
* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
-/

@[expose] public section

namespace Cslib.Communication

open Finset Probability

variable {X Y Z : Type*}

/-- The function `f` is `(α, δ)`-*corrupted* on the value `z` under `ν` when on every rectangle
`A × B` the `ν`-mass of the pairs on which `f` is not `z` is at least `α` times the mass of the
pairs on which `f` is `z`, up to `δ`: `α ν(A × B ∩ f⁻¹(z)) ≤ ν(A × B \ f⁻¹(z)) + δ`. -/
def Corrupted [DecidableEq Z] (ν : PMF (X × Y)) (f : X → Y → Z) (z : Z) (α δ : ℝ) : Prop :=
  ∀ (A : Finset X) (B : Finset Y),
    α * ∑ x ∈ A, ∑ y ∈ B, (if f x y = z then (ν (x, y)).toReal else 0) ≤
      ∑ x ∈ A, ∑ y ∈ B, (if f x y = z then 0 else (ν (x, y)).toReal) + δ

namespace Corrupted

variable [DecidableEq Z] {ν : PMF (X × Y)} {f : X → Y → Z} {z : Z} {α δ : ℝ}

/-- The slack `δ` of a corrupted function is nonnegative: the empty rectangle has no mass. -/
theorem nonneg (h : Corrupted ν f z α δ) : 0 ≤ δ := by
  simpa using h ∅ ∅

/-- The `ν`-mass of `{q | f q.1 q.2 = z}` is at most the mass where both `p.run` and `f` equal `z`
plus the distributional error of `p`. -/
private theorem toReal_eq_le_add_distributionalError [Fintype X] [Fintype Y]
    (p : Protocol X Y Z) :
    (ν.toOuterMeasure {q | f q.1 q.2 = z}).toReal ≤
      (∑ q : X × Y, if p.run q.1 q.2 = z ∧ f q.1 q.2 = z then (ν q).toReal else 0) +
        p.distributionalError ν (fun x y b => f x y = b) := by
  classical
  simp only [Protocol.distributionalError, PMF.toOuterMeasure_apply_toReal, Set.mem_ofPred_eq,
    ← sum_add_distrib]
  refine sum_le_sum fun q _ => ?_
  split_ifs <;> simp_all

variable [Finite X] [Finite Y]

/-- **The corruption bound** for deterministic protocols: if `f` is `(α, δ)`-corrupted on `z` under
`ν`, with `α ≥ 0`, a protocol erring with probability `err` on inputs drawn from `ν` has
`α (ν(f⁻¹(z)) - err) ≤ err + 2 ^ depth δ`. -/
theorem mul_sub_distributionalError_le (h : Corrupted ν f z α δ) (hα : 0 ≤ α)
    (p : Protocol X Y Z) :
    α * ((ν.toOuterMeasure {q | f q.1 q.2 = z}).toReal -
        p.distributionalError ν (fun x y b => f x y = b)) ≤
      p.distributionalError ν (fun x y b => f x y = b) + 2 ^ p.depth * δ := by
  classical
  have := Fintype.ofFinite X
  have := Fintype.ofFinite Y
  -- Each leaf rectangle labelled `z` has weight at most `δ` when the inputs where `f` is `z` weigh
  -- `α` times their mass and the others minus their mass.
  set w : X → Y → ℝ := fun x y =>
    α * (if f x y = z then (ν (x, y)).toReal else 0) - (if f x y = z then 0 else (ν (x, y)).toReal)
  have hsum := p.sum_filter_run_le_mul z w (K := δ) fun i _ => by
    have := h {x | x ∈ p.leafAlice i} {y | y ∈ p.leafBob i}
    simp only [w, sum_sub_distrib, ← mul_sum]
    linarith
  have hleaves : (#{i | p.leafOutput i = z} : ℝ) * δ ≤ 2 ^ p.depth * δ := by
    gcongr
    · exact h.nonneg
    · exact_mod_cast (card_le_univ _).trans (by simpa using p.leafCount_le_two_pow_depth)
  -- The masses involved, as sums over all pairs of inputs.
  set E := p.distributionalError ν (fun x y b => f x y = b)
  have hE : E = ∑ q : X × Y, if f q.1 q.2 = p.run q.1 q.2 then 0 else (ν q).toReal := by
    simp only [E, Protocol.distributionalError, PMF.toOuterMeasure_apply_toReal,
      Set.mem_ofPred_eq]
    exact sum_congr rfl fun q _ => by split_ifs <;> simp_all
  have hw : ∑ q : X × Y with p.run q.1 q.2 = z, w q.1 q.2 =
      α * (∑ q : X × Y, if p.run q.1 q.2 = z ∧ f q.1 q.2 = z then (ν q).toReal else 0) -
        ∑ q : X × Y, if p.run q.1 q.2 = z ∧ f q.1 q.2 ≠ z then (ν q).toReal else 0 := by
    rw [sum_filter, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun q _ => ?_
    simp only [w]
    split_ifs <;> simp_all
  -- `f` is `z` only where the protocol answers `z` or errs, and the protocol errs where it answers
  -- `z` but `f` is not `z`.
  have h₁ : (ν.toOuterMeasure {q | f q.1 q.2 = z}).toReal ≤
      (∑ q : X × Y, if p.run q.1 q.2 = z ∧ f q.1 q.2 = z then (ν q).toReal else 0) + E :=
    toReal_eq_le_add_distributionalError p
  have h₂ : (∑ q : X × Y, if p.run q.1 q.2 = z ∧ f q.1 q.2 ≠ z then (ν q).toReal else 0) ≤ E := by
    rw [hE]
    refine sum_le_sum fun q _ => ?_
    split_ifs <;> simp_all
  have h₃ := mul_le_mul_of_nonneg_left (sub_le_iff_le_add.mpr h₁) hα
  linarith

/-- **The corruption bound** on distributional complexity: if `f` is `(α, δ)`-corrupted on `z`
under `ν`, with `α ≥ 0`, and some protocol sending at most `c` bits errs with probability at most
`ε` on inputs drawn from `ν`, then `α (ν(f⁻¹(z)) - ε) ≤ ε + 2 ^ c δ`. -/
theorem mul_sub_le_of_distributionalComplexity_le (h : Corrupted ν f z α δ) (hα : 0 ≤ α)
    {ε : ℝ} {c : ℕ}
    (hc : Protocol.distributionalComplexity ε (fun x y b => f x y = b) ν ≤ c) :
    α * ((ν.toOuterMeasure {q | f q.1 q.2 = z}).toReal - ε) ≤ ε + 2 ^ c * δ := by
  obtain ⟨p, hp, hd⟩ := Protocol.distributionalComplexity_le_iff.mp hc
  have hpow : (2 : ℝ) ^ p.depth * δ ≤ 2 ^ c * δ :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hd) h.nonneg
  have := h.mul_sub_distributionalError_le hα p
  have := mul_le_mul_of_nonneg_left (sub_le_sub_left hp
    (ν.toOuterMeasure {q | f q.1 q.2 = z}).toReal) hα
  linarith

/-- **The corruption bound** on public-coin complexity: if `f` is `(α, δ)`-corrupted on `z` under
`ν`, with `α ≥ 0`, then a public-coin protocol computing `f` with error `ε` and sending at most `c`
bits has `α (ν(f⁻¹(z)) - ε) ≤ ε + 2 ^ c δ`. -/
theorem mul_sub_le_of_ecomplexityFun_le (h : Corrupted ν f z α δ) (hα : 0 ≤ α) {ε : ℝ} {c : ℕ}
    (hc : PublicCoin.ecomplexityFun ε f ≤ c) :
    α * ((ν.toOuterMeasure {q | f q.1 q.2 = z}).toReal - ε) ≤ ε + 2 ^ c * δ :=
  h.mul_sub_le_of_distributionalComplexity_le hα
    ((PublicCoin.distributionalComplexity_le_ecomplexity fun _ _ => ⟨trivial, trivial⟩).trans hc)

end Corrupted

end Cslib.Communication
