/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Unbounded
public import CslibFrontier.MachineLearning.UniformLearning.LowDegree
import CslibFrontier.Computability.Circuit.Boolean.LMN
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Learning constant-depth circuits from random examples

By the Linial–Mansour–Nisan theorem above an explicit degree
(`Circuits.Boolean.Unbounded.sum_fourierCoeff_sq_le_of_computes_of_depth_le`), a function computed
by a circuit of negations and unbounded fan-in conjunctions and disjunctions of depth at most `d`
with at most `g` gates (`UniformLearning.circuitClass`) has Fourier weight at most `2 g / 2 ^ s`
above degree `t`, for every `s ≥ 2` and `t + 1 ≥ 2 max 8 (2 s) (16 s + 1) ^ d`. Taking
`2 ^ s ≥ 4 g / ε`, the weight is at most `ε / 2`, so the low-degree algorithm learns these circuits
from uniform random examples (`UniformLearning.lowDegreeLearner_learns_circuitClass`): a form of
[O'Donnell, Theorem 4.31][ODonnell2014] [LinialMansourNisan1993] with exponent `d + 1`. With
`s = max 2 ⌈log₂ ⌈4 g / ε⌉⌉` the degree is `t = UniformLearning.lmnDegree d g ε`, which is
`O (log (g / ε)) ^ (d + 1)` for fixed `d` (`UniformLearning.lowDegreeLearner_learns_lmnDegree`), and
the algorithm uses `m ≥ (4 N / ε) log (2 N / δ)` examples, where `N ≤ (n + 1) ^ t` is the number of
sets of at most `t` coordinates (`BitString.card_filter_card_le_le_pow`). Read asymptotically (this
reading is not itself formalized), for `g` polynomial in `n` and constant `d`, `ε` and `δ` this is
`n ^ O (log n) ^ (d + 1)` examples: quasi-polynomially many.

Depth counts every gate on a path, negations included (`Circuit.depth`). For a circuit whose
negations sit at the inputs, of AND/OR depth `d'` in the usual sense, this depth is at most
`d' + 1`; this conversion is not formalized here. The exponent `d + 1` is inherited from the
Fourier bound used here (`Circuits.Boolean.Unbounded.sum_fourierCoeff_sq_le_of_computes`), in which
each restriction stage keeps a `1 / (16 s + 1)` fraction of the free bits. It is weaker than the
degree `O (log (g / ε)) ^ d` of Linial, Mansour and Nisan, and than the degree
`O (log (g / ε)) ^ (d - 1) · log (1 / ε)` of the sharper form presented by O'Donnell
[O'Donnell, Section 4.5][ODonnell2014].

The learner computes `N` empirical coefficients from `m` examples, `O (N m t)` arithmetic
operations; this running time is an informal count, not certified by a machine model.

## Main definitions

* `Cslib.MachineLearning.UniformLearning.circuitClass`: the functions computed by circuits of
  bounded depth and size.
* `Cslib.MachineLearning.UniformLearning.lmnDegree`: the degree used for circuits of depth `d` with
  `g` gates and error `ε`.

## Main results

* `Cslib.MachineLearning.UniformLearning.lowDegreeLearner_learns_circuitClass`,
  `Cslib.MachineLearning.UniformLearning.lowDegreeLearner_learns_lmnDegree`: the low-degree
  algorithm learns circuits of constant depth from uniform random examples.

## References

* [N. Linial, Y. Mansour, N. Nisan, *Constant depth circuits, Fourier transform, and
  learnability*][LinialMansourNisan1993]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.MachineLearning.UniformLearning

open BitString Finset PACLearning Circuits Circuits.Boolean

variable {n : ℕ}

/-- The functions of `n` bits computed by circuits of negations and unbounded fan-in conjunctions
and disjunctions of depth at most `d` with at most `g` gates. -/
def circuitClass (n d g : ℕ) : ConceptClass (BitString n) Bool :=
  {f | ∃ C : Circuit Unbounded.signature n 1,
    C.Computes Unbounded.interpretation (single f) ∧ C.depth ≤ d ∧ C.size ≤ g}

/-- **The low-degree algorithm learns constant-depth circuits**, a form of
[O'Donnell, Theorem 4.31][ODonnell2014] [LinialMansourNisan1993] with exponent `d + 1`. Let `s ≥ 2`
with `4 g ≤ ε 2 ^ s`, let `t + 1 ≥ 2 max 8 (2 s) (16 s + 1) ^ d`, and let `N` be the number of sets
of at most `t` of the `n` coordinates. Then the low-degree algorithm of degree `t` from
`m ≥ (4 N / ε) log (2 N / δ)` uniform random examples learns the functions computed by circuits of
negations and unbounded fan-in conjunctions and disjunctions of depth at most `d` with at most `g`
gates, with error `ε` and confidence `1 - δ`. -/
theorem lowDegreeLearner_learns_circuitClass {d g s t m : ℕ} {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hs : 2 ≤ s) (hsg : 4 * (g : ℝ) ≤ ε * 2 ^ s)
    (ht : 2 * max 8 (2 * s) * (16 * s + 1) ^ d ≤ t + 1)
    (hm : 4 * #{S : Finset (Fin n) | #S ≤ t} / ε *
      Real.log (2 * #{S : Finset (Fin n) | #S ≤ t} / δ) ≤ m) :
    Learns (lowDegreeLearner (Fin n) t m) (circuitClass n d g) ε δ := by
  refine lowDegreeLearner_learns hε hδ hm fun f ⟨C, hC, hd, hg⟩ => ?_
  refine (Unbounded.sum_fourierCoeff_sq_le_of_computes_of_depth_le hC hs hd ht).trans ?_
  have hgR : (C.size : ℝ) ≤ g := by exact_mod_cast hg
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- The degree of the low-degree algorithm for circuits of depth `d` with `g` gates and error
`ε`: `2 max 8 (2 s) (16 s + 1) ^ d - 1` for `s = max 2 ⌈log₂ ⌈4 g / ε⌉⌉`, which is
`O (log (g / ε)) ^ (d + 1)` for fixed `d`. -/
noncomputable def lmnDegree (d g : ℕ) (ε : ℝ) : ℕ :=
  let s := max 2 (Nat.clog 2 ⌈4 * g / ε⌉₊)
  2 * max 8 (2 * s) * (16 * s + 1) ^ d - 1

/-- **The low-degree algorithm learns constant-depth circuits**, with the explicit degree
`t = lmnDegree d g ε = O (log (g / ε)) ^ (d + 1)` [LinialMansourNisan1993]
[O'Donnell, Section 4.5][ODonnell2014]: from `m ≥ (4 N / ε) log (2 N / δ)` uniform random
examples, where `N ≤ (n + 1) ^ t` is the number of sets of at most `t` of the `n` coordinates, it
learns the functions computed by circuits of negations and unbounded fan-in conjunctions and
disjunctions of depth at most `d` with at most `g` gates, with error `ε` and confidence
`1 - δ`. -/
theorem lowDegreeLearner_learns_lmnDegree {d g m : ℕ} {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hm : 4 * #{S : Finset (Fin n) | #S ≤ lmnDegree d g ε} / ε *
      Real.log (2 * #{S : Finset (Fin n) | #S ≤ lmnDegree d g ε} / δ) ≤ m) :
    Learns (lowDegreeLearner (Fin n) (lmnDegree d g ε) m) (circuitClass n d g) ε δ := by
  set s := max 2 (Nat.clog 2 ⌈4 * g / ε⌉₊)
  have hs : 2 ≤ s := le_max_left _ _
  have hsg : 4 * (g : ℝ) ≤ ε * 2 ^ s := by
    have h₁ : 4 * (g : ℝ) / ε ≤ 2 ^ s :=
      calc 4 * (g : ℝ) / ε ≤ ⌈4 * g / ε⌉₊ := Nat.le_ceil _
        _ ≤ ((2 ^ Nat.clog 2 ⌈4 * g / ε⌉₊ : ℕ) : ℝ) :=
            Nat.cast_le.2 (Nat.le_pow_clog (by norm_num) _)
        _ ≤ 2 ^ s := by
            rw [Nat.cast_pow, Nat.cast_ofNat]
            exact pow_le_pow_right₀ (by norm_num) (le_max_right _ _)
    rw [div_le_iff₀ hε] at h₁
    linarith
  have hpos : 0 < 2 * max 8 (2 * s) * (16 * s + 1) ^ d := by positivity
  have ht : 2 * max 8 (2 * s) * (16 * s + 1) ^ d ≤ lmnDegree d g ε + 1 := by
    change _ ≤ 2 * max 8 (2 * s) * (16 * s + 1) ^ d - 1 + 1
    omega
  exact lowDegreeLearner_learns_circuitClass hε hδ hs hsg ht hm

end Cslib.MachineLearning.UniformLearning
