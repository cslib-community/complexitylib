/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Interactive.Security
public import Complexity.Computability.Probabilistic.PPT
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Complexity.Probability.PMF.Event

/-!
# Fully polynomial almost uniform samplers

A **fully polynomial almost uniform sampler** (FPAUS) for a finite set of witnesses `W x` of each
instance `x` is a randomized algorithm that, given `x` and a tolerance `ε`, outputs a witness
whose law is within total-variation distance `ε` of the uniform law on `W x`, in time polynomial
in the length of `x` and in `log (1 / ε)` [Sinclair and Jerrum][SinclairJerrum1989],
[Jerrum, Valiant and Vazirani][JerrumValiantVazirani1986],
[Sinclair, Lecture 4, Section 4.2][Sinclair2025].

`Cslib.Complexity.IsFPAUS enc W S` parameterizes the tolerance as `ε = 2 ^ (-q)` for a natural
number `q` written in unary, so a running time polynomial in the length of the encoded input
`(x, q)` is exactly a running time polynomial in `|x|` and `log (1 / ε)`. Witnesses are bit
strings, and the sampler returns an `Option (List Bool)`: the target law
(`Cslib.Complexity.uniformWitness`) is uniform on `some w` for `w ∈ W x`, and is `none` with
probability one when `W x` is empty, so an instance without witnesses is reported rather than
left unconstrained. The requirements stay separate:

* **runtime**: `S` is a strict probabilistic polynomial-time program (`Cslib.Probability.IsPPTOn`)
  on the encoded input `(x, q)`, with the result encoded by `encOption encBits`;
* **output-distribution error**: for every event `E`, the probability of `E` under `S x q` exceeds
  its probability under the target law by at most `(1 / 2) ^ q` (`Cslib.Interactive.CloseTo`,
  which quantifies over all events and is therefore symmetric). This is the total-variation
  distance `max_E |μ E - ν E|`; `Cslib.Interactive.CloseTo.abs_toReal_sub_le` gives the real,
  two-sided form.

## Main definitions

* `Cslib.Complexity.uniformWitness`: the uniform law on a finite set of witnesses.
* `Cslib.Complexity.IsFPAUS`: a fully polynomial almost uniform sampler.
* `Cslib.Complexity.FPAUS`: the witness families admitting one.

## Main results

* `Cslib.Complexity.uniformWitness_toOuterMeasure_some`: the probability of an event of witnesses
  is its relative cardinality.
* `Cslib.Interactive.CloseTo.abs_toReal_sub_le`: closeness bounds real probability differences.

## References

* [A. Sinclair, M. Jerrum, *Approximate counting, uniform generation and rapidly mixing Markov
  chains*][SinclairJerrum1989]
* [M. R. Jerrum, L. G. Valiant, V. V. Vazirani, *Random generation of combinatorial structures from
  a uniform distribution*][JerrumValiantVazirani1986]
* [A. Sinclair, *CS294 Partition Functions*, Lecture 4, Definition 4.3 and Section
  4.2][Sinclair2025]
-/

public section

namespace Cslib.Complexity

open Cslib.Probability Turing.MultiTapeTM

variable {α : Type}

/-- The uniform law on the witnesses `W`, as `some w`; the point mass at `none` when there are
none. -/
noncomputable def uniformWitness (W : Finset (List Bool)) : PMF (Option (List Bool)) :=
  if h : W.Nonempty then (PMF.uniformOfFinset W h).map some else PMF.pure none

/-- **A fully polynomial almost uniform sampler** for the witness sets `W`, on instances encoded
by `enc`. The sampler `S x q` receives the instance `x` and the accuracy `q` (so the tolerance is
`ε = 2 ^ (-q)`), with `q` in unary. It is a strict probabilistic polynomial-time program on the
encoded pair `(x, q)`, outputs an optional bit string, and its output law is within
total-variation distance `(1 / 2) ^ q` of `uniformWitness (W x)` (`Cslib.Interactive.CloseTo`). -/
@[expose]
def IsFPAUS (enc : α ↪ List Bool) (W : α → Finset (List Bool))
    (S : α → ℕ → ProbComp (Option (List Bool))) : Prop :=
  IsPPTOn (encPair enc encUnary) (encOption encBits) (Function.uncurry S) ∧
    ∀ x q, Interactive.CloseTo (ProbComp.eval (S x q)) (uniformWitness (W x))
      (ENNReal.ofReal ((1 / 2 : ℝ) ^ q))

/-- The witness families with a fully polynomial almost uniform sampler, on instances encoded by
`enc`. -/
@[expose]
def FPAUS (enc : α ↪ List Bool) : Set (α → Finset (List Bool)) :=
  {W | ∃ S, IsFPAUS enc W S}

theorem uniformWitness_of_nonempty {W : Finset (List Bool)} (h : W.Nonempty) :
    uniformWitness W = (PMF.uniformOfFinset W h).map some :=
  dite_eq_left h

@[simp]
theorem uniformWitness_empty : uniformWitness ∅ = PMF.pure none :=
  dite_eq_right Finset.not_nonempty_empty

/-- The probability that the uniform witness lies in `E` is the relative number of witnesses
in `E`. -/
theorem uniformWitness_toOuterMeasure_some {W : Finset (List Bool)} (h : W.Nonempty)
    (E : Set (List Bool)) [DecidablePred (· ∈ E)] :
    ((uniformWitness W).toOuterMeasure (some '' E)).toReal =
      ((W.filter (· ∈ E)).card : ℝ) / W.card := by
  classical
  rw [uniformWitness_of_nonempty h, PMF.toOuterMeasure_map_apply,
    Set.preimage_image_eq _ (Option.some_injective _), PMF.toOuterMeasure_apply,
    tsum_eq_sum (s := W) (fun w hw => by simp [Set.indicator, hw])]
  have hsum : ∑ w ∈ W, E.indicator (PMF.uniformOfFinset W h) w =
      ∑ w ∈ W.filter (· ∈ E), ((W.card : ENNReal)⁻¹) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun w hw => by simp [Set.indicator, hw]
  rw [hsum, Finset.sum_const, nsmul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp [div_eq_mul_inv]

end Cslib.Complexity

namespace Cslib.Interactive

/-- Closeness within a real tolerance `ε ≥ 0` bounds the real difference of the probabilities of
every event by `ε`. -/
theorem CloseTo.abs_toReal_sub_le {β : Type} {μ ν : PMF β} {ε : ℝ} (hε : 0 ≤ ε)
    (h : CloseTo μ ν (ENNReal.ofReal ε)) (E : Set β) :
    |(μ.toOuterMeasure E).toReal - (ν.toOuterMeasure E).toReal| ≤ ε := by
  have hμ := Cslib.Probability.PMF.toOuterMeasure_ne_top μ E
  have hν := Cslib.Probability.PMF.toOuterMeasure_ne_top ν E
  have h₁ := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hν, ENNReal.ofReal_ne_top⟩) (h E)
  have h₂ := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hμ, ENNReal.ofReal_ne_top⟩) (h.symm E)
  rw [ENNReal.toReal_add hν ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε] at h₁
  rw [ENNReal.toReal_add hμ ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε] at h₂
  rw [abs_le]
  constructor <;> linarith

end Cslib.Interactive
