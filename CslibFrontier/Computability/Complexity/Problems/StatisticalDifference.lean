/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Polarization
public import CslibFrontier.Computability.Complexity.Classes.Promise.Reduction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Statistical Difference

**Statistical Difference** `SD^{α,β}` [SahaiVadhan2003, §3.1 and p. 234] is the promise problem
whose instances are pairs of circuits, each read as a sampler of its output distribution on uniform
inputs (`Cslib.Circuits.Circuit.outputDist`). An instance is a yes-instance when the statistical
distance between the two output distributions is at least `α`, and a no-instance when it is at most
`β`. Sahai and Vadhan define SD in §3.1 with the strict thresholds `> 2/3` and `< 1/3`, and prove
that it is complete for the class SZK of problems with statistical zero-knowledge proofs. The
variant `SD^{α,β}` with the non-strict thresholds used here is defined on p. 234, where it is noted
to be interreducible with SD whenever `1 > α² > β > 0`. This file formalizes the problem and the
Polarization Lemma on instances, not completeness, and not the class SZK.

Instances here are pairs of De Morgan circuits with a common number of inputs and a common number
of outputs (`SDInstance`). The XOR construction feeds the same data bits to both circuits, so it
needs the common input count. `SD^{α,β}` is the gap problem `PromiseProblem.gapMax` of the distance
(`StatisticalDifference`).

Polarizing an instance runs the circuit polarization construction
`Cslib.Circuits.Boolean.polarizeCircuit` on both circuits (`SDInstance.polarize`). Its distance is
the distance of the polarized pair of output distributions (`SDInstance.distance_polarize`).
`Cslib.Probability.PMF.exists_polarization` then gives the **Polarization Lemma on instances**,
for constant thresholds `0 ≤ β < α² ≤ 1` (`SDInstance.exists_polarize`). With
`λ = m (⌊log₂ (k + 1)⌋ + 1)` inner coordinates, `ℓ = 2 ^ (b (⌊log₂ (k + 1)⌋ + 1))` copies and
`k + 1` outer coordinates, where the constants `m` and `b` depend only on `α` and `β`, it maps
yes-instances of `SD^{α,β}` to yes-instances of `SD^{1 - 2⁻⁽ᵏ⁺¹⁾, 2⁻⁽ᵏ⁺¹⁾}` and no-instances to
no-instances, for every `k ≥ 1` (`StatisticalDifference.exists_mapsTo_polarize`).

This is the semantic half of the Sahai–Vadhan polarization reduction. The efficiency half, that
the polarized instance is computable in polynomial time from the encoded instance, with `k` growing
with the instance length, is in `Problems.StatisticalDifference.PolyTime`.

## Main definitions

* `Cslib.Complexity.SDInstance`: a pair of circuits with common input and output counts.
* `Cslib.Complexity.SDInstance.distance`: the statistical distance between their output
  distributions.
* `Cslib.Complexity.SDInstance.polarize`: the polarization of an instance.
* `Cslib.Complexity.StatisticalDifference`: the promise problem `SD^{α,β}`.

## Main results

* `Cslib.Complexity.SDInstance.distance_polarize`: the distance of the polarized instance is the
  distance of the polarized pair of output distributions.
* `Cslib.Complexity.SDInstance.exists_polarize`: the Polarization Lemma on instances, for constant
  thresholds `0 ≤ β < α² ≤ 1`.
* `Cslib.Complexity.StatisticalDifference.exists_mapsTo_polarize`: polarization maps `SD^{α,β}` into
  `SD^{1 - 2⁻⁽ᵏ⁺¹⁾, 2⁻⁽ᵏ⁺¹⁾}` for `k ≥ 1`.

## References

* [A. Sahai, S. Vadhan, *A complete problem for statistical zero knowledge*][SahaiVadhan2003]
-/

@[expose] public section

namespace Cslib.Complexity

open Circuits Circuits.Boolean
open scoped Cslib.Probability.PMF

/-- An instance of **Statistical Difference** [SahaiVadhan2003, §3.1]: two De Morgan circuits with
the same numbers of inputs and outputs, read as samplers of their output distributions on uniform
inputs. -/
structure SDInstance where
  /-- The number of inputs of both circuits. -/
  inputs : ℕ
  /-- The number of outputs of both circuits. -/
  outputs : ℕ
  /-- The first circuit. -/
  left : Circuit signature inputs outputs
  /-- The second circuit. -/
  right : Circuit signature inputs outputs

namespace SDInstance

/-- The statistical distance between the output distributions of the two circuits. -/
noncomputable def distance (x : SDInstance) : ℝ :=
  dist (x.left.outputDist interpretation) (x.right.outputDist interpretation)

theorem distance_nonneg (x : SDInstance) : 0 ≤ x.distance :=
  dist_nonneg

theorem distance_le_one (x : SDInstance) : x.distance ≤ 1 :=
  Probability.PMF.dist_le_one _ _

/-- The **polarization** of an instance [SahaiVadhan2003, proof of Lemma 3.3]: `polarizeCircuit` on
both circuits, with `lam + 1` inner coordinates, `ell` copies and `k + 1` outer coordinates. -/
def polarize (x : SDInstance) (lam ell k : ℕ) : SDInstance :=
  ⟨_, _, polarizeCircuit x.left x.right lam ell k false,
    polarizeCircuit x.left x.right lam ell k true⟩

/-- The distance of the polarized instance is the distance of the polarized pair of output
distributions. -/
theorem distance_polarize (x : SDInstance) (lam ell k : ℕ) :
    (x.polarize lam ell k).distance =
      dist (Probability.PMF.polarize (x.left.outputDist interpretation)
          (x.right.outputDist interpretation) (lam + 1) ell (k + 1) false)
        (Probability.PMF.polarize (x.left.outputDist interpretation)
          (x.right.outputDist interpretation) (lam + 1) ell (k + 1) true) :=
  dist_outputDist_polarizeCircuit x.left x.right lam ell k

end SDInstance

/-- **Statistical Difference** `SD^{α,β}` [SahaiVadhan2003, §3.1 and p. 234]: the yes-instances are
the pairs of circuits whose output distributions are at statistical distance at least `α`, and the
no-instances those at distance at most `β`, when `β < α`. -/
noncomputable def StatisticalDifference (α β : ℝ) : PromiseProblem SDInstance :=
  PromiseProblem.gapMax SDInstance.distance (fun _ => α) (fun _ => β)

theorem mem_yes_statisticalDifference {α β : ℝ} {x : SDInstance} :
    x ∈ (StatisticalDifference α β).yes ↔ α ≤ x.distance :=
  Iff.rfl

theorem mem_no_statisticalDifference {α β : ℝ} (h : β < α) {x : SDInstance} :
    x ∈ (StatisticalDifference α β).no ↔ x.distance ≤ β :=
  PromiseProblem.mem_no_gapMax_of_lt h

/-- **The Polarization Lemma on instances** [SahaiVadhan2003, Lemma 3.3 and the remark after its
proof], for constant thresholds `0 ≤ β < α² ≤ 1`. There are constants `m ≥ 1` and `b` such that,
with `λ = m (⌊log₂ (k + 1)⌋ + 1)` inner coordinates (passed as `λ - 1`),
`ℓ = 2 ^ (b (⌊log₂ (k + 1)⌋ + 1))` copies and `k + 1` outer coordinates, an instance at distance at
least `α` polarizes to distance at least `1 - 2⁻⁽ᵏ⁺¹⁾`, and an instance at distance at most `β`
polarizes to distance at most `2⁻⁽ᵏ⁺¹⁾`. Both parameters are polynomially bounded in `k`. -/
theorem SDInstance.exists_polarize {α β : ℝ} (hβ : 0 ≤ β) (hβα : β < α ^ 2) (hα : 0 ≤ α)
    (hα1 : α ≤ 1) :
    ∃ m b : ℕ, m ≠ 0 ∧
      PolynomiallyBounded (fun k => m * (Nat.log 2 k + 1)) ∧
      PolynomiallyBounded (fun k => 2 ^ (b * (Nat.log 2 k + 1))) ∧
      ∀ (x : SDInstance) (k : ℕ),
        (α ≤ x.distance → 1 - (1 / 2) ^ (k + 1) ≤
          (x.polarize (m * (Nat.log 2 (k + 1) + 1) - 1) (2 ^ (b * (Nat.log 2 (k + 1) + 1)))
            k).distance) ∧
        (x.distance ≤ β →
          (x.polarize (m * (Nat.log 2 (k + 1) + 1) - 1) (2 ^ (b * (Nat.log 2 (k + 1) + 1)))
            k).distance ≤ (1 / 2) ^ (k + 1)) := by
  obtain ⟨m, b, hm, hlam, hell, h⟩ := Probability.PMF.exists_polarization hβ hβα hα hα1
  refine ⟨m, b, hm, hlam, hell, fun x k => ?_⟩
  have hpos : m * (Nat.log 2 (k + 1) + 1) - 1 + 1 = m * (Nat.log 2 (k + 1) + 1) :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hm (Nat.succ_ne_zero _)))
  rw [SDInstance.distance_polarize, hpos]
  exact h (x.left.outputDist interpretation) (x.right.outputDist interpretation) (k + 1)

/-- **Polarization maps `SD^{α,β}` into `SD^{1 - 2⁻⁽ᵏ⁺¹⁾, 2⁻⁽ᵏ⁺¹⁾}`** [SahaiVadhan2003, Lemma 3.3
and the remark after its proof], for every `k ≥ 1` and constant thresholds `0 ≤ β < α² ≤ 1`, with
the parameters of `SDInstance.exists_polarize`. At `k = 0` the two target thresholds are both
`1 / 2`, which is not a gap. -/
theorem StatisticalDifference.exists_mapsTo_polarize {α β : ℝ} (hβ : 0 ≤ β) (hβα : β < α ^ 2)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ m b : ℕ, m ≠ 0 ∧
      PolynomiallyBounded (fun k => m * (Nat.log 2 k + 1)) ∧
      PolynomiallyBounded (fun k => 2 ^ (b * (Nat.log 2 k + 1))) ∧
      ∀ k : ℕ, k ≠ 0 →
        Set.MapsTo (fun x : SDInstance => x.polarize (m * (Nat.log 2 (k + 1) + 1) - 1)
            (2 ^ (b * (Nat.log 2 (k + 1) + 1))) k)
          (StatisticalDifference α β).yes
          (StatisticalDifference (1 - (1 / 2) ^ (k + 1)) ((1 / 2) ^ (k + 1))).yes ∧
        Set.MapsTo (fun x : SDInstance => x.polarize (m * (Nat.log 2 (k + 1) + 1) - 1)
            (2 ^ (b * (Nat.log 2 (k + 1) + 1))) k)
          (StatisticalDifference α β).no
          (StatisticalDifference (1 - (1 / 2) ^ (k + 1)) ((1 / 2) ^ (k + 1))).no := by
  obtain ⟨m, b, hm, hlam, hell, h⟩ := SDInstance.exists_polarize hβ hβα hα hα1
  refine ⟨m, b, hm, hlam, hell, fun k hk => ⟨fun x hx => (h x k).1 hx, fun x hx => ?_⟩⟩
  have hβα' : β < α := hβα.trans_le (pow_le_of_le_one hα hα1 two_ne_zero)
  have hgap : (1 / 2 : ℝ) ^ (k + 1) < 1 - (1 / 2) ^ (k + 1) := by
    have : (1 / 2 : ℝ) ^ k < 1 := pow_lt_one₀ (by norm_num) (by norm_num) hk
    rw [pow_succ]
    linarith
  rw [mem_no_statisticalDifference hβα'] at hx
  exact (mem_no_statisticalDifference hgap).2 ((h x k).2 hx)

end Cslib.Complexity
