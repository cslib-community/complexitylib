/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.MarkovChain.Basic

/-!
# Metropolis chains

Given a proposal chain `Ψ` and a target distribution `π`, the Metropolis chain at `x` draws a
candidate `y ~ Ψ x`, accepts it with probability `min (π y Ψ(y, x) / (π x Ψ(x, y))) 1` and
otherwise stays at `x` ([LevinPeres2017], Section 3.2.2, (3.4)). For a symmetric proposal
the acceptance ratio is `π y / π x` (Section 3.2.1). Every Metropolis chain is reversible with
respect to `π`, and so has `π` as a stationary distribution ([LevinPeres2017],
Section 3.2 and Exercise 3.1).

The construction is total. Ratios are computed in `ℝ≥0∞`, where `d / 0 = ⊤` for `d ≠ 0` and
`0 / 0 = 0`. So if `π x Ψ(x, y) = 0` the move is always accepted when `π y Ψ(y, x) ≠ 0` and
always rejected when `π y Ψ(y, x) = 0`. Either way `π x P(x, y) = min (π x Ψ(x, y)) (π y Ψ(y, x))`
for `x ≠ y`. No positivity, irreducibility or symmetry hypothesis is needed for reversibility.
The source divides by `π x`, so it implicitly assumes `π` is positive; that assumption is not
needed here.

## Main definitions

* `Cslib.Probability.MarkovChain.acceptCoin`: a coin showing `true` with probability `min p 1`.
* `Cslib.Probability.MarkovChain.metropolisRatio`: the Metropolis–Hastings ratio.
* `Cslib.Probability.MarkovChain.metropolis`: the Metropolis chain for `Ψ` and `π`.

## Main results

* `Cslib.Probability.MarkovChain.metropolis_apply_of_ne`: off-diagonal transition probabilities,
  [LevinPeres2017], (3.5).
* `Cslib.Probability.MarkovChain.isReversible_metropolis`: detailed balance with respect to `π`.
* `Cslib.Probability.MarkovChain.isStationary_metropolis`: `π` is stationary.
* `Cslib.Probability.MarkovChain.metropolisRatio_of_symm`: the symmetric-proposal ratio.

## References

* [LevinPeres2017], Section 3.2.
-/

public section

open scoped ENNReal

namespace Cslib.Probability

namespace MarkovChain

variable {S : Type*}

/-- A coin showing `true` with probability `min p 1`. -/
noncomputable def acceptCoin (p : ℝ≥0∞) : PMF Bool :=
  PMF.ofFintype (fun b => if b then min p 1 else 1 - min p 1) (by
    simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
      Finset.sum_insert, ite_true, Finset.sum_singleton, Bool.false_eq_true, ite_false]
    exact add_tsub_cancel_of_le (min_le_right _ _))

@[simp] theorem acceptCoin_true (p : ℝ≥0∞) : acceptCoin p true = min p 1 := by
  rw [acceptCoin, PMF.ofFintype_apply, ite_eq_left rfl]

@[simp] theorem acceptCoin_false (p : ℝ≥0∞) : acceptCoin p false = 1 - min p 1 := by
  rw [acceptCoin, PMF.ofFintype_apply, ite_eq_right Bool.false_ne_true]

/-- The Metropolis–Hastings ratio `π(y) Ψ(y, x) / (π(x) Ψ(x, y))` for a move from `x` to `y`
([LevinPeres2017], (3.4)); the acceptance probability is its minimum with `1`. -/
noncomputable def metropolisRatio (Ψ : MarkovChain S) (π : PMF S) (x y : S) : ℝ≥0∞ :=
  π y * Ψ y x / (π x * Ψ x y)

/-- The Metropolis chain for the proposal chain `Ψ` and the target distribution `π`
([LevinPeres2017], Section 3.2.2): from `x`, propose `y ~ Ψ x`, move to `y` with probability
`min (metropolisRatio Ψ π x y) 1`, and otherwise stay at `x`. -/
noncomputable def metropolis (Ψ : MarkovChain S) (π : PMF S) : MarkovChain S where
  step x := (Ψ x).bind fun y =>
    (acceptCoin (metropolisRatio Ψ π x y)).map fun b => if b then y else x

/-- Off the diagonal, the Metropolis chain moves from `x` to `y` with probability
`Ψ(x, y) min (r(x, y)) 1` ([LevinPeres2017], (3.5)). -/
theorem metropolis_apply_of_ne (Ψ : MarkovChain S) (π : PMF S) {x y : S} (hxy : x ≠ y) :
    metropolis Ψ π x y = Ψ x y * min (metropolisRatio Ψ π x y) 1 := by
  change ((Ψ x).bind _) y = _
  rw [PMF.bind_apply, tsum_eq_single y]
  · congr 1
    rw [PMF.map_apply, tsum_eq_single true]
    · simp
    · intro b hb
      cases b
      · simp [Ne.symm hxy]
      · exact absurd rfl hb
  · intro z hz
    rw [PMF.map_apply]
    convert mul_zero (Ψ x z)
    refine tsum_eq_zero_iff.mpr fun b => ?_
    cases b <;> simp [Ne.symm hxy, Ne.symm hz]

private theorem mul_min_div_one {c d : ℝ≥0∞} (hc : c ≠ ⊤) : c * min (d / c) 1 = min d c := by
  rcases eq_or_ne c 0 with rfl | h0
  · simp
  · rw [mul_min, mul_one, ENNReal.mul_div_cancel h0 hc]

/-- The Metropolis chain satisfies detailed balance with respect to its target distribution:
`π(x) P(x, y) = min (π x Ψ(x, y)) (π y Ψ(y, x))` is symmetric in `x` and `y`
([LevinPeres2017], Section 3.2 and Exercise 3.1). -/
theorem isReversible_metropolis (Ψ : MarkovChain S) (π : PMF S) :
    (metropolis Ψ π).IsReversible π := by
  intro x y
  rcases eq_or_ne x y with rfl | hxy
  · rfl
  rw [metropolis_apply_of_ne Ψ π hxy, metropolis_apply_of_ne Ψ π (Ne.symm hxy), ← mul_assoc,
    ← mul_assoc, metropolisRatio, metropolisRatio,
    mul_min_div_one (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)),
    mul_min_div_one (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)), min_comm]

/-- The target distribution is stationary for the Metropolis chain. -/
theorem isStationary_metropolis (Ψ : MarkovChain S) (π : PMF S) :
    (metropolis Ψ π).IsStationary π :=
  (isReversible_metropolis Ψ π).isStationary

/-- For a symmetric proposal, the Metropolis ratio of a possible move is `π y / π x`
([LevinPeres2017], Section 3.2.1). -/
theorem metropolisRatio_of_symm (Ψ : MarkovChain S) (π : PMF S) {x y : S}
    (hΨ : Ψ x y = Ψ y x) (h0 : Ψ x y ≠ 0) : metropolisRatio Ψ π x y = π y / π x := by
  rw [metropolisRatio, hΨ, ENNReal.mul_div_mul_right _ _ (hΨ ▸ h0) (PMF.apply_ne_top _ _)]

end MarkovChain

end Cslib.Probability
