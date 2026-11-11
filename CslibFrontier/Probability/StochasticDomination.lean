/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.PoissonBinomial
public import CslibFrontier.Probability.StochasticDomination.Basic
public import CslibFrontier.Probability.StochasticDomination.PoissonBinomial
public import CslibFrontier.Probability.StochasticDomination.Adapted
public import CslibFrontier.Probability.StochasticDomination.Stopping

/-!
# Stochastic domination of adapted Bernoulli counts

Umbrella module importing the base stochastic-domination toolkit:

* `CslibFrontier.Probability.StochasticDomination.Basic`: first-order stochastic order on
  `MeasureTheory.Measure` and `PMF` (preorder, `ℕ`, `ℝ`, `Bool`, CDF/integral characterizations,
  and closure properties).
* `CslibFrontier.Probability.PoissonBinomial`: Poisson-binomial distributions on `ℕ`.
* `CslibFrontier.Probability.StochasticDomination.PoissonBinomial`: parameter monotonicity, binomial
  specialization, and the negative-binomial survival-series identity `∑' t, Bin(t, p)(< r)`.
* `CslibFrontier.Probability.StochasticDomination.Adapted`: Poisson-binomial stochastic
  domination for adapted Bernoulli sequences (`Filtration ℕ m`, `Kernel.traj`, `Kernel.trajMeasure`,
  and finite-horizon sequential `PMF` processes).
* `CslibFrontier.Probability.StochasticDomination.Stopping`: `WithTop ℕ` survival-series
  expectation identity and infinite-horizon stopping-time mean bounds `𝔼[τ] ≤ r / p`.
-/
