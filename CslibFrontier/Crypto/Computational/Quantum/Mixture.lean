/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Quantum
import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Probability.PMF.Uniform

/-!
# Fair mixtures of native quantum challenge ensembles

Mixing two challenge ensembles with a fair classical bit preserves native quantum
indistinguishability. The same circuit tests both branches: the concrete bound is the average
of the two branch bounds, with the input-length cap and separate qubit, gate and query budgets
unchanged. The bit is sampled by the challenge experiment, not by an additional circuit.

These are original closure results for the existing native model. They do not compile a typed
probabilistic reduction into a native circuit or claim a cost for challenge sampling.

## Main results

* `Cslib.Crypto.NativeQuantum.supportsLengthAt_bind_iff`: the support-length contract for a
  mixture is exactly the contract for every supported branch.
* `Cslib.Crypto.NativeQuantum.SupportsLength.bind`: propagate a common length cap through a
  mixture.
* `Cslib.Crypto.NativeQuantum.IndistinguishableWithin.bind_uniformBool`: average the concrete
  bounds for a fair mixture, using the same native test and resource budget.
* `Cslib.Crypto.NativeQuantum.ComputationallyIndistinguishable.bind_uniformBool`: fair mixtures
  preserve asymptotic native quantum indistinguishability.
-/

public section

namespace Cslib.Crypto.NativeQuantum

open Probability Quantum
open scoped NNReal

/-- A mixed ensemble meets a length cap exactly when every supported branch meets it. The
distribution of branches may depend on the security parameter. -/
theorem supportsLengthAt_bind_iff {ι : Type*} (μ : ℕ → PMF ι)
    (X : ι → ℕ → PMF (List Bool)) (L : ℕ → ℕ) (n : ℕ) :
    SupportsLengthAt (fun n => (μ n).bind (fun i => X i n)) L n ↔
      ∀ i ∈ (μ n).support, SupportsLengthAt (X i) L n := by
  constructor
  · intro h i hi x hx
    exact h x ((PMF.mem_support_bind_iff _ _ _).mpr ⟨i, hi, hx⟩)
  · intro h x hx
    obtain ⟨i, hi, hix⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
    exact h i hi x hix

/-- Mixing ensembles with a common length cap preserves that cap. -/
theorem SupportsLength.bind {ι : Type*} {X : ι → ℕ → PMF (List Bool)} {L : ℕ → ℕ}
    (h : ∀ i, SupportsLength (X i) L) (μ : ℕ → PMF ι) :
    SupportsLength (fun n => (μ n).bind (fun i => X i n)) L :=
  fun n => (supportsLengthAt_bind_iff μ X L n).mpr fun i _ => h i n

/-- A fair mixture averages the two concrete error bounds. The native test, input-length cap
and each of its three resource budgets are unchanged. -/
theorem IndistinguishableWithin.bind_uniformBool
    {X Y : Bool → ℕ → PMF (List Bool)} {L : ℕ → ℕ}
    {ε : Bool → ℕ → OracleCircuit.Resources → ℝ≥0}
    (h : ∀ b, IndistinguishableWithin (X b) (Y b) L (ε b)) :
    IndistinguishableWithin
      (fun n => (PMF.uniformOfFintype Bool).bind (fun b => X b n))
      (fun n => (PMF.uniformOfFintype Bool).bind (fun b => Y b n)) L
      (fun n budget => (ε false n budget + ε true n budget) / 2) := by
  intro n budget family hfamily
  have hbranch (b : Bool) := h b n budget family
    ⟨(supportsLengthAt_bind_iff _ X L n).mp hfamily.1 b
        (Probability.PMF.mem_support_uniformOfFintype b),
      (supportsLengthAt_bind_iff _ Y L n).mp hfamily.2.1 b
        (Probability.PMF.mem_support_uniformOfFintype b), hfamily.2.2⟩
  have hmix := Probability.CloseTo.bind_right_tsum (PMF.uniformOfFintype Bool)
    (fun b _ => Game.closeTo_iff_advantage_le.mpr (hbranch b))
  rw [Game.closeTo_iff_coe_advantage_le] at hmix
  apply ENNReal.coe_le_coe.mp
  convert hmix using 1 <;>
    norm_num [distinguishingGame, PMF.bind_bind, tsum_bool, PMF.uniformOfFintype_apply,
      ENNReal.coe_div, add_div, div_eq_mul_inv, add_mul, mul_comm, add_comm]

/-- Fair mixtures preserve asymptotic native quantum indistinguishability. The same uniform
circuit family tests both branches at every security parameter. -/
theorem ComputationallyIndistinguishable.bind_uniformBool
    {X Y : Bool → ℕ → PMF (List Bool)}
    (h : ∀ b, ComputationallyIndistinguishable (X b) (Y b)) :
    ComputationallyIndistinguishable
      (fun n => (PMF.uniformOfFintype Bool).bind (fun b => X b n))
      (fun n => (PMF.uniformOfFintype Bool).bind (fun b => Y b n)) := by
  rw [computationallyIndistinguishable_iff]
  intro family
  apply negligible_of_le
    (((computationallyIndistinguishable_iff.mp (h false)) family).add
      ((computationallyIndistinguishable_iff.mp (h true)) family))
  intro n
  simp only [distinguishingGame, PMF.bind_bind]
  apply Game.advantage_bind_le_nnreal
  intro b
  cases b
  · exact le_add_of_nonneg_right zero_le
  · exact le_add_of_nonneg_left zero_le

end Cslib.Crypto.NativeQuantum
