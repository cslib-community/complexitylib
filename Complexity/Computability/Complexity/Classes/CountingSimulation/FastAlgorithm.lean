/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.CountingSimulation.Guarded
public import Complexity.Computability.Complexity.Classes.CountingSimulation.Admissible
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionMachine
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The fast contraction algorithm, assembled

The guard of the fast contraction algorithm (`CountingSimulation.fastGuard`) tests what
`ExplicitAdmissible` already implies (rows first, full tables) and the degree bound
`degreeBound m` of the schedule (§D.4.2 of [OpenAI2026ETH], (D.6), p. 58). An admissible network of
degree at most `C ⌊log₂ s⌋` fails it only for `s` below a threshold depending on `C`
(`CountingSimulation.exists_le_of_fastGuard_eq_false`), since `degreeBound m ≥ m ^ (9 / 10)` and
`m ≥ s`.

## Main definitions

* `Cslib.Complexity.CountingSimulation.fastGuard`: the guard.

## Main results

* `Cslib.Complexity.CountingSimulation.exists_le_of_fastGuard_eq_false`: admissible networks
  failing the guard are small.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Theorem D.1 (p. 53) and
  Appendix D.4.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open Cslib.Circuits.Frontier Cslib.Circuits.Frontier.ContractionSchedule Filter

/-- **The guard of the fast algorithm**: the network is rows-first bipartite at its number of
rows, every table lists the values at all bit strings on its ports, and its maximum degree is at
most `degreeBound m`, for `m` its number of edges. -/
@[expose] def fastGuard (G : ℕ × ExplicitTensorNetwork ℕ) : Bool :=
  decide (G.2.IsRowsFirstBipartite G.1 ∧ (∀ v ∈ G.2.vertices, v.2.length = 2 ^ v.1.length) ∧
    G.2.maxDegree ≤ degreeBound G.2.numEdges)

/-- A power of the logarithm is eventually below a power: `(C L) ^ 10 ≤ 2 ^ (9 L)` from some
`L₀` on. -/
private theorem exists_pow_ten_le (C : ℕ) : ∃ L₀, ∀ L, L₀ ≤ L → (C * L) ^ 10 ≤ 2 ^ (9 * L) := by
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt 10 (r := (2 : ℝ) ^ 9) (by norm_num)
  have hC : (0 : ℝ) < 1 / ((C : ℝ) ^ 10 + 1) := by positivity
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp ((tendsto_order.1 hlim).2 _ hC)
  refine ⟨L₀, fun L hL => ?_⟩
  have h := hL₀ L hL
  have h2 : (0 : ℝ) < ((2 : ℝ) ^ 9) ^ L := by positivity
  have h1 : (0 : ℝ) < (C : ℝ) ^ 10 + 1 := by positivity
  rw [div_lt_div_iff₀ h2 h1, one_mul] at h
  have hL10 : (0 : ℝ) ≤ (L : ℝ) ^ 10 := by positivity
  have hle : ((C * L) ^ 10 : ℕ) ≤ ((2 ^ (9 * L) : ℕ) : ℝ) := by
    push_cast
    rw [mul_pow, pow_mul]
    nlinarith
  exact_mod_cast hle

/-- **Admissible networks failing the guard are small.** For every `C` there is `s₀` such that a
network admissible at size `s` with constant `C` that fails `fastGuard` has `s ≤ s₀`. -/
theorem exists_le_of_fastGuard_eq_false (C : ℕ) :
    ∃ s₀, ∀ s G, ExplicitAdmissible C s G → fastGuard G = false → s ≤ s₀ := by
  obtain ⟨L₀, hL₀⟩ := exists_pow_ten_le C
  refine ⟨2 ^ L₀, fun s G hA hg => ?_⟩
  obtain ⟨hrows, -, hdeg, -, htab, hsm⟩ := hA
  have hbig : degreeBound G.2.numEdges < G.2.maxDegree := by
    simp only [fastGuard, decide_eq_false_iff_not, not_and, not_le] at hg
    exact hg hrows htab
  by_contra hs
  rw [not_le] at hs
  have hL : L₀ ≤ Nat.log 2 s := Nat.le_log_of_pow_le one_lt_two hs.le
  have h1 : s ^ 9 ≤ G.2.numEdges ^ 9 := Nat.pow_le_pow_left hsm 9
  have h2 := pow_nine_le_degreeBound_pow_ten G.2.numEdges
  have h3 : degreeBound G.2.numEdges ^ 10 < (C * Nat.log 2 s) ^ 10 :=
    Nat.pow_lt_pow_left (hbig.trans_le hdeg) (by norm_num)
  have h4 := hL₀ _ hL
  have h5 : 2 ^ (9 * Nat.log 2 s) ≤ s ^ 9 := by
    rw [pow_mul']
    exact Nat.pow_le_pow_left
      (Nat.pow_log_le_self 2 (by have := Nat.one_le_two_pow (n := L₀); omega)) 9
  omega

end Cslib.Complexity.CountingSimulation
