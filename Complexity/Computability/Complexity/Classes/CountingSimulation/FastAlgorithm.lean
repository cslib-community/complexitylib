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

/-! ### The clock -/

open FastContraction in
/-- **The clock is subexponential on admissible inputs**: with `m ≤ C s` edges and precision
`P ≤ D s`, it is at most `2 ^ (K₀ (C + D) s / √⌊log₂ s⌋)`. -/
theorem fuel_le {C D s P : ℕ} {G : ℕ × ExplicitTensorNetwork ℕ} (hA : ExplicitAdmissible C s G)
    (hs : 2 ≤ s) (hP : P ≤ D * s) :
    fuel (ExplicitTensorNetwork.capPrecision (P, G)) ≤
      2 ^ (fuelConst * (C + D) * s / Nat.sqrt (Nat.log 2 s)) := by
  obtain ⟨-, hm, -, -, -, hsm⟩ := hA
  simp only [fuel, ExplicitTensorNetwork.capPrecision]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  set x := G.2.numEdges + min (ExplicitTensorNetwork.encExplicitNetwork G.2).length P
  have hx : x ≤ (C + D) * s := by
    have := min_le_right (ExplicitTensorNetwork.encExplicitNetwork G.2).length P
    rw [add_mul]; omega
  have hsx : s ≤ x := by omega
  have hq : 1 ≤ Nat.sqrt (Nat.log 2 s) := by
    rw [Nat.le_sqrt, Nat.one_mul]; exact Nat.le_log_of_pow_le one_lt_two (by simpa using hs)
  have hq' : Nat.sqrt (Nat.log 2 s) ≤ Nat.sqrt (Nat.log 2 x) :=
    Nat.sqrt_le_sqrt (Nat.log_mono_right hsx)
  calc fuelConst * x / Nat.sqrt (Nat.log 2 x) ≤ fuelConst * x / Nat.sqrt (Nat.log 2 s) :=
        Nat.div_le_div_left hq' hq
    _ ≤ fuelConst * (C + D) * s / Nat.sqrt (Nat.log 2 s) := by
        refine Nat.div_le_div_right ?_
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ hx

/-! ### The resources of the fast machine -/

section Resources

open FastContraction Cslib.GenericRAM Cslib.GenericRAM.StackRecursion Turing.MultiTapeTM

variable (mk : Call → ChildCursor.State → ℕ × DescribedNetwork VertexDesc)

/-- **The resource analysis of the fast machine**, the remaining obligation of the running time.
For all constants `C` and `D` there are `K` and `s₀` such that on every input `(P, r, G)` with
`2 ≤ s`, `1 ≤ P ≤ D s`, `G` admissible at size `s` with constant `C` and passing the guard, the
root of the capped input has a derivation whose nodes, frames and values are at most `F` long,
whose leaves take time at most `TL` and space at most `SL`, with `H` open calls, such that
`H + F + SL ≤ K (n + 1) ^ K` and `TL ≤ K (n + 1) ^ K 2 ^ (K s / √⌊log₂ s⌋)` for the input length
`n`; and from `s₀` on its `N` nodes fit in the clock, `2 N - 1 ≤ fuel`. -/
@[expose] def FastAnalysis : Prop :=
  ∀ C D : ℕ, ∃ K s₀ : ℕ, ∀ (s P : ℕ) (G : ℕ × ExplicitTensorNetwork ℕ), 2 ≤ s → 1 ≤ P →
    P ≤ D * s → ExplicitAdmissible C s G → fastGuard G = true →
    ∃ (I : Invariant Call Frame (ℕ × List ℕ)) (N H F TL SL : ℕ),
      (scheme mk).Eval I (root (ExplicitTensorNetwork.capPrecision (P, G)))
        (0, value mk (root (ExplicitTensorNetwork.capPrecision (P, G)))) N H ∧
      (s₀ ≤ s → 2 * N - 1 ≤ fuel (ExplicitTensorNetwork.capPrecision (P, G))) ∧
      (∀ x, I.node x → (encCall x).length ≤ F ∧ ((scheme mk).isLeaf x = true →
        (leafCertificate mk).time x ≤ TL ∧ (leafCertificate mk).space x ≤ SL)) ∧
      (∀ x a, I.frame x a → (encPair encCall encFrame (x, a)).length ≤ F) ∧
      (∀ v, I.value v → (encValue v).length ≤ F) ∧
      H + F + SL ≤ K * ((FastContraction.encInput (P, G)).length + 1) ^ K ∧
      TL ≤ K * ((FastContraction.encInput (P, G)).length + 1) ^ K *
        2 ^ (K * s / Nat.sqrt (Nat.log 2 s))

/-- `c B ^ d ≤ c B ^ E X` for `1 ≤ B`, `d ≤ E` and `1 ≤ X`. -/
private theorem lift_le {c B d E X : ℕ} (hB : 1 ≤ B) (hd : d ≤ E) (hX : 1 ≤ X) :
    c * B ^ d ≤ c * B ^ E * X :=
  (Nat.mul_le_mul_left c (Nat.pow_le_pow_right hB hd)).trans (Nat.le_mul_of_pos_right _ hX)

end Resources

end Cslib.Complexity.CountingSimulation
