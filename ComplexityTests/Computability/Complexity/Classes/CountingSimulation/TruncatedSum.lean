/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Complexity.Classes.CountingSimulation.TruncatedSum
public import ComplexityTests.Computability.Circuit.Frontier.TensorNetworkTruncatedAlgorithm
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Tests for the loop summing truncated contractions

The resource bound of the loop is not vacuous. It applies to direct summation on networks of
boundedly many edges (the test instance `boundedAlgorithm` of the interface of Theorem D.1 at
truncation order `ℓ`) with the empty network at precision and truncation order `n + 1`, and every
context `n` satisfies its hypotheses. The loop over two empty networks is `2` modulo
`2 ^ (n + 1)`: the empty network contracts to `1`, whose coefficients below `V ^ (n + 1)` sum to
`1`.
-/

@[expose] public section

namespace ComplexityTests.TruncatedSum

open Cslib Cslib.GenericRAM Cslib.Circuits.Frontier Cslib.Complexity.CountingSimulation
  Turing.MultiTapeTM Finset ComplexityTests.TensorNetworkTruncatedAlgorithm

/-- The empty network, at precision and truncation order `n + 1`, for every index. -/
def build (q : ℕ × ℕ) : ℕ × ℕ × ℕ × DescribedNetwork (List ℕ) :=
  (q.1 + 1, q.1 + 1, 0, ⟨0, []⟩)

theorem build_polyTime :
    ComputableInPolyTime build (encPair encUnary encNat) (encTrunc (encList encNat)) := by
  unfold build
  fun_prop

theorem modulus_polyTime :
    ComputableInPolyTime (fun n : ℕ => 2 ^ (n + 1)) encUnary encNat :=
  ComputableInPolyTime.binary_two_pow.comp
    (by fun_prop : ComputableInPolyTime (fun n : ℕ => n + 1) encUnary encUnary)

theorem count_polyTime : ComputableInPolyTime (fun _ : ℕ => 2) encUnary encNat := by
  fun_prop

/-- **The resource bound applies to every context**: the empty networks have no edges, and
precision and truncation order `n + 1` lie between `1` and `n + 2`. -/
example : ∃ (cs : NativeCertificate
      (truncSum constEntry build (fun n => 2 ^ (n + 1)) fun _ => 2) encUnary encNat) (K : ℕ),
    ∀ n : ℕ, cs.time n ≤ 3 * (K * ((encUnary n).length + 1) ^ K *
        2 ^ (K * (n + 2) / Nat.sqrt (Nat.log 2 (n + 2)))) ∧
      cs.space n ≤ K * ((encUnary n).length + 1) ^ K := by
  obtain ⟨cs, K, hK⟩ := exists_truncSum_certificate boundedAlgorithm build_polyTime
    modulus_polyTime count_polyTime (fun n => Nat.two_pow_pos _) 0 1 (fun n => n + 2)
  refine ⟨cs, K, fun n => hK n (by omega) fun i _ => ?_⟩
  simp only [build, BoundedEdges, le_refl, and_true]
  omega

/-- The empty network contracts to `1`, so its truncated contraction is `[1, 0, …, 0]` and each
term is `1`; the loop over two networks is `2` modulo `2 ^ (n + 1)`. -/
example (n : ℕ) :
    truncSum constEntry build (fun n => 2 ^ (n + 1)) (fun _ => 2) n = 2 % 2 ^ (n + 1) := by
  have hpoly : DescribedNetwork.polyContraction constEntry
      (⟨0, []⟩ : DescribedNetwork (List ℕ)) = 1 := by
    simp [DescribedNetwork.polyContraction, DescribedNetwork.contraction]
  have hterm : ∀ i, truncCoeffSum constEntry (build (n, i)) = 1 := by
    intro i
    rw [build, truncCoeffSum_eq, hpoly, sum_range_succ']
    simp [Polynomial.coeff_one, Nat.one_mod_two_pow]
  rw [truncSum_eq]
  simp [hterm]

end ComplexityTests.TruncatedSum
