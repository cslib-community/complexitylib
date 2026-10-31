/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Formula
import Complexity.Computability.Circuit.Monotone.BipartiteMatching.Asymptotic
import Complexity.Computability.Circuit.Monotone.Formula

/-!
# Tests: Razborov's lower bound for monotone circuits computing perfect matchings

Two disjoint edges form a matching and two edges at a vertex do not. The graph of the colouring of
`K_{2,2}` with only the left vertex `0` coloured `true` has no perfect matching, and a single edge
lies in the graphs of exactly half of the `16` colourings. The hypotheses of the explicit bound are
satisfiable, and at `⌊log₂ n⌋ = 320` an actual monotone circuit computing perfect matching, the
formula of `Cslib.Circuits.Monotone.exists_computes_of_monotone`, has more than `2 ^ 400` gates.
-/

namespace ComplexityTests.MonotoneBipartiteMatchingRazborov

open Cslib Cslib.Circuits Cslib.Circuits.BipartiteMatching

/-- Two disjoint edges form a matching. -/
example : IsMatching ({(0, 0), (1, 1)} : Finset (Fin 2 × Fin 2)) := by decide

/-- Two edges at the same left vertex do not. -/
example : ¬IsMatching ({(0, 0), (0, 1)} : Finset (Fin 2 × Fin 2)) := by decide

/-- The graph of the colouring with only the left vertex `0` coloured `true` has no perfect
matching: that vertex has no neighbour. -/
example : bipartitePerfectMatching 2 (ofColoring fun v => decide (v = .inl 0)) = false := by
  decide

/-- The graph of the constant colouring is complete, and has a perfect matching. -/
example : bipartitePerfectMatching 2 (ofColoring fun _ => true) = true := by decide

/-- A single edge lies in the graphs of `4 ^ 2 / 2 = 8` of the `16` colourings of `K_{2,2}`. -/
example : (Finset.univ.filter fun c : Coloring 2 => Contains (ofColoring c) {(0, 1)}).card = 8 := by
  have := card_filter_contains_ofColoring_mul_two_pow (n := 2) (isMatching_singleton ((0, 1) :
    Fin 2 × Fin 2))
  simp only [Finset.card_singleton, pow_one] at this
  omega

/-- `C(8, 4) ^ 2 · 9 = 44100 ≤ 16 ^ 4`. -/
example : Nat.centralBinom 4 ^ 2 * (2 * 4 + 1) ≤ 16 ^ 4 := centralBinom_sq_mul_le 4

/-- The hypotheses of the explicit bound hold at `s = q = 1`, `r = 2` and `n = 8`. -/
example : (1 * 1) ^ 2 < 2 ∧ 4 ^ (1 + 1) ≤ 2 * 8 + 1 := by norm_num

-- Unifying with `2 ^ 320` evaluates it, beyond the default `exponentiation.threshold` of `256`.
set_option exponentiation.threshold 512 in
/-- `⌊log₂ 2 ^ 320⌋ = 320`, so the asymptotic bound applies to `n = 2 ^ 320`. -/
example : Nat.log 2 (2 ^ 320) = 320 := Nat.log_pow Nat.one_lt_two 320

-- `simp` evaluates `2 ^ 400`, beyond the default `exponentiation.threshold` of `256`.
set_option exponentiation.threshold 512 in
/-- **The `n ^ Ω(log n)` bound instantiated** at `⌊log₂ n⌋ = 320` on an actual monotone circuit
computing perfect matching: it has more than `2 ^ ((320 / 16) ^ 2) = 2 ^ 400` gates. -/
example {n : ℕ} (hn : Nat.log 2 n = 320) : ∃ C : Circuit Monotone.signature (n * n) 1,
    C.Computes Monotone.interpretation (single (bipartitePerfectMatching n)) ∧
      2 ^ 400 < C.size := by
  obtain ⟨F, hF⟩ :=
    Monotone.exists_computes_of_monotone (monotone_bipartitePerfectMatching (n := n))
  refine ⟨F.toCircuit, hF.toCircuit, ?_⟩
  simpa [hn] using Monotone.two_pow_sq_lt_size_of_computes_bipartitePerfectMatching hn.ge
    hF.toCircuit

end ComplexityTests.MonotoneBipartiteMatchingRazborov
