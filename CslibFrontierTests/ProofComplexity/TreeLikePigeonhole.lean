/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Logics.Propositional.Resolution.Pigeonhole
import CslibFrontier.Logics.Propositional.Resolution.TreeLikePigeonhole

/-!
# Tests: Prover–Delayer potentials and tree-like refutations of the pigeonhole principle

Partial assignments that falsify a clause and ones that do not; a two-valued potential that splits
and bounds the size of every refutation of `x ∧ ¬x` below by `2`; a concrete tree-like
refutation of `PHP^2_1` that the bounds apply to; instances of the `(n + 1 - h) ^ h` bound,
including a choice of `h` that beats `h = n / 2`, a comparison with the bound from Haken's theorem,
a weak instance with many pigeons, and the corresponding DPLL leaf bound.
-/

namespace CslibFrontierTests.ProofComplexity.TreeLikePigeonhole

open Cslib Cslib.Logic.PL Function

/-! ### Falsified clauses -/

/-- Setting `x₀` to `false` and `x₁` to `true` falsifies `x₀ ∨ ¬x₁`; leaving `x₁` unset does not. -/
example :
    Clause.FalsifiedBy (fun v : ℕ => if v = 0 then some false else some true)
      [(0, true), (1, false)] ∧
    ¬ Clause.FalsifiedBy (fun v : ℕ => if v = 0 then some false else none)
      [(0, true), (1, false)] := by
  refine ⟨fun l hl => ?_, fun h => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> rfl
  · have := h (1, false) (by simp)
    simp at this

/-! ### A two-valued potential for `x ∧ ¬x` -/

/-- `x₀ ∧ ¬x₀`. -/
private def ψ : CNF ℕ := [[(0, true)], [(0, false)]]

/-- `2` while `x₀` is unset, `1` once it is set. -/
private def μψ (ρ : ℕ → Option Bool) : ℕ := if ρ 0 = none then 2 else 1

/-- The potential `μψ` splits and is at most `1` on assignments falsifying a clause of `ψ`, so every
tree-like refutation of `ψ` has at least `2` nodes. -/
example (d : ψ.Derivation []) : 2 ≤ d.size := by
  refine CNF.Derivation.potential_none_le_size (φ := ψ) μψ (fun ρ v hv => ?_)
    (fun ρ c hc hρ => ?_) d
  · by_cases hv0 : v = 0
    · subst hv0
      simp [μψ, hv]
    · simp only [μψ, update_of_ne (Ne.symm hv0)]
      split_ifs <;> omega
  · simp only [ψ, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · have := hρ (0, true) (by simp)
      simp [μψ, this]
    · have := hρ (0, false) (by simp)
      simp [μψ, this]

/-! ### A tree-like refutation of `PHP^2_1` -/

/-- Resolve each pigeon clause against the hole clause: a tree-like refutation of `PHP^2_1` with
five nodes. -/
private def php21 : (CNF.pigeonhole 2 1).Derivation [] :=
  (CNF.Derivation.resolvent (1, 0) (.mem (c := [((1, 0), true)]) (by decide))
    (CNF.Derivation.resolvent (0, 0) (.mem (c := [((0, 0), true)]) (by decide))
      (.mem (c := [((0, 0), false), ((1, 0), false)]) (by decide)) (by decide) (by decide))
    (by decide) (by decide) : (CNF.pigeonhole 2 1).Derivation _)

example : php21.size = 5 := rfl

/-- The bounds apply to an actual refutation: at `h = 1` the bound `(1 + 1 - 1) ^ 1 = 1` holds for
`php21`, and every refutation of `PHP^2_1` has at least one node. -/
example : (1 + 1 - 1) ^ 1 ≤ php21.size :=
  php21.pow_le_size_pigeonhole 1 (by decide)

/-! ### Instances of the lower bound -/

/-- `PHP^5_4` at `h = 2`: at least `3 ^ 2 = 9` nodes. -/
example (d : (CNF.pigeonhole 5 4).Derivation []) : 9 ≤ d.size :=
  d.pow_le_size_pigeonhole 2 (by decide)

/-- The weak pigeonhole formula `PHP^100_4` needs as many nodes as `PHP^5_4`. -/
example (d : (CNF.pigeonhole 100 4).Derivation []) : 9 ≤ d.size :=
  d.pow_le_size_pigeonhole 2 (by decide)

/-- At `n = 10`, `h = 7` gives `4 ^ 7 = 16384` nodes, more than the `6 ^ 5 = 7776` of
`h = n / 2`. -/
example (d : (CNF.pigeonhole 11 10).Derivation []) :
    16384 ≤ d.size ∧ (10 / 2 + 1) ^ (10 / 2) < 16384 :=
  ⟨d.pow_le_size_pigeonhole 7 (by decide), by decide⟩

/-- At `n = 48`, the bound `(n / 2 + 1) ^ (n / 2) = 25 ^ 24` far exceeds the `2 ^ (48 / 24) = 4`
that Haken's theorem gives. -/
example (d : (CNF.pigeonhole 49 48).Derivation []) :
    2 ^ (48 / 24) ≤ d.size ∧ 25 ^ 24 ≤ d.size :=
  ⟨CNF.Derivation.two_pow_le_size_pigeonhole (n := 48) d,
    d.pow_half_le_size_pigeonhole (by decide)⟩

/-- A DPLL search tree for `PHP^5_4` has at least `5` leaves. -/
example {t : DecisionTree (Fin 5 × Fin 4) (Clause (Fin 5 × Fin 4))}
    (ht : t.FindsFalsifiedClause (CNF.pigeonhole 5 4)) : 5 ≤ t.leafCount := by
  have := CNF.pow_lt_two_mul_leafCount_pigeonhole 2 (by decide) ht
  omega

end CslibFrontierTests.ProofComplexity.TreeLikePigeonhole
