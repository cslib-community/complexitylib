/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Continuity
public import Cslib.Computability.Circuit.Boolean.Complexity
public import Mathlib.Basic.Real.Basic
import CslibFrontier.Computability.Circuit.Boolean.SparseSynthesis

/-!
# Square-root continuity of De Morgan circuit complexity

For the De Morgan basis on `n = 2 p` inputs, the sparse synthesis bounds of
`CslibFrontier.Computability.Circuit.Boolean.SparseSynthesis` locate the modulus of continuity
`ω_{2p,m}(r)` of circuit complexity (`Cslib.Circuits.complexityModulus`) at the square root
`r = 2 ^ p` of the number of inputs. For every `ε > 0` and all large `p`:

* `ω_{2p,1}(2 ^ p) ≤ (1 + ε) 2 ^ p` for a single output
  (`Cslib.Circuits.Boolean.complexityModulus_two_pow_single_output_le`);
* `ω_{2p,m}(2 ^ p) ≤ (3 + ε) 2 ^ p` for `m ≤ 2 p` outputs
  (`Cslib.Circuits.Boolean.complexityModulus_two_pow_le`).

The order `2 ^ p` is optimal: for every `p ≥ 4`, `2 ^ p ≤ 16 ω_{2p,1}(2 ^ p)`
(`Cslib.Circuits.Boolean.two_pow_le_sixteen_mul_complexityModulus`).

These restate `Cslib.Circuits.Boolean.SparseSynthesis.dist_complexity_single_le`,
`Cslib.Circuits.Boolean.SparseSynthesis.dist_complexity_le` and
`Cslib.Circuits.Boolean.SparseSynthesis.exists_hammingDist_eq_le_dist_complexity` in terms of the
modulus.

## Main results

* `Cslib.Circuits.Boolean.complexityModulus_two_pow_single_output_le`,
  `Cslib.Circuits.Boolean.complexityModulus_two_pow_le`: square-root continuity.
* `Cslib.Circuits.Boolean.two_pow_le_sixteen_mul_complexityModulus`: its optimality.

## References

* [A. V. Chashkin, *On computing partial Boolean functions*][Chashkin2024]
-/

public section

namespace Cslib.Circuits.Boolean

/-- A function with one output is the single-valued function of its output. -/
private theorem single_apply_zero {n : ℕ} (f : BitString n → Fin 1 → Bool) :
    single (fun x => f x 0) = f :=
  funext fun x => funext fun o => by rw [Subsingleton.elim o 0]; rfl

/-- **Square-root continuity for a single output**: for every `ε > 0` and all large `p`, changing
a Boolean function on at most `2 ^ p` of its `2 ^ (2 p)` inputs changes its De Morgan complexity
by at most `(1 + ε) 2 ^ p`, that is, `ω_{2p,1}(2 ^ p) ≤ (1 + ε) 2 ^ p`. -/
theorem complexityModulus_two_pow_single_output_le (ε : ℝ) (hε : 0 < ε) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀,
      (complexityModulus interpretation (2 * p) 1 (2 ^ p) : ℝ) ≤ (1 + ε) * 2 ^ p := by
  obtain ⟨p₀, hp₀⟩ := SparseSynthesis.dist_complexity_single_le ε hε
  refine ⟨p₀, fun p hp => ?_⟩
  obtain ⟨f, g, hfg, heq⟩ :=
    exists_dist_complexity_eq_complexityModulus (I := interpretation) (n := 2 * p) (m := 1)
      (r := 2 ^ p)
  rw [← heq, ← single_apply_zero f, ← single_apply_zero g]
  rw [← single_apply_zero f, ← single_apply_zero g, hammingDist_single] at hfg
  exact hp₀ p hp _ _ hfg

/-- **Square-root continuity**: for every `ε > 0` and all large `p`, changing a Boolean function
with at most `2 p` outputs on at most `2 ^ p` of its `2 ^ (2 p)` inputs changes its De Morgan
complexity by at most `(3 + ε) 2 ^ p`, that is, `ω_{2p,m}(2 ^ p) ≤ (3 + ε) 2 ^ p` for
`m ≤ 2 p`. -/
theorem complexityModulus_two_pow_le (ε : ℝ) (hε : 0 < ε) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ m ≤ 2 * p,
      (complexityModulus interpretation (2 * p) m (2 ^ p) : ℝ) ≤ (3 + ε) * 2 ^ p := by
  obtain ⟨p₀, hp₀⟩ := SparseSynthesis.dist_complexity_le ε hε
  refine ⟨p₀, fun p hp m hm => ?_⟩
  obtain ⟨f, g, hfg, heq⟩ :=
    exists_dist_complexity_eq_complexityModulus (I := interpretation) (n := 2 * p) (m := m)
      (r := 2 ^ p)
  rw [← heq]
  exact hp₀ p hp m f g hfg ((hammingDist_le_card_fintype).trans (by simpa using hm))

/-- **Square-root continuity is optimal**: for `p ≥ 4`, `2 ^ p ≤ 16 ω_{2p,1}(2 ^ p)`, witnessed
by a function differing from the constant `false` on exactly `2 ^ p` inputs. -/
theorem two_pow_le_sixteen_mul_complexityModulus {p : ℕ} (hp : 4 ≤ p) :
    2 ^ p ≤ 16 * complexityModulus interpretation (2 * p) 1 (2 ^ p) := by
  obtain ⟨f, hf, hle⟩ := SparseSynthesis.exists_hammingDist_eq_le_dist_complexity hp
  refine hle.trans (Nat.mul_le_mul_left 16 (dist_complexity_le_complexityModulus ?_))
  rw [hammingDist_single, hf]

end Cslib.Circuits.Boolean
