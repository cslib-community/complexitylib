/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Mathlib.Data.Nat.Prime.Defs
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div

/-!
# Primality of unary naturals by trial division

A natural `p` is prime exactly when `2 ≤ p` and no `m` with `2 ≤ m < p` divides it
(`Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_prime_eq`). Testing every candidate below
`p` takes time polynomial in `p`, hence in the length of its unary encoding
(`Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_decide_prime`).

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_prime_eq`: primality by trial division.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_decide_prime`: in polynomial time.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Primality by trial division. -/
theorem decide_prime_eq (p : ℕ) : decide p.Prime =
    (decide (2 ≤ p) && (List.range p).all fun m => decide (m < 2) || decide (p % m ≠ 0)) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.prime_def_lt']
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, ne_eq, Nat.dvd_iff_mod_eq_zero]
  refine and_congr_right fun _ => ⟨fun h m hm => ?_, fun h m h2 hm => ?_⟩
  · by_cases h2 : m < 2
    · exact Or.inl h2
    · exact Or.inr (h m (by omega) hm)
  · exact (h m hm).resolve_left (by omega)

/-- Primality of a unary natural, by trial division. -/
@[fun_prop]
theorem unary_decide_prime :
    ComputableTidilyInPolyTime (fun p : ℕ => decide p.Prime) encUnary encBool := by
  simp_rw [decide_prime_eq]
  fun_prop

end Turing.MultiTapeTM.ComputableTidilyInPolyTime
