/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.MassProduction.Uhlig
import Cslib.Foundations.Data.Nat.Asymptotics
import CslibFrontier.Computability.Circuit.Complexity.Composition
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Mass production of a constant number of copies

Uhlig's theorem with a constant copy count. Eventually in `L`, every Boolean function `F` on `L`
inputs can be evaluated on any constant number `c` of independent inputs with
`(1 + 1 / P) 2 ^ L / L` gates (`eventually_mul_complexity_directProduct_le_of_le`), uniformly in
`F`. A circuit that reads a hard-wired table `F` at `c` addresses therefore costs this much plus the
cost of computing the addresses and of combining the inputs with the `c` table values
(`eventually_mul_complexity_table_le`).

The threshold beyond which these bounds hold is existential: it comes from Lupanov's bound and is
not computed.

## Main results

* `Cslib.Circuits.Boolean.MassProduction.isUhligDepth_const`: a constant depth satisfies Uhlig's
  depth condition.
* `Cslib.Circuits.Boolean.MassProduction.eventually_mul_complexity_directProduct_le_of_le`: at most
  `c` copies of any function on `L` inputs cost at most `(1 + 1 / P) 2 ^ L / L` gates.
* `Cslib.Circuits.Boolean.MassProduction.complexity_table_le`: reading a table at `c` computed
  addresses and combining the values costs at most the sum of the three parts.
* `Cslib.Circuits.Boolean.MassProduction.eventually_mul_complexity_table_le`: the eventual bound
  for such table circuits.

## References

* [D. Uhlig, *Networks computing Boolean functions for multiple input values*][Uhlig1992].
* [I. Wegener, *The Complexity of Boolean Functions*, Theorem 10.2.3][Wegener1987].
-/

public section

namespace Cslib.Circuits.Boolean.MassProduction

open Filter

/-- A constant depth satisfies Uhlig's depth condition `d(n) log₂ n = o(n)`. -/
theorem isUhligDepth_const (d : ℕ) : IsUhligDepth fun _ => d := fun c => by
  simpa only [mul_assoc] using Nat.eventually_mul_log_le (c * d) one_lt_two

/-- **Uhlig's theorem for a constant number of copies.** For every precision `P` and copy bound
`c`, eventually every function `F` on `L` inputs has `k ≤ c` independent copies of size `s` with
`P * L * s ≤ (P + 1) * 2 ^ L`: for `P > 0`, at most `(1 + 1 / P) 2 ^ L / L`.

The threshold `L₀` beyond which this holds is existential (it comes from Lupanov's bound); a
client that needs it as a number obtains it with `Filter.eventually_atTop`. -/
theorem eventually_mul_complexity_directProduct_le_of_le (P c : ℕ) :
    ∀ᶠ L in atTop, ∀ (F : BooleanFunction L) (k : ℕ), k ≤ c →
      P * L * complexity interpretation (directProduct F k) ≤ (P + 1) * 2 ^ L := by
  filter_upwards [eventually_mul_complexity_directProduct_le (isUhligDepth_const c) P]
    with L hL F k hk
  exact hL F k (hk.trans Nat.lt_two_pow_self.le)

/-- **Table circuits.** Reading a table `F` on `L` inputs at `c` addresses computed from the input
`x`, and combining `x` with the `c` table values by `G`, costs at most the complexity of the
addresses, plus that of `c` copies of `F`, plus that of `G`. -/
theorem complexity_table_le {n L c p : ℕ} (F : BooleanFunction L)
    (addr : (Fin n → Bool) → Fin (c * L) → Bool) (G : (Fin (n + c) → Bool) → Fin p → Bool) :
    complexity interpretation (fun x => G (Fin.append x (directProduct F c (addr x)))) ≤
      complexity interpretation addr + complexity interpretation (directProduct F c) +
        complexity interpretation G := by
  refine (complexity_comp_append_le (fun x => directProduct F c (addr x)) G).trans ?_
  gcongr
  exact complexity_comp_le addr (directProduct F c)

/-- **Table circuits, eventually.** For every precision `P` and constant copy count `c`,
eventually in `L`, reading any table `F` on `L` inputs at `c` computed addresses and combining the
input with the values costs at most `(1 + 1 / P) 2 ^ L / L` gates plus the cost of the addresses
and of the combining map: `P * L * s ≤ (P + 1) * 2 ^ L + P * L * (s_addr + s_G)`.

The threshold `L₀` beyond which this holds is existential, as in
`eventually_mul_complexity_directProduct_le_of_le`; a client obtains it with
`Filter.eventually_atTop`. -/
theorem eventually_mul_complexity_table_le (P c : ℕ) :
    ∀ᶠ L in atTop, ∀ {n p : ℕ} (F : BooleanFunction L)
      (addr : (Fin n → Bool) → Fin (c * L) → Bool) (G : (Fin (n + c) → Bool) → Fin p → Bool),
      P * L * complexity interpretation
          (fun x => G (Fin.append x (directProduct F c (addr x)))) ≤
        (P + 1) * 2 ^ L +
          P * L * (complexity interpretation addr + complexity interpretation G) := by
  filter_upwards [eventually_mul_complexity_directProduct_le_of_le P c] with L hL n p F addr G
  have h := Nat.mul_le_mul_left (P * L) (complexity_table_le F addr G)
  have hF := hL F c le_rfl
  calc _ ≤ P * L * (complexity interpretation addr +
        complexity interpretation (directProduct F c) + complexity interpretation G) := h
    _ = P * L * complexity interpretation (directProduct F c) +
        P * L * (complexity interpretation addr + complexity interpretation G) := by ring
    _ ≤ _ := Nat.add_le_add_right hF _

end Cslib.Circuits.Boolean.MassProduction
