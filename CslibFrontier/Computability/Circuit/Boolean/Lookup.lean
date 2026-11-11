/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Boolean.Complexity
public import Mathlib.Logic.Function.DependsOn
import Cslib.Computability.Circuit.Boolean.Synthesis
import CslibFrontier.Computability.Circuit.Boolean.Hierarchy
import CslibFrontier.Computability.Circuit.Boolean.Synthesis
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.GCongr

/-!
# Lookup tables and local maps

Two size bounds for multi-output Boolean functions, used when a circuit reads a hard-wired table.

A *lookup table* is an arbitrary map `D` from `a` index bits to `r` output bits. One shared
decoder computes the `2 ^ a` minterms of the index, with `2 a + 1` gates each, and every output
bit is the disjunction of the minterms of the indices where it is set. So `D` costs at most
`2 ^ a * (2 a + 1) + r * (2 ^ a + 1)` gates (`complexity_le_lookup`): linear in the number of
table entries times the index and output widths, instead of `r` separate truth tables.

A *local map* is one where every output bit depends on at most `t` inputs. Each output then costs
at most the truth-table bound on `t` inputs, so the whole map costs at most
`r * (2 ^ t * (2 t + 3) + 1)` gates (`complexity_le_mul_of_forall_dependsOn`); for constant `t`
this is linear in the number of outputs.

## Main results

* `Cslib.Circuits.Boolean.complexity_le_lookup`: a table on `a` index bits with `r` output bits
  costs at most `2 ^ a * (2 * a + 1) + r * (2 ^ a + 1)` gates.
* `Cslib.Circuits.Boolean.complexity_le_mul_of_forall_dependsOn`: a map whose `r` outputs each
  depend on at most `t` inputs costs at most `r * (2 ^ t * (2 * t + 3) + 1)` gates.
-/

public section

namespace Cslib.Circuits.Boolean

open Finset

variable {n a r t : ℕ}

/-- **Lookup tables.** Any map from `a` index bits to `r` output bits costs at most
`2 ^ a * (2 * a + 1) + r * (2 ^ a + 1)` gates: a shared decoder computes every minterm of the
index, and each output bit is the disjunction of the minterms of the indices where it is set. -/
theorem complexity_le_lookup (D : (Fin a → Bool) → Fin r → Bool) :
    complexity interpretation D ≤ 2 ^ a * (2 * a + 1) + r * (2 ^ a + 1) := by
  classical
  let minterm : (Fin a → Bool) → BooleanFunction a := fun v x => decide ((fun i => x (id i)) = v)
  have hmin : Synthesis interpretation (inputs a) (Set.range minterm)
      (∑ _v : Fin a → Bool, (2 * a + 1)) :=
    Synthesis.family minterm _ fun v => synthesis_minterm id v
  have hout (j : Fin r) : Synthesis interpretation (inputs a ∪ Set.range minterm) {fun x => D x j}
      (2 ^ a + 1) := by
    have h := Synthesis.exists_mem (s := inputs a ∪ Set.range minterm)
      (univ.filter fun v => D v j = true) minterm (fun _ => 0)
      fun v _ => Synthesis.of_mem (Set.mem_union_right _ ⟨v, rfl⟩)
    refine (Synthesis.congr_iff h fun x => ?_).mono Set.Subset.rfl Set.Subset.rfl ?_
    · simp [minterm]
    · simp only [zero_add, sum_const, smul_eq_mul, mul_one]
      have hcard : (univ.filter fun v : Fin a → Bool => D v j = true).card ≤ 2 ^ a := by
        simpa [Fintype.card_fun] using card_le_univ (univ.filter fun v => D v j = true)
      omega
  have hall := hmin.trans (Synthesis.family (fun j x => D x j) _ hout)
  obtain ⟨c, hc, hsize⟩ := hall.exists_circuit_outputs
  refine (complexity_le_of_computes c hc).trans (hsize.trans ?_)
  simp

/-- **Local maps.** A map whose `r` outputs each depend on at most `t` of its inputs costs at most
`r * (2 ^ t * (2 * t + 3) + 1)` gates: compute each output from its truth table on those inputs. -/
theorem complexity_le_mul_of_forall_dependsOn (f : (Fin n → Bool) → Fin r → Bool)
    (hf : ∀ j, ∃ s : Finset (Fin n), #s ≤ t ∧ DependsOn (fun x => f x j) s) :
    complexity interpretation f ≤ r * (2 ^ t * (2 * t + 3) + 1) := by
  refine (complexity_pi_le (I := interpretation) fun j x => f x j).trans ?_
  calc _ ≤ ∑ _j : Fin r, (2 ^ t * (2 * t + 3) + 1) := by
        refine sum_le_sum fun j _ => ?_
        obtain ⟨s, hs, hdep⟩ := hf j
        refine (complexity_le_of_dependsOn hdep).trans ?_
        gcongr
    _ = _ := by simp

end Cslib.Circuits.Boolean
