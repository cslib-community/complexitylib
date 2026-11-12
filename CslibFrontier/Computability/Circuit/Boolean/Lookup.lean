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

A *selected answer* reads one of `q` answer bits `z`, chosen by the inputs in a set `s`. Disjoining
one minterm conjoined with its selected answer wire for each assignment of `s` costs at most
`2 ^ #s * (2 #s + 3) + 1` gates whatever `q` is (`complexity_select_le`). Learners use this to read
the answers to their queries from input wires.

## Main results

* `Cslib.Circuits.Boolean.complexity_le_lookup`: a table on `a` index bits with `r` output bits
  costs at most `2 ^ a * (2 * a + 1) + r * (2 ^ a + 1)` gates.
* `Cslib.Circuits.Boolean.complexity_le_mul_of_forall_dependsOn`: a map whose `r` outputs each
  depend on at most `t` inputs costs at most `r * (2 ^ t * (2 * t + 3) + 1)` gates.
* `Cslib.Circuits.Boolean.complexity_select_le`: reading the answer bit selected by the inputs in
  `s` costs at most `2 ^ #s * (2 * #s + 3) + 1` gates.
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

/-- **Reading a selected answer.** On inputs `z ++ x`, returning the answer bit
`z (sel (x restricted to s))` costs at most `2 ^ #s * (2 * #s + 3) + 1` gates, the bound of
`complexity_le_of_dependsOn` for a function of `s` alone: one minterm and two gates for each
assignment of `s`. The answer bits `z` are not part of that count, whereas treating the map as a
function of `s` and all of `z` would cost `2 ^ (#s + q)`. -/
theorem complexity_select_le {q : ℕ} (s : Finset (Fin n)) (sel : (s → Bool) → Fin q) :
    complexity interpretation (single fun zx : Fin (q + n) → Bool =>
      zx (Fin.castAdd n (sel fun i => zx (Fin.natAdd q i)))) ≤ 2 ^ #s * (2 * #s + 3) + 1 := by
  classical
  let restr : (Fin (q + n) → Bool) → s → Bool := fun zx i => zx (Fin.natAdd q i)
  let wires : Fin #s → Fin (q + n) := fun i => Fin.natAdd q (s.equivFin.symm i)
  have hmin (v : s → Bool) : Synthesis interpretation (inputs (q + n))
      {fun zx => decide (restr zx = v)} (2 * #s + 1) := by
    have hmin_eq (zx : Fin (q + n) → Bool) :
        decide ((fun i => zx (wires i)) = v ∘ s.equivFin.symm) = decide (restr zx = v) := by
      refine decide_eq_decide.2 ⟨fun h => funext fun i => ?_, fun h => ?_⟩
      · simpa [wires, restr] using congrFun h (s.equivFin i)
      · subst h
        rfl
    simpa only [hmin_eq] using synthesis_minterm wires (v ∘ s.equivFin.symm)
  have h := Synthesis.exists_mem (s := inputs (q + n)) (univ : Finset (s → Bool))
    (fun v zx => decide (restr zx = v) && zx (Fin.castAdd n (sel v)))
    (fun _ => 2 * #s + 2) fun v _ => by
      have hread : Synthesis interpretation (inputs (q + n))
          {fun zx => zx (Fin.castAdd n (sel v))} 0 :=
        Synthesis.of_mem ⟨Fin.castAdd n (sel v), rfl⟩
      simpa only [Nat.add_zero, Nat.add_assoc] using (hmin v).and hread
  have hsel := Synthesis.congr_iff
    (g := fun zx => zx (Fin.castAdd n (sel (restr zx)))) h fun zx => by
      simp only [decide_eq_true_eq, mem_univ, true_and, Bool.and_eq_true]
      constructor
      · rintro ⟨v, hv, hz⟩
        rw [hv]
        exact hz
      · intro hz
        exact ⟨restr zx, rfl, hz⟩
  simpa [restr, Fintype.card_coe, Nat.add_assoc] using hsel.complexity_le

end Cslib.Circuits.Boolean
