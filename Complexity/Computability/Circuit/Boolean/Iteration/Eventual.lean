/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration.Target

/-!
# Circuits for eventual behaviour

Questions about arbitrarily late times reduce to one fixed power. Two orbits are ever in the
same state at the same time exactly when they are at time `2 ^ n`
(`FunctionalGraph.exists_iterate_eq_iterate_iff`), so synchronous coalescence costs two fixed
powers and an equality test (`synchronous_coalescence`). A recognized target recurs arbitrarily
late exactly when it is reachable from the cycle projection `f^[(2 ^ n)!] x`
(`recurring_target_circuit`), and it holds from some time on exactly when its complement does not
recur (`eventually_always_target_circuit`). Balancing the parameter gives the square-root bounds
(`synchronous_coalescence_optimized`, `recurring_target_optimized`,
`eventually_always_target_optimized`).

The circuits are native De Morgan circuits: every NOT, AND and OR gate and every constant is
charged, while wiring and fanout are free. They exist for each parameter choice; nothing here
bounds the time to construct them.

## Main results

* `Cslib.Circuits.Boolean.Iteration.synchronous_coalescence`,
  `Cslib.Circuits.Boolean.Iteration.synchronous_coalescence_optimized`: meeting orbits.
* `Cslib.Circuits.Boolean.Iteration.recurring_target_circuit`,
  `Cslib.Circuits.Boolean.Iteration.recurring_target_optimized`: recurring targets.
* `Cslib.Circuits.Boolean.Iteration.eventually_always_target_circuit`,
  `Cslib.Circuits.Boolean.Iteration.eventually_always_target_optimized`: eventually permanent
  targets.

## References

* Adapted from lean/Proofs/EventualQueries.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open FunctionalGraph

variable {n : ℕ}

/-- **Synchronous coalescence.** For every `0 < L ≤ 2 ^ n`, some circuit of size at most
`80000 * powerBudget n c.size (2 ^ n) L + 6 * n + 1` decides, for two states given as the two
halves of its input, whether their orbits are ever in the same state at the same time. -/
theorem synchronous_coalescence (c : Circuit signature n n) (L : ℕ) (hL : 0 < L)
    (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature (n + n) 1,
      (∀ z, out.eval interpretation z 0 = true ↔
        ∃ t, (c.eval interpretation)^[t] (fun i => z (Fin.castAdd n i)) =
          (c.eval interpretation)^[t] (fun i => z (Fin.natAdd n i))) ∧
      out.size ≤ 80000 * powerBudget n c.size (2 ^ n) L + 6 * n + 1 := by
  let f := c.eval interpretation
  obtain ⟨power, hp, hs⟩ := fixed_power n c (Fintype.card (BitString n)) L hL hLN
  let left := fun z : BitString (n + n) => fun i : Fin n => z (Fin.castAdd n i)
  let right := fun z : BitString (n + n) => fun i : Fin n => z (Fin.natAdd n i)
  have ha := Synthesis.circuit (I := interpretation) (s := inputs (n + n)) power
    (fun i z => left z i) fun i => ⟨_, rfl⟩
  have hb := Synthesis.circuit (I := interpretation) (s := inputs (n + n)) power
    (fun i z => right z i) fun i => ⟨_, rfl⟩
  have heq := synthesis_bits_eq (inputs (n + n) ∪ (wires (fun z => power.eval interpretation
      (left z)) ∪ wires fun z => power.eval interpretation (right z)))
    (fun z => power.eval interpretation (left z)) (fun z => power.eval interpretation (right z))
    (fun _ h => Or.inr (Or.inl h)) fun _ h => Or.inr (Or.inr h)
  obtain ⟨out, ho, hsize⟩ := ((ha.union hb).trans heq).exists_circuit
  refine ⟨out, fun z => ?_, by omega⟩
  rw [ho z]
  change decide (power.eval interpretation (left z) = power.eval interpretation (right z)) = true ↔
    _
  rw [decide_eq_true_iff, hp, hp]
  exact (exists_iterate_eq_iterate_iff f (left z) (right z)).symm

/-- **Square-root synchronous coalescence.** -/
theorem synchronous_coalescence_optimized (c : Circuit signature n n) :
    ∃ out : Circuit signature (n + n) 1,
      (∀ z, out.eval interpretation z 0 = true ↔
        ∃ t, (c.eval interpretation)^[t] (fun i => z (Fin.castAdd n i)) =
          (c.eval interpretation)^[t] (fun i => z (Fin.natAdd n i))) ∧
      (out.size : ℝ) ≤ 240000 * optimizedBudget n c.size (2 ^ n) + 6 * n + 1 := by
  obtain ⟨L, hL, hLN, hopt⟩ := exists_powerBudget_le_optimizedBudget n c.size (2 ^ n) le_rfl
  obtain ⟨out, ho, hs⟩ := synchronous_coalescence c L hL hLN
  refine ⟨out, ho, ?_⟩
  have hs' : (out.size : ℝ) ≤ 80000 * (powerBudget n c.size (2 ^ n) L : ℝ) + 6 * n + 1 := by
    exact_mod_cast hs
  linarith

/-- **Recurring targets.** For every `0 < L ≤ 2 ^ n`, some circuit of size at most
`80000 * powerBudget n (c.size + p.size + 4 * n) (2 ^ n) L + p.size` decides whether the orbit of
its input visits a state accepted by `p` at arbitrarily late times. -/
theorem recurring_target_circuit (c : Circuit signature n n) (p : Circuit signature n 1)
    (L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature n 1,
      (∀ x, out.eval interpretation x 0 = true ↔
        ∀ a, ∃ t, a ≤ t ∧ p.eval interpretation ((c.eval interpretation)^[t] x) 0 = true) ∧
      out.size ≤ 80000 * powerBudget n (c.size + p.size + 4 * n) (2 ^ n) L + p.size := by
  let f := c.eval interpretation
  obtain ⟨project, hp, hps⟩ := fixed_power n c (Fintype.card (BitString n)).factorial L hL hLN
  obtain ⟨target, ht, hts⟩ := target_reachability c p L hL hLN
  refine ⟨target.comp project, fun x => ?_, ?_⟩
  · rw [Circuit.eval_comp, ht, hp]
    exact (recurring_target_iff f (fun y => p.eval interpretation y 0 = true) x).symm
  · have hb : powerBudget n c.size (2 ^ n) L ≤
        powerBudget n (c.size + p.size + 4 * n) (2 ^ n) L := by
      unfold powerBudget
      gcongr
      omega
    rw [Circuit.size_comp]
    omega

/-- Negating a one-bit circuit costs one gate. -/
private theorem exists_not_circuit (p : Circuit signature n 1) :
    ∃ out : Circuit signature n 1,
      (∀ x, out.eval interpretation x 0 = !p.eval interpretation x 0) ∧ out.size ≤ p.size + 1 := by
  have hp : Synthesis interpretation (inputs n) {fun x => p.eval interpretation x 0} p.size :=
    (Synthesis.circuit (I := interpretation) (s := inputs n) p (fun i x => x i)
      fun i => ⟨i, rfl⟩).mono Set.Subset.rfl (by rintro _ rfl; exact ⟨0, rfl⟩) le_rfl
  obtain ⟨out, ho, hs⟩ := hp.not.exists_circuit
  exact ⟨out, fun x => congrFun (ho x) 0, hs⟩

/-- **Eventually permanent targets.** For every `0 < L ≤ 2 ^ n`, some circuit of size at most
`80000 * powerBudget n (c.size + (p.size + 1) + 4 * n) (2 ^ n) L + p.size + 2` decides whether
the orbit of its input is accepted by `p` from some time on. -/
theorem eventually_always_target_circuit (c : Circuit signature n n)
    (p : Circuit signature n 1) (L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature n 1,
      (∀ x, out.eval interpretation x 0 = true ↔
        ∃ a, ∀ t, a ≤ t → p.eval interpretation ((c.eval interpretation)^[t] x) 0 = true) ∧
      out.size ≤ 80000 * powerBudget n (c.size + (p.size + 1) + 4 * n) (2 ^ n) L +
        p.size + 2 := by
  obtain ⟨reject, hr, hrs⟩ := exists_not_circuit p
  obtain ⟨recurs, hc, hcs⟩ := recurring_target_circuit c reject L hL hLN
  obtain ⟨out, ho, hos⟩ := exists_not_circuit recurs
  refine ⟨out, fun x => ?_, ?_⟩
  · rw [ho, Bool.not_eq_true', Bool.eq_false_iff, Ne, hc]
    simp only [hr, Bool.not_eq_true', Bool.eq_false_iff, not_forall, not_exists, not_and,
      not_not]
  · have hb : powerBudget n (c.size + reject.size + 4 * n) (2 ^ n) L ≤
        powerBudget n (c.size + (p.size + 1) + 4 * n) (2 ^ n) L := by
      unfold powerBudget
      gcongr
    omega

/-- **Square-root recurring targets.** -/
theorem recurring_target_optimized (c : Circuit signature n n) (p : Circuit signature n 1) :
    ∃ out : Circuit signature n 1,
      (∀ x, out.eval interpretation x 0 = true ↔
        ∀ a, ∃ t, a ≤ t ∧ p.eval interpretation ((c.eval interpretation)^[t] x) 0 = true) ∧
      (out.size : ℝ) ≤
        240000 * optimizedBudget n (c.size + p.size + 4 * n) (2 ^ n) + p.size := by
  obtain ⟨L, hL, hLN, hopt⟩ :=
    exists_powerBudget_le_optimizedBudget n (c.size + p.size + 4 * n) (2 ^ n) le_rfl
  obtain ⟨out, ho, hs⟩ := recurring_target_circuit c p L hL hLN
  refine ⟨out, ho, ?_⟩
  have hs' : (out.size : ℝ) ≤
      80000 * (powerBudget n (c.size + p.size + 4 * n) (2 ^ n) L : ℝ) + p.size := by
    exact_mod_cast hs
  linarith

/-- **Square-root eventually permanent targets.** -/
theorem eventually_always_target_optimized (c : Circuit signature n n)
    (p : Circuit signature n 1) :
    ∃ out : Circuit signature n 1,
      (∀ x, out.eval interpretation x 0 = true ↔
        ∃ a, ∀ t, a ≤ t → p.eval interpretation ((c.eval interpretation)^[t] x) 0 = true) ∧
      (out.size : ℝ) ≤
        240000 * optimizedBudget n (c.size + (p.size + 1) + 4 * n) (2 ^ n) + p.size + 2 := by
  obtain ⟨L, hL, hLN, hopt⟩ :=
    exists_powerBudget_le_optimizedBudget n (c.size + (p.size + 1) + 4 * n) (2 ^ n) le_rfl
  obtain ⟨out, ho, hs⟩ := eventually_always_target_circuit c p L hL hLN
  refine ⟨out, ho, ?_⟩
  have hs' : (out.size : ℝ) ≤
      80000 * (powerBudget n (c.size + (p.size + 1) + 4 * n) (2 ^ n) L : ℝ) + p.size + 2 := by
    exact_mod_cast hs
  linarith

end Cslib.Circuits.Boolean.Iteration
