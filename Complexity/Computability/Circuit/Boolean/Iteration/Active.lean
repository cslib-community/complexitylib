/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration
public import Complexity.Foundations.Combinatorics.FunctionalGraph.Active
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Fixed powers charged to long trajectories

The storage term of the fixed-power bound counts all `2 ^ n` states. It suffices to count the
*active* states: those of transient depth at least `L` and those on cycles of length at least
`L` (`FunctionalGraph.activeVertices`). Checkpoints packed inside the active set cover every
orbit within `4 L` steps (`FunctionalGraph.exists_active_checkpoints`), so the fixed-power
construction with an orbit prefix of `4 L` states gives a circuit of size at most
`120000 * powerBudget n s Q L`, where `Q` is the number of active states for this `L`
(`active_mass_fixed_power`). The count `Q` depends on `L`.

The circuits are native De Morgan circuits: every NOT, AND and OR gate and every constant is
charged, while wiring and fanout are free. The checkpoints are chosen nonconstructively, so the
circuits exist for each `T` and `L`; nothing here bounds the time to construct them.

## Main results

* `Cslib.Circuits.Boolean.Iteration.active_mass_fixed_power`: fixed powers charged to the
  active states.

## References

* Adapted from lean/Proofs/ActivePowers.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open FunctionalGraph

private theorem active_construction_cost (n s M L d : ℕ) (hL : 0 < L) (hd : d ≤ n + 3)
    (hR : 2 ^ d ≤ 2 * (M + 4 * L + 1)) :
    2 + 5 * (4 * L) * s + (18 * d ^ 2 + 30) * 2 ^ d * (Record.width n (n + 3) + 1) +
      1000 * (4 * L + 1) * (n + (n + 3) + 1) ^ 2 ≤
      120000 * (L * s + (n + 1) ^ 3 * (L + M + 1)) := by
  have h1 : 18 * d ^ 2 + 30 ≤ 192 * (n + 1) ^ 2 := by
    have hs : d ^ 2 ≤ (n + 3) ^ 2 := by gcongr
    nlinarith
  have h2 : Record.width n (n + 3) + 1 ≤ 6 * (n + 1) := by unfold Record.width; omega
  have hs : (18 * d ^ 2 + 30) * 2 ^ d * (Record.width n (n + 3) + 1) ≤
      (192 * (n + 1) ^ 2) * (2 * (M + 4 * L + 1)) * (6 * (n + 1)) := by gcongr
  have h3 : (n + (n + 3) + 1) ^ 2 ≤ 16 * (n + 1) ^ 2 := by nlinarith
  have hh : 1000 * (4 * L + 1) * (n + (n + 3) + 1) ^ 2 ≤
      1000 * (5 * L) * (16 * (n + 1) ^ 2) := by gcongr; omega
  nlinarith [Nat.zero_le (L * n ^ 3), Nat.zero_le (M * n ^ 3),
    Nat.zero_le (M * n ^ 2), Nat.zero_le (L * n ^ 2), Nat.zero_le (L * s)]

/-- **Fixed powers charged to long trajectories.** For every exponent `T` and every
`0 < L ≤ 2 ^ n`, some circuit of size at most `120000 * powerBudget n c.size Q L` computes `T`
applications of `c`, where `Q` is the number of states of transient depth at least `L` or on
cycles of length at least `L`. -/
theorem active_mass_fixed_power (n : ℕ) (c : Circuit signature n n) (T L : ℕ) (hL : 0 < L)
    (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature n n,
      out.Computes interpretation (c.eval interpretation)^[T] ∧
      out.size ≤
        120000 * powerBudget n c.size (activeVertices (c.eval interpretation) L).card L := by
  classical
  let f := c.eval interpretation
  by_cases hT : T < 4 * L
  · refine ⟨c.iterate T, fun x => by rw [Circuit.eval_iterate], ?_⟩
    rw [Circuit.size_iterate]
    have ht : T * c.size ≤ 4 * L * c.size := Nat.mul_le_mul_right _ hT.le
    unfold powerBudget
    nlinarith [Nat.zero_le ((n + 1) ^ 3 * (L + (activeVertices f L).card / L + 1))]
  obtain ⟨H, -, hcard, hcover⟩ := exists_active_checkpoints f L hL
  let cp : Fin H.card → BitString n := fun j => (H.equivFin.symm j).val
  let d := Nat.clog 2 (H.card + 4 * L + 1)
  have hcapacity : H.card + (4 * L + 1) ≤ BitonicSort.arity d := by
    simpa only [BitonicSort.arity_eq_two_pow, d, Nat.add_assoc] using
      Nat.le_pow_clog (by decide : 1 < 2) (H.card + 4 * L + 1)
  have hN : H.card ≤ 2 ^ n := by
    simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] using
      Finset.card_le_univ H
  have hd : d ≤ n + 3 := by
    apply Nat.clog_le_of_le_pow
    simp only [Nat.pow_succ]
    have := Nat.one_le_two_pow (n := n)
    omega
  have hR : 2 ^ d ≤ 2 * (H.card + 4 * L + 1) := by
    have hpos : 0 < d := Nat.clog_pos (by decide) (by omega)
    have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2)
      (show 1 < H.card + 4 * L + 1 by omega)
    have hpow : 2 ^ d = 2 ^ (d - 1) * 2 := by rw [← Nat.pow_succ, show (d - 1).succ = d by omega]
    rw [hpow]
    change 2 ^ (d - 1) < _ at hp
    omega
  have hfit : 4 * L < 2 ^ (n + 3) := by
    simp only [Nat.pow_succ]
    omega
  obtain ⟨out, hout, hsize⟩ := exists_fixedOutput (w := n + 3) c T (4 * L) d cp
  refine ⟨out, fun x => ?_, ?_⟩
  · rw [hout x]
    apply reconstruct_spec f T (4 * L) cp x _ _ hfit (by omega)
    apply Record.detect_sorted_witness f T (4 * L) d cp x hcapacity hfit
    rcases hcover x with ⟨i, j, hij, hj, heq⟩ | ⟨t, ht, hmem⟩
    · exact Or.inr ⟨i, j, hij, by omega, heq⟩
    · exact Or.inl ⟨t, ht.le, H.equivFin ⟨f^[t] x, hmem⟩, by simp [cp]⟩
  · have hc : H.card ≤ (activeVertices f L).card / L := (Nat.le_div_iff_mul_le hL).mpr hcard
    apply hsize.trans ((active_construction_cost n c.size H.card L d hL hd hR).trans ?_)
    unfold powerBudget
    gcongr

end Cslib.Circuits.Boolean.Iteration
