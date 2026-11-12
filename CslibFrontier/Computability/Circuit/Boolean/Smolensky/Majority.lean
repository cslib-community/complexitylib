/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.TC0
public import CslibFrontier.Computability.Circuit.Boolean.Smolensky
import CslibFrontier.Computability.Circuit.Boolean.ModMajority
import CslibFrontier.Computability.Circuit.Boolean.Razborov.MiddleSlice

/-!
# Majority is not in AC⁰[p], and AC⁰[p] is strictly contained in TC⁰

The AC⁰[p] basis contains the unbounded fan-in basis, so a circuit for majority yields circuits for
every threshold, every "exactly `k`" function and parity, in constant extra depth
(`exactlyCircuitOfMajority`, `ConstDepth.parity_mem_of_majority_mem`). For an odd prime `p` this
contradicts `parity_notMem_AC0Mod` [Smolensky1987]. For `p = 2` it contradicts the lower bound for
the middle slice `Razborov.middleSlice`, an "exactly `k`" function
(`Razborov.middleSlice_notMem_AC0Mod_two`) [Razborov1987]. So majority is not in AC⁰[p] for any
prime `p`, and since majority is in TC⁰, `TC⁰` is not contained in `AC⁰[p]`
(`TC0_not_subset_AC0Mod`). Together with `AC⁰[p] ⊆ TC⁰` (`AC0Mod_subset_TC0`), **AC⁰[p] is
strictly contained in TC⁰** (`AC0Mod_ssubset_TC0`).

## Main results

* `Cslib.Circuits.Boolean.Smolensky.majority_notMem_AC0Mod`: majority is not in AC⁰[p] for every
  prime `p`; odd `p` through parity [Smolensky1987], `p = 2` through `exactlyCircuitOfMajority` and
  Razborov's middle slice [Razborov1987].
* `Cslib.Circuits.Boolean.Smolensky.TC0_not_subset_AC0Mod`: `TC⁰ ⊄ AC⁰[p]`.
* `Cslib.Circuits.Boolean.Smolensky.AC0Mod_ssubset_TC0`: `AC⁰[p] ⊊ TC⁰`.

## References

* [A. A. Razborov, *Lower bounds on the size of bounded depth circuits over a complete basis with
  logical addition*][Razborov1987]
* [R. Smolensky, *Algebraic methods in the theory of lower bounds for Boolean circuit
  complexity*][Smolensky1987]
-/

public section

namespace Cslib.Circuits.Boolean.Smolensky

open Razborov

variable {p : ℕ} [Fact p.Prime]

/-- Majority is not in AC⁰[2]: from a circuit for majority, `exactlyCircuitOfMajority` decides the
middle slice in three more levels. -/
private theorem majority_notMem_AC0Mod_two : Language.ofSlices majority ∉ AC0Mod 2 := by
  intro h
  obtain ⟨d, size, hsize, hC⟩ := ConstDepth.mem_iff.1 h
  refine middleSlice_notMem_AC0Mod_two (ConstDepth.mem_iff.2 ⟨d + 3,
    fun n => 2 * (2 + size (n + (n + 2))) + 2, by fun_prop, fun n => ?_⟩)
  obtain ⟨M, hM, hMd, hMs⟩ := hC (n + (n + 2))
  rw [Language.slice_ofSlices] at hM
  refine ⟨exactlyCircuitOfMajority Unbounded.toExt M (n - sliceLevel n), fun x => ?_,
    (depth_exactlyCircuitOfMajority_le _).trans (by omega), ?_⟩
  · funext j
    rw [Language.slice_ofSlices, Subsingleton.elim j 0,
      eval_exactlyCircuitOfMajority hM (Nat.sub_le _ _)]
    rw [single, Bool.eq_iff_iff, decide_eq_true_iff, middleSlice_eq_true_iff]
  · rw [size_exactlyCircuitOfMajority]
    beta_reduce
    omega

/-- **Majority is not in AC⁰[p]** for every prime `p`. -/
theorem majority_notMem_AC0Mod : Language.ofSlices majority ∉ AC0Mod p := by
  rcases eq_or_ne p 2 with rfl | hp2
  · exact majority_notMem_AC0Mod_two
  · exact fun h =>
      parity_notMem_AC0Mod hp2 (ConstDepth.parity_mem_of_majority_mem Unbounded.toExt h)

/-- **TC⁰ is not contained in AC⁰[p]** for every prime `p`. -/
theorem TC0_not_subset_AC0Mod : ¬ TC0 ⊆ AC0Mod p :=
  fun h => majority_notMem_AC0Mod (h majority_mem_TC0)

/-- **AC⁰[p] is strictly contained in TC⁰** for every prime `p`. -/
theorem AC0Mod_ssubset_TC0 : AC0Mod p ⊂ TC0 :=
  ⟨AC0Mod_subset_TC0 p, TC0_not_subset_AC0Mod⟩

end Cslib.Circuits.Boolean.Smolensky
