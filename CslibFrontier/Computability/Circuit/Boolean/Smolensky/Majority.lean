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

/-!
# Majority is not in AC⁰[p], and AC⁰[p] is strictly contained in TC⁰

The AC⁰[p] basis contains the unbounded fan-in basis, so parity reduces to majority there in
constant depth (`ConstDepth.parity_mem_of_majority_mem`). As parity is not in AC⁰[p] for an odd
prime `p` (`parity_notMem_AC0Mod`), neither is majority, and since majority is in TC⁰,
`TC⁰` is not contained in `AC⁰[p]` (`TC0_not_subset_AC0Mod`). Together with `AC⁰[p] ⊆ TC⁰`
(`AC0Mod_subset_TC0`), **AC⁰[p] is strictly contained in TC⁰** (`AC0Mod_ssubset_TC0`)
[Razborov1987], [Smolensky1987].

## Main results

* `Cslib.Circuits.Boolean.Smolensky.majority_notMem_AC0Mod`: majority is not in AC⁰[p].
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

variable {p : ℕ} [Fact p.Prime]

/-- **Majority is not in AC⁰[p]** for an odd prime `p`. -/
theorem majority_notMem_AC0Mod (hp2 : p ≠ 2) : Language.ofSlices majority ∉ AC0Mod p :=
  fun h => parity_notMem_AC0Mod hp2 (ConstDepth.parity_mem_of_majority_mem Unbounded.toExt h)

/-- **TC⁰ is not contained in AC⁰[p]** for an odd prime `p`. -/
theorem TC0_not_subset_AC0Mod (hp2 : p ≠ 2) : ¬ TC0 ⊆ AC0Mod p :=
  fun h => majority_notMem_AC0Mod hp2 (h majority_mem_TC0)

/-- **AC⁰[p] is strictly contained in TC⁰** for an odd prime `p`. -/
theorem AC0Mod_ssubset_TC0 (hp2 : p ≠ 2) : AC0Mod p ⊂ TC0 :=
  ⟨AC0Mod_subset_TC0 p, TC0_not_subset_AC0Mod hp2⟩

end Cslib.Circuits.Boolean.Smolensky
