/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Inclusions
public import CslibFrontier.Computability.Complexity.Classes.IP.PSPACE
public import CslibFrontier.Computability.Complexity.Classes.IP.Reduction
public import CslibFrontier.Computability.Complexity.Classes.IP.TQBF
public import CslibFrontier.Computability.Complexity.Classes.PH
public import CslibFrontier.Computability.Complexity.Classes.Space.TQBF

/-!
# `IP = PSPACE`

Every problem in `PSPACE` reduces to `TQBF` in polynomial time
(`Cslib.Complexity.TQBF_pspaceHard`), `TQBF` has an interactive proof
(`Cslib.Complexity.TQBF_mem_IP`), and `IP` is closed under polynomial-time reductions
(`Cslib.Complexity.PolyTimeReducible.mem_IP`), so `PSPACE ⊆ IP`. With `IP ⊆ PSPACE`
(`Cslib.Complexity.IP_subset_PSPACE`) this is the theorem of Shamir [Shamir][Shamir1992], with the
simplification of Shen [Shen][Shen1992], following Lund, Fortnow, Karloff and Nisan
[LundFortnowKarloffNisan1992]; see [Arora and Barak, Section 8.3][AroraBarak09]. Every class of
the polynomial hierarchy, in particular `coNP`, has interactive proofs.

The classes are those of the library: `IP` with private fair coins, a strict polynomial clock for
one oracle machine against every stateful prover, completeness `2 / 3` and soundness `1 / 3`, and
`PSPACE` decided by one deterministic machine in polynomial space, with respect to any encoding of
the instances.

## Main results

* `Cslib.Complexity.PSPACE_subset_IP`, `Cslib.Complexity.IP_eq_PSPACE`.
* `Cslib.Complexity.PH_subset_IP`, `Cslib.Complexity.coNP_subset_IP`.

## References

* [C. Lund, L. Fortnow, H. Karloff, N. Nisan, *Algebraic methods for interactive proof
  systems*][LundFortnowKarloffNisan1992]
* [A. Shamir, *IP = PSPACE*][Shamir1992]
* [A. Shen, *IP = SPACE: simplified proof*][Shen1992]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

variable {α : Type} (enc : α ↪ List Bool)

/-- **`PSPACE ⊆ IP`** [Shamir][Shamir1992]: every problem in `PSPACE` reduces to `TQBF`, which has
an interactive proof. -/
theorem PSPACE_subset_IP : PSPACE enc ⊆ IP enc :=
  fun A hA => (TQBF_pspaceHard enc A hA).mem_IP TQBF_mem_IP

/-- **`IP = PSPACE`** [Lund, Fortnow, Karloff and Nisan][LundFortnowKarloffNisan1992],
[Shamir][Shamir1992], [Shen][Shen1992]. -/
theorem IP_eq_PSPACE : IP enc = PSPACE enc :=
  (IP_subset_PSPACE enc).antisymm (PSPACE_subset_IP enc)

/-- **Every class of the polynomial hierarchy has interactive proofs.** -/
theorem PH_subset_IP : PH enc ⊆ IP enc :=
  PH_subset_PSPACE.trans (PSPACE_subset_IP enc)

/-- **`coNP ⊆ IP`** [Lund, Fortnow, Karloff and Nisan][LundFortnowKarloffNisan1992]. -/
theorem coNP_subset_IP : coNP enc ⊆ IP enc :=
  coNP_subset_PH.trans (PH_subset_IP enc)

end Cslib.Complexity
