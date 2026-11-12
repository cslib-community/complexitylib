/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Complement
public import CslibFrontier.Computability.Complexity.Problems.STCON
import CslibFrontier.Computability.Complexity.Problems.STCON.Reduction
import CslibFrontier.Computability.Complexity.Problems.STCON.Search

/-!
# Directed s–t connectivity is NL-complete

Directed `s`–`t` connectivity on adjacency matrices (`Cslib.Complexity.STCON`, encoded by
`Cslib.Complexity.encSTCON`) is complete for nondeterministic logarithmic space under logspace
many-one reductions [Sipser, Theorem 8.25][Sipser2013] (`Cslib.Complexity.STCON.logSpaceComplete`).
The classes are the library's native ones: `NL` is decided by one finite-state nondeterministic
machine within work space `c * (Nat.log2 n + 1)`, every branch halting, and the reductions are
computed by deterministic machines within such space (`Cslib.Complexity.LogSpaceReducible`).

* **Membership** (`Cslib.Complexity.STCON.mem_NL`) [Sipser, Example 8.19][Sipser2013]: a
  nondeterministic counter program walks from `s`, guessing one vertex at a time and giving up
  after `n` steps (`Cslib.Complexity.STCON.searchProgram`).
* **Hardness** (`Cslib.Complexity.STCON.logSpaceHard`): a problem decided by a machine within
  space `c * (Nat.log2 n + 1)` reduces to `STCON` by mapping an instance to the configuration graph
  of the machine on its encoding, with a sink after the accepting vertices
  (`Cslib.Complexity.STCON.configurationInstance`), computed in logarithmic space by a counter
  program (`Cslib.Complexity.STCON.computableInLogSpace_configurationInstance`).

The complement of `STCON` is in `NL` too (`Cslib.Complexity.STCON.compl_mem_NL`) by the
Immerman–Szelepcsényi theorem `Cslib.Complexity.NL_eq_coNL` [Sipser, Section 8.6][Sipser2013],
proved for these native classes by Erik Demaine's inductive-counting construction. Consequently
the complement is `NL`-complete as well (`Cslib.Complexity.STCON.compl_logSpaceComplete`), the
form in which the hardness of 2SAT is usually derived. Finally `STCON` is in `L` exactly when
`NL = L` (`Cslib.Complexity.STCON.mem_L_iff_forall_NL_eq_L`)
[Sipser, Corollary 8.24][Sipser2013].

## Main results

* `Cslib.Complexity.STCON.mem_NL`: `STCON ∈ NL`.
* `Cslib.Complexity.STCON.logSpaceReducible_of_mem_NL`, `Cslib.Complexity.STCON.logSpaceHard`:
  every problem in `NL` reduces to `STCON` in logarithmic space.
* `Cslib.Complexity.STCON.logSpaceComplete`: `STCON` is `NL`-complete.
* `Cslib.Complexity.STCON.compl_mem_NL`: the complement of `STCON` is in `NL`.
* `Cslib.Complexity.STCON.compl_logSpaceComplete`: the complement of `STCON` is `NL`-complete.
* `Cslib.Complexity.STCON.mem_L_iff_forall_NL_eq_L`: `STCON ∈ L` exactly when `NL = L`.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Example 8.19, Corollary 8.24,
  Theorem 8.25 and Section 8.6][Sipser2013]
* [N. Immerman, *Nondeterministic Space Is Closed under Complementation*][Immerman1988]
* [R. Szelepcsényi, *The Method of Forcing for Nondeterministic Automata*][Szelepcsenyi1987]
-/

public section

namespace Cslib.Complexity

namespace STCON

open _root_.Turing _root_.Turing.MultiTapeTM

/-- **Directed `s`–`t` connectivity is in `NL`** [Sipser, Example 8.19][Sipser2013]. -/
theorem mem_NL : STCON ∈ NL encSTCON :=
  exists_decidesInLogSpace

/-- **Every problem in `NL` reduces to directed `s`–`t` connectivity in logarithmic space**: an
instance is mapped to the configuration graph of a logarithmic-space decider on its encoding,
with a sink after the accepting vertices [Sipser, Theorem 8.25][Sipser2013]. -/
theorem logSpaceReducible_of_mem_NL {α : Type} {enc : α ↪ List Bool} {A : Set α}
    (hA : A ∈ NL enc) : LogSpaceReducible enc encSTCON A STCON := by
  obtain ⟨k, State, _, ntm, c, h⟩ := hA
  let := Fintype.ofFinite State
  refine ⟨fun a => configurationInstance ntm c (enc a),
    (computableInLogSpace_configurationInstance ntm c).comp (computableInLogSpace_frame enc),
    fun a => ?_⟩
  exact ((h.1 a).2).trans (configurationInstance_mem_iff ntm c (h.1 a).1).symm

/-- **Directed `s`–`t` connectivity is `NL`-hard** under logspace many-one reductions. -/
theorem logSpaceHard : LogSpaceHard NL encSTCON STCON :=
  fun _ _ _ hA => logSpaceReducible_of_mem_NL hA

/-- **Directed `s`–`t` connectivity is `NL`-complete** under logspace many-one reductions
[Sipser, Theorem 8.25][Sipser2013]. -/
theorem logSpaceComplete : LogSpaceComplete NL encSTCON STCON :=
  ⟨mem_NL, logSpaceHard⟩

/-- **The complement of directed `s`–`t` connectivity is in `NL`**, by the Immerman–Szelepcsényi
theorem `NL = coNL` [Sipser, Section 8.6][Sipser2013]. -/
theorem compl_mem_NL : STCONᶜ ∈ NL encSTCON :=
  Cslib.Complexity.compl_mem_NL mem_NL

/-- **The complement of directed `s`–`t` connectivity is `NL`-complete**: a problem in `NL` has
its complement in `NL`, which reduces to `STCON`. This combines Theorem 8.25 of Sipser with
`NL = coNL` [Sipser, Section 8.6][Sipser2013]. -/
theorem compl_logSpaceComplete : LogSpaceComplete NL encSTCON STCONᶜ := by
  refine ⟨compl_mem_NL, fun _ _ A hA => ?_⟩
  have h := (logSpaceReducible_of_mem_NL (Cslib.Complexity.compl_mem_NL hA)).compl
  rwa [compl_compl] at h

/-- **Directed `s`–`t` connectivity is in `L` exactly when `NL = L`**, for every encoding of
instances [Sipser, Corollary 8.24][Sipser2013]. -/
theorem mem_L_iff_forall_NL_eq_L :
    STCON ∈ L encSTCON ↔ ∀ {α : Type} (enc : α ↪ List Bool), NL enc = L enc :=
  logSpaceComplete.mem_L_iff fun _ => L_subset_NL

end STCON

end Cslib.Complexity
