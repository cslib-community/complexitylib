/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.LogSpace
public import Complexity.Computability.USTCON.Space

/-!
# Undirected connectivity, symmetric logarithmic space, and `SL = L`

**Reingold's theorem** [Reingold, Theorem 4.1][Reingold2008]
[Arora and Barak, Section 21.4][AroraBarak09]: undirected `s`–`t` connectivity, on simple graphs
given by their adjacency matrices (`Cslib.Complexity.encUSTCON`), is in `L`
(`Cslib.Complexity.USTCON_mem_L`).

The decider is the read machine `Cslib.USTCON.Reader.machine`, which walks in Reingold's graph of
the input along all label sequences of length `O(log n)` and evaluates its rotation map in place
with a constant number of labels per level; its simulation on multi-tape machines runs in space
`O(log m)` on encodings of length `m` (`Cslib.USTCON.computableInLogSpace_decide`). As for every
problem in `L enc`, the decider is only required to be correct on the encodings of instances;
recognising which bit strings are encodings is not part of the statement.

Symmetric logarithmic space (`Cslib.Complexity.SL`) is defined here by its logspace many-one
reduction characterization as the class of problems logspace many-one reducible to `USTCON`
[Lewis and Papadimitriou][LewisPapadimitriou1982]
[Reingold, Section 1 and Theorem 4.2][Reingold2008] (the symmetric Turing machine model and its
equivalence with logspace reducibility to `USTCON` are not separately formalized). Combining
`USTCON_mem_L` with the logspace reduction of any problem in `L` to `USTCON` via the canonical
two-vertex witness `Cslib.Complexity.USTCONInstance.ofBool` yields completeness of `USTCON` for `L`
(`Cslib.Complexity.USTCON_logSpaceComplete_L`) and Reingold's corollary `SL = L`
(`Cslib.Complexity.SL_eq_L`) [Reingold, Theorem 4.2][Reingold2008]. This completeness says
nothing beyond `USTCON_mem_L`. Under logspace many-one reductions, every problem in `L` with a
member and a non-member is complete for `L`, because the reduction can decide its input. A
meaningful notion of completeness for `L` needs weaker reductions, such as first-order reductions;
this file does not state one.

## Main definitions

* `Cslib.Complexity.SL`: symmetric logarithmic space, characterized as the problems logspace
  many-one reducible to `USTCON`.

## Main results

* `Cslib.Complexity.USTCON_mem_L`: undirected connectivity is in `L`.
* `Cslib.Complexity.USTCON_mem_SL`, `Cslib.Complexity.LogSpaceReducible.mem_SL`: `USTCON ∈ SL` and
  closure of `SL` under logspace many-one reductions.
* `Cslib.Complexity.USTCON_logSpaceHard_SL`, `Cslib.Complexity.USTCON_logSpaceComplete_SL`:
  `USTCON` is logspace-complete for `SL`, immediately from the definition of `SL`.
* `Cslib.Complexity.USTCON_logSpaceHard_L`, `Cslib.Complexity.USTCON_logSpaceComplete_L`:
  `USTCON` is logspace-complete for `L`, immediately from `USTCON_mem_L`, as is every problem in
  `L` with a member and a non-member.
* `Cslib.Complexity.SL_subset_L`, `Cslib.Complexity.L_subset_SL`, `Cslib.Complexity.SL_eq_L`:
  symmetric logarithmic space coincides with deterministic logarithmic space (`SL = L`).
* `Cslib.Complexity.compl_mem_SL`: `SL` is closed under complement.

## References

* [O. Reingold, *Undirected connectivity in log-space*][Reingold2008]
* [H. R. Lewis, C. H. Papadimitriou, *Symmetric space-bounded computation*][LewisPapadimitriou1982]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing.MultiTapeTM

variable {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}

/-- **Reingold's theorem**: undirected `s`–`t` connectivity is in deterministic logarithmic
space. -/
theorem USTCON_mem_L : USTCON ∈ L encUSTCON :=
  ⟨_, USTCON.computableInLogSpace_decide, fun _ ↦ by simp⟩

/-- **Symmetric logarithmic space** `SL`, defined by its logspace many-one reduction
characterization as the class of problems logspace many-one reducible to undirected `s`–`t`
connectivity `USTCON` [Lewis and Papadimitriou][LewisPapadimitriou1982]
[Reingold, Section 1 and Theorem 4.2][Reingold2008]. The symmetric Turing machine model and its
equivalence with logspace reducibility to `USTCON` are not separately formalized. -/
def SL (enc : α ↪ List Bool) : Set (Set α) :=
  {A | LogSpaceReducible enc encUSTCON A USTCON}

/-- Membership in `SL` is logspace many-one reducibility to `USTCON`. -/
@[simp]
theorem mem_SL_iff : A ∈ SL enc ↔ LogSpaceReducible enc encUSTCON A USTCON :=
  Iff.rfl

/-- Undirected `s`–`t` connectivity belongs to `SL`. -/
theorem USTCON_mem_SL : USTCON ∈ SL encUSTCON :=
  LogSpaceReducible.refl encUSTCON USTCON

/-- **`SL` is closed under logspace many-one reductions.** -/
theorem LogSpaceReducible.mem_SL (hAB : LogSpaceReducible enc encB A B) (hB : B ∈ SL encB) :
    A ∈ SL enc :=
  hAB.trans hB

/-- `USTCON` is logspace-hard for `SL`. This holds by the definition of `SL`; the theorem of Lewis
and Papadimitriou about symmetric machines is not formalized. -/
theorem USTCON_logSpaceHard_SL : LogSpaceHard SL encUSTCON USTCON :=
  fun _ _ _ hA ↦ hA

/-- `USTCON` is logspace-complete for `SL`, by the definition of `SL`. For symmetric machines this
is the theorem of Lewis and Papadimitriou [LewisPapadimitriou1982], which is not formalized. -/
theorem USTCON_logSpaceComplete_SL : LogSpaceComplete SL encUSTCON USTCON :=
  ⟨USTCON_mem_SL, USTCON_logSpaceHard_SL⟩

/-- `USTCON` is logspace-hard for `L`: compose a logspace decider with the finite map
`USTCONInstance.ofBool`. The same argument makes every problem with a member and a non-member
logspace-hard for `L`. -/
theorem USTCON_logSpaceHard_L : LogSpaceHard L encUSTCON USTCON := by
  rintro α enc A ⟨f, hf, hA⟩
  refine ⟨USTCONInstance.ofBool ∘ f,
    (ComputableInLogSpace.of_finite (encIn := encBool) USTCONInstance.ofBool).comp hf,
    fun a ↦ (hA a).trans USTCONInstance.ofBool_mem_USTCON.symm⟩

/-- `USTCON` is logspace-complete for `L`. The content is membership (`USTCON_mem_L`)
[Reingold, Theorem 4.1][Reingold2008]. Hardness under logspace many-one reductions holds for every
problem in `L` with a member and a non-member (`USTCON_logSpaceHard_L`). -/
theorem USTCON_logSpaceComplete_L : LogSpaceComplete L encUSTCON USTCON :=
  ⟨USTCON_mem_L, USTCON_logSpaceHard_L⟩

/-- **Symmetric logarithmic space is contained in deterministic logarithmic space**: every
problem logspace-reducible to `USTCON` is in `L` by `USTCON_mem_L`
[Reingold, Theorem 4.2][Reingold2008]. -/
theorem SL_subset_L : SL enc ⊆ L enc :=
  USTCON_logSpaceHard_SL.subset_L USTCON_mem_L enc

/-- **Deterministic logarithmic space is contained in symmetric logarithmic space**: every
problem in `L` reduces in logarithmic space to `USTCON` via a two-vertex witness. -/
theorem L_subset_SL : L enc ⊆ SL enc :=
  fun _ hA ↦ USTCON_logSpaceHard_L enc _ hA

/-- **Reingold's corollary (`SL = L`)** [Reingold, Theorem 4.2][Reingold2008]: symmetric
logarithmic space, characterized by logspace many-one reducibility to `USTCON`, coincides with
deterministic logarithmic space. -/
theorem SL_eq_L : SL enc = L enc :=
  Set.Subset.antisymm SL_subset_L L_subset_SL

/-- **`SL` is closed under complement**, as a consequence of `SL = L` and `compl_mem_L`. -/
theorem compl_mem_SL (h : A ∈ SL enc) : Aᶜ ∈ SL enc := by
  rw [SL_eq_L] at h ⊢
  exact compl_mem_L h

end Cslib.Complexity
