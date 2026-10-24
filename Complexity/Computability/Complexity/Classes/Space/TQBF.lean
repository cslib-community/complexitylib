/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Space.TQBF.Membership
import Complexity.Computability.Complexity.Classes.Space.TQBF.PolyTime

/-!
# `TQBF` is `PSPACE`-complete

A problem is `PSPACE`-hard when every problem in `PSPACE`, with any encoding of its instances,
reduces to it in polynomial time (`Cslib.Complexity.PSPACEHard`), and `PSPACE`-complete when it is
moreover in `PSPACE` (`Cslib.Complexity.PSPACEComplete`) [Arora and Barak, Section
4.2][AroraBarak09] [Sipser, Section 8.3][Sipser2013].

The true closed quantified Boolean formulas (`Cslib.Complexity.TQBF`) form a `PSPACE`-complete
problem [Sipser, Theorem 8.9][Sipser2013] [Arora and Barak, Theorem 4.13][AroraBarak09]:

* `TQBF ∈ PSPACE` (`Cslib.Complexity.TQBF_mem_PSPACE`): an explicit-stack evaluator decides it
  within polynomial space.
* `TQBF` is `PSPACE`-hard (`Cslib.Complexity.TQBF_pspaceHard`): a problem in `PSPACE` is decided
  by a deterministic machine, which is a nondeterministic machine with one computation path whose
  computation paths visit polynomially many work cells (`Cslib.Complexity.PSPACE_subset_NPSPACE`).
  Acceptance is reachability between the codes of its finite views
  (`Turing.MultiTapeNTM.savitchDecide_eq_true_iff`), which Savitch's formula expresses with a
  polynomial number of tokens (`Cslib.Complexity.TQBF.reduce_mem_TQBF_iff`), constructed in
  polynomial time (`Cslib.Complexity.TQBF.computableInPolyTime_reduce`). Its formula of level
  `0` is the Cook–Levin tableau of a polynomial-time machine testing one step or none between codes
  (`Cslib.Complexity.TQBF.computableInPolyTime_edgeTest`).

The reduction maps every instance to a closed formula: the quantified variables of the formula of
level `0` are odd, those of the blocks of the midpoint recursion even, and the source and target
blocks of the top level are fixed to the codes of the initial view and of acceptance. The
alternating characterization `AP = PSPACE` is not proved here.

Boundary cases: there is no empty formula, since every formula has a token
(`Cslib.Logic.PL.QBF.tokens_ne_nil`), so no instance of `TQBF` has an empty encoding. The formulas
without variables are built from `top` and `bot` and are decided by their value; formulas with a
free variable are not in `TQBF`, even when they are valid. The empty conjunction is `top` and the
empty clause `bot` (`Cslib.Logic.PL.QBF.conj`, `Cslib.Logic.PL.QBF.ofClause`). The formulas
produced by the reduction always quantify over some variables: their codes have width at least `2`,
even on the empty input.

## Main results

* `Cslib.Complexity.TQBF_pspaceHard`: `TQBF` is `PSPACE`-hard.
* `Cslib.Complexity.TQBF_pspaceComplete`: `TQBF` is `PSPACE`-complete.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.9][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Theorem 4.13][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

/-- **`TQBF` is `PSPACE`-hard** [Sipser, Theorem 8.9][Sipser2013]
[Arora and Barak, Theorem 4.13][AroraBarak09]: every problem decided by a deterministic machine
within polynomial space reduces to `TQBF` in polynomial time, by Savitch's formula on the codes of
the finite views of the machine. -/
theorem TQBF_pspaceHard : PSPACEHard encQBF TQBF := by
  intro α enc A hA
  obtain ⟨k, State, hfinite, ntm, s, hs, hA⟩ := PSPACE_subset_NPSPACE hA
  obtain ⟨c, d, hcd⟩ := hs.exists_le
  obtain ⟨tV, sV, htV, -, kV, StateV, hfiniteV, tmV, htmV⟩ :=
    (TQBF.computableInPolyTime_edgeTest (enc := enc) (ntm := ntm) (c := c) (d := d)).tidy
  obtain ⟨cV, dV, htV⟩ := htV.exists_le
  have := Fintype.ofFinite StateV
  classical
  refine ⟨TQBF.reduce enc ntm c d tmV cV dV,
    (TQBF.computableInPolyTime_reduce tmV cV dV), fun a => ?_⟩
  rw [TQBF.reduce_mem_TQBF_iff (htmV.mono htV fun _ => le_rfl) (hA.recognizesInSpace a).1
    (hcd a)]
  exact (hA.recognizesInSpace a).2

/-- **`TQBF` is `PSPACE`-complete** [Sipser, Theorem 8.9][Sipser2013]
[Arora and Barak, Theorem 4.13][AroraBarak09]. -/
theorem TQBF_pspaceComplete : PSPACEComplete encQBF TQBF :=
  ⟨TQBF_mem_PSPACE, TQBF_pspaceHard⟩

end Cslib.Complexity
