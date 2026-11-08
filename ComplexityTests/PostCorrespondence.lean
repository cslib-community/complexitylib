/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PostCorrespondence.Undecidable

/-! # Post's correspondence problem: checked instances

Sipser's solvable example with an explicit match, an instance without a match for a length reason,
the counterexample to Sipser's MPCP-to-PCP construction without a start marker, and the MPCP
instances of a machine that halts at once and of a machine that never halts. -/

@[expose] public section

namespace Cslib.Tests.PostCorrespondence

open Cslib.PostCorrespondence Cslib.PostCorrespondence.Marked Turing

/-! ### A solvable instance -/

/-- The letters `a`, `b`, `c`. -/
abbrev a : Fin 3 := 0
/-- The letter `b`. -/
abbrev b : Fin 3 := 1
/-- The letter `c`. -/
abbrev c : Fin 3 := 2

/-- Sipser's example [Sipser2013, §5.2]: `b / ca`, `a / ab`, `ca / a`, `abc / c`. -/
def sipser : List (Domino (Fin 3)) :=
  [⟨[b], [c, a]⟩, ⟨[a], [a, b]⟩, ⟨[c, a], [a]⟩, ⟨[a, b, c], [c]⟩]

/-- The match `a / ab`, `b / ca`, `ca / a`, `a / ab`, `abc / c`, reading `abcaaabc` on both
sides. -/
theorem solvable_sipser : Solvable sipser :=
  ⟨[⟨[a], [a, b]⟩, ⟨[b], [c, a]⟩, ⟨[c, a], [a]⟩, ⟨[a], [a, b]⟩, ⟨[a, b, c], [c]⟩],
    by decide, by decide, by decide⟩

/-- The same match in index form. -/
example : ∃ is : List (Fin sipser.length), is ≠ [] ∧
    tops (is.map sipser.get) = bottoms (is.map sipser.get) :=
  (solvable_iff_exists_indices sipser).mp solvable_sipser

/-! ### An instance without a match -/

/-- Every top is longer than its bottom: `aa / a`, `b / ε`. -/
def longTops : List (Domino (Fin 3)) := [⟨[a, a], [a]⟩, ⟨[b], []⟩]

theorem not_solvable_longTops : ¬Solvable longTops :=
  not_solvable_of_length_lt (by decide)

/-! ### Why the start marker is needed -/

/-- The MPCP instance with start domino `a / ba` and the single domino `b / ε`, over `Bool` with
`a = true` and `b = false`. -/
def badM : MInstance Bool := ⟨⟨[true], [false, true]⟩, [⟨[false], []⟩]⟩

/-- `badM` has no match: its top begins with `a` and its bottom with `b`. -/
theorem not_solvable_badM : ¬badM.Solvable := by
  rintro ⟨ds, -, h⟩
  exact absurd (List.cons.inj h).1 (by decide)

/-- Sipser's construction applied to `badM`, without the start marker: `⋆a / ⋆b⋆a⋆`, `⋆b / ε` and
the end domino `⋆◇ / ◇`. -/
def badPCP : List (Domino (Marked Bool)) :=
  [⟨[sep, letter true], [sep, letter false, sep, letter true, sep]⟩, ⟨[sep, letter false], []⟩,
    ⟨[sep, stop], [stop]⟩]

/-- `badPCP` is solvable, by `⋆b / ε`, `⋆a / ⋆b⋆a⋆`, `⋆◇ / ◇`, although `badM` is not. -/
theorem solvable_badPCP : Solvable badPCP :=
  ⟨[⟨[sep, letter false], []⟩, ⟨[sep, letter true], [sep, letter false, sep, letter true, sep]⟩,
    ⟨[sep, stop], [stop]⟩], by decide, by decide, by decide⟩

/-- With the start marker, the reduction is correct on `badM`. -/
theorem not_solvable_toPCP_badM : ¬Solvable (toPCP badM) :=
  fun h => not_solvable_badM ((solvable_toPCP_iff badM).mp h)

/-! ### Machines -/

/-- A machine that halts at once. -/
def haltM : TM0.Machine Bool Unit := fun _ _ => none

/-- A machine that rewrites the scanned symbol forever. -/
def loopM : TM0.Machine Bool Unit := fun _ x => some ((), .write x)

theorem solvable_mInstance_haltM (l : List Bool) : (OfTM0.mInstance haltM l).Solvable := by
  refine (OfTM0.eval_dom_iff_solvable haltM l).mp ((OfTM0.eval_dom_iff haltM l).mpr ?_)
  exact ⟨_, Relation.ReflTransGen.refl, rfl⟩

theorem not_solvable_mInstance_loopM (l : List Bool) : ¬(OfTM0.mInstance loopM l).Solvable := by
  intro h
  obtain ⟨cfg, -, hc⟩ :=
    (OfTM0.eval_dom_iff loopM l).mp ((OfTM0.eval_dom_iff_solvable loopM l).mpr h)
  obtain ⟨q, x, L, R, rfl⟩ := OfTM0.exists_cfgOf cfg
  rw [OfTM0.step_of_eq_write (q' := ()) (b := x) rfl L R] at hc
  cases hc

end Cslib.Tests.PostCorrespondence
