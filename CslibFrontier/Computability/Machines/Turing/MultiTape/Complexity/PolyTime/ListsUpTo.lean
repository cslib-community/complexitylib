/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Foundations.Data.List.ListsUpTo

/-!
# Listing short lists in polynomial time

For a fixed length bound `r`, listing the lists of length at most `r` over a list computed in
polynomial time is polynomial-time
(`Turing.MultiTapeTM.ComputableInPolyTime.listsUpTo`): the listing is `r` nested
`List.flatMap`s.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.listsUpTo`: `List.listsUpTo (l a) r` is
  polynomial-time in `a` for a fixed `r`.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {γ α : Type} {encIn : γ ↪ List Bool} {encA : α ↪ List Bool}

/-- **Listing short lists is polynomial-time** for a fixed length bound `r`, over a list computed
in polynomial time. -/
theorem listsUpTo {l : γ → List α} (hl : ComputableInPolyTime l encIn (encList encA)) (r : ℕ) :
    ComputableInPolyTime (fun a => (l a).listsUpTo r) encIn (encList (encList encA)) := by
  induction r with
  | zero => exact ComputableInPolyTime.const _
  | succ r ih =>
    simp only [List.listsUpTo]
    refine ComputableInPolyTime.cons' (ComputableInPolyTime.const []) ?_
    refine ComputableInPolyTime.flatMapWithInput hl ?_
    have hp := ComputableInPolyTime.id' (encIn := encPair encIn encA)
    refine ComputableInPolyTime.mapWithInput (ih.comp hp.fst') ?_
    have hq := ComputableInPolyTime.id' (encIn := encPair (encPair encIn encA) (encList encA))
    exact ComputableInPolyTime.cons' hq.fst'.snd' hq.snd'

end Turing.MultiTapeTM.ComputableInPolyTime
