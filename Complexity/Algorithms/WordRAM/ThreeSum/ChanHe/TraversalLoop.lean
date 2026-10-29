/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalLive
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalSkip
public import Complexity.Computability.WordRAM.GhostLoop

/-!
# Complete bounded native Chan–He worklist loop

Each body execution is discharged by the actual pop, modulus, histogram, packing and push
programs. The explicit proof-state loop rule then counts every pending entry, including skipped
calls. Termination returns the exact finite preorder, whose native pointer table and packed
arrays have full readback. The arena bounds cover all live memory throughout the loop.

## Main results

* `transition`: actual native body execution and invariant preservation for every pending entry.
* `loop_exec`: the complete actual native loop terminates with exact finite node output.

These native composition and resource proofs are original. Initialized-input preprocessing
composition is a separate obligation.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum.ChanHe (Node)

/-- Every actual live loop header admits a native body execution with the same finite program. -/
theorem transition {a : Arena} {w : ℕ} {target : List Node}
    (ha : a.Separated) (hw : a.Ready w) (h2 : Fits (w + 2) 2)
    (hcap : Fits (w + 2) (a.stack + a.capacity)) (s : Cursor) (x : Data 128)
    (h : s.Invariant a w target x) (hc : (Cond.lt zero (registers Stack.len)).Holds x) :
    ∃ (s' : Cursor) (y : Data 128),
      ExecWithin (w + 2) body x y (visitTime a.n a.m a.N + 314) ∧
      s'.Invariant a w target y ∧ s'.work < s.work := by
  rcases s with ⟨pending, ns⟩
  cases pending with
  | nil => exact (h.nonempty hc rfl).elim
  | cons e es =>
    by_cases hs : e.fuel = 0 ∨ (e.data 0).length = 0 ∨
        (e.data 1).length = 0 ∨ (e.data 2).length = 0
    · obtain ⟨y, hy, hi, hd⟩ := skip_transition e es ns x ha h2 hcap h hs
      exact ⟨⟨es, ns⟩, y, hy.mono (by omega), hi, hd⟩
    · apply live_transition e es ns x ha hw h2 hcap h
      · intro he
        exact hs (Or.inl he)
      · intro j
        fin_cases j
        · exact fun he => hs (Or.inr (Or.inl he))
        · exact fun he => hs (Or.inr (Or.inr (Or.inl he)))
        · exact fun he => hs (Or.inr (Or.inr (Or.inr he)))

/-- Execute the complete actual native loop. Every call and fit is discharged by `transition`;
the final emitted list equals the entire target, with exact pointer and packed-array readback. -/
theorem loop_exec {a : Arena} {w : ℕ} {target : List Node}
    (ha : a.Separated) (hw : a.Ready w) (h2 : Fits (w + 2) 2)
    (hcap : Fits (w + 2) (a.stack + a.capacity)) (s : Cursor) (x : Data 128)
    (h : s.Invariant a w target x) :
    ∃ (ns : List (ℕ × Node)) (y : Data 128),
      ExecWithin (w + 2) loop x y (s.work * (visitTime a.n a.m a.N + 316) + 2) ∧
      (Cursor.mk [] ns).Invariant a w target y ∧ ns.map Prod.snd = target := by
  obtain ⟨s', y, he, hi, hexit⟩ := ExecWithin.loop_invariant_state
    (fun s x => s.Invariant a w target x) Cursor.work
    (transition ha hw h2 hcap) h
  obtain ⟨hp, hout⟩ := hi.finished hexit
  refine ⟨s'.emitted, y, ?_, ?_, hout⟩
  · simpa only [loop, Nat.add_assoc, Nat.reduceAdd] using he
  · cases s' with
    | mk pending ns =>
      change pending = [] at hp
      subst pending
      exact hi

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal
