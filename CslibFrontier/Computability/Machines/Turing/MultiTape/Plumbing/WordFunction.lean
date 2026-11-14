/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.RunsBetween
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelOnWords
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Native functions between selected work-tape words

A plain polynomial-time certificate gives one finite machine that preserves a serialized source
word and writes its result on a separate blank tape. The caller selects the private tape footprint
by an embedding; every other tape and its head remain unchanged. The clock includes normalization,
output writing, and head restoration. The host input head starts and ends at position one.

The workspace bound counts visited cells and follows from the clock. Initializing the selected
storage and positioning the host input from its left blank are separate charged operations.
-/

public section

namespace Turing.MultiTapeTM.WordFunction

/-- Compute a native function on selected tapes, preserving its source and all ambient storage.
The selected tapes other than the source start blank; the selected output alone changes. -/
theorem exists_of_polyTime {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {f : α → β} (hf : ComputableInPolyTime f encIn encOut) :
    ∃ (k : ℕ) (S : Type) (_ : Finite S) (tm : MultiTapeTM (k + 1 + 2) Bool S) (c d : ℕ),
      ∀ (K : ℕ) (e : Fin (k + 1 + 2) ↪ Fin K) (input : List Bool) (a : α)
        (words : Fin K → List Bool) (out : List Bool),
        words (e (Fin.natAdd (k + 1) 0)) = encIn a →
        (∀ j ≠ Fin.natAdd (k + 1) 0, words (e j) = []) →
        RunsBetween (tm.extendTapes e) (tapesCfg input words 0 0 out)
          (tapesCfg input (Function.update words (e ((Fin.last k).castAdd 2)) (encOut (f a)))
            0 0 out)
          (c * ((encIn a).length + 1) ^ d) (K * (c * ((encIn a).length + 1) ^ d + 1)) := by
  have htidy := hf.tidy
  have hlength := htidy.polyBounded_length
  obtain ⟨t, s, ht, _, k, S, hS, tm, htm⟩ := htidy
  let := hS
  obtain ⟨c, d, hclock⟩ := ((ht.add hlength).add (PolyBounded.const 6)).exists_le
  refine ⟨k, _, inferInstance, tm.onWords true, c, d, ?_⟩
  intro K e input a words out hsource hblank
  have hspec := transformsTapes_onWords_embed (htm a) true e
  obtain ⟨words', emitted, ⟨hwords, hemitted⟩, hr⟩ :=
    RunsBetween.of_transformsTapes (input := input) hspec (ws := words)
      ⟨hsource, hblank⟩ 0 out
  rw [hwords, hemitted, List.append_nil] at hr
  apply RunsBetween.of_runFrom
  rw [runFrom_eq_of_halt _ _ (hclock a) (by rw [hr.1]; rfl), hr.1]

end Turing.MultiTapeTM.WordFunction
