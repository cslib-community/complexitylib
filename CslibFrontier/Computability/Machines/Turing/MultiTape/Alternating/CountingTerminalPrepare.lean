/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CarryLookahead.Query.Terminal
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WordFunction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.FromLeftBlank

/-!
# Native preparation of a finishing-adder terminal request

A finite machine reads only the short routing metadata and writes the three dispatch flags and
binary component index. It preserves the metadata, clears private scratch, restores all heads,
and starts and ends at the host input's left blank. Constructing the metadata is a separate phase.
-/

public section

namespace Turing.MultiTapeATM.CountingTerminalPrepare

open MultiTapeTM Cslib.Circuits.Boolean.CarryLookahead.Query

/-- The source tape contains the complete short routing position. -/
abbrev metadata (k : ℕ) : Fin (k + 1 + 2) := Fin.natAdd (k + 1) 0

/-- The separate output tape contains the dispatch flags followed by the raw binary index. -/
abbrev flags (k : ℕ) : Fin (k + 1 + 2) := (Fin.last k).castAdd 2

/-- Metadata and request words beside blank private work tapes and marker. -/
@[expose] def words (k : ℕ) (p : Routing.Position) (request : List Bool) :
    Fin (k + 1 + 2) → List Bool :=
  Function.update (Function.update (fun _ => []) (metadata k) (Routing.encPosition p))
    (flags k) request

/-- The preparation layout has all heads at zero and no emitted output. -/
@[expose] def config (k : ℕ) (input : List Bool) (p : Routing.Position) (request : List Bool) :
    Cfg (k + 1 + 2) Bool Unit input :=
  { tapesCfg input (words k p request) 0 0 [] with inputPos := 0 }

/-- One finite native machine constructs every terminal request with a polynomial clock in the
short metadata length, including both host-head movements. It never reads an operand word. -/
theorem exists_machine :
    ∃ (k : ℕ) (S : Type) (_ : Finite S) (tm : MultiTapeTM (k + 1 + 2) Bool S) (c d : ℕ),
      ∀ (input : List Bool) (p : Routing.Position),
        tm.runFrom ((config k input p []).withState (some tm.q₀))
          (c * ((Routing.encPosition p).length + 1) ^ d + 2) =
          (config k input p (Terminal.word p)).withState none := by
  obtain ⟨k, S, hS, tm, c, d, htm⟩ := WordFunction.exists_of_polyTime Terminal.word_polyTime
  let := hS
  refine ⟨k, _, inferInstance,
    (tm.extendTapes (Function.Embedding.refl _)).fromLeftBlank, c, d, ?_⟩
  intro input p
  have hne : metadata k ≠ flags k := (Fin.castAdd_ne_natAdd _ _).symm
  have hr := htm (k + 1 + 2) (Function.Embedding.refl _) input p (words k p []) []
    (by simp [words, hne]) (by
      intro j hj
      by_cases hf : j = flags k <;> simp [words, hf, hj])
  have hwords : Function.update (words k p []) (flags k) (Terminal.word p) =
      words k p (Terminal.word p) := by
    simp [words]
  simp only [Function.Embedding.refl_apply, encBits_apply] at hr
  rw [hwords] at hr
  exact (hr.fromLeftBlank rfl rfl).1

end Turing.MultiTapeATM.CountingTerminalPrepare
