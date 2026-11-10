/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of local-only files)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Nondeterministic

/-!
# Descriptions of nondeterministic machines

A machine without work tapes that emits either bit and halts. Its description lists both
transitions, so from the initial configuration it can step to either output; a halted
configuration takes no step; and the machine accepts every input, read off its description.
-/

@[expose] public section

namespace CslibFrontierTests.UniversalNondeterministic

open Turing Turing.MultiTapeTM.Universal

/-- Emit either bit and halt. -/
def coin : MultiTapeNTM 0 Bool Unit where
  q₀ := ()
  Tr _ _ _ a := ∃ b, a = ⟨0, Fin.elim0, some b, none⟩

/-- The single state, as a number. -/
def eUnit : Unit ↪ ℕ := ⟨fun _ => 0, fun _ _ _ => rfl⟩

/-- From the initial configuration, the description of `coin` can emit either bit and halt. -/
theorem nStep_init (input : List Bool) (b : Bool) :
    NStep (descN eUnit eBit coin) (input.map eBit) (init (descN eUnit eBit coin), [])
      (⟨none, 1, []⟩, [eBit b]) := by
  refine ⟨eUnit (), by simp [init], _, (mem_descN eUnit eBit coin).mpr
    ⟨(), input.head?, Fin.elim0, ⟨0, Fin.elim0, some b, none⟩, ⟨b, rfl⟩, rfl⟩, ?_, ?_⟩
  · simp [init, key, SCfg.key, inputSymbol, List.head?_map]
  · simp only [init, descN_tapes, descN_q₀, List.replicate_zero]
    rfl

/-- A halted configuration takes no step. -/
example (x : List ℕ) (o : List ℕ) (p : SCfg × List ℕ) :
    ¬NStep (descN eUnit eBit coin) x (⟨none, 1, []⟩, o) p := by
  rintro ⟨q, hq, -⟩
  cases hq

/-- Both outputs are reachable. -/
example (input : List Bool) (b : Bool) :
    Relation.ReflTransGen (NStep (descN eUnit eBit coin) (input.map eBit))
      (init (descN eUnit eBit coin), []) (⟨none, 1, []⟩, [eBit b]) :=
  .single (nStep_init input b)

/-- `coin` accepts every input, read off its description. -/
example (input : List Bool) : coin.Accepts input :=
  (accepts_iff_reflTransGen_nStep eUnit coin input).mpr ⟨_, rfl, .single (nStep_init input true)⟩

end CslibFrontierTests.UniversalNondeterministic
