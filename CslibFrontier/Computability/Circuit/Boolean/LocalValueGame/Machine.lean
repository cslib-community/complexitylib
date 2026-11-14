/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.LocalValueGame
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.WordGameTime

/-!
# Native multitape machines for local Boolean value queries

This connects local Boolean semantics to the existing finite multitape alternating machine.
Preparation and each local update have native tidy machine certificates. The bound charges the
update clock, encoding lengths, and the tape copying and clearing required between rounds.
Neither the decoder nor random access is provided for free. A potential is used only in the proof.

The result is conditional on these implementation certificates and their branch charges. It does
not supply a succinct arithmetic decoder or a tensor-contraction construction.
-/

public section

namespace Cslib.Circuits.Boolean.LocalValueGame

open Turing Turing.MultiTapeTM Turing.MultiTapeATM WordGame

/-- A typed local move: the word-game player and selected bit followed by its claim. -/
structure Move (α : Type) where
  /-- The current player bit. -/
  player : Bool
  /-- The selected child bit. -/
  bit : Bool
  /-- The claim being advanced. -/
  claim : Claim α
  deriving DecidableEq, Fintype

variable {α : Type} (D : Decoder α) (encC : Claim α ↪ List Bool)

/-- Two unframed bits (player, move) precede the supplied claim encoding. This custom prefix
layout is required by `wordGame`; the fields are not encoded as a framed tuple. -/
@[expose] def encMove : Move α ↪ List Bool where
  toFun m := m.player :: m.bit :: encC m.claim
  inj' := by
    intro x y h
    obtain ⟨hx, ht⟩ := List.cons.inj h
    obtain ⟨hb, hc⟩ := List.cons.inj ht
    have hc' := encC.injective hc
    cases x
    cases y
    simp_all

/-- The two control bits are followed by the claim with no additional framing. -/
@[simp] theorem encMove_apply (m : Move α) :
    encMove encC m = m.player :: m.bit :: encC m.claim := rfl

/-- A typed move adds exactly two bits to its claim. -/
@[simp] theorem length_encMove (m : Move α) :
    (encMove encC m).length = (encC m.claim).length + 2 := by
  simp only [encMove_apply, List.length_cons]

/-- One decoded update follows the selected child and prepares its next query. -/
@[expose] def step (m : Move α) : List Bool := position D encC (next D m.claim m.bit)

/-- Native implementation of local value queries. Every nonterminal move pays its own machine
clock, tape plumbing and successor potential. Constants are handled by the charged preparation
or preceding update. The same finite machine handles all encoded claims. -/
theorem exists_machine {rank : α → ℕ} (hd : D.Descends rank) (value : α → Bool)
    (hv : ∀ a, value a = D.eval value a)
    {tI sI : Claim α → ℕ} {tF sF : Move α → ℕ}
    (hI : ComputableTidilyInTimeAndSpace (position D encC) encC encBits tI sI)
    (hF : ComputableTidilyInTimeAndSpace (step D encC) (encMove encC) encBits tF sF)
    (budget : α → ℕ)
    (hcost : ∀ (c : Claim α) (u b : Bool), (∀ v, D.op c.wire ≠ .const v) →
      tF ⟨u, b, c⟩ + 3 * (encMove encC ⟨u, b, c⟩).length +
        7 * (step D encC ⟨u, b, c⟩).length + 26 + budget (next D c b).wire ≤ budget c.wire) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (atm : MultiTapeATM k Bool State),
      ∀ c, (atm.Accepts (encC c) ↔ value c.wire = c.value) ∧
        atm.toPTM.toNTM.RunsInTime (encC c)
          (tI c + (position D encC c).length + budget c.wire + 4) := by
  obtain ⟨k, State, hfin, atm, h⟩ := exists_wordGame_of_tidy hI hF
    (fun _ => potential encC budget) (by
      intro c₀ u x r b hr
      obtain ⟨c, he, _⟩ := reach_position hd hr
      obtain ⟨hc, henc⟩ := position_eq_cons he.symm
      subst r
      refine ⟨⟨u, b, c⟩, rfl, ?_, ?_⟩
      · exact (update_cons c u b).symm
      · rw [potential_cons]
        have hp := potential_position_le (D := D) (encC := encC) budget (next D c b)
        have ht := hcost c u b hc
        change _ + potential encC budget (position D encC (next D c b)) ≤ _
        omega)
  refine ⟨k, State, hfin, atm, fun c => ⟨?_, ?_⟩⟩
  · exact (h c).1.trans (wins_position_iff hd value hv c)
  · exact (h c).2.mono (by have := potential_position_le (D := D) (encC := encC) budget c; omega)

end Cslib.Circuits.Boolean.LocalValueGame
