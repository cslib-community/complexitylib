/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Circuit.Boolean.LocalValueGame.Machine
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
A three-address decoder has an AND root with true and false leaves. The tests instantiate the
native endpoint with actual finite-domain preparation/update machines, construct a paying
potential, and obtain one finite multitape alternating machine with a uniform finite clock.
No machine-implementation or cost premise is left as an assumption of the example.
-/

namespace CslibFrontierTests.LocalValueGame

open Cslib.Circuits.Boolean Cslib.Circuits.Boolean.LocalValueGame
open Turing Turing.MultiTapeTM Turing.MultiTapeATM WordGame

private def decoder : Decoder (Fin 3) where
  op a := if a = 0 then .and else .const (a == 1)
  child _ b := if b then 2 else 1

private def rank (a : Fin 3) : ℕ := if a = 0 then 1 else 0

private def value (a : Fin 3) : Bool := a == 1

private theorem descends : decoder.Descends rank := by
  intro a b
  fin_cases a <;> cases b <;> simp [decoder, rank]

private theorem values : ∀ a, value a = decoder.eval value a := by decide

private noncomputable def enc : Claim (Fin 3) ↪ List Bool := encFinite _

/-- The false claim at the AND root wins: the existential player selects the false leaf. -/
example : Wins (update decoder enc) (position decoder enc ⟨0, false⟩) :=
  (wins_position_iff descends value values _).mpr rfl

/-- The true claim at the AND root loses: the universal player can select the false leaf. -/
example : ¬ Wins (update decoder enc) (position decoder enc ⟨0, true⟩) := by
  rw [wins_position_iff descends value values]
  decide

/-- Every branch of either root claim terminates within one move. -/
example (b : Bool) : Ends (update decoder enc) 1 (position decoder enc ⟨0, b⟩) :=
  by simpa [rank] using ends_position (encC := enc) descends (⟨0, b⟩ : Claim (Fin 3))

/-- The concrete nonterminal decoder has one actual native machine, including both correct and
incorrect claims, with jointly inhabited preparation, round, and time certificates. -/
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (atm : MultiTapeATM k Bool State)
    (clock : ℕ), ∀ c : Claim (Fin 3),
      (atm.Accepts (enc c) ↔ value c.wire = c.value) ∧
        atm.toPTM.toNTM.RunsInTime (enc c) clock := by
  classical
  obtain ⟨tI, sI, _, _, hI⟩ :=
    (ComputableTidilyInPolyTime.of_finite (encA := enc) (encB := encBits)
      (position decoder enc))
  obtain ⟨tF, sF, _, _, hF⟩ :=
    (ComputableTidilyInPolyTime.of_finite (encA := encMove enc) (encB := encBits)
      (step decoder enc))
  let charge (m : Move (Fin 3)) := tF m + 3 * (encMove enc m).length +
    7 * (step decoder enc m).length + 26
  let bound := Finset.univ.sup charge
  let budget (a : Fin 3) := if a = 0 then bound else 0
  have hcost (c : Claim (Fin 3)) (u b : Bool)
      (hc : ∀ v, decoder.op c.wire ≠ .const v) :
      tF ⟨u, b, c⟩ + 3 * (encMove enc ⟨u, b, c⟩).length +
        7 * (step decoder enc ⟨u, b, c⟩).length + 26 +
          budget (next decoder c b).wire ≤ budget c.wire := by
    have hc0 : c.wire = 0 := by
      by_contra hn
      exact hc (c.wire == 1) (by simp [decoder, hn])
    have hn : (next decoder c b).wire ≠ 0 := by
      cases b <;> simp [LocalValueGame.next, decoder, hc0]
    have hbound := Finset.le_sup (f := charge) (Finset.mem_univ ⟨u, b, c⟩)
    simpa only [budget, hn, hc0, ↓reduceIte, add_zero] using hbound
  obtain ⟨k, State, hfin, atm, h⟩ :=
    exists_machine decoder enc descends value values hI hF budget hcost
  let clock (c : Claim (Fin 3)) := tI c + (position decoder enc c).length + budget c.wire + 4
  refine ⟨k, State, hfin, atm, Finset.univ.sup clock, fun c => ⟨(h c).1, ?_⟩⟩
  exact (h c).2.mono (Finset.le_sup (f := clock) (Finset.mem_univ c))

end CslibFrontierTests.LocalValueGame
