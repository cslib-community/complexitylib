/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.BitGame
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.BitString

/-!
# Loops that stop on a test, and games of single-bit moves, within space

Client checks for `Turing.MultiTapeTM.ComputableInSpace.iterateUntil`, whose number of rounds may
be exponential in the input, and for `Turing.MultiTapeTM.ComputableInSpace.bitGame_value`, on the
game in which the players alternately choose `n` bits and the last bit decides.
-/

namespace CslibFrontierTests.BitGame

open Cslib Cslib.Complexity Turing.MultiTapeTM BigOLe

/-- Counting down from `n` takes `n` steps, exponentially many in the binary input. -/
theorem countdown_inSpace :
    ComputableInSpace (fun n : ℕ => (· - 1)^[n] n) encNat encNat
      fun n => (encNat n).length := by
  have hit (n j : ℕ) : (· - 1)^[j] n = n - j := by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih]; omega
  refine (ComputableInSpace.iterateUntil (n := fun n => n) (ComputableInSpace.budget_id (.refl _))
    ComputableInSpace.natPred ComputableInSpace.natIsZero
    (Q := fun n => 2 * (encNat n).length + 1) (B := fun n => (encNat n).length)
    (fun n => by simp [hit]) (fun n j hj => by simp [hit]; omega)
    (fun n j _ => ?_) (fun n j _ => ?_)).weaken ⟨4, fun n => by dsimp only; omega⟩
  · have := length_encNat_mono (show n - j ≤ n by omega)
    simp only [hit]
    omega
  · simpa only [hit] using length_encNat_mono (show n - j ≤ n by omega)

example : (fun n : ℕ => (· - 1)^[n] n) 5 = 0 := rfl

/-- The game of `n` single-bit moves: the existential player moves first, and the last bit is
the value. -/
def leaf (p : ℕ × List Bool) : Bool := decide (p.2.length = p.1)

/-- The last move decides the game. -/
def last (p : ℕ × List Bool) : Bool := p.2.headD false

/-- The existential player moves after an even number of moves. -/
def even (p : ℕ × List Bool) : Bool := decide (p.2.length % 2 = 0)

/-- The value of the game of `n` moves. -/
def lastBit (n : ℕ) : Bool :=
  BitGame.value (fun u => leaf (n, u)) (fun u => last (n, u)) (fun u => even (n, u)) n []

/-- The existential player wins exactly when the number of moves is odd, as then it moves last. -/
example : lastBit 0 = false := by decide
example : lastBit 1 = true := by decide
example : lastBit 2 = false := by decide
example : lastBit 3 = true := by decide

/-- The game is evaluated within space linear in `n`, although its tree has `2 ^ n` leaves. -/
theorem lastBit_inSpace :
    ComputableInSpace lastBit encNat encBool fun n => n + (encNat n).length := by
  set S : ℕ × List Bool → ℕ := fun p => (encPair encNat encBits p).length
  have hid := ComputableInSpace.budget_id (enc := encPair encNat encBits) (S := S) (.refl _)
  have hbits : ComputableInSpace (fun l : List Bool => l) encBits (encList encBool)
      fun l => (encBits l).length :=
    ComputableInSpace.of_inO ComputableInDegree.bitsToList.inO_one
  have hu := ComputableInSpace.budget_comp_linear hbits hid.snd'
  have hlen := ComputableInSpace.budget_length hu
  have hL : ComputableInSpace leaf (encPair encNat encBits) encBool S :=
    ComputableInSpace.budget_natEq hlen hid.fst'
  have hV : ComputableInSpace last (encPair encNat encBits) encBool S :=
    ComputableInSpace.budget_headD false hu
  have hP : ComputableInSpace even (encPair encNat encBits) encBool S :=
    ComputableInSpace.budget_natEq
      (ComputableInSpace.budget_natMod hlen (ComputableInSpace.budget_const 2 (.refl _)))
      (ComputableInSpace.budget_const 0 (.refl _))
  refine (ComputableInSpace.bitGame_value hL hV hP (m := fun n => n)
    (Q := fun n => 3 * (2 * (encNat n).length + 1 + n))
    (fun n u hu => by simp [leaf, hu]) fun n u hu => ?_).weaken
      ⟨8, fun n => by dsimp only; omega⟩
  simp only [S, length_encPair, encBits, Function.Embedding.refl_apply] at hu ⊢
  omega

end CslibFrontierTests.BitGame
