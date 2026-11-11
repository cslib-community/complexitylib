/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.ArthurMerlin.Amplification
import Complexity.Computability.Complexity.Classes.ArthurMerlin.RoundCollapse
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! Concrete clients for public-coin games with a fixed pattern of moves: evaluated counts, a game
verifier that holds in one order of the moves and fails in the other, satisfiable error-exponent
conditions and the round collapse. -/

namespace ComplexityTests.ArthurMerlinGames

open Cslib Cslib.Complexity Turing.MultiTapeTM

example : alternatingMoves .arthur 3 = [.arthur, .merlin, .arthur] := rfl

example : alternatingMoves .merlin 4 = [.merlin, .arthur, .merlin, .arthur] := rfl

/-- Merlin wins when his bit echoes Arthur's coin. -/
private def echo (t : List Bool) : Bool := t.getD 0 false == t.getD 1 false

/-- When Arthur moves first, Merlin echoes both coins. -/
example : AMGame.count [(.arthur, 1), (.merlin, 1)] echo = 2 := by decide

/-- When Merlin moves first, his bit matches one coin of two. -/
example : AMGame.count [(.merlin, 1), (.arthur, 1)] echo = 1 := by decide

example : AMGame.arthurBits [(.merlin, 2), (.arthur, 3), (.merlin, 1), (.arthur, 4)] = 7 := rfl

private theorem evalShape_one (x y : AMMove) (n : ℕ) :
    AMGame.evalShape [(x, (1 : Polynomial ℕ)), (y, 1)] n = [(x, 1), (y, 1)] := by
  simp [AMGame.evalShape]

/-- The echo verifier accepts every instance as an `A M` game. -/
example : IsAMGameVerifier encBits [(.arthur, 1), (.merlin, 1)] (fun x => echo x.2) Set.univ := by
  intro a
  refine ⟨fun _ => ?_, fun h => absurd (Set.mem_univ a) h⟩
  rw [evalShape_one]
  exact (by decide : 2 * 2 ^ AMGame.arthurBits [(.arthur, 1), (.merlin, 1)] ≤
    3 * AMGame.count [(.arthur, 1), (.merlin, 1)] echo)

/-- With the moves swapped, the same verifier accepts only half of the coins. -/
example : ¬ IsAMGameVerifier encBits [(.merlin, 1), (.arthur, 1)] (fun x => echo x.2) Set.univ := by
  intro h
  have := (h []).1 (Set.mem_univ _)
  rw [evalShape_one] at this
  exact absurd this (by decide)

private theorem head_mem_AM : {w : List Bool | w.headD false = true} ∈ AM encBits :=
  BPP_subset_AM (P_subset_BPP ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩)

/-- A four-move game `M A M A` for a problem in `AM`, by the round collapse. -/
private theorem head_mem_MAMA : {w : List Bool | w.headD false = true} ∈
    AMGameClass encBits [.merlin, .arthur, .merlin, .arthur] := by
  rw [AMGameClass_eq_AM (by decide)]
  exact head_mem_AM

/-- Every error exponent is achieved by a game verifier with the pattern `M A M A`. -/
example (e : Polynomial ℕ) : ∃ (G : List (AMMove × Polynomial ℕ))
    (V : List Bool × List Bool → Bool), G.map Prod.fst = [.merlin, .arthur, .merlin, .arthur] ∧
      ComputableInPolyTime V (encPair encBits encBits) encBool ∧
        IsAMGameVerifierWithErrorExponent encBits e G V {w : List Bool | w.headD false = true} :=
  mem_AMGameClass_iff_forall_errorExponent.1 head_mem_MAMA e

/-- `MA ⊆ AM`, recovered from the round collapse. -/
example {α : Type} (enc : α ↪ List Bool) : MA enc ⊆ AM enc :=
  AMGameClass_merlin_arthur ▸ AMGameClass_subset_AM _

/-- The collapse for alternating patterns, and the patterns with two moves. -/
example {α : Type} (enc : α ↪ List Bool) :
    AMk enc 2 = AM enc ∧ AMk enc 7 = AM enc ∧ MAk enc 2 = MA enc ∧ MAk enc 5 = AM enc ∧
      AMGameClass enc [.merlin, .arthur, .merlin] = AM enc ∧ AMGameClass enc [] ⊆ AM enc :=
  ⟨AMk_two, AMk_eq_AM (by norm_num), MAk_two, MAk_eq_AM (by norm_num),
    AMGameClass_merlin_arthur_merlin, AMGameClass_subset_AM _⟩

end ComplexityTests.ArthurMerlinGames
