/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Amplification
import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.RoundCollapse
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! Concrete clients for public-coin games with a fixed pattern of moves: evaluated counts, a game
verifier that holds in one order of the moves and fails in the other, satisfiable error-exponent
conditions and the round collapse. -/

namespace CslibFrontierTests.ArthurMerlinGames

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

/-- Zero-move and single-move game verifiers match deterministic, bounded-error and `NP`
verifiers. -/
example : IsAMGameVerifier encBits [] (fun x => x.1.headD false)
    {w : List Bool | w.headD false = true} :=
  isAMGameVerifier_nil_iff.2 fun _ => Iff.rfl

example : IsAMGameVerifier encBits [(.arthur, 2)]
    (fun x => if x.1.headD false then !(x.2.getD 0 false && x.2.getD 1 false)
      else (x.2.getD 0 false && x.2.getD 1 false))
    {w : List Bool | w.headD false = true} := by
  rw [isAMGameVerifier_arthur_iff]
  intro w
  have hev : (2 : Polynomial ℕ).eval (encBits w).length = 2 := by simp
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · have hw' : w.headD false = true := hw
    rw [boundedErrorAt_true_iff, hev, acceptCount_congr (W := fun x =>
      !(x.2.getD 0 false && x.2.getD 1 false)) fun u => ite_eq_left hw']
    exact (by decide : 2 * 2 ^ 2 ≤
      3 * acceptCount (fun x : Unit × List Bool => !(x.2.getD 0 false && x.2.getD 1 false)) () 2)
  · rw [boundedErrorAt_false_iff, hev, acceptCount_congr (W := fun x =>
      x.2.getD 0 false && x.2.getD 1 false) fun u => ite_eq_right hw]
    exact (by decide : 3 * acceptCount
      (fun x : Unit × List Bool => x.2.getD 0 false && x.2.getD 1 false) () 2 ≤ 2 ^ 2)

example : IsAMGameVerifier encBits [(.merlin, 1)]
    (fun x => x.1.headD false == x.2.headD false) Set.univ :=
  isAMGameVerifier_merlin_iff.2 fun w =>
    ⟨fun _ => ⟨[w.headD false], by simp, by simp⟩, fun _ => Set.mem_univ w⟩

/-- Prepending an existential quantifier over one-bit words turns a zero-move game into an `NP`
game (`[.merlin]`). -/
example : {w : List Bool | ∃ u : List Bool, u.length = (1 : Polynomial ℕ).eval (encBits w).length ∧
    (w, u) ∈ {p : List Bool × List Bool | p.1.headD false = p.2.headD false}} ∈ NP encBits := by
  rw [← AMGameClass_merlin]
  refine mem_AMGameClass_cons_merlin ?_ 1
  rw [AMGameClass_nil]
  exact ⟨fun p => p.1.headD false == p.2.headD false, by fun_prop, fun _ => by simp⟩

/-- `MA ⊆ AM`, recovered from the round collapse. -/
example {α : Type} (enc : α ↪ List Bool) : MA enc ⊆ AM enc := MA_subset_AM

/-- Short move patterns (`[]`, `A`, `M`, `A M`, `M A`) and the collapse for alternating patterns. -/
example {α : Type} (enc : α ↪ List Bool) :
    AMGameClass enc [] = P enc ∧ AMGameClass enc [.arthur] = BPP enc ∧
      AMGameClass enc [.merlin] = NP enc ∧
      AMk enc 0 = P enc ∧ MAk enc 0 = P enc ∧
      AMk enc 1 = BPP enc ∧ MAk enc 1 = NP enc ∧
      AMk enc 2 = AM enc ∧ AMk enc 7 = AM enc ∧ MAk enc 2 = MA enc ∧ MAk enc 5 = AM enc ∧
      AMGameClass enc [.merlin, .arthur, .merlin] = AM enc :=
  ⟨AMGameClass_nil, AMGameClass_arthur, AMGameClass_merlin,
    AMk_zero, MAk_zero, AMk_one, MAk_one,
    AMk_two, AMk_eq_AM (by norm_num), MAk_two, MAk_eq_AM (by norm_num),
    AMGameClass_merlin_arthur_merlin⟩

end CslibFrontierTests.ArthurMerlinGames
