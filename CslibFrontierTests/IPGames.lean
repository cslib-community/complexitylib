/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.IP.Games.Repetition
import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Amplification
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! Concrete clients for private-coin games with a fixed pattern of moves: evaluated counts, the
difference between private and public coins on one game, a verifier that holds and one that
fails, `AM[k] ⊆ IP[k]`, and gap amplification by parallel repetition. -/

namespace ComplexityTests.IPGames

open Cslib Cslib.Complexity Cslib.Complexity.IPGame Turing.MultiTapeTM

example : (alternatingMoves .arthur 3).map AMMove.toIP = [.verifier, .prover, .verifier] := rfl

/-- The prover wins when its bit echoes the verifier's bit. -/
private def echo (t : List Bool) : ℕ := if t.getD 0 false = t.getD 1 false then 1 else 0

/-- When the verifier moves first, the prover echoes both messages. -/
example : count [(.verifier, 1), (.prover, 1)] echo = 2 := by decide

/-- When the prover moves first, its bit matches one message of two. -/
example : count [(.prover, 1), (.verifier, 1)] echo = 1 := by decide

/-- The verifier with one coin that sends it and accepts when the prover's reply echoes it. -/
private def echoMsg : BitString 1 → ℕ → List Bool → List Bool := fun c _ _ => List.ofFn c

private def echoDec : BitString 1 → List Bool → Bool := fun _ t => t.getD 0 false == t.getD 1 false

/-- Against the echo verifier, which reveals its coin, an optimal prover wins on both coins. -/
example : bestCount echoMsg echoDec [(.verifier, 1), (.prover, 1)] = 2 := by decide

/-- The verifier that keeps its coin private, sends nothing and accepts when the prover's bit is
the coin: an optimal prover is accepted on one coin of two. This is the difference between private
and public coins. -/
private def guessMsg : BitString 1 → ℕ → List Bool → List Bool := fun _ _ _ => []

private def guessDec : BitString 1 → List Bool → Bool := fun c t => t.getD 1 false == c 0

example : bestCount guessMsg guessDec [(.verifier, 1), (.prover, 1)] = 1 := by decide

/-- The guessing verifier, reading its coins as a list. -/
private def guessMsgList (_ : List Bool) (_ : ℕ) (_ : List Bool) : List Bool := []

private def guessDecList (c t : List Bool) : Bool := t.getD 1 false == c.getD 0 false

/-- Two parallel copies of the guessing game: an optimal prover is accepted on one coin string of
four, `1 ^ 2` out of `2 ^ 2`. -/
example : bestCount (ρ := 2 * 1)
    (fun c => repeatMsg 2 [(.verifier, 1), (.prover, 1)] fun i =>
      guessMsgList (BitString.listRow 1 i (List.ofFn c)))
    (fun c => repeatDec 2 [(.verifier, 1), (.prover, 1)] fun i =>
      guessDecList (BitString.listRow 1 i (List.ofFn c)))
    (repeatShape 2 [(.verifier, 1), (.prover, 1)]) = 1 := by
  rw [bestCount_repeat]
  decide

/-- `AM[k] ⊆ IP[k]`. -/
example {α : Type} (enc : α ↪ List Bool) (k : ℕ) : AMk enc k ⊆ IPk enc k := AMk_subset_IPk k

private theorem head_mem_IP2 : {w : List Bool | w.headD false = true} ∈ IPk encBits 2 := by
  refine AMk_subset_IPk 2 ?_
  rw [AMk_two]
  exact BPP_subset_AM (P_subset_BPP ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩)

/-- Every gap `2 ^ T(n)` is achieved by a private-coin verifier with two moves. -/
example (T : Polynomial ℕ) : ∃ (G : List (IPMove × Polynomial ℕ)) (ρ : Polynomial ℕ)
    (msg : List Bool × List Bool × ℕ × List Bool → List Bool)
    (dec : List Bool × List Bool × List Bool → Bool),
    G.map Prod.fst = [.verifier, .prover] ∧
      ComputableInPolyTime msg (encMsgInput encBits) encBits ∧
      ComputableInPolyTime dec (encDecInput encBits) encBool ∧
      ∀ a, (a ∈ {w : List Bool | w.headD false = true} →
          2 ^ T.eval a.length * 2 ^ ρ.eval a.length ≤
            3 ^ T.eval a.length * countAt encBits G ρ msg dec a) ∧
        (a ∉ {w : List Bool | w.headD false = true} →
          3 ^ T.eval a.length * countAt encBits G ρ msg dec a ≤ 2 ^ ρ.eval a.length) :=
  IPGameClass.exists_repeat head_mem_IP2 T

end ComplexityTests.IPGames
