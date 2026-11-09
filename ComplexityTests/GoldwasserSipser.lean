/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.IP.Games.GoldwasserSipser
import Complexity.Computability.Complexity.Classes.ArthurMerlin.Amplification

/-! Concrete clients for the Goldwasser–Sipser emulation of private coins by public coins: the
move pattern of the emulation, the public-coin verifier on a small game with an honest and an
inflated claim, revealing the coins of a private-coin verifier, and `IP[k] ⊆ AM[k + 2]` and
`IP[k] = AM`. -/

namespace ComplexityTests.GoldwasserSipser

open Cslib Cslib.Complexity Cslib.Complexity.IPGame Cslib.Complexity.Emulation Turing.MultiTapeTM

/-- A verifier move becomes an Arthur move and a Merlin move, a prover move a Merlin move. -/
example : pattern [.verifier, .prover] = [.arthur, .merlin, .merlin] := rfl

/-- `IP[2]` emulated with the coins revealed: two adjacent Merlin moves, which merge into the
alternating pattern of `AM[4]`, so `IP[2] ⊆ AM[4]` before round collapse. -/
example : pattern ((alternatingMoves .arthur 2).map AMMove.toIP ++ [.verifier]) =
    [.arthur, .merlin, .merlin, .arthur, .merlin] := rfl

/-- `IP[1]` emulated with the coins revealed: the pattern `A M A M`, which is `AM[1 + 3]`. -/
example : pattern ((alternatingMoves .arthur 1).map AMMove.toIP ++ [.verifier]) =
    [.arthur, .merlin, .arthur, .merlin] := rfl

/-- The emulating shape of one verifier bit with one bit of claims and one padding bit: Arthur
sends a hash seed of `1 · (1 + 1) + 1` bits, Merlin a claim bit, a message bit and a padding
bit. -/
example : shape 1 1 [(.verifier, 1)] = [(.arthur, 3), (.merlin, 3)] := rfl

/-- One verifier bit and the payoff that accepts the message `true`, so the count is `1 = 2 ^ 0`.
With the honest claim `0` Merlin wins on six of the eight seeds. -/
example : AMGame.count (shape 1 1 [(.verifier, 1)])
    (check 1 1 1 (fun t => t == [true]) [(.verifier, 1)] 0 []) = 6 := by decide

/-- With the inflated claim `1` against the count `1`, Merlin must send zero padding and wins on
only four of the eight seeds. At these tiny parameters the errors are large; the class theorem
takes `B` polynomial and `K = B + O(log B)`. -/
example : AMGame.count (shape 1 1 [(.verifier, 1)])
    (check 1 1 1 (fun t => t == [true]) [(.verifier, 1)] 1 []) = 4 := by decide

/-- Against the payoff that always rejects Merlin never wins. -/
example : AMGame.count (shape 1 1 [(.verifier, 1)])
    (check 1 1 1 (fun _ => false) [(.verifier, 1)] 0 []) = 0 := by decide

/-- The verifier that keeps its coin private and accepts when the prover's bit is the coin. -/
private def guessMsg (_ : List Bool) (_ : ℕ) (_ : List Bool) : List Bool := []

private def guessDec (c t : List Bool) : Bool := t.getD 1 false == c.getD 0 false

/-- Revealing the coin of the guessing verifier after the game: the count is the number of coins
accepted against an optimal prover, one of two. -/
example : countFrom ([(.verifier, 1), (.prover, 1)] ++ [(.verifier, 1)])
    (revealPayoff guessMsg guessDec [(.verifier, 1), (.prover, 1)] 2) [] = 1 := by
  rw [countFrom_revealPayoff guessMsg guessDec _ (L := 2) rfl]
  decide

/-- `IP[k] ⊆ AM[k + 2]`. -/
example {α : Type} (enc : α ↪ List Bool) (k : ℕ) : IPk enc k ⊆ AMk enc (k + 2) := IPk_subset_AMk k

private theorem head_mem_IP2 : {w : List Bool | w.headD false = true} ∈ IPk encBits 2 := by
  refine AMk_subset_IPk 2 ?_
  rw [AMk_two]
  exact BPP_subset_AM (P_subset_BPP ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩)

/-- A problem in `IP[2]`, through the emulation, has a public-coin verifier whose pattern has five
entries, four moves once the adjacent Merlin moves are merged. -/
example : {w : List Bool | w.headD false = true} ∈
    AMGameClass encBits [.arthur, .merlin, .merlin, .arthur, .merlin] :=
  IPGameClass_subset_AMGameClass _ head_mem_IP2

/-- `IP[3] = AM`. -/
example {α : Type} (enc : α ↪ List Bool) : IPk enc 3 = AM enc := IPk_eq_AM (by norm_num)

end ComplexityTests.GoldwasserSipser
