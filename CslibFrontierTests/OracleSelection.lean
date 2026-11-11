/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.Oracle.Selection

/-!
# Tests: selection rounds of oracle gates

A toy instance over a truth table `T : BitString (2 ^ n)`. Candidate `y : Fin (2 ^ n)` asks the
oracle about its `n` bits as constants, the table wire `T y` and every earlier-selection wire; its
word is the pair `(y, T y)`, and the default is the pair `(0, T 0)`. Then every round of an
accumulation emits a pair `(y, T y)`, whatever the oracle, with `2 ^ n` oracle gates per round and
oracle depth at most the number of rounds.
-/

namespace CslibFrontierTests.OracleSelection

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

/-- The `n` bits of `y`, as constants. -/
private def bitsOf (n : ℕ) (y : Fin (2 ^ n)) : Fin n → Bool := fun b => y.val.testBit b

/-- The sources of candidate `y`'s pair: its bits, then the table wire `T y`. -/
private def pairSrc (n E : ℕ) (y : Fin (2 ^ n)) : Fin (n + 1) → Source (2 ^ n + E) :=
  Fin.lastCases (.inl (Fin.castAdd E y)) fun b => .inr (bitsOf n y b)

/-- The sources of candidate `y`'s query: its pair, then every earlier-selection wire. -/
private def querySrc (n E : ℕ) (y : Fin (2 ^ n)) : Fin (n + 1 + E) → Source (2 ^ n + E) :=
  Fin.append (pairSrc n E y) fun e => .inl (Fin.natAdd (2 ^ n) e)

/-- The toy round on the table and `E` earlier-selection wires, with default `(0, T 0)`. -/
private def toyRound (n E : ℕ) : Circuit oracleSignature (2 ^ n + E) (2 ^ n + E + (n + 1)) :=
  selectionRound (querySrc n E) (pairSrc n E) (pairSrc n E ⟨0, Nat.two_pow_pos n⟩)

private theorem val_pairSrc (n E : ℕ) (y : Fin (2 ^ n)) (x : BitString (2 ^ n + E)) :
    substitute (pairSrc n E y) x = Fin.lastCases (x (Fin.castAdd E y)) (bitsOf n y) := by
  funext b
  induction b using Fin.lastCases <;> simp [pairSrc, substitute]

/-- Every round emits a pair `(y, T y)`. -/
private theorem toyRound_pair (n E : ℕ) (O : Language Bool) (x : BitString (2 ^ n + E)) :
    ∃ y : Fin (2 ^ n),
      selectedWord O (querySrc n E) (pairSrc n E) (pairSrc n E ⟨0, Nat.two_pow_pos n⟩) x =
        Fin.lastCases (x (Fin.castAdd E y)) (bitsOf n y) :=
  selectedWord_prop
    (P := fun v => ∃ y : Fin (2 ^ n), v = Fin.lastCases (x (Fin.castAdd E y)) (bitsOf n y))
    O _ _ _ x ⟨_, val_pairSrc n E _ x⟩ fun y _ => ⟨y, val_pairSrc n E y x⟩

/-- `R` toy rounds; round `r` reads the table and the `r` earlier pairs. -/
private def toyChain (n R : ℕ) : Circuit oracleSignature (2 ^ n) (2 ^ n + (n + 1) * R) :=
  Circuit.accumulate (fun r => toyRound n ((n + 1) * r)) R

private theorem eval_toyRound (n : ℕ) (O : Language Bool) (r : ℕ)
    (y : BitString (2 ^ n + (n + 1) * r)) :
    (toyRound n ((n + 1) * r)).eval (oracleInterpretation O) y =
      Fin.append y (selectedWord O (querySrc n _) (pairSrc n _) (pairSrc n _ ⟨0, Nat.two_pow_pos n⟩)
        y) :=
  eval_selectionRound _ _ _ O y

/-- **Every block of the accumulation is a pair `(y, T y)` of the input table `T`.** -/
example (n R : ℕ) (O : Language Bool) (T : BitString (2 ^ n)) {r : ℕ} (hr : r < R) :
    ∃ y : Fin (2 ^ n), ∀ b : Fin (n + 1),
      (toyChain n R).eval (oracleInterpretation O) T
          ⟨2 ^ n + (n + 1) * r + b, by
            have := Nat.mul_le_mul_left (n + 1) (Nat.succ_le_of_lt hr)
            rw [Nat.mul_succ] at this
            omega⟩ =
        Fin.lastCases (T y) (bitsOf n y) b := by
  obtain ⟨y, hy⟩ := toyRound_pair n _ O ((toyChain n r).eval (oracleInterpretation O) T)
  refine ⟨y, fun b => ?_⟩
  rw [toyChain, Circuit.eval_accumulate_block (eval_toyRound n O) T hr b, ← toyChain, hy]
  have hT := Circuit.eval_accumulate_input (eval_toyRound n O) T r y
  rw [← toyChain] at hT
  exact congrFun (congrArg (fun t => Fin.lastCases (motive := fun _ => Bool) t (bitsOf n y)) hT) b

/-- `R` rounds have `R * 2 ^ n` oracle gates. -/
example (n R : ℕ) : (toyChain n R).program.cost OracleOp.queryWeight = R * 2 ^ n := by
  simp [toyChain, Circuit.cost_program_accumulate, toyRound]

/-- `R` rounds have at most `R` oracle gates on any path. -/
example (n R : ℕ) : (toyChain n R).depthWith OracleOp.queryWeight ≤ R := by
  simpa [toyChain, toyRound] using
    Circuit.depthWith_accumulate_le _ _ (fun r _ => depthWith_selectionRound_le _ _ _)

/-- Each round has `2 + 2 ^ n` gates besides its multiplexers, so `R` rounds have at most
`R * (2 ^ n * (3 * n + 7))` gates. -/
example (n R : ℕ) : (toyChain n R).size ≤ R * (2 ^ n * (3 * n + 7)) := by
  simp only [toyChain, Circuit.size_accumulate, toyRound, size_selectionRound, Finset.sum_const,
    Finset.card_range, smul_eq_mul]
  refine Nat.mul_le_mul_left R ?_
  have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  nlinarith

/-- Round `r` reads at most `n + 1 + (n + 1) * r` wires per oracle gate. -/
example (n R : ℕ) : (toyChain n R).FanInAtMost (max (n + 1 + (n + 1) * R) 2) :=
  Circuit.fanInAtMost_accumulate _ fun _ hr => (fanInAtMost_selectionRound _ _ _).mono <|
    max_le_max (Nat.add_le_add_left (Nat.mul_le_mul_left _ hr.le) _) le_rfl

end CslibFrontierTests.OracleSelection
