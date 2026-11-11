/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (spike for #4383 M5.4d; not for merge)

public import CslibFrontier.Computability.Circuit.Boolean.Oracle.Selection
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Spike: a toy selection round over a truth table

Scratch for #4383 (M5.4d). Not for merge. Candidate `y : Fin (2 ^ n)` queries its `n` bits as
constants, the table wire `T y`, and every earlier-selection wire; its pair is `(y, T y)`, and the
default is `(0, T 0)`.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Spike

/-- The `n` bits of `y`, as constants. -/
def bitsOf (n : ℕ) (y : Fin (2 ^ n)) : Fin n → Bool := fun b => y.val.testBit b

/-- The sources of candidate `y`'s pair: its bits, then the table wire `T y`. -/
def pairSrc (n E : ℕ) (y : Fin (2 ^ n)) : Fin (n + 1) → Source (2 ^ n + E) :=
  Fin.lastCases (.inl (Fin.castAdd E y)) fun b => .inr (bitsOf n y b)

/-- The sources of candidate `y`'s query: its pair, then every earlier-selection wire. -/
def querySrc (n E : ℕ) (y : Fin (2 ^ n)) : Fin (n + 1 + E) → Source (2 ^ n + E) :=
  Fin.append (pairSrc n E y) fun e => .inl (Fin.natAdd (2 ^ n) e)

/-- The toy round on the table and `E` earlier-selection wires. -/
def toyRound (n E : ℕ) : Circuit oracleSignature (2 ^ n + E) (2 ^ n + E + (n + 1)) :=
  round (querySrc n E) (pairSrc n E) (pairSrc n E ⟨0, Nat.two_pow_pos n⟩)

/-- The pair read from the sources of candidate `y`. -/
theorem val_pairSrc (n E : ℕ) (y : Fin (2 ^ n)) (x : BitString (2 ^ n + E)) :
    (fun b => (pairSrc n E y b).val x) =
      Fin.lastCases (x (Fin.castAdd E y)) (bitsOf n y) := by
  funext b
  induction b using Fin.lastCases <;> simp [pairSrc, Source.val]

/-- **Every emitted pair is `(y, T y)`.** -/
theorem toyRound_pair (n E : ℕ) (O : Language Bool) (x : BitString (2 ^ n + E)) :
    ∃ y : Fin (2 ^ n), (fun b => (toyRound n E).eval (oracleInterpretation O) x
        (Fin.natAdd (2 ^ n + E) b)) = Fin.lastCases (x (Fin.castAdd E y)) (bitsOf n y) := by
  simp only [toyRound, eval_round, Fin.append_right]
  rcases firstSel_mem (fun b => (pairSrc n E ⟨0, Nat.two_pow_pos n⟩ b).val x) _
      (fun i b => (pairSrc n E i b).val x) with h | ⟨y, h⟩
  · exact ⟨_, h.trans (val_pairSrc n E _ x)⟩
  · exact ⟨y, h.trans (val_pairSrc n E y x)⟩

theorem size_toyRound (n E : ℕ) : (toyRound n E).size = 2 + 2 ^ n + 2 ^ n * (3 * (n + 1) + 1) :=
  size_round _ _ _

theorem cost_toyRound (n E : ℕ) : (toyRound n E).program.cost OracleOp.queryWeight = 2 ^ n :=
  cost_round _ _ _

theorem depthWith_toyRound_le (n E : ℕ) : (toyRound n E).depthWith OracleOp.queryWeight ≤ 1 :=
  depthWith_round_le _ _ _

theorem fanInAtMost_toyRound (n E : ℕ) : (toyRound n E).FanInAtMost (max (n + 1 + E) 2) :=
  fanInAtMost_round _ _ _

/-! ### `R` rounds -/

/-- `R` toy rounds; round `r` reads the table and the `r` earlier selections. -/
def toyChain (n R : ℕ) : Circuit oracleSignature (2 ^ n) (2 ^ n + (n + 1) * R) :=
  chain (fun r => toyRound n ((n + 1) * r)) R

theorem cost_toyChain (n R : ℕ) :
    (toyChain n R).program.cost OracleOp.queryWeight = R * 2 ^ n := by
  rw [toyChain, cost_chain]
  simp [cost_toyRound]

theorem depthWith_toyChain_le (n R : ℕ) :
    (toyChain n R).depthWith OracleOp.queryWeight ≤ R := by
  simpa [toyChain] using depthWith_chain_le _ _ (fun r => depthWith_toyRound_le n ((n + 1) * r)) R

theorem size_toyChain_le (n R : ℕ) : (toyChain n R).size ≤ R * (2 ^ n * (3 * n + 7)) := by
  rw [toyChain, size_chain]
  simp only [size_toyRound, Finset.sum_const, Finset.card_range, smul_eq_mul]
  refine Nat.mul_le_mul_left R ?_
  have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  nlinarith

theorem fanInAtMost_toyChain (n R : ℕ) :
    (toyChain n R).FanInAtMost (max (n + 1 + (n + 1) * R) 2) :=
  fanInAtMost_chain _ fun _ hr => (fanInAtMost_toyRound n _).mono <|
    max_le_max (Nat.add_le_add_left (Nat.mul_le_mul_left _ hr.le) _) le_rfl

end Cslib.Circuits.Boolean.Spike
