/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Flat
public import CslibFrontier.Computability.WordRAM.Width
import Mathlib.Data.List.GetD

/-!
# Original-input bounds at every wider native query prefix

The program never reads the physical width. Its actual halting execution at the
original-input admission threshold therefore identifies every successful prefix
at any larger width. Words and zero memory above the original support bound are
controlled by that minimum execution, independently of the chosen physical width.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Every actual wider prefix has original-input bounded words and zero memory outside
the same width-independent support envelope. -/
theorem prefix_bounded {W L m t A B : ℕ} (q : Fin (10 ^ L))
    (hη : (innerSetO (PrunedQuery.queryAt q)).card = m)
    (a b : Fin (10 ^ L) → ℤ)
    (ha : ∀ i, (a i).natAbs ≤ A) (hb : ∀ i, (b i).natAbs ≤ B)
    (hW : admissionWidth L m t A B ≤ W) (s : State registers) (steps : ℕ)
    (hr : Runs W (program.program Reg.answer) (State.init (input L m t q a b)) s steps) :
    (∀ i, s.data.regs i < wordBound L m t A B) ∧
      (∀ p, s.data.mem p < wordBound L m t A B) ∧
      ∀ p, wordBound L m t A B ≤ p → s.data.mem p = 0 := by
  obtain ⟨hi, _, _, _, _, halt, _⟩ := runs_wide q hη a b ha hb le_rfl
  exact hr.prefix_bounds_init (Code.not_readsWidth_program not_readsWidth Reg.answer)
    hW hi halt (pow_admissionWidth_lt_wordBound L m t A B).le

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
