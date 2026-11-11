import Mathlib
import CslibFrontier.Algorithms.Lean.Simplex.TwoPhase

open Cslib.Algorithms.Lean.Simplex
open Matrix
open Dictionary

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m n : ℕ}

theorem phaseOneDict_equivalent_aux (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) :
    (auxDictionary A b).Equivalent (phaseOneDict A b) := by
  unfold phaseOneDict
  cases h : minRhsIndex b with
  | none => dsimp only; exact .refl _
  | some r =>
    dsimp only
    split_ifs with hneg
    · refine Dictionary.equivalent_pivot (r := slackIndex r) (s := x₀Index) ?_ ?_ ?_
      · sorry
      · sorry
      · sorry
    · exact .refl _
