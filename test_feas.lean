import Mathlib
import CslibFrontier.Algorithms.Lean.Simplex.TwoPhase

open Cslib.Algorithms.Lean.Simplex
open Matrix
open Dictionary

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m n : ℕ}

theorem phaseOneDict_feasible (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) :
    (phaseOneDict A b).Feasible := by
  sorry
