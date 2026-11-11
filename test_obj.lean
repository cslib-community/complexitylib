import Mathlib
import CslibFrontier.Algorithms.Lean.Simplex.Dictionary

open Cslib.Algorithms.Lean.Simplex
open Matrix
open Dictionary

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m n : ℕ}

def x₀Index : Fin (n + 1 + m) := Fin.castAdd m (Fin.last n)

def unskipX₀ (i : Fin (n + 1 + m)) (hi : i ≠ x₀Index) : Fin (n + m) :=
  if h : i.val < n then
    ⟨i.val, by omega⟩
  else
    ⟨i.val - 1, by
      have h1 : i.val ≠ n := by
        intro heq
        apply hi
        ext
        simp [x₀Index, heq]
      omega⟩
