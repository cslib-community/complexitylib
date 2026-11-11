import Mathlib
import CslibFrontier.Algorithms.Lean.Simplex.Dictionary

open Cslib.Algorithms.Lean.Simplex
open Matrix
open Dictionary

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m n : ℕ}

def x₀Index : Fin (n + 1 + m) := Fin.castAdd m (Fin.last n)

def forcePivotX₀ (D : Dictionary (Fin (n + 1 + m)) K) : Dictionary (Fin (n + 1 + m)) K :=
  if h : x₀Index ∈ D.basis then
    match minOpt (D.basisᶜ.filter (fun j => D.coeff x₀Index j ≠ 0)) with
    | none => D
    | some j => D.pivot x₀Index j
  else D
