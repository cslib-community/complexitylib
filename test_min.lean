import Mathlib
import CslibFrontier.Algorithms.Lean.Simplex.Bland

open Cslib.Algorithms.Lean.Simplex

def minRhsIndex {K : Type*} [LinearOrder K] {m : ℕ} (b : Fin m → K) : Option (Fin m) :=
  match minOpt (Finset.image b Finset.univ) with
  | none => none
  | some min_val => minOpt (Finset.univ.filter fun i => b i = min_val)
