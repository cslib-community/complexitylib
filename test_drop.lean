import Mathlib
import CslibFrontier.Algorithms.Lean.Simplex.Bland

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
      have h1 : i.val ≠ n := by intro heq; apply hi; ext; simp [x₀Index, heq]
      omega⟩

def skipX₀ (i : Fin (n + m)) : Fin (n + 1 + m) :=
  if h : i.val < n then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩

def dropX₀ (D : Dictionary (Fin (n + 1 + m)) K) (c : Fin n → K) : Dictionary (Fin (n + m)) K where
  basis := Finset.image (fun i : {x // x ∈ D.basis.erase x₀Index} =>
    unskipX₀ i.val (Finset.ne_of_mem_erase i.prop)) (D.basis.erase x₀Index).attach
  rhs i := D.rhs (skipX₀ i)
  coeff i j := D.coeff (skipX₀ i) (skipX₀ j)
  objConst := ∑ j : Fin n,
    if skipX₀ (Fin.castAdd m j) ∈ D.basis then
      c j * D.rhs (skipX₀ (Fin.castAdd m j))
    else 0
  objCoeff k := (if hk : k.val < n then c ⟨k.val, hk⟩ else 0) +
    ∑ j : Fin n,
      if skipX₀ (Fin.castAdd m j) ∈ D.basis then
        c j * D.coeff (skipX₀ (Fin.castAdd m j)) (skipX₀ k)
      else 0
