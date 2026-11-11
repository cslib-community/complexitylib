/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Simplex.LinearProgram

/-!
# Two-phase simplex method

This module implements the two-phase simplex method for linear programs
`max c ⬝ᵥ x` subject to `x ≥ 0`, `A *ᵥ x ≤ b`.
-/

public section

namespace Cslib.Algorithms.Lean.Simplex

open Matrix
open Dictionary

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m n : ℕ}

/-- The outcome of the two-phase simplex method. -/
inductive TwoPhaseResult (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (c : Fin n → K)
  /-- The program is infeasible, certified by a Farkas certificate `y`. -/
  | infeasible (y : Fin m → K)
  /-- The program is unbounded, certified by a feasible ray `d` and a feasible point `x`. -/
  | unbounded (x d : Fin n → K)
  /-- The program is optimal, with primal solution `x` and dual solution `y`. -/
  | optimal (x : Fin n → K) (y : Fin m → K)

/-- The auxiliary matrix `[A | -1]` for Phase I. -/
def auxMatrix (A : Matrix (Fin m) (Fin n) K) : Matrix (Fin m) (Fin (n + 1)) K :=
  Matrix.of fun i j => if hj : j.val < n then A i ⟨j.val, hj⟩ else -1

/-- The objective for Phase I: `max -x₀`. -/
def auxObj : Fin (n + 1) → K :=
  fun j => if j.val < n then 0 else -1

/-- The auxiliary Phase I dictionary. -/
def auxDictionary (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) :
    Dictionary (Fin (n + 1 + m)) K :=
  slackDictionary (auxMatrix A) b auxObj

/-- The index of `x₀` in the auxiliary dictionary. -/
def x₀Index : Fin (n + 1 + m) := Fin.castAdd m (Fin.last n)

/-- The index of the slack variable for row `i` in the auxiliary dictionary. -/
def slackIndex (i : Fin m) : Fin (n + 1 + m) := Fin.natAdd (n + 1) i

/-- Finds the index `r : Fin m` minimizing `b r`. -/
def minRhsIndex (b : Fin m → K) : Option (Fin m) :=
  match minOpt (Finset.image b Finset.univ) with
  | none => none
  | some min_val => minOpt (Finset.univ.filter fun i => b i = min_val)

/-- Phase I initial feasible dictionary. -/
def phaseOneDict (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) : Dictionary (Fin (n + 1 + m)) K :=
  match minRhsIndex b with
  | none => auxDictionary A b
  | some r =>
    if b r < 0 then
      (auxDictionary A b).pivot (slackIndex r) x₀Index
    else
      auxDictionary A b

def unskipX₀ (i : Fin (n + 1 + m)) (hi : i ≠ x₀Index) : Fin (n + m) :=
  if h : i.val < n then
    ⟨i.val, by omega⟩
  else
    ⟨i.val - 1, by
      have h1 : i.val ≠ n := by intro heq; apply hi; ext; simp [x₀Index, heq]
      omega⟩

def skipX₀ (i : Fin (n + m)) : Fin (n + 1 + m) :=
  if h : i.val < n then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩

/-- Drop `x₀` from the dictionary and install the original objective `c`. -/
def dropX₀ (D : Dictionary (Fin (n + 1 + m)) K) (c : Fin n → K) : Dictionary (Fin (n + m)) K where
  basis := Finset.image (fun (i : {x // x ∈ D.basis.erase x₀Index}) =>
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

/-- Perform a degenerate pivot to remove `x₀` from the basis if it is basic. -/
def forcePivotX₀ (D : Dictionary (Fin (n + 1 + m)) K) : Dictionary (Fin (n + 1 + m)) K :=
  if h : x₀Index ∈ D.basis then
    match minOpt (D.basisᶜ.filter (fun j => D.coeff x₀Index j ≠ 0)) with
    | none => D
    | some j => D.pivot x₀Index j
  else D

/-- Extract Phase I result and prepare Phase II. -/
def phaseOneExtract (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (c : Fin n → K) :
    TwoPhaseResult A b c ⊕ Dictionary (Fin (n + m)) K :=
  match (phaseOneDict A b).simplex with
  | .optimal D =>
    if D.objConst < 0 then
      .inl (.infeasible D.slackDual)
    else
      .inr (dropX₀ (forcePivotX₀ D) c)
  | .unbounded _ _ => .inl (.infeasible 0) -- unreachable
  | .outOfFuel _ => .inl (.infeasible 0) -- unreachable

/-- The total two-phase simplex method returning terminating certificates. -/
def twoPhase (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (c : Fin n → K) : TwoPhaseResult A b c :=
  match phaseOneExtract A b c with
  | .inl res => res
  | .inr D =>
    match D.simplex with
    | .optimal D' =>
      TwoPhaseResult.optimal (fun j => D'.basicSolution (Fin.castAdd m j)) D'.slackDual
    | .unbounded D' s =>
      TwoPhaseResult.unbounded (fun j => D'.basicSolution (Fin.castAdd m j)) (fun j => D'.ray s (Fin.castAdd m j))
    | .outOfFuel _ => TwoPhaseResult.infeasible 0 -- unreachable

theorem phaseOneDict_feasible (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) :
    (phaseOneDict A b).Feasible := sorry

theorem extractInfeasible_spec (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (c : Fin n → K)
    (D : Dictionary (Fin (n + 1 + m)) K)
    (hopt : (phaseOneDict A b).simplex = .optimal D)
    (hneg : D.objConst < 0) :
    let y := D.slackDual; 0 ≤ y ∧ 0 ≤ y ᵥ* A ∧ y ⬝ᵥ b < 0 := sorry

theorem dropX₀_equivalent (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (c : Fin n → K)
    (D : Dictionary (Fin (n + 1 + m)) K)
    (hopt : (phaseOneDict A b).simplex = .optimal D)
    (hzero : D.objConst = 0) :
    let D' := dropX₀ (forcePivotX₀ D) c
    D'.Feasible ∧ D'.Equivalent (slackDictionary A b c) := sorry

/-- The total certificate specification for the two-phase simplex method. -/
theorem twoPhase_spec (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (c : Fin n → K) :
    match twoPhase A b c with
    | TwoPhaseResult.infeasible y => 0 ≤ y ∧ 0 ≤ y ᵥ* A ∧ y ⬝ᵥ b < 0
    | TwoPhaseResult.unbounded x d => 0 ≤ x ∧ A *ᵥ x ≤ b ∧ 0 ≤ d ∧ A *ᵥ d ≤ 0 ∧ 0 < c ⬝ᵥ d
    | TwoPhaseResult.optimal x y => 0 ≤ x ∧ A *ᵥ x ≤ b ∧ 0 ≤ y ∧ c ≤ y ᵥ* A ∧ c ⬝ᵥ x = y ⬝ᵥ b := sorry

end Cslib.Algorithms.Lean.Simplex
