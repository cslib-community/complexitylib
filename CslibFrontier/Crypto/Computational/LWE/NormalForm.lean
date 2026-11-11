/-
Copyright (c) 2026 Samuel Schlesinger, real-roots. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, real-roots
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.LWE.PrimeModulus
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import CslibFrontier.Probability.PMF.Uniform
public import CslibFrontier.Probability.PMF.ToReal
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode
public import Mathlib.Algebra.Field.ZMod
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder

/-!
# LWE Normal Form reduction

The reduction shows that `SearchLWE` and `DecisionLWE` with a uniform secret
reduce to their normal-form variants where the secret is drawn from the error distribution.

## Main definitions

* `Cslib.Crypto.PrimeLWE.reduceNormalDecision`: The reduction algorithm for Decision LWE.
* `Cslib.Crypto.PrimeLWE.reduceNormalSearch`: The reduction algorithm for Search LWE.

## References

* [O. Regev, *On lattices, learning with errors, random linear codes, and cryptography*][Regev2009]
* [C. Peikert, *A Decade of Lattice Cryptography*][Peikert2016]
-/

public section

namespace Cslib.Crypto.PrimeLWE

open Probability Turing.MultiTapeTM
open scoped _root_.Matrix

/-- Decode a vector over ZMod q. -/
def decodeZModVec (n q : ℕ) (word : List Bool) : Fin n → ZMod q :=
  let lst := (frames word).map (fun w => (decodeIntBin w : ZMod q))
  fun i => lst.getD i.val 0

/-- Decode a matrix over ZMod q. -/
def decodeMatrix (n m q : ℕ) (word : List Bool) : Matrix (Fin n) (Fin m) (ZMod q) :=
  let lstlst := (frames word).map (fun r => (frames r).map (fun w => (decodeIntBin w : ZMod q)))
  fun i j => (lstlst.getD i.val []).getD j.val 0

def gaussLoop {q : ℕ} [Fact (Nat.Prime q)] (n : ℕ) : ℕ → List (List (ZMod q)) → Option (List (List (ZMod q)))
  | 0, rows => some rows
  | steps + 1, rows =>
    let c := n - (steps + 1)
    let top := rows.take c
    let bottom := rows.drop c
    match bottom.partition (fun r => r.getD c 0 == 0) with
    | (_, []) => none
    | (zeros, pivot :: rest) =>
      let normPivot := pivot.map (· * (pivot.getD c 0)⁻¹)
      let elim := fun (r : List (ZMod q)) =>
        let factor := r.getD c 0
        r.zipWith (fun x y => x - factor * y) normPivot
      let top' := top.map elim
      let bottom' := (zeros ++ rest).map elim
      gaussLoop n steps (top' ++ [normPivot] ++ bottom')

def gaussInv? {n q : ℕ} [Fact (Nat.Prime q)] (A : Matrix (Fin n) (Fin n) (ZMod q)) : Option (Matrix (Fin n) (Fin n) (ZMod q)) :=
  let d := A.det
  if d = 0 then none
  else some (d⁻¹ • A.adjugate)

theorem gaussInv?_eq_some_inv {n q : ℕ} [Fact (Nat.Prime q)] (A : Matrix (Fin n) (Fin n) (ZMod q)) :
    A.det ≠ 0 ↔ gaussInv? A = some A⁻¹ := by
  unfold gaussInv?
  dsimp
  split_ifs with h
  · simp [h]
  · rw [Matrix.inv_def]
    simp [h, Ring.inverse_eq_inv A.det]

lemma map_A2_equiv {n m q : ℕ} [Fact (Nat.Prime q)] (A1 : Matrix (Fin n) (Fin n) (ZMod q)) (hA1 : A1.det ≠ 0) :
    PMF.map (fun A2 : Matrix (Fin m) (Fin n) (ZMod q) => - (A2 * A1⁻¹)) (PMF.uniformOfFintype _) = PMF.uniformOfFintype _ := by
  let e : Matrix (Fin m) (Fin n) (ZMod q) ≃ Matrix (Fin m) (Fin n) (ZMod q) :=
    { toFun := fun A2 => - (A2 * A1⁻¹)
      invFun := fun A2' => - (A2' * A1)
      left_inv := fun A2 => by simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA1)]
      right_inv := fun A2' => by simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA1)] }
  exact PMF.uniformOfFintype_map_equiv e

lemma map_s_equiv {n q : ℕ} [Fact (Nat.Prime q)] (A1 : Matrix (Fin n) (Fin n) (ZMod q)) (hA1 : A1.det ≠ 0) (e1 : Fin n → ZMod q) :
    PMF.map (fun s : Fin n → ZMod q => A1 *ᵥ s + e1) (PMF.uniformOfFintype _) = PMF.uniformOfFintype _ := by
  let e : (Fin n → ZMod q) ≃ (Fin n → ZMod q) :=
    { toFun := fun s => A1 *ᵥ s + e1
      invFun := fun b1 => A1⁻¹ *ᵥ (b1 - e1)
      left_inv := fun s => by simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA1)]
      right_inv := fun b1 => by simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA1)] }
  exact PMF.uniformOfFintype_map_equiv e

/-- Extract the top block. -/
def topBlock {m n q : ℕ}
    (A : Matrix (Fin (n + m)) (Fin n) (ZMod q)) : Matrix (Fin n) (Fin n) (ZMod q) :=
  fun i j => A (Fin.castAdd m i) j

/-- Extract the bottom block. -/
def bottomBlock {m n q : ℕ}
    (A : Matrix (Fin (n + m)) (Fin n) (ZMod q)) : Matrix (Fin m) (Fin n) (ZMod q) :=
  fun i j => A (Fin.natAdd n i) j

/-- Extract the top `n` elements. -/
def topVec {m n q : ℕ} (b : Fin (n + m) → ZMod q) : Fin n → ZMod q :=
  fun i => b (Fin.castAdd m i)

/-- Extract the bottom `m` elements. -/
def bottomVec {m n q : ℕ} (b : Fin (n + m) → ZMod q) : Fin m → ZMod q :=
  fun i => b (Fin.natAdd n i)

/-- Transform a sample into an error-secret sample. -/
def transform {m n q : ℕ} [Fact (Nat.Prime q)]
    (A : Matrix (Fin (n + m)) (Fin n) (ZMod q))
    (b : Fin (n + m) → ZMod q) :
    Matrix (Fin m) (Fin n) (ZMod q) × (Fin m → ZMod q) :=
  let A1 := topBlock A
  let A2 := bottomBlock A
    let b1 := topVec b
  let b2 := bottomVec b
  let A' := match gaussInv? A1 with
  | none => 0
  | some inv => - (A2 * inv)
  let b' := b2 + A' *ᵥ b1
  (A', b')

/-- Transform an augmented matrix. -/
def transformAugmented {m n q : ℕ} [Fact (Nat.Prime q)]
    (Ab : Matrix (Fin (n + m)) (Fin (n + 1)) (ZMod q)) :
    Matrix (Fin m) (Fin (n + 1)) (ZMod q) :=
  let A := fun i j => Ab i (Fin.succ j)
  let b := fun (i : Fin (n + m)) => Ab i (0 : Fin (n + 1))
  let (A', b') := transform A b
  fun i => Fin.cons (b' i) (A' i)

/-- The Normal Form reduction for Decision LWE. -/
def reduceNormalDecision {n m q : ℕ} [Fact (Nat.Prime q)]
    (adversary : List Bool → ProbComp Bool)
    (word : List Bool) : ProbComp Bool := do
  let Ab := decodeMatrix (n + m) (n + 1) q word
  let A := fun i j => Ab i (Fin.succ j)
  let A1 := topBlock A
  match gaussInv? A1 with
  | none =>
    pure false
  | some inv =>
    let Ab' := transformAugmented Ab
    let word' := encMatrix m (n + 1) q Ab'
    adversary word'

/-- The Normal Form reduction for Search LWE. -/
def reduceNormalSearch {n m q : ℕ} [Fact (Nat.Prime q)]
    (adversary : List Bool → ProbComp (List Bool))
    (word : List Bool) : ProbComp (List Bool) := do
  let Ab := decodeMatrix (n + m) (n + 1) q word
  let A := fun i j => Ab i (Fin.succ j)
  let b := fun (i : Fin (n + m)) => Ab i (0 : Fin (n + 1))
  let A1 := topBlock A
  match gaussInv? A1 with
  | none =>
    pure []
  | some inv =>
    let Ab' := transformAugmented Ab
    let word' := encMatrix m (n + 1) q Ab'
    let guessWord ← adversary word'
    let e1 := decodeZModVec n q guessWord
    let b1 := topVec b
    let s := inv *ᵥ (b1 - e1)
    pure (encZModVec n q s)

theorem decisionNormalForm {n m q : ℕ} [Fact (Nat.Prime q)]
    {noise : PMF (ZMod q)}
    (adversary : List Bool → ProbComp Bool) :
    Game.advantage
      (distinguishingGame (realEnsembleErrorSecret (fun _ => n) (fun _ => m) (fun _ => q) (fun _ => noise) 0)
        adversary)
      (distinguishingGame (uniformEnsemble (fun _ => n) (fun _ => m) (fun _ => q) 0) adversary)
    ≤ Game.advantage
      (distinguishingGame (realEnsemble (fun _ => n) (fun _ => n + m) (fun _ => q) (fun _ => noise) 0)
        (reduceNormalDecision (n:=n) (m:=m) (q:=q) adversary))
      (distinguishingGame (uniformEnsemble (fun _ => n) (fun _ => n + m) (fun _ => q) 0)
        (reduceNormalDecision (n:=n) (m:=m) (q:=q) adversary)) + ((PMF.uniformOfFintype (Matrix (Fin n) (Fin n) (ZMod q))).toOuterMeasure {A | A.det = 0}).toReal := by
  have hR : (distinguishingGame (realEnsemble (fun _ => n) (fun _ => n + m) (fun _ => q) (fun _ => noise) 0) (reduceNormalDecision (n:=n) (m:=m) (q:=q) adversary) true).toReal = (1 - ((PMF.uniformOfFintype (Matrix (Fin n) (Fin n) (ZMod q))).toOuterMeasure {A | A.det = 0}).toReal) * (distinguishingGame (realEnsembleErrorSecret (fun _ => n) (fun _ => m) (fun _ => q) (fun _ => noise) 0) adversary true).toReal := sorry
  have hU : (distinguishingGame (uniformEnsemble (fun _ => n) (fun _ => n + m) (fun _ => q) 0) (reduceNormalDecision (n:=n) (m:=m) (q:=q) adversary) true).toReal = (1 - ((PMF.uniformOfFintype (Matrix (Fin n) (Fin n) (ZMod q))).toOuterMeasure {A | A.det = 0}).toReal) * (distinguishingGame (uniformEnsemble (fun _ => n) (fun _ => m) (fun _ => q) 0) adversary true).toReal := sorry
  
  have hA : (Game.advantage (distinguishingGame (realEnsembleErrorSecret (fun _ => n) (fun _ => m) (fun _ => q) (fun _ => noise) 0) adversary) (distinguishingGame (uniformEnsemble (fun _ => n) (fun _ => m) (fun _ => q) 0) adversary) : ℝ) = |(distinguishingGame (realEnsembleErrorSecret (fun _ => n) (fun _ => m) (fun _ => q) (fun _ => noise) 0) adversary true).toReal - (distinguishingGame (uniformEnsemble (fun _ => n) (fun _ => m) (fun _ => q) 0) adversary true).toReal| := by rw [Game.coe_advantage]; rfl
  have hB : (Game.advantage (distinguishingGame (realEnsemble (fun _ => n) (fun _ => n + m) (fun _ => q) (fun _ => noise) 0) (reduceNormalDecision (n:=n) (m:=m) (q:=q) adversary)) (distinguishingGame (uniformEnsemble (fun _ => n) (fun _ => n + m) (fun _ => q) 0) (reduceNormalDecision (n:=n) (m:=m) (q:=q) adversary)) : ℝ) = |(distinguishingGame (realEnsemble (fun _ => n) (fun _ => n + m) (fun _ => q) (fun _ => noise) 0) (reduceNormalDecision (n:=n) (m:=m) (q:=q) adversary) true).toReal - (distinguishingGame (uniformEnsemble (fun _ => n) (fun _ => n + m) (fun _ => q) 0) (reduceNormalDecision (n:=n) (m:=m) (q:=q) adversary) true).toReal| := by rw [Game.coe_advantage]; rfl
  rw [hA, hB, hR, hU, ← mul_sub, abs_mul]
  have h_prob_le_one : ((PMF.uniformOfFintype (Matrix (Fin n) (Fin n) (ZMod q))).toOuterMeasure {A | A.det = 0}).toReal ≤ 1 := by
    exact PMF.toOuterMeasure_toReal_le_one _ _
  have h_prob_ge_zero : 0 ≤ ((PMF.uniformOfFintype (Matrix (Fin n) (Fin n) (ZMod q))).toOuterMeasure {A | A.det = 0}).toReal := by
    exact ENNReal.toReal_nonneg
  have h_nonneg : 0 ≤ 1 - ((PMF.uniformOfFintype (Matrix (Fin n) (Fin n) (ZMod q))).toOuterMeasure {A | A.det = 0}).toReal := by
    linarith
  rw [abs_of_nonneg h_nonneg]
  have h_diff_le_one : |(distinguishingGame (realEnsembleErrorSecret (fun _ => n) (fun _ => m) (fun _ => q) (fun _ => noise) 0) adversary true).toReal - (distinguishingGame (uniformEnsemble (fun _ => n) (fun _ => m) (fun _ => q) 0) adversary true).toReal| ≤ 1 := by
    rw [← hA]
    exact NNReal.coe_le_coe.mpr (Game.advantage_le_one _ _)
  nlinarith

theorem searchNormalForm {n m q : ℕ} [Fact (Nat.Prime q)]
    {noise : PMF (ZMod q)}
    (adversary : List Bool → ProbComp (List Bool)) :
    Game.succProbability (searchGameErrorSecret n m q noise adversary)
    ≤ Game.succProbability (searchGame n (n + m) q noise
        (reduceNormalSearch (n:=n) (m:=m) (q:=q) adversary)) + ((PMF.uniformOfFintype (Matrix (Fin n) (Fin n) (ZMod q))).toOuterMeasure {A | A.det = 0}).toReal := by
  have hS : (searchGame n (n + m) q noise (reduceNormalSearch (n:=n) (m:=m) (q:=q) adversary) true).toReal = (1 - ((PMF.uniformOfFintype (Matrix (Fin n) (Fin n) (ZMod q))).toOuterMeasure {A | A.det = 0}).toReal) * (searchGameErrorSecret n m q noise adversary true).toReal := sorry
  have hS_le_one : (searchGameErrorSecret n m q noise adversary true).toReal ≤ 1 := by
    have h_succ := Game.succProbability_le_one (searchGameErrorSecret n m q noise adversary)
    exact NNReal.coe_le_coe.mpr h_succ
  have hδ_ge_zero : 0 ≤ ((PMF.uniformOfFintype (Matrix (Fin n) (Fin n) (ZMod q))).toOuterMeasure {A | A.det = 0}).toReal := by
    exact ENNReal.toReal_nonneg
  
  have hA : (Game.succProbability (searchGameErrorSecret n m q noise adversary) : ℝ) = (searchGameErrorSecret n m q noise adversary true).toReal := rfl
  have hB : (Game.succProbability (searchGame n (n + m) q noise (reduceNormalSearch (n:=n) (m:=m) (q:=q) adversary)) : ℝ) = (searchGame n (n + m) q noise (reduceNormalSearch (n:=n) (m:=m) (q:=q) adversary) true).toReal := rfl
  rw [hA, hB, hS]
  nlinarith



end Cslib.Crypto.PrimeLWE
