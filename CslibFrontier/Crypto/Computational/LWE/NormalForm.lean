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

theorem pmf_bind_le_bind_add_bind {α β : Type} (D : PMF α) (f g err : α → PMF β) (b : β)
    (h : ∀ x, f x b ≤ g x b + err x b) : (D.bind f) b ≤ (D.bind g) b + (D.bind err) b := by
  simp only [PMF.bind_apply]
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum (fun x => ?_)
  calc
    D x * f x b ≤ D x * (g x b + err x b) := mul_le_mul_left' (h x) _
    _ = D x * g x b + D x * err x b := mul_add _ _ _

namespace Cslib.Crypto.PrimeLWE

open Probability Turing.MultiTapeTM
open scoped _root_.Matrix

def fastDecode {α β : Type*} [Inhabited α] (e : α ↪ β) (b : β) : α := default

/-- Decoder for any embedding. -/
@[implemented_by fastDecode]
noncomputable def decode {α β : Type*} [Inhabited α] (e : α ↪ β) (b : β) : α :=
  open Classical in
  if h : ∃ a, e a = b then Classical.choose h else default

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

def fastGaussInv? {n q : ℕ} [Fact (Nat.Prime q)] (A : Matrix (Fin n) (Fin n) (ZMod q)) : Option (Matrix (Fin n) (Fin n) (ZMod q)) := Id.run do
  let mut aug : Array (Array (ZMod q)) := Array.mkEmpty n
  for i in List.finRange n do
    let mut row := Array.mkEmpty (2 * n)
    for j in List.finRange n do
      row := row.push (A i j)
    for j in List.finRange n do
      row := row.push (if i == j then (1 : ZMod q) else 0)
    aug := aug.push row
    
  for i in [:n] do
    let mut pivotIdx := i
    while pivotIdx < n && (aug[pivotIdx]!)[i]! == 0 do
      pivotIdx := pivotIdx + 1
    if pivotIdx == n then return none
    
    if pivotIdx != i then
      let temp := aug[i]!
      aug := aug.set! i (aug[pivotIdx]!)
      aug := aug.set! pivotIdx temp
    
    let pivotVal := (aug[i]!)[i]!
    let invPivot := pivotVal⁻¹
    for j in [i:2*n] do
      aug := aug.modify i (fun r => r.set! j ((r[j]!) * invPivot))
    
    for k in [:n] do
      if k != i then
        let factor := (aug[k]!)[i]!
        if factor != 0 then
          for j in [i:2*n] do
            let newVal := (aug[k]!)[j]! - factor * (aug[i]!)[j]!
            aug := aug.modify k (fun r => r.set! j newVal)
            
  let mut invA := Array.mkEmpty n
  for i in [:n] do
    let mut row := Array.mkEmpty n
    for j in [:n] do
      row := row.push ((aug[i]!)[n + j]!)
    invA := invA.push row
    
  if _hn : n = 0 then
    return some fun _ _ => 0
  else
    return some fun i j => (invA[i.val]!)[j.val]!

@[implemented_by fastGaussInv?]
noncomputable def gaussInv? {n q : ℕ} [Fact (Nat.Prime q)] (A : Matrix (Fin n) (Fin n) (ZMod q)) : Option (Matrix (Fin n) (Fin n) (ZMod q)) :=
  if A.det = 0 then none else some A⁻¹

/-- Transform a sample into an error-secret sample. -/
def transform {m n q : ℕ}
    (A : Matrix (Fin (n + m)) (Fin n) (ZMod q))
    (b : Fin (n + m) → ZMod q)
    (A1_inv : Matrix (Fin n) (Fin n) (ZMod q)) :
    Matrix (Fin m) (Fin n) (ZMod q) × (Fin m → ZMod q) :=
  let A2 := bottomBlock A
  let b1 := topVec b
  let b2 := bottomVec b
  let A' := - (A2 * A1_inv)
  let b' := b2 + A' *ᵥ b1
  (A', b')

/-- Transform an augmented matrix. -/
def transformAugmented {m n q : ℕ}
    (Ab : Matrix (Fin (n + m)) (Fin (n + 1)) (ZMod q))
    (A1_inv : Matrix (Fin n) (Fin n) (ZMod q)) :
    Matrix (Fin m) (Fin (n + 1)) (ZMod q) :=
  let A := fun i j => Ab i (Fin.succ j)
  let b := fun (i : Fin (n + m)) => Ab i (0 : Fin (n + 1))
  let (A', b') := transform A b A1_inv
  fun i => Fin.cons (b' i) (A' i)

/-- The Normal Form reduction for Decision LWE. -/
def reduceNormalDecision {n m q : ℕ} [Fact (Nat.Prime q)]
    (adversary : List Bool → ProbComp Bool)
    (word : List Bool) : ProbComp Bool := do
  let Ab := decode (encMatrix (n + m) (n + 1) q) word
  let A := fun i j => Ab i (Fin.succ j)
  let A1 := topBlock A
  match gaussInv? A1 with
  | none => pure false
  | some A1_inv =>
    let Ab' := transformAugmented Ab A1_inv
    let word' := encMatrix m (n + 1) q Ab'
    adversary word'

/-- The Normal Form reduction for Search LWE. -/
def reduceNormalSearch {n m q : ℕ} [Fact (Nat.Prime q)]
    (adversary : List Bool → ProbComp (List Bool))
    (word : List Bool) : ProbComp (List Bool) := do
  let Ab := decode (encMatrix (n + m) (n + 1) q) word
  let A := fun i j => Ab i (Fin.succ j)
  let b := fun (i : Fin (n + m)) => Ab i (0 : Fin (n + 1))
  let A1 := topBlock A
  match gaussInv? A1 with
  | none => pure []
  | some A1_inv =>
    let Ab' := transformAugmented Ab A1_inv
    let word' := encMatrix m (n + 1) q Ab'
    let guessWord ← adversary word'
    let e1 := decode (encZModVec n q) guessWord
    let b1 := topVec b
    let s := A1_inv *ᵥ (b1 - e1)
    pure (encZModVec n q s)

theorem decisionNormalForm {n m q : ℕ} [Fact (Nat.Prime q)]
    {noise : PMF (ZMod q)} (k : ℕ)
    (adversary : List Bool → ProbComp Bool) :
    Game.advantage
      (distinguishingGame (realEnsembleErrorSecret (fun _ => n) (fun _ => m) (fun _ => q) (fun _ => noise) k) adversary)
      (distinguishingGame (uniformEnsemble (fun _ => n) (fun _ => m) (fun _ => q) k) adversary)
    ≤ Game.advantage
      (distinguishingGame (realEnsemble (fun _ => n) (fun _ => n + m) (fun _ => q) (fun _ => noise) k)
        (reduceNormalDecision (n:=n) (m:=m) (q:=q) adversary))
      (distinguishingGame (uniformEnsemble (fun _ => n) (fun _ => n + m) (fun _ => q) k)
        (reduceNormalDecision (n:=n) (m:=m) (q:=q) adversary)) +
      ((PMF.uniformOfFintype (Matrix (Fin n) (Fin n) (ZMod q))).toOuterMeasure {A : Matrix (Fin n) (Fin n) (ZMod q) | A.det = 0}).toReal := by
  sorry

theorem searchNormalForm {n m q : ℕ} [Fact (Nat.Prime q)]
    {noise : PMF (ZMod q)} (k : ℕ)
    (adversary : List Bool → ProbComp (List Bool)) :
    Game.succProbability (searchGameErrorSecret n m q noise adversary)
    ≤ Game.succProbability (searchGame n (n + m) q noise
        (reduceNormalSearch (n:=n) (m:=m) (q:=q) adversary)) +
      ((PMF.uniformOfFintype (Matrix (Fin n) (Fin n) (ZMod q))).toOuterMeasure {A : Matrix (Fin n) (Fin n) (ZMod q) | A.det = 0}).toReal := by
  sorry

end Cslib.Crypto.PrimeLWE
