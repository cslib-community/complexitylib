/-
Copyright (c) 2026 Samuel Schlesinger, real-roots. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, real-roots
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.LWE.PrimeModulus
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode
public import Mathlib.Algebra.Field.ZMod
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.Uniform

/-!
# LWE Normal Form reduction

The reduction shows that `SearchLWE` and `DecisionLWE` with a uniform secret
reduce to their normal-form variants where the secret is drawn from the error distribution.

Given `n + m` samples `[A * s + e | A]`, the reduction splits `A` into a top `n × n` block `A₁`
and a bottom block `A₂`. When `A₁` is invertible it outputs the `m` samples
`[A' * e₁ + e₂ | A']` with `A' = -A₂ A₁⁻¹`, whose secret is the top error vector `e₁`; the
uniform secret `s` cancels. Otherwise it gives up. The loss is the probability that a uniform
`n × n` matrix is singular.

## Main definitions

* `Cslib.Crypto.PrimeLWE.reduceNormalDecision`: The reduction algorithm for Decision LWE.
* `Cslib.Crypto.PrimeLWE.reduceNormalSearch`: The reduction algorithm for Search LWE.

## Main results

* `Cslib.Crypto.PrimeLWE.decisionNormalForm`: the advantage against error-secret decision LWE
  is at most the reduction's advantage against decision LWE plus the singularity probability.
* `Cslib.Crypto.PrimeLWE.searchNormalForm`: the same bound for search LWE.

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

/-- The inverse of a square matrix over `ZMod q`, or `none` when it is singular. -/
def gaussInv? {n q : ℕ} [Fact (Nat.Prime q)] (A : Matrix (Fin n) (Fin n) (ZMod q)) :
    Option (Matrix (Fin n) (Fin n) (ZMod q)) :=
  let d := A.det
  if d = 0 then none
  else some (d⁻¹ • A.adjugate)

theorem gaussInv?_eq_some_inv {n q : ℕ} [Fact (Nat.Prime q)]
    (A : Matrix (Fin n) (Fin n) (ZMod q)) :
    A.det ≠ 0 ↔ gaussInv? A = some A⁻¹ := by
  unfold gaussInv?
  dsimp
  split_ifs with h
  · simp [h]
  · rw [Matrix.inv_def]
    simp [h, Ring.inverse_eq_inv A.det]

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
  | some _ =>
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

/-! ### Correctness of the reductions -/

section Proofs

variable {n m q : ℕ} [Fact (Nat.Prime q)]

private theorem gaussInv?_eq (A : Matrix (Fin n) (Fin n) (ZMod q)) :
    gaussInv? A = if A.det = 0 then none else some A⁻¹ := by
  by_cases h : A.det = 0
  · simp [gaussInv?, h]
  · simpa [h] using (gaussInv?_eq_some_inv A).mp h

omit [Fact (Nat.Prime q)] in
private theorem decodeZModVec_encZModVec (v : Fin n → ZMod q) :
    decodeZModVec n q (encZModVec n q v) = v := by
  funext i
  simp only [decodeZModVec, encZModVec, encZMod, Function.Embedding.coeFn_mk, frames_encList,
    List.map_map, Function.comp_def, decodeIntBin_encIntBin, ZMod.intCast_zmod_cast]
  simp

omit [Fact (Nat.Prime q)] in
private theorem decodeMatrix_encMatrix (M : Matrix (Fin n) (Fin m) (ZMod q)) :
    decodeMatrix n m q (encMatrix n m q M) = M := by
  funext i j
  simp only [decodeMatrix, encMatrix, encZMod, Function.Embedding.coeFn_mk, frames_encList,
    List.map_map, Function.comp_def, decodeIntBin_encIntBin, ZMod.intCast_zmod_cast]
  simp

private theorem map_neg_mul_inv (A1 : Matrix (Fin n) (Fin n) (ZMod q)) (hA1 : A1.det ≠ 0) :
    PMF.map (fun A2 : Matrix (Fin m) (Fin n) (ZMod q) => -(A2 * A1⁻¹))
      (PMF.uniformOfFintype _) = PMF.uniformOfFintype _ := by
  have hu := isUnit_iff_ne_zero.mpr hA1
  let e : Matrix (Fin m) (Fin n) (ZMod q) ≃ Matrix (Fin m) (Fin n) (ZMod q) :=
    { toFun := fun A2 => -(A2 * A1⁻¹)
      invFun := fun A2' => -(A2' * A1)
      left_inv := fun A2 => by simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu]
      right_inv := fun A2' => by simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu] }
  exact PMF.uniformOfFintype_map_equiv e

private theorem publicMatrix_tail {k : ℕ} (A : Matrix (Fin k) (Fin n) (ZMod q))
    (s : Fin n → ZMod q) (e : Fin k → ZMod q) :
    (fun i j => publicMatrix A s e i (Fin.succ j)) = A := by
  funext i j
  simp [publicMatrix]

private theorem publicMatrix_head {k : ℕ} (A : Matrix (Fin k) (Fin n) (ZMod q))
    (s : Fin n → ZMod q) (e : Fin k → ZMod q) :
    (fun i => publicMatrix A s e i 0) = A *ᵥ s + e := by
  funext i
  simp [publicMatrix]

private theorem transformAugmented_publicMatrix (A : Matrix (Fin (n + m)) (Fin n) (ZMod q))
    (s : Fin n → ZMod q) (e : Fin (n + m) → ZMod q) (h : (topBlock A).det ≠ 0) :
    transformAugmented (publicMatrix A s e) =
      publicMatrix (-(bottomBlock A * (topBlock A)⁻¹)) (topVec e) (bottomVec e) := by
  have hu : IsUnit (topBlock A).det := isUnit_iff_ne_zero.mpr h
  have key : bottomVec (A *ᵥ s + e) + (-(bottomBlock A * (topBlock A)⁻¹)) *ᵥ topVec (A *ᵥ s + e) =
      (-(bottomBlock A * (topBlock A)⁻¹)) *ᵥ topVec e + bottomVec e := by
    change bottomBlock A *ᵥ s + bottomVec e +
        (-(bottomBlock A * (topBlock A)⁻¹)) *ᵥ (topBlock A *ᵥ s + topVec e) = _
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.neg_mul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hu, Matrix.mul_one, Matrix.neg_mulVec]
    abel
  simp only [transformAugmented, transform, publicMatrix_tail, publicMatrix_head, (gaussInv?_eq_some_inv _).mp h]
  funext i
  simp only [publicMatrix]
  rw [key]
  rfl

private theorem eval_reduceNormalDecision_publicMatrix (adversary : List Bool → ProbComp Bool)
    (A : Matrix (Fin (n + m)) (Fin n) (ZMod q)) (s : Fin n → ZMod q) (e : Fin (n + m) → ZMod q) :
    ProbComp.eval (reduceNormalDecision (n := n) (m := m) (q := q) adversary
        (encMatrix _ _ _ (publicMatrix A s e))) =
      if (topBlock A).det = 0 then PMF.pure false else
        ProbComp.eval (adversary (encMatrix _ _ _
          (publicMatrix (-(bottomBlock A * (topBlock A)⁻¹)) (topVec e) (bottomVec e)))) := by
  unfold reduceNormalDecision
  rw [decodeMatrix_encMatrix]
  simp only [publicMatrix_tail, gaussInv?_eq]
  split_ifs with h
  · simp
  · simp only [transformAugmented_publicMatrix A s e h]

private theorem eval_reduceNormalSearch_publicMatrix
    (adversary : List Bool → ProbComp (List Bool))
    (A : Matrix (Fin (n + m)) (Fin n) (ZMod q)) (s : Fin n → ZMod q) (e : Fin (n + m) → ZMod q)
    (h : (topBlock A).det ≠ 0) :
    ProbComp.eval (reduceNormalSearch (n := n) (m := m) (q := q) adversary
        (encMatrix _ _ _ (publicMatrix A s e))) =
      (ProbComp.eval (adversary (encMatrix _ _ _
        (publicMatrix (-(bottomBlock A * (topBlock A)⁻¹)) (topVec e) (bottomVec e))))).bind
        fun g => PMF.pure (encZModVec n q ((topBlock A)⁻¹ *ᵥ
          (topBlock A *ᵥ s + topVec e - decodeZModVec n q g))) := by
  unfold reduceNormalSearch
  rw [decodeMatrix_encMatrix]
  simp only [publicMatrix_tail, publicMatrix_head, gaussInv?_eq, h, ↓reduceIte, transformAugmented_publicMatrix A s e h,
    pmf_norm]
  rfl

/-- Stack a top block on a bottom block. -/
private def stackRows (A1 : Matrix (Fin n) (Fin n) (ZMod q))
    (A2 : Matrix (Fin m) (Fin n) (ZMod q)) : Matrix (Fin (n + m)) (Fin n) (ZMod q) :=
  Fin.append A1 A2

omit [Fact (Nat.Prime q)] in
private theorem topBlock_stackRows (A1 : Matrix (Fin n) (Fin n) (ZMod q))
    (A2 : Matrix (Fin m) (Fin n) (ZMod q)) : topBlock (stackRows A1 A2) = A1 := by
  funext i j
  exact congrFun (Fin.append_left A1 A2 i) j

omit [Fact (Nat.Prime q)] in
private theorem bottomBlock_stackRows (A1 : Matrix (Fin n) (Fin n) (ZMod q))
    (A2 : Matrix (Fin m) (Fin n) (ZMod q)) : bottomBlock (stackRows A1 A2) = A2 := by
  funext i j
  exact congrFun (Fin.append_right A1 A2 i) j

omit [Fact (Nat.Prime q)] in
private theorem topVec_append (e1 : Fin n → ZMod q) (e2 : Fin m → ZMod q) :
    topVec (Fin.append e1 e2) = e1 := by
  funext i
  simp [topVec]

omit [Fact (Nat.Prime q)] in
private theorem bottomVec_append (e1 : Fin n → ZMod q) (e2 : Fin m → ZMod q) :
    bottomVec (Fin.append e1 e2) = e2 := by
  funext i
  simp [bottomVec]

private theorem uniformOfFintype_matrix_split :
    PMF.uniformOfFintype (Matrix (Fin (n + m)) (Fin n) (ZMod q)) =
      ((PMF.uniformOfFintype (Matrix (Fin n) (Fin n) (ZMod q))).bind fun A1 =>
        (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).map fun A2 => (A1, A2)).map
        fun p => stackRows p.1 p.2 := by
  let E : Matrix (Fin n) (Fin n) (ZMod q) × Matrix (Fin m) (Fin n) (ZMod q) ≃
      Matrix (Fin (n + m)) (Fin n) (ZMod q) := Fin.appendEquiv n m
  rw [PMF.uniformOfFintype_prod]
  exact (PMF.uniformOfFintype_map_equiv E).symm

omit [Fact (Nat.Prime q)] in
private theorem pi_fin_add {γ : Type*} [Finite γ] (p : PMF γ) :
    PMF.pi (fun _ : Fin (n + m) => p) =
      ((PMF.pi fun _ : Fin n => p).bind fun e1 =>
        (PMF.pi fun _ : Fin m => p).map fun e2 => (e1, e2)).map
        fun x => Fin.append x.1 x.2 := by
  ext outcome
  rw [show (fun x : (Fin n → γ) × (Fin m → γ) => Fin.append x.1 x.2) =
      Fin.appendEquiv n m from rfl, PMF.map_equiv_apply, PMF.bind_map_prodMk_apply]
  simp only [PMF.pi_apply, Fin.appendEquiv_symm_apply]
  exact Fin.prod_univ_add (fun i => p (outcome i))

/-- The common shape of both reductions: drawing a full sample and giving up on a singular top
block is drawing the top block first, then an error-secret sample when the block is invertible. -/
private theorem bind_split {β : Type*} (noise : PMF (ZMod q)) (μ : PMF β)
    (K : Matrix (Fin m) (Fin n) (ZMod q) → (Fin n → ZMod q) → (Fin m → ZMod q) → PMF Bool) :
    (μ.bind fun _ => (PMF.uniformOfFintype (Matrix (Fin (n + m)) (Fin n) (ZMod q))).bind fun A =>
      (PMF.pi fun _ : Fin (n + m) => noise).bind fun e =>
        if (topBlock A).det = 0 then PMF.pure false else
          K (-(bottomBlock A * (topBlock A)⁻¹)) (topVec e) (bottomVec e)) =
    (PMF.uniformOfFintype (Matrix (Fin n) (Fin n) (ZMod q))).bind fun A1 =>
      if A1.det = 0 then PMF.pure false else
        (PMF.pi fun _ : Fin n => noise).bind fun e1 =>
          (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A' =>
            (PMF.pi fun _ : Fin m => noise).bind fun e2 => K A' e1 e2 := by
  rw [PMF.bind_const, uniformOfFintype_matrix_split (n := n) (m := m) (q := q),
    pi_fin_add (n := n) (m := m)]
  simp only [PMF.bind_map, PMF.bind_bind, Function.comp_def, topBlock_stackRows,
    bottomBlock_stackRows, topVec_append, bottomVec_append]
  congr 1
  funext A1
  split_ifs with h
  · simp only [PMF.bind_const]
  · conv_rhs => rw [PMF.bind_comm (PMF.pi fun _ : Fin n => noise)]
    conv_rhs => rw [← map_neg_mul_inv (m := m) A1 h]
    rw [PMF.bind_map]
    rfl

omit [Fact (Nat.Prime q)] in
private theorem toReal_bind_ite_apply_true {α : Type*} (μ : PMF α) (P : α → Prop)
    [DecidablePred P] (g : PMF Bool) :
    ((μ.bind fun a => if P a then PMF.pure false else g) true).toReal =
      (1 - (μ.toOuterMeasure {a | P a}).toReal) * (g true).toReal := by
  have hsplit : (μ.bind fun a => if P a then PMF.pure false else g) true =
      μ.toOuterMeasure {a | P a}ᶜ * g true := by
    rw [PMF.bind_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
    congr 1
    funext a
    by_cases h : P a <;> simp [h]
  have hcompl := PMF.toOuterMeasure_toReal_add_compl μ {a | P a}
  rw [hsplit, ENNReal.toReal_mul,
    show (μ.toOuterMeasure {a | P a}ᶜ).toReal = 1 - (μ.toOuterMeasure {a | P a}).toReal by
      linarith]

/-- On real samples, the decision reduction runs the adversary on an error-secret sample exactly
when the top block is invertible. -/
private theorem distinguishingGame_reduceNormalDecision (noise : PMF (ZMod q))
    (adversary : List Bool → ProbComp Bool) :
    distinguishingGame
        (realEnsemble (fun _ => n) (fun _ => n + m) (fun _ => q) (fun _ => noise) 0)
        (reduceNormalDecision (n := n) (m := m) (q := q) adversary) =
      (PMF.uniformOfFintype (Matrix (Fin n) (Fin n) (ZMod q))).bind fun A1 =>
        if A1.det = 0 then PMF.pure false else
          distinguishingGame
            (realEnsembleErrorSecret (fun _ => n) (fun _ => m) (fun _ => q) (fun _ => noise) 0)
            adversary := by
  have herr : distinguishingGame
      (realEnsembleErrorSecret (fun _ => n) (fun _ => m) (fun _ => q) (fun _ => noise) 0)
        adversary =
      (PMF.pi fun _ : Fin n => noise).bind fun e1 =>
        (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A' =>
          (PMF.pi fun _ : Fin m => noise).bind fun e2 =>
            ProbComp.eval (adversary (encMatrix _ _ _ (publicMatrix A' e1 e2))) := by
    simp only [distinguishingGame, realEnsembleErrorSecret, publicMatrixLawErrorSecret, pmf_norm]
  rw [herr, ← bind_split noise (PMF.uniformOfFintype (Fin n → ZMod q))
    (fun A' e1 e2 => ProbComp.eval (adversary (encMatrix _ _ _ (publicMatrix A' e1 e2))))]
  simp only [distinguishingGame, realEnsemble, publicMatrixLaw, pmf_norm,
    eval_reduceNormalDecision_publicMatrix]

private theorem toReal_distinguishingGame_reduceNormalDecision (noise : PMF (ZMod q))
    (adversary : List Bool → ProbComp Bool) :
    (distinguishingGame
        (realEnsemble (fun _ => n) (fun _ => n + m) (fun _ => q) (fun _ => noise) 0)
        (reduceNormalDecision (n := n) (m := m) (q := q) adversary) true).toReal =
      (1 - ((PMF.uniformOfFintype (Matrix (Fin n) (Fin n) (ZMod q))).toOuterMeasure
        {A | A.det = 0}).toReal) *
        (distinguishingGame
          (realEnsembleErrorSecret (fun _ => n) (fun _ => m) (fun _ => q) (fun _ => noise) 0)
          adversary true).toReal := by
  rw [distinguishingGame_reduceNormalDecision, toReal_bind_ite_apply_true]

/-- With a uniform error the public matrix `[A * s + e | A]` is uniform, whatever the secret's
law. -/
private theorem bind_publicMatrix_uniform {k : ℕ} (μ : PMF (Fin n → ZMod q)) :
    (μ.bind fun s => (PMF.uniformOfFintype (Matrix (Fin k) (Fin n) (ZMod q))).bind fun A =>
      (PMF.pi fun _ : Fin k => PMF.uniformOfFintype (ZMod q)).bind fun e =>
        PMF.pure (publicMatrix A s e)) =
      PMF.uniformOfFintype (Matrix (Fin k) (Fin (n + 1)) (ZMod q)) := by
  have h (s : Fin n → ZMod q) :
      ((PMF.uniformOfFintype (Matrix (Fin k) (Fin n) (ZMod q))).bind fun A =>
        (PMF.uniformOfFintype (Fin k → ZMod q)).bind fun e => PMF.pure (publicMatrix A s e)) =
        PMF.uniformOfFintype (Matrix (Fin k) (Fin (n + 1)) (ZMod q)) := by
    let E : Matrix (Fin k) (Fin n) (ZMod q) × (Fin k → ZMod q) ≃
        Matrix (Fin k) (Fin (n + 1)) (ZMod q) :=
      { toFun := fun x => publicMatrix x.1 s x.2
        invFun := fun M =>
          (fun i j => M i j.succ, fun i => M i 0 - ((fun i j => M i j.succ) *ᵥ s) i)
        left_inv := fun x => by
          ext <;> simp [publicMatrix]
        right_inv := fun M => by
          funext i j
          refine Fin.cases ?_ (fun j => ?_) j <;> simp [publicMatrix] }
    rw [← PMF.uniformOfFintype_map_equiv E, ← PMF.uniformOfFintype_prod]
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    simp only [PMF.map, Function.comp_def]
    rfl
  rw [PMF.pi_uniformOfFintype]
  simp only [h, PMF.bind_const]

private theorem uniformEnsemble_eq_realEnsemble {k : ℕ} :
    uniformEnsemble (fun _ => n) (fun _ => k) (fun _ => q) 0 =
      realEnsemble (fun _ => n) (fun _ => k) (fun _ => q)
        (fun _ => PMF.uniformOfFintype (ZMod q)) 0 := by
  unfold uniformEnsemble realEnsemble
  congr 1
  simp only [publicMatrixLaw, pmf_norm]
  exact (bind_publicMatrix_uniform _).symm

private theorem uniformEnsemble_eq_realEnsembleErrorSecret {k : ℕ} :
    uniformEnsemble (fun _ => n) (fun _ => k) (fun _ => q) 0 =
      realEnsembleErrorSecret (fun _ => n) (fun _ => k) (fun _ => q)
        (fun _ => PMF.uniformOfFintype (ZMod q)) 0 := by
  unfold uniformEnsemble realEnsembleErrorSecret
  congr 1
  simp only [publicMatrixLawErrorSecret, pmf_norm]
  exact (bind_publicMatrix_uniform _).symm

/-- On real samples with an invertible top block, the search reduction recovers the secret
whenever the adversary names the error-secret sample's secret. -/
private theorem le_searchGame_reduceNormalSearch (noise : PMF (ZMod q))
    (adversary : List Bool → ProbComp (List Bool)) :
    ((PMF.uniformOfFintype (Matrix (Fin n) (Fin n) (ZMod q))).bind fun A1 =>
        if A1.det = 0 then PMF.pure false else searchGameErrorSecret n m q noise adversary) true ≤
      searchGame n (n + m) q noise (reduceNormalSearch (n := n) (m := m) (q := q) adversary)
        true := by
  have herr : searchGameErrorSecret n m q noise adversary =
      (PMF.pi fun _ : Fin n => noise).bind fun e1 =>
        (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A' =>
          (PMF.pi fun _ : Fin m => noise).bind fun e2 =>
            (ProbComp.eval (adversary (encMatrix _ _ _ (publicMatrix A' e1 e2)))).bind fun g =>
              PMF.pure (decide (g = encZModVec n q e1)) := by
    simp only [searchGameErrorSecret, pmf_norm]
  rw [herr, ← bind_split noise (PMF.uniformOfFintype (Fin n → ZMod q))
    (fun A' e1 e2 => (ProbComp.eval (adversary (encMatrix _ _ _ (publicMatrix A' e1 e2)))).bind
      fun g => PMF.pure (decide (g = encZModVec n q e1)))]
  simp only [searchGame, pmf_norm]
  refine PMF.bind_apply_mono_on_support _ _ fun s _ => ?_
  refine PMF.bind_apply_mono_on_support _ _ fun A _ => ?_
  refine PMF.bind_apply_mono_on_support _ _ fun e _ => ?_
  split_ifs with h
  · simp
  · rw [eval_reduceNormalSearch_publicMatrix adversary A s e h, PMF.bind_bind]
    refine PMF.bind_apply_mono_on_support _ _ fun g _ => ?_
    simp only [PMF.pure_bind]
    by_cases hg : g = encZModVec n q (topVec e)
    · have hs : (topBlock A)⁻¹ *ᵥ (topBlock A *ᵥ s + topVec e - decodeZModVec n q g) = s := by
        rw [hg, decodeZModVec_encZModVec, add_sub_cancel_right, Matrix.mulVec_mulVec,
          Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h), Matrix.one_mulVec]
      simp only [hs, decide_true, PMF.pure_apply]
      split_ifs <;> simp
    · simp [hg]

omit [Fact (Nat.Prime q)] in
private theorem coe_toReal_game_le_one (g : Game) : (g true).toReal ≤ 1 := by
  simpa using NNReal.coe_le_coe.mpr (Game.succProbability_le_one g)

end Proofs

/-- Decision LWE with a secret drawn from the error distribution reduces to decision LWE with a
uniform secret, losing the probability that a uniform `n × n` matrix is singular. -/
theorem decisionNormalForm {n m q : ℕ} [Fact (Nat.Prime q)]
    {noise : PMF (ZMod q)}
    (adversary : List Bool → ProbComp Bool) :
    Game.advantage
      (distinguishingGame
        (realEnsembleErrorSecret (fun _ => n) (fun _ => m) (fun _ => q) (fun _ => noise) 0)
        adversary)
      (distinguishingGame (uniformEnsemble (fun _ => n) (fun _ => m) (fun _ => q) 0) adversary)
    ≤ Game.advantage
      (distinguishingGame
        (realEnsemble (fun _ => n) (fun _ => n + m) (fun _ => q) (fun _ => noise) 0)
        (reduceNormalDecision (n := n) (m := m) (q := q) adversary))
      (distinguishingGame (uniformEnsemble (fun _ => n) (fun _ => n + m) (fun _ => q) 0)
        (reduceNormalDecision (n := n) (m := m) (q := q) adversary)) +
      ((PMF.uniformOfFintype (Matrix (Fin n) (Fin n) (ZMod q))).toOuterMeasure
        {A | A.det = 0}).toReal := by
  have hR := toReal_distinguishingGame_reduceNormalDecision (n := n) (m := m) noise adversary
  have hU := toReal_distinguishingGame_reduceNormalDecision (n := n) (m := m)
    (PMF.uniformOfFintype (ZMod q)) adversary
  rw [← uniformEnsemble_eq_realEnsemble, ← uniformEnsemble_eq_realEnsembleErrorSecret] at hU
  have hδ0 : 0 ≤ ((PMF.uniformOfFintype (Matrix (Fin n) (Fin n) (ZMod q))).toOuterMeasure
      {A | A.det = 0}).toReal := ENNReal.toReal_nonneg
  have hδ1 := PMF.toOuterMeasure_toReal_le_one
    (PMF.uniformOfFintype (Matrix (Fin n) (Fin n) (ZMod q))) {A | A.det = 0}
  have hR1 := coe_toReal_game_le_one (distinguishingGame
    (realEnsembleErrorSecret (fun _ => n) (fun _ => m) (fun _ => q) (fun _ => noise) 0) adversary)
  have hU1 := coe_toReal_game_le_one
    (distinguishingGame (uniformEnsemble (fun _ => n) (fun _ => m) (fun _ => q) 0) adversary)
  have hR0 : 0 ≤ (distinguishingGame
    (realEnsembleErrorSecret (fun _ => n) (fun _ => m) (fun _ => q) (fun _ => noise) 0)
      adversary true).toReal := ENNReal.toReal_nonneg
  have hU0 : 0 ≤ (distinguishingGame (uniformEnsemble (fun _ => n) (fun _ => m) (fun _ => q) 0)
    adversary true).toReal := ENNReal.toReal_nonneg
  simp only [Game.coe_advantage, Game.coe_succProbability]
  rw [hR, hU]
  generalize ((PMF.uniformOfFintype (Matrix (Fin n) (Fin n) (ZMod q))).toOuterMeasure
    {A | A.det = 0}).toReal = δ at hδ0 hδ1 ⊢
  generalize (distinguishingGame
    (realEnsembleErrorSecret (fun _ => n) (fun _ => m) (fun _ => q) (fun _ => noise) 0)
      adversary true).toReal = r at hR0 hR1 ⊢
  generalize (distinguishingGame (uniformEnsemble (fun _ => n) (fun _ => m) (fun _ => q) 0)
    adversary true).toReal = u at hU0 hU1 ⊢
  have habs : |r - u| ≤ 1 := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  rw [← mul_sub, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - δ)]
  nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr habs)]

/-- Search LWE with a secret drawn from the error distribution reduces to search LWE with a
uniform secret, losing the probability that a uniform `n × n` matrix is singular. -/
theorem searchNormalForm {n m q : ℕ} [Fact (Nat.Prime q)]
    {noise : PMF (ZMod q)}
    (adversary : List Bool → ProbComp (List Bool)) :
    Game.succProbability (searchGameErrorSecret n m q noise adversary)
    ≤ Game.succProbability (searchGame n (n + m) q noise
        (reduceNormalSearch (n := n) (m := m) (q := q) adversary)) +
      ((PMF.uniformOfFintype (Matrix (Fin n) (Fin n) (ZMod q))).toOuterMeasure
        {A | A.det = 0}).toReal := by
  have hS := ENNReal.toReal_mono (PMF.apply_ne_top _ _)
    (le_searchGame_reduceNormalSearch (n := n) (m := m) noise adversary)
  rw [toReal_bind_ite_apply_true] at hS
  have hδ0 : 0 ≤ ((PMF.uniformOfFintype (Matrix (Fin n) (Fin n) (ZMod q))).toOuterMeasure
      {A | A.det = 0}).toReal := ENNReal.toReal_nonneg
  have hS1 := coe_toReal_game_le_one (searchGameErrorSecret n m q noise adversary)
  simp only [Game.coe_succProbability]
  nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr hS1)]

end Cslib.Crypto.PrimeLWE
