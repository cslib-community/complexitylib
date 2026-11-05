/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Probability.LinearCombination
public import Complexity.Computability.Interactive.Plain
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Matrix.Mul
import Complexity.Probability.PMF
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Uniform
import Complexity.Probability.Uniform

/-!
# Polynomial commitment schemes, evaluation batching, and the Ligero matrix-code IOP core

A polynomial commitment scheme (`Cslib.Crypto.Protocols.PolyCommitScheme`) commits to a polynomial
from an admissible class `ValidPoly` and opens evaluations `eval p z = y` with short proofs
[Kate, Zaverucha and Goldberg][KateZaveruchaGoldberg2010]. Its core security properties are
evaluation completeness (`PolyCommitScheme.EvalComplete`), commitment binding
(`PolyCommitScheme.CommitmentBinding`, `PolyCommitScheme.CommitmentBindingExtract`), and evaluation
binding at each query point (`PolyCommitScheme.EvaluationBinding`,
`PolyCommitScheme.EvaluationBindingExtract`).

When a prover claims `k` evaluations `eval (p i) z = y i` at a point `z`, random-linear-combination
batching (`Cslib.Crypto.Protocols.batchEvalReduction`) samples a uniform challenge vector
`r : Fin k → F` and reduces the `k` claims to the single linear combination
`∑ i, r i * eval (p i) z = ∑ i, r i * y i` [Chiesa and Yogev][ChiesaYogev2024]. When any single
claimed evaluation is false (`eval (p i₀) z ≠ y i₀`), the discrepancy
`∑ i, r i * (eval (p i) z - y i)` is a surjective additive homomorphism of `r : Fin k → F` onto `F`,
so it is uniformly distributed on `F` (`uniformOfFintype_map_linearComb`) and vanishes with
probability *exactly* `1 / |F|` (`toOuterMeasure_batchEval_sub_eq_zero`,
`toOuterMeasure_batchEval_eq`, `batchEvalReduction_sound`).

In the Ligero matrix-code interactive oracle proof [Ames, Hazay, Ishai and
Venkitasubramaniam][AmesHazayIshaiVenkitasubramaniam2017], [Chiesa and Yogev][ChiesaYogev2024], a
witness vector is reshaped into an `m × l` matrix `U : Matrix (Fin m) (Fin l) F` and encoded
row-wise by a linear generator matrix `G : Matrix (Fin l) (Fin n) F` into `M = U * G`. To check
proximity and row-wise consistency, the verifier sends a random challenge `r : Fin m → F`, the
prover replies with the row combination `v = ligeroRowComb r U = r ᵥ* U : Fin l → F`, and the
verifier checks `(v ᵥ* G) j = (r ᵥ* M) j` at queried columns `j` (`ligeroColumnCheck`,
`ligeroEvalCheck`). Associativity of vector-matrix multiplication (`Matrix.vecMul_vecMul`) gives
perfect completeness (`ligeroRowComb_mul`), while any row `i₀` where `M i₀ j ≠ ((U i₀) ᵥ* G) j` is
caught at column `j` with probability `1 - 1 / |F|` (`toOuterMeasure_ligeroRowComb_eq`,
`LigeroMatrixIOP.columnReduction_sound`).

## Main definitions

* `Cslib.Crypto.Protocols.PolyCommitScheme`: syntax of a polynomial commitment scheme.
* `Cslib.Crypto.Protocols.PolyCommitScheme.EvalComplete`,
  `Cslib.Crypto.Protocols.PolyCommitScheme.OpenValueCorrect`,
  `Cslib.Crypto.Protocols.PolyCommitScheme.CommitmentBinding`,
  `Cslib.Crypto.Protocols.PolyCommitScheme.CommitmentBindingExtract`,
  `Cslib.Crypto.Protocols.PolyCommitScheme.EvaluationBinding`,
  `Cslib.Crypto.Protocols.PolyCommitScheme.EvaluationBindingExtract`: completeness and binding
  predicates.
* `Cslib.Crypto.Protocols.PolyCommitScheme.direct`: canonical degree-bounded polynomial commitment.
* `Cslib.Crypto.Protocols.batchEvalReduction`: public-coin interactive reduction batching `k`
  evaluation claims into a single random linear combination.
* `Cslib.Crypto.Protocols.ligeroRowComb`, `Cslib.Crypto.Protocols.ligeroEval`,
  `Cslib.Crypto.Protocols.ligeroColumnCheck`, `Cslib.Crypto.Protocols.ligeroEvalCheck`,
  `Cslib.Crypto.Protocols.LigeroMatrixIOP`: Ligero matrix-code operations, column/evaluation
  checks, and interactive reduction.

## Main results

* `Cslib.Crypto.Protocols.PolyCommitScheme.EvaluationBinding.eq_eval_of_verifyEval`,
  `Cslib.Crypto.Protocols.PolyCommitScheme.EvaluationBinding.commitmentBinding_of_eval_inj`:
  evaluation binding forces any valid opening of an honest commitment to equal `eval p z` and
  implies commitment binding when evaluations separate valid polynomials.
* `Cslib.Probability.uniformOfFintype_map_linearComb`,
  `Cslib.Probability.toOuterMeasure_uniform_linearComb_eq_zero`: a random linear combination
  of a nonzero vector over a finite field is uniform and vanishes with exact probability `1 / |F|`.
* `Cslib.Crypto.Protocols.batchEvalReduction_complete`,
  `Cslib.Crypto.Protocols.batchEvalReduction_rbrSound`,
  `Cslib.Crypto.Protocols.batchEvalReduction_sound`: completeness and `1 / |F|` soundness of random
  linear combination evaluation batching.
* `Cslib.Crypto.Protocols.ligeroRowComb_mul`,
  `Cslib.Crypto.Protocols.toOuterMeasure_ligeroRowComb_eq`,
  `Cslib.Crypto.Protocols.LigeroMatrixIOP.columnReduction_complete`,
  `Cslib.Crypto.Protocols.LigeroMatrixIOP.columnReduction_sound`: Ligero matrix-code completeness
  and row-consistency soundness.

## References

* [S. Ames, C. Hazay, Y. Ishai, M. Venkitasubramaniam, *Ligero: Lightweight Sublinear Arguments
  Without a Trusted Setup*][AmesHazayIshaiVenkitasubramaniam2017]
* [A. Chiesa, E. Yogev, *Building Cryptographic Proofs from Hash Functions*][ChiesaYogev2024]
* [A. Kate, G. M. Zaverucha, I. Goldberg, *Constant-Size Commitments to Polynomials and Their
  Applications*][KateZaveruchaGoldberg2010]
-/

public section

namespace Cslib.Crypto.Protocols

open Cslib.Interactive Cslib.Interactive.Spec Cslib.Probability
open scoped BigOperators ENNReal Matrix

universe u

/-! ### Polynomial commitment scheme interface -/

/-- A polynomial commitment scheme over polynomial representation `Poly`, commitment randomness
`Randomness`, evaluation point type `Point`, value type `F`, commitment type `Commit`, and opening
proof type `Proof` [Kate, Zaverucha and Goldberg][KateZaveruchaGoldberg2010]. -/
structure PolyCommitScheme (Poly Randomness Point F Commit Proof : Type u) where
  /-- Evaluate a polynomial at a query point. -/
  eval : Poly → Point → F
  /-- Admissibility / degree-bound predicate on committed polynomials. -/
  ValidPoly : Poly → Prop
  /-- Commit to a polynomial using explicit randomness. -/
  commit : Poly → Randomness → Commit
  /-- Open a committed polynomial at a point, returning the claimed value and an opening proof. -/
  openEval : Poly → Randomness → Point → F × Proof
  /-- Deterministic verification of a claimed evaluation `(y, π)` at point `z` against `c`. -/
  verifyEval : Commit → Point → F → Proof → Bool

namespace PolyCommitScheme

variable {Poly Randomness Point F Commit Proof : Type u}
  (S : PolyCommitScheme Poly Randomness Point F Commit Proof)

/-- The proposition that the verifier accepts opening `(y, π)` for commitment `c` at point `z`. -/
@[expose] def AcceptsEval (c : Commit) (z : Point) (y : F) (π : Proof) : Prop :=
  S.verifyEval c z y π = true

instance (c : Commit) (z : Point) (y : F) (π : Proof) : Decidable (S.AcceptsEval c z y π) :=
  inferInstanceAs (Decidable (S.verifyEval c z y π = true))

/-- Evaluation completeness: for every valid polynomial `p`, commitment randomness `r`, and query
point `z`, the honest opening proof `(openEval p r z).2` is accepted for the true evaluation
`eval p z` on `commit p r`. -/
@[expose] def EvalComplete : Prop :=
  ∀ p r z, S.ValidPoly p →
    S.verifyEval (S.commit p r) z (S.eval p z) (S.openEval p r z).2 = true

/-- Honest opening value correctness: the value component of `openEval p r z` is `eval p z`. -/
@[expose] def OpenValueCorrect : Prop :=
  ∀ p r z, S.ValidPoly p → (S.openEval p r z).1 = S.eval p z

/-- Commitment binding: no two distinct valid polynomials produce the same commitment. -/
@[expose] def CommitmentBinding : Prop :=
  ∀ p₁ r₁ p₂ r₂, S.ValidPoly p₁ → S.ValidPoly p₂ →
    S.commit p₁ r₁ = S.commit p₂ r₂ → p₁ = p₂

/-- Witness-extracting commitment binding: from any two distinct valid polynomials with the same
commitment, `extract` recovers a witness satisfying `Collision` (such as a hash collision or
discrete-logarithm relation). -/
@[expose] def CommitmentBindingExtract {Witness : Type*} (Collision : Witness → Prop)
    (extract : Poly → Randomness → Poly → Randomness → Witness) : Prop :=
  ∀ p₁ r₁ p₂ r₂, S.ValidPoly p₁ → S.ValidPoly p₂ →
    p₁ ≠ p₂ → S.commit p₁ r₁ = S.commit p₂ r₂ → Collision (extract p₁ r₁ p₂ r₂)

/-- Evaluation binding: at any query point `z`, no commitment `c` has two accepting openings
`(y₁, π₁)` and `(y₂, π₂)` for distinct values `y₁ ≠ y₂`. -/
@[expose] def EvaluationBinding : Prop :=
  ∀ c z y₁ π₁ y₂ π₂,
    S.verifyEval c z y₁ π₁ = true → S.verifyEval c z y₂ π₂ = true → y₁ = y₂

/-- Witness-extracting evaluation binding: from any two accepting openings `(y₁, π₁)` and `(y₂, π₂)`
of the same commitment `c` at point `z` with `y₁ ≠ y₂`, `extract` recovers a witness satisfying
`Collision`. -/
@[expose] def EvaluationBindingExtract {Witness : Type*} (Collision : Witness → Prop)
    (extract : Commit → Point → F → Proof → F → Proof → Witness) : Prop :=
  ∀ c z y₁ π₁ y₂ π₂, y₁ ≠ y₂ →
    S.verifyEval c z y₁ π₁ = true → S.verifyEval c z y₂ π₂ = true →
    Collision (extract c z y₁ π₁ y₂ π₂)

variable {S}

/-- Under `EvalComplete` and `OpenValueCorrect`, both components of `openEval p r z` verify. -/
theorem EvalComplete.verifyEval_openEval (hcomp : S.EvalComplete) (hval : S.OpenValueCorrect)
    {p : Poly} (hp : S.ValidPoly p) (r : Randomness) (z : Point) :
    S.verifyEval (S.commit p r) z (S.openEval p r z).1 (S.openEval p r z).2 = true := by
  rw [hval p r z hp]
  exact hcomp p r z hp

/-- Under `EvalComplete` and `EvaluationBinding`, any accepting opening `(y, π)` for an honest
commitment `commit p r` to a valid polynomial `p` must satisfy `y = eval p z`. -/
theorem EvaluationBinding.eq_eval_of_verifyEval (hbind : S.EvaluationBinding)
    (hcomp : S.EvalComplete) {p : Poly} (hp : S.ValidPoly p) (r : Randomness) (z : Point)
    {y : F} {π : Proof} (hver : S.verifyEval (S.commit p r) z y π = true) :
    y = S.eval p z :=
  hbind (S.commit p r) z y π (S.eval p z) (S.openEval p r z).2 hver (hcomp p r z hp)

/-- If evaluation completeness and evaluation binding hold, and valid polynomials are determined by
their evaluations, then commitment binding holds. -/
theorem EvaluationBinding.commitmentBinding_of_eval_inj (hbind : S.EvaluationBinding)
    (hcomp : S.EvalComplete)
    (hinj : ∀ p₁ p₂, S.ValidPoly p₁ → S.ValidPoly p₂ →
      (∀ z, S.eval p₁ z = S.eval p₂ z) → p₁ = p₂) :
    S.CommitmentBinding := by
  intro p₁ r₁ p₂ r₂ hp₁ hp₂ hcomm
  refine hinj p₁ p₂ hp₁ hp₂ fun z => ?_
  have h₁ := hcomp p₁ r₁ z hp₁
  rw [hcomm] at h₁
  exact hbind.eq_eval_of_verifyEval hcomp hp₂ r₂ z h₁

/-- Strict commitment binding implies witness-extracting commitment binding for any relation. -/
theorem CommitmentBinding.commitmentBindingExtract (hbind : S.CommitmentBinding)
    {Witness : Type*} (Collision : Witness → Prop)
    (extract : Poly → Randomness → Poly → Randomness → Witness) :
    S.CommitmentBindingExtract Collision extract :=
  fun p₁ r₁ p₂ r₂ hp₁ hp₂ hne hcomm => (hne (hbind p₁ r₁ p₂ r₂ hp₁ hp₂ hcomm)).elim

/-- Strict evaluation binding implies witness-extracting evaluation binding for any relation. -/
theorem EvaluationBinding.evaluationBindingExtract (hbind : S.EvaluationBinding)
    {Witness : Type*} (Collision : Witness → Prop)
    (extract : Commit → Point → F → Proof → F → Proof → Witness) :
    S.EvaluationBindingExtract Collision extract :=
  fun c z y₁ π₁ y₂ π₂ hne hv₁ hv₂ => (hne (hbind c z y₁ π₁ y₂ π₂ hv₁ hv₂)).elim

/-- The canonical transparent degree-bounded polynomial commitment scheme over `Polynomial F`, in
which the commitment is the polynomial itself and verification checks the degree bound and direct
evaluation. -/
@[expose] def direct (F : Type) [CommSemiring F] [DecidableEq F] (d : ℕ) :
    PolyCommitScheme (Polynomial F) Unit F F (Polynomial F) Unit where
  eval p z := p.eval z
  ValidPoly p := p.natDegree ≤ d
  commit p _ := p
  openEval p _ z := (p.eval z, ())
  verifyEval c z y _ := decide (c.natDegree ≤ d ∧ c.eval z = y)

theorem direct_evalComplete (F : Type) [CommSemiring F] [DecidableEq F] (d : ℕ) :
    (direct F d).EvalComplete := by
  intro p _ z hp
  simp only [direct, decide_eq_true_eq, and_true]
  exact hp

theorem direct_openValueCorrect (F : Type) [CommSemiring F] [DecidableEq F] (d : ℕ) :
    (direct F d).OpenValueCorrect := by
  intro _ _ _ _
  rfl

theorem direct_commitmentBinding (F : Type) [CommSemiring F] [DecidableEq F] (d : ℕ) :
    (direct F d).CommitmentBinding := by
  intro _ _ _ _ _ _ h
  exact h

theorem direct_evaluationBinding (F : Type) [CommSemiring F] [DecidableEq F] (d : ℕ) :
    (direct F d).EvaluationBinding := by
  intro c z y₁ _ y₂ _ hv₁ hv₂
  simp only [direct, decide_eq_true_eq] at hv₁ hv₂
  exact hv₁.2.symm.trans hv₂.2

end PolyCommitScheme

/-! ### Random linear combination evaluation-batching reduction -/

section BatchEval

variable {Poly Point F : Type} {k : ℕ}

/-- The single verifier-challenge round for batching `k` polynomial evaluation claims. -/
abbrev batchEvalSpec (k : ℕ) (F : Type) : Spec := [.verifier (Fin k → F)]

/-- A batched evaluation claim: the challenge vector `r : Fin k → F` and the claimed linear
combination `v : F`. -/
abbrev BatchEvalClaim (k : ℕ) (F : Type) : Type := (Fin k → F) × F

/-- The input relation for batching `k` evaluation claims at `z`: all `k` claimed values `y i` match
`eval (p i) z`. -/
@[expose] def batchEvalRelIn (eval : Poly → Point → F) (p : Fin k → Poly) (z : Point) :
    (Fin k → F) → Unit → Prop :=
  fun y _ => ∀ i, eval (p i) z = y i

/-- The output relation after sampling the batching weights `r : Fin k → F`: the single linear
combination `∑ i, r i * eval (p i) z` equals the batched value. -/
@[expose] def batchEvalRelOut [Semiring F] (eval : Poly → Point → F) (p : Fin k → Poly)
    (z : Point) : BatchEvalClaim k F → Unit → Prop :=
  fun c _ => (∑ i, c.1 i * eval (p i) z) = c.2

/-- If `eval (p i₀) z ≠ y i₀` for some `i₀ : Fin k`, then over uniform `r : Fin k → F`, the
probability that `∑ i, r i * (eval (p i) z - y i) = 0` is *exactly* `1 / |F|`. -/
theorem toOuterMeasure_batchEval_sub_eq_zero [Field F] [Fintype F] (eval : Poly → Point → F)
    (p : Fin k → Poly) (z : Point) (y : Fin k → F) {i₀ : Fin k} (hne : eval (p i₀) z ≠ y i₀) :
    (PMF.uniformOfFintype (Fin k → F)).toOuterMeasure
        {r | ∑ i, r i * (eval (p i) z - y i) = 0} =
      1 / (Fintype.card F : ℝ≥0∞) :=
  toOuterMeasure_uniform_linearComb_eq_zero (sub_ne_zero.mpr hne)

/-- If `eval (p i₀) z ≠ y i₀` for some `i₀ : Fin k`, then over uniform `r : Fin k → F`, the
probability that the batched linear combinations agree (`∑ i, r i * eval (p i) z = ∑ i, r i * y i`)
is *exactly* `1 / |F|`. -/
theorem toOuterMeasure_batchEval_eq [Field F] [Fintype F] (eval : Poly → Point → F)
    (p : Fin k → Poly) (z : Point) (y : Fin k → F) {i₀ : Fin k} (hne : eval (p i₀) z ≠ y i₀) :
    (PMF.uniformOfFintype (Fin k → F)).toOuterMeasure
        {r | ∑ i, r i * eval (p i) z = ∑ i, r i * y i} =
      1 / (Fintype.card F : ℝ≥0∞) := by
  have hset : {r : Fin k → F | ∑ i, r i * eval (p i) z = ∑ i, r i * y i} =
      {r : Fin k → F | ∑ i, r i * (eval (p i) z - y i) = 0} := by
    ext r
    simp only [Set.mem_ofPred_eq, mul_sub, Finset.sum_sub_distrib, sub_eq_zero]
  rw [hset]
  exact toOuterMeasure_batchEval_sub_eq_zero eval p z y hne

/-- **Random linear combination evaluation-batching reduction** [Chiesa and Yogev][ChiesaYogev2024]:
given a vector of `k` claimed evaluations `y : Fin k → F` for `(p i)` at `z`, the verifier samples
a uniform challenge vector `r : Fin k → F` and outputs the single linear-combination claim
`(r, ∑ i, r i * y i)`. -/
noncomputable def batchEvalReduction [Field F] [Fintype F] (_eval : Poly → Point → F)
    (_p : Fin k → Poly) (_z : Point) :
    Reduction OracleSpec.empty OracleSpec.empty (batchEvalSpec k F)
      (Fin k → F) Unit (BatchEvalClaim k F) Unit where
  prover y _ :=
    pure (show (Fin k → F) → ProbOracleComp OracleSpec.empty (BatchEvalClaim k F × Unit) from
      fun r => pure ((r, ∑ i, r i * y i), ()))
  verifier :=
    { samplers := (ProbComp.uniform (Fin k → F), ())
      decide := fun y c => pure (some (c.1, ∑ i, c.1 i * y i)) }

theorem batchEvalReduction_outputOn [Field F] [Fintype F] (eval : Poly → Point → F)
    (p : Fin k → Poly) (z : Point) (y : Fin k → F) (τ : Transcript (batchEvalSpec k F)) :
    (batchEvalReduction eval p z).verifier.outputOn y τ = some (τ.1, ∑ i, τ.1 i * y i) := by
  rfl

/-- **Completeness of random linear combination batching**: when all `k` claimed evaluations are
correct (`∀ i, eval (p i) z = y i`), the batched claim holds with probability `1` (error `0`). -/
theorem batchEvalReduction_complete [Field F] [Fintype F] (eval : Poly → Point → F)
    (p : Fin k → Poly) (z : Point) :
    (batchEvalReduction eval p z).Complete World.plain
      (batchEvalRelIn eval p z) (batchEvalRelOut eval p z) 0 := by
  intro y _ hy
  rw [Reduction.run, World.plain_eval_execute, PMF.toOuterMeasure_map_apply]
  simp only [batchEvalReduction, runStrategy, plainLaw_bind, plainLaw_pure, plainLaw_sample,
    PMF.pure_bind]
  rw [PMF.toOuterMeasure_bind_apply]
  refine Probability.PMF.tsum_mul_le_of_forall_le _ fun r => le_of_eq ?_
  refine (PMF.toOuterMeasure_pure_apply _ _).trans (ite_eq_right fun h => h ⟨rfl, ?_⟩)
  simp only [batchEvalRelOut]
  exact Finset.sum_congr rfl fun i _ => by rw [hy i]

/-- **Round-by-round soundness of random linear combination batching**: a false multi-evaluation
claim survives with probability at most `1 / |F|`. -/
theorem batchEvalReduction_rbrSound [Field F] [Fintype F] (eval : Poly → Point → F)
    (p : Fin k → Poly) (z : Point) :
    (batchEvalReduction eval p z).verifier.RbrSound
      (language (batchEvalRelIn eval p z)) (language (batchEvalRelOut eval p z))
      (1 / (Fintype.card F : ℝ≥0∞), ()) := by
  refine ⟨fun y pfx => match pfx with
    | none => ∀ i, eval (p i) z = y i
    | some (r, _) => ∑ i, r i * eval (p i) z = ∑ i, r i * y i,
    fun y hy h => hy ⟨(), h⟩, fun y => ⟨?_, fun r => ?_⟩⟩
  · intro hS
    change ¬ (∀ i, eval (p i) z = y i) at hS
    push Not at hS
    obtain ⟨i₀, hi₀⟩ := hS
    change (ProbComp.eval (ProbComp.uniform (Fin k → F))).toOuterMeasure
      {r | ∑ i, r i * eval (p i) z = ∑ i, r i * y i} ≤ 1 / (Fintype.card F : ℝ≥0∞)
    rw [ProbComp.eval_uniform, toOuterMeasure_batchEval_eq eval p z y hi₀]
  · rintro hS ⟨c, ⟨_, hc⟩, hout⟩
    rw [batchEvalReduction_outputOn] at hout
    obtain rfl := Option.some.inj hout
    exact hS hc

/-- **Soundness of random linear combination batching**: against any prover strategy, a false
multi-evaluation claim produces a valid batched claim with probability at most `1 / |F|`. -/
theorem batchEvalReduction_sound [Field F] [Fintype F] (eval : Poly → Point → F)
    (p : Fin k → Poly) (z : Point) :
    (batchEvalReduction eval p z).verifier.Sound (oP := OracleSpec.empty) World.plain
      (language (batchEvalRelIn eval p z)) (language (batchEvalRelOut eval p z))
      (1 / (Fintype.card F : ℝ≥0∞)) := by
  have h := (batchEvalReduction_rbrSound eval p z).sound
  simpa only [PerChallenge.sum, add_zero] using h

end BatchEval

/-! ### Ligero matrix-code IOP core -/

section Ligero

variable {F : Type} {m l n : ℕ}

/-- The Ligero prover's row linear combination `v = r ᵥ* U : Fin l → F` for challenge vector
`r : Fin m → F` and witness matrix `U : Matrix (Fin m) (Fin l) F` [Ames, Hazay, Ishai and
Venkitasubramaniam][AmesHazayIshaiVenkitasubramaniam2017]. -/
@[expose] def ligeroRowComb [Semiring F] (r : Fin m → F) (U : Matrix (Fin m) (Fin l) F) :
    Fin l → F :=
  r ᵥ* U

/-- **Ligero row-combination completeness identity**: encoding the row linear combination
`ligeroRowComb r U` by `G` equals taking the same linear combination of the encoded matrix
`U * G`. -/
theorem ligeroRowComb_mul [Semiring F] (r : Fin m → F) (U : Matrix (Fin m) (Fin l) F)
    (G : Matrix (Fin l) (Fin n) F) :
    ligeroRowComb r U ᵥ* G = r ᵥ* (U * G) :=
  Matrix.vecMul_vecMul r U G

/-- Pointwise form of `ligeroRowComb_mul` at column `j`. -/
theorem ligeroRowComb_mul_apply [Semiring F] (r : Fin m → F) (U : Matrix (Fin m) (Fin l) F)
    (G : Matrix (Fin l) (Fin n) F) (j : Fin n) :
    (ligeroRowComb r U ᵥ* G) j = (r ᵥ* (U * G)) j :=
  congrFun (ligeroRowComb_mul r U G) j

/-- Expanding `((ligeroRowComb r U) ᵥ* G) j` as a linear combination of the encoded witness rows
`((U i) ᵥ* G) j`. -/
theorem ligeroRowComb_mul_eq_sum [CommSemiring F] (r : Fin m → F) (U : Matrix (Fin m) (Fin l) F)
    (G : Matrix (Fin l) (Fin n) F) (j : Fin n) :
    (ligeroRowComb r U ᵥ* G) j = ∑ i : Fin m, r i * ((U i) ᵥ* G) j := by
  rw [ligeroRowComb_mul_apply]
  rfl

/-- Target bilinear evaluation `(b ᵥ* U) ⬝ᵥ c` of a witness matrix `U : Matrix (Fin m) (Fin l) F` at
outer-product query vectors `b : Fin m → F` and `c : Fin l → F`. -/
@[expose] def ligeroEval [Semiring F] (U : Matrix (Fin m) (Fin l) F) (b : Fin m → F)
    (c : Fin l → F) : F :=
  ligeroRowComb b U ⬝ᵥ c

/-- The Ligero verifier's column check at column `j : Fin n`: the `j`-th coordinate of the encoded
response `v ᵥ* G` matches the `r`-linear combination of column `j` of the oracle matrix `M`. -/
@[expose] def ligeroColumnCheck [Semiring F] [DecidableEq F] (G : Matrix (Fin l) (Fin n) F)
    (M : Matrix (Fin m) (Fin n) F) (r : Fin m → F) (v : Fin l → F) (j : Fin n) : Bool :=
  decide ((v ᵥ* G) j = (r ᵥ* M) j)

/-- The Ligero verifier's combined evaluation and column check at column `j : Fin n` for a linear
evaluation claim `(b, c, w)`: checks both `v ⬝ᵥ c = w` and `(v ᵥ* G) j = (b ᵥ* M) j`. -/
@[expose] def ligeroEvalCheck [Semiring F] [DecidableEq F] (G : Matrix (Fin l) (Fin n) F)
    (M : Matrix (Fin m) (Fin n) F) (b : Fin m → F) (c : Fin l → F) (w : F) (v : Fin l → F)
    (j : Fin n) : Bool :=
  decide (v ⬝ᵥ c = w ∧ (v ᵥ* G) j = (b ᵥ* M) j)

/-- **Completeness of the Ligero column check**: when `M = U * G` and `v = ligeroRowComb r U`, the
column check passes at every column `j`. -/
theorem ligeroColumnCheck_honest [Semiring F] [DecidableEq F] (G : Matrix (Fin l) (Fin n) F)
    (U : Matrix (Fin m) (Fin l) F) (r : Fin m → F) (j : Fin n) :
    ligeroColumnCheck G (U * G) r (ligeroRowComb r U) j = true := by
  simp [ligeroColumnCheck, ligeroRowComb_mul_apply]

/-- **Completeness of the Ligero evaluation check**: when `M = U * G`, `w = ligeroEval U b c`, and
`v = ligeroRowComb b U`, the evaluation check passes at every column `j`. -/
theorem ligeroEvalCheck_honest [Semiring F] [DecidableEq F] (G : Matrix (Fin l) (Fin n) F)
    (U : Matrix (Fin m) (Fin l) F) (b : Fin m → F) (c : Fin l → F) (j : Fin n) :
    ligeroEvalCheck G (U * G) b c (ligeroEval U b c) (ligeroRowComb b U) j = true := by
  simp [ligeroEvalCheck, ligeroEval, ligeroRowComb_mul_apply]

/-- **Ligero row-consistency soundness (exact probability)**: if some row `i₀` of `M` disagrees with
the encoded witness row `(U i₀) ᵥ* G` at column `j`, then over a uniform challenge `r : Fin m → F`,
`(r ᵥ* M) j = ((ligeroRowComb r U) ᵥ* G) j` holds with probability *exactly* `1 / |F|`. -/
theorem toOuterMeasure_ligeroRowComb_eq [Field F] [Fintype F] (G : Matrix (Fin l) (Fin n) F)
    (M : Matrix (Fin m) (Fin n) F) (U : Matrix (Fin m) (Fin l) F) {i₀ : Fin m} {j : Fin n}
    (hne : M i₀ j ≠ ((U i₀) ᵥ* G) j) :
    (PMF.uniformOfFintype (Fin m → F)).toOuterMeasure
        {r | (r ᵥ* M) j = (ligeroRowComb r U ᵥ* G) j} =
      1 / (Fintype.card F : ℝ≥0∞) := by
  have hset : {r : Fin m → F | (r ᵥ* M) j = (ligeroRowComb r U ᵥ* G) j} =
      {r : Fin m → F | ∑ i : Fin m, r i * (M i j - ((U i) ᵥ* G) j) = 0} := by
    ext r
    simp only [Set.mem_ofPred_eq]
    rw [ligeroRowComb_mul_eq_sum, Matrix.vecMul_apply_eq_sum r M j, ← sub_eq_zero,
      ← Finset.sum_sub_distrib]
    simp only [mul_sub]
  rw [hset]
  exact toOuterMeasure_uniform_linearComb_eq_zero (sub_ne_zero.mpr hne)

/-- **Ligero row-consistency soundness bound**: if `M i₀ j ≠ ((U i₀) ᵥ* G) j` for some row `i₀`,
then over uniform `r : Fin m → F`, `(r ᵥ* M) j = ((ligeroRowComb r U) ᵥ* G) j` holds with
probability at most `1 / |F|`. -/
theorem toOuterMeasure_ligeroRowComb_le [Field F] [Fintype F] (G : Matrix (Fin l) (Fin n) F)
    (M : Matrix (Fin m) (Fin n) F) (U : Matrix (Fin m) (Fin l) F) {i₀ : Fin m} {j : Fin n}
    (hne : M i₀ j ≠ ((U i₀) ᵥ* G) j) :
    (PMF.uniformOfFintype (Fin m → F)).toOuterMeasure
        {r | (r ᵥ* M) j = (ligeroRowComb r U ᵥ* G) j} ≤
      1 / (Fintype.card F : ℝ≥0∞) :=
  le_of_eq (toOuterMeasure_ligeroRowComb_eq G M U hne)

/-- If `M i₀ j ≠ ((U i₀) ᵥ* G) j` for some row `i₀`, then `ligeroEvalCheck` on the honest row
combination `ligeroRowComb b U` accepts at column `j` with probability at most `1 / |F|` over
uniform `b : Fin m → F`. -/
theorem toOuterMeasure_ligeroEvalCheck_le [Field F] [Fintype F] [DecidableEq F]
    (G : Matrix (Fin l) (Fin n) F) (M : Matrix (Fin m) (Fin n) F) (U : Matrix (Fin m) (Fin l) F)
    (c : Fin l → F) {i₀ : Fin m} {j : Fin n} (hne : M i₀ j ≠ ((U i₀) ᵥ* G) j) :
    (PMF.uniformOfFintype (Fin m → F)).toOuterMeasure
        {b | ligeroEvalCheck G M b c (ligeroEval U b c) (ligeroRowComb b U) j = true} ≤
      1 / (Fintype.card F : ℝ≥0∞) := by
  refine ((PMF.uniformOfFintype (Fin m → F)).toOuterMeasure.mono fun b hb => ?_).trans
    (toOuterMeasure_ligeroRowComb_le G M U hne)
  simp only [Set.mem_ofPred_eq, ligeroEvalCheck, decide_eq_true_eq] at hb
  exact hb.2.symm

/-- Bundle of a Ligero matrix-code IOP instance over an `m × l` witness matrix `U`, an `l × n`
generator matrix `G`, and an `m × n` purported codeword matrix `M` [Ames, Hazay, Ishai and
Venkitasubramaniam][AmesHazayIshaiVenkitasubramaniam2017]. -/
structure LigeroMatrixIOP (F : Type) (m l n : ℕ) where
  /-- Linear code generator matrix `G : l × n`. -/
  G : Matrix (Fin l) (Fin n) F
  /-- Witness matrix `U : m × l`. -/
  U : Matrix (Fin m) (Fin l) F
  /-- Purported codeword matrix `M : m × n`. -/
  M : Matrix (Fin m) (Fin n) F

namespace LigeroMatrixIOP

/-- All rows of `M` at column `j` equal the encoded rows of `U`. -/
@[expose] def RowConsistentAt [Semiring F] (L : LigeroMatrixIOP F m l n) (j : Fin n) : Prop :=
  ∀ i : Fin m, L.M i j = ((L.U i) ᵥ* L.G) j

/-- The round specification of a Ligero row-consistency check: the verifier sends a uniform
challenge `r : Fin m → F` and the prover responds with a vector `v : Fin l → F` read in full. -/
abbrev spec (m l : ℕ) (F : Type) : Spec :=
  [.verifier (Fin m → F), .prover (Fin l → F) (OracleInterface.full (Fin l → F))]

/-- The input relation at column `j`: the purported matrix `M` is row-consistent with `U * G` at
column `j`. -/
@[expose] def relIn [Semiring F] (L : LigeroMatrixIOP F m l n) : Fin n → Unit → Prop :=
  fun j _ => L.RowConsistentAt j

/-- The output relation of the Ligero column reduction: the prover's response `v` equals the true
row combination `ligeroRowComb r L.U`. -/
@[expose] def relOut [Semiring F] (L : LigeroMatrixIOP F m l n) :
    ((Fin m → F) × (Fin l → F)) → Unit → Prop :=
  fun rv _ => rv.2 = ligeroRowComb rv.1 L.U

/-- **Public-coin interactive reduction for the Ligero column check**: on input column `j : Fin n`,
the verifier samples a uniform row challenge `r : Fin m → F`, the prover sends
`v = ligeroRowComb r L.U`, and the verifier checks `(v ᵥ* L.G) j = (r ᵥ* L.M) j`, outputting the
claim `(r, v)`. -/
noncomputable def columnReduction [Field F] [Fintype F] [DecidableEq F]
    (L : LigeroMatrixIOP F m l n) :
    Reduction OracleSpec.empty OracleSpec.empty (spec m l F)
      (Fin n) Unit ((Fin m → F) × (Fin l → F)) Unit where
  prover _ _ :=
    pure (show (Fin m → F) → ProbOracleComp OracleSpec.empty
        (ProbOracleComp OracleSpec.empty
          ((Fin l → F) × (((Fin m → F) × (Fin l → F)) × Unit))) from
      fun r =>
        let v := ligeroRowComb r L.U
        pure (pure (v, ((r, v), ()))))
  verifier :=
    { samplers := (ProbComp.uniform (Fin m → F), ())
      decide := fun j c => do
        let v ← OracleComp.query (spec := OracleSpec.empty ⊕ₒ msgSpec (spec m l F))
          (.inr (.inl ()))
        return if ligeroColumnCheck L.G L.M c.1 v j then some (c.1, v) else none }

theorem columnReduction_outputOn [Field F] [Fintype F] [DecidableEq F]
    (L : LigeroMatrixIOP F m l n) (j : Fin n) (r : Fin m → F) (v : Fin l → F) :
    L.columnReduction.verifier.outputOn j (r, v, ()) =
      if ligeroColumnCheck L.G L.M r v j then some (r, v) else none := by
  rfl

/-- **Completeness of the Ligero column reduction**: if `L.M` is row-consistent with `L.U * L.G` at
column `j`, the honest prover convinces the verifier with probability `1` (error `0`). -/
theorem columnReduction_complete [Field F] [Fintype F] [DecidableEq F]
    (L : LigeroMatrixIOP F m l n) :
    L.columnReduction.Complete World.plain L.relIn L.relOut 0 := by
  intro j _ hj
  rw [Reduction.run, World.plain_eval_execute, PMF.toOuterMeasure_map_apply]
  simp only [columnReduction, runStrategy, plainLaw_bind, plainLaw_pure, plainLaw_sample,
    PMF.pure_bind, PMF.bind_bind]
  rw [PMF.toOuterMeasure_bind_apply]
  refine Probability.PMF.tsum_mul_le_of_forall_le _ fun r => le_of_eq ?_
  have hchk : ligeroColumnCheck L.G L.M r (ligeroRowComb r L.U) j = true := by
    simp only [ligeroColumnCheck, decide_eq_true_eq, ligeroRowComb_mul_eq_sum]
    rw [Matrix.vecMul_apply_eq_sum r L.M j]
    exact (Finset.sum_congr rfl fun i _ => by rw [hj i]).symm
  refine (PMF.toOuterMeasure_pure_apply _ _).trans (ite_eq_right fun h => h ⟨?_, rfl⟩)
  exact (L.columnReduction_outputOn j r (ligeroRowComb r L.U)).trans (ite_eq_left hchk)

/-- **Round-by-round soundness of the Ligero column reduction**: if column `j` has any inconsistent
row `L.M i₀ j ≠ ((L.U i₀) ᵥ* L.G) j`, then any prover produces an accepted transcript in
`language L.relOut` (where `v = ligeroRowComb r L.U`) with probability at most `1 / |F|`. -/
theorem columnReduction_rbrSound [Field F] [Fintype F] [DecidableEq F]
    (L : LigeroMatrixIOP F m l n) :
    L.columnReduction.verifier.RbrSound (language L.relIn) (language L.relOut)
      (1 / (Fintype.card F : ℝ≥0∞), ()) := by
  refine ⟨fun j pfx => match pfx with
    | none => L.RowConsistentAt j
    | some (r, none) => (r ᵥ* L.M) j = (ligeroRowComb r L.U ᵥ* L.G) j
    | some (r, some (v, _)) => (r ᵥ* L.M) j = (ligeroRowComb r L.U ᵥ* L.G) j,
    fun j hj h => hj ⟨(), h⟩,
    fun j => ⟨?_, fun r => ⟨fun hS _ h => hS h, fun v hS ⟨rv, ⟨_, hrv⟩, hout⟩ => ?_⟩⟩⟩
  · intro hS
    change ¬ L.RowConsistentAt j at hS
    unfold RowConsistentAt at hS
    push Not at hS
    obtain ⟨i₀, hi₀⟩ := hS
    change (ProbComp.eval (ProbComp.uniform (Fin m → F))).toOuterMeasure
      {r | (r ᵥ* L.M) j = (ligeroRowComb r L.U ᵥ* L.G) j} ≤ 1 / (Fintype.card F : ℝ≥0∞)
    rw [ProbComp.eval_uniform]
    exact toOuterMeasure_ligeroRowComb_le L.G L.M L.U hi₀
  · rw [columnReduction_outputOn] at hout
    split_ifs at hout with hchk
    obtain rfl := Option.some.inj hout
    change v = ligeroRowComb r L.U at hrv
    subst hrv
    simp only [ligeroColumnCheck, decide_eq_true_eq] at hchk
    exact hS hchk.symm

/-- **Soundness of the Ligero column reduction**: if column `j` is not row-consistent with
`L.U * L.G`, no prover strategy can make the verifier output a valid row-combination claim with
probability greater than `1 / |F|`. -/
theorem columnReduction_sound [Field F] [Fintype F] [DecidableEq F]
    (L : LigeroMatrixIOP F m l n) :
    L.columnReduction.verifier.Sound (oP := OracleSpec.empty) World.plain
      (language L.relIn) (language L.relOut) (1 / (Fintype.card F : ℝ≥0∞)) := by
  have h := L.columnReduction_rbrSound.sound
  simpa only [PerChallenge.sum, add_zero] using h

end LigeroMatrixIOP

end Ligero

end Cslib.Crypto.Protocols
