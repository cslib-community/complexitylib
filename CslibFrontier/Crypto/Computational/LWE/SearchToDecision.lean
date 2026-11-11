/-
Copyright (c) 2026 Samuel Schlesinger, real-roots. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, real-roots
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.LWE.NormalForm
public import CslibFrontier.Languages.Probabilistic.Vector
public import Mathlib.Analysis.SpecialFunctions.Exp
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.Concentration
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.Union
import CslibFrontier.Probability.Product.Reindex
import CslibFrontier.Tactic.PMFSwap

/-!
# Search to decision for prime-modulus LWE

Regev's reduction recovers the LWE secret with a decision distinguisher `D`. To test whether a
guess `g` equals coordinate `j` of the secret `s`, it takes a fresh `m`-row sample `[b | A]`,
re-randomizes the secret to `s + s'` with a uniform `s'` (`b ↦ b + A *ᵥ s'`), and adds `r` to
column `j` of `A` and `(g + s' j) • r` to `b` for a uniform `r`. When `g = s j` the result is a
fresh LWE sample; otherwise its first column is uniform and independent of the rest, so the
result is a uniform matrix. Each trial therefore accepts with `D`'s acceptance probability on
real samples or on uniform matrices, independently of all other trials.

The reduction runs `N` such trials for every coordinate `j` and guess `g`, each on its own block of
`m` samples, and `N` trials of `D` on uniform matrices. For each `j` it outputs the guess whose
acceptance count is farthest from the uniform count. Hoeffding's inequality and a union bound over
the `n * q + 1` estimators bound its failure probability.

The reduction is concrete: it samples exactly uniform elements of `ZMod q`, which a fair-coin
machine cannot do for odd `q`, so no `IsPPT` certificate or asymptotic `SearchLWE → DecisionLWE`
statement is given here.

## Main definitions

* `Cslib.Crypto.PrimeLWE.lweSelfReduceDistinguisher`: shift coordinate `j` by a guess, then run
  the distinguisher.
* `Cslib.Crypto.PrimeLWE.rerandomizeSecret`: move the secret of a sample from `s` to `s + s'`.
* `Cslib.Crypto.PrimeLWE.reduceSearchToDecision`: the search reduction on
  `searchSamples n q N m = (n * q + 1) * N * m` samples.

## Main results

* `Cslib.Crypto.PrimeLWE.lweSelfReduce_real`, `Cslib.Crypto.PrimeLWE.lweSelfReduce_ideal`: a
  correct guess preserves an LWE sample; a wrong guess makes it uniform.
* `Cslib.Crypto.PrimeLWE.searchToDecision`: the reduction recovers the secret with probability at
  least `1 - (n * q + 1) * 2 * exp (-N * ε ^ 2 / 8)`, where `ε` is the distinguisher's
  decision-LWE advantage with `m` samples.

## References

* [O. Regev, *On lattices, learning with errors, random linear codes, and cryptography*][Regev2009],
  Lemma 4.2.
* [C. Peikert, *A Decade of Lattice Cryptography*][Peikert2016], Section 4.2.
-/

public section

namespace Cslib.Crypto.PrimeLWE

open Probability Turing.MultiTapeTM
open scoped _root_.Matrix

/-! ### Shifting one coordinate -/

/-- Shift the `j`-th coordinate of the public matrix by adding a vector `r` to the `j`-th
column of `A`, and adding `g * r` to the `0`-th column `b`. -/
def shiftCoordinate {n m q : ℕ} (P : Matrix (Fin m) (Fin (n + 1)) (ZMod q))
    (j : Fin n) (g : ZMod q) (r : Fin m → ZMod q) :
    Matrix (Fin m) (Fin (n + 1)) (ZMod q) :=
  fun i => Fin.cons (P i 0 + g * r i) (fun c => if c = j then P i c.succ + r i else P i c.succ)

/-- Shifting an LWE sample adds `r` to column `j` of `A` and `(g - s j) * r` to the error. -/
theorem shiftCoordinate_publicMatrix {n m q : ℕ} [Fact (Nat.Prime q)]
    (A : Matrix (Fin m) (Fin n) (ZMod q)) (s : Fin n → ZMod q) (e : Fin m → ZMod q)
    (j : Fin n) (g : ZMod q) (r : Fin m → ZMod q) :
    shiftCoordinate (publicMatrix A s e) j g r =
    publicMatrix (fun i c => if c = j then A i c + r i else A i c) s
      (fun i => e i + (g - s j) * r i) := by
  funext i c
  refine Fin.cases ?_ (fun c => ?_) c
  · have h : ((fun i c => if c = j then A i c + r i else A i c) *ᵥ s) i =
        (A *ᵥ s) i + r i * s j := by
      simp only [Matrix.mulVec, dotProduct, ite_mul, add_mul]
      rw [show (∑ x, if x = j then A i x * s x + r i * s x else A i x * s x) =
          ∑ x, (A i x * s x + if x = j then r i * s x else 0) from
        Finset.sum_congr rfl fun x _ => by split_ifs <;> ring]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp
    simp only [shiftCoordinate, publicMatrix, Fin.cons_zero, h]
    ring
  · simp only [shiftCoordinate, publicMatrix, Fin.cons_succ]

/-- For a fixed `r`, adding `r` to the `j`-th column is a bijection on matrices. -/
def shiftMatrixEquiv {n m q : ℕ} (j : Fin n) (r : Fin m → ZMod q) :
    Matrix (Fin m) (Fin n) (ZMod q) ≃ Matrix (Fin m) (Fin n) (ZMod q) where
  toFun A i c := if c = j then A i c + r i else A i c
  invFun A i c := if c = j then A i c - r i else A i c
  left_inv A := by ext i c; dsimp; split_ifs <;> ring
  right_inv A := by ext i c; dsimp; split_ifs <;> ring

/-- For `c ≠ 0`, `r ↦ e + c • r` is a bijection on vectors over the field `ZMod q`. -/
def shiftErrorEquiv {m q : ℕ} [Fact (Nat.Prime q)] (e : Fin m → ZMod q)
    (c : ZMod q) (hc : c ≠ 0) :
    (Fin m → ZMod q) ≃ (Fin m → ZMod q) where
  toFun r i := e i + c * r i
  invFun r' i := c⁻¹ * (r' i - e i)
  left_inv r := by ext i; dsimp; field_simp; ring
  right_inv r' := by ext i; dsimp; field_simp; ring

open Cslib Cslib.ProbComp

/-- The self-reduction for decision LWE: shift coordinate `j` by the guess `g` with a uniform
vector, then run the distinguisher. -/
noncomputable def lweSelfReduceDistinguisher {n m q : ℕ} [Fact (Nat.Prime q)]
    (distinguisher : Matrix (Fin m) (Fin (n + 1)) (ZMod q) → ProbComp Bool)
    (P : Matrix (Fin m) (Fin (n + 1)) (ZMod q)) (j : Fin n) (g : ZMod q) : ProbComp Bool := do
  let r ← ProbComp.uniform (Fin m → ZMod q)
  distinguisher (shiftCoordinate P j g r)

/-- Over a uniform `A`, the self-reduction runs the distinguisher on an LWE sample with error
`e + (g - s j) • r` for a uniform `r`. -/
theorem uniform_bind_lweSelfReduceDistinguisher {n m q : ℕ} [Fact (Nat.Prime q)]
    (distinguisher : Matrix (Fin m) (Fin (n + 1)) (ZMod q) → ProbComp Bool)
    (s : Fin n → ZMod q) (e : Fin m → ZMod q) (j : Fin n) (g : ZMod q) :
    ((PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
      eval (lweSelfReduceDistinguisher distinguisher (publicMatrix A s e) j g)) =
    ((PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
      (PMF.uniformOfFintype (Fin m → ZMod q)).bind fun r =>
        eval (distinguisher (publicMatrix A s (fun i => e i + (g - s j) * r i)))) := by
  simp_rw [lweSelfReduceDistinguisher, eval_bind, eval_uniform, shiftCoordinate_publicMatrix]
  rw [PMF.bind_comm, PMF.bind_comm (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q)))]
  congr 1
  funext r
  exact PMF.uniformOfFintype_bind_equiv (shiftMatrixEquiv j r)
    (fun A => eval (distinguisher (publicMatrix A s (fun i => e i + (g - s j) * r i))))

/-- A correct guess leaves the law of an LWE sample with a uniform `A` unchanged. -/
theorem lweSelfReduce_real {n m q : ℕ} [Fact (Nat.Prime q)]
    (distinguisher : Matrix (Fin m) (Fin (n + 1)) (ZMod q) → ProbComp Bool)
    (s : Fin n → ZMod q) (e : Fin m → ZMod q) (j : Fin n) (g : ZMod q) (hg : g = s j) :
    ((PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
      eval (lweSelfReduceDistinguisher distinguisher (publicMatrix A s e) j g)) =
    ((PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
      eval (distinguisher (publicMatrix A s e))) := by
  rw [uniform_bind_lweSelfReduceDistinguisher]
  simp only [hg, sub_self, zero_mul, add_zero, PMF.bind_const]

/-- A wrong guess replaces the error of an LWE sample with a uniform `A` by a uniform vector. -/
theorem lweSelfReduce_ideal {n m q : ℕ} [Fact (Nat.Prime q)]
    (distinguisher : Matrix (Fin m) (Fin (n + 1)) (ZMod q) → ProbComp Bool)
    (s : Fin n → ZMod q) (e : Fin m → ZMod q) (j : Fin n) (g : ZMod q) (hg : g ≠ s j) :
    ((PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
      eval (lweSelfReduceDistinguisher distinguisher (publicMatrix A s e) j g)) =
    ((PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
      (PMF.uniformOfFintype (Fin m → ZMod q)).bind fun v =>
        eval (distinguisher (publicMatrix A s v))) := by
  rw [uniform_bind_lweSelfReduceDistinguisher]
  congr 1
  funext A
  exact PMF.uniformOfFintype_bind_equiv (shiftErrorEquiv e (g - s j) (sub_ne_zero.mpr hg))
    (fun v => eval (distinguisher (publicMatrix A s v)))

/-! ### Secret re-randomization and single trials -/

/-- Move the secret of a sample `[b | A]` from `s` to `s + s'` by adding `A *ᵥ s'` to `b`. -/
def rerandomizeSecret {n m q : ℕ} (P : Matrix (Fin m) (Fin (n + 1)) (ZMod q))
    (s' : Fin n → ZMod q) : Matrix (Fin m) (Fin (n + 1)) (ZMod q) :=
  fun i => Fin.cons (P i 0 + ((fun i c => P i c.succ) *ᵥ s') i) (fun c => P i c.succ)

/-- Re-randomizing an LWE sample by `s'` adds `s'` to its secret. -/
theorem rerandomizeSecret_publicMatrix {n m q : ℕ} [Fact (Nat.Prime q)]
    (A : Matrix (Fin m) (Fin n) (ZMod q)) (s s' : Fin n → ZMod q) (e : Fin m → ZMod q) :
    rerandomizeSecret (publicMatrix A s e) s' = publicMatrix A (s + s') e := by
  funext i c
  refine Fin.cases ?_ (fun c => ?_) c
  · simp only [rerandomizeSecret, publicMatrix, Fin.cons_zero, Fin.cons_succ, Matrix.mulVec_add,
      Pi.add_apply]
    ring
  · simp only [rerandomizeSecret, publicMatrix, Fin.cons_succ]

/-- One trial for coordinate `j` and guess `g` on a fresh sample: re-randomize the secret by a
uniform `s'`, then run the self-reduction with the guess `g + s' j`. -/
noncomputable def coordinateTrial {n m q : ℕ} [Fact (Nat.Prime q)]
    (distinguisher : Matrix (Fin m) (Fin (n + 1)) (ZMod q) → ProbComp Bool)
    (j : Fin n) (g : ZMod q) (P : Matrix (Fin m) (Fin (n + 1)) (ZMod q)) : ProbComp Bool := do
  let s' ← ProbComp.uniform (Fin n → ZMod q)
  lweSelfReduceDistinguisher distinguisher (rerandomizeSecret P s') j (g + s' j)

/-- The trial of an estimator on a sample. The estimator `none` runs the distinguisher on a fresh
uniform matrix and ignores the sample; `some (j, g)` tests the guess `g` for coordinate `j`. -/
noncomputable def estimatorTrial {n m q : ℕ} [Fact (Nat.Prime q)]
    (distinguisher : Matrix (Fin m) (Fin (n + 1)) (ZMod q) → ProbComp Bool) :
    Option (Fin n × ZMod q) → Matrix (Fin m) (Fin (n + 1)) (ZMod q) → ProbComp Bool
  | none, _ => ProbComp.uniform (Matrix (Fin m) (Fin (n + 1)) (ZMod q)) >>= distinguisher
  | some (j, g), P => coordinateTrial distinguisher j g P

/-- The distinguisher's output law on real LWE samples. -/
noncomputable def realLaw {n m q : ℕ} [Fact (Nat.Prime q)] (noise : PMF (ZMod q))
    (distinguisher : Matrix (Fin m) (Fin (n + 1)) (ZMod q) → ProbComp Bool) : PMF Bool :=
  (publicMatrixLaw n m q noise).bind fun P => eval (distinguisher P)

/-- The distinguisher's output law on uniform matrices. -/
noncomputable def uniformLaw {n m q : ℕ} [Fact (Nat.Prime q)]
    (distinguisher : Matrix (Fin m) (Fin (n + 1)) (ZMod q) → ProbComp Bool) : PMF Bool :=
  (PMF.uniformOfFintype (Matrix (Fin m) (Fin (n + 1)) (ZMod q))).bind fun P =>
    eval (distinguisher P)

/-- The law of an LWE sample with the fixed secret `s`. -/
noncomputable def sampleLaw (n m q : ℕ) [Fact (Nat.Prime q)] (noise : PMF (ZMod q))
    (s : Fin n → ZMod q) : PMF (Matrix (Fin m) (Fin (n + 1)) (ZMod q)) :=
  (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
    (PMF.pi fun _ : Fin m => noise).bind fun e => PMF.pure (publicMatrix A s e)

/-- The output law of an estimator's trial on a fresh sample with secret `s`. -/
noncomputable def estimatorLaw {n m q : ℕ} [Fact (Nat.Prime q)] (noise : PMF (ZMod q))
    (distinguisher : Matrix (Fin m) (Fin (n + 1)) (ZMod q) → ProbComp Bool)
    (s : Fin n → ZMod q) : Option (Fin n × ZMod q) → PMF Bool
  | none => uniformLaw distinguisher
  | some (j, g) => if g = s j then realLaw noise distinguisher else uniformLaw distinguisher

/-- On a fresh sample with secret `s`, a trial of guess `g` for coordinate `j` behaves like the
distinguisher on real samples when `g = s j` and like the distinguisher on uniform matrices
otherwise. -/
theorem sampleLaw_bind_coordinateTrial {n m q : ℕ} [Fact (Nat.Prime q)] (noise : PMF (ZMod q))
    (distinguisher : Matrix (Fin m) (Fin (n + 1)) (ZMod q) → ProbComp Bool)
    (s : Fin n → ZMod q) (j : Fin n) (g : ZMod q) :
    (sampleLaw n m q noise s).bind (fun P => eval (coordinateTrial distinguisher j g P)) =
      if g = s j then realLaw noise distinguisher else uniformLaw distinguisher := by
  have hswap :
      (sampleLaw n m q noise s).bind (fun P => eval (coordinateTrial distinguisher j g P)) =
      (PMF.uniformOfFintype (Fin n → ZMod q)).bind fun s' =>
        (PMF.pi fun _ : Fin m => noise).bind fun e =>
          (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
            eval (lweSelfReduceDistinguisher distinguisher (publicMatrix A (s + s') e) j
              (g + s' j)) := by
    simp only [sampleLaw, coordinateTrial, PMF.bind_bind, PMF.pure_bind, eval_bind, eval_uniform,
      rerandomizeSecret_publicMatrix]
    pmf_swap
  rw [hswap]
  split_ifs with hg
  · calc _ = (PMF.uniformOfFintype (Fin n → ZMod q)).bind fun s' =>
          (PMF.pi fun _ : Fin m => noise).bind fun e =>
            (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
              eval (distinguisher (publicMatrix A (s + s') e)) := by
          congr 1; funext s'; congr 1; funext e
          exact lweSelfReduce_real distinguisher (s + s') e j (g + s' j)
            (by simp [hg])
      _ = (PMF.uniformOfFintype (Fin n → ZMod q)).bind fun s' =>
          (PMF.pi fun _ : Fin m => noise).bind fun e =>
            (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
              eval (distinguisher (publicMatrix A s' e)) :=
          PMF.uniformOfFintype_bind_equiv (Equiv.addLeft s) (fun s' =>
            (PMF.pi fun _ : Fin m => noise).bind fun e =>
              (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
                eval (distinguisher (publicMatrix A s' e)))
      _ = _ := by
          simp only [realLaw, publicMatrixLaw, pmf_norm]
          pmf_swap
  · calc _ = (PMF.uniformOfFintype (Fin n → ZMod q)).bind fun s' =>
          (PMF.pi fun _ : Fin m => noise).bind fun _ =>
            (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
              (PMF.uniformOfFintype (Fin m → ZMod q)).bind fun v =>
                eval (distinguisher (publicMatrix A (s + s') v)) := by
          congr 1; funext s'; congr 1; funext e
          exact lweSelfReduce_ideal distinguisher (s + s') e j (g + s' j)
            (by simpa [add_comm] using hg)
      _ = _ := by
          have h (s' : Fin n → ZMod q) :
              ((PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
                (PMF.uniformOfFintype (Fin m → ZMod q)).bind fun v =>
                  eval (distinguisher (publicMatrix A (s + s') v))) =
                uniformLaw distinguisher := by
            rw [uniformLaw, ← uniform_bind_publicMatrix (s + s')]
            simp only [PMF.bind_bind, PMF.pure_bind]
          simp only [PMF.bind_const, h]

/-- On a fresh sample with secret `s`, each estimator's trial has law `estimatorLaw`. -/
theorem sampleLaw_bind_estimatorTrial {n m q : ℕ} [Fact (Nat.Prime q)] (noise : PMF (ZMod q))
    (distinguisher : Matrix (Fin m) (Fin (n + 1)) (ZMod q) → ProbComp Bool)
    (s : Fin n → ZMod q) (o : Option (Fin n × ZMod q)) :
    (sampleLaw n m q noise s).bind (fun P => eval (estimatorTrial distinguisher o P)) =
      estimatorLaw noise distinguisher s o := by
  rcases o with _ | ⟨j, g⟩
  · simp only [estimatorTrial, estimatorLaw, uniformLaw, eval_bind, eval_uniform, PMF.bind_const]
  · exact sampleLaw_bind_coordinateTrial noise distinguisher s j g

/-! ### Independent blocks -/

/-- Run one program for each element of a finite type, independently. -/
noncomputable def sampleEach {ι β : Type} [Fintype ι] (programs : ι → ProbComp β) :
    ProbComp (ι → β) :=
  (fun x i => x (Fintype.equivFin ι i)) <$>
    OracleComp.pi fun k => programs ((Fintype.equivFin ι).symm k)

/-- The programs run by `sampleEach` are independent. -/
theorem eval_sampleEach {ι β : Type} [Fintype ι] [Finite β] (programs : ι → ProbComp β) :
    eval (sampleEach programs) = PMF.pi fun i => eval (programs i) := by
  rw [sampleEach, eval_map, eval_pi]
  have h := PMF.pi_map_piCongrLeft_symm
    (fun k => eval (programs ((Fintype.equivFin ι).symm k))) (Fintype.equivFin ι)
  simp only [Equiv.symm_apply_apply] at h
  rw [← h]
  rfl

/-- The law of one row `[a ⬝ᵥ s + x | a]` of an LWE sample with secret `s`. -/
noncomputable def rowLaw (n q : ℕ) [Fact (Nat.Prime q)] (noise : PMF (ZMod q))
    (s : Fin n → ZMod q) : PMF (Fin (n + 1) → ZMod q) :=
  (PMF.uniformOfFintype (Fin n → ZMod q)).bind fun a =>
    noise.bind fun x => PMF.pure (Fin.cons (a ⬝ᵥ s + x) a)

private theorem pi_pure {ι γ : Type} [Fintype ι] [Finite γ] (c : ι → γ) :
    (PMF.pi fun i => PMF.pure (c i)) = PMF.pure c := by
  classical
  ext x
  simp only [PMF.pi_apply, PMF.pure_apply]
  by_cases h : x = c
  · subst h
    simp
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ c i := by simpa [funext_iff] using h
    simp only [h, ↓reduceIte]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- The rows of an LWE sample with a fixed secret are independent. -/
theorem sampleLaw_eq_pi (n m q : ℕ) [Fact (Nat.Prime q)] (noise : PMF (ZMod q))
    (s : Fin n → ZMod q) :
    sampleLaw n m q noise s = PMF.pi fun _ : Fin m => rowLaw n q noise s := by
  rw [rowLaw, PMF.pi_bind]
  simp only [PMF.pi_bind (fun _ => noise), pi_pure]
  rw [PMF.pi_uniformOfFintype]
  rfl

/-- Number of samples used by `reduceSearchToDecision`: `N` blocks of `m` samples for each of
the `n * q + 1` estimators. -/
def searchSamples (n q N m : ℕ) : ℕ := (n * q + 1) * N * m

/-- Row `i` of block `t` of estimator `o` among the `searchSamples n q N m` samples. -/
noncomputable def blockRow (n q N m : ℕ) [Fact (Nat.Prime q)] :
    (Option (Fin n × ZMod q) × Fin N) × Fin m ≃ Fin (searchSamples n q N m) :=
  Fintype.equivFinOfCardEq (by simp [searchSamples, ZMod.card])

/-- Block `t` of estimator `o` of a sample with `searchSamples n q N m` rows. -/
noncomputable def sampleBlock {n q N m : ℕ} [Fact (Nat.Prime q)]
    (P : Matrix (Fin (searchSamples n q N m)) (Fin (n + 1)) (ZMod q))
    (o : Option (Fin n × ZMod q)) (t : Fin N) : Matrix (Fin m) (Fin (n + 1)) (ZMod q) :=
  fun i => P (blockRow n q N m ((o, t), i))

private theorem pi_map_sampleBlock {n q N m : ℕ} [Fact (Nat.Prime q)]
    (μ : PMF (Fin (n + 1) → ZMod q)) :
    (PMF.pi fun _ : Fin (searchSamples n q N m) => μ).map sampleBlock =
      PMF.pi fun _ : Option (Fin n × ZMod q) => PMF.pi fun _ : Fin N =>
        PMF.pi fun _ : Fin m => μ := by
  let reindex (b : Fin (searchSamples n q N m) → Fin (n + 1) → ZMod q)
      (k : (Option (Fin n × ZMod q) × Fin N) × Fin m) : Fin (n + 1) → ZMod q :=
    b (blockRow n q N m k)
  have h : (PMF.pi fun _ : Fin (searchSamples n q N m) => μ).map sampleBlock =
      (((PMF.pi fun _ : Fin (searchSamples n q N m) => μ).map reindex).map
        Function.curry).map Function.curry := by
    rw [PMF.map_comp, PMF.map_comp]
    rfl
  refine h.trans ?_
  rw [PMF.pi_map_comp_equiv, PMF.pi_map_curry, PMF.pi_map_curry]

/-- With secret `s`, the blocks of a `searchSamples n q N m`-row sample are independent
`m`-row samples. -/
theorem sampleLaw_map_sampleBlock {n q N m : ℕ} [Fact (Nat.Prime q)] (noise : PMF (ZMod q))
    (s : Fin n → ZMod q) :
    (sampleLaw n (searchSamples n q N m) q noise s).map sampleBlock =
      PMF.pi fun _ : Option (Fin n × ZMod q) => PMF.pi fun _ : Fin N =>
        sampleLaw n m q noise s := by
  rw [sampleLaw_eq_pi, pi_map_sampleBlock, sampleLaw_eq_pi]
  rfl

/-- Run every estimator's trials, each on its own block. -/
noncomputable def runTrials {n m q N : ℕ} [Fact (Nat.Prime q)]
    (distinguisher : Matrix (Fin m) (Fin (n + 1)) (ZMod q) → ProbComp Bool)
    (P : Matrix (Fin (searchSamples n q N m)) (Fin (n + 1)) (ZMod q)) :
    ProbComp (Option (Fin n × ZMod q) → Fin N → Bool) :=
  sampleEach fun o => sampleEach fun t => estimatorTrial distinguisher o (sampleBlock P o t)

/-- On a sample with secret `s`, all trials are independent with their estimators' laws. -/
theorem sampleLaw_bind_runTrials {n m q N : ℕ} [Fact (Nat.Prime q)] (noise : PMF (ZMod q))
    (distinguisher : Matrix (Fin m) (Fin (n + 1)) (ZMod q) → ProbComp Bool)
    (s : Fin n → ZMod q) :
    (sampleLaw n (searchSamples n q N m) q noise s).bind
        (fun P => eval (runTrials (N := N) distinguisher P)) =
      PMF.pi fun o => PMF.pi fun _ : Fin N => estimatorLaw noise distinguisher s o := by
  have hinner (o : Option (Fin n × ZMod q)) :
      (PMF.pi fun _ : Fin N => sampleLaw n m q noise s).bind
          (fun B => PMF.pi fun t => eval (estimatorTrial distinguisher o (B t))) =
        PMF.pi fun _ : Fin N => estimatorLaw noise distinguisher s o := by
    have h := PMF.pi_bind (fun _ : Fin N => sampleLaw n m q noise s)
      (fun _ P => eval (estimatorTrial distinguisher o P))
    simp only [sampleLaw_bind_estimatorTrial] at h
    exact h.symm
  have houter := PMF.pi_bind
    (fun _ : Option (Fin n × ZMod q) => PMF.pi fun _ : Fin N => sampleLaw n m q noise s)
    (fun o B => PMF.pi fun t => eval (estimatorTrial distinguisher o (B t)))
  simp only [hinner] at houter
  simp only [runTrials, eval_sampleEach]
  rw [houter, ← sampleLaw_map_sampleBlock, PMF.bind_map]
  rfl

/-! ### Choosing the secret from the counts -/

/-- The number of accepting trials. -/
def trueCount {N : ℕ} (x : Fin N → Bool) : ℕ := (Finset.univ.filter fun t => x t = true).card

/-- For coordinate `j`, a guess `g` whose acceptance count is farthest from the count of the
uniform estimator `none`. -/
noncomputable def guessSecret {n q N : ℕ} [Fact (Nat.Prime q)]
    (X : Option (Fin n × ZMod q) → Fin N → Bool) (j : Fin n) : ZMod q :=
  Classical.choose (Finset.exists_max_image Finset.univ
    (fun g : ZMod q => |(trueCount (X (some (j, g))) : ℤ) - trueCount (X none)|)
    Finset.univ_nonempty)

/-- `guessSecret` maximizes the distance from the uniform estimator's count. -/
theorem abs_sub_le_guessSecret {n q N : ℕ} [Fact (Nat.Prime q)]
    (X : Option (Fin n × ZMod q) → Fin N → Bool) (j : Fin n) (g : ZMod q) :
    |(trueCount (X (some (j, g))) : ℝ) - trueCount (X none)| ≤
      |(trueCount (X (some (j, guessSecret X j))) : ℝ) - trueCount (X none)| := by
  have h := (Classical.choose_spec (Finset.exists_max_image Finset.univ
    (fun g : ZMod q => |(trueCount (X (some (j, g))) : ℤ) - trueCount (X none)|)
    Finset.univ_nonempty)).2 g (Finset.mem_univ g)
  simp only [guessSecret]
  exact_mod_cast h

/-- If every count is within `N * |pR - pU| / 4` of its mean, where correct guesses have mean
`N * pR` and the uniform estimator and wrong guesses have mean `N * pU`, then `guessSecret`
returns the secret. -/
theorem guessSecret_eq_of_close {n q N : ℕ} [Fact (Nat.Prime q)]
    (X : Option (Fin n × ZMod q) → Fin N → Bool) (s : Fin n → ZMod q) {pR pU : ℝ}
    (hnone : |(trueCount (X none) : ℝ) - N * pU| < N * |pR - pU| / 4)
    (hsome : ∀ j g, |(trueCount (X (some (j, g))) : ℝ) - N * (if g = s j then pR else pU)| <
      N * |pR - pU| / 4) :
    guessSecret X = s := by
  funext j
  by_contra hne
  have hc := hsome j (s j)
  have hw := hsome j (guessSecret X j)
  simp only [↓reduceIte] at hc
  simp only [hne, ↓reduceIte] at hw
  have hmax := abs_sub_le_guessSecret X j (s j)
  set cU := (trueCount (X none) : ℝ)
  set cR := (trueCount (X (some (j, s j))) : ℝ)
  set cW := (trueCount (X (some (j, guessSecret X j))) : ℝ)
  have hN : |(N : ℝ) * pR - N * pU| = N * |pR - pU| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
  have h1 : |cW - cU| ≤ |cW - N * pU| + |cU - N * pU| := by
    rw [abs_sub_comm cU]
    exact abs_sub_le _ _ _
  have h2 : |(N : ℝ) * pR - N * pU| ≤ |cR - N * pR| + |cR - cU| + |cU - N * pU| := by
    rw [abs_sub_comm cR (N * pR)]
    calc |(N : ℝ) * pR - N * pU| ≤ |N * pR - cR| + |cR - N * pU| := abs_sub_le _ _ _
      _ ≤ |N * pR - cR| + (|cR - cU| + |cU - N * pU|) := by gcongr; exact abs_sub_le _ _ _
      _ = _ := by ring
  linarith

private theorem pi_trueCount_far_le {N : ℕ} (μ : PMF Bool) {ε : ℝ} (hε : 0 ≤ ε) :
    ((PMF.pi fun _ : Fin N => μ).toOuterMeasure
      {x | ε ≤ |(trueCount x : ℝ) - N * (μ true).toReal|}).toReal ≤
        2 * Real.exp (-2 * ε ^ 2 / N) := by
  have h := PMF.pi_sum_abs_sub_mean_ge (fun _ : Fin N => μ)
    (fun _ b => if b then (1 : ℝ) else 0) (bound := 1) zero_le_one
    (fun _ b _ => by cases b <;> simp) hε
  have hsum (x : Fin N → Bool) : ∑ i, (if x i then (1 : ℝ) else 0) = trueCount x := by
    simp [trueCount, Finset.sum_boole]
  have hmean : ∑ _i : Fin N, ∑ a : Bool, (μ a).toReal * (if a then (1 : ℝ) else 0) =
      N * (μ true).toReal := by
    simp
  simp only [hsum, hmean, Fintype.card_fin, one_pow, mul_one] at h
  exact h

/-- When the trials are drawn from their estimators' laws, `guessSecret` misses the secret with
probability at most `(n * q + 1) * 2 * exp (-N * |pR - pU| ^ 2 / 8)`. -/
theorem pi_estimatorLaw_guessSecret_ne_le {n m q : ℕ} [Fact (Nat.Prime q)] (N : ℕ)
    (noise : PMF (ZMod q))
    (distinguisher : Matrix (Fin m) (Fin (n + 1)) (ZMod q) → ProbComp Bool)
    (s : Fin n → ZMod q) :
    ((PMF.pi fun o => PMF.pi fun _ : Fin N => estimatorLaw noise distinguisher s o).toOuterMeasure
        {X | guessSecret X ≠ s}).toReal ≤
      (n * q + 1) * (2 * Real.exp (-(N * |(realLaw noise distinguisher true).toReal -
        (uniformLaw distinguisher true).toReal| ^ 2) / 8)) := by
  set pR := (realLaw noise distinguisher true).toReal
  set pU := (uniformLaw distinguisher true).toReal
  set μ := PMF.pi fun o => PMF.pi fun _ : Fin N => estimatorLaw noise distinguisher s o
  let p (o : Option (Fin n × ZMod q)) : ℝ := (estimatorLaw noise distinguisher s o true).toReal
  let E (o : Option (Fin n × ZMod q)) : Set (Option (Fin n × ZMod q) → Fin N → Bool) :=
    {X | N * |pR - pU| / 4 ≤ |(trueCount (X o) : ℝ) - N * p o|}
  have hsub : {X | guessSecret X ≠ s} ⊆ ⋃ o ∈ Finset.univ, E o := by
    intro X hX
    by_contra hnot
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_const, not_exists, Set.mem_ofPred_eq,
      not_le, E] at hnot
    apply hX
    refine guessSecret_eq_of_close X s (pR := pR) (pU := pU) ?_ fun j g => ?_
    · simpa [p, estimatorLaw] using hnot none
    · by_cases hg : g = s j <;> simpa [p, estimatorLaw, hg] using hnot (some (j, g))
  have hE (o : Option (Fin n × ZMod q)) :
      (μ.toOuterMeasure (E o)).toReal ≤ 2 * Real.exp (-(N * |pR - pU| ^ 2) / 8) := by
    have hmap : μ.toOuterMeasure (E o) =
        (PMF.pi fun _ : Fin N => estimatorLaw noise distinguisher s o).toOuterMeasure
          {x | N * |pR - pU| / 4 ≤ |(trueCount x : ℝ) - N * p o|} := by
      rw [← PMF.pi_map_eval
        (fun o => PMF.pi fun _ : Fin N => estimatorLaw noise distinguisher s o) o,
        PMF.toOuterMeasure_map_apply]
      rfl
    rw [hmap]
    refine (pi_trueCount_far_le _ (by positivity)).trans (le_of_eq ?_)
    congr 2
    rcases Nat.eq_zero_or_pos N with hN | hN
    · simp [hN]
    · have : (N : ℝ) ≠ 0 := by positivity
      field_simp
      ring
  calc (μ.toOuterMeasure {X | guessSecret X ≠ s}).toReal
      ≤ (μ.toOuterMeasure (⋃ o ∈ Finset.univ, E o)).toReal :=
        ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top _ _) (MeasureTheory.measure_mono hsub)
    _ ≤ ∑ o, (μ.toOuterMeasure (E o)).toReal :=
        PMF.toOuterMeasure_toReal_biUnion_finset_le μ Finset.univ E
    _ ≤ ∑ _o : Option (Fin n × ZMod q), 2 * Real.exp (-(N * |pR - pU| ^ 2) / 8) :=
        Finset.sum_le_sum fun o _ => hE o
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_option, Fintype.card_prod,
          Fintype.card_fin, ZMod.card, nsmul_eq_mul]
        push_cast
        ring

/-! ### The search reduction -/

/-- Regev's search-to-decision reduction on `searchSamples n q N m` samples: decode the sample,
run `N` trials of every estimator on its own `m`-row blocks, each with the decision adversary
on encoded matrices, and output the guessed secret. -/
noncomputable def reduceSearchToDecision {n m q : ℕ} [Fact (Nat.Prime q)] (N : ℕ)
    (adversary : List Bool → ProbComp Bool) (word : List Bool) : ProbComp (List Bool) := do
  let X ← runTrials (N := N) (fun M => adversary (encMatrix m (n + 1) q M))
    (decodeMatrix (searchSamples n q N m) (n + 1) q word)
  return encZModVec n q (guessSecret X)

private theorem searchGame_reduceSearchToDecision {n m q : ℕ} [Fact (Nat.Prime q)]
    (noise : PMF (ZMod q)) (adversary : List Bool → ProbComp Bool) (N : ℕ) :
    searchGame n (searchSamples n q N m) q noise
        (reduceSearchToDecision (n := n) (m := m) (q := q) N adversary) =
      (PMF.uniformOfFintype (Fin n → ZMod q)).bind fun s =>
        (PMF.pi fun o => PMF.pi fun _ : Fin N =>
          estimatorLaw noise (fun M => adversary (encMatrix m (n + 1) q M)) s o).bind fun X =>
            PMF.pure (decide (guessSecret X = s)) := by
  simp only [searchGame, reduceSearchToDecision, decodeMatrix_encMatrix, pmf_norm,
    EmbeddingLike.apply_eq_iff_eq]
  congr 1
  funext s
  rw [← sampleLaw_bind_runTrials]
  simp only [sampleLaw, pmf_norm]

/-- **Search to decision for prime-modulus LWE.** From a decision-LWE adversary with advantage
`ε` on `m` samples, `reduceSearchToDecision` finds the secret from `(n * q + 1) * N * m` samples
with probability at least `1 - (n * q + 1) * 2 * exp (-N * ε ^ 2 / 8)`. -/
theorem searchToDecision {n m q : ℕ} [Fact (Nat.Prime q)] {noise : PMF (ZMod q)}
    (adversary : List Bool → ProbComp Bool) (N : ℕ) :
    1 - (n * q + 1) * (2 * Real.exp (-(N * (Game.advantage
        (distinguishingGame
          (realEnsemble (fun _ => n) (fun _ => m) (fun _ => q) (fun _ => noise) 0) adversary)
        (distinguishingGame (uniformEnsemble (fun _ => n) (fun _ => m) (fun _ => q) 0)
          adversary) : ℝ) ^ 2) / 8)) ≤
      Game.succProbability (searchGame n (searchSamples n q N m) q noise
        (reduceSearchToDecision (n := n) (m := m) (q := q) N adversary)) := by
  set D := fun M : Matrix (Fin m) (Fin (n + 1)) (ZMod q) => adversary (encMatrix m (n + 1) q M)
  have hR : distinguishingGame
      (realEnsemble (fun _ => n) (fun _ => m) (fun _ => q) (fun _ => noise) 0) adversary =
        realLaw noise D := by
    simp only [distinguishingGame, realEnsemble, realLaw, pmf_norm]
    rfl
  have hU : distinguishingGame (uniformEnsemble (fun _ => n) (fun _ => m) (fun _ => q) 0)
      adversary = uniformLaw D := by
    simp only [distinguishingGame, uniformEnsemble, uniformLaw, pmf_norm]
    rfl
  rw [Game.coe_advantage, Game.coe_succProbability, Game.coe_succProbability, hR, hU,
    Game.coe_succProbability]
  set B := (n * q + 1) * (2 * Real.exp (-(N * |(realLaw noise D true).toReal -
    (uniformLaw D true).toReal| ^ 2) / 8))
  have hB : 0 ≤ B := by positivity
  set game := searchGame n (searchSamples n q N m) q noise
    (reduceSearchToDecision (n := n) (m := m) (q := q) N adversary)
  have hfalse : game false ≤ ENNReal.ofReal B := by
    rw [show game = _ from searchGame_reduceSearchToDecision (m := m) noise adversary N]
    refine PMF.bind_apply_le_on_support _ fun s _ => ?_
    have hmap {α : Type} (μ : PMF α) (f : α → Bool) :
        μ.bind (fun X => PMF.pure (f X)) = μ.map f := rfl
    rw [hmap, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      ENNReal.le_ofReal_iff_toReal_le (PMF.toOuterMeasure_ne_top _ _) hB]
    convert pi_estimatorLaw_guessSecret_ne_le N noise D s using 3
    ext X
    simp
  have h := PMF.toReal_false_eq_one_sub game
  have h' := ENNReal.toReal_le_of_le_ofReal hB hfalse
  linarith

end Cslib.Crypto.PrimeLWE
