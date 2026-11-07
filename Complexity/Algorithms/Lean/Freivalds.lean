/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Basic
public import Complexity.Probability.Freivalds
public import Cslib.Algorithms.Lean.TimeM

/-!
# Freivalds' Matrix-Product Verification

Freivalds' algorithm (`[Freivalds1979]`; `[MitzenmacherUpfal2017]`, Section 1.3;
`[MotwaniRaghavan1995]`, Section 7.1) checks a claimed product `A * B = C` without multiplying
matrices. It draws random vectors `x` and accepts when `A *ᵥ (B *ᵥ x) = C *ᵥ x` for every
drawn vector. Each check uses three matrix-vector products and one vector comparison.

This module implements the check in `Cslib.Algorithms.Lean.TimeM` (`checkM`, `checkAllM`). It
then defines the randomized verifier `verify` as a `ProbComp` that samples the vectors uniformly
and runs `checkAllM`. Entries of `x` are drawn from a finite set `S` and encoded in the ring by
`e : S → R`. The analysis needs only that every nonzero `d` makes `s ↦ d * e s` injective (see
`Cslib.Probability.card_filter_mulVec_eq_mul_card_le`).

## Source Conventions

* **Matrices:** `A : Matrix (Fin l) (Fin m) R`, `B : Matrix (Fin m) (Fin n) R` and
  `C : Matrix (Fin l) (Fin n) R` are rectangular over any ring `R` with decidable equality,
  rather than the square matrices of `[MitzenmacherUpfal2017]`, Theorem 1.4.
* **Random vectors:** `verify e k` draws all `k` vectors `Fin k → Fin n → S` from one uniform
  law. This is the product of `k` independent uniform vectors.
* **Error:** one-sided. A correct product is accepted with probability `1`
  (`eval_verify_of_mul_eq`). An incorrect product is accepted with probability at most
  `(1/|S|)^k` (`eval_verify_true_le`): `(1/2)^k` for `0`/`1` vectors over any ring
  (`eval_verify_bool_true_le`, the case `k = 1` being `[MitzenmacherUpfal2017]`, Theorem 1.4),
  and `(1/|F|)^k` for uniform vectors over a finite field (`eval_verify_field_true_le`).

## Cost Model

* **Charged (`TimeM` ticks):** `2` per entry of a dot product (one ring multiplication and one
  ring addition), and `1` per entry of a vector equality comparison.
* **Uncharged:** reading matrix and vector entries, loop and recursion control, building result
  vectors, sampling the random vectors, and the encoding `e`. Ring operations have unit cost
  regardless of the size of their operands.

Under this model one check costs exactly `2 * (m * n + l * m + l * n) + l` (`time_checkM`), and
`k` checks cost `k` times as much (`time_checkAllM`). For square `n × n` matrices this is
`k * (6 * n ^ 2 + n)` (`time_checkAllM_square`). For comparison, computing `A * B` from the
definition takes `n ^ 2` dot products of length `n`, that is `2 * n ^ 3` operations under the same
model; this comparison is not formalized here. The verifier compares the result vectors in full
and checks all `k` vectors, so each bound is an exact cost rather than a worst case.

## Main definitions

* `Cslib.Algorithms.Lean.Freivalds.dotProductM`, `mulVecM`, `vecEqM`: costed dot product,
  matrix-vector product and vector comparison.
* `Cslib.Algorithms.Lean.Freivalds.checkM`: one deterministic check `A *ᵥ (B *ᵥ x) = C *ᵥ x`.
* `Cslib.Algorithms.Lean.Freivalds.checkAllM`: the check on each of `k` vectors.
* `Cslib.Algorithms.Lean.Freivalds.verify`: the randomized verifier with `k` uniform vectors.
* `Cslib.Algorithms.Lean.Freivalds.bit`: the `0`/`1` encoding of a bit in a ring.

## Main results

* `ret_checkM`, `time_checkM`, `ret_checkAllM`, `time_checkAllM`: exact results and costs.
* `eval_verify_of_mul_eq`: perfect completeness.
* `eval_verify_true_le`: soundness error at most `(1/|S|)^k` for any admissible encoding.
* `eval_verify_bool_true_le`: soundness error at most `(1/2)^k` for `0`/`1` vectors.
* `eval_verify_field_true_le`: soundness error at most `(1/|F|)^k` over a finite field `F`.

## References

* [R. Freivalds, *Fast probabilistic algorithms*][Freivalds1979]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
* [R. Motwani and P. Raghavan, *Randomized Algorithms*][MotwaniRaghavan1995]
-/

public section

namespace Cslib.Algorithms.Lean.Freivalds

open scoped Matrix ENNReal
open Cslib.Probability

variable {R : Type} [Ring R]

/-- The dot product of two length-`k` vectors, charging `2` (one multiplication and one
addition) per entry. -/
def dotProductM : (k : ℕ) → (Fin k → R) → (Fin k → R) → TimeM ℕ R
  | 0, _, _ => pure 0
  | k + 1, u, v => do
    let rest ← dotProductM k (Fin.tail u) (Fin.tail v)
    TimeM.tick 2
    pure (u 0 * v 0 + rest)

@[simp] theorem ret_dotProductM (k : ℕ) (u v : Fin k → R) :
    (dotProductM k u v).ret = u ⬝ᵥ v := by
  induction k with
  | zero => simp [dotProductM, dotProduct]
  | succ k ih =>
    simp only [dotProductM, TimeM.ret_bind, TimeM.ret_pure, ih, dotProduct, Fin.sum_univ_succ]
    rfl

@[simp] theorem time_dotProductM (k : ℕ) (u v : Fin k → R) :
    (dotProductM k u v).time = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [dotProductM, TimeM.time_bind, TimeM.time_pure, TimeM.time_tick, ih]
    ring

/-- Matrix-vector multiplication, one dot product per row. -/
def mulVecM {k : ℕ} : (l : ℕ) → Matrix (Fin l) (Fin k) R → (Fin k → R) → TimeM ℕ (Fin l → R)
  | 0, _, _ => pure Fin.elim0
  | l + 1, M, v => do
    let first ← dotProductM k (M 0) v
    let rest ← mulVecM l (M.submatrix Fin.succ id) v
    pure (Fin.cons first rest)

@[simp] theorem ret_mulVecM {k : ℕ} (l : ℕ) (M : Matrix (Fin l) (Fin k) R) (v : Fin k → R) :
    (mulVecM l M v).ret = M *ᵥ v := by
  induction l with
  | zero => funext i; exact i.elim0
  | succ l ih =>
    simp only [mulVecM, TimeM.ret_bind, TimeM.ret_pure, ih, ret_dotProductM]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · rfl

@[simp] theorem time_mulVecM {k : ℕ} (l : ℕ) (M : Matrix (Fin l) (Fin k) R) (v : Fin k → R) :
    (mulVecM l M v).time = 2 * k * l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    simp only [mulVecM, TimeM.time_bind, TimeM.time_pure, ih, time_dotProductM]
    ring

section Check

variable [DecidableEq R]

omit [Ring R] in
/-- Compare two length-`l` vectors entry by entry, charging `1` per entry. -/
def vecEqM : (l : ℕ) → (Fin l → R) → (Fin l → R) → TimeM ℕ Bool
  | 0, _, _ => pure true
  | l + 1, u, v => do
    let rest ← vecEqM l (Fin.tail u) (Fin.tail v)
    TimeM.tick 1
    pure (decide (u 0 = v 0) && rest)

omit [Ring R] in
@[simp] theorem ret_vecEqM (l : ℕ) (u v : Fin l → R) :
    (vecEqM l u v).ret = decide (u = v) := by
  induction l with
  | zero => simp [vecEqM, Subsingleton.elim u v]
  | succ l ih =>
    simp only [vecEqM, TimeM.ret_bind, TimeM.ret_pure, ih, ← Bool.decide_and]
    congr 1
    exact propext ⟨fun ⟨h0, ht⟩ => funext fun i => Fin.cases h0 (fun i => congrFun ht i) i,
      fun h => ⟨congrFun h 0, by rw [h]⟩⟩

omit [Ring R] in
@[simp] theorem time_vecEqM (l : ℕ) (u v : Fin l → R) : (vecEqM l u v).time = l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    simp only [vecEqM, TimeM.time_bind, TimeM.time_pure, TimeM.time_tick, ih, add_zero]

variable {l m n : ℕ}

/-- One deterministic Freivalds check: compute `y = B *ᵥ x`, `z = A *ᵥ y` and `w = C *ᵥ x`, and
compare `z` with `w`. -/
def checkM (A : Matrix (Fin l) (Fin m) R) (B : Matrix (Fin m) (Fin n) R)
    (C : Matrix (Fin l) (Fin n) R) (x : Fin n → R) : TimeM ℕ Bool := do
  let y ← mulVecM m B x
  let z ← mulVecM l A y
  let w ← mulVecM l C x
  vecEqM l z w

@[simp] theorem ret_checkM (A : Matrix (Fin l) (Fin m) R) (B : Matrix (Fin m) (Fin n) R)
    (C : Matrix (Fin l) (Fin n) R) (x : Fin n → R) :
    (checkM A B C x).ret = decide ((A * B) *ᵥ x = C *ᵥ x) := by
  simp only [checkM, TimeM.ret_bind, ret_mulVecM, ret_vecEqM, Matrix.mulVec_mulVec]

/-- One check costs `2 * (m * n + l * m + l * n) + l`, independently of the vector. -/
@[simp] theorem time_checkM (A : Matrix (Fin l) (Fin m) R) (B : Matrix (Fin m) (Fin n) R)
    (C : Matrix (Fin l) (Fin n) R) (x : Fin n → R) :
    (checkM A B C x).time = 2 * (m * n + l * m + l * n) + l := by
  simp only [checkM, TimeM.time_bind, time_mulVecM, time_vecEqM]
  ring

/-- Run `checkM` on each of `k` vectors and accept when every check accepts. All `k` checks are
performed, so the cost is exact. -/
def checkAllM (A : Matrix (Fin l) (Fin m) R) (B : Matrix (Fin m) (Fin n) R)
    (C : Matrix (Fin l) (Fin n) R) : (k : ℕ) → (Fin k → Fin n → R) → TimeM ℕ Bool
  | 0, _ => pure true
  | k + 1, xs => do
    let first ← checkM A B C (xs 0)
    let rest ← checkAllM A B C k (Fin.tail xs)
    pure (first && rest)

@[simp] theorem ret_checkAllM (A : Matrix (Fin l) (Fin m) R) (B : Matrix (Fin m) (Fin n) R)
    (C : Matrix (Fin l) (Fin n) R) (k : ℕ) (xs : Fin k → Fin n → R) :
    (checkAllM A B C k xs).ret = decide (∀ t, (A * B) *ᵥ xs t = C *ᵥ xs t) := by
  induction k with
  | zero => simp [checkAllM]
  | succ k ih =>
    simp only [checkAllM, TimeM.ret_bind, TimeM.ret_pure, ret_checkM, ih, ← Bool.decide_and,
      Fin.forall_fin_succ]
    rfl

/-- `k` checks cost `k * (2 * (m * n + l * m + l * n) + l)`. -/
@[simp] theorem time_checkAllM (A : Matrix (Fin l) (Fin m) R) (B : Matrix (Fin m) (Fin n) R)
    (C : Matrix (Fin l) (Fin n) R) (k : ℕ) (xs : Fin k → Fin n → R) :
    (checkAllM A B C k xs).time = k * (2 * (m * n + l * m + l * n) + l) := by
  induction k with
  | zero => simp only [checkAllM, TimeM.time_pure, zero_mul]
  | succ k ih =>
    simp only [checkAllM, TimeM.time_bind, TimeM.time_pure, time_checkM, ih]
    ring

/-- For square `n × n` matrices, `k` checks cost `k * (6 * n ^ 2 + n)`. -/
theorem time_checkAllM_square (A B C : Matrix (Fin n) (Fin n) R) (k : ℕ)
    (xs : Fin k → Fin n → R) :
    (checkAllM A B C k xs).time = k * (6 * n ^ 2 + n) := by
  rw [time_checkAllM]
  ring

/-- Freivalds' randomized verifier: draw `k` independent uniform vectors in `Fin n → S`, encode
their entries with `e`, and run `checkAllM`. -/
noncomputable def verify {S : Type} [Fintype S] [Nonempty S] (e : S → R) (k : ℕ)
    (A : Matrix (Fin l) (Fin m) R) (B : Matrix (Fin m) (Fin n) R)
    (C : Matrix (Fin l) (Fin n) R) : ProbComp Bool := do
  let xs ← ProbComp.uniform (Fin k → Fin n → S)
  pure (checkAllM A B C k fun t => e ∘ xs t).ret

variable {S : Type} [Fintype S] [Nonempty S]

theorem eval_verify (e : S → R) (k : ℕ) (A : Matrix (Fin l) (Fin m) R)
    (B : Matrix (Fin m) (Fin n) R) (C : Matrix (Fin l) (Fin n) R) :
    ProbComp.eval (verify e k A B C) = (PMF.uniformOfFintype (Fin k → Fin n → S)).map
      fun xs => decide (∀ t, (A * B) *ᵥ (e ∘ xs t) = C *ᵥ (e ∘ xs t)) := by
  simp only [verify, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure, ret_checkAllM]
  rfl

/-- Perfect completeness: a correct product is always accepted. -/
theorem eval_verify_of_mul_eq (e : S → R) (k : ℕ) {A : Matrix (Fin l) (Fin m) R}
    {B : Matrix (Fin m) (Fin n) R} {C : Matrix (Fin l) (Fin n) R} (h : A * B = C) :
    ProbComp.eval (verify e k A B C) = PMF.pure true := by
  simp only [eval_verify, h, implies_true, decide_true]
  exact PMF.map_const _ _

/-- Soundness: if `A * B ≠ C`, the verifier accepts with probability at most `(1/|S|)^k`. -/
theorem eval_verify_true_le {e : S → R}
    (he : ∀ d : R, d ≠ 0 → Function.Injective fun s => d * e s) (k : ℕ)
    {A : Matrix (Fin l) (Fin m) R} {B : Matrix (Fin m) (Fin n) R}
    {C : Matrix (Fin l) (Fin n) R} (h : A * B ≠ C) :
    ProbComp.eval (verify e k A B C) true ≤ ((Fintype.card S : ℝ≥0∞)⁻¹) ^ k := by
  have hbound := toOuterMeasure_forall_mulVec_eq_le (κ := Fin k) (S := S) he h
  rw [Fintype.card_fin] at hbound
  rw [eval_verify, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  convert hbound using 2
  ext xs
  simp only [Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq, Set.mem_ofPred_eq]

end Check

/-- The `0`/`1` encoding of a bit in a ring. -/
def bit (b : Bool) : R := if b then 1 else 0

variable [DecidableEq R] {l m n : ℕ}

/-- Freivalds' verifier with `0`/`1` vectors accepts an incorrect product with probability at
most `(1/2)^k`. The case `k = 1` is `[MitzenmacherUpfal2017]`, Theorem 1.4. -/
theorem eval_verify_bool_true_le (k : ℕ) {A : Matrix (Fin l) (Fin m) R}
    {B : Matrix (Fin m) (Fin n) R} {C : Matrix (Fin l) (Fin n) R} (h : A * B ≠ C) :
    ProbComp.eval (verify bit k A B C) true ≤ 2⁻¹ ^ k := by
  have := eval_verify_true_le (S := Bool) (e := bit) injective_mul_boolIndicator k h
  rwa [Fintype.card_bool, Nat.cast_ofNat] at this

/-- Over a finite field with uniform vectors, Freivalds' verifier accepts an incorrect product
with probability at most `(1/|F|)^k`. -/
theorem eval_verify_field_true_le {F : Type} [Field F] [Fintype F] [DecidableEq F] (k : ℕ)
    {A : Matrix (Fin l) (Fin m) F} {B : Matrix (Fin m) (Fin n) F}
    {C : Matrix (Fin l) (Fin n) F} (h : A * B ≠ C) :
    ProbComp.eval (verify id k A B C) true ≤ ((Fintype.card F : ℝ≥0∞)⁻¹) ^ k :=
  eval_verify_true_le (fun _ hd => mul_right_injective₀ hd) k h

end Cslib.Algorithms.Lean.Freivalds
