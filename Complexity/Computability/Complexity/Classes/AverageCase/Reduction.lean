/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.AverageCase.Distributional
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts
import Complexity.Probability.PMF.Map
import Complexity.Tactic.PolyTime
import Cslib.Foundations.Data.Polynomial.Monotone

/-!
# Distributional reductions

A distributional reduction from `(L, D)` to `(L', D')` (`Cslib.Complexity.DistReduction`,
[Bogdanov and Trevisan, Definition 17][BogdanovTrevisan2006]) is a polynomial-time map `f` that
is correct on the support of `D` and whose image distribution is **dominated** by `D'`: for a
length map `m` and a polynomial `p`, every word `y` satisfies
`Pr_{x ~ D_n}[f x = y] ≤ p(n) · D'_{m(n)}(y)`.

The source imposes the domination inequality only on the support of `D'_{m(n)}`. Here it is
required at every word. By `Cslib.Probability.PMF.forall_map_apply_le_mul_iff`, this is
exactly the source's condition together with `f (Supp D_n) ⊆ Supp D'_{m(n)}`
(`Cslib.Complexity.DistReduction.mem_support`). The source's proof of closure (Lemma 18) uses
that inclusion when it applies the correctness of the target algorithm to `f x`, and without it
the closure fails. For example, take `D'_n` to be the point mass at `0^n` and
`L' = {x ++ [true] | x ∈ L}`. Then `f x = x ++ [true]` is correct for every `L` and satisfies the
source's domination vacuously, while `(L', D')` is in `AvgP` (answer "no" on all inputs); so every
`(L, D)` would be in `AvgP`. The bounded-halting reduction proving `DistNP`-completeness
[Bogdanov and Trevisan, Theorem 19][BogdanovTrevisan2006] satisfies the strengthened condition:
it is injective on the support of `D_n` and the source bounds `D_n(x)` by a polynomial multiple of
the target probability of `f x` for every `x` in that support, so the image probability of every
word is either `D_n(x)` for its unique preimage `x` in the support, or `0`. The source takes `m`
to be a polynomial; here `m` is arbitrary and a polynomial bound on it follows from the running
time of `f` (`Cslib.Complexity.DistReduction.exists_m_le`).

Reductions preserve the average-case classes
[Bogdanov and Trevisan, Lemma 18][BogdanovTrevisan2006]: a scheme for the target with confidence
parameter `p(n) · (k + 1)` composed with `f` is a scheme for the source with confidence parameter
`k`. For single algorithms the failure bound transfers quantitatively, from `δ` to
`n ↦ p(n) · δ(m(n))`.

## Main definitions

* `Cslib.Complexity.DistReduction`, `Cslib.Complexity.DistReducible`.
* `Cslib.Complexity.DistHard`, `Cslib.Complexity.DistComplete`: hardness and completeness for a
  class of distributional problems under distributional reductions.

## Main results

* `Cslib.Complexity.DistReduction.toOuterMeasure_preimage_le`: domination of events.
* `Cslib.Complexity.DistReduction.mem_support`: reductions preserve supports.
* `Cslib.Complexity.DistReduction.exists_m_le`: the length map is polynomially bounded.
* `Cslib.Complexity.DistReduction.mem_AvgP`, `Cslib.Complexity.DistReduction.mem_HeurP`:
  closure of `AvgP` and `HeurP` under reductions
  [Bogdanov and Trevisan, Lemma 18][BogdanovTrevisan2006].
* `Cslib.Complexity.DistReduction.mem_AvgDeltaP`, `Cslib.Complexity.DistReduction.mem_HeurDeltaP`:
  the quantitative versions for `Avg_δ P` and `Heur_δ P`.
* `Cslib.Complexity.DistReducible.refl`, `Cslib.Complexity.DistReducible.trans`.
* `Cslib.Complexity.DistComplete.mem_AvgP_iff`: a complete problem is in `AvgP` exactly when the
  whole class is.

## References

* [A. Bogdanov, L. Trevisan, *Average-Case Complexity*][BogdanovTrevisan2006]
* [L. A. Levin, *Average Case Complete Problems*][Levin1986]
-/

public section

namespace Cslib.Complexity

open scoped ENNReal
open Turing.MultiTapeTM

/-- A **distributional reduction** from `L` to `L'`
[Bogdanov and Trevisan, Definition 17][BogdanovTrevisan2006]: a polynomial-time map `f`, correct
on the support of the source ensemble, whose image of `L.ens.dist n` is dominated by `p(n)` times
`L'.ens.dist (m n)` at every word. Domination at every word is the source's condition plus support
preservation (`Cslib.Probability.PMF.forall_map_apply_le_mul_iff`), which closure under
reductions needs; see the module documentation. -/
structure DistReduction (L L' : DistProblem) where
  /-- The reduction map on instances. -/
  f : List Bool → List Bool
  /-- The length of the reduced instances of length-`n` inputs. -/
  m : ℕ → ℕ
  /-- The domination factor. -/
  p : Polynomial ℕ
  /-- The map is computable in polynomial time. -/
  polyTime : ComputableInPolyTime f encBits encBits
  /-- The map is correct on the support of the source ensemble. -/
  correct : ∀ n x, x ∈ (L.ens.dist n).support → (x ∈ L.lang ↔ f x ∈ L'.lang)
  /-- The image distribution is dominated by the target ensemble at length `m n`. -/
  dominates : ∀ n y, (L.ens.dist n).map f y ≤ ((p.eval n : ℕ) : ℝ≥0∞) * L'.ens.dist (m n) y

/-- `L` reduces to `L'` by a distributional reduction. -/
@[expose] def DistReducible (L L' : DistProblem) : Prop := Nonempty (DistReduction L L')

namespace DistReduction

variable {L L' L'' : DistProblem}

/-- Domination extends from words to events. -/
theorem toOuterMeasure_preimage_le (R : DistReduction L L') (n : ℕ) (S : Set (List Bool)) :
    (L.ens.dist n).toOuterMeasure (R.f ⁻¹' S) ≤
      ((R.p.eval n : ℕ) : ℝ≥0∞) * (L'.ens.dist (R.m n)).toOuterMeasure S := by
  rw [← PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply,
    ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun y => ?_
  by_cases hy : y ∈ S
  · simp only [Set.indicator_of_mem hy]
    exact R.dominates n y
  · simp only [Set.indicator_of_notMem hy, mul_zero, le_refl]

/-- A reduction maps the support of the source ensemble into the support of the target. -/
theorem mem_support (R : DistReduction L L') {n : ℕ} {x : List Bool}
    (hx : x ∈ (L.ens.dist n).support) : R.f x ∈ (L'.ens.dist (R.m n)).support :=
  (Probability.PMF.forall_map_apply_le_mul_iff.mp (R.dominates n)).2 x hx

/-- The length map of a reduction is polynomially bounded. -/
theorem exists_m_le (R : DistReduction L L') : ∃ c d : ℕ, ∀ n, R.m n ≤ c * (n + 1) ^ d := by
  obtain ⟨t, s, ht, -, hcomp⟩ := R.polyTime
  obtain ⟨c, d, hle⟩ := polynomiallyBounded_iff_le.mp ht
  refine ⟨c, d, fun n => ?_⟩
  obtain ⟨x, hx⟩ := (L.ens.dist n).support_nonempty
  have hlen := ComputableInTimeAndSpace.length_le hcomp x
  rw [← L'.ens.length_eq _ _ (R.mem_support hx)]
  have hxn := L.ens.length_eq n x hx
  simp only [encBits, Function.Embedding.coe_refl, id_eq] at hlen
  rw [← hxn]
  exact hlen.trans (hle _)

private theorem mul_inv_mul_succ_le (a k : ℕ) :
    (a : ℝ≥0∞) * ((a * (k + 1) + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [ENNReal.le_inv_iff_mul_le, mul_right_comm, ← div_eq_mul_inv]
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul]
  exact_mod_cast Nat.le_succ _

/-- **Closure of `AvgP` under reductions** [Bogdanov and Trevisan, Lemma 18][BogdanovTrevisan2006]:
the scheme `(x, k) ↦ A' (f x, p(|x|) · (k + 1))` is an errorless scheme for the source. -/
theorem mem_AvgP (R : DistReduction L L') (h : L' ∈ AvgP) : L ∈ AvgP := by
  obtain ⟨A', hA'⟩ := h
  have hpt := hA'.polyTime
  have hf := R.polyTime
  refine ⟨fun q => A' (R.f q.1, R.p.eval q.1.length * (q.2 + 1)), ⟨?_, ?_, ?_⟩⟩
  · polytime
  · intro n x k b hx hb
    rw [R.correct n x hx]
    exact hA'.correct _ _ _ b (R.mem_support hx) hb
  · intro n k
    have hset : {x | A' (R.f x, R.p.eval x.length * (k + 1)) = none} ∩
        (L.ens.dist n).support ⊆
        R.f ⁻¹' {y | A' (y, R.p.eval n * (k + 1)) = none} := by
      rintro x ⟨hx, hsupp⟩
      simpa only [Set.mem_preimage, Set.mem_ofPred_eq, L.ens.length_eq n x hsupp] using hx
    refine (PMF.toOuterMeasure_mono _ hset).trans ((R.toOuterMeasure_preimage_le n _).trans ?_)
    exact (mul_le_mul' le_rfl (hA'.failure_le _ _)).trans (mul_inv_mul_succ_le _ _)

/-- **Closure of `HeurP` under reductions** [Bogdanov and Trevisan, Lemma 18][BogdanovTrevisan2006]:
the scheme `(x, k) ↦ A' (f x, p(|x|) · (k + 1))` is a heuristic scheme for the source. -/
theorem mem_HeurP (R : DistReduction L L') (h : L' ∈ HeurP) : L ∈ HeurP := by
  obtain ⟨A', hA'⟩ := h
  have hpt := hA'.polyTime
  have hf := R.polyTime
  refine ⟨fun q => A' (R.f q.1, R.p.eval q.1.length * (q.2 + 1)), ⟨?_, ?_⟩⟩
  · polytime
  · intro n k
    have hset : {x | ¬(A' (R.f x, R.p.eval x.length * (k + 1)) = true ↔ x ∈ L.lang)} ∩
        (L.ens.dist n).support ⊆
        R.f ⁻¹' {y | ¬(A' (y, R.p.eval n * (k + 1)) = true ↔ y ∈ L'.lang)} := by
      rintro x ⟨hx, hsupp⟩
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, L.ens.length_eq n x hsupp] at hx ⊢
      rwa [← R.correct n x hsupp]
    refine (PMF.toOuterMeasure_mono _ hset).trans ((R.toOuterMeasure_preimage_le n _).trans ?_)
    exact (mul_le_mul' le_rfl (hA'.error_le _ _)).trans (mul_inv_mul_succ_le _ _)

/-- Reductions transfer errorless heuristic algorithms, multiplying the failure bound by the
domination factor: `δ` becomes `n ↦ p(n) · δ(m(n))`. -/
theorem mem_AvgDeltaP (R : DistReduction L L') {δ : ℕ → ℝ≥0∞} (h : L' ∈ AvgDeltaP δ) :
    L ∈ AvgDeltaP (fun n => (R.p.eval n : ℕ) * δ (R.m n)) := by
  obtain ⟨A', hA'⟩ := h
  have hpt := hA'.polyTime
  have hf := R.polyTime
  refine ⟨fun x => A' (R.f x), ⟨?_, ?_, ?_⟩⟩
  · polytime
  · intro n x b hx hb
    rw [R.correct n x hx]
    exact hA'.correct _ _ b (R.mem_support hx) hb
  · intro n
    exact (R.toOuterMeasure_preimage_le n {y | A' y = none}).trans
      (mul_le_mul' le_rfl (hA'.failure_le _))

/-- Reductions transfer heuristic algorithms, multiplying the error bound by the domination
factor: `δ` becomes `n ↦ p(n) · δ(m(n))`. -/
theorem mem_HeurDeltaP (R : DistReduction L L') {δ : ℕ → ℝ≥0∞} (h : L' ∈ HeurDeltaP δ) :
    L ∈ HeurDeltaP (fun n => (R.p.eval n : ℕ) * δ (R.m n)) := by
  obtain ⟨A', hA'⟩ := h
  have hpt := hA'.polyTime
  have hf := R.polyTime
  refine ⟨fun x => A' (R.f x), ⟨?_, ?_⟩⟩
  · polytime
  · intro n
    have hset : {x | ¬(A' (R.f x) = true ↔ x ∈ L.lang)} ∩ (L.ens.dist n).support ⊆
        R.f ⁻¹' {y | ¬(A' y = true ↔ y ∈ L'.lang)} := by
      rintro x ⟨hx, hsupp⟩
      simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hx ⊢
      rwa [← R.correct n x hsupp]
    exact (PMF.toOuterMeasure_mono _ hset).trans ((R.toOuterMeasure_preimage_le n _).trans
      (mul_le_mul' le_rfl (hA'.error_le _)))

/-- The identity reduction. -/
noncomputable def refl (L : DistProblem) : DistReduction L L where
  f := id
  m := id
  p := 1
  polyTime := .of_eq fun _ => rfl
  correct _ _ _ := Iff.rfl
  dominates n y := by
    rw [PMF.map_id, Polynomial.eval_one, Nat.cast_one, one_mul]
    exact le_rfl

/-- The composite of two reductions. The domination factor of the composite is
`p(n) · p'(c (n + 1)^d)`, where `c (n + 1)^d` bounds the length map of the first reduction
(`Cslib.Complexity.DistReduction.exists_m_le`). -/
theorem exists_comp (R : DistReduction L L') (R' : DistReduction L' L'') :
    ∃ R'' : DistReduction L L'', R''.f = R'.f ∘ R.f ∧ R''.m = R'.m ∘ R.m := by
  obtain ⟨c, d, hm⟩ := R.exists_m_le
  refine ⟨⟨R'.f ∘ R.f, R'.m ∘ R.m,
    R.p * R'.p.comp (Polynomial.C c * (Polynomial.X + 1) ^ d),
    R'.polyTime.comp R.polyTime, fun n x hx => (R.correct n x hx).trans
      (R'.correct _ _ (R.mem_support hx)), fun n y => ?_⟩, rfl, rfl⟩
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
    ← PMF.toOuterMeasure_apply_singleton, Set.preimage_comp]
  have hbound : R'.p.eval (R.m n) ≤
      (R'.p.comp (Polynomial.C c * (Polynomial.X + 1) ^ d)).eval n := by
    rw [Polynomial.eval_comp]
    refine R'.p.eval_mono ?_
    simpa using hm n
  calc (L.ens.dist n).toOuterMeasure (R.f ⁻¹' (R'.f ⁻¹' {y}))
      ≤ ((R.p.eval n : ℕ) : ℝ≥0∞) * (L'.ens.dist (R.m n)).toOuterMeasure (R'.f ⁻¹' {y}) :=
        R.toOuterMeasure_preimage_le n _
    _ ≤ ((R.p.eval n : ℕ) : ℝ≥0∞) * (((R'.p.eval (R.m n) : ℕ) : ℝ≥0∞) *
          (L''.ens.dist (R'.m (R.m n))).toOuterMeasure {y}) :=
        mul_le_mul' le_rfl (R'.toOuterMeasure_preimage_le _ _)
    _ ≤ _ := by
      rw [← mul_assoc, Polynomial.eval_mul, Nat.cast_mul]
      exact mul_le_mul' (mul_le_mul' le_rfl (by exact_mod_cast hbound)) le_rfl

end DistReduction

namespace DistReducible

variable {L L' L'' : DistProblem}

theorem refl (L : DistProblem) : DistReducible L L := ⟨DistReduction.refl L⟩

theorem trans (h : DistReducible L L') (h' : DistReducible L' L'') : DistReducible L L'' :=
  let ⟨R⟩ := h
  let ⟨R'⟩ := h'
  let ⟨R'', _⟩ := R.exists_comp R'
  ⟨R''⟩

theorem mem_AvgP (h : DistReducible L L') (h' : L' ∈ AvgP) : L ∈ AvgP :=
  let ⟨R⟩ := h
  R.mem_AvgP h'

theorem mem_HeurP (h : DistReducible L L') (h' : L' ∈ HeurP) : L ∈ HeurP :=
  let ⟨R⟩ := h
  R.mem_HeurP h'

end DistReducible

/-- `L` is **hard** for the class `C` of distributional problems: every problem of `C` reduces to
`L` [Bogdanov and Trevisan, §3][BogdanovTrevisan2006]. -/
@[expose] def DistHard (C : Set DistProblem) (L : DistProblem) : Prop :=
  ∀ L' ∈ C, DistReducible L' L

/-- `L` is **complete** for the class `C`: it lies in `C` and is hard for `C`
[Bogdanov and Trevisan, §3][BogdanovTrevisan2006]. -/
@[expose] def DistComplete (C : Set DistProblem) (L : DistProblem) : Prop :=
  L ∈ C ∧ DistHard C L

/-- If a problem hard for `C` is in `AvgP`, then so is all of `C`. -/
theorem DistHard.subset_AvgP {C : Set DistProblem} {L : DistProblem} (h : DistHard C L)
    (hL : L ∈ AvgP) : C ⊆ AvgP :=
  fun _ hL' => (h _ hL').mem_AvgP hL

/-- If a problem hard for `C` is in `HeurP`, then so is all of `C`. -/
theorem DistHard.subset_HeurP {C : Set DistProblem} {L : DistProblem} (h : DistHard C L)
    (hL : L ∈ HeurP) : C ⊆ HeurP :=
  fun _ hL' => (h _ hL').mem_HeurP hL

/-- A complete problem for `C` is in `AvgP` exactly when `C ⊆ AvgP`. -/
theorem DistComplete.mem_AvgP_iff {C : Set DistProblem} {L : DistProblem}
    (h : DistComplete C L) : L ∈ AvgP ↔ C ⊆ AvgP :=
  ⟨h.2.subset_AvgP, fun hC => hC h.1⟩

/-- A complete problem for `C` is in `HeurP` exactly when `C ⊆ HeurP`. -/
theorem DistComplete.mem_HeurP_iff {C : Set DistProblem} {L : DistProblem}
    (h : DistComplete C L) : L ∈ HeurP ↔ C ⊆ HeurP :=
  ⟨h.2.subset_HeurP, fun hC => hC h.1⟩

end Cslib.Complexity
