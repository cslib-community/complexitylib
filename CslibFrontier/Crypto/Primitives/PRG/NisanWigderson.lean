/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Primitives.PRG.NextBit
public import Mathlib.Data.Finset.Sort
public import Mathlib.Logic.Function.DependsOn
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF
import CslibFrontier.Tactic.PMFSwap

/-!
# The Nisan–Wigderson generator and its reconstruction

An `(ℓ, n, a)`-design with `m` blocks is a family of `m` subsets of `Fin ℓ`, each with `n` elements,
any two of which share at most `a` elements. Given such a design and a Boolean function `f` on `n`
bits, the Nisan–Wigderson generator stretches a seed `z` of `ℓ` bits to the `m` bits
`f (z|S₀) … f (z|Sₘ₋₁)`, where `z|S` lists the bits of `z` in `S` in increasing order of position
[NisanWigderson1994], [Arora and Barak, Chapter 20][AroraBarak09].

Its analysis is a reconstruction. Suppose that a test accepts generated outputs with probability
at least `ε` more than uniform ones. By the next-bit theorem
(`Cslib.Crypto.PRG.Generator.exists_half_add_div_le_predictionExperiment`), the predictor built
from the test guesses some bit `i` from the bits before it with probability at least
`1 / 2 + ε / m`. This probability is an average over seeds, and a seed consists of the input
`x = z|Sᵢ` of bit `i` together with the bits outside `Sᵢ`, so for some choice of the bits outside
`Sᵢ` the predictor still guesses `f x` from the earlier bits with probability at least
`1 / 2 + ε / m`. Once the bits outside `Sᵢ` are fixed, each earlier bit `j < i` depends on `x`
only through the at most `a` positions of `Sᵢ ∩ Sⱼ`, so as a function of `x` it is given by a
table of at most `2 ^ a` values of `f`. For a deterministic test, fixing the random choices of the
predictor as well yields a function that agrees with `f` on at least a `1 / 2 + ε / m` fraction
of the inputs and is computed by the test from `i` functions of at most `a` input bits each. A
lower bound on the size of circuits approximating `f` thus becomes a lower bound on the size of
circuits distinguishing the generator; this file is the finite core of that argument, without a
model of computation.

Designs with good parameters exist (`Cslib.Crypto.PRG.NisanWigderson.Design.nonempty_four_mul_sq`).

## Main definitions

* `Cslib.Crypto.PRG.NisanWigderson.Design`: an `(ℓ, n, a)`-design with `m` blocks.
* `Cslib.Crypto.PRG.NisanWigderson.Design.restrict`,
  `Cslib.Crypto.PRG.NisanWigderson.Design.extend`: reading a block of a string, and overwriting it.
* `Cslib.Crypto.PRG.NisanWigderson.Design.overlap`: the positions of one block lying in another.
* `Cslib.Crypto.PRG.NisanWigderson.generator`: the Nisan–Wigderson generator.
* `Cslib.Crypto.PRG.NisanWigderson.hardwiredExperiment`: the prediction experiment for bit `i`
  with the seed bits outside the `i`-th block fixed.

## Main results

* `Cslib.Crypto.PRG.NisanWigderson.predictionExperiment_generator`: the prediction experiment is
  the average of the hardwired experiments, so
  `Cslib.Crypto.PRG.NisanWigderson.exists_predictionExperiment_le_hardwiredExperiment` some
  hardwiring does at least as well.
* `Cslib.Crypto.PRG.NisanWigderson.dependsOn_generator_extend`,
  `Cslib.Crypto.PRG.NisanWigderson.Design.card_overlap_le`: with the bits outside block `i`
  fixed, output bit `j ≠ i` depends on at most `a` bits of the input of bit `i`.
* `Cslib.Crypto.PRG.NisanWigderson.exists_half_add_div_le_hardwiredExperiment`: the
  reconstruction for randomized tests, in the language of the next-bit test.
* `Cslib.Crypto.PRG.NisanWigderson.exists_half_add_div_le_card_nextBitGuess_eq`,
  `Cslib.Crypto.PRG.NisanWigderson.exists_dependsOn_half_add_div_le_card_nextBitGuess_eq`: the
  reconstruction for deterministic tests, as a statement about functions: `f` agrees on a
  `1 / 2 + ε / m` fraction of inputs with a function computed by the test from `i` functions of
  at most `a` input bits each.

## References

* [N. Nisan, A. Wigderson, *Hardness vs randomness*][NisanWigderson1994]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 20
-/

@[expose] public section

namespace Cslib.Crypto.PRG.NisanWigderson

open Cslib.Probability.PMF Finset
open scoped ENNReal

/-- An `(ℓ, n, a)`-design with `m` blocks [Arora and Barak, Chapter 20][AroraBarak09]: `m` subsets
of `Fin ℓ`, each with `n` elements, any two distinct ones sharing at most `a` elements. -/
structure Design (ℓ n a m : ℕ) where
  /-- The `i`-th block of the design. -/
  block : Fin m → Finset (Fin ℓ)
  /-- Every block has `n` elements. -/
  card_block (i : Fin m) : #(block i) = n
  /-- Two distinct blocks share at most `a` elements. -/
  card_inter_le {i j : Fin m} : i ≠ j → #(block i ∩ block j) ≤ a

variable {ℓ n a m : ℕ} {α : Type*}

section Design

/-- The bits of `z` in the `i`-th block of `D`, in increasing order of position. -/
def Design.restrict (D : Design ℓ n a m) (i : Fin m) (z : Fin ℓ → α) : Fin n → α :=
  z ∘ (D.block i).orderEmbOfFin (D.card_block i)

/-- The string that agrees with `w` outside the `i`-th block of `D` and carries the bits of `x`
on it, in increasing order of position. -/
def Design.extend (D : Design ℓ n a m) (i : Fin m) (x : Fin n → α) (w : Fin ℓ → α) :
    Fin ℓ → α := fun k =>
  if h : k ∈ D.block i then x (((D.block i).orderIsoOfFin (D.card_block i)).symm ⟨k, h⟩)
  else w k

/-- The positions in the `i`-th block of `D`, counted in increasing order, of the elements that
also lie in the `j`-th block. -/
def Design.overlap (D : Design ℓ n a m) (i j : Fin m) : Finset (Fin n) :=
  {k | (D.block i).orderEmbOfFin (D.card_block i) k ∈ D.block j}

variable (D : Design ℓ n a m)

private theorem orderEmbOfFin_orderIsoOfFin_symm {β : Type*} [LinearOrder β] (s : Finset β)
    {k : ℕ} (h : #s = k) (p : s) : s.orderEmbOfFin h ((s.orderIsoOfFin h).symm p) = p := by
  rw [← coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

@[simp]
theorem Design.restrict_apply (i : Fin m) (z : Fin ℓ → α) (k : Fin n) :
    D.restrict i z k = z ((D.block i).orderEmbOfFin (D.card_block i) k) :=
  rfl

@[simp]
theorem Design.extend_apply_orderEmbOfFin (i : Fin m) (x : Fin n → α) (w : Fin ℓ → α)
    (k : Fin n) : D.extend i x w ((D.block i).orderEmbOfFin (D.card_block i) k) = x k := by
  rw [Design.extend, dite_eq_left (orderEmbOfFin_mem _ _ k)]
  congr
  rw [OrderIso.symm_apply_eq]
  exact Subtype.ext (coe_orderIsoOfFin_apply _ _ k).symm

theorem Design.extend_apply_of_notMem (i : Fin m) (x : Fin n → α) (w : Fin ℓ → α) {k : Fin ℓ}
    (hk : k ∉ D.block i) : D.extend i x w k = w k :=
  dite_eq_right hk

/-- Reading the `i`-th block of a string whose `i`-th block was overwritten by `x` gives `x`. -/
@[simp]
theorem Design.restrict_extend (i : Fin m) (x : Fin n → α) (w : Fin ℓ → α) :
    D.restrict i (D.extend i x w) = x := by
  ext k
  simp

/-- Overwriting the `i`-th block of `z` by its own bits gives `z`. -/
@[simp]
theorem Design.extend_restrict (i : Fin m) (z : Fin ℓ → α) : D.extend i (D.restrict i z) z = z := by
  ext k
  by_cases hk : k ∈ D.block i
  · rw [Design.extend, dite_eq_left hk, Design.restrict_apply, orderEmbOfFin_orderIsoOfFin_symm]
  · exact D.extend_apply_of_notMem i _ z hk

/-- Overwriting the `i`-th block twice keeps only the second overwrite. -/
@[simp]
theorem Design.extend_extend (i : Fin m) (x y : Fin n → α) (w : Fin ℓ → α) :
    D.extend i y (D.extend i x w) = D.extend i y w := by
  ext k
  by_cases hk : k ∈ D.block i
  · simp only [Design.extend, dite_eq_left hk]
  · simp only [Design.extend, dite_eq_right hk]

/-- The positions of the `i`-th block lying in the `j`-th block are as many as the elements the
two blocks share. -/
theorem Design.card_overlap (i j : Fin m) : #(D.overlap i j) = #(D.block i ∩ D.block j) := by
  rw [← card_map ((D.block i).orderEmbOfFin (D.card_block i)).toEmbedding]
  congr 1
  ext p
  simp only [Design.overlap, mem_map, mem_filter, mem_univ, true_and, mem_inter,
    RelEmbedding.coe_toEmbedding]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨orderEmbOfFin_mem _ _ k, hk⟩
  · rintro ⟨hi, hj⟩
    obtain ⟨k, rfl⟩ : p ∈ Set.range ((D.block i).orderEmbOfFin (D.card_block i)) := by
      simpa using hi
    exact ⟨k, hj, rfl⟩

/-- For distinct blocks, at most `a` positions of the `i`-th block lie in the `j`-th block. -/
theorem Design.card_overlap_le {i j : Fin m} (hij : i ≠ j) : #(D.overlap i j) ≤ a :=
  (D.card_overlap i j).trans_le (D.card_inter_le hij)

/-- With the bits outside the `i`-th block fixed to those of `w`, the bits in the `j`-th block
depend on the bits `x` in the `i`-th block only through the positions in `D.overlap i j`. -/
theorem Design.dependsOn_restrict_extend (i j : Fin m) (w : Fin ℓ → α) :
    DependsOn (fun x : Fin n → α => D.restrict j (D.extend i x w)) (D.overlap i j) := by
  intro x y hxy
  ext k
  simp only [Design.restrict_apply, Design.extend]
  split_ifs with h
  · refine hxy _ ?_
    simp only [Design.overlap, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq,
      orderEmbOfFin_orderIsoOfFin_symm, orderEmbOfFin_mem]
  · rfl

/-- The map `(w, x) ↦ (D.extend i x w, D.restrict i w)`, swapping the `i`-th block of `w` with
`x`, is an involution. -/
private theorem Design.involutive_extend_restrict (i : Fin m) :
    Function.Involutive fun p : (Fin ℓ → α) × (Fin n → α) =>
      (D.extend i p.2 p.1, D.restrict i p.1) := by
  rintro ⟨w, x⟩
  simp

end Design

section Uniform

variable [Fintype α] [Nonempty α]

/-- Overwriting the `i`-th block of a uniform seed by independent uniform values leaves it
uniform, inside an experiment: `(w, x) ↦ (D.extend i x w, D.restrict i w)` is a permutation. -/
private theorem Design.uniformOfFintype_bind_eq {β : Type*} (D : Design ℓ n a m) (i : Fin m)
    (F : (Fin ℓ → α) → PMF β) :
    (uniformOfFintype (Fin ℓ → α)).bind F = (uniformOfFintype (Fin ℓ → α)).bind fun w =>
      (uniformOfFintype (Fin n → α)).bind fun x => F (D.extend i x w) :=
  (uniformOfFintype_bind_bind_fst_equiv
    (Function.Involutive.toPerm _ (D.involutive_extend_restrict (α := α) i)) F).symm

private theorem toReal_uniformOfFintype_map_decide_apply_true {β : Type*} [Fintype β]
    [Nonempty β] (p : β → Prop) [DecidablePred p] :
    (((uniformOfFintype β).map fun b => decide (p b)) true).toReal =
      (#{b | p b} : ℝ) / Fintype.card β := by
  rw [PMF.map_apply, tsum_fintype]
  simp [sum_ite, div_eq_mul_inv]

end Uniform

/-- The Nisan–Wigderson generator of a design `D` and a function `f` on `n` bits
[Arora and Barak, Chapter 20][AroraBarak09]: bit `i` of the output on a seed `z` is `f` applied to
the bits of `z` in the `i`-th block. -/
def generator (D : Design ℓ n a m) (f : (Fin n → Bool) → Bool) :
    Generator (Fin ℓ → Bool) (Fin m → Bool) :=
  ⟨fun z i => f (D.restrict i z)⟩

@[simp]
theorem generator_apply (D : Design ℓ n a m) (f : (Fin n → Bool) → Bool) (z : Fin ℓ → Bool)
    (i : Fin m) : generator D f z i = f (D.restrict i z) :=
  rfl

/-- With the bits outside the `i`-th block fixed to those of `w`, output bit `j` of the
generator depends on the bits `x` in the `i`-th block only through the positions in
`D.overlap i j`. For `j ≠ i` there are at most `a` of them (`Design.card_overlap_le`). -/
theorem dependsOn_generator_extend (D : Design ℓ n a m) (f : (Fin n → Bool) → Bool) (i j : Fin m)
    (w : Fin ℓ → Bool) :
    DependsOn (fun x => generator D f (D.extend i x w) j) (D.overlap i j) := fun _ _ h =>
  congrArg f (D.dependsOn_restrict_extend i j w h)

/-- The prediction experiment for bit `i` of the generator with the seed bits outside the `i`-th
block fixed to those of `w`: the input `x` of bit `i` is uniform, the predictor receives the
first `i` bits of the output on the seed `D.extend i x w`, and the experiment outputs `true`
exactly when the predictor's guess is `f x`. -/
noncomputable def hardwiredExperiment (D : Design ℓ n a m) (f : (Fin n → Bool) → Bool)
    (i : Fin m) (w : Fin ℓ → Bool) (predictor : Adversary (Fin i → Bool)) : PMF Bool := do
  let x ← uniformOfFintype (Fin n → Bool)
  (predictor (Fin.take i i.isLt.le (generator D f (D.extend i x w)))).map fun g =>
    decide (g = f x)

/-- The prediction experiment for bit `i` of the generator is the average, over a uniform `w`,
of the experiments with the seed bits outside the `i`-th block fixed to those of `w`. -/
theorem predictionExperiment_generator (D : Design ℓ n a m) (f : (Fin n → Bool) → Bool)
    (i : Fin m) (predictor : Adversary (Fin i → Bool)) :
    (generator D f).predictionExperiment i predictor =
      (do
        let w ← uniformOfFintype (Fin ℓ → Bool)
        hardwiredExperiment D f i w predictor) := by
  simp only [Generator.predictionExperiment, Generator.outputDist, monad_bind_eq_bind, PMF.bind_map]
  rw [D.uniformOfFintype_bind_eq i]
  simp only [Function.comp_apply, generator_apply, Design.restrict_extend]
  rfl

/-- **Hardwiring.** Some choice of the seed bits outside the `i`-th block keeps the probability
that a predictor guesses bit `i` of the generator correctly. -/
theorem exists_predictionExperiment_le_hardwiredExperiment (D : Design ℓ n a m)
    (f : (Fin n → Bool) → Bool) (i : Fin m) (predictor : Adversary (Fin i → Bool)) :
    ∃ w, (generator D f).predictionExperiment i predictor true ≤
      hardwiredExperiment D f i w predictor true := by
  rw [predictionExperiment_generator]
  obtain ⟨w, -, hw⟩ := exists_bind_apply_le (uniformOfFintype (Fin ℓ → Bool)) _ true
  exact ⟨w, hw⟩

/-- **The Nisan–Wigderson reconstruction** [Arora and Barak, Chapter 20][AroraBarak09]. If `0 < m`
and a test accepts outputs of the generator with probability at least `ε` more than uniform strings,
then for some position `i` and some choice `w` of the seed bits outside the `i`-th block, the
predictor built from the test guesses `f x` from the first `i` bits of the output on
`D.extend i x w` with probability at least `1 / 2 + ε / m`, for a uniform `x`. By
`dependsOn_generator_extend` and `Design.card_overlap_le`, each of these `i` bits depends on at most
`a` bits of `x`. -/
theorem exists_half_add_div_le_hardwiredExperiment (D : Design ℓ n a m)
    (f : (Fin n → Bool) → Bool) (adversary : Adversary (Fin m → Bool)) (hm : 0 < m) {ε : ℝ}
    (hε : ε ≤ ((generator D f).realExperiment adversary true).toReal -
      (Generator.idealExperiment adversary true).toReal) :
    ∃ i w, 1 / 2 + ε / m ≤
      (hardwiredExperiment D f i w (nextBitPredictor adversary i) true).toReal := by
  obtain ⟨i, hi⟩ := (generator D f).exists_half_add_div_le_predictionExperiment adversary hm hε
  obtain ⟨w, hw⟩ :=
    exists_predictionExperiment_le_hardwiredExperiment D f i (nextBitPredictor adversary i)
  exact ⟨i, w, hi.trans (ENNReal.toReal_mono (PMF.apply_ne_top _ _) hw)⟩

/-- The hardwired experiment against the predictor built from a deterministic test, with the
random choices of the predictor drawn first. -/
theorem hardwiredExperiment_nextBitPredictor_pure (D : Design ℓ n a m)
    (f : (Fin n → Bool) → Bool) (test : (Fin m → Bool) → Bool) (i : Fin m) (w : Fin ℓ → Bool) :
    hardwiredExperiment D f i w (nextBitPredictor (fun y => PMF.pure (test y)) i) =
      (do
        let r ← uniformOfFintype Bool
        let u ← uniformOfFintype (Fin m → Bool)
        (uniformOfFintype (Fin n → Bool)).map fun x => decide
          (nextBitGuess test i r u (Fin.take i i.isLt.le (generator D f (D.extend i x w))) =
            f x)) := by
  simp only [hardwiredExperiment, nextBitPredictor_pure, monad_bind_eq_bind, ← PMF.bind_pure_comp,
    PMF.bind_bind,
    Function.comp_apply, PMF.pure_bind]
  pmf_swap

/-- **The Nisan–Wigderson reconstruction for deterministic tests**, with explicit hardwiring. If
`0 < m` and a deterministic test accepts outputs of the generator with probability at least `ε`
more than uniform strings, then for some position `i`, seed `w`, bit `r` and string `u`, the
guess `nextBitGuess test i r u` on the first `i` bits of the output on `D.extend i x w` equals
`f x` for at least a `1 / 2 + ε / m` fraction of the inputs `x`. -/
theorem exists_half_add_div_le_card_nextBitGuess_eq (D : Design ℓ n a m)
    (f : (Fin n → Bool) → Bool) (test : (Fin m → Bool) → Bool) (hm : 0 < m) {ε : ℝ}
    (hε : ε ≤ ((generator D f).realExperiment (fun y => PMF.pure (test y)) true).toReal -
      (Generator.idealExperiment (fun y => PMF.pure (test y)) true).toReal) :
    ∃ (i : Fin m) (w : Fin ℓ → Bool) (r : Bool) (u : Fin m → Bool), 1 / 2 + ε / m ≤
      (#{x | nextBitGuess test i r u (Fin.take i i.isLt.le (generator D f (D.extend i x w))) =
        f x} : ℝ) / 2 ^ n := by
  obtain ⟨i, w, h⟩ := exists_half_add_div_le_hardwiredExperiment D f _ hm hε
  rw [hardwiredExperiment_nextBitPredictor_pure] at h
  obtain ⟨r, -, hr⟩ := exists_bind_apply_le (uniformOfFintype Bool) _ true
  obtain ⟨u, -, hu⟩ := exists_bind_apply_le (uniformOfFintype (Fin m → Bool)) _ true
  refine ⟨i, w, r, u, h.trans ?_⟩
  calc _ ≤ _ := ENNReal.toReal_mono (PMF.apply_ne_top _ _) (hr.trans hu)
    _ = _ := by
      rw [toReal_uniformOfFintype_map_decide_apply_true]
      simp

/-- **The Nisan–Wigderson reconstruction for deterministic tests**, as a statement about
functions. If `0 < m` and a deterministic test accepts outputs of the generator with probability
at least `ε` more than uniform strings, then for some position `i` there are a bit `r`, a string
`u`, and `i` functions `bit j` on `n` bits, each depending only on a set `s j` of at most `a`
positions, such that `nextBitGuess test i r u (fun j => bit j x) = f x` for at least a
`1 / 2 + ε / m` fraction of the inputs `x`. -/
theorem exists_dependsOn_half_add_div_le_card_nextBitGuess_eq (D : Design ℓ n a m)
    (f : (Fin n → Bool) → Bool) (test : (Fin m → Bool) → Bool) (hm : 0 < m) {ε : ℝ}
    (hε : ε ≤ ((generator D f).realExperiment (fun y => PMF.pure (test y)) true).toReal -
      (Generator.idealExperiment (fun y => PMF.pure (test y)) true).toReal) :
    ∃ (i : Fin m) (s : Fin i → Finset (Fin n)) (bit : Fin i → (Fin n → Bool) → Bool) (r : Bool)
      (u : Fin m → Bool), (∀ j, #(s j) ≤ a) ∧ (∀ j, DependsOn (bit j) (s j)) ∧
      1 / 2 + ε / m ≤ (#{x | nextBitGuess test i r u (fun j => bit j x) = f x} : ℝ) / 2 ^ n := by
  obtain ⟨i, w, r, u, h⟩ := exists_half_add_div_le_card_nextBitGuess_eq D f test hm hε
  refine ⟨i, fun j => D.overlap i (Fin.castLE i.isLt.le j),
    fun j x => generator D f (D.extend i x w) (Fin.castLE i.isLt.le j), r, u,
    fun j => D.card_overlap_le (Fin.ne_of_gt j.isLt), fun j => dependsOn_generator_extend D f _ _ w,
    h⟩

end Cslib.Crypto.PRG.NisanWigderson
