/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.PMF
public import Mathlib.Basic.Real.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
import Complexity.Probability.PMF.Event
import Mathlib.Analysis.Convex.Basic
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Sion

/-!
# Averaging and the minimax principle for finite distributions

Think of a two-player game in which one player picks a strategy `a` and the other an input `b`,
with loss `loss a b`; for an algorithm, `loss a b` may be whether `a` errs on `b`. Drawing the
strategy from a distribution `μ` and the input from a distribution `ν` relates the two classical
guarantees of randomized algorithms [Yao1977]. Distributions appear in two forms: finitely
supported ones as points of the standard simplex (`Convexity.StdSimplex`), and probability mass
functions (`PMF`), whose supports may be infinite. On a finite type the two correspond
(`Probability.PMF.ofStdSimplex`, `Probability.PMF.toStdSimplex`).

* *The averaging argument*: some outcome of a distribution is at most the mean
  (`Convexity.StdSimplex.exists_mem_support_le_sum_mul`,
  `Probability.PMF.exists_mem_support_le_tsum_mul`). So if a strategy drawn from `μ` has expected
  loss at most `ε` on every input, then for every `ν` some single strategy has expected loss at
  most `ε` on inputs drawn from `ν` (`Probability.PMF.exists_mem_support_tsum_mul_le`; for the
  probability of failing, `Probability.PMF.exists_mem_support_toOuterMeasure_le`). This is the easy
  direction of Yao's principle.
* *The minimax theorem* [vonNeumann1928]: for finitely many strategies and inputs, the converse
  holds. If against every distribution `ν` on the inputs some strategy has expected loss at most
  `ε`, then some distribution `μ` on the strategies has expected loss at most `ε` on every input
  (`Convexity.StdSimplex.exists_forall_sum_le_of_forall_exists_sum_le`, from Sion's minimax
  theorem `Sion.exists_isSaddlePointOn` [Sion1958]; `Probability.PMF.exists_forall_sum_mul_le` for
  distributions as probability mass functions). For the probability of failing, only the inputs
  need to be finite: strategies failing on the same inputs are interchangeable, so `μ` can be taken
  with finite support (`Probability.PMF.exists_forall_toOuterMeasure_le`). This is the hard
  direction of Yao's principle.

## Main definitions

* `Cslib.Probability.PMF.ofStdSimplex`, `Cslib.Probability.PMF.toStdSimplex`: distributions on a
  finite type as points of the standard simplex.

## Main results

* `Convexity.StdSimplex.exists_mem_support_le_sum_mul`,
  `Cslib.Probability.PMF.exists_mem_support_le_tsum_mul`: some outcome is at most the mean.
* `Cslib.Probability.PMF.exists_mem_support_tsum_mul_le`,
  `Cslib.Probability.PMF.exists_mem_support_toOuterMeasure_le`: the averaging argument.
* `Convexity.StdSimplex.exists_forall_sum_le_of_forall_exists_sum_le`,
  `Cslib.Probability.PMF.exists_forall_sum_mul_le`: the minimax theorem for finite games.
* `Cslib.Probability.PMF.exists_forall_toOuterMeasure_le`: the minimax theorem for failure
  probabilities on finitely many inputs.

## References

* [A. C.-C. Yao, *Probabilistic computations: toward a unified measure of complexity*][Yao1977]
* [J. von Neumann, *Zur Theorie der Gesellschaftsspiele*][vonNeumann1928]
* [M. Sion, *On general minimax theorems*][Sion1958]
-/

@[expose] public section

namespace Convexity.StdSimplex

/-! ### Finitely supported distributions -/

section Averaging

variable {α : Type*} {μ : StdSimplex ℝ α} {g : α → ℝ} {c : ℝ}

/-- An average under a finitely supported distribution is at most any bound on the support. -/
theorem sum_mul_le_of_forall_le (h : ∀ a ∈ μ.weights.support, g a ≤ c) :
    (μ.weights.sum fun a w => w * g a) ≤ c :=
  calc (μ.weights.sum fun a w => w * g a) ≤ μ.weights.sum fun _ w => w * c :=
        Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (h a ha) (μ.weights_nonneg a)
    _ = c := by rw [← Finsupp.sum_mul, μ.total, one_mul]

/-- **The averaging argument**: some point of the support of a finitely supported distribution is
at most the average. -/
theorem exists_mem_support_le_sum_mul (μ : StdSimplex ℝ α) (g : α → ℝ) :
    ∃ a ∈ μ.weights.support, g a ≤ μ.weights.sum fun a w => w * g a := by
  by_contra! h
  have hlt : (μ.weights.sum fun a w => w * (μ.weights.sum fun a w => w * g a)) <
      μ.weights.sum fun a w => w * g a :=
    Finset.sum_lt_sum_of_nonempty μ.support_weights_nonempty fun a ha =>
      mul_lt_mul_of_pos_left (h a ha)
        ((μ.weights_nonneg a).lt_of_ne' (Finsupp.mem_support_iff.mp ha))
  rw [← Finsupp.sum_mul, μ.total, one_mul] at hlt
  exact lt_irrefl _ hlt

end Averaging

/-! ### The minimax theorem for finite games -/

/-- `x ↦ ∑ i, x i * a i` is linear. -/
private theorem isLinearMap_sum_mul {I : Type*} [Fintype I] (a : I → ℝ) :
    IsLinearMap ℝ fun x : I → ℝ => ∑ i, x i * a i :=
  ⟨fun x y => by simp [add_mul, Finset.sum_add_distrib],
    fun c x => by simp [Finset.mul_sum, mul_assoc]⟩

/-- The weight vectors of the distributions on a finite type form a convex set. -/
private theorem convex_range_weights (I : Type*) [Finite I] :
    Convex ℝ (Set.range fun p : StdSimplex ℝ I => (p.weights : I → ℝ)) := by
  have := Fintype.ofFinite I
  rw [range_toFun_comp_weights]
  refine Convex.inter (convex_iInter fun i => ?_) ?_
  · exact convex_halfSpace_ge ⟨fun x y => rfl, fun c x => rfl⟩ 0
  · simpa using convex_hyperplane (isLinearMap_sum_mul fun _ => (1 : ℝ)) 1

/-- The weight vectors of the distributions on a finite type form a compact set. -/
private theorem isCompact_range_weights (I : Type*) [Finite I] :
    IsCompact (Set.range fun p : StdSimplex ℝ I => (p.weights : I → ℝ)) :=
  isCompact_range (isEmbedding_toFun_comp_weights ℝ I).continuous

/-- **The minimax theorem for finite two-player zero-sum games** [Sion1958], in the form used by
Yao's principle. A row player picks `i : I`, a column player picks `j : J`, and the row player pays
`M i j`. If against every mixed strategy `q` of the column player some row `i` has expected payment
at most `c`, then some mixed strategy `p` of the row player has expected payment at most `c` against
every column `j`. -/
theorem exists_forall_sum_le_of_forall_exists_sum_le {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] (M : I → J → ℝ) {c : ℝ}
    (h : ∀ q : StdSimplex ℝ J, ∃ i, ∑ j, q.weights j * M i j ≤ c) :
    ∃ p : StdSimplex ℝ I, ∀ j, ∑ i, p.weights i * M i j ≤ c := by
  classical
  rcases isEmpty_or_nonempty J with hJ | hJ
  · exact ⟨.single (Classical.arbitrary I), fun j => isEmptyElim j⟩
  -- the expected payment, a bilinear function on pairs of weight vectors
  set φ : (I → ℝ) → (J → ℝ) → ℝ := fun x y => ∑ i, ∑ j, x i * y j * M i j
  have hφx (y : J → ℝ) : (fun x => φ x y) = fun x => ∑ i, x i * ∑ j, y j * M i j := by
    funext x
    simp only [φ, Finset.mul_sum, mul_assoc]
  have hφy (x : I → ℝ) : (fun y => φ x y) = fun y => ∑ j, y j * ∑ i, x i * M i j := by
    funext y
    simp only [φ, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have hcont : Continuous fun p : (I → ℝ) × (J → ℝ) => φ p.1 p.2 := by
    simp only [φ]
    fun_prop
  -- a saddle point of `φ` on the two simplices
  obtain ⟨a, ⟨p, rfl⟩, b, ⟨q, rfl⟩, hab⟩ := Sion.exists_isSaddlePointOn (f := φ)
    (Set.range_nonempty _) (convex_range_weights I) (isCompact_range_weights I)
    (fun y _ =>
      (hcont.comp (Continuous.prodMk_left y)).lowerSemicontinuous.lowerSemicontinuousOn _)
    (fun y _ r => by
      rw [hφx]
      exact (convex_range_weights I).inter (convex_halfSpace_le (isLinearMap_sum_mul _) r))
    (convex_range_weights J) (Set.range_nonempty _) (isCompact_range_weights J)
    (fun x _ =>
      (hcont.comp (Continuous.prodMk_right x)).upperSemicontinuous.upperSemicontinuousOn _)
    (fun x _ r => by
      rw [hφy]
      exact (convex_range_weights J).inter (convex_halfSpace_ge (isLinearMap_sum_mul _) r))
  -- against the column strategy `q` some row `i` pays at most `c`, and `p` does no worse
  obtain ⟨i, hi⟩ := h q
  refine ⟨p, fun j => ?_⟩
  have h₁ := hab _ ⟨.single i, rfl⟩ _ ⟨.single j, rfl⟩
  simp only [φ, weights_single, Finsupp.single_apply] at h₁
  simp only [mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Finset.sum_ite_irrel, Finset.sum_const_zero] at h₁
  exact h₁.trans hi

end Convexity.StdSimplex

namespace Cslib.Probability.PMF

open scoped ENNReal
open Convexity Finset

/-! ### Probability mass functions -/

variable {α β : Type*}

/-- **Some possible outcome is at most the mean**: for every distribution `μ` and every function
`g` with values in `[0, ∞]`, some outcome `a` that `μ` can produce has `g a` at most the mean of `g`
under `μ`. The sample space may be infinite. -/
theorem exists_mem_support_le_tsum_mul (μ : PMF α) (g : α → ℝ≥0∞) :
    ∃ a ∈ μ.support, g a ≤ ∑' a, μ a * g a := by
  by_contra! hlt
  obtain ⟨a₀, ha₀⟩ := μ.support_nonempty
  have htop : ∑' a, μ a * g a ≠ ⊤ := ne_top_of_lt (hlt a₀ ha₀)
  have := ENNReal.tsum_lt_tsum (f := fun a => μ a * ∑' a, μ a * g a)
    (g := fun a => μ a * g a) (i := a₀)
    (by rwa [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul])
    (fun a => by
      by_cases ha : a ∈ μ.support
      · gcongr
        exact (hlt a ha).le
      · simp [(PMF.apply_eq_zero_iff μ a).mpr ha])
    (ENNReal.mul_lt_mul_right ((PMF.mem_support_iff μ a₀).mp ha₀) (PMF.apply_ne_top μ a₀)
      (hlt a₀ ha₀))
  rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul] at this
  exact lt_irrefl _ this

/-- **The averaging argument**, the easy direction of Yao's principle. Let `loss a b` be the loss
of a strategy `a` on an input `b`. If drawing the strategy from `μ` has expected loss at most `ε` on
every input that `ν` can produce, then some strategy that `μ` can produce has expected loss at most
`ε` on inputs drawn from `ν`. The sample spaces may be infinite. -/
theorem exists_mem_support_tsum_mul_le (μ : PMF α) (ν : PMF β) (loss : α → β → ℝ≥0∞)
    {ε : ℝ≥0∞} (h : ∀ b ∈ ν.support, ∑' a, μ a * loss a b ≤ ε) :
    ∃ a ∈ μ.support, ∑' b, ν b * loss a b ≤ ε := by
  obtain ⟨a, ha, hle⟩ := exists_mem_support_le_tsum_mul μ fun a => ∑' b, ν b * loss a b
  refine ⟨a, ha, hle.trans ?_⟩
  calc ∑' a, μ a * ∑' b, ν b * loss a b
      = ∑' b, ν b * ∑' a, μ a * loss a b := by
        simp only [← ENNReal.tsum_mul_left]
        rw [tsum_comm]
        exact tsum_congr fun b => tsum_congr fun a => by ring
    _ ≤ ∑' b, ν b * ε := by
        refine tsum_le_tsum fun b => ?_
        by_cases hb : b ∈ ν.support
        · gcongr
          exact h b hb
        · simp [(PMF.apply_eq_zero_iff ν b).mpr hb]
    _ = ε := by rw [ENNReal.tsum_mul_right, ν.tsum_coe, one_mul]

/-- The probability of an event as the mean of its indicator. -/
private theorem toOuterMeasure_eq_tsum_mul_ite {γ : Type*} (π : PMF γ) (s : Set γ)
    [DecidablePred (· ∈ s)] : π.toOuterMeasure s = ∑' c, π c * if c ∈ s then 1 else 0 := by
  rw [PMF.toOuterMeasure_apply]
  exact tsum_congr fun c => by by_cases hc : c ∈ s <;> simp [hc]

/-- **The averaging argument** for events, the easy direction of Yao's principle: if a strategy
drawn from `μ` fails on every input that `ν` can produce with probability at most `ε`, then some
strategy that `μ` can produce fails on an input drawn from `ν` with probability at most `ε`. The
sample spaces may be infinite. -/
theorem exists_mem_support_toOuterMeasure_le (μ : PMF α) (ν : PMF β) (E : α → β → Prop)
    {ε : ℝ} (h : ∀ b ∈ ν.support, (μ.toOuterMeasure {a | E a b}).toReal ≤ ε) :
    ∃ a ∈ μ.support, (ν.toOuterMeasure {b | E a b}).toReal ≤ ε := by
  classical
  obtain ⟨b₀, hb₀⟩ := ν.support_nonempty
  have hε : 0 ≤ ε := ENNReal.toReal_nonneg.trans (h b₀ hb₀)
  obtain ⟨a, ha, hle⟩ := exists_mem_support_tsum_mul_le μ ν
    (fun a b => if E a b then 1 else 0) (ε := ENNReal.ofReal ε) fun b hb => by
      have := h b hb
      rw [← ENNReal.ofReal_le_ofReal_iff hε, ENNReal.ofReal_toReal (PMF.toOuterMeasure_ne_top μ _),
        toOuterMeasure_eq_tsum_mul_ite] at this
      simpa only [Set.mem_ofPred_eq] using this
  refine ⟨a, ha, ENNReal.toReal_le_of_le_ofReal hε ?_⟩
  rw [toOuterMeasure_eq_tsum_mul_ite]
  simpa only [Set.mem_ofPred_eq] using hle

/-! ### The minimax theorem for probability mass functions -/

section Minimax

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The distribution on a finite type whose probabilities are the weights of a point of the
standard simplex. -/
def ofStdSimplex (p : StdSimplex ℝ I) : PMF I :=
  PMF.ofFintype (fun i => ENNReal.ofReal (p.weights i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => p.weights_nonneg i, p.total_of_fintype,
      ENNReal.ofReal_one])

/-- The probability of `i` under `ofStdSimplex p` is the weight of `i` in `p`. -/
@[simp] theorem toReal_ofStdSimplex (p : StdSimplex ℝ I) (i : I) :
    (ofStdSimplex p i).toReal = p.weights i :=
  ENNReal.toReal_ofReal (p.weights_nonneg i)

/-- The point of the standard simplex whose weights are the probabilities of a distribution on a
finite type. -/
noncomputable def toStdSimplex (μ : PMF I) : StdSimplex ℝ I where
  weights := Finsupp.equivFunOnFinite.symm fun i => (μ i).toReal
  nonneg _ := ENNReal.toReal_nonneg
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simpa using sum_toReal μ

/-- The weight of `i` in `toStdSimplex μ` is the probability of `i`, as a real number. -/
@[simp] theorem weights_toStdSimplex (μ : PMF I) (i : I) :
    (toStdSimplex μ).weights i = (μ i).toReal :=
  rfl

/-- Passing from a distribution to the simplex and back returns the distribution. -/
@[simp] theorem ofStdSimplex_toStdSimplex (μ : PMF I) : ofStdSimplex (toStdSimplex μ) = μ :=
  PMF.ext fun i => by
    rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top μ i), ← weights_toStdSimplex]
    rfl

/-- **The minimax theorem for finite games** [vonNeumann1928], for distributions. Let `M i j` be
the loss of a strategy `i` on an input `j`. If against every distribution `ν` on the inputs some
strategy has expected loss at most `ε`, then some distribution `μ` on the strategies has expected
loss at most `ε` on every input. This is the hard direction of Yao's principle; it is
`Convexity.StdSimplex.exists_forall_sum_le_of_forall_exists_sum_le`, from Sion's theorem, read
through `ofStdSimplex`. -/
theorem exists_forall_sum_mul_le [Nonempty I] (M : I → J → ℝ) {ε : ℝ}
    (h : ∀ ν : PMF J, ∃ i, ∑ j, (ν j).toReal * M i j ≤ ε) :
    ∃ μ : PMF I, ∀ j, ∑ i, (μ i).toReal * M i j ≤ ε := by
  obtain ⟨p, hp⟩ := StdSimplex.exists_forall_sum_le_of_forall_exists_sum_le M fun q => by
    simpa using h (ofStdSimplex q)
  exact ⟨ofStdSimplex p, by simpa using hp⟩

/-- The probability of an event in a finite space as a sum. -/
private theorem toReal_toOuterMeasure_eq_sum {γ : Type*} [Fintype γ] (π : PMF γ) (s : Set γ)
    [DecidablePred (· ∈ s)] :
    (π.toOuterMeasure s).toReal = ∑ c, (π c).toReal * if c ∈ s then 1 else 0 := by
  rw [toOuterMeasure_apply_toReal]
  exact sum_congr rfl fun c _ => by by_cases hc : c ∈ s <;> simp [hc]

/-- **Yao's minimax principle** for finite sets of inputs. Let `E i j` say that a strategy `i`
fails on an input `j`, where there may be infinitely many strategies but only finitely many inputs.
If against every distribution `ν` on the inputs some strategy fails with probability at most `ε`,
then some distribution `μ` on finitely many strategies fails with probability at most `ε` on every
input. -/
theorem exists_forall_toOuterMeasure_le {I J : Type*} [Finite J] [Nonempty I] (E : I → J → Prop)
    {ε : ℝ} (h : ∀ ν : PMF J, ∃ i, (ν.toOuterMeasure {j | E i j}).toReal ≤ ε) :
    ∃ μ : PMF I, μ.support.Finite ∧ ∀ j, (μ.toOuterMeasure {i | E i j}).toReal ≤ ε := by
  classical
  have := Fintype.ofFinite J
  -- Strategies with the same failures are interchangeable: play on the finitely many sets of
  -- failures, each represented by one strategy.
  let r : I → Set J := fun i => {j | E i j}
  have := Fintype.ofFinite (Set.range r)
  have : Nonempty (Set.range r) := ⟨⟨r (Classical.arbitrary I), _, rfl⟩⟩
  let rep : Set.range r → I := fun s => s.2.choose
  have hrep (s : Set.range r) (j : J) : E (rep s) j ↔ j ∈ s.1 := by
    rw [← s.2.choose_spec]
    rfl
  obtain ⟨μ, hμ⟩ := exists_forall_sum_mul_le (fun (s : Set.range r) j => if j ∈ s.1 then 1 else 0)
    (ε := ε) fun ν => by
      obtain ⟨i, hi⟩ := h ν
      refine ⟨⟨r i, i, rfl⟩, ?_⟩
      rwa [toReal_toOuterMeasure_eq_sum] at hi
  refine ⟨μ.map rep, by rw [PMF.support_map]; exact (Set.toFinite _).image _, fun j => ?_⟩
  rw [PMF.toOuterMeasure_map_apply, toReal_toOuterMeasure_eq_sum]
  refine le_of_eq_of_le (sum_congr rfl fun s _ => ?_) (hμ j)
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hrep]

end Minimax

end Cslib.Probability.PMF
