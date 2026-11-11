/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.GameTheory.Strategic.Mixed
public import Complexity.GameTheory.Strategic.NoRegret
public import Complexity.MachineLearning.OnlineLearning.Hedge
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Hedge dynamics in finite games

In *multiplicative-update dynamics* ([Roughgarden2013CS364A], Lecture 17, §3) every player `i` of a
finite cost-minimization game keeps one weight per strategy, starting at `1`. In round `t` it plays
its weights normalized to a mixed strategy (`mwuProb`). It then observes its expected cost vector
`deviationCost G (mwuProb φ t) i` against the product of everyone's current mixed strategies and
multiplies the weight of each strategy `a` by `φ i (deviationCost G (mwuProb φ t) i a)`
(`mwuWeight`).

The players' losses are coupled: the cost vector of player `i` in round `t` depends on the other
players' current mixed strategies. These depend on their past cost vectors, and so on the past play
of `i`. This is an adaptive adversary ([Roughgarden2013CS364A], Lecture 17, Remark 3.2). The
dynamics are deterministic, though, so each player faces one fixed loss sequence `mwuLoss G φ i`,
and its mixed strategies are exactly those of the single-learner multiplicative update against
that sequence (`prob_mwuLoss`). So the regret bounds of
`Complexity.MachineLearning.OnlineLearning` apply to every player.

*Hedge dynamics* (`hedgeProb`) use the factor `exp (-η_i x / M)`, that is, Hedge on the costs
scaled by a bound `M` on their absolute values, with the tuned learning rate
`η_i = √(ln |S i| / T)` for a known horizon `T`. Every player then has regret at most
`2 M √(T ln |S i|)` against every fixed strategy (`hedge_regret_le`, from
`Experts.hedge_regret_le_sqrt`; [AroraHazanKale2012], Theorem 2.3). [Roughgarden2013CS364A]
assumes costs in `[0, 1]` and notes bounded costs as an extension (Lecture 17, footnote 1).

With the results of `Complexity.GameTheory.Strategic.NoRegret` this gives the headline bound
(`IsSmooth.timeAverage_hedgeDist_socialCost_le`). In a `(λ, μ)`-smooth game with `μ < 1` and costs
bounded by `M`, after `T ≥ max_i ln |S i|` rounds of Hedge dynamics, the expected social cost
under the time average of the outcome distributions is at most
`(λ socialCost s' + 2 M ∑ i, √(ln |S i| / T)) / (1 - μ)` for every profile `s'`. This bound
converges to the robust price of anarchy `λ / (1 - μ)` at rate `O(1 / √T)`.

## Main definitions

* `Cslib.GameTheory.CostGame.mwuWeight`, `Cslib.GameTheory.CostGame.mwuProb`: weights and mixed
  strategies under simultaneous multiplicative updates with factors `φ i`.
* `Cslib.GameTheory.CostGame.mwuLoss`: the loss sequence each player faces.
* `Cslib.GameTheory.CostGame.hedgeProb`, `Cslib.GameTheory.CostGame.hedgeDist`: Hedge dynamics
  with the tuned learning rate `√(ln |S i| / T)` and their outcome distribution in each round.

## Main results

* `Cslib.GameTheory.CostGame.prob_mwuLoss`: each player runs the single-learner multiplicative
  update against the losses it faces.
* `Cslib.GameTheory.CostGame.hedge_regret_le`, `Cslib.GameTheory.CostGame.hedgeDist_regret`:
  regret `2 M √(T ln |S i|)` for every player.
* `Cslib.GameTheory.CostGame.timeAverage_hedgeDist_le_add`: the time average of Hedge dynamics is
  a coarse correlated equilibrium up to the slack `2 M √(ln |S i| / T)`.
* `Cslib.GameTheory.CostGame.IsSmooth.sum_hedgeDist_socialCost_le`,
  `Cslib.GameTheory.CostGame.IsSmooth.timeAverage_hedgeDist_socialCost_le`: the price of anarchy
  of Hedge dynamics in smooth games.

## References

* [S. Arora, E. Hazan, S. Kale, *The Multiplicative Weights Update Method: a Meta-Algorithm and
  Applications*][AroraHazanKale2012]
* [T. Roughgarden, *CS364A: Algorithmic Game Theory*, lecture notes][Roughgarden2013CS364A]
-/

public section

namespace Cslib.GameTheory.CostGame

open Finset Cslib.MachineLearning.OnlineLearning.Experts

variable {ι : Type*} {S : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)]

/-! ### Simultaneous multiplicative updates -/

/-- The weights under simultaneous multiplicative updates with factors `φ i`: every weight
starts at `1`. In round `t`, player `i` multiplies the weight of `a` by `φ i` of the expected cost
of `a` against everyone's normalized weights. -/
noncomputable def mwuWeight (G : CostGame ι S) (φ : ι → ℝ → ℝ) : ℕ → ∀ i, S i → ℝ
  | 0 => fun _ _ => 1
  | t + 1 => fun i a => mwuWeight G φ t i a *
      φ i (G.deviationCost (fun j b => mwuWeight G φ t j b / ∑ c, mwuWeight G φ t j c) i a)

/-- The mixed strategies in round `t` under simultaneous multiplicative updates: the weights
normalized by their sum. -/
noncomputable def mwuProb (G : CostGame ι S) (φ : ι → ℝ → ℝ) (t : ℕ) (i : ι) (a : S i) : ℝ :=
  G.mwuWeight φ t i a / ∑ b, G.mwuWeight φ t i b

/-- The loss sequence faced by player `i`: its expected cost vector in each round. -/
noncomputable def mwuLoss (G : CostGame ι S) (φ : ι → ℝ → ℝ) (i : ι) (t : ℕ) (a : S i) : ℝ :=
  G.deviationCost (G.mwuProb φ t) i a

/-- In the first round every player plays the uniform distribution. -/
theorem mwuProb_zero (G : CostGame ι S) (φ : ι → ℝ → ℝ) (i : ι) (a : S i) :
    G.mwuProb φ 0 i a = 1 / Fintype.card (S i) := by
  simp only [mwuProb, mwuWeight, sum_const, card_univ, nsmul_eq_mul, mul_one]

/-- The single-learner weights against the losses of player `i` are its weights in the
simultaneous dynamics. -/
theorem weight_mwuLoss (G : CostGame ι S) (φ : ι → ℝ → ℝ) (i : ι) (t : ℕ) :
    weight (φ i) (G.mwuLoss φ i) t = fun a => G.mwuWeight φ t i a := by
  induction t with
  | zero =>
    funext a
    rw [weight_zero]
    rfl
  | succ t ih =>
    funext a
    rw [weight_succ, ih]
    rfl

/-- **Each player runs the single-learner multiplicative update**: the mixed strategies of player
`i` are those of the multiplicative update with factor `φ i` against the loss sequence that the
dynamics produce for `i`. -/
theorem prob_mwuLoss (G : CostGame ι S) (φ : ι → ℝ → ℝ) (i : ι) (t : ℕ) :
    prob (φ i) (G.mwuLoss φ i) t = G.mwuProb φ t i := by
  funext a
  rw [prob, potential, weight_mwuLoss]
  rfl

/-! ### Hedge dynamics -/

/-- **Hedge dynamics** with cost bound `M` and horizon `T`: the mixed strategies in round `t` when
every player `i` runs Hedge with the tuned learning rate `√(ln |S i| / T)` on the costs divided by
`M`. -/
noncomputable def hedgeProb (G : CostGame ι S) (M : ℝ) (T t : ℕ) : ∀ i, S i → ℝ :=
  G.mwuProb (fun i x => hedgeFactor √(Real.log (Fintype.card (S i)) / T) (x / M)) t

variable {G : CostGame ι S} {M : ℝ} {T : ℕ}

/-- In the first round of Hedge dynamics every player plays the uniform distribution. -/
theorem hedgeProb_zero (i : ι) (a : S i) : G.hedgeProb M T 0 i a = 1 / Fintype.card (S i) :=
  mwuProb_zero G _ i a

theorem hedgeProb_nonneg (t : ℕ) (i : ι) (a : S i) : 0 ≤ G.hedgeProb M T t i a := by
  rw [hedgeProb, ← prob_mwuLoss]
  exact prob_nonneg (fun _ _ _ => by rw [hedgeFactor_apply]; exact Real.exp_pos _) a

theorem sum_hedgeProb [∀ i, Nonempty (S i)] (t : ℕ) (i : ι) :
    ∑ a, G.hedgeProb M T t i a = 1 := by
  rw [hedgeProb, ← prob_mwuLoss]
  exact sum_prob (fun _ _ _ => by rw [hedgeFactor_apply]; exact Real.exp_pos _)

/-- **Regret of Hedge dynamics**: if the costs are bounded by `M > 0` in absolute value and
`ln |S i| ≤ T`, then under Hedge dynamics with horizon `T`, the total expected cost of player `i`
over the first `T` rounds exceeds that of every fixed strategy `a` by at most
`2 M √(T ln |S i|)`. -/
theorem hedge_regret_le [∀ i, Nonempty (S i)] (hM : 0 < M) (hc : ∀ i s, |G.cost i s| ≤ M)
    {i : ι} (hT : Real.log (Fintype.card (S i)) ≤ T) (a : S i) :
    ∑ t ∈ range T, ∑ b, G.hedgeProb M T t i b * G.deviationCost (G.hedgeProb M T t) i b
      ≤ ∑ t ∈ range T, G.deviationCost (G.hedgeProb M T t) i a
        + 2 * M * √(T * Real.log (Fintype.card (S i))) := by
  set D := fun t b => G.deviationCost (G.hedgeProb M T t) i b with hD
  set q := fun t b => G.hedgeProb M T t i b with hq
  rcases Nat.lt_or_ge (Fintype.card (S i)) 2 with h1 | h2
  · -- With a single strategy there is no regret.
    have hone : Fintype.card (S i) = 1 := by
      have := Fintype.card_pos (α := S i)
      omega
    obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp hone
    rw [hone, Nat.cast_one, Real.log_one, mul_zero, Real.sqrt_zero, mul_zero, add_zero]
    refine le_of_eq (sum_congr rfl fun t _ => ?_)
    calc ∑ b, q t b * D t b = ∑ b, q t b * D t a :=
          sum_congr rfl fun b _ => by rw [hx b, hx a]
      _ = D t a := by rw [← sum_mul, sum_hedgeProb, one_mul]
  · set ℓ : ℕ → S i → ℝ := fun t b => D t b / M with hℓ
    have hprob : ∀ t, prob (hedgeFactor √(Real.log (Fintype.card (S i)) / T)) ℓ t = q t :=
      fun t => G.prob_mwuLoss
        (fun i x => hedgeFactor √(Real.log (Fintype.card (S i)) / T) (x / M)) i t
    have hℓ1 : ∀ s < T, ∀ b, |ℓ s b| ≤ 1 := fun s _ b => by
      rw [hℓ, abs_div, abs_of_pos hM, div_le_one hM]
      exact G.abs_deviationCost_le (fun j b => hedgeProb_nonneg s j b)
        (fun j => sum_hedgeProb s j) (hc i) b
    have h := hedge_regret_le_sqrt h2 hT hℓ1 a
    simp only [hprob] at h
    simp only [hℓ] at h
    have e1 : ∑ t ∈ range T, ∑ b, q t b * (D t b / M)
        = (∑ t ∈ range T, ∑ b, q t b * D t b) / M := by
      rw [sum_div]
      refine sum_congr rfl fun t _ => ?_
      rw [sum_div]
      exact sum_congr rfl fun b _ => (mul_div_assoc _ _ _).symm
    rw [e1, ← sum_div, div_le_iff₀ hM, add_mul, div_mul_cancel₀ _ hM.ne'] at h
    linarith

variable [∀ i, Nonempty (S i)]

/-- The outcome distribution in round `t` of Hedge dynamics: the product of the players' mixed
strategies. -/
noncomputable def hedgeDist (G : CostGame ι S) (M : ℝ) (T t : ℕ) :
    Convexity.StdSimplex ℝ (∀ i, S i) :=
  productDist (fun i a => hedgeProb_nonneg (G := G) (M := M) (T := T) t i a)
    (fun i => sum_hedgeProb (G := G) (M := M) (T := T) t i)

/-- **Regret of Hedge dynamics** in terms of the outcome distributions: with costs bounded by
`M > 0` and `ln |S j| ≤ T` for every player `j`, player `i` has regret at most `2 M √(T ln |S i|)`
against every fixed strategy `a`. -/
theorem hedgeDist_regret (hM : 0 < M) (hc : ∀ i s, |G.cost i s| ≤ M)
    (hT : ∀ i, Real.log (Fintype.card (S i)) ≤ T) (i : ι) (a : S i) :
    ∑ t ∈ range T, (G.hedgeDist M T t).weights.sum (fun s w => w * G.cost i s)
      ≤ ∑ t ∈ range T, (G.hedgeDist M T t).weights.sum
          (fun s w => w * G.cost i (Function.update s i a))
        + 2 * M * √(T * Real.log (Fintype.card (S i))) := by
  simp only [hedgeDist, productDist_sum]
  refine le_trans (le_of_eq (sum_congr rfl fun t _ =>
    (sum_mul_deviationCost G _ (sum_hedgeProb t i)).symm)) ?_
  simpa only [deviationCost_def] using hedge_regret_le hM hc (hT i) a

private theorem sqrt_mul_div_self {T L : ℝ} (hT : 0 < T) : √(T * L) / T = √(L / T) := by
  have hs : √T * √T = T := Real.mul_self_sqrt hT.le
  have hs0 : 0 < √T := Real.sqrt_pos.mpr hT
  rw [Real.sqrt_mul hT.le, Real.sqrt_div' L hT.le, div_eq_div_iff hT.ne' hs0.ne']
  linear_combination √L * hs

/-- **Hedge dynamics yield approximate coarse correlated equilibria**: with costs bounded by
`M > 0` and `ln |S j| ≤ T` for every player `j`, the time average of the first `T > 0` outcome
distributions of Hedge dynamics satisfies the coarse correlated equilibrium inequalities up to the
slack `2 M √(ln |S i| / T)` for player `i`. -/
theorem timeAverage_hedgeDist_le_add (hM : 0 < M) (hc : ∀ i s, |G.cost i s| ≤ M) (hT0 : 0 < T)
    (hT : ∀ i, Real.log (Fintype.card (S i)) ≤ T) (i : ι) (a : S i) :
    (timeAverage (G.hedgeDist M T) T hT0).weights.sum (fun s w => w * G.cost i s)
      ≤ (timeAverage (G.hedgeDist M T) T hT0).weights.sum
          (fun s w => w * G.cost i (Function.update s i a))
        + 2 * M * √(Real.log (Fintype.card (S i)) / T) := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT0
  have h := timeAverage_le_add hT0 (hedgeDist_regret hM hc hT) i a
  rwa [mul_div_assoc, sqrt_mul_div_self hT'] at h

/-- **The price of anarchy of Hedge dynamics**, total form: if `G` is `(λ, μ)`-smooth with
`μ < 1`, its costs are bounded by `M > 0` and `ln |S i| ≤ T` for every player `i`, then the total
expected social cost of the first `T` rounds of Hedge dynamics is at most
`(T λ socialCost s' + 2 M ∑ i, √(T ln |S i|)) / (1 - μ)` for every profile `s'`. -/
theorem IsSmooth.sum_hedgeDist_socialCost_le {lam μ : ℝ} (hG : G.IsSmooth lam μ) (hμ : μ < 1)
    (hM : 0 < M) (hc : ∀ i s, |G.cost i s| ≤ M) (hT : ∀ i, Real.log (Fintype.card (S i)) ≤ T)
    (s' : ∀ i, S i) :
    ∑ t ∈ range T, (G.hedgeDist M T t).weights.sum (fun s w => w * G.socialCost s)
      ≤ (T * lam * G.socialCost s'
          + 2 * M * ∑ i, √(T * Real.log (Fintype.card (S i)))) / (1 - μ) := by
  rw [mul_sum]
  exact hG.sum_expected_socialCost_le hμ (hedgeDist_regret hM hc hT) s'

/-- **The price of anarchy of Hedge dynamics** ([Roughgarden2013CS364A], Lecture 17,
Corollary 3.3, with Hedge as the no-regret algorithm): if `G` is `(λ, μ)`-smooth with `μ < 1`, its
costs are bounded by `M > 0` and `ln |S i| ≤ T` for every player `i`, then the expected social
cost under the time average of the first `T > 0` outcome distributions of Hedge dynamics is at most
`(λ socialCost s' + 2 M ∑ i, √(ln |S i| / T)) / (1 - μ)` for every profile `s'`. -/
theorem IsSmooth.timeAverage_hedgeDist_socialCost_le {lam μ : ℝ} (hG : G.IsSmooth lam μ)
    (hμ : μ < 1) (hM : 0 < M) (hc : ∀ i s, |G.cost i s| ≤ M) (hT0 : 0 < T)
    (hT : ∀ i, Real.log (Fintype.card (S i)) ≤ T) (s' : ∀ i, S i) :
    (timeAverage (G.hedgeDist M T) T hT0).weights.sum (fun s w => w * G.socialCost s)
      ≤ (lam * G.socialCost s' + 2 * M * ∑ i, √(Real.log (Fintype.card (S i)) / T)) / (1 - μ) := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT0
  have h := hG.timeAverage_expected_socialCost_le hμ hT0 (hedgeDist_regret hM hc hT) s'
  refine h.trans (le_of_eq ?_)
  simp only [mul_div_assoc, sqrt_mul_div_self hT', mul_sum]

end Cslib.GameTheory.CostGame
