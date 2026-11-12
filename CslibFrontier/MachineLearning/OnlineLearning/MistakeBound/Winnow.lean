/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Winnow and monotone disjunctions

WINNOW1 [Littlestone1988, §5, Algorithm 3] is an online learner on `Fin n → Bool` for
**monotone disjunctions** `x ↦ ∨_{i ∈ R} xᵢ` (`monotoneDisjunction R`). It keeps a nonnegative
weight `wᵢ` per variable, all starting at `1`, and predicts `true` when the score
`∑_{xᵢ} wᵢ` exceeds the threshold `θ` and `false` when it is below `θ`; the prediction at
`∑_{xᵢ} wᵢ = θ` is the parameter `tie`, since the source leaves that choice open. Weights change
only on mistakes and only on active variables. A false negative multiplies the active weights by
`α > 1` (a *promotion step*), and a false positive sets them to `0` (an *elimination step*).

**Littlestone's Theorem 7.** If every example is labelled by a monotone disjunction of `k`
variables, `α > 1` and `θ ≥ 1 / α`, then WINNOW1 makes at most `α k (log_α θ + 1) + n / θ`
mistakes on any sequence (`mistakes_winnow_le`). The bound does not depend on the length of the
sequence, and only logarithmically on the number `n` of variables. The proof counts the
promotion steps `u` and the elimination steps `v` (`winnow_invariant`): the total weight is at
most `n + (α - 1) θ u - θ v` and stays nonnegative (Lemma 3), each weight stays at most `α θ`
(Lemma 4, `winnowWeight_le`), and the product of the weights of the relevant variables is at least
`α ^ u` (Lemma 5).

The source's specializations are `mistakes_winnow_two_le` (`α = 2`, `θ = n`: at most
`2 k (log₂ n + 1) + 1`) and `mistakes_winnow_le_div` (`θ = n / α`: at most `α k log_α n + α`).
For a target of `1 ≤ k ≤ n` variables, `mistakes_winnow_two_div_card_le` takes `α = 2` and
`θ = n / k`, giving `2 k log₂ (n / k) + 3 k`. For `2 k ≤ n` this matches Littlestone's lower bound
`k ⌊log₂ (n / k)⌋` (in `MonotoneDisjunctions`) up to a constant factor. The hypothesis `1 ≤ k`
is needed: for `k = 0` the threshold `n / k` is `0`. `mistakeBound_winnow_le` restates Theorem 7
over the class `monotoneDisjunctions n k` of disjunctions of exactly `k` variables.

The weights are real numbers, so WINNOW1 is a mathematical specification here: no bit cost or
running time is charged. Winnow updates multiplicatively, like the experts algorithms of
`OnlineLearning.MultiplicativeUpdate`, but it is driven by mistakes, its weights are not
normalized, and it predicts by a threshold, so it is defined directly as an `OnlineLearner`.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.monotoneDisjunction`: the disjunction of the
  variables in `R`.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.monotoneDisjunctions`: the class of
  disjunctions of exactly `k` of `n` variables.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.winnowWeight`: WINNOW1's weights after a
  history.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.winnow`: WINNOW1 as an online learner.

## Main results

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.mistakes_winnow_le`: Littlestone's
  Theorem 7.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.mistakeBound_winnow_le`: the same bound as a
  mistake bound for the class of `k`-literal monotone disjunctions.

## References

* [N. Littlestone, *Learning quickly when irrelevant attributes abound: a new linear-threshold
  algorithm*][Littlestone1988]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.MistakeBound

open PACLearning (ConceptClass)

variable {n : ℕ}

/-! ### Monotone disjunctions -/

/-- The monotone disjunction `x ↦ ∨_{i ∈ R} xᵢ` of the variables in `R`
[Littlestone1988, §5, Definition 5]. -/
def monotoneDisjunction (R : Finset (Fin n)) : (Fin n → Bool) → Bool :=
  fun x => decide (∃ i ∈ R, x i = true)

/-- The class of monotone disjunctions of exactly `k` of the `n` variables. -/
def monotoneDisjunctions (n k : ℕ) : ConceptClass (Fin n → Bool) Bool :=
  {f | ∃ R : Finset (Fin n), R.card = k ∧ monotoneDisjunction R = f}

theorem monotoneDisjunction_eq_true {R : Finset (Fin n)} {x : Fin n → Bool} :
    monotoneDisjunction R x = true ↔ ∃ i ∈ R, x i = true := by
  simp [monotoneDisjunction]

theorem monotoneDisjunction_eq_false {R : Finset (Fin n)} {x : Fin n → Bool} :
    monotoneDisjunction R x = false ↔ ∀ i ∈ R, x i = false := by
  simp [monotoneDisjunction]

theorem mem_monotoneDisjunctions {k : ℕ} {f : (Fin n → Bool) → Bool} :
    f ∈ monotoneDisjunctions n k ↔ ∃ R : Finset (Fin n), R.card = k ∧ monotoneDisjunction R = f :=
  Iff.rfl

/-- There are disjunctions of exactly `k` of `n` variables iff `k ≤ n`. -/
theorem monotoneDisjunctions_nonempty_iff {k : ℕ} :
    (monotoneDisjunctions n k).Nonempty ↔ k ≤ n := by
  constructor
  · rintro ⟨_, R, rfl, -⟩
    exact (Finset.card_le_univ R).trans_eq (Fintype.card_fin n)
  · intro hk
    obtain ⟨R, -, hR⟩ := Finset.exists_subset_card_eq (s := Finset.univ (α := Fin n))
      (by simpa using hk)
    exact ⟨_, R, hR, rfl⟩

/-! ### WINNOW1 -/

/-- The score `∑_{xᵢ} wᵢ` of the instance `x` under the weights `w`. -/
def winnowScore (w : Fin n → ℝ) (x : Fin n → Bool) : ℝ :=
  ∑ i, if x i then w i else 0

/-- WINNOW1's prediction: `true` above the threshold `θ`, `false` below it, and `tie` at it. -/
noncomputable def winnowPredict (θ : ℝ) (tie : Bool) (w : Fin n → ℝ) (x : Fin n → Bool) : Bool :=
  if winnowScore w x = θ then tie else decide (θ < winnowScore w x)

/-- A promotion step: multiply the weights of the active variables by `α`
[Littlestone1988, §5, Table 2]. -/
def winnowPromote (α : ℝ) (w : Fin n → ℝ) (x : Fin n → Bool) : Fin n → ℝ :=
  fun i => if x i then α * w i else w i

/-- An elimination step: set the weights of the active variables to `0`
[Littlestone1988, §5, Table 2]. -/
def winnowEliminate (w : Fin n → ℝ) (x : Fin n → Bool) : Fin n → ℝ :=
  fun i => if x i then 0 else w i

/-- One round of WINNOW1 on the example `(x, y)`: keep the weights on a correct prediction,
promote on a false negative and eliminate on a false positive. -/
noncomputable def winnowStep (α θ : ℝ) (tie : Bool) (w : Fin n → ℝ) (p : (Fin n → Bool) × Bool) :
    Fin n → ℝ :=
  if winnowPredict θ tie w p.1 = p.2 then w
  else if p.2 then winnowPromote α w p.1 else winnowEliminate w p.1

/-- WINNOW1's weights after the history `h`, starting from all ones. -/
noncomputable def winnowWeight (α θ : ℝ) (tie : Bool) (h : List ((Fin n → Bool) × Bool)) :
    Fin n → ℝ :=
  h.foldl (winnowStep α θ tie) fun _ => 1

/-- WINNOW1 [Littlestone1988, §5, Algorithm 3] with update factor `α`, threshold `θ` and
prediction `tie` at the threshold. -/
noncomputable def winnow (α θ : ℝ) (tie : Bool) : OnlineLearner (Fin n → Bool) := fun h x =>
  winnowPredict θ tie (winnowWeight α θ tie h) x

/-! ### Basic facts -/

theorem winnowScore_def (w : Fin n → ℝ) (x : Fin n → Bool) :
    winnowScore w x = ∑ i, if x i then w i else 0 := by
  rw [winnowScore]

theorem winnowPredict_of_eq {θ : ℝ} (tie : Bool) {w : Fin n → ℝ} {x : Fin n → Bool}
    (h : winnowScore w x = θ) : winnowPredict θ tie w x = tie := by
  rw [winnowPredict, ite_eq_left h]

theorem winnowPredict_of_lt {θ : ℝ} (tie : Bool) {w : Fin n → ℝ} {x : Fin n → Bool}
    (h : winnowScore w x < θ) : winnowPredict θ tie w x = false := by
  rw [winnowPredict, ite_eq_right h.ne, decide_eq_false_iff_not, not_lt]
  exact h.le

theorem winnowPredict_of_gt {θ : ℝ} (tie : Bool) {w : Fin n → ℝ} {x : Fin n → Bool}
    (h : θ < winnowScore w x) : winnowPredict θ tie w x = true := by
  rw [winnowPredict, ite_eq_right h.ne', decide_eq_true h]

theorem winnowPromote_apply (α : ℝ) (w : Fin n → ℝ) (x : Fin n → Bool) (i : Fin n) :
    winnowPromote α w x i = if x i then α * w i else w i := by
  rw [winnowPromote]

theorem winnowEliminate_apply (w : Fin n → ℝ) (x : Fin n → Bool) (i : Fin n) :
    winnowEliminate w x i = if x i then 0 else w i := by
  rw [winnowEliminate]

theorem winnowStep_of_eq {α θ : ℝ} {tie : Bool} {w : Fin n → ℝ} {p : (Fin n → Bool) × Bool}
    (h : winnowPredict θ tie w p.1 = p.2) : winnowStep α θ tie w p = w := by
  rw [winnowStep, ite_eq_left h]

theorem winnowStep_promote {α θ : ℝ} {tie : Bool} {w : Fin n → ℝ} {x : Fin n → Bool}
    (h : winnowPredict θ tie w x = false) :
    winnowStep α θ tie w (x, true) = winnowPromote α w x := by
  rw [winnowStep, ite_eq_right (by simp [h])]
  rfl

theorem winnowStep_eliminate {α θ : ℝ} {tie : Bool} {w : Fin n → ℝ} {x : Fin n → Bool}
    (h : winnowPredict θ tie w x = true) :
    winnowStep α θ tie w (x, false) = winnowEliminate w x := by
  rw [winnowStep, ite_eq_right (by simp [h])]
  rfl

/-- The three cases of a WINNOW1 round on `(x, y)`: a correct prediction keeps the weights, a false
negative promotes and a false positive eliminates. -/
theorem winnowStep_cases (α θ : ℝ) (tie : Bool) (w : Fin n → ℝ) (x : Fin n → Bool) (y : Bool) :
    winnowPredict θ tie w x = y ∧ winnowStep α θ tie w (x, y) = w ∨
      y = true ∧ winnowPredict θ tie w x = false ∧
        winnowStep α θ tie w (x, y) = winnowPromote α w x ∨
      y = false ∧ winnowPredict θ tie w x = true ∧
        winnowStep α θ tie w (x, y) = winnowEliminate w x := by
  by_cases hc : winnowPredict θ tie w x = y
  · exact Or.inl ⟨hc, winnowStep_of_eq hc⟩
  · cases y with
    | true =>
      have hpred : winnowPredict θ tie w x = false := by simpa using hc
      exact Or.inr (Or.inl ⟨rfl, hpred, winnowStep_promote hpred⟩)
    | false =>
      have hpred : winnowPredict θ tie w x = true := by simpa using hc
      exact Or.inr (Or.inr ⟨rfl, hpred, winnowStep_eliminate hpred⟩)

theorem winnow_apply (α θ : ℝ) (tie : Bool) (h : List ((Fin n → Bool) × Bool))
    (x : Fin n → Bool) : winnow α θ tie h x = winnowPredict θ tie (winnowWeight α θ tie h) x := by
  rw [winnow]

theorem winnowScore_le_of_winnowPredict_eq_false {θ : ℝ} {tie : Bool} {w : Fin n → ℝ}
    {x : Fin n → Bool} (h : winnowPredict θ tie w x = false) : winnowScore w x ≤ θ := by
  unfold winnowPredict at h
  split_ifs at h with he
  · exact he.le
  · simpa using h

theorem le_winnowScore_of_winnowPredict_eq_true {θ : ℝ} {tie : Bool} {w : Fin n → ℝ}
    {x : Fin n → Bool} (h : winnowPredict θ tie w x = true) : θ ≤ winnowScore w x := by
  unfold winnowPredict at h
  split_ifs at h with he
  · exact he.ge
  · exact (decide_eq_true_iff.mp h).le

theorem winnowScore_nonneg {w : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i) (x : Fin n → Bool) :
    0 ≤ winnowScore w x :=
  Finset.sum_nonneg fun i _ => by split <;> simp [hw i]

/-- An active weight is at most the score. -/
theorem le_winnowScore {w : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i) {x : Fin n → Bool} {i : Fin n}
    (hi : x i = true) : w i ≤ winnowScore w x := by
  have := Finset.single_le_sum (f := fun j => if x j then w j else 0)
    (fun j _ => by split <;> simp [hw j]) (Finset.mem_univ i)
  simpa only [winnowScore, hi, ↓reduceIte] using this

theorem sum_winnowPromote (α : ℝ) (w : Fin n → ℝ) (x : Fin n → Bool) :
    ∑ i, winnowPromote α w x i = ∑ i, w i + (α - 1) * winnowScore w x := by
  rw [winnowScore, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold winnowPromote
  split <;> ring

theorem sum_winnowEliminate (w : Fin n → ℝ) (x : Fin n → Bool) :
    ∑ i, winnowEliminate w x i = ∑ i, w i - winnowScore w x := by
  rw [winnowScore, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold winnowEliminate
  split <;> ring

theorem winnowPromote_nonneg {α : ℝ} (hα : 0 ≤ α) {w : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i)
    (x : Fin n → Bool) (i : Fin n) : 0 ≤ winnowPromote α w x i := by
  unfold winnowPromote
  split
  · exact mul_nonneg hα (hw i)
  · exact hw i

theorem winnowEliminate_nonneg {w : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i) (x : Fin n → Bool)
    (i : Fin n) : 0 ≤ winnowEliminate w x i := by
  unfold winnowEliminate
  split
  · exact le_rfl
  · exact hw i

@[simp] theorem winnowWeight_nil (α θ : ℝ) (tie : Bool) :
    winnowWeight α θ tie ([] : List ((Fin n → Bool) × Bool)) = fun _ => 1 := by
  simp [winnowWeight]

theorem winnowWeight_append_singleton (α θ : ℝ) (tie : Bool) (h : List ((Fin n → Bool) × Bool))
    (p : (Fin n → Bool) × Bool) :
    winnowWeight α θ tie (h ++ [p]) = winnowStep α θ tie (winnowWeight α θ tie h) p := by
  simp [winnowWeight, List.foldl_append]

theorem winnowStep_nonneg {α θ : ℝ} (hα : 0 ≤ α) {tie : Bool} {w : Fin n → ℝ}
    (hw : ∀ i, 0 ≤ w i) (p : (Fin n → Bool) × Bool) (i : Fin n) :
    0 ≤ winnowStep α θ tie w p i := by
  obtain ⟨x, y⟩ := p
  rcases winnowStep_cases α θ tie w x y with ⟨-, hs⟩ | ⟨-, -, hs⟩ | ⟨-, -, hs⟩ <;> rw [hs]
  · exact hw i
  · exact winnowPromote_nonneg hα hw _ i
  · exact winnowEliminate_nonneg hw _ i

/-- WINNOW1's weights stay nonnegative. -/
theorem winnowWeight_nonneg {α θ : ℝ} (hα : 0 ≤ α) (tie : Bool)
    (h : List ((Fin n → Bool) × Bool)) (i : Fin n) : 0 ≤ winnowWeight α θ tie h i := by
  revert i
  induction h using List.reverseRecOn with
  | nil => simp
  | append_singleton h p ih =>
    intro i
    rw [winnowWeight_append_singleton]
    exact winnowStep_nonneg hα ih p i

/-- Each weight stays at most `α θ` [Littlestone1988, §5, Lemma 4]: a weight is promoted only when
the score, and hence the weight, is at most `θ`. -/
theorem winnowWeight_le {α θ : ℝ} (hα : 1 ≤ α) (hθ : 1 ≤ α * θ) (tie : Bool)
    (h : List ((Fin n → Bool) × Bool)) (i : Fin n) : winnowWeight α θ tie h i ≤ α * θ := by
  induction h using List.reverseRecOn with
  | nil => simpa using hθ
  | append_singleton h p ih =>
    obtain ⟨x, y⟩ := p
    rw [winnowWeight_append_singleton]
    have hw := winnowWeight_nonneg (θ := θ) (zero_le_one.trans hα) tie h
    rcases winnowStep_cases α θ tie (winnowWeight α θ tie h) x y with
      ⟨-, hs⟩ | ⟨-, hpred, hs⟩ | ⟨-, -, hs⟩ <;> rw [hs]
    · exact ih
    · -- a promoted weight is active, so it is at most the score, which is at most `θ`
      have hscore := winnowScore_le_of_winnowPredict_eq_false hpred
      unfold winnowPromote
      split
      · rename_i hx
        exact mul_le_mul_of_nonneg_left ((le_winnowScore hw hx).trans hscore)
          (zero_le_one.trans hα)
      · exact ih
    · unfold winnowEliminate
      split
      · exact zero_le_one.trans hθ
      · exact ih

/-! ### The mistake bound -/

/-- On a promotion step for an example of a disjunction over `R`, some active variable lies in
`R`, so the product of the weights over `R` grows by a factor of at least `α`. -/
theorem mul_prod_le_prod_winnowPromote {α : ℝ} (hα : 1 ≤ α) {w : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i)
    {R : Finset (Fin n)} {x : Fin n → Bool} (hx : ∃ i ∈ R, x i = true) :
    α * ∏ i ∈ R, w i ≤ ∏ i ∈ R, winnowPromote α w x i := by
  obtain ⟨j, hj, hxj⟩ := hx
  rw [← Finset.mul_prod_erase R w hj, ← Finset.mul_prod_erase R _ hj, ← mul_assoc]
  have hj' : winnowPromote α w x j = α * w j := by simp [winnowPromote, hxj]
  rw [hj']
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun i _ => hw i) fun i _ => ?_)
    (mul_nonneg (zero_le_one.trans hα) (hw j))
  unfold winnowPromote
  split
  · nlinarith [hw i]
  · exact le_rfl

/-- An elimination step for an example of a disjunction over `R` leaves the weights over `R`
unchanged. -/
theorem prod_winnowEliminate {w : Fin n → ℝ} {R : Finset (Fin n)} {x : Fin n → Bool}
    (hx : ∀ i ∈ R, x i = false) : ∏ i ∈ R, winnowEliminate w x i = ∏ i ∈ R, w i :=
  Finset.prod_congr rfl fun i hi => by simp [winnowEliminate, hx i hi]

/-- The invariants of WINNOW1 [Littlestone1988, §5, Lemmas 3 and 5]. After the history `h`, the
mistakes on a sequence `S` labelled by the disjunction over `R` split into `u` promotion steps and
`v` elimination steps. Each promotion step adds at most `(α - 1) θ` to the total weight and
multiplies the product of the weights over `R` by at least `α`; each elimination step removes at
least `θ` from the total weight. -/
theorem winnow_invariant {α θ : ℝ} (hα : 1 ≤ α) (tie : Bool) (R : Finset (Fin n))
    (h S : List ((Fin n → Bool) × Bool)) (hS : ∀ p ∈ S, monotoneDisjunction R p.1 = p.2) :
    ∃ u v : ℕ, mistakesFrom (winnow α θ tie) h S = u + v ∧
      ∑ i, winnowWeight α θ tie (h ++ S) i ≤
        ∑ i, winnowWeight α θ tie h i + (α - 1) * θ * u - θ * v ∧
      α ^ u * ∏ i ∈ R, winnowWeight α θ tie h i ≤ ∏ i ∈ R, winnowWeight α θ tie (h ++ S) i := by
  induction S generalizing h with
  | nil => exact ⟨0, 0, by simp⟩
  | cons p S ih =>
    obtain ⟨x, y⟩ := p
    obtain ⟨u, v, hm, hsum, hprod⟩ :=
      ih (h ++ [(x, y)]) fun p hp => hS p (List.mem_cons_of_mem _ hp)
    have hy : monotoneDisjunction R x = y := hS (x, y) List.mem_cons_self
    have happ : h ++ (x, y) :: S = (h ++ [(x, y)]) ++ S := by simp
    rw [happ, mistakesFrom_cons]
    rw [winnowWeight_append_singleton] at hsum hprod
    rw [winnow_apply]
    set w := winnowWeight α θ tie h with hw_def
    have hw : ∀ i, 0 ≤ w i := winnowWeight_nonneg (zero_le_one.trans hα) tie h
    rcases winnowStep_cases α θ tie w x y with
      ⟨hc, hstep⟩ | ⟨rfl, hpred, hstep⟩ | ⟨rfl, hpred, hstep⟩
    · rw [hstep] at hsum hprod
      exact ⟨u, v, by simp [hc, hm], hsum, hprod⟩
    · -- a promotion step: the total weight grows by at most `(α - 1) θ`
      rw [hstep, sum_winnowPromote] at hsum
      rw [hstep] at hprod
      have hs := winnowScore_le_of_winnowPredict_eq_false hpred
      have hR := mul_prod_le_prod_winnowPromote hα hw (monotoneDisjunction_eq_true.mp hy)
      refine ⟨u + 1, v, by simp [hpred, hm]; ring, ?_, ?_⟩
      · push_cast
        have : (α - 1) * winnowScore w x ≤ (α - 1) * θ := by gcongr
        linarith
      · rw [pow_succ, mul_assoc]
        have hu : 0 ≤ α ^ u := pow_nonneg (zero_le_one.trans hα) u
        exact (mul_le_mul_of_nonneg_left hR hu).trans hprod
    · -- an elimination step: the total weight drops by at least `θ`
      rw [hstep, sum_winnowEliminate] at hsum
      rw [hstep, prod_winnowEliminate (monotoneDisjunction_eq_false.mp hy)] at hprod
      have hs := le_winnowScore_of_winnowPredict_eq_true hpred
      refine ⟨u, v + 1, by simp [hpred, hm]; ring, ?_, hprod⟩
      push_cast
      linarith

/-- **Littlestone's Theorem 7** [Littlestone1988, §5]: if every example of `S` is labelled by the
monotone disjunction of the `k` variables in `R`, `α > 1` and `θ ≥ 1 / α`, then WINNOW1 makes at
most `α k (log_α θ + 1) + n / θ` mistakes on `S`, for every prediction `tie` at the threshold. -/
theorem mistakes_winnow_le {α θ : ℝ} (hα : 1 < α) (hθ : 1 ≤ α * θ) (tie : Bool)
    (R : Finset (Fin n)) (S : List ((Fin n → Bool) × Bool))
    (hS : ∀ p ∈ S, monotoneDisjunction R p.1 = p.2) :
    (mistakes (winnow α θ tie) S : ℝ) ≤ α * R.card * (Real.logb α θ + 1) + n / θ := by
  have hα0 : 0 < α := zero_lt_one.trans hα
  have hθ0 : 0 < θ := by
    by_contra hneg
    have : α * θ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hα0.le (not_lt.mp hneg)
    linarith
  obtain ⟨u, v, hm, hsum, hprod⟩ := winnow_invariant hα.le tie R [] S hS
  simp only [List.nil_append, winnowWeight_nil, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Finset.prod_const_one] at hsum hprod
  change mistakes (winnow α θ tie) S = u + v at hm
  -- the total weight is nonnegative (Lemma 3)
  have hsum0 : 0 ≤ ∑ i, winnowWeight α θ tie S i :=
    Finset.sum_nonneg fun i _ => winnowWeight_nonneg hα0.le tie S i
  -- the weights over `R` are at most `α θ` (Lemmas 4 and 5)
  have hprodle : ∏ i ∈ R, winnowWeight α θ tie S i ≤ (α * θ) ^ R.card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun i _ => winnowWeight_nonneg hα0.le tie S i)
      fun i _ => winnowWeight_le hα.le hθ tie S i
  have hpow : α ^ u ≤ (α * θ) ^ R.card := hprod.trans hprodle
  have hu : (u : ℝ) ≤ R.card * (Real.logb α θ + 1) := by
    have hlog := Real.logb_le_logb_of_le hα (pow_pos hα0 u) hpow
    rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one hα, mul_one,
      Real.logb_mul hα0.ne' hθ0.ne', Real.logb_self_eq_one hα] at hlog
    linarith
  have hv : (v : ℝ) ≤ n / θ + (α - 1) * u := by
    rw [div_add' _ _ _ hθ0.ne', le_div_iff₀ hθ0]
    nlinarith
  rw [hm]
  push_cast
  nlinarith

/-- Theorem 7 with `α = 2` and `θ = n` [Littlestone1988, §5]: at most `2 k (log₂ n + 1) + 1`
mistakes. -/
theorem mistakes_winnow_two_le (hn : 1 ≤ n) (tie : Bool) (R : Finset (Fin n))
    (S : List ((Fin n → Bool) × Bool)) (hS : ∀ p ∈ S, monotoneDisjunction R p.1 = p.2) :
    (mistakes (winnow 2 n tie) S : ℝ) ≤ 2 * R.card * (Real.logb 2 n + 1) + 1 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := mistakes_winnow_le (α := 2) (θ := n) one_lt_two (by linarith) tie R S hS
  rwa [div_self (by positivity : (n : ℝ) ≠ 0)] at h

/-- Theorem 7 with `θ = n / α` [Littlestone1988, §5]: at most `α k log_α n + α` mistakes. -/
theorem mistakes_winnow_le_div {α : ℝ} (hα : 1 < α) (hn : 1 ≤ n) (tie : Bool)
    (R : Finset (Fin n)) (S : List ((Fin n → Bool) × Bool))
    (hS : ∀ p ∈ S, monotoneDisjunction R p.1 = p.2) :
    (mistakes (winnow α (n / α) tie) S : ℝ) ≤ α * R.card * Real.logb α n + α := by
  have hα0 : 0 < α := zero_lt_one.trans hα
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hmul : α * (n / α) = n := by field_simp
  have hdiv : (n : ℝ) / (n / α) = α := by field_simp
  have h := mistakes_winnow_le hα (θ := n / α) (by rw [hmul]; exact_mod_cast hn) tie R S hS
  rwa [Real.logb_div hn0.ne' hα0.ne', Real.logb_self_eq_one hα, sub_add_cancel, hdiv] at h

/-- Theorem 7 with `α = 2` and `θ = n / k` for a disjunction of `1 ≤ k ≤ n` variables: at most
`2 k log₂ (n / k) + 3 k` mistakes. This specialization is derived here from Theorem 7; compare the
lower bound `k ⌊log₂ (n / k)⌋` of `MonotoneDisjunctions`. -/
theorem mistakes_winnow_two_div_card_le (tie : Bool) (R : Finset (Fin n)) (hR : 1 ≤ R.card)
    (S : List ((Fin n → Bool) × Bool)) (hS : ∀ p ∈ S, monotoneDisjunction R p.1 = p.2) :
    (mistakes (winnow 2 (n / R.card) tie) S : ℝ) ≤
      2 * R.card * Real.logb 2 (n / R.card) + 3 * R.card := by
  have hk : (1 : ℝ) ≤ R.card := by exact_mod_cast hR
  have hkn : (R.card : ℝ) ≤ n := by
    exact_mod_cast (Finset.card_le_univ R).trans_eq (Fintype.card_fin n)
  have hk0 : (0 : ℝ) < R.card := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ : 1 ≤ 2 * ((n : ℝ) / R.card) := by
    rw [mul_div_assoc', le_div_iff₀ hk0]; linarith
  have hdiv : (n : ℝ) / (n / R.card) = R.card := by field_simp
  have h := mistakes_winnow_le (α := 2) one_lt_two hθ tie R S hS
  rw [hdiv] at h
  linarith

/-- Theorem 7 as a mistake bound for the class of disjunctions of exactly `k` of the `n`
variables [Littlestone1988, §5]. -/
theorem mistakeBound_winnow_le {α θ : ℝ} (hα : 1 < α) (hθ : 1 ≤ α * θ) (tie : Bool) (k : ℕ) :
    mistakeBound (winnow α θ tie) (monotoneDisjunctions n k) ≤
      (⌊α * k * (Real.logb α θ + 1) + n / θ⌋₊ : ℕ) := by
  refine mistakeBound_le_iff.mpr fun S hS => ?_
  obtain ⟨c, ⟨R, hRk, rfl⟩, hcS⟩ := realizable_iff.mp hS
  have h := mistakes_winnow_le hα hθ tie R S hcS
  rw [hRk] at h
  exact_mod_cast Nat.le_floor h

end Cslib.MachineLearning.OnlineLearning.MistakeBound
