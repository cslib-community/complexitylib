/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.FPAUS.Counting
public import Complexity.Languages.Probabilistic.Retry
public import Complexity.Languages.Probabilistic.UniformNat
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Map
import Mathlib.Data.Nat.Size

/-!
# Approximate counting gives almost uniform sampling for self-reducible families

For a one-bit self-reducible witness family (`Cslib.Complexity.SelfReducible`), a randomized
approximate counter yields an almost uniform sampler [Jerrum, Valiant and
Vazirani][JerrumValiantVazirani1986], [Sinclair, Lecture 4, Section 4.2.3][Sinclair2025]. This file
builds the sampler from a counter `A` (with `A y p t` an estimate `num / den` of `|W y|`) and proves
that its **output law** is within statistical distance `2 ^ (-q)` of the uniform law on the
witnesses.

## The construction

Let `ℓ = R.len x` be the witness length. The sampler estimates `|W x|` once
(`Cslib.Complexity.SelfReducible.nodeEstimate`, exact at witness length `0`), then runs up to
`trials q = 6 (q + 2)` independent trials (`Cslib.OracleComp.retry`) and returns the first
witness found, or `none`. A trial (`Cslib.Complexity.SelfReducible.trial`) walks down the
self-reduction tree. At a node with estimate `a / b` it estimates both children (`a_c / b_c`) and
moves to child `c` with probability about `(1 - 1 / m) (a_c / b_c) / (a / b)`, rejecting with the
remaining probability. Here the damping is `m = 2 ℓ + 2`, and the coin consists of `precision ℓ q`
extra fair bits beyond the size of the common denominator. The counter is called with relative
error `1 / (4 ℓ + 3)` and confidence parameter `precision ℓ q = q + ℓ + 4`.

Because the leaf estimates are exact, the probability of reaching a witness telescopes to about
`(1 - 1 / m) ^ ℓ · b / a` for the root estimate `a / b`, the same for every witness. This spreads
the single final rejection step of Sinclair's sketch over the levels, so no path probability needs
to be recorded. With good estimates a trial succeeds with probability at least `1 / 8`. Estimates
that miss their accuracy (probability at most `2 ^ (-t)` each) and coin rounding only lower the
pointwise bounds, and pointwise lower bounds `(1 - ε) / |W x|` suffice for closeness
(`Cslib.Complexity.closeTo_uniformWitness_of_le`).

## Main definitions

* `Cslib.Complexity.SelfReducible.walk`, `Cslib.Complexity.SelfReducible.trial`: one walk down the
  tree, with a branching coin `Cslib.Complexity.SelfReducible.choose` at each level.
* `Cslib.Complexity.SelfReducible.sampler`: the counting-to-sampling sampler.
* `Cslib.Complexity.SelfReducible.GoodEstimate`: an estimate within relative error `1 / p`, exact
  at witness length `0`.
* `Cslib.Complexity.SelfReducible.CounterAccurate`: a counter within relative error `1 / p` with
  probability at least `1 - 2 ^ (-t)` on every instance.

## Main results

* `Cslib.Complexity.SelfReducible.eval_walk_le`, `Cslib.Complexity.SelfReducible.le_eval_walk`:
  upper and lower bounds on the probability that a walk returns a given witness.
* `Cslib.Complexity.SelfReducible.eval_trial_none_le`: at a good root estimate, a trial rejects
  with probability at most `7 / 8`.
* `Cslib.Complexity.SelfReducible.le_eval_retry`: the retry loop's pointwise lower bound.
* `Cslib.Complexity.SelfReducible.closeTo_sampler`: **approximate counting gives almost uniform
  sampling**: the sampler's output law is within statistical distance `2 ^ (-q)` of
  `Cslib.Complexity.uniformWitness (W x)`.
* `Cslib.Complexity.SelfReducible.closeTo_sampler_of_isFPRAS`: the same for an FPRAS.

## Scope

* This file proves the **output-distribution** half of `Cslib.Complexity.IsFPAUS`. The runtime
  half, and with it `FPRAS ⇒ FPAUS` as a class inclusion, is
  `Cslib.Complexity.SelfReducible.isFPAUS_of_isFPRAS` in
  `Complexity.Computability.Complexity.Classes.FPAUS.OfFPRAS`. The sampler makes at most
  `1 + 2 ℓ · trials q` counter calls, linear in `q`.
* The self-reduction fixes one bit per step (`Cslib.Complexity.SelfReducible`).
* The counter must be accurate to relative error `1 / (4 ℓ + 3)` on every intermediate instance,
  as in Sinclair's sketch (accuracy `1 + O(1 / ℓ)`). Sinclair and Jerrum's weighted random walk,
  which tolerates polynomial errors [Sinclair and Jerrum][SinclairJerrum1989], is not formalized.

## References

* [M. R. Jerrum, L. G. Valiant, V. V. Vazirani, *Random generation of combinatorial structures from
  a uniform distribution*][JerrumValiantVazirani1986]
* [A. Sinclair, *CS294 Partition Functions*, Lecture 4, Section 4.2.3][Sinclair2025]
* [A. Sinclair, M. Jerrum, *Approximate counting, uniform generation and rapidly mixing Markov
  chains*][SinclairJerrum1989]
-/

public section

namespace Cslib.Complexity.SelfReducible

open Cslib.Probability Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {W : α → Finset (List Bool)}

/-! ### The sampler -/

/-- The inverse relative error `p = 4 ℓ + 3` requested from the counter, for witness length
`ℓ`. -/
@[expose]
def counterAccuracy (ℓ : ℕ) : ℕ := 4 * ℓ + 3

/-- The precision `q + ℓ + 4`: the counter's confidence parameter, and the number of extra bits of
each branching coin. -/
@[expose]
def precision (ℓ q : ℕ) : ℕ := q + ℓ + 4

/-- The number of trials, `6 (q + 2)`. -/
@[expose]
def trials (q : ℕ) : ℕ := 6 * (q + 2)

/-- The damping denominator `m = 2 ℓ + 2`: every level continues with probability about
`1 - 1 / m`. -/
@[expose]
def damping (ℓ : ℕ) : ℕ := 2 * ℓ + 2

/-- The estimate of the number of witnesses of `y`, as a fraction `(num, den)`: exact at witness
length `0`, otherwise the counter's answer with relative error `1 / p` and confidence `t`. -/
@[expose]
noncomputable def nodeEstimate (R : SelfReducible enc W) (A : α → ℕ → ℕ → ProbComp (ℕ × ℕ))
    (p t : ℕ) (y : α) : ProbComp (ℕ × ℕ) :=
  if R.len y = 0 then pure (if [] ∈ W y then 1 else 0, 1) else A y p t

/-- The outcome of the branching coin for the draw `r`: `some true` below `g₁`, `some false` from
`g₁` to `g₁ + g₀`, and `none` above. -/
@[expose]
def coinOutcome (g₀ g₁ r : ℕ) : Option Bool :=
  if r < g₁ then some true else if r < g₁ + g₀ then some false else none

/-- One draw of `k` fair bits, compared with the thresholds `g₁` and `g₁ + g₀`: `some true` with
probability `min g₁ 2ᵏ / 2ᵏ`, `some false` with probability `g₀ / 2ᵏ` when `g₀ + g₁ ≤ 2ᵏ`, and
`none` otherwise. -/
@[expose]
noncomputable def branch (k g₀ g₁ : ℕ) : ProbComp (Option Bool) :=
  coinOutcome g₀ g₁ <$> ProbComp.sampleBinaryNat k

/-- The branching weight of the child `c` at a node with estimate `e = a / b` whose children have
estimates `e₀ = a₀ / b₀` and `e₁ = a₁ / b₁`: together with `total`, the child `c` is to be chosen
with probability `weight / total = (1 - 1 / m) (a_c / b_c) / (a / b)`. -/
@[expose]
def weight (m : ℕ) (e e₀ e₁ : ℕ × ℕ) (c : Bool) : ℕ :=
  (m - 1) * (cond c e₁ e₀).1 * (cond c e₀ e₁).2 * e.2

/-- The common denominator `m a b₀ b₁` of the branching weights. -/
@[expose]
def total (m : ℕ) (e e₀ e₁ : ℕ × ℕ) : ℕ :=
  m * e.1 * e₀.2 * e₁.2

/-- The number of fair bits of the branching coin: the size of `total` plus `extra`. -/
@[expose]
def coinWidth (m extra : ℕ) (e e₀ e₁ : ℕ × ℕ) : ℕ :=
  (total m e e₀ e₁).size + extra

/-- The branching coin at a node, with `extra` bits of precision beyond the size of `total`:
child `c` with probability about `weight c / total`, otherwise reject. -/
@[expose]
noncomputable def choose (m extra : ℕ) (e e₀ e₁ : ℕ × ℕ) : ProbComp (Option Bool) :=
  branch (coinWidth m extra e e₀ e₁)
    (weight m e e₀ e₁ false * 2 ^ coinWidth m extra e e₀ e₁ / total m e e₀ e₁)
    (weight m e e₀ e₁ true * 2 ^ coinWidth m extra e e₀ e₁ / total m e e₀ e₁)

/-- Continue after the branching coin: reject on `none`, and on `some c` run `next c` and prefix
its result with `c`. -/
@[expose]
noncomputable def descend (next : Bool → ProbComp (Option (List Bool))) :
    Option Bool → ProbComp (Option (List Bool))
  | none => pure none
  | some c => Option.map (c :: ·) <$> next c

/-- One walk down `n` levels from `y`, whose current estimate is `e`: estimate both children,
branch (or reject), and continue in the chosen child. At witness length `0` it returns the empty
word exactly when it is a witness. -/
@[expose]
noncomputable def walk (R : SelfReducible enc W) (A : α → ℕ → ℕ → ProbComp (ℕ × ℕ))
    (p t m extra : ℕ) : ℕ → α → ℕ × ℕ → ProbComp (Option (List Bool))
  | 0, y, _ => pure (if [] ∈ W y then some [] else none)
  | n + 1, y, e => do
    let e₀ ← R.nodeEstimate A p t (R.child y false)
    let e₁ ← R.nodeEstimate A p t (R.child y true)
    let c ← choose m extra e e₀ e₁
    descend (fun c => walk R A p t m extra n (R.child y c) (cond c e₁ e₀)) c

/-- One trial of the sampler for accuracy `q` from the root `x` with estimate `e`: a walk down all
`R.len x` levels with counter accuracy `counterAccuracy`, confidence `precision`, damping
`damping`, and `precision` extra bits per branching coin. -/
@[expose]
noncomputable def trial (R : SelfReducible enc W) (A : α → ℕ → ℕ → ProbComp (ℕ × ℕ)) (x : α)
    (q : ℕ) (e : ℕ × ℕ) : ProbComp (Option (List Bool)) :=
  R.walk A (counterAccuracy (R.len x)) (precision (R.len x) q) (damping (R.len x))
    (precision (R.len x) q) (R.len x) x e

/-- **The counting-to-sampling sampler** with total-variation error `2 ^ (-q)`: estimate the
number of witnesses of `x` once, then run at most `trials q` independent trials from `x` and return
the first witness found, or `none`. -/
@[expose]
noncomputable def sampler (R : SelfReducible enc W) (A : α → ℕ → ℕ → ProbComp (ℕ × ℕ)) (x : α)
    (q : ℕ) : ProbComp (Option (List Bool)) := do
  let e ← R.nodeEstimate A (counterAccuracy (R.len x)) (precision (R.len x) q) x
  Option.join <$> OracleComp.retry (fun o : Option (List Bool) => o.isSome) (R.trial A x q e)
    (trials q)

/-! ### The branching coin -/

section Branch

private theorem card_coinOutcome_some_true (k g₀ g₁ : ℕ) :
    Nat.card {i : Fin (2 ^ k) // coinOutcome g₀ g₁ i.val = some true} = min (2 ^ k) g₁ := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← Fin.card_filter_val_lt]
  congr 1
  ext i
  rw [Finset.mem_filter, Finset.mem_filter]
  unfold coinOutcome
  split_ifs <;> simp_all

private theorem card_coinOutcome_some_false (k g₀ g₁ : ℕ) :
    Nat.card {i : Fin (2 ^ k) // coinOutcome g₀ g₁ i.val = some false} =
      min (2 ^ k) (g₁ + g₀) - min (2 ^ k) g₁ := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsplit : (Finset.univ.filter fun i : Fin (2 ^ k) => i.val < g₁ + g₀) =
      (Finset.univ.filter fun i : Fin (2 ^ k) => i.val < g₁) ∪
        Finset.univ.filter fun i : Fin (2 ^ k) => coinOutcome g₀ g₁ i.val = some false := by
    ext i
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
    unfold coinOutcome
    split_ifs <;> simp_all <;> omega
  have hdisj : Disjoint (Finset.univ.filter fun i : Fin (2 ^ k) => i.val < g₁)
      (Finset.univ.filter fun i : Fin (2 ^ k) => coinOutcome g₀ g₁ i.val = some false) := by
    rw [Finset.disjoint_filter]
    intro i _ h
    simp [coinOutcome, h]
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [← hsplit, Fin.card_filter_val_lt, Fin.card_filter_val_lt] at hcard
  omega

private theorem eval_branch_apply (k g₀ g₁ : ℕ) (c : Bool) :
    ProbComp.eval (branch k g₀ g₁) (some c) =
      (Nat.card {i : Fin (2 ^ k) // coinOutcome g₀ g₁ i.val = some c} : ENNReal) / (2 ^ k : ℕ) := by
  rw [branch, ProbComp.eval_map, ProbComp.eval_sampleBinaryNat, PMF.map_comp,
    PMF.uniformOfFintype_map_apply, Fintype.card_fin]
  rfl

/-- The branching coin picks `c` with probability at most `g_c / 2 ᵏ`. -/
theorem eval_branch_le (k g₀ g₁ : ℕ) (c : Bool) :
    ProbComp.eval (branch k g₀ g₁) (some c) ≤ ((cond c g₁ g₀ : ℕ) : ENNReal) / (2 ^ k : ℕ) := by
  rw [eval_branch_apply]
  gcongr
  cases c
  · rw [card_coinOutcome_some_false]; simp only [Bool.cond_false]; omega
  · rw [card_coinOutcome_some_true]; exact min_le_right _ _

/-- When `g₀ + g₁ ≤ 2 ᵏ` the branching coin picks `c` with probability exactly `g_c / 2 ᵏ`. -/
theorem eval_branch_eq {k g₀ g₁ : ℕ} (h : g₀ + g₁ ≤ 2 ^ k) (c : Bool) :
    ProbComp.eval (branch k g₀ g₁) (some c) = ((cond c g₁ g₀ : ℕ) : ENNReal) / (2 ^ k : ℕ) := by
  rw [eval_branch_apply]
  congr 2
  cases c
  · rw [card_coinOutcome_some_false]; simp only [Bool.cond_false]; omega
  · rw [card_coinOutcome_some_true]; simp only [Bool.cond_true]; omega

end Branch

/-! ### The choice at a node -/

section Choose

private theorem natCast_div_div_le (u D K : ℕ) :
    (((u * K / D : ℕ) : ℝ) / (K : ℝ)) ≤ (u : ℝ) / D := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    simp only [Nat.cast_zero, div_zero]
    positivity
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  rw [div_le_iff₀ hK']
  calc ((u * K / D : ℕ) : ℝ) ≤ ((u * K : ℕ) : ℝ) / D := Nat.cast_div_le
    _ = (u : ℝ) / D * K := by push_cast; ring

private theorem le_natCast_div_div {u D s x : ℕ} (hD : 0 < D) (hs : D < 2 ^ s) (hu : 1 ≤ u) :
    (1 - (1 / 2 : ℝ) ^ x) * ((u : ℝ) / D) ≤
      (((u * 2 ^ (s + x) / D : ℕ) : ℝ) / ((2 ^ (s + x) : ℕ) : ℝ)) := by
  generalize hN : u * 2 ^ (s + x) = N
  have hdiv := Nat.div_add_mod N D
  have hmod := Nat.mod_lt N hD
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hpos : (0 : ℝ) < ((2 ^ (s + x) : ℕ) : ℝ) := by positivity
  rw [le_div_iff₀ hpos]
  have hN' : (N : ℝ) = u * 2 ^ s * 2 ^ x := by rw [← hN]; push_cast; ring
  have hlt : (N : ℝ) < D * ((N / D : ℕ) : ℝ) + D := by
    have : N < D * (N / D) + D := by omega
    exact_mod_cast this
  have hs' : (D : ℝ) + 1 ≤ 2 ^ s := by exact_mod_cast hs
  have hu' : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hx : (0 : ℝ) < 2 ^ x := by positivity
  have hcast : (((2 ^ (s + x) : ℕ) : ℝ)) = 2 ^ s * 2 ^ x := by push_cast; ring
  have key : (1 - (1 / 2 : ℝ) ^ x) * ((u : ℝ) / D) * ((2 ^ (s + x) : ℕ) : ℝ) =
      ((N : ℝ) - u * 2 ^ s) / D := by
    rw [hcast, hN', one_div_pow]
    field_simp
  rw [key, div_le_iff₀ hD']
  nlinarith

/-- The choice at a node picks the child `c` with probability at most `weight c / total`. -/
theorem eval_choose_le (m extra : ℕ) (e e₀ e₁ : ℕ × ℕ) (c : Bool) :
    ProbComp.eval (choose m extra e e₀ e₁) (some c) ≤
      ENNReal.ofReal ((weight m e e₀ e₁ c : ℝ) / total m e e₀ e₁) := by
  refine (eval_branch_le _ _ _ c).trans ?_
  have hK : (0 : ℝ) < ((2 ^ coinWidth m extra e e₀ e₁ : ℕ) : ℝ) := by positivity
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_div_of_pos hK]
  refine ENNReal.ofReal_le_ofReal ?_
  cases c <;> exact natCast_div_div_le _ _ _

/-- When the weights fit (`weight false + weight true ≤ total`), the choice at a node picks a child
`c` of positive weight with probability at least `(1 - 2 ^ (-extra)) weight c / total`. -/
theorem le_eval_choose {m extra : ℕ} {e e₀ e₁ : ℕ × ℕ}
    (hfit : weight m e e₀ e₁ false + weight m e e₀ e₁ true ≤ total m e e₀ e₁) {c : Bool}
    (hc : 1 ≤ weight m e e₀ e₁ c) :
    ENNReal.ofReal ((1 - (1 / 2 : ℝ) ^ extra) *
        ((weight m e e₀ e₁ c : ℝ) / total m e e₀ e₁)) ≤
      ProbComp.eval (choose m extra e e₀ e₁) (some c) := by
  have hD : 0 < total m e e₀ e₁ := by
    cases c <;> omega
  have hsum : weight m e e₀ e₁ false * 2 ^ coinWidth m extra e e₀ e₁ / total m e e₀ e₁ +
      weight m e e₀ e₁ true * 2 ^ coinWidth m extra e e₀ e₁ / total m e e₀ e₁ ≤
        2 ^ coinWidth m extra e e₀ e₁ := by
    refine Nat.div_add_div_le_add_div.trans ?_
    rw [← add_mul]
    exact (Nat.div_le_div_right (Nat.mul_le_mul_right _ hfit)).trans
      (Nat.mul_div_cancel_left _ hD).le
  rw [choose, eval_branch_eq hsum]
  have hK : (0 : ℝ) < ((2 ^ coinWidth m extra e e₀ e₁ : ℕ) : ℝ) := by positivity
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_div_of_pos hK]
  refine ENNReal.ofReal_le_ofReal ?_
  cases c <;> exact le_natCast_div_div hD (Nat.lt_size_self _) hc

end Choose

/-! ### One step of the walk -/

section Step

private theorem eval_map_cons_some_cons (μ : PMF (Option (List Bool))) (b c : Bool)
    (v : List Bool) :
    μ.map (Option.map (b :: ·)) (some (c :: v)) = if b = c then μ (some v) else 0 := by
  split_ifs with h
  · subst h
    exact Probability.PMF.map_apply_of_injective μ
      (Option.map_injective (List.cons_injective)) (some v)
  · have h' : c ≠ b := Ne.symm h
    rw [PMF.map_apply]
    refine tsum_eq_zero_iff.2 fun o => ?_
    cases o <;> simp [h']

private theorem eval_bind_descend_some_cons (μ : PMF (Option Bool))
    (next : Bool → ProbComp (Option (List Bool))) (c : Bool) (v : List Bool) :
    (μ.bind fun o => ProbComp.eval (descend next o)) (some (c :: v)) =
      μ (some c) * ProbComp.eval (next c) (some v) := by
  rw [PMF.bind_apply, tsum_fintype, Fintype.sum_option, Fintype.sum_bool]
  simp only [descend, ProbComp.eval_pure, ProbComp.eval_map, PMF.pure_apply, reduceCtorEq,
    ite_false, mul_zero, zero_add, eval_map_cons_some_cons]
  cases c <;> simp

private theorem eval_bind_descend_some_nil (μ : PMF (Option Bool))
    (next : Bool → ProbComp (Option (List Bool))) :
    (μ.bind fun o => ProbComp.eval (descend next o)) (some []) = 0 := by
  rw [PMF.bind_apply]
  refine tsum_eq_zero_iff.2 fun o => ?_
  cases o with
  | none => simp [descend]
  | some c =>
    rw [descend, ProbComp.eval_map, PMF.map_apply]
    simp

/-- One level of a walk: estimate both children, run the branching coin, and descend. -/
theorem eval_walk_succ (R : SelfReducible enc W) (A : α → ℕ → ℕ → ProbComp (ℕ × ℕ))
    (p t m extra n : ℕ) (y : α) (e : ℕ × ℕ) :
    ProbComp.eval (R.walk A p t m extra (n + 1) y e) =
      (ProbComp.eval (R.nodeEstimate A p t (R.child y false))).bind fun e₀ =>
        (ProbComp.eval (R.nodeEstimate A p t (R.child y true))).bind fun e₁ =>
          (ProbComp.eval (choose m extra e e₀ e₁)).bind fun o =>
            ProbComp.eval (descend
              (fun c => R.walk A p t m extra n (R.child y c) (cond c e₁ e₀)) o) := by
  simp only [walk, ProbComp.eval_bind]

/-- At witness length `0` a walk returns the empty word exactly when it is a witness. -/
theorem eval_walk_zero (R : SelfReducible enc W) (A : α → ℕ → ℕ → ProbComp (ℕ × ℕ))
    (p t m extra : ℕ) (y : α) (e : ℕ × ℕ) (v : List Bool) :
    ProbComp.eval (R.walk A p t m extra 0 y e) (some v) = if v = [] ∧ [] ∈ W y then 1 else 0 := by
  rw [walk, ProbComp.eval_pure, PMF.pure_apply]
  by_cases hv : v = [] <;> by_cases hy : [] ∈ W y <;> simp [hv, hy]

/-- A walk only returns witnesses. -/
theorem eval_walk_eq_zero (R : SelfReducible enc W) (A : α → ℕ → ℕ → ProbComp (ℕ × ℕ))
    (p t m extra : ℕ) :
    ∀ n y, R.len y = n → ∀ e v, v ∉ W y → ProbComp.eval (R.walk A p t m extra n y e) (some v) = 0
  | 0, y, _, e, v, hv => by
    rw [eval_walk_zero]
    split_ifs with h
    · exact absurd (h.1 ▸ h.2) hv
    · rfl
  | n + 1, y, hy, e, v, hv => by
    have hpos : 0 < R.len y := by omega
    rw [eval_walk_succ]
    refine Probability.PMF.bind_apply_of_forall _ fun e₀ => ?_
    refine Probability.PMF.bind_apply_of_forall _ fun e₁ => ?_
    cases v with
    | nil => exact eval_bind_descend_some_nil _ _
    | cons c w =>
      rw [eval_bind_descend_some_cons]
      have hw : w ∉ W (R.child y c) := fun h => hv ((R.cons_mem_iff y hpos c w).2 h)
      rw [eval_walk_eq_zero R A p t m extra n (R.child y c) (by rw [R.len_child y hpos]; omega)
        _ w hw, mul_zero]

end Step

/-! ### Bounds for one walk -/

section Walk

/-- The per-level continuation factor `1 - 1 / m = (m - 1) / m` of a walk with damping `m`. -/
noncomputable def levelFactor (m : ℕ) : ℝ := ((m - 1 : ℕ) : ℝ) / m

/-- The inverse `b / a` of an estimate `a / b`. -/
noncomputable def invEstimate (e : ℕ × ℕ) : ℝ := (e.2 : ℝ) / e.1

/-- The level factor is nonnegative. -/
theorem levelFactor_nonneg (m : ℕ) : 0 ≤ levelFactor m := by
  unfold levelFactor
  positivity

/-- The inverse of an estimate is nonnegative. -/
theorem invEstimate_nonneg (e : ℕ × ℕ) : 0 ≤ invEstimate e := by
  unfold invEstimate
  positivity

private theorem ratio_eq {M' M a b ac bc bc' : ℝ} (hac : ac ≠ 0) (hbc : bc ≠ 0)
    (hbc' : bc' ≠ 0) :
    M' * ac * bc' * b / (M * a * bc * bc') * (bc / ac) = M' / M * (b / a) := by
  rw [div_mul_div_comm, div_mul_div_comm]
  have hP : ac * bc * bc' ≠ 0 := mul_ne_zero (mul_ne_zero hac hbc) hbc'
  calc M' * ac * bc' * b * bc / (M * a * bc * bc' * ac)
      = (M' * b) * (ac * bc * bc') / ((M * a) * (ac * bc * bc')) := by ring_nf
    _ = M' * b / (M * a) := mul_div_mul_right _ _ hP

private theorem ratio_le {M' M a b ac bc bc' : ℝ} (hM' : 0 ≤ M') (hM : 0 ≤ M) (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    M' * ac * bc' * b / (M * a * bc * bc') * (bc / ac) ≤ M' / M * (b / a) := by
  by_cases hac : ac = 0
  · simp only [hac, mul_zero, zero_mul, zero_div, div_zero]
    positivity
  by_cases hbc : bc = 0
  · simp only [hbc, mul_zero, zero_div]
    positivity
  by_cases hbc' : bc' = 0
  · simp only [hbc', mul_zero, zero_mul, div_zero]
    positivity
  exact (ratio_eq hac hbc hbc').le

private theorem total_cast (m : ℕ) (e e₀ e₁ : ℕ × ℕ) (c : Bool) :
    (total m e e₀ e₁ : ℝ) = (m : ℝ) * e.1 * (cond c e₁ e₀).2 * (cond c e₀ e₁).2 := by
  cases c
  · simp only [total, Bool.cond_false, Nat.cast_mul]
  · simp only [total, Bool.cond_true, Nat.cast_mul]
    ring

/-- Choosing a child and continuing with its inverse estimate loses at most the level factor. -/
theorem weight_div_total_mul_le (m : ℕ) (e e₀ e₁ : ℕ × ℕ) (c : Bool) :
    (weight m e e₀ e₁ c : ℝ) / total m e e₀ e₁ * invEstimate (cond c e₁ e₀) ≤
      levelFactor m * invEstimate e := by
  rw [total_cast m e e₀ e₁ c]
  simp only [weight, Nat.cast_mul, invEstimate, levelFactor]
  exact ratio_le (by positivity) (by positivity) (by positivity) (by positivity)

/-- With positive child estimates, choosing a child and continuing with its inverse estimate loses
exactly the level factor. -/
theorem weight_div_total_mul_eq (m : ℕ) (e e₀ e₁ : ℕ × ℕ) (c : Bool)
    (ha : (cond c e₁ e₀).1 ≠ 0) (hb : (cond c e₁ e₀).2 ≠ 0) (hb' : (cond c e₀ e₁).2 ≠ 0) :
    (weight m e e₀ e₁ c : ℝ) / total m e e₀ e₁ * invEstimate (cond c e₁ e₀) =
      levelFactor m * invEstimate e := by
  rw [total_cast m e e₀ e₁ c]
  simp only [weight, Nat.cast_mul, invEstimate, levelFactor]
  exact ratio_eq (by exact_mod_cast ha) (by exact_mod_cast hb) (by exact_mod_cast hb')

/-- **Upper bound for one walk.** From a node at witness length `n` with estimate `e` (exact if
`n = 0`), a walk returns a given word with probability at most `(1 - 1 / m) ^ n · b / a`. -/
theorem eval_walk_le (R : SelfReducible enc W) (A : α → ℕ → ℕ → ProbComp (ℕ × ℕ))
    (p t m extra : ℕ) :
    ∀ n y, R.len y = n → ∀ e,
      (R.len y = 0 → e ∈ (ProbComp.eval (R.nodeEstimate A p t y)).support) → ∀ v,
      ProbComp.eval (R.walk A p t m extra n y e) (some v) ≤
        ENNReal.ofReal (levelFactor m ^ n * invEstimate e)
  | 0, y, hy, e, he, v => by
    rw [eval_walk_zero]
    split_ifs with h
    · have he' := he hy
      simp only [nodeEstimate, hy, h.2, ↓reduceIte, ProbComp.eval_pure, PMF.support_pure,
        Set.mem_singleton_iff] at he'
      subst he'
      simp [invEstimate]
    · exact zero_le
  | n + 1, y, hy, e, _, v => by
    have hpos : 0 < R.len y := by omega
    rw [eval_walk_succ]
    refine Probability.PMF.bind_apply_le_on_support _ fun e₀ he₀ => ?_
    refine Probability.PMF.bind_apply_le_on_support _ fun e₁ he₁ => ?_
    cases v with
    | nil =>
      rw [eval_bind_descend_some_nil]
      exact zero_le
    | cons c w =>
      rw [eval_bind_descend_some_cons]
      have hlen : R.len (R.child y c) = n := by rw [R.len_child y hpos]; omega
      have hsupp : R.len (R.child y c) = 0 →
          cond c e₁ e₀ ∈ (ProbComp.eval (R.nodeEstimate A p t (R.child y c))).support := by
        intro _
        cases c
        · exact he₀
        · exact he₁
      have hw := eval_walk_le R A p t m extra n _ hlen _ hsupp w
      calc ProbComp.eval (choose m extra e e₀ e₁) (some c) *
            ProbComp.eval (R.walk A p t m extra n (R.child y c) (cond c e₁ e₀)) (some w)
          ≤ ENNReal.ofReal ((weight m e e₀ e₁ c : ℝ) / total m e e₀ e₁) *
              ENNReal.ofReal (levelFactor m ^ n * invEstimate (cond c e₁ e₀)) :=
            mul_le_mul' (eval_choose_le _ _ _ _ _ c) hw
        _ = ENNReal.ofReal ((weight m e e₀ e₁ c : ℝ) / total m e e₀ e₁ *
              (levelFactor m ^ n * invEstimate (cond c e₁ e₀))) :=
            (ENNReal.ofReal_mul (by positivity)).symm
        _ ≤ ENNReal.ofReal (levelFactor m ^ (n + 1) * invEstimate e) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have h1 := weight_div_total_mul_le m e e₀ e₁ c
            have h2 : 0 ≤ levelFactor m ^ n := pow_nonneg (levelFactor_nonneg m) n
            calc (weight m e e₀ e₁ c : ℝ) / total m e e₀ e₁ *
                  (levelFactor m ^ n * invEstimate (cond c e₁ e₀))
                = levelFactor m ^ n * ((weight m e e₀ e₁ c : ℝ) / total m e e₀ e₁ *
                    invEstimate (cond c e₁ e₀)) := by ring
              _ ≤ levelFactor m ^ n * (levelFactor m * invEstimate e) :=
                  mul_le_mul_of_nonneg_left h1 h2
              _ = levelFactor m ^ (n + 1) * invEstimate e := by ring

/-- The counter `A` is **accurate** for relative error `1 / p` and confidence `t` when, on every
instance `y`, its estimate of `|W y|` is within relative error `1 / p` with probability at least
`1 - 2 ^ (-t)`. For all `p > 0` and `t` this is the correctness clause of `IsFPRAS`. -/
@[expose]
def CounterAccurate (W : α → Finset (List Bool)) (A : α → ℕ → ℕ → ProbComp (ℕ × ℕ)) (p t : ℕ) :
    Prop :=
  ∀ y, 1 - (1 / 2 : ℝ) ^ t ≤
    ((ProbComp.eval (A y p t)).toOuterMeasure {out | ApproxWithin (W y).card p out.1 out.2}).toReal

/-- An estimate `a / b` of the number of witnesses of `y` is **good** when it is within relative
error `1 / p` and, at witness length `0`, exact. -/
def GoodEstimate (R : SelfReducible enc W) (p : ℕ) (y : α) (e : ℕ × ℕ) : Prop :=
  ApproxWithin (W y).card p e.1 e.2 ∧ (R.len y = 0 → (e.1 : ℝ) = (W y).card * e.2)

/-- A node's estimate is good with probability at least `1 - 2 ^ (-t)`: at witness length `0` it
is exact, otherwise it is the counter's answer. -/
theorem nodeEstimate_good (R : SelfReducible enc W) {A : α → ℕ → ℕ → ProbComp (ℕ × ℕ)} {p t : ℕ}
    (hA : CounterAccurate W A p t) (y : α) :
    1 - (1 / 2 : ℝ) ^ t ≤
      ((ProbComp.eval (R.nodeEstimate A p t y)).toOuterMeasure
        {e | R.GoodEstimate p y e}).toReal := by
  by_cases hy : R.len y = 0
  · have hgood : R.GoodEstimate p y (if [] ∈ W y then 1 else 0, 1) := by
      rcases Finset.subset_singleton_iff.1 (R.subset_singleton_nil hy) with h | h
      · simp [GoodEstimate, ApproxWithin, h]
      · simp [GoodEstimate, ApproxWithin, h]
    have hone : (ProbComp.eval (R.nodeEstimate A p t y)).toOuterMeasure
        {e | R.GoodEstimate p y e} = 1 := by
      simp only [nodeEstimate, hy, ↓reduceIte, ProbComp.eval_pure, PMF.toOuterMeasure_pure_apply,
        Set.mem_ofPred_eq, hgood]
    rw [hone, ENNReal.toReal_one]
    have : (0 : ℝ) ≤ (1 / 2) ^ t := by positivity
    linarith
  · have hset : {e | R.GoodEstimate p y e} = {out | ApproxWithin (W y).card p out.1 out.2} := by
      ext e
      simp only [GoodEstimate, Set.mem_ofPred_eq, hy, IsEmpty.forall_iff, and_true]
    simp only [nodeEstimate, hy, ↓reduceIte, hset]
    exact hA y

private theorem lower_of_approx {c p num den : ℕ} (h : ApproxWithin c p num den) :
    (c : ℝ) * (1 - 1 / p) * den ≤ num := by
  obtain ⟨hden, habs⟩ := h
  have hden' : (0 : ℝ) < den := by exact_mod_cast hden
  have h1 := (abs_le.1 habs).1
  have h2 : (c : ℝ) * (1 - 1 / p) ≤ (num : ℝ) / den := by
    have : (c : ℝ) * (1 - 1 / p) = c - c / p := by ring
    linarith
  exact (le_div_iff₀ hden').1 h2

private theorem upper_of_approx {c p num den : ℕ} (h : ApproxWithin c p num den) :
    (num : ℝ) ≤ (c : ℝ) * (1 + 1 / p) * den := by
  obtain ⟨hden, habs⟩ := h
  have hden' : (0 : ℝ) < den := by exact_mod_cast hden
  have h1 := (abs_le.1 habs).2
  have h2 : (num : ℝ) / den ≤ (c : ℝ) * (1 + 1 / p) := by
    have : (c : ℝ) * (1 + 1 / p) = c + c / p := by ring
    linarith
  exact (div_le_iff₀ hden').1 h2

private theorem pos_of_approx {c p num den : ℕ} (h : ApproxWithin c p num den) (hc : 1 ≤ c)
    (hp : 2 ≤ p) : 0 < num := by
  have hl := lower_of_approx h
  have hden' : (1 : ℝ) ≤ den := by exact_mod_cast h.1
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hinv : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp'
  have h3 : (1 : ℝ) / 2 ≤ c * (1 - 1 / p) := by nlinarith
  have h4 : (1 : ℝ) / 2 ≤ c * (1 - 1 / p) * den := by nlinarith
  have : (0 : ℝ) < num := by linarith
  exact_mod_cast this

private theorem fit_of_approx {m p N N₀ N₁ : ℕ} {e e₀ e₁ : ℕ × ℕ} (hm : 1 ≤ m)
    (hp : 2 * m - 1 ≤ p) (hN : N = N₀ + N₁) (he : ApproxWithin N p e.1 e.2)
    (he₀ : ApproxWithin N₀ p e₀.1 e₀.2) (he₁ : ApproxWithin N₁ p e₁.1 e₁.2) :
    weight m e e₀ e₁ false + weight m e e₀ e₁ true ≤ total m e e₀ e₁ := by
  have hl := lower_of_approx he
  have hu₀ := upper_of_approx he₀
  have hu₁ := upper_of_approx he₁
  have hM : ((m - 1 : ℕ) : ℝ) = m - 1 := by rw [Nat.cast_sub hm, Nat.cast_one]
  have hp' : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hpm : 2 * (m : ℝ) - 1 ≤ p := by
    have h' : ((2 * m - 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast hp
    have h'' : ((2 * m - 1 : ℕ) : ℝ) = 2 * m - 1 := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    linarith
  have hpr : (p : ℝ) * (1 / p) = 1 := by field_simp
  have hr0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hkey : ((m : ℝ) - 1) * (1 + 1 / p) ≤ m * (1 - 1 / p) := by nlinarith
  have hb : (0 : ℝ) ≤ e.2 := by positivity
  have hb₀ : (0 : ℝ) ≤ e₀.2 := by positivity
  have hb₁ : (0 : ℝ) ≤ e₁.2 := by positivity
  have hN' : (N : ℝ) = N₀ + N₁ := by exact_mod_cast hN
  have hm1 : (0 : ℝ) ≤ m - 1 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have goal : ((m : ℝ) - 1) * e₀.1 * e₁.2 * e.2 + ((m : ℝ) - 1) * e₁.1 * e₀.2 * e.2 ≤
      (m : ℝ) * e.1 * e₀.2 * e₁.2 := by
    calc ((m : ℝ) - 1) * e₀.1 * e₁.2 * e.2 + ((m : ℝ) - 1) * e₁.1 * e₀.2 * e.2
        = ((m : ℝ) - 1) * e.2 * (e₀.1 * e₁.2 + e₁.1 * e₀.2) := by ring
      _ ≤ ((m : ℝ) - 1) * e.2 *
            (N₀ * (1 + 1 / p) * e₀.2 * e₁.2 + N₁ * (1 + 1 / p) * e₁.2 * e₀.2) :=
          mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right hu₀ hb₁)
            (mul_le_mul_of_nonneg_right hu₁ hb₀)) (mul_nonneg hm1 hb)
      _ = ((m : ℝ) - 1) * (1 + 1 / p) * (N * e.2 * e₀.2 * e₁.2) := by rw [hN']; ring
      _ ≤ m * (1 - 1 / p) * (N * e.2 * e₀.2 * e₁.2) :=
          mul_le_mul_of_nonneg_right hkey (by positivity)
      _ = m * e₀.2 * e₁.2 * (N * (1 - 1 / p) * e.2) := by ring
      _ ≤ m * e₀.2 * e₁.2 * e.1 := mul_le_mul_of_nonneg_left hl (by positivity)
      _ = (m : ℝ) * e.1 * e₀.2 * e₁.2 := by ring
  have : ((weight m e e₀ e₁ false + weight m e e₀ e₁ true : ℕ) : ℝ) ≤ (total m e e₀ e₁ : ℕ) := by
    simp only [weight, total, Bool.cond_false, Bool.cond_true, Nat.cast_add, Nat.cast_mul, hM]
    exact goal
  exact_mod_cast this

private theorem one_le_weight {m : ℕ} {e e₀ e₁ : ℕ × ℕ} (hm : 2 ≤ m) {c : Bool}
    (ha : 0 < (cond c e₁ e₀).1) (hb' : 0 < (cond c e₀ e₁).2) (hb : 0 < e.2) :
    1 ≤ weight m e e₀ e₁ c :=
  Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) ha) hb') hb

private theorem one_sub_half_pow_nonneg (t : ℕ) : 0 ≤ 1 - (1 / 2 : ℝ) ^ t := by
  have : (1 / 2 : ℝ) ^ t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith

/-- The per-level success factor `(1 - 2 ^ (-t)) ^ 2 (1 - 2 ^ (-extra))`: both child estimates
are good, and the branching coin is accurate. -/
noncomputable def stepFactor (t extra : ℕ) : ℝ :=
  (1 - (1 / 2 : ℝ) ^ t) ^ 2 * (1 - (1 / 2 : ℝ) ^ extra)

/-- **Lower bound for one walk.** If the counter is accurate with probability `1 - 2 ^ (-t)` and
`p ≥ 2 m - 1`, then from a node at witness length `n` with a good estimate `e`, a walk returns each
witness with probability at least `stepFactor ^ n · (1 - 1 / m) ^ n · b / a`. -/
theorem le_eval_walk (R : SelfReducible enc W) {A : α → ℕ → ℕ → ProbComp (ℕ × ℕ)}
    {p t m extra : ℕ} (hm : 2 ≤ m) (hp : 2 * m - 1 ≤ p)
    (hA : CounterAccurate W A p t) :
    ∀ n y, R.len y = n → ∀ e, R.GoodEstimate p y e → ∀ v ∈ W y,
      ENNReal.ofReal (stepFactor t extra ^ n * levelFactor m ^ n * invEstimate e) ≤
        ProbComp.eval (R.walk A p t m extra n y e) (some v)
  | 0, y, hy, e, he, v, hv => by
    have hW := R.eq_singleton_nil hy (Finset.card_pos.2 ⟨v, hv⟩)
    rw [hW, Finset.mem_singleton] at hv
    subst hv
    have hnil : [] ∈ W y := by
      rw [hW]
      exact Finset.mem_singleton_self _
    have hexact := he.2 hy
    rw [hW, Finset.card_singleton, Nat.cast_one, one_mul] at hexact
    rw [eval_walk_zero]
    split_ifs with h
    · rw [pow_zero, pow_zero, one_mul, one_mul]
      refine ENNReal.ofReal_le_one.2 ?_
      unfold invEstimate
      rw [← hexact]
      exact div_self_le_one _
    · exact absurd ⟨rfl, hnil⟩ h
  | n + 1, y, hy, e, he, v, hv => by
    have hpos : 0 < R.len y := by omega
    have hp2 : 2 ≤ p := by omega
    cases v with
    | nil =>
      have h := R.length_eq y [] hv
      simp only [List.length_nil] at h
      omega
    | cons c w =>
      have hw : w ∈ W (R.child y c) := (R.cons_mem_iff y hpos c w).1 hv
      have hlen : ∀ b, R.len (R.child y b) = n := fun b => by rw [R.len_child y hpos]; omega
      have hδ := one_sub_half_pow_nonneg t
      have hx := one_sub_half_pow_nonneg extra
      have hgood := nodeEstimate_good R hA
      have key : ∀ e₀, R.GoodEstimate p (R.child y false) e₀ →
          ∀ e₁, R.GoodEstimate p (R.child y true) e₁ →
          ENNReal.ofReal ((1 - (1 / 2 : ℝ) ^ extra) * stepFactor t extra ^ n *
              levelFactor m ^ (n + 1) * invEstimate e) ≤
            ((ProbComp.eval (choose m extra e e₀ e₁)).bind fun o => ProbComp.eval (descend
              (fun c => R.walk A p t m extra n (R.child y c) (cond c e₁ e₀)) o))
              (some (c :: w)) := by
        intro e₀ he₀ e₁ he₁
        rw [eval_bind_descend_some_cons]
        have gc : R.GoodEstimate p (R.child y c) (cond c e₁ e₀) := by
          cases c
          · exact he₀
          · exact he₁
        have hbc' : 0 < (cond c e₀ e₁).2 := by
          cases c
          · exact he₁.1.1
          · exact he₀.1.1
        have hNc : 1 ≤ (W (R.child y c)).card := Finset.card_pos.2 ⟨w, hw⟩
        have hac := pos_of_approx gc.1 hNc hp2
        have hbc := gc.1.1
        have hfit := fit_of_approx (by omega) hp (R.card_eq_add hpos) he.1 he₀.1 he₁.1
        have hwc := one_le_weight (c := c) hm hac hbc' he.1.1
        have heq := weight_div_total_mul_eq m e e₀ e₁ c hac.ne' hbc.ne' hbc'.ne'
        have hrec := le_eval_walk (extra := extra) R hm hp hA n (R.child y c) (hlen c) _ gc w hw
        calc ENNReal.ofReal ((1 - (1 / 2 : ℝ) ^ extra) * stepFactor t extra ^ n *
              levelFactor m ^ (n + 1) * invEstimate e)
            = ENNReal.ofReal ((1 - (1 / 2 : ℝ) ^ extra) *
                ((weight m e e₀ e₁ c : ℝ) / total m e e₀ e₁)) *
              ENNReal.ofReal (stepFactor t extra ^ n * levelFactor m ^ n *
                invEstimate (cond c e₁ e₀)) := by
              rw [← ENNReal.ofReal_mul (mul_nonneg hx (by positivity))]
              congr 1
              linear_combination
                (-(1 - (1 / 2 : ℝ) ^ extra) * stepFactor t extra ^ n * levelFactor m ^ n) * heq
          _ ≤ _ := mul_le_mul' (le_eval_choose hfit hwc) hrec
      rw [eval_walk_succ]
      refine le_of_le_of_eq ?_ (PMF.toOuterMeasure_apply_singleton _ _)
      have hsucc : stepFactor t extra ^ (n + 1) =
          stepFactor t extra ^ n * ((1 - (1 / 2 : ℝ) ^ t) ^ 2 * (1 - (1 / 2 : ℝ) ^ extra)) :=
        pow_succ _ _
      calc ENNReal.ofReal (stepFactor t extra ^ (n + 1) * levelFactor m ^ (n + 1) * invEstimate e)
          = ENNReal.ofReal (1 - (1 / 2 : ℝ) ^ t) * (ENNReal.ofReal (1 - (1 / 2 : ℝ) ^ t) *
              ENNReal.ofReal ((1 - (1 / 2 : ℝ) ^ extra) * stepFactor t extra ^ n *
                levelFactor m ^ (n + 1) * invEstimate e)) := by
            rw [← ENNReal.ofReal_mul hδ, ← ENNReal.ofReal_mul hδ, hsucc]
            congr 1
            ring
        _ ≤ _ := by
            refine Probability.PMF.toOuterMeasure_bind_ge_mul_ennreal _ _
              {e₀ | R.GoodEstimate p (R.child y false) e₀} _
              ((ENNReal.ofReal_le_iff_le_toReal (Probability.PMF.toOuterMeasure_ne_top _ _)).2
                (hgood _)) fun e₀ _ he₀ => ?_
            refine Probability.PMF.toOuterMeasure_bind_ge_mul_ennreal _ _
              {e₁ | R.GoodEstimate p (R.child y true) e₁} _
              ((ENNReal.ofReal_le_iff_le_toReal (Probability.PMF.toOuterMeasure_ne_top _ _)).2
                (hgood _)) fun e₁ _ he₁ => ?_
            rw [PMF.toOuterMeasure_apply_singleton]
            exact key e₀ he₀ e₁ he₁

end Walk

/-! ### The constants -/

section Constants

private theorem precision_aux (ℓ q : ℕ) :
    ((3 * ℓ + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ precision ℓ q ≤ (1 / 2 : ℝ) ^ q / 4 := by
  have hpow : (1 / 2 : ℝ) ^ precision ℓ q = (1 / 2) ^ q * (1 / 16) * (1 / 2) ^ ℓ := by
    rw [precision, pow_add, pow_add]
    norm_num
    ring
  have h2 : ((ℓ + 1 : ℕ) : ℝ) ≤ 2 ^ ℓ := by exact_mod_cast Nat.lt_two_pow_self
  have hx0 : (0 : ℝ) ≤ (1 / 2) ^ ℓ := by positivity
  have hx : (2 : ℝ) ^ ℓ * (1 / 2) ^ ℓ = 1 := by rw [← mul_pow]; norm_num
  have hb : ((3 * ℓ + 1 : ℕ) : ℝ) * (1 / 2) ^ ℓ ≤ 4 := by
    push_cast at h2 ⊢
    nlinarith
  have hq : (0 : ℝ) ≤ (1 / 2) ^ q := by positivity
  rw [hpow]
  nlinarith

private theorem stepFactor_precision (ℓ q : ℕ) :
    stepFactor (precision ℓ q) (precision ℓ q) = (1 - (1 / 2 : ℝ) ^ precision ℓ q) ^ 3 := by
  rw [stepFactor]
  ring

private theorem half_le_stepFactor_pow (ℓ q : ℕ) :
    1 / 2 ≤ stepFactor (precision ℓ q) (precision ℓ q) ^ ℓ := by
  rw [stepFactor_precision, ← pow_mul]
  have hδ : (0 : ℝ) ≤ (1 / 2) ^ precision ℓ q := by positivity
  have hδ1 : (1 / 2 : ℝ) ^ precision ℓ q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hbern := one_add_mul_le_pow (a := -(1 / 2 : ℝ) ^ precision ℓ q) (by linarith) (3 * ℓ)
  have haux := precision_aux ℓ q
  have hq : (1 / 2 : ℝ) ^ q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  push_cast at hbern haux
  rw [← sub_eq_add_neg] at hbern
  nlinarith

private theorem half_le_levelFactor_pow (ℓ : ℕ) : 1 / 2 ≤ levelFactor (damping ℓ) ^ ℓ := by
  have hm : levelFactor (damping ℓ) = 1 + -(1 / ((2 * ℓ + 2 : ℕ) : ℝ)) := by
    rw [levelFactor, damping, show 2 * ℓ + 2 - 1 = 2 * ℓ + 1 by omega]
    push_cast
    field_simp
    ring
  have hpos : (0 : ℝ) < ((2 * ℓ + 2 : ℕ) : ℝ) := by positivity
  have hle : 1 / ((2 * ℓ + 2 : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one hpos]
    push_cast
    linarith
  have hbern := one_add_mul_le_pow (a := -(1 / ((2 * ℓ + 2 : ℕ) : ℝ))) (by linarith) ℓ
  rw [← hm] at hbern
  have hfrac : (ℓ : ℝ) * (1 / ((2 * ℓ + 2 : ℕ) : ℝ)) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_iff₀ hpos]
    push_cast
    linarith
  linarith

private theorem final_aux (ℓ q : ℕ) :
    1 - (1 / 2 : ℝ) ^ q ≤ (1 - (1 / 2 : ℝ) ^ precision ℓ q) *
      stepFactor (precision ℓ q) (precision ℓ q) ^ ℓ * (1 - (7 / 8 : ℝ) ^ trials q) := by
  rw [stepFactor_precision, ← pow_mul, ← pow_succ']
  have hδ : (0 : ℝ) ≤ (1 / 2) ^ precision ℓ q := by positivity
  have hδ1 : (1 / 2 : ℝ) ^ precision ℓ q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hbern := one_add_mul_le_pow (a := -(1 / 2 : ℝ) ^ precision ℓ q) (by linarith) (3 * ℓ + 1)
  rw [← sub_eq_add_neg] at hbern
  have haux := precision_aux ℓ q
  have hc : (7 / 8 : ℝ) ^ trials q ≤ (1 / 2) ^ q / 4 := by
    rw [trials, pow_mul]
    calc ((7 / 8 : ℝ) ^ 6) ^ (q + 2) ≤ (1 / 2) ^ (q + 2) :=
          pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = (1 / 2) ^ q / 4 := by rw [pow_add]; norm_num; ring
  have hc0 : (0 : ℝ) ≤ (7 / 8) ^ trials q := by positivity
  have hq0 : (0 : ℝ) ≤ (1 / 2) ^ q := by positivity
  have hq1 : (1 / 2 : ℝ) ^ q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hA : 1 - (1 / 2 : ℝ) ^ q / 4 ≤ (1 - (1 / 2) ^ precision ℓ q) ^ (3 * ℓ + 1) := by
    push_cast at hbern haux
    linarith
  have hB : 1 - (1 / 2 : ℝ) ^ q / 4 ≤ 1 - (7 / 8) ^ trials q := by linarith
  calc 1 - (1 / 2 : ℝ) ^ q ≤ (1 - (1 / 2) ^ q / 4) * (1 - (1 / 2) ^ q / 4) := by nlinarith
    _ ≤ _ := mul_le_mul hA hB (by linarith) (pow_nonneg (by linarith) _)

private theorem three_quarters_le_card_mul_invEstimate {N p : ℕ} {e : ℕ × ℕ} (hN : 1 ≤ N)
    (hp : 3 ≤ p) (he : ApproxWithin N p e.1 e.2) : 3 / 4 ≤ (N : ℝ) * invEstimate e := by
  have hu := upper_of_approx he
  have ha : 0 < e.1 := pos_of_approx he hN (by omega)
  have ha' : (0 : ℝ) < e.1 := by exact_mod_cast ha
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hinv : (1 : ℝ) / p ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hp'
  have hinv0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hNb : (0 : ℝ) ≤ N * e.2 := by positivity
  rw [invEstimate, mul_div_assoc', le_div_iff₀ ha']
  nlinarith

end Constants

/-! ### One trial -/

section Trial

/-- A trial only returns witnesses. -/
theorem eval_trial_eq_zero (R : SelfReducible enc W) (A : α → ℕ → ℕ → ProbComp (ℕ × ℕ)) (x : α)
    (q : ℕ) (e : ℕ × ℕ) {v : List Bool} (hv : v ∉ W x) :
    ProbComp.eval (R.trial A x q e) (some v) = 0 :=
  eval_walk_eq_zero R A _ _ _ _ _ x rfl e v hv

/-- The rejection probability of a trial and its probabilities of the witnesses add up to `1`. -/
theorem eval_trial_none_add_sum (R : SelfReducible enc W) (A : α → ℕ → ℕ → ProbComp (ℕ × ℕ))
    (x : α) (q : ℕ) (e : ℕ × ℕ) :
    ProbComp.eval (R.trial A x q e) none +
      ∑ w ∈ W x, ProbComp.eval (R.trial A x q e) (some w) = 1 := by
  have h := Probability.PMF.toOuterMeasure_add_compl_ennreal (ProbComp.eval (R.trial A x q e))
    {none}
  rw [PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_apply,
    tsum_eq_sum (s := (W x).map Function.Embedding.some)] at h
  · rw [Finset.sum_map] at h
    refine (congrArg (_ + ·) (Finset.sum_congr rfl fun w _ => ?_)).trans h
    simp
  · intro o ho
    cases o with
    | none => simp
    | some w =>
      have hw : w ∉ W x := fun hw => ho (Finset.mem_map_of_mem _ hw)
      simp [eval_trial_eq_zero R A x q e hw]

private theorem le_eval_trial_toReal (R : SelfReducible enc W)
    {A : α → ℕ → ℕ → ProbComp (ℕ × ℕ)} {x : α} {q : ℕ}
    (hA : CounterAccurate W A (counterAccuracy (R.len x)) (precision (R.len x) q))
    {e : ℕ × ℕ} (he : R.GoodEstimate (counterAccuracy (R.len x)) x e) {w : List Bool}
    (hw : w ∈ W x) :
    stepFactor (precision (R.len x) q) (precision (R.len x) q) ^ R.len x *
        (levelFactor (damping (R.len x)) ^ R.len x * invEstimate e) ≤
      (ProbComp.eval (R.trial A x q e) (some w)).toReal := by
  have hm : 2 ≤ damping (R.len x) := by rw [damping]; omega
  have hp : 2 * damping (R.len x) - 1 ≤ counterAccuracy (R.len x) := by
    rw [damping, counterAccuracy]; omega
  have h := le_eval_walk (extra := precision (R.len x) q) R hm hp hA (R.len x) x rfl e he w hw
  rw [mul_assoc] at h
  exact (ENNReal.ofReal_le_iff_le_toReal (PMF.apply_ne_top _ _)).1 h

private theorem one_eighth_le {N ℓ q : ℕ} {e : ℕ × ℕ} (hN : 0 < N)
    (he : ApproxWithin N (counterAccuracy ℓ) e.1 e.2) :
    1 / 8 ≤ (N : ℝ) * (stepFactor (precision ℓ q) (precision ℓ q) ^ ℓ *
      (levelFactor (damping ℓ) ^ ℓ * invEstimate e)) := by
  have h1 := half_le_stepFactor_pow ℓ q
  have h2 := half_le_levelFactor_pow ℓ
  have h3 := three_quarters_le_card_mul_invEstimate hN (by rw [counterAccuracy]; omega) he
  have h4 : (N : ℝ) * (stepFactor (precision ℓ q) (precision ℓ q) ^ ℓ *
      (levelFactor (damping ℓ) ^ ℓ * invEstimate e)) =
        stepFactor (precision ℓ q) (precision ℓ q) ^ ℓ * levelFactor (damping ℓ) ^ ℓ *
          (N * invEstimate e) := by ring
  rw [h4]
  have h5 : (1 / 2 : ℝ) * (1 / 2) ≤
      stepFactor (precision ℓ q) (precision ℓ q) ^ ℓ * levelFactor (damping ℓ) ^ ℓ :=
    mul_le_mul h1 h2 (by norm_num) (by linarith)
  nlinarith

/-- **The acceptance probability of a trial.** If the counter is accurate and the root estimate
`e` is good, then a trial from an instance with at least one witness rejects with probability at
most `7 / 8`, so it returns a witness with probability at least `1 / 8`. -/
theorem eval_trial_none_le (R : SelfReducible enc W) {A : α → ℕ → ℕ → ProbComp (ℕ × ℕ)} {x : α}
    {q : ℕ}
    (hA : CounterAccurate W A (counterAccuracy (R.len x)) (precision (R.len x) q))
    {e : ℕ × ℕ} (he : R.GoodEstimate (counterAccuracy (R.len x)) x e) (hW : (W x).Nonempty) :
    ProbComp.eval (R.trial A x q e) none ≤ 7 / 8 := by
  have hN : 0 < (W x).card := Finset.card_pos.2 hW
  have hsl := Finset.card_nsmul_le_sum (W x) (fun w => (ProbComp.eval (R.trial A x q e)
    (some w)).toReal) _ fun w hw => le_eval_trial_toReal R hA he hw
  rw [nsmul_eq_mul] at hsl
  have h8 := one_eighth_le (q := q) hN he.1
  have htot : (ProbComp.eval (R.trial A x q e) none).toReal +
      ∑ w ∈ W x, (ProbComp.eval (R.trial A x q e) (some w)).toReal = 1 := by
    rw [← ENNReal.toReal_sum fun w _ => PMF.apply_ne_top _ _, ← ENNReal.toReal_add
      (PMF.apply_ne_top _ _) (ENNReal.sum_ne_top.2 fun w _ => PMF.apply_ne_top _ _),
      eval_trial_none_add_sum, ENNReal.toReal_one]
  have hle : (ProbComp.eval (R.trial A x q e) none).toReal ≤ 7 / 8 := by linarith
  calc ProbComp.eval (R.trial A x q e) none
      ≤ ENNReal.ofReal (7 / 8) := ENNReal.le_ofReal_iff_toReal_le (PMF.apply_ne_top _ _)
        (by norm_num) |>.2 hle
    _ = 7 / 8 := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num

end Trial

/-! ### The output law of the sampler -/

section Sampler

private theorem retry_bound {P f L U κ' c : ℝ} {N T : ℕ} (hN : 0 < N) (hL : L = κ' * U)
    (hκ' : 0 ≤ κ') (hP : L ≤ P) (hf0 : 0 ≤ f) (hfs : N * L ≤ 1 - f) (hfu : 1 - f ≤ N * U)
    (h8 : 1 / 8 ≤ N * L) (hc : c = (7 / 8 : ℝ) ^ T) :
    κ' * (1 - c) / N ≤ P * ∑ i ∈ Finset.range T, f ^ i := by
  set g := ∑ i ∈ Finset.range T, f ^ i
  have hgeom : g * (1 - f) = 1 - f ^ T := geom_sum_mul_neg f T
  have hf78 : f ≤ 7 / 8 := by linarith
  have hfT : f ^ T ≤ c := hc ▸ pow_le_pow_left₀ hf0 hf78 T
  have hg0 : 0 ≤ g := Finset.sum_nonneg fun i _ => pow_nonneg hf0 i
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : 1 - c ≤ N * U * g := by nlinarith
  have h2 : κ' * (1 - c) ≤ N * (P * g) := by
    have h3 : κ' * (1 - c) ≤ κ' * (N * U * g) := mul_le_mul_of_nonneg_left h1 hκ'
    have h4 : N * L * g ≤ N * P * g := by
      have := mul_le_mul_of_nonneg_left hP hN'.le
      exact mul_le_mul_of_nonneg_right this hg0
    rw [hL] at h4
    nlinarith
  rw [div_le_iff₀ hN']
  linarith

/-- **The retry loop at a good root estimate.** With the sampler's parameters, a good root
estimate `e` makes the retry loop return each witness with probability at least
`(1 - 2 ^ (-t)) ^ (3 ℓ) (1 - (7 / 8) ^ T) / |W x|`, where `t = precision ℓ q`, `ℓ = R.len x` and
`T = trials q`. -/
theorem le_eval_retry (R : SelfReducible enc W) {A : α → ℕ → ℕ → ProbComp (ℕ × ℕ)} {x : α} {q : ℕ}
    (hA : CounterAccurate W A (counterAccuracy (R.len x)) (precision (R.len x) q))
    {e : ℕ × ℕ}
    (hsupp : R.len x = 0 → e ∈ (ProbComp.eval (R.nodeEstimate A (counterAccuracy (R.len x))
      (precision (R.len x) q) x)).support)
    (he : R.GoodEstimate (counterAccuracy (R.len x)) x e) {v : List Bool} (hv : v ∈ W x) :
    ENNReal.ofReal (stepFactor (precision (R.len x) q) (precision (R.len x) q) ^ R.len x *
        (1 - (7 / 8 : ℝ) ^ trials q) / (W x).card) ≤
      ProbComp.eval (Option.join <$> OracleComp.retry (fun o : Option (List Bool) => o.isSome)
        (R.trial A x q e) (trials q)) (some v) := by
  have hN : 0 < (W x).card := Finset.card_pos.2 ⟨v, hv⟩
  have hup : ∀ w, ProbComp.eval (R.trial A x q e) (some w) ≤
      ENNReal.ofReal (levelFactor (damping (R.len x)) ^ R.len x * invEstimate e) := fun w =>
    eval_walk_le R A _ _ _ _ (R.len x) x rfl e hsupp w
  have hU : 0 ≤ levelFactor (damping (R.len x)) ^ R.len x * invEstimate e :=
    mul_nonneg (pow_nonneg (levelFactor_nonneg _) _) (invEstimate_nonneg e)
  have hκ' : 0 ≤ stepFactor (precision (R.len x) q) (precision (R.len x) q) ^ R.len x := by
    have := half_le_stepFactor_pow (R.len x) q
    linarith
  have hUle : ∀ w ∈ W x, (ProbComp.eval (R.trial A x q e) (some w)).toReal ≤
      levelFactor (damping (R.len x)) ^ R.len x * invEstimate e := fun w _ =>
    ENNReal.toReal_le_of_le_ofReal hU (hup w)
  have htotr : (ProbComp.eval (R.trial A x q e) none).toReal +
      ∑ w ∈ W x, (ProbComp.eval (R.trial A x q e) (some w)).toReal = 1 := by
    rw [← ENNReal.toReal_sum fun w _ => PMF.apply_ne_top _ _, ← ENNReal.toReal_add
      (PMF.apply_ne_top _ _) (ENNReal.sum_ne_top.2 fun w _ => PMF.apply_ne_top _ _),
      eval_trial_none_add_sum, ENNReal.toReal_one]
  have hsl := Finset.card_nsmul_le_sum (W x) (fun w => (ProbComp.eval (R.trial A x q e)
    (some w)).toReal) _ fun w hw => le_eval_trial_toReal R hA he hw
  have hsu := Finset.sum_le_card_nsmul (W x) (fun w => (ProbComp.eval (R.trial A x q e)
    (some w)).toReal) _ hUle
  rw [nsmul_eq_mul] at hsl hsu
  have h8 := one_eighth_le (q := q) hN he.1
  have hfail : (ProbComp.eval (R.trial A x q e)).toOuterMeasure {o | ¬ o.isSome = true} =
      ProbComp.eval (R.trial A x q e) none := by
    have : {o : Option (List Bool) | ¬ o.isSome = true} = {none} := by
      ext o
      cases o <;> simp
    rw [this, PMF.toOuterMeasure_apply_singleton]
  rw [ProbComp.eval_map]
  refine le_trans ?_ (Probability.PMF.le_map_apply _ Option.join (some (some v)))
  rw [ProbComp.eval_eq_evalWith, OracleComp.evalWith_retry_some, ← ProbComp.eval_eq_evalWith,
    hfail]
  simp only [Option.isSome_some, ↓reduceIte]
  rw [ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
    (ENNReal.sum_ne_top.2 fun i _ => ENNReal.pow_ne_top (PMF.apply_ne_top _ _))),
    ENNReal.toReal_mul, ENNReal.toReal_sum fun i _ => ENNReal.pow_ne_top (PMF.apply_ne_top _ _)]
  simp only [ENNReal.toReal_pow]
  exact retry_bound hN rfl hκ' (le_eval_trial_toReal R hA he hv) ENNReal.toReal_nonneg
    (by linarith) (by linarith) h8 rfl

/-- **Approximate counting gives almost uniform sampling** (output law). If `A` estimates the
number of witnesses within relative error `1 / p` with probability at least `1 - 2 ^ (-t)`, for
all `p > 0` and `t` (`CounterAccurate`), then
the sampler built from `A` has output law within statistical distance `2 ^ (-q)` of the uniform law
on the witnesses of `x`. -/
theorem closeTo_sampler (R : SelfReducible enc W) {A : α → ℕ → ℕ → ProbComp (ℕ × ℕ)}
    (hA : ∀ p t, 0 < p → CounterAccurate W A p t) (x : α) (q : ℕ) :
    Probability.CloseTo (ProbComp.eval (R.sampler A x q)) (uniformWitness (W x))
      (ENNReal.ofReal ((1 / 2 : ℝ) ^ q)) := by
  have hA' : CounterAccurate W A (counterAccuracy (R.len x)) (precision (R.len x) q) :=
    hA _ _ (by rw [counterAccuracy]; omega)
  refine closeTo_uniformWitness_of_le (by positivity) (fun v hv => ?_) (fun hW v => ?_)
  · have hN : (0 : ℝ) < (W x).card := by exact_mod_cast Finset.card_pos.2 ⟨v, hv⟩
    rw [sampler, ProbComp.eval_bind]
    refine le_of_le_of_eq ?_ (PMF.toOuterMeasure_apply_singleton _ _)
    calc ENNReal.ofReal ((1 - (1 / 2 : ℝ) ^ q) / (W x).card)
        ≤ ENNReal.ofReal (1 - (1 / 2 : ℝ) ^ precision (R.len x) q) *
            ENNReal.ofReal (stepFactor (precision (R.len x) q) (precision (R.len x) q) ^ R.len x *
              (1 - (7 / 8 : ℝ) ^ trials q) / (W x).card) := by
          rw [← ENNReal.ofReal_mul (one_sub_half_pow_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [mul_div_assoc', ← mul_assoc]
          exact div_le_div_of_nonneg_right (final_aux (R.len x) q) hN.le
      _ ≤ _ := by
          refine Probability.PMF.toOuterMeasure_bind_ge_mul_ennreal _ _
            {e | R.GoodEstimate (counterAccuracy (R.len x)) x e} _
            ((ENNReal.ofReal_le_iff_le_toReal (Probability.PMF.toOuterMeasure_ne_top _ _)).2
              (nodeEstimate_good R hA' x)) fun e hsupp he => ?_
          rw [PMF.toOuterMeasure_apply_singleton]
          exact le_eval_retry R hA' (fun _ => hsupp) he hv
  · rw [sampler, ProbComp.eval_bind]
    refine Probability.PMF.bind_apply_of_forall _ fun e => ?_
    rw [ProbComp.eval_map, PMF.map_apply]
    refine tsum_eq_zero_iff.2 fun o => ?_
    rcases o with _ | _ | w
    · simp
    · simp
    · by_cases hvw : v = w
      · subst hvw
        rw [ProbComp.eval_eq_evalWith, OracleComp.evalWith_retry_some, ← ProbComp.eval_eq_evalWith,
          eval_trial_eq_zero R A x q e (by rw [hW]; exact Finset.notMem_empty v)]
        simp
      · simp [hvw]

/-- **An FPRAS gives the output law of an FPAUS.** The sampler built from a fully polynomial
randomized approximation scheme for the number of witnesses has output law within statistical
distance `2 ^ (-q)` of the uniform law on the witnesses, for every instance and accuracy `q`. This
is the output-distribution half of `IsFPAUS`; its runtime half is not proved here. -/
theorem closeTo_sampler_of_isFPRAS (R : SelfReducible enc W) {A : α → ℕ → ℕ → ProbComp (ℕ × ℕ)}
    (hA : IsFPRAS enc (fun x => (W x).card) A) (x : α) (q : ℕ) :
    Probability.CloseTo (ProbComp.eval (R.sampler A x q)) (uniformWitness (W x))
      (ENNReal.ofReal ((1 / 2 : ℝ) ^ q)) :=
  R.closeTo_sampler (fun p t hp x => hA.2 x p t hp) x q

end Sampler

end Cslib.Complexity.SelfReducible
