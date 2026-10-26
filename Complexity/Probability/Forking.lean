/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.Rewinding
import Complexity.Probability.PMF.Uniform
import Complexity.Probability.PMF
import Mathlib.Algebra.Order.Chebyshev

/-!
# The general forking lemma

An algorithm `A` gets coins `s`, drawn from a distribution, and `q` answers `h : Fin q → H`, drawn
independently and uniformly from a finite set `H`, and outputs an optional index `j : Fin q`
together with a result. The *forking algorithm* runs `A` once; if it outputs an index `j`, it
runs `A` again on the same coins and the same answers before `j`, with fresh answers from `j` on
(`splice`). It succeeds when the second run outputs the same index `j` and the two answers at `j`
differ, and it returns both results.

The general forking lemma of Bellare and Neven ([BellareNeven2006], Lemma 1) bounds the success
probability `frk` of forking by the acceptance probability `acc` of one run:
`acc ^ 2 / q - acc / |H| ≤ frk` (`sq_div_sub_le_fork`), and consequently
`acc ≤ q / |H| + √(q · frk)` (`le_add_sqrt_fork`). For each index `j` this is the rewinding lemma
(`Rewinding.sq_sub_le_twice`), with the coins and the answers before `j` as the first stage, the
answer at `j` as the challenge and the answers after `j` as fresh randomness of the second stage;
summing over `j` loses the factor `q` by the Cauchy–Schwarz inequality. Boneh and Shoup prove the
same bound for `r`-impersonation adversaries ([BonehShoup2023], Lemma 19.8).

The algorithm is deterministic given its coins and answers, which is the form forking needs: the
second run reuses the coins. The statements are exact; no efficiency is involved.

## Main definitions

* `Cslib.Probability.Forking.splice`: answers from one vector before an index, another from it on.
* `Cslib.Probability.Forking.accept`: run once and accept when an index is output.
* `Cslib.Probability.Forking.fork`: the forking algorithm.

## Main results

* `Cslib.Probability.Forking.sq_div_sub_le_fork`: `acc ^ 2 / q - acc / |H| ≤ frk`.
* `Cslib.Probability.Forking.le_add_sqrt_fork`: `acc ≤ q / |H| + √(q · frk)`.
* `Cslib.Probability.Forking.mem_support_fork`: what a successful fork returns.

## References

* [M. Bellare, G. Neven, *Multi-Signatures in the Plain Public-Key Model and a General Forking
  Lemma*][BellareNeven2006], Lemma 1.
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Lemma 19.8.
-/

@[expose] public section

namespace Cslib.Probability.Forking

variable {S H β : Type} {q : ℕ}

/-- The answers of `h` before the index `j` and those of `h'` from `j` on. -/
def splice (j : Fin q) (h h' : Fin q → H) : Fin q → H := fun i => if i < j then h i else h' i

variable [Fintype H] [Nonempty H]

/-- One run: draw coins and uniform answers, and accept when `A` outputs an index. -/
noncomputable def accept (first : PMF S) (A : S → (Fin q → H) → Option (Fin q) × β) :
    PMF Bool := do
  let s ← first
  let h ← PMF.uniformOfFintype (Fin q → H)
  return (A s h).1.isSome

/-- The forking algorithm ([BellareNeven2006]): run `A` on coins `s` and answers `h`; if it
outputs an index `j`, rerun it on `s` and on `splice j h h'` for fresh answers `h'`, and succeed
with both results when the rerun outputs `j` too and `h j ≠ h' j`. -/
noncomputable def fork [DecidableEq H] (first : PMF S)
    (A : S → (Fin q → H) → Option (Fin q) × β) : PMF (Option (Fin q × β × β)) := do
  let s ← first
  let h ← PMF.uniformOfFintype (Fin q → H)
  let h' ← PMF.uniformOfFintype (Fin q → H)
  return match (A s h).1 with
    | none => none
    | some j => if (A s (splice j h h')).1 = some j ∧ h j ≠ h' j then
        some (j, (A s h).2, (A s (splice j h h')).2) else none

/-! ### Splitting the answers at an index -/

/-- Answers from `b` before `j`, the answer `t` at `j`, and answers from `r` after `j`. -/
private def glue (j : Fin q) (b : Fin q → H) (t : H) (r : Fin q → H) : Fin q → H :=
  fun i => if i < j then b i else if i = j then t else r i

/-- Gluing is the first component of an equivalence, whose other components are the unused
parts of `b` and `r`. -/
private def glueEquiv (j : Fin q) :
    (Fin q → H) × H × (Fin q → H) ≃ (Fin q → H) × (Fin q → H) × H where
  toFun x := (glue j x.1 x.2.1 x.2.2, fun i => if i < j then x.2.2 i else x.1 i, x.2.2 j)
  invFun y := (fun i => if i < j then y.1 i else y.2.1 i, y.1 j,
    fun i => if i < j then y.2.1 i else if i = j then y.2.2 else y.1 i)
  left_inv x := by
    obtain ⟨b, t, r⟩ := x
    simp only [glue, lt_self_iff_false, ite_false, ite_true, Prod.mk.injEq]
    refine ⟨funext fun i => ?_, trivial, funext fun i => ?_⟩
    · split_ifs <;> rfl
    · by_cases h₁ : i < j <;> by_cases h₂ : i = j <;> simp [h₁, h₂]
  right_inv y := by
    obtain ⟨x, z, u⟩ := y
    simp only [lt_self_iff_false, ite_false, ite_true, Prod.mk.injEq]
    refine ⟨funext fun i => ?_, funext fun i => ?_, trivial⟩
    · by_cases h₁ : i < j <;> by_cases h₂ : i = j <;> simp [glue, h₁, h₂]
    · split_ifs <;> rfl

/-- Gluing independent uniform parts gives uniform answers. -/
private theorem bind_glue {γ : Type} (j : Fin q) (k : (Fin q → H) → PMF γ) :
    ((PMF.uniformOfFintype (Fin q → H)).bind fun b => (PMF.uniformOfFintype H).bind fun t =>
      (PMF.uniformOfFintype (Fin q → H)).bind fun r => k (glue j b t r)) =
      (PMF.uniformOfFintype (Fin q → H)).bind k := by
  have hprod : ((PMF.uniformOfFintype (Fin q → H)).bind fun b =>
      (PMF.uniformOfFintype H).bind fun t => (PMF.uniformOfFintype (Fin q → H)).bind fun r =>
        PMF.pure (b, t, r)) = PMF.uniformOfFintype ((Fin q → H) × H × (Fin q → H)) := by
    rw [← Probability.PMF.uniformOfFintype_prod, ← Probability.PMF.uniformOfFintype_prod]
    simp only [PMF.map, PMF.bind_bind, Function.comp_def, PMF.pure_bind]
  have hfst : (PMF.uniformOfFintype ((Fin q → H) × H × (Fin q → H))).map
      (fun x => glue j x.1 x.2.1 x.2.2) = PMF.uniformOfFintype (Fin q → H) := by
    have := Probability.PMF.uniformOfFintype_prod_map_fst (α := Fin q → H)
      (β := (Fin q → H) × H)
    rw [← Probability.PMF.uniformOfFintype_map_equiv (glueEquiv j), PMF.map_comp] at this
    exact this
  calc _ = ((PMF.uniformOfFintype ((Fin q → H) × H × (Fin q → H))).map
        (fun x => glue j x.1 x.2.1 x.2.2)).bind k := by
        rw [← hprod]
        simp only [PMF.bind_map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
    _ = _ := by rw [hfst]

omit [Fintype H] [Nonempty H] in
private theorem glue_self (j : Fin q) (b : Fin q → H) (t : H) (r : Fin q → H) :
    glue j b t r j = t := by
  simp [glue]

omit [Fintype H] [Nonempty H] in
private theorem splice_glue (j : Fin q) (b b' : Fin q → H) (t t' : H) (r r' : Fin q → H) :
    splice j (glue j b t r) (glue j b' t' r') = glue j b t' r' := by
  funext i
  by_cases h₁ : i < j <;> simp [splice, glue, h₁]

/-! ### One index -/

/-- The first stage at an index: coins, and answers to use before the index. -/
private noncomputable def firstAt (first : PMF S) : PMF (S × (Fin q → H)) := do
  let s ← first
  let b ← PMF.uniformOfFintype (Fin q → H)
  return (s, b)

/-- Accepting with the index `j` is one run of a rewinding experiment. -/
private theorem acceptAt_eq_once (first : PMF S) (A : S → (Fin q → H) → Option (Fin q) × β)
    (j : Fin q) :
    (do
      let s ← first
      let h ← PMF.uniformOfFintype (Fin q → H)
      return decide ((A s h).1 = some j) : PMF Bool) =
      Rewinding.once (firstAt first) (fun _ => PMF.uniformOfFintype H)
        (fun _ _ => PMF.uniformOfFintype (Fin q → H))
        (fun x t r => decide ((A x.1 (glue j x.2 t r)).1 = some j)) := by
  simp only [Rewinding.once, firstAt, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  congr 1
  funext s
  exact (bind_glue j fun h => PMF.pure (decide ((A s h).1 = some j))).symm

variable [DecidableEq H]

/-- Forking with the index `j` is two runs of the rewinding experiment. -/
private theorem forkAt_eq_twice (first : PMF S) (A : S → (Fin q → H) → Option (Fin q) × β)
    (j : Fin q) :
    (do
      let s ← first
      let h ← PMF.uniformOfFintype (Fin q → H)
      let h' ← PMF.uniformOfFintype (Fin q → H)
      return decide ((A s h).1 = some j ∧ (A s (splice j h h')).1 = some j ∧ h j ≠ h' j) :
      PMF Bool) =
      Rewinding.twice (firstAt first) (fun _ => PMF.uniformOfFintype H)
        (fun _ _ => PMF.uniformOfFintype (Fin q → H))
        (fun x t r => decide ((A x.1 (glue j x.2 t r)).1 = some j)) := by
  simp only [Rewinding.twice, firstAt, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  congr 1
  funext s
  rw [← bind_glue j]
  congr 1
  funext b
  congr 1
  funext t
  conv_lhs => enter [2, r]; rw [← bind_glue j]
  simp only [splice_glue, glue_self, PMF.bind_const]
  rw [PMF.bind_comm]
  congr 1
  funext t'
  congr 1
  funext r
  congr 1
  funext r'
  congr 1
  simp only [Bool.decide_and, ne_eq, decide_not, Bool.and_assoc]
  rfl

/-! ### Summing over the indices -/

omit [DecidableEq H] [Fintype H] [Nonempty H] in
/-- An event that names one index is the disjoint union of its events at each index. -/
private theorem bind_match_apply {X : Type} (μ : PMF X) (index : X → Option (Fin q))
    (event : Fin q → X → Prop) [∀ j x, Decidable (event j x)] :
    (μ.bind fun x => PMF.pure (match index x with
      | none => false
      | some j => decide (event j x))) true =
      ∑ j, (μ.bind fun x => PMF.pure (decide (index x = some j ∧ event j x))) true := by
  simp only [PMF.bind_apply, PMF.pure_apply]
  rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  refine tsum_congr fun x => ?_
  rw [← Finset.mul_sum]
  congr 1
  cases hx : index x with
  | none => simp
  | some j =>
    rw [Finset.sum_eq_single j (fun j' _ hj' => by simp [Ne.symm hj']) (by simp)]
    simp

omit [DecidableEq H] in
/-- The acceptance probability, as a real number. -/
private theorem toReal_accept (first : PMF S) (A : S → (Fin q → H) → Option (Fin q) × β) :
    (accept first A true).toReal = ∑ j, ((do
      let s ← first
      let h ← PMF.uniformOfFintype (Fin q → H)
      return decide ((A s h).1 = some j) : PMF Bool) true).toReal := by
  have h := bind_match_apply ((first.bind fun s => (PMF.uniformOfFintype (Fin q → H)).bind
    fun h => PMF.pure (s, h))) (fun x => (A x.1 x.2).1) (fun _ _ => True)
  simp only [PMF.bind_bind, PMF.pure_bind, and_true] at h
  rw [← ENNReal.toReal_sum fun _ _ => PMF.apply_ne_top _ _]
  refine congrArg ENNReal.toReal (Eq.trans ?_ h)
  simp only [accept, Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure]
  refine congrArg (fun p : PMF Bool => p true)
    (congrArg _ (funext fun s => congrArg _ (funext fun h => ?_)))
  cases (A s h).1 <;> rfl

/-- The success probability of forking, as a real number. -/
private theorem toReal_fork (first : PMF S) (A : S → (Fin q → H) → Option (Fin q) × β) :
    ((fork first A).map Option.isSome true).toReal = ∑ j, ((do
      let s ← first
      let h ← PMF.uniformOfFintype (Fin q → H)
      let h' ← PMF.uniformOfFintype (Fin q → H)
      return decide ((A s h).1 = some j ∧ (A s (splice j h h')).1 = some j ∧ h j ≠ h' j) :
        PMF Bool) true).toReal := by
  have h := bind_match_apply ((first.bind fun s => (PMF.uniformOfFintype (Fin q → H)).bind
    fun h => (PMF.uniformOfFintype (Fin q → H)).bind fun h' => PMF.pure (s, h, h')))
    (fun x => (A x.1 x.2.1).1)
    (fun j x => (A x.1 (splice j x.2.1 x.2.2)).1 = some j ∧ x.2.1 j ≠ x.2.2 j)
  simp only [PMF.bind_bind, PMF.pure_bind] at h
  rw [← ENNReal.toReal_sum fun _ _ => PMF.apply_ne_top _ _]
  refine congrArg ENNReal.toReal (Eq.trans ?_ h)
  simp only [fork, Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
    PMF.map_bind, PMF.pure_map]
  refine congrArg (fun p : PMF Bool => p true) (congrArg _ (funext fun s =>
    congrArg _ (funext fun h => congrArg _ (funext fun h' => ?_))))
  cases (A s h).1 with
  | none => rfl
  | some j => by_cases hc : (A s (splice j h h')).1 = some j ∧ h j ≠ h' j <;> simp [hc]

/-! ### The forking lemma -/

/-- **The general forking lemma** ([BellareNeven2006], Lemma 1): forking succeeds with
probability at least `acc ^ 2 / q - acc / |H|`, where `acc` is the probability that one run
outputs an index. -/
theorem sq_div_sub_le_fork (first : PMF S) (A : S → (Fin q → H) → Option (Fin q) × β) :
    (accept first A true).toReal ^ 2 / q - (accept first A true).toReal / Fintype.card H ≤
      ((fork first A).map Option.isSome true).toReal := by
  set N : ℝ := (Fintype.card H : ℝ)
  set a : Fin q → ℝ := fun j => ((do
    let s ← first
    let h ← PMF.uniformOfFintype (Fin q → H)
    return decide ((A s h).1 = some j) : PMF Bool) true).toReal
  have hj (j : Fin q) : a j ^ 2 - a j / N ≤ ((do
      let s ← first
      let h ← PMF.uniformOfFintype (Fin q → H)
      let h' ← PMF.uniformOfFintype (Fin q → H)
      return decide ((A s h).1 = some j ∧ (A s (splice j h h')).1 = some j ∧ h j ≠ h' j) :
        PMF Bool) true).toReal := by
    simp only [a, acceptAt_eq_once, forkAt_eq_twice]
    exact Rewinding.sq_sub_le_twice _ _ _
  rw [toReal_fork, toReal_accept]
  have hcs : (∑ j, a j) ^ 2 / q ≤ ∑ j, a j ^ 2 := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp
    · rw [div_le_iff₀ (by exact_mod_cast hq), mul_comm]
      simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := a)
  calc (∑ j, a j) ^ 2 / q - (∑ j, a j) / N ≤ ∑ j, a j ^ 2 - ∑ j, a j / N := by
        rw [Finset.sum_div]
        linarith
    _ = ∑ j, (a j ^ 2 - a j / N) := by rw [Finset.sum_sub_distrib]
    _ ≤ _ := Finset.sum_le_sum fun j _ => hj j

/-- The forking lemma solved for the acceptance probability: `acc ≤ q / |H| + √(q · frk)`. -/
theorem le_add_sqrt_fork (first : PMF S) (A : S → (Fin q → H) → Option (Fin q) × β) :
    (accept first A true).toReal ≤
      q / Fintype.card H + √(q * ((fork first A).map Option.isSome true).toReal) := by
  set ε := (accept first A true).toReal with hεdef
  set N : ℝ := (Fintype.card H : ℝ)
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hfork := sq_div_sub_le_fork first A
  by_cases hε : ε ≤ q / N
  · exact hε.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  · have hq : (0 : ℝ) < q := by
      rcases Nat.eq_zero_or_pos q with hq0 | hq0
      · subst hq0
        exact absurd (by simp [hεdef, toReal_accept]) hε
      · exact_mod_cast hq0
    have hsq : (ε - q / N) ^ 2 ≤ q * ((fork first A).map Option.isSome true).toReal := by
      have hmul := mul_le_mul_of_nonneg_left hfork hq.le
      refine le_trans ?_ hmul
      have hexpand : q * (ε ^ 2 / q - ε / N) = (ε - q / N) ^ 2 + (ε - q / N) * (q / N) := by
        field_simp
        ring
      rw [hexpand]
      exact le_add_of_nonneg_right (mul_nonneg (by linarith) (by positivity))
    have := Real.abs_le_sqrt hsq
    linarith [le_abs_self (ε - q / N)]

/-- A successful fork comes from one coin sample and two answer vectors that agree before the
returned index `j` and differ at it, on both of which `A` outputs `j`. -/
theorem mem_support_fork {first : PMF S} {A : S → (Fin q → H) → Option (Fin q) × β}
    {j : Fin q} {out out' : β} (hfork : some (j, out, out') ∈ (fork first A).support) :
    ∃ s ∈ first.support, ∃ h h' : Fin q → H, (∀ i < j, h i = h' i) ∧ h j ≠ h' j ∧
      A s h = (some j, out) ∧ A s h' = (some j, out') := by
  simp only [fork, Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hfork
  obtain ⟨s, hs, h, -, h', -, hres⟩ := hfork
  refine ⟨s, hs, h, splice j h h', fun i hi => by simp [splice, hi], ?_⟩
  cases hA : (A s h).1 with
  | none => simp [hA] at hres
  | some j' =>
    simp only [hA] at hres
    split_ifs at hres with hc
    · simp only [Option.some.injEq, Prod.mk.injEq] at hres
      obtain ⟨rfl, rfl, rfl⟩ := hres
      refine ⟨by simpa [splice] using hc.2, Prod.ext hA rfl, Prod.ext hc.1 rfl⟩

end Cslib.Probability.Forking
