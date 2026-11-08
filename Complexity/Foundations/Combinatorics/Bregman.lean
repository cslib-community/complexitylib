/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, Mathlib/Combinatorics/)

public import Complexity.Init
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.Matrix.Permanent
import Complexity.Foundations.Analysis.SpecialFunctions.LogSum
import Complexity.Foundations.Data.Matrix.Permanent.ZeroOne
import Mathlib.GroupTheory.Perm.DomMulAct

/-!
# Brégman's theorem (Minc's conjecture)

The permanent of an `n × n` 0/1 matrix with row sums `r i` is at most `∏ i, (r i)! ^ (1 / r i)`
[Bregman1973]. Equivalently, a bipartite graph whose left vertices have degrees `d a` has at most
`∏ a, (d a)! ^ (1 / d a)` perfect matchings. The bound is attained by disjoint unions of complete
bipartite graphs `K_{d,d}`, that is, by block-diagonal all-ones matrices.

A bipartite graph is a relation `R : α → β → Prop` between finite types, and its perfect matchings
are the bijections `e : α ≃ β` with `R a (e a)` for every `a`. The permanent of a 0/1 matrix `A`
counts the perfect matchings of `fun i j => A i j = 1` (`Matrix.permanent_eq_card_filter_of_le_one`
in `Complexity.Foundations.Data.Matrix.Permanent.ZeroOne`).

The proof is Schrijver's induction on `n` [Schrijver1978]: the log-sum inequality
(`Real.sum_mul_log_div_card_le`) bounds the number of matchings through the edges at one vertex,
the induction hypothesis bounds the matchings of each graph with an edge's two endpoints deleted,
and averaging over all left vertices turns the deleted-column counts into the identity
`log d + (d - 1) log (d - 1)! / (d - 1) + (n - d) log d! / d = n log d! / d`. Radhakrishnan's
entropy proof [Radhakrishnan1997] and the random-ordering proof in [AlonSpencer2016] (The
Probabilistic Lens: Brégman's Theorem, after Chapter 2) are alternative proofs of the same bound.

A vertex of degree `0` contributes the factor `0! ^ (1 / 0) = 1` with Mathlib's `Real.rpow`
convention `x ^ (1 / 0) = x ^ 0 = 1`; the graph then has no perfect matching, so the bound holds
for every relation and every 0/1 matrix, without positivity hypotheses.

## Main results

* `Equiv.card_filter_forall_rel_le_prod_factorial_rpow`: Brégman's bound on the number of perfect
  matchings of a bipartite graph in terms of its left degrees.
* `Equiv.log_card_filter_forall_rel_le_sum`: the same bound in logarithmic form.
* `Equiv.card_filter_forall_eq_eq_prod_factorial_rpow`: equality for disjoint unions of complete
  bipartite graphs.
* `Matrix.permanent_le_prod_factorial_rpow`: Brégman's theorem for the permanent of a 0/1 matrix.
* `Matrix.permanent_le_factorial_rpow_card_div`: `per A ≤ d! ^ (n / d)` when every row sum is `d`.
* `Matrix.permanent_eq_prod_factorial_rpow_of_eq_ite`: equality for block-diagonal all-ones
  matrices.

## References

* [L. M. Brégman, *Some properties of nonnegative matrices and their permanents*][Bregman1973]
* [A. Schrijver, *A short proof of Minc's conjecture*][Schrijver1978]
* [J. Radhakrishnan, *An entropy proof of Bregman's theorem*][Radhakrishnan1997]
* [N. Alon and J. H. Spencer, *The Probabilistic Method*][AlonSpencer2016], The Probabilistic Lens:
  Brégman's Theorem
-/

public section

open Finset

namespace Equiv

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The Brégman weight `log (r!) / r`, so that `exp (bregmanWeight r) = (r!) ^ (1 / r)`. -/
private noncomputable def bregmanWeight (r : ℕ) : ℝ := Real.log r.factorial / r

private theorem bregmanWeight_nonneg (r : ℕ) : 0 ≤ bregmanWeight r :=
  div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

private theorem mul_bregmanWeight (r : ℕ) : r * bregmanWeight r = Real.log r.factorial := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · rw [bregmanWeight, mul_div_cancel₀ _ (by exact_mod_cast hr.ne')]

/-- The row identity of Schrijver's proof: deleting column `k ∈ s` from row `s` lowers its degree
by one exactly when the column is in `s`. -/
private theorem row_identity (s : Finset β) {k : β} (hk : k ∈ s) :
    Real.log #s + ∑ b ∈ univ.erase k, bregmanWeight #(s.erase b) =
      Fintype.card β * bregmanWeight #s := by
  set a := #(s.erase k) with ha
  have hs : #s = a + 1 := by rw [ha, card_erase_of_mem hk]; have := card_pos.2 ⟨k, hk⟩; omega
  have hsplit : ∑ b ∈ univ.erase k, bregmanWeight #(s.erase b) =
      ∑ b ∈ s.erase k, bregmanWeight a + ∑ b ∈ sᶜ, bregmanWeight #s := by
    rw [← sum_filter_add_sum_filter_not (univ.erase k) (· ∈ s)]
    congr 1
    · have : (univ.erase k).filter (· ∈ s) = s.erase k := by
        ext b; simp [and_comm]
      rw [this]
      refine sum_congr rfl fun b hb => ?_
      rw [card_erase_of_mem (mem_of_mem_erase hb), hs, ha, card_erase_of_mem hk, hs]
      simp [ha]
    · have : (univ.erase k).filter (· ∉ s) = sᶜ := by
        ext b; simp only [mem_filter, mem_erase, mem_univ, and_true, mem_compl]
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨fun hb => h (hb ▸ hk), h⟩
      rw [this]
      exact sum_congr rfl fun b hb => by rw [erase_eq_of_notMem (mem_compl.1 hb)]
  rw [hsplit, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, ← ha]
  have hcompl : (#sᶜ : ℝ) + #s = Fintype.card β := by
    exact_mod_cast card_compl_add_card s
  have h1 : (a : ℝ) * bregmanWeight a = Real.log a.factorial := mul_bregmanWeight a
  have h2 : (#s : ℝ) * bregmanWeight #s = Real.log (#s).factorial := mul_bregmanWeight _
  rw [hs, Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)] at h2
  rw [← hcompl, hs] at *
  push_cast at *
  linarith

universe u v

/-- Schrijver's induction, in logarithmic form with the private weight. -/
private theorem log_card_le_sum_bregmanWeight :
    ∀ (n : ℕ) {α : Type u} {β : Type v} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
      (R : α → β → Prop) [DecidableRel R], Fintype.card α = n →
      Real.log #{e : α ≃ β | ∀ a, R a (e a)} ≤
        ∑ a, bregmanWeight #{b | R a b} := by
  intro n
  induction n with
  | zero =>
    intro α β _ _ _ _ R _ hn
    have : IsEmpty α := Fintype.card_eq_zero_iff.1 hn
    have hle : #{e : α ≃ β | ∀ a, R a (e a)} ≤ 1 :=
      card_le_one.2 fun e _ e' _ => Equiv.ext fun a => isEmptyElim a
    have : Real.log #{e : α ≃ β | ∀ a, R a (e a)} ≤ 0 :=
      Real.log_nonpos (Nat.cast_nonneg _) (by exact_mod_cast hle)
    linarith [sum_nonneg fun a (_ : a ∈ univ) => bregmanWeight_nonneg #{b | R a b}]
  | succ n ih =>
    intro α β _ _ _ _ R _ hn
    obtain ⟨M, hM⟩ : ∃ M : Finset (α ≃ β),
        M = ({e : α ≃ β | ∀ a, R a (e a)} : Finset (α ≃ β)) := ⟨_, rfl⟩
    obtain ⟨s, hs⟩ : ∃ s : α → Finset β, s = fun a => ({b | R a b} : Finset β) := ⟨_, rfl⟩
    have memM : ∀ e, e ∈ M ↔ ∀ a, R a (e a) := fun e => by simp [hM]
    have mems : ∀ a b, b ∈ s a ↔ R a b := fun a b => by simp [hs]
    rw [← hM, show (fun a => bregmanWeight #{b | R a b}) = fun a => bregmanWeight #(s a) by
      rw [hs]]
    rcases M.eq_empty_or_nonempty with hM0 | ⟨e₀, he₀⟩
    · rw [hM0, card_empty, Nat.cast_zero, Real.log_zero]
      exact sum_nonneg fun a _ => bregmanWeight_nonneg _
    have hMpos : (0 : ℝ) < #M := by exact_mod_cast card_pos.2 ⟨e₀, he₀⟩
    have hβ : Fintype.card β = n + 1 := (Fintype.card_congr e₀).symm.trans hn
    -- Step A: the minor bound, from the induction hypothesis.
    have hminor : ∀ i k, Real.log #{e ∈ M | e i = k} ≤
        ∑ j ∈ univ.erase i, bregmanWeight #((s j).erase k) := by
      intro i k
      have hcard : Fintype.card {a // a ≠ i} = n := by
        simp [Fintype.card_subtype_compl, hn]
      have hIH := ih (fun (a : {a // a ≠ i}) (b : {b // b ≠ k}) => R a b) hcard
      have hinj : #{e ∈ M | e i = k} ≤
          #{e : {a // a ≠ i} ≃ {b // b ≠ k} | ∀ a : {a // a ≠ i}, R a (e a)} := by
        have hiff : ∀ e : α ≃ β, e i = k → ∀ a, a ≠ i ↔ e a ≠ k := fun e he a => by
          rw [← he]; exact e.injective.ne_iff.symm
        rw [← card_attach]
        refine card_le_card_of_injOn
          (fun e => e.1.subtypeEquiv (hiff e.1 (mem_filter.1 e.2).2)) ?_ ?_
        · intro e _
          simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and]
          intro a
          exact (memM _).1 (mem_filter.1 e.2).1 a
        · intro e _ e' _ h
          apply Subtype.ext
          ext a
          by_cases ha : a = i
          · rw [ha, (mem_filter.1 e.2).2, (mem_filter.1 e'.2).2]
          · have := congrArg (fun f => (f ⟨a, ha⟩ : β)) h
            simpa using this
      have hlog : Real.log #{e ∈ M | e i = k} ≤
          Real.log #{e : {a // a ≠ i} ≃ {b // b ≠ k} | ∀ a : {a // a ≠ i}, R a (e a)} := by
        rcases Nat.eq_zero_or_pos #{e ∈ M | e i = k} with h0 | hpos
        · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg _
        · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hinj)
      refine hlog.trans (hIH.trans_eq ?_)
      rw [sum_subtype (univ.erase i) (p := fun a => a ≠ i) (by simp)
        (f := fun j => bregmanWeight #((s j).erase k))]
      refine sum_congr rfl fun a _ => ?_
      congr 1
      rw [← card_map (Function.Embedding.subtype _)]
      congr 1
      ext b
      simp [mems, and_comm]
    -- Step B: the row bound, by the log-sum inequality.
    have hrow : ∀ i, (#M : ℝ) * Real.log #M ≤
        #M * Real.log #(s i) + ∑ e ∈ M, Real.log #{e' ∈ M | e' i = e i} := by
      intro i
      have hmaps : ∀ e ∈ M, e i ∈ s i := fun e he => (mems i (e i)).2 ((memM e).1 he i)
      have hfib : (#M : ℝ) = ∑ k ∈ s i, (#{e ∈ M | e i = k} : ℝ) := by
        exact_mod_cast card_eq_sum_card_fiberwise hmaps
      have hspos : (0 : ℝ) < #(s i) := by exact_mod_cast card_pos.2 ⟨e₀ i, hmaps e₀ he₀⟩
      have hJ := Real.sum_mul_log_div_card_le (s i)
        (x := fun k => (#{e ∈ M | e i = k} : ℝ)) fun _ _ => Nat.cast_nonneg _
      rw [← hfib, Real.log_div hMpos.ne' hspos.ne', mul_sub] at hJ
      rw [← sub_le_iff_le_add']
      refine hJ.trans_eq ?_
      rw [← sum_fiberwise_of_maps_to (g := fun e : α ≃ β => e i) (t := s i) hmaps]
      refine sum_congr rfl fun k _ => ?_
      rw [sum_congr rfl fun e he => show Real.log (#{e' ∈ M | e' i = e i} : ℕ) =
        Real.log (#{e' ∈ M | e' i = k} : ℕ) by rw [(mem_filter.1 he).2], sum_const, nsmul_eq_mul]
    -- Step C: average over the rows and reindex.
    have hswap : ∀ e ∈ M, ∑ i, ∑ j ∈ univ.erase i, bregmanWeight #((s j).erase (e i)) =
        ∑ j, ∑ b ∈ univ.erase (e j), bregmanWeight #((s j).erase b) := by
      intro e _
      simp only [sum_erase_eq_sub (mem_univ _)]
      rw [sum_sub_distrib, sum_sub_distrib, sum_comm]
      congr 1
      exact sum_congr rfl fun j _ => e.sum_comp fun b => bregmanWeight #((s j).erase b)
    have hrowid : ∀ e ∈ M,
        ∑ j, (Real.log #(s j) + ∑ b ∈ univ.erase (e j), bregmanWeight #((s j).erase b)) =
          ((n + 1 : ℕ) : ℝ) * ∑ j, bregmanWeight #(s j) := by
      intro e he
      rw [mul_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [row_identity (s j) ((mems j (e j)).2 ((memM e).1 he j)), hβ]
    have hmain : ((n + 1 : ℕ) : ℝ) * (#M * Real.log #M) ≤
        ((n + 1 : ℕ) : ℝ) * (#M * ∑ j, bregmanWeight #(s j)) := by
      calc ((n + 1 : ℕ) : ℝ) * (#M * Real.log #M) = ∑ i : α, (#M : ℝ) * Real.log #M := by
            rw [sum_const, card_univ, hn, nsmul_eq_mul]
        _ ≤ ∑ i, (#M * Real.log #(s i) + ∑ e ∈ M, Real.log #{e' ∈ M | e' i = e i}) :=
            sum_le_sum fun i _ => hrow i
        _ ≤ ∑ i, (#M * Real.log #(s i) +
              ∑ e ∈ M, ∑ j ∈ univ.erase i, bregmanWeight #((s j).erase (e i))) :=
            sum_le_sum fun i _ => add_le_add le_rfl (sum_le_sum fun (e : α ≃ β) _ => hminor i (e i))
        _ = ∑ e ∈ M, ∑ j,
              (Real.log #(s j) + ∑ b ∈ univ.erase (e j), bregmanWeight #((s j).erase b)) := by
            simp only [sum_add_distrib]
            rw [sum_const (∑ j, Real.log (#(s j) : ℝ)), nsmul_eq_mul, ← mul_sum, sum_comm,
              sum_congr rfl hswap]
        _ = ∑ e ∈ M, ((n + 1 : ℕ) : ℝ) * ∑ j, bregmanWeight #(s j) := sum_congr rfl hrowid
        _ = _ := by rw [sum_const, nsmul_eq_mul]; ring
    exact le_of_mul_le_mul_left (le_of_mul_le_mul_left hmain (by positivity)) hMpos

/-- **Brégman's theorem** (Minc's conjecture), logarithmic form: the number of bijections
`e : α ≃ β` with `R a (e a)` for every `a` has logarithm at most `∑ a, log (d a)! / d a`, where
`d a = #{b | R a b}`. A vertex with `d a = 0` contributes `0`. -/
theorem log_card_filter_forall_rel_le_sum (R : α → β → Prop) [DecidableRel R] :
    Real.log #{e : α ≃ β | ∀ a, R a (e a)} ≤
      ∑ a, Real.log (#{b | R a b} : ℕ).factorial / #{b | R a b} :=
  log_card_le_sum_bregmanWeight _ R rfl

/-- **Brégman's theorem** (Minc's conjecture) for bipartite perfect matchings: the number of
bijections `e : α ≃ β` with `R a (e a)` for every `a` is at most `∏ a, (d a)! ^ (1 / d a)`, where
`d a = #{b | R a b}` is the degree of the left vertex `a`. A vertex with `d a = 0` contributes the
factor `0! ^ (1 / 0) = 1`; then there is no such bijection. -/
theorem card_filter_forall_rel_le_prod_factorial_rpow (R : α → β → Prop) [DecidableRel R] :
    (#{e : α ≃ β | ∀ a, R a (e a)} : ℝ) ≤
      ∏ a, ((#{b | R a b} : ℕ).factorial : ℝ) ^ (1 / (#{b | R a b} : ℝ)) := by
  rcases Nat.eq_zero_or_pos #{e : α ≃ β | ∀ a, R a (e a)} with h0 | hpos
  · rw [h0, Nat.cast_zero]
    exact prod_nonneg fun a _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hP : (0 : ℝ) < #{e : α ≃ β | ∀ a, R a (e a)} := by exact_mod_cast hpos
  rw [← Real.exp_log hP]
  refine (Real.exp_le_exp.2 (log_card_filter_forall_rel_le_sum R)).trans_eq ?_
  rw [Real.exp_sum]
  refine prod_congr rfl fun a _ => ?_
  rw [Real.rpow_def_of_pos (by exact_mod_cast Nat.factorial_pos _), mul_one_div]

/-- **Equality in Brégman's theorem** for disjoint unions of complete bipartite graphs: when `a`
and `b` are adjacent exactly if `f a = f b`, the bound of
`card_filter_forall_rel_le_prod_factorial_rpow` is attained. Each fiber of `f` of size `d` is a
block `K_{d,d}` contributing `d!` matchings. -/
theorem card_filter_forall_eq_eq_prod_factorial_rpow {ι : Type*} [DecidableEq ι] (f : α → ι) :
    (#{e : α ≃ α | ∀ a, f a = f (e a)} : ℝ) =
      ∏ a, ((#{b | f a = f b} : ℕ).factorial : ℝ) ^ (1 / (#{b | f a = f b} : ℝ)) := by
  have hstab : #{e : α ≃ α | ∀ a, f a = f (e a)} =
      ∏ i ∈ univ.image f, (Fintype.card {a // f a = i}).factorial := by
    rw [← DomMulAct.stabilizer_card' f, ← Fintype.card_subtype]
    refine Fintype.card_congr (Equiv.subtypeEquivRight fun σ => ?_)
    simp only [funext_iff, Function.comp_apply]
    exact forall_congr' fun a => eq_comm
  rw [hstab, Finset.prod_comp
    (fun i => ((#{b | i = f b} : ℕ).factorial : ℝ) ^ (1 / (#{b | i = f b} : ℝ))) f]
  push_cast
  refine prod_congr rfl fun i hi => ?_
  obtain ⟨a, -, rfl⟩ := mem_image.1 hi
  have hfib : #{x | f x = f a} = #{b | f a = f b} := by
    congr 1; ext b; simp [eq_comm]
  rw [Fintype.card_subtype, ← hfib, one_div]
  rw [Real.rpow_inv_natCast_pow (Nat.cast_nonneg _)]
  exact (card_pos.2 ⟨a, by simp⟩).ne'

end Equiv

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Brégman's theorem** (Minc's conjecture): the permanent of an `n × n` 0/1 matrix with row sums
`r i` is at most `∏ i, (r i)! ^ (1 / r i)`. A zero row makes both the permanent `0` and its factor
`0! ^ (1 / 0) = 1`. -/
theorem permanent_le_prod_factorial_rpow {A : Matrix n n ℕ} (hA : ∀ i j, A i j ≤ 1) :
    (A.permanent : ℝ) ≤ ∏ i, ((∑ j, A i j).factorial : ℝ) ^ (1 / ((∑ j, A i j : ℕ) : ℝ)) := by
  have hrow : ∀ i, ∑ j, A i j = #{j | A i j = 1} := fun i => by
    rw [card_eq_sum_ones, sum_filter]
    refine sum_congr rfl fun j _ => ?_
    have := hA i j
    split_ifs with h <;> omega
  rw [permanent_eq_card_filter_of_le_one hA]
  have hperm : #{σ : Equiv.Perm n | ∀ i, A i (σ i) = 1} = #{e : n ≃ n | ∀ i, A i (e i) = 1} := by
    convert rfl
  rw [hperm]
  refine (@Equiv.card_filter_forall_rel_le_prod_factorial_rpow n n _ _ _ _ (fun i j => A i j = 1)
    fun _ _ => inferInstance).trans_eq (prod_congr rfl fun i _ => ?_)
  rw [hrow i]

/-- **Brégman's theorem for regular 0/1 matrices**: if every row sum is `d`, then
`per A ≤ d! ^ (n / d)`. For `d = 0` both sides are `0` and `1`. -/
theorem permanent_le_factorial_rpow_card_div {A : Matrix n n ℕ} (hA : ∀ i j, A i j ≤ 1) {d : ℕ}
    (hd : ∀ i, ∑ j, A i j = d) :
    (A.permanent : ℝ) ≤ (d.factorial : ℝ) ^ ((Fintype.card n : ℝ) / d) := by
  refine (permanent_le_prod_factorial_rpow hA).trans_eq ?_
  simp only [hd, prod_const, card_univ]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), one_div_mul_eq_div]

/-- **Equality in Brégman's theorem**: a 0/1 matrix whose one-entries form diagonal all-ones blocks
(`A i j = 1` exactly when `f i = f j`) attains the bound of `permanent_le_prod_factorial_rpow`. -/
theorem permanent_eq_prod_factorial_rpow_of_eq_ite {A : Matrix n n ℕ} {ι : Type*} [DecidableEq ι]
    (f : n → ι) (hA : ∀ i j, A i j = if f i = f j then 1 else 0) :
    (A.permanent : ℝ) = ∏ i, ((∑ j, A i j).factorial : ℝ) ^ (1 / ((∑ j, A i j : ℕ) : ℝ)) := by
  have hle : ∀ i j, A i j ≤ 1 := fun i j => by rw [hA]; split_ifs <;> omega
  have hrow : ∀ i, ∑ j, A i j = #{j | f i = f j} := fun i => by
    simp only [hA, sum_boole, Nat.cast_id]
  rw [permanent_eq_card_filter_of_le_one hle]
  have hperm : #{σ : Equiv.Perm n | ∀ i, A i (σ i) = 1} =
      #{e : n ≃ n | ∀ i, f i = f (e i)} := by
    convert rfl using 2
    ext σ
    simp only [mem_filter, mem_univ, true_and, hA, ite_eq_left_iff, zero_ne_one, imp_false,
      not_not]
  rw [hperm, Equiv.card_filter_forall_eq_eq_prod_factorial_rpow f]
  refine prod_congr rfl fun i _ => ?_
  rw [hrow i]

end Matrix
