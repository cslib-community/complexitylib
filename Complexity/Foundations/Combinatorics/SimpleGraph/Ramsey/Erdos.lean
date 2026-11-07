/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/Ramsey.lean`)

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.SimpleGraph.Ramsey.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Complexity.Foundations.Data.BitString.Agree
import Mathlib.Data.Sym.Card

/-!
# Erdős's lower bound for Ramsey numbers

Erdős's 1947 argument, the first application of the probabilistic method, is a count. A fixed
`k`-set of `Fin n` is a clique in exactly a `2 ^ (-C(k, 2))` fraction of the `2 ^ C(n, 2)` graphs
on `Fin n`, and an independent set in the same fraction. If the `C(n, k)` candidate sets together
cover fewer than all graphs, some graph has neither a `k`-clique nor a `k`-independent set:

* `2 * C(n, k) < 2 ^ C(k, 2)` implies `n < R(k, k)` [AlonSpencer2016, Proposition 1.1.1];
* `n ^ 2 ≤ 2 ^ k` and `k ≥ 3` imply `2 * C(n, k) < 2 ^ C(k, 2)`, hence `2 ^ (k / 2) < R(k, k)` for
  `k ≥ 3` [Erdos1947] [Jukna2011, §4.9].

We count graphs exactly rather than build the uniform distribution: the graphs are encoded by their
edge indicators `Sym2 (Fin n) → Bool`, and the union bound becomes `Finset.card_biUnion_le`.

The argument proves existence only. No explicit graph matching it is known; Nagy's explicit graph
`SimpleGraph.nagyGraph` has only `C(t, 3)` vertices (`SimpleGraph.choose_three_lt_ramseyNumber`).

## Main results

* `SimpleGraph.exists_cliqueFree_indepSetFree_of_choose`: the asymmetric counting bound, with no
  `k`-clique and no `l`-independent set.
* `SimpleGraph.lt_ramseyNumber_of_choose`, `SimpleGraph.lt_ramseyNumber_of_two_mul_choose_lt`:
  the resulting lower bounds on `R(k, l)` and `R(k, k)`.
* `SimpleGraph.lt_ramseyNumber_of_sq_le`: `n ^ 2 ≤ 2 ^ k` and `k ≥ 3` imply `n < R(k, k)`.
* `SimpleGraph.two_pow_lt_ramseyNumber_sq`: `2 ^ k < R(k, k) ^ 2` for `k ≥ 3`.
* `SimpleGraph.two_rpow_half_lt_ramseyNumber`: `2 ^ (k / 2) < R(k, k)` for `k ≥ 3`.

## References

* [N. Alon, J. H. Spencer, *The Probabilistic Method*][AlonSpencer2016]
* [P. Erdős, *Some remarks on the theory of graphs*][Erdos1947]
* [S. Jukna, *Extremal Combinatorics*][Jukna2011]
-/

public section

open Finset

namespace SimpleGraph

/-- The graph on `Fin n` whose edges are the pairs marked `true`. -/
private def ofMarks {n : ℕ} (x : Sym2 (Fin n) → Bool) : SimpleGraph (Fin n) :=
  fromEdgeSet {e | x e = true}

/-- The `C(#s, 2)` pairs of distinct elements of `s`. -/
private def pairs {n : ℕ} (s : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  s.offDiag.image (Function.uncurry Sym2.mk)

private theorem card_pairs {n : ℕ} (s : Finset (Fin n)) : #(pairs s) = (#s).choose 2 :=
  Sym2.card_image_offDiag s

private theorem forall_pairs_of_isClique {n : ℕ} {x : Sym2 (Fin n) → Bool} {s : Finset (Fin n)}
    (h : (ofMarks x).IsClique (s : Set (Fin n))) : ∀ e ∈ pairs s, x e = true := by
  intro e he
  obtain ⟨⟨u, v⟩, huv, rfl⟩ := mem_image.1 (by simpa only [pairs] using he)
  obtain ⟨hu, hv, hne⟩ := mem_offDiag.1 huv
  exact ((fromEdgeSet_adj _).1 (h hu hv hne)).1

private theorem forall_pairs_of_isIndepSet {n : ℕ} {x : Sym2 (Fin n) → Bool} {s : Finset (Fin n)}
    (h : (ofMarks x).IsIndepSet (s : Set (Fin n))) : ∀ e ∈ pairs s, x e = false := by
  intro e he
  obtain ⟨⟨u, v⟩, huv, rfl⟩ := mem_image.1 (by simpa only [pairs] using he)
  obtain ⟨hu, hv, hne⟩ := mem_offDiag.1 huv
  have hna := h hu hv hne
  rw [ofMarks, fromEdgeSet_adj] at hna
  simpa [hne] using hna

/-- Prescribing the values on `S` leaves `2 ^ (|ι| - |S|)` Boolean functions. -/
private theorem card_filter_forall_mem_eq_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (b : Bool) :
    #{x : ι → Bool | ∀ i ∈ S, x i = b} * 2 ^ #S = 2 ^ Fintype.card ι := by
  have hcard : #{x : ι → Bool | ∀ i ∈ S, x i = b} = 2 ^ #Sᶜ := by
    rw [← Cslib.BitString.card_filter_forall_notMem_eq Sᶜ fun _ => b]
    refine congrArg card (filter_congr fun x _ => ?_)
    simp only [mem_compl, not_not]
  rw [hcard, ← pow_add, card_compl, Nat.sub_add_cancel (card_le_univ S)]

/-- **Erdős's counting bound**, asymmetric form: if
`C(n, k) 2 ^ (-C(k, 2)) + C(n, l) 2 ^ (-C(l, 2)) < 1`, written without division, then some graph
on `Fin n` has no `k`-clique and no `l`-independent set [Erdos1947] [AlonSpencer2016, §1.1]. -/
theorem exists_cliqueFree_indepSetFree_of_choose {n k l : ℕ}
    (h : n.choose k * 2 ^ l.choose 2 + n.choose l * 2 ^ k.choose 2 <
      2 ^ (k.choose 2 + l.choose 2)) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ G.IndepSetFree l := by
  classical
  set N := Fintype.card (Sym2 (Fin n))
  let A : Finset (Sym2 (Fin n) → Bool) :=
    (powersetCard k univ).biUnion fun t => {x | ∀ e ∈ pairs t, x e = true}
  let B : Finset (Sym2 (Fin n) → Bool) :=
    (powersetCard l univ).biUnion fun t => {x | ∀ e ∈ pairs t, x e = false}
  have hA : #A * 2 ^ k.choose 2 ≤ n.choose k * 2 ^ N := by
    calc #A * 2 ^ k.choose 2
        ≤ (∑ t ∈ powersetCard k univ, #{x : Sym2 (Fin n) → Bool | ∀ e ∈ pairs t, x e = true})
            * 2 ^ k.choose 2 := Nat.mul_le_mul_right _ (card_biUnion_le)
      _ = ∑ t ∈ powersetCard k (univ : Finset (Fin n)), 2 ^ N := by
          rw [sum_mul]
          refine sum_congr rfl fun t ht => ?_
          rw [← (mem_powersetCard.1 ht).2, ← card_pairs]
          exact card_filter_forall_mem_eq_mul _ _
      _ = n.choose k * 2 ^ N := by
          rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul]
  have hB : #B * 2 ^ l.choose 2 ≤ n.choose l * 2 ^ N := by
    calc #B * 2 ^ l.choose 2
        ≤ (∑ t ∈ powersetCard l univ, #{x : Sym2 (Fin n) → Bool | ∀ e ∈ pairs t, x e = false})
            * 2 ^ l.choose 2 := Nat.mul_le_mul_right _ (card_biUnion_le)
      _ = ∑ t ∈ powersetCard l (univ : Finset (Fin n)), 2 ^ N := by
          rw [sum_mul]
          refine sum_congr rfl fun t ht => ?_
          rw [← (mem_powersetCard.1 ht).2, ← card_pairs]
          exact card_filter_forall_mem_eq_mul _ _
      _ = n.choose l * 2 ^ N := by
          rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul]
  have hlt : #(A ∪ B) < #(univ : Finset (Sym2 (Fin n) → Bool)) := by
    rw [card_univ, Fintype.card_fun, Fintype.card_bool]
    have hP := pow_pos (show 0 < 2 by norm_num) N
    refine lt_of_le_of_lt (card_union_le A B) ?_
    refine lt_of_mul_lt_mul_right (a := 2 ^ k.choose 2 * 2 ^ l.choose 2) ?_ (Nat.zero_le _)
    calc (#A + #B) * (2 ^ k.choose 2 * 2 ^ l.choose 2)
        = #A * 2 ^ k.choose 2 * 2 ^ l.choose 2 + #B * 2 ^ l.choose 2 * 2 ^ k.choose 2 := by ring
      _ ≤ n.choose k * 2 ^ N * 2 ^ l.choose 2 + n.choose l * 2 ^ N * 2 ^ k.choose 2 := by
          gcongr
      _ = 2 ^ N * (n.choose k * 2 ^ l.choose 2 + n.choose l * 2 ^ k.choose 2) := by ring
      _ < 2 ^ N * 2 ^ (k.choose 2 + l.choose 2) := Nat.mul_lt_mul_of_pos_left h hP
      _ = 2 ^ N * (2 ^ k.choose 2 * 2 ^ l.choose 2) := by rw [pow_add]
  obtain ⟨x, -, hx⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨ofMarks x, fun t ht => hx ?_, fun t ht => hx ?_⟩
  · exact mem_union_left _ (mem_biUnion.2 ⟨t, mem_powersetCard.2 ⟨subset_univ _, ht.2⟩,
      mem_filter.2 ⟨mem_univ _, forall_pairs_of_isClique ht.1⟩⟩)
  · exact mem_union_right _ (mem_biUnion.2 ⟨t, mem_powersetCard.2 ⟨subset_univ _, ht.2⟩,
      mem_filter.2 ⟨mem_univ _, forall_pairs_of_isIndepSet ht.1⟩⟩)

/-- The counting bound as a lower bound on `R(k, l)`. -/
theorem lt_ramseyNumber_of_choose {n k l : ℕ}
    (h : n.choose k * 2 ^ l.choose 2 + n.choose l * 2 ^ k.choose 2 <
      2 ^ (k.choose 2 + l.choose 2)) : n < ramseyNumber k l := by
  have := card_lt_ramseyNumber_iff (k := k) (l := l) (V := Fin n)
  rw [Fintype.card_fin] at this
  exact this.2 (exists_cliqueFree_indepSetFree_of_choose h)

/-- If `C(n, k) 2 ^ (1 - C(k, 2)) < 1`, then `n < R(k, k)` [AlonSpencer2016, Proposition 1.1.1]. -/
theorem lt_ramseyNumber_of_two_mul_choose_lt {n k : ℕ} (h : 2 * n.choose k < 2 ^ k.choose 2) :
    n < ramseyNumber k k := by
  refine lt_ramseyNumber_of_choose ?_
  rw [pow_add, ← two_mul, ← mul_assoc]
  exact Nat.mul_lt_mul_of_pos_right h (pow_pos (by norm_num) _)

private theorem four_mul_two_pow_lt_factorial_sq : ∀ {k : ℕ}, 3 ≤ k → 4 * 2 ^ k < k.factorial ^ 2
  | 3, _ => by decide
  | k + 4, _ => by
    have ih := four_mul_two_pow_lt_factorial_sq (k := k + 3) (by omega)
    rw [Nat.factorial_succ, mul_pow, pow_succ]
    have : 2 ≤ (k + 3 + 1) ^ 2 := by nlinarith
    calc 4 * (2 ^ (k + 3) * 2) = 4 * 2 ^ (k + 3) * 2 := by ring
      _ < (k + 3).factorial ^ 2 * 2 := by omega
      _ ≤ (k + 3).factorial ^ 2 * (k + 3 + 1) ^ 2 := Nat.mul_le_mul_left _ this
      _ = (k + 3 + 1) ^ 2 * (k + 3).factorial ^ 2 := by ring

/-- The arithmetic of Erdős's bound: if `k ≥ 3` and `n ^ 2 ≤ 2 ^ k`, then
`2 * C(n, k) < 2 ^ C(k, 2)`. Squaring, `(k! C(n, k)) ^ 2 ≤ n ^ (2k) ≤ 2 ^ (k ^ 2)` and
`4 * 2 ^ k < k! ^ 2`. -/
theorem two_mul_choose_lt_of_sq_le {n k : ℕ} (hk : 3 ≤ k) (hn : n ^ 2 ≤ 2 ^ k) :
    2 * n.choose k < 2 ^ k.choose 2 := by
  have hkk : k * k = 2 * k.choose 2 + k := by
    rw [Nat.choose_two_right]
    have h2 : 2 ∣ k * (k - 1) := (Nat.even_mul_pred_self k).two_dvd
    rcases k with _ | k
    · omega
    · rw [Nat.mul_div_cancel' h2]
      simp only [Nat.add_sub_cancel]
      ring
  rcases Nat.eq_zero_or_pos (n.choose k) with h0 | hpos
  · rw [h0]; exact pow_pos (by norm_num) _
  have hsq : (k.factorial * n.choose k) ^ 2 ≤ 2 ^ (k * k) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    calc (n.descFactorial k) ^ 2 ≤ (n ^ k) ^ 2 :=
          Nat.pow_le_pow_left (Nat.descFactorial_le_pow _ _) _
      _ = (n ^ 2) ^ k := by ring
      _ ≤ (2 ^ k) ^ k := Nat.pow_le_pow_left hn _
      _ = 2 ^ (k * k) := by ring
  have hfac := four_mul_two_pow_lt_factorial_sq hk
  have hmain : (2 * n.choose k) ^ 2 * 2 ^ k < 2 ^ (k * k) := by
    calc (2 * n.choose k) ^ 2 * 2 ^ k = 4 * 2 ^ k * n.choose k ^ 2 := by ring
      _ < k.factorial ^ 2 * n.choose k ^ 2 :=
          Nat.mul_lt_mul_of_pos_right hfac (pow_pos hpos _)
      _ = (k.factorial * n.choose k) ^ 2 := by ring
      _ ≤ 2 ^ (k * k) := hsq
  rw [hkk, pow_add] at hmain
  have hlt : (2 * n.choose k) ^ 2 < (2 ^ k.choose 2) ^ 2 := by
    rw [← pow_mul, mul_comm (k.choose 2) 2]
    exact lt_of_mul_lt_mul_right hmain (Nat.zero_le _)
  exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) hlt

/-- **Erdős 1947**: if `k ≥ 3` and `n ≤ 2 ^ (k / 2)`, that is `n ^ 2 ≤ 2 ^ k`, then some graph on
`n` vertices has neither a `k`-clique nor a `k`-independent set, so `n < R(k, k)`
[Erdos1947] [Jukna2011, §4.9]. -/
theorem lt_ramseyNumber_of_sq_le {n k : ℕ} (hk : 3 ≤ k) (hn : n ^ 2 ≤ 2 ^ k) :
    n < ramseyNumber k k :=
  lt_ramseyNumber_of_two_mul_choose_lt (two_mul_choose_lt_of_sq_le hk hn)

/-- Erdős's bound in integer form: `2 ^ k < R(k, k) ^ 2` for `k ≥ 3`. -/
theorem two_pow_lt_ramseyNumber_sq {k : ℕ} (hk : 3 ≤ k) : 2 ^ k < ramseyNumber k k ^ 2 := by
  have h1 := lt_ramseyNumber_of_sq_le hk (Nat.sqrt_le' (2 ^ k))
  have h2 := Nat.lt_succ_sqrt' (2 ^ k)
  calc 2 ^ k < (Nat.sqrt (2 ^ k) + 1) ^ 2 := h2
    _ ≤ ramseyNumber k k ^ 2 := Nat.pow_le_pow_left h1 _

/-- **Erdős 1947**: `2 ^ (k / 2) < R(k, k)` for every `k ≥ 3` [Erdos1947] [Jukna2011, §4.9]. -/
theorem two_rpow_half_lt_ramseyNumber {k : ℕ} (hk : 3 ≤ k) :
    (2 : ℝ) ^ ((k : ℝ) / 2) < ramseyNumber k k := by
  have h := two_pow_lt_ramseyNumber_sq hk
  refine lt_of_pow_lt_pow_left₀ 2 (Nat.cast_nonneg _) ?_
  rw [← Real.rpow_natCast ((2 : ℝ) ^ ((k : ℝ) / 2)) 2, ← Real.rpow_mul (by norm_num)]
  rw [show (k : ℝ) / 2 * ((2 : ℕ) : ℝ) = k by push_cast; ring, Real.rpow_natCast]
  exact_mod_cast h

end SimpleGraph

end
