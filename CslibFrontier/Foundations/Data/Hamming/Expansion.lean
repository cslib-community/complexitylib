/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Init
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Expansion of the axis-parallel line closure

The *line closure* of a set `S` of points of `X ^ n` is the union of the axis-parallel lines
through the points of `S`: the points `y` such that changing one coordinate of `y` lands in `S`
(`Cslib.lineClosure`). This is the closure `S̄ = ⋃ᵢ πᵢ⁻¹(πᵢ(S))` of
[Babai, Fortnow, Lund, Definition 5.7][BabaiFortnowLund1991], where `πᵢ` forgets the `i`-th
coordinate. The closure of a set of at most half of the points is larger than the set by a factor
`1 + 1 / (2 n)` (`Cslib.card_le_two_mul_card_lineClosure_sdiff`, `Cslib.card_lineClosure_ge`),
the Expansion Lemma [Babai, Fortnow, Lund, Lemma 5.8][BabaiFortnowLund1991], which they attribute
to Aldous.

Our proof is a canonical-path argument, not Aldous's. For `x ∈ S` and `z ∉ S`, the path from `x` to
`z` that replaces the coordinates of `x` by those of `z` in increasing order leaves `S` along some
edge `(u, update u c (z c))` with `u ∈ S`. Swapping the first `c` coordinates of `x` and `z` is a
bijection of pairs that sends this event to the event that changing the `c`-th coordinate of a point
`u ∈ S` to that of an arbitrary point leaves `S`. Counting, `|S| |Sᶜ| ≤ n |X| ^ n |S̄ \ S|`, and
`|Sᶜ| ≥ |X| ^ n / 2` gives `|S| ≤ 2 n |S̄ \ S|`.

## Main definitions

* `Cslib.lineClosure`: the union of the axis-parallel lines through the points of a set.

## Main results

* `Cslib.card_mul_card_compl_le`: `|S| |Sᶜ| ≤ n |X| ^ n |S̄ \ S|`.
* `Cslib.card_le_two_mul_card_lineClosure_sdiff`, `Cslib.card_lineClosure_ge`: the Expansion
  Lemma.

## References

* [L. Babai, L. Fortnow, C. Lund, *Non-deterministic exponential time has two-prover interactive
  protocols*][BabaiFortnowLund1991], Section 5.2
-/

@[expose] public section

namespace Cslib

open Finset Function

variable {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}

/-- The *line closure* of a set `S` of points of `X ^ n`: the points `y` that agree with some point
of `S` in all coordinates but one, that is, the union of the axis-parallel lines through the points
of `S` [Babai, Fortnow, Lund, Definition 5.7][BabaiFortnowLund1991]. -/
def lineClosure (S : Finset (Fin n → X)) : Finset (Fin n → X) :=
  {y | ∃ i t, update y i t ∈ S}

/-- Membership in the line closure. -/
theorem mem_lineClosure {S : Finset (Fin n → X)} {y : Fin n → X} :
    y ∈ lineClosure S ↔ ∃ i t, update y i t ∈ S := by
  simp [lineClosure]

/-- In positive dimension, a set lies in its line closure. -/
theorem subset_lineClosure {S : Finset (Fin n → X)} (hn : 0 < n) : S ⊆ lineClosure S :=
  fun y hy => mem_lineClosure.mpr ⟨⟨0, hn⟩, y ⟨0, hn⟩, by simpa using hy⟩

/-- The point that takes its first `k` coordinates from `z` and the others from `x`: the `k`-th
point of the canonical path from `x` to `z`. -/
private def mix (k : ℕ) (x z : Fin n → X) : Fin n → X :=
  fun j => if (j : ℕ) < k then z j else x j

omit [Fintype X] [DecidableEq X] in
private theorem mix_zero (x z : Fin n → X) : mix 0 x z = x := by
  funext j
  simp [mix]

omit [Fintype X] [DecidableEq X] in
private theorem mix_self (x z : Fin n → X) : mix n x z = z := by
  funext j
  simp [mix, j.isLt]

omit [Fintype X] [DecidableEq X] in
private theorem mix_succ (x z : Fin n → X) (c : Fin n) :
    mix ((c : ℕ) + 1) x z = update (mix c x z) c (z c) := by
  funext j
  by_cases hj : j = c
  · subst hj
    simp [mix]
  · have hne : (j : ℕ) ≠ c := fun h => hj (Fin.ext h)
    have hiff : (j : ℕ) < c + 1 ↔ (j : ℕ) < c := by omega
    rw [update_of_ne hj]
    simp only [mix, hiff]

omit [Fintype X] [DecidableEq X] in
/-- **The canonical path leaves `S`**: from `x ∈ S` to `z ∉ S`, some step of the canonical path
goes from a point of `S` to a point outside `S`. -/
private theorem exists_mix_mem_update_not_mem {S : Finset (Fin n → X)} {x z : Fin n → X}
    (hx : x ∈ S) (hz : z ∉ S) :
    ∃ c : Fin n, mix c x z ∈ S ∧ update (mix c x z) c (z c) ∉ S := by
  by_contra! h
  have hall (k : ℕ) (hk : k ≤ n) : mix k x z ∈ S := by
    induction k with
    | zero => rwa [mix_zero]
    | succ k ih =>
      have hc := h ⟨k, hk⟩ (ih (by omega))
      rwa [← mix_succ] at hc
  exact hz (mix_self x z ▸ hall n le_rfl)

/-- Swapping the first `c` coordinates of two points. -/
private def swapPrefix (c : ℕ) (p : (Fin n → X) × (Fin n → X)) : (Fin n → X) × (Fin n → X) :=
  (mix c p.1 p.2, mix c p.2 p.1)

omit [Fintype X] [DecidableEq X] in
private theorem swapPrefix_involutive (c : ℕ) :
    Involutive (swapPrefix (n := n) (X := X) c) := by
  intro p
  ext j <;> simp only [swapPrefix, mix] <;> split_ifs <;> rfl

/-- The number of directed edges in direction `c` from a point of `S` to a point outside `S`. -/
private theorem card_filter_swap (S : Finset (Fin n → X)) (c : Fin n) :
    #{p : (Fin n → X) × (Fin n → X) | mix c p.1 p.2 ∈ S ∧ update (mix c p.1 p.2) c (p.2 c) ∉ S} =
      #{p : (Fin n → X) × (Fin n → X) | p.1 ∈ S ∧ update p.1 c (p.2 c) ∉ S} := by
  have hc (p : (Fin n → X) × (Fin n → X)) : (swapPrefix c p).2 c = p.2 c := by
    simp [swapPrefix, mix]
  simp only [card_filter]
  refine Fintype.sum_equiv ((swapPrefix_involutive (n := n) (X := X) c).toPerm _) _ _
    fun p => ?_
  simp only [Involutive.coe_toPerm, hc]
  rfl

/-- Changing the `c`-th coordinate of a point of `S` to that of an arbitrary point: the count
is `|X| ^ (n - 1)` times the count of directed edges from `S` to its complement in direction
`c`. -/
private theorem card_filter_update_apply (S : Finset (Fin n → X)) (c : Fin n) :
    #{p : (Fin n → X) × (Fin n → X) | p.1 ∈ S ∧ update p.1 c (p.2 c) ∉ S} =
      Fintype.card X ^ (n - 1) * #{q : (Fin n → X) × X | q.1 ∈ S ∧ update q.1 c q.2 ∉ S} := by
  have hfib (t : X) : #{w : Fin n → X | w c = t} = Fintype.card X ^ (n - 1) := by
    have := Fintype.card_filter_piFinset_const_eq_of_mem (univ : Finset X) c (mem_univ t)
    simpa [Fintype.piFinset_univ] using this
  simp only [card_filter, Fintype.sum_prod_type]
  rw [mul_sum]
  refine sum_congr rfl fun u _ => ?_
  have : (∑ w : Fin n → X, if u ∈ S ∧ update u c (w c) ∉ S then (1 : ℕ) else 0) =
      ∑ t : X, ∑ w : Fin n → X, if w c = t then (if u ∈ S ∧ update u c t ∉ S then (1 : ℕ) else 0)
        else 0 := by
    rw [sum_comm]
    refine sum_congr rfl fun w _ => ?_
    rw [sum_ite_eq]
    simp
  rw [this, mul_sum]
  refine sum_congr rfl fun t _ => ?_
  rw [← sum_filter, sum_const, smul_eq_mul, hfib, mul_comm]

/-- Each point outside `S` is the endpoint of at most `|X|` directed edges in direction `c` from
`S`. -/
private theorem card_edges_le (S : Finset (Fin n → X)) (c : Fin n) :
    #{q : (Fin n → X) × X | q.1 ∈ S ∧ update q.1 c q.2 ∉ S} ≤
      Fintype.card X * #(lineClosure S \ S) := by
  refine card_le_mul_card_image_of_maps_to (f := fun q => update q.1 c q.2) (fun q hq => ?_) _
    fun y _ => ?_
  · simp only [mem_filter, mem_univ, true_and] at hq
    simp only [mem_sdiff, mem_lineClosure]
    exact ⟨⟨c, q.1 c, by simpa using hq.1⟩, hq.2⟩
  · rw [← card_univ]
    refine card_le_card_of_injOn (fun q => q.1 c) (fun _ _ => mem_univ _) fun q hq q' hq' h => ?_
    simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hq hq'
    have h1 : q.1 = q'.1 := by
      funext j
      by_cases hj : j = c
      · subst hj
        exact h
      · have := congrFun (hq.2.trans hq'.2.symm) j
        simpa [update_of_ne hj] using this
    have h2 : q.2 = q'.2 := by
      have := congrFun (hq.2.trans hq'.2.symm) c
      simpa using this
    exact Prod.ext h1 h2

/-- **Edge counting for the line closure**: `|S| |Sᶜ| ≤ n |X| ^ n |S̄ \ S|`. -/
theorem card_mul_card_compl_le (S : Finset (Fin n → X)) :
    #S * #Sᶜ ≤ n * Fintype.card X ^ n * #(lineClosure S \ S) := by
  calc #S * #Sᶜ = #(S ×ˢ Sᶜ) := (card_product _ _).symm
    _ ≤ #(univ.biUnion fun c : Fin n => ({p : (Fin n → X) × (Fin n → X) |
          mix c p.1 p.2 ∈ S ∧ update (mix c p.1 p.2) c (p.2 c) ∉ S} :
            Finset ((Fin n → X) × (Fin n → X)))) := by
        refine card_le_card fun p hp => ?_
        simp only [mem_product, mem_compl] at hp
        obtain ⟨c, hc⟩ := exists_mix_mem_update_not_mem hp.1 hp.2
        simp only [mem_biUnion, mem_univ, true_and, mem_filter]
        exact ⟨c, hc⟩
    _ ≤ ∑ c : Fin n, #({p : (Fin n → X) × (Fin n → X) |
          mix c p.1 p.2 ∈ S ∧ update (mix c p.1 p.2) c (p.2 c) ∉ S} :
            Finset ((Fin n → X) × (Fin n → X))) := card_biUnion_le
    _ = ∑ c : Fin n, Fintype.card X ^ (n - 1) *
          #{q : (Fin n → X) × X | q.1 ∈ S ∧ update q.1 c q.2 ∉ S} := by
        refine sum_congr rfl fun c _ => ?_
        rw [card_filter_swap, card_filter_update_apply]
    _ ≤ ∑ _c : Fin n, Fintype.card X ^ (n - 1) * (Fintype.card X * #(lineClosure S \ S)) :=
        sum_le_sum fun c _ => Nat.mul_le_mul_left _ (card_edges_le S c)
    _ = n * Fintype.card X ^ n * #(lineClosure S \ S) := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, ← mul_assoc, ← mul_assoc,
          mul_assoc n, ← pow_succ, Nat.sub_add_cancel hn]

/-- **The Expansion Lemma**: if `S` has at most half of the points of `X ^ n`, then
`|S| ≤ 2 n |S̄ \ S|` [Babai, Fortnow, Lund, Lemma 5.8][BabaiFortnowLund1991]. -/
theorem card_le_two_mul_card_lineClosure_sdiff {S : Finset (Fin n → X)}
    (hS : 2 * #S ≤ Fintype.card X ^ n) : #S ≤ 2 * n * #(lineClosure S \ S) := by
  have hcompl : #S + #Sᶜ = Fintype.card X ^ n := by
    rw [card_add_card_compl, Fintype.card_pi, prod_const, card_univ, Fintype.card_fin]
  have h := card_mul_card_compl_le S
  rcases Nat.eq_zero_or_pos (Fintype.card X ^ n) with h0 | hpos
  · omega
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc #S * Fintype.card X ^ n ≤ 2 * (#S * #Sᶜ) := by
        rw [← hcompl]
        nlinarith
    _ ≤ 2 * (n * Fintype.card X ^ n * #(lineClosure S \ S)) := Nat.mul_le_mul_left _ h
    _ = 2 * n * #(lineClosure S \ S) * Fintype.card X ^ n := by ring

/-- **The Expansion Lemma** in the form of [Babai, Fortnow, Lund, Lemma 5.8][BabaiFortnowLund1991]:
in positive dimension, if `|S| ≤ |X| ^ n / 2` then `|S̄| ≥ |S| (1 + 1 / (2 n))`. -/
theorem card_lineClosure_ge {S : Finset (Fin n → X)} (hn : 0 < n)
    (hS : 2 * #S ≤ Fintype.card X ^ n) : (2 * n + 1) * #S ≤ 2 * n * #(lineClosure S) := by
  have h := card_le_two_mul_card_lineClosure_sdiff hS
  have hsplit := card_sdiff_add_card_eq_card (subset_lineClosure (S := S) hn)
  rw [← hsplit]
  nlinarith

end Cslib
