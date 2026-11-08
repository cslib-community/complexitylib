/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.Classes.ArthurMerlin.Amplification
public import Complexity.Computability.Complexity.Classes.NP.Advice

import Complexity.Computability.Complexity.Classes.NP.Witness
import Complexity.Foundations.Data.BitString.List

/-!
# `AM ⊆ NP/poly`

Every problem with an Arthur–Merlin verifier is in `NP` with polynomial advice
(`Cslib.Complexity.AM_subset_NPPoly`), a theorem usually attributed to
[Babai and Moran][BabaiMoran1988]. The proof is the fixed-coins argument of
[Adleman][Adleman1978] for `BPP ⊆ P/poly`, applied to Arthur's coins:

* Reduce the error of the verifier to `2 ^ (-(n + 1))`, where `n` is the length of the encoded
  instance (`Cslib.Complexity.mem_AM_iff_forall_errorExponent`).
* At most `2 ^ n` instances have encodings of length `n`, and on each of them fewer than a
  `2 ^ (-(n + 1))` fraction of the random strings are bad. By the union bound some random string
  `r n` is good for all of them (`Cslib.Complexity.exists_coins_forall_iff_exists`): an instance
  of length `n` is a member exactly when Merlin has an accepted reply to `r n`.
* The advice for length `n` is `r n`, of `p(n)` bits. Merlin's reply is then an `NP` certificate
  for the pair of the advice and the instance (`Cslib.Complexity.mem_NP_setOf_exists_append`).

Hence `MA ⊆ NP/poly` (`Cslib.Complexity.MA_subset_NPPoly`). Problems in `AM` include graph
non-isomorphism, so graph isomorphism is in `coNP/poly`
(`Cslib.Complexity.GraphNonIsomorphism.GraphIsomorphism_mem_coNPPoly`).

## Main results

* `Cslib.Complexity.exists_coins_forall_iff_exists`: one random string for every instance of a
  given length.
* `Cslib.Complexity.AM_subset_NPPoly`: **`AM ⊆ NP/poly`**.
* `Cslib.Complexity.MA_subset_NPPoly`: `MA ⊆ NP/poly`.

## References

* [L. Babai, S. Moran, *Arthur–Merlin games: a randomized proof system, and a hierarchy of
  complexity classes*][BabaiMoran1988]
* [L. Adleman, *Two theorems on random polynomial time*][Adleman1978]
-/

public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- **Fixed coins for one length** [Adleman][Adleman1978]. If the Arthur–Merlin verifier `V` has
error at most `2 ^ (-(n + 1))` on instances whose encodings have length `n`, then one random
string `r` decides all of them: such an instance is a member exactly when Merlin has a reply
to `r` that `V` accepts. -/
theorem exists_coins_forall_iff_exists {e p q : Polynomial ℕ} {V : α × List Bool → Bool}
    (hV : IsArthurMerlinVerifierWithErrorExponent enc e p q V A) (n : ℕ)
    (he : n + 1 ≤ e.eval n) :
    ∃ r : Fin (p.eval n) → Bool, ∀ a, (enc a).length = n →
      (a ∈ A ↔ ∃ y : Fin (q.eval n) → Bool, V (a, List.ofFn r ++ List.ofFn y) = true) := by
  classical
  -- The random strings that are bad for the instance encoded by the word `x`, if any.
  let bad : (Fin n → Bool) → Finset (Fin (p.eval n) → Bool) := fun x =>
    univ.filter fun r => ∃ a, enc a = List.ofFn x ∧
      ¬ (a ∈ A ↔ ∃ y : Fin (q.eval n) → Bool, V (a, List.ofFn r ++ List.ofFn y) = true)
  have hbad (x : Fin n → Bool) : 2 ^ (n + 1) * (bad x).card ≤ 2 ^ p.eval n := by
    by_cases hx : ∃ a, enc a = List.ofFn x
    · obtain ⟨a, ha⟩ := hx
      have hlen : (enc a).length = n := by rw [ha, List.length_ofFn]
      have hfilter : bad x = univ.filter fun r : Fin (p.eval n) → Bool =>
          ¬ (a ∈ A ↔ ∃ y : Fin (q.eval n) → Bool, V (a, List.ofFn r ++ List.ofFn y) = true) := by
        refine filter_congr fun r _ => ⟨?_, fun h => ⟨a, ha, h⟩⟩
        rintro ⟨b, hb, h⟩
        rwa [enc.injective (hb.trans ha.symm)] at h
      rw [hfilter]
      have h := hV a
      rw [hlen] at h
      refine le_trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right two_pos he)) ?_
      by_cases haA : a ∈ A
      · refine le_trans (Nat.mul_le_mul_left _ (card_le_card fun r hr => ?_)) (h.1 haA)
        simp only [mem_filter, mem_univ, true_and, iff_true_left haA, not_exists,
          Bool.not_eq_true] at hr ⊢
        exact hr
      · refine le_trans (Nat.mul_le_mul_left _ (card_le_card fun r hr => ?_)) (h.2 haA)
        simp only [mem_filter, mem_univ, true_and, iff_false_left haA, not_not] at hr ⊢
        exact hr
    · have : bad x = ∅ := filter_false_of_mem fun r _ ⟨a, ha, _⟩ => hx ⟨a, ha⟩
      rw [this, card_empty, mul_zero]
      exact Nat.zero_le _
  have hsum : (univ.biUnion bad).card < (univ : Finset (Fin (p.eval n) → Bool)).card := by
    rw [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    have h1 := card_biUnion_le (s := (univ : Finset (Fin n → Bool))) (t := bad)
    have h2 : 2 ^ (n + 1) * ∑ x : Fin n → Bool, (bad x).card ≤ 2 ^ n * 2 ^ p.eval n := by
      rw [mul_sum]
      calc ∑ x : Fin n → Bool, 2 ^ (n + 1) * (bad x).card
          ≤ ∑ _x : Fin n → Bool, 2 ^ p.eval n := sum_le_sum fun x _ => hbad x
        _ = 2 ^ n * 2 ^ p.eval n := by
          rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
            smul_eq_mul]
    have h3 : 0 < 2 ^ p.eval n := Nat.two_pow_pos _
    rw [pow_succ, mul_assoc] at h2
    have h4 := Nat.le_of_mul_le_mul_left h2 (Nat.two_pow_pos n)
    omega
  obtain ⟨r, -, hr⟩ := exists_mem_notMem_of_card_lt_card hsum
  refine ⟨r, fun a ha => ?_⟩
  by_contra h
  refine hr (mem_biUnion.2 ⟨fun i => (enc a)[i.val]'(ha ▸ i.isLt), mem_univ _, ?_⟩)
  refine mem_filter.2 ⟨mem_univ _, a, ?_, h⟩
  subst ha
  exact List.ofFn_getElem.symm

/-- **`AM ⊆ NP/poly`** [Babai and Moran][BabaiMoran1988], by the fixed-coins argument of
[Adleman][Adleman1978]: with the error of an Arthur–Merlin verifier reduced to `2 ^ (-(n + 1))`,
one random string of `p(n)` bits serves every instance of length `n` as advice, and Merlin's
reply is the `NP` certificate. -/
theorem AM_subset_NPPoly : AM enc ⊆ NPPoly enc := by
  classical
  intro A hA
  obtain ⟨p, q, V, hVc, hV⟩ := mem_AM_iff_forall_errorExponent.1 hA (Polynomial.X + 1)
  choose r hr using fun n => exists_coins_forall_iff_exists hV n (by simp)
  refine ⟨fun n => List.ofFn (r n), ?_, (fun y : List Bool × α => (y.2, y.1)) ⁻¹'
    {y : α × List Bool | ∃ v : List Bool, v.length = q.eval (enc y.1).length ∧
      V (y.1, y.2 ++ v) = true}, ?_, fun a => ?_⟩
  · simpa using PolynomiallyBounded.polynomial_eval p
  · exact PolyTimeReducible.mem_NP ⟨fun y => (y.2, y.1), by fun_prop, fun _ => Iff.rfl⟩
      (mem_NP_setOf_exists_append hVc q)
  · simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [hr _ a rfl]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨List.ofFn y, List.length_ofFn, hy⟩
    · rintro ⟨v, hv, hy⟩
      exact ⟨BitString.ofList _ v, by rwa [BitString.ofFn_ofList hv]⟩

/-- **`MA ⊆ NP/poly`**, through `MA ⊆ AM`. -/
theorem MA_subset_NPPoly : MA enc ⊆ NPPoly enc := MA_subset_AM.trans AM_subset_NPPoly

end Cslib.Complexity
