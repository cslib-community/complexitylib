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
import Complexity.Foundations.Combinatorics.FiniteCover.Basic
import Complexity.Foundations.Data.BitString.List

/-!
# `AM ⊆ NP/poly`

Every problem with an Arthur–Merlin verifier is in `NP` with polynomial advice
(`Cslib.Complexity.AM_subset_NPPoly`), a theorem usually attributed to
[Babai and Moran][BabaiMoran1988]. The proof is the fixed-coins argument of
[Adleman][Adleman1978] (for `RP ⊆ P/poly`), applied to Arthur's coins:

* Reduce the error of the verifier to `2 ^ (-(n + 1))`, where `n` is the length of the encoded
  instance (`Cslib.Complexity.mem_AM_iff_forall_errorExponent`).
* At most `2 ^ n` instances have encodings of length `n`, and on each of them fewer than a
  `2 ^ (-(n + 1))` fraction of the random strings are bad. By the union bound some random string
  `r n` is good for all of them (`Cslib.Complexity.exists_coins_forall_iff_exists`, through
  `Cslib.exists_cover_of_scaled_card_lt` with one test): an instance
  of length `n` is a member exactly when Merlin has an accepted reply to `r n`.
* The advice for length `n` is `r n`, of `p(n)` bits. Merlin's reply is then an `NP` certificate
  for the pair of the advice and the instance (`Cslib.Complexity.mem_NP_setOf_exists_append`).

Hence `MA ⊆ NP/poly` (`Cslib.Complexity.MA_subset_NPPoly`). Problems in `AM` include graph
non-isomorphism, so graph isomorphism is in `coNP/poly`
(`Cslib.Complexity.GraphNonIsomorphism.GraphIsomorphism_mem_coNPPoly`, proved in
`Complexity.Computability.Complexity.Classes.ArthurMerlin.GraphNonIsomorphism`).

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

/-- **Fixed coins for one length**, the argument of [Adleman][Adleman1978] for `RP ⊆ P/poly`.
If the Arthur–Merlin verifier `V` has error at most `2 ^ (-(n + 1))` on instances whose
encodings have length `n`, then one random string `r` decides all of them: such an instance is
a member exactly when Merlin has a reply to `r` that `V` accepts. -/
theorem exists_coins_forall_iff_exists {e p q : Polynomial ℕ} {V : α × List Bool → Bool}
    (hV : IsArthurMerlinVerifierWithErrorExponent enc e p q V A) (n : ℕ)
    (he : n + 1 ≤ e.eval n) :
    ∃ r : Fin (p.eval n) → Bool, ∀ a, (enc a).length = n →
      (a ∈ A ↔ ∃ y : Fin (q.eval n) → Bool, V (a, List.ofFn r ++ List.ofFn y) = true) := by
  classical
  -- A random string `r` is good for the word `x` if it decides every instance encoded by `x`.
  let good : (Fin (p.eval n) → Bool) → (Fin n → Bool) → Prop := fun r x => ∀ a,
    enc a = List.ofFn x →
      (a ∈ A ↔ ∃ y : Fin (q.eval n) → Bool, V (a, List.ofFn r ++ List.ofFn y) = true)
  have hloc (x : Fin n → Bool) : 2 ^ (n + 1) *
      Fintype.card {r : Fin (p.eval n) → Bool // ¬ good r x} ≤
        1 * Fintype.card (Fin (p.eval n) → Bool) := by
    rw [one_mul, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_subtype]
    by_cases hx : ∃ a, enc a = List.ofFn x
    · obtain ⟨a, ha⟩ := hx
      have hlen : (enc a).length = n := by rw [ha, List.length_ofFn]
      have hfilter : (univ.filter fun r => ¬ good r x) = univ.filter fun r :
          Fin (p.eval n) → Bool =>
          ¬ (a ∈ A ↔ ∃ y : Fin (q.eval n) → Bool, V (a, List.ofFn r ++ List.ofFn y) = true) := by
        refine filter_congr fun r _ => ⟨fun h h' => h fun b hb => ?_, fun h h' => h (h' a ha)⟩
        rwa [enc.injective (hb.trans ha.symm)]
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
    · rw [filter_false_of_mem fun r _ h => h fun a ha => (hx ⟨a, ha⟩).elim, card_empty,
        mul_zero]
      exact Nat.zero_le _
  obtain ⟨r, hr⟩ := exists_cover_of_scaled_card_lt good 1 (2 ^ (n + 1)) 1 hloc
    (by simp [pow_succ])
  refine ⟨r 0, fun a ha => ?_⟩
  obtain ⟨i, hi⟩ := hr fun i => (enc a)[i.val]'(ha ▸ i.isLt)
  rw [Subsingleton.elim i 0] at hi
  exact hi a (by subst ha; exact List.ofFn_getElem.symm)

/-- **`AM ⊆ NP/poly`**, usually attributed to [Babai and Moran][BabaiMoran1988], by the
fixed-coins argument of [Adleman][Adleman1978] (for `RP ⊆ P/poly`): with the error of an
Arthur–Merlin verifier reduced to `2 ^ (-(n + 1))`, one random string of `p(n)` bits serves
every instance of length `n` as advice, and Merlin's reply is the `NP` certificate. -/
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
