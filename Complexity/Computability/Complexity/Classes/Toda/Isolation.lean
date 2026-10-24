/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.ValiantVazirani.Reduction
public import Complexity.Foundations.Data.BitString.WordCount
public import Complexity.Probability.BitString.AffineHash
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Probabilistic.LinearHash
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Data.List.GetD

/-!
# Isolation with parities

The randomized step of Toda's theorem [Toda][Toda1991], [Arora and Barak, Section 17.4]
[AroraBarak09]: an existential quantifier over the strings `x` of length `M`, applied to a
predicate given by the parities of numbers `c x` of witnesses, becomes, with high probability, the
parity of a single number of witnesses.

The Valiant–Vazirani test (`Cslib.Complexity.Toda.hashesToZero`) reads `k` random parity
equations `A x = b` from a seed and tests whether `x` satisfies them; on bit strings it is the
affine hash `Cslib.BitString.LinearHash.affineHash` of the seed's coefficients and offsets hitting
`0` (`Cslib.Complexity.Toda.hashesToZero_ofFn_iff`). For a nonempty set `S` of strings of length
`M`, with `k = log₂ #S + 2` equations, exactly one element of `S` passes the test for at least
`3 / 16` of the seeds of length `B ≥ (M + 2) (M + 1)`
(`Cslib.Complexity.Toda.three_mul_two_pow_le_card_filter_card_eq_one`), by the Valiant–Vazirani
lemma
`Cslib.Probability.IsPairwiseIndependentHash.three_sixteenths_le_dens_filter_card_filter_eq_one`.

A *trial* sums the numbers `c x` over the strings `x` passing the test of some level `k` with some
seed; its parity is the parity of the number of `x` with `c x` odd that pass the test
(`Finset.odd_sum_iff_odd_card_odd`). The trials are combined by the parity form of a
disjunction: `1 + ∏ⱼ (1 + cⱼ)` is odd exactly when some `cⱼ` is
(`Cslib.BitString.odd_one_add_prod_one_add`). Running `4 (E + 1)` rounds, each with one
trial at every level `k ≤ M + 2`, the combined number is odd exactly when `S` is nonempty, unless
some `c x` has the wrong parity or every round fails to isolate an element of `S`
(`Cslib.Complexity.Toda.two_pow_mul_card_filter_not_odd_iff_le`). With `c x` depending on
inner random bits `r` and wrong for a `2 ^ (-(E + M + 1))` fraction of them for each `x`, the
first failure has probability at most `2 ^ M * 2 ^ (-(E + M + 1))`, the second at most
`(13 / 16) ^ (4 (E + 1)) ≤ 2 ^ (-(E + 1))`, so the result is wrong with probability at most
`2 ^ (-E)`.

## Main definitions

* `Cslib.Complexity.Toda.hashesToZero`: the Valiant–Vazirani test on words.

## Main results

* `Cslib.Complexity.Toda.hashesToZero_ofFn_iff`: the test is the affine hash hitting `0`.
* `Cslib.Complexity.Toda.three_mul_two_pow_le_card_filter_card_eq_one`: isolation with
  probability at least `3 / 16`.
* `Cslib.Complexity.Toda.two_pow_mul_card_filter_not_odd_iff_le`: the isolation step errs with
  probability at most `2 ^ (-E)`.

## References

* [S. Toda, *PP is as hard as the polynomial-time hierarchy*][Toda1991]
* [L. G. Valiant, V. V. Vazirani, *NP is as easy as detecting unique
  solutions*][ValiantVazirani1986]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.Toda

open Finset BitString Turing.MultiTapeTM

/-! ### The Valiant–Vazirani test -/

/-- **The Valiant–Vazirani test**: `w` satisfies the `k` parity equations read from `seed`, whose
coefficients are `k` rows of `w.length` bits and whose offsets are the next `k` bits, missing
bits being `false`. -/
def hashesToZero (k : ℕ) (seed w : List Bool) : Bool :=
  BitString.LinearHash.wordHash k seed w == BitString.listRow k w.length seed

/-- The test is polynomial-time, with all its arguments computed. -/
@[fun_prop]
theorem computableInPolyTime_hashesToZero {γ : Type} {input : γ ↪ List Bool} {k : γ → ℕ}
    {seed w : γ → List Bool}
    (hk : ComputableInPolyTime k input encUnary)
    (hseed : ComputableInPolyTime seed input encBits)
    (hw : ComputableInPolyTime w input encBits) :
    ComputableInPolyTime (fun x => hashesToZero (k x) (seed x) (w x)) input encBool := by
  unfold hashesToZero
  fun_prop

/-- The offsets of the Valiant–Vazirani equations are the row of `k` bits after the `k` rows of
`M` coefficients. -/
private theorem listRow_eq_ofFn_offset (k M : ℕ) (seed : List Bool) :
    BitString.listRow k M seed = List.ofFn (ValiantVazirani.offset k M seed) := by
  rw [BitString.listRow, Nat.mul_comm M k]
  apply List.ext_getElem (by simp)
  intro i hi _
  simp only [List.length_take, List.length_append, List.length_replicate] at hi
  rw [List.getElem_ofFn, List.getElem_take]
  simp only [ValiantVazirani.offset, BitString.ofList]
  by_cases h : i < (seed.drop (k * M)).length
  · rw [List.getElem_append_left h, List.getD_eq_getElem _ _ h]
  · rw [List.getElem_append_right (by omega), List.getElem_replicate,
      List.getD_eq_default _ _ (by omega)]

/-- On a bit string, the test is the affine hash of the coefficients and offsets read from the
seed hitting `0`. -/
theorem hashesToZero_ofFn_iff {k M : ℕ} (seed : List Bool) (x : BitString M) :
    hashesToZero k seed (List.ofFn x) = true ↔
      BitString.LinearHash.affineHash
        (ValiantVazirani.matrix k M seed, ValiantVazirani.offset k M seed) x = 0 := by
  rw [hashesToZero, beq_iff_eq, BitString.LinearHash.wordHash_eq_ofFn, List.length_ofFn,
    listRow_eq_ofFn_offset, List.ofFn_inj, BitString.LinearHash.affineHash]
  constructor
  · intro h
    rw [ValiantVazirani.matrix, ← h]
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    generalize BitString.LinearHash.hash _ x i = a
    revert a
    decide
  · intro h
    funext i
    have := congrFun h i
    simp only [Pi.add_apply, Pi.zero_apply] at this
    rw [ValiantVazirani.matrix] at this
    revert this
    generalize BitString.LinearHash.hash _ x i = a
    generalize ValiantVazirani.offset k M seed i = b
    revert a b
    decide

open ValiantVazirani BitString.LinearHash in
/-- **Isolation with probability `3 / 16`**: for a nonempty set `S` of strings of length `M`, with
`k = log₂ #S + 2` equations, exactly one element of `S` passes the test for at least `3 / 16` of
the seeds of any length `B ≥ k M + k`. -/
theorem three_mul_two_pow_le_card_filter_card_eq_one {M B : ℕ} {S : Finset (BitString M)}
    (hS : S.Nonempty)
    (hB : (Nat.log 2 #S + 2) * M + (Nat.log 2 #S + 2) ≤ B) :
    3 * 2 ^ B ≤ 16 * (univ.filter fun σ : Fin B → Bool =>
      #{x ∈ S | hashesToZero (Nat.log 2 #S + 2) (List.ofFn σ) (List.ofFn x)} = 1).card := by
  classical
  set k := Nat.log 2 #S + 2 with hk
  -- the Valiant–Vazirani lemma for the seeds
  have hY : Fintype.card (BitString k) = 2 ^ k := by simp
  have hlog := Nat.pow_log_le_self 2 hS.card_pos.ne'
  have hlog' := Nat.lt_pow_succ_log_self (b := 2) (by decide) #S
  have hdens :=
    (isPairwiseIndependentHash_affineHash k M).three_sixteenths_le_dens_filter_card_filter_eq_one
    (S := S) 0 (by rw [hY, hk, pow_add]; omega) (by rw [hY, hk, pow_add, pow_succ] at *; omega)
  have hU : 3 * 2 ^ (k * M + k) ≤
      16 * (univ.filter fun p : (Fin k → BitString M) × BitString k =>
        #{x ∈ S | affineHash p x = 0} = 1).card := by
    rw [dens, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin, Fintype.card_fin, le_div_iff₀ (by positivity)] at hdens
    have h : (3 * 2 ^ (k * M + k) : ℚ≥0) ≤ 16 * (univ.filter fun p :
        (Fin k → BitString M) × BitString k => #{x ∈ S | affineHash p x = 0} = 1).card := by
      rw [pow_add, pow_mul', ← mul_assoc]
      have := mul_le_mul_of_nonneg_left hdens (by norm_num : (0 : ℚ≥0) ≤ 16)
      convert this using 1
      push_cast
      ring
    exact_mod_cast h
  -- transfer to the words read by the test
  have hsplit := BitString.card_filter_take_drop (m := B) hB
    (fun w => #{x ∈ S | affineHash (matrix k M w, offset k M w) x = 0} = 1) (fun _ => True)
  simp only [and_true, filter_true, card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, matrix_take, offset_take] at hsplit
  rw [card_filter_seed (fun p => #{x ∈ S | affineHash p x = 0} = 1)] at hsplit
  have hfilter : (univ.filter fun σ : Fin B → Bool =>
      #{x ∈ S | hashesToZero k (List.ofFn σ) (List.ofFn x)} = 1) =
      univ.filter fun σ : Fin B → Bool =>
        #{x ∈ S | affineHash (matrix k M (List.ofFn σ), offset k M (List.ofFn σ)) x = 0} = 1 := by
    simp only [hashesToZero_ofFn_iff]
  rw [hfilter, hsplit]
  have hB' : B = (k * M + k) + (B - (k * M + k)) := by omega
  calc 3 * 2 ^ B = 3 * 2 ^ (k * M + k) * 2 ^ (B - (k * M + k)) := by
        conv_lhs => rw [hB', pow_add]
        ring
    _ ≤ 16 * (univ.filter fun p : (Fin k → BitString M) × BitString k =>
          #{x ∈ S | affineHash p x = 0} = 1).card * 2 ^ (B - (k * M + k)) := by gcongr
    _ = _ := by ring

/-! ### The isolation step -/

/-- `2 ^ (E + 1) * 13 ^ (4 (E + 1)) ≤ 16 ^ (4 (E + 1))`: `4 (E + 1)` rounds failing with
probability at most `13 / 16` each all fail with probability at most `2 ^ (-(E + 1))`. -/
private theorem two_pow_mul_thirteen_pow_le (E : ℕ) :
    2 ^ (E + 1) * 13 ^ (4 * (E + 1)) ≤ 16 ^ (4 * (E + 1)) := by
  rw [pow_mul, pow_mul, ← mul_pow]
  exact Nat.pow_le_pow_left (by norm_num) _

/-- **The isolation step errs with probability at most `2 ^ (-E)`.** Let `c r x` be numbers
whose parity says whether `x ∈ S`, except for at most a `2 ^ (-e')` fraction of the random
strings `r` of length `R`, for each string `x` of length `M`, where `e' ≥ E + M + 1`. Draw seeds
of `B ≥ (M + 2) (M + 1)` bits for `T = 4 (E + 1) (M + 3)` trials, the trial `j` testing at level
`j % (M + 3)`. Then `1 + ∏ⱼ (1 + ∑ c r x)`, the inner sum over the `x` passing trial `j`, is odd
exactly when `S` is nonempty, except for at most a `2 ^ (-E)` fraction of the random strings and
seeds. -/
theorem two_pow_mul_card_filter_not_odd_iff_le {R M E e' B : ℕ}
    (c : (Fin R → Bool) → (Fin M → Bool) → ℕ) (S : Finset (Fin M → Bool))
    (hc : ∀ x, 2 ^ e' * (univ.filter fun r => ¬(Odd (c r x) ↔ x ∈ S)).card ≤ 2 ^ R)
    (he : E + M + 1 ≤ e') (hB : (M + 2) * (M + 1) ≤ B) :
    2 ^ E * (univ.filter fun p : (Fin R → Bool) × (Fin (4 * (E + 1) * (M + 3)) → BitString B) =>
      ¬(Odd (1 + ∏ j : Fin (4 * (E + 1) * (M + 3)), (1 + ∑ x with
        hashesToZero ((j : ℕ) % (M + 3)) (List.ofFn (p.2 j)) (List.ofFn x) = true, c p.1 x)) ↔
        S.Nonempty)).card ≤ 2 ^ R * 2 ^ (4 * (E + 1) * (M + 3) * B) := by
  classical
  set t := 4 * (E + 1)
  set T := t * (M + 3)
  -- the good randomness
  set A := (univ.filter fun r : Fin R → Bool => ∃ x, ¬(Odd (c r x) ↔ x ∈ S)) with hA
  set Iso : Fin T → BitString B → Prop := fun j σ =>
    #{x ∈ S | hashesToZero ((j : ℕ) % (M + 3)) (List.ofFn σ) (List.ofFn x)} = 1 with hIso
  set Bc := (univ.filter fun s : Fin T → BitString B => ∀ j, ¬Iso j (s j)) with hBc
  -- the bad event is covered
  have hcover : (univ.filter fun p : (Fin R → Bool) × (Fin T → BitString B) =>
      ¬(Odd (1 + ∏ j : Fin T, (1 + ∑ x with
        hashesToZero ((j : ℕ) % (M + 3)) (List.ofFn (p.2 j)) (List.ofFn x) = true, c p.1 x)) ↔
        S.Nonempty)) ⊆ (A ×ˢ univ) ∪ (univ ×ˢ Bc).filter fun _ => S.Nonempty := by
    intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    by_contra hnot
    rw [mem_union, not_or] at hnot
    obtain ⟨hA', hB''⟩ := hnot
    have hgood : ∀ x, (Odd (c p.1 x) ↔ x ∈ S) := fun x => by
      by_contra h
      exact hA' (mem_product.2 ⟨by rw [hA, mem_filter]; exact ⟨mem_univ _, x, h⟩, mem_univ _⟩)
    have hiso : S.Nonempty → ∃ j, Iso j (p.2 j) := fun hS => by
      by_contra h
      push Not at h
      exact hB'' (mem_filter.2 ⟨mem_product.2 ⟨mem_univ _, by
        rw [hBc, mem_filter]; exact ⟨mem_univ _, h⟩⟩, hS⟩)
    apply hp
    rw [odd_one_add_prod_one_add]
    have hpar (j : Fin T) : Odd (∑ x with
        hashesToZero ((j : ℕ) % (M + 3)) (List.ofFn (p.2 j)) (List.ofFn x) = true, c p.1 x) ↔
        Odd #{x ∈ S | hashesToZero ((j : ℕ) % (M + 3)) (List.ofFn (p.2 j)) (List.ofFn x)} := by
      rw [Finset.odd_sum_iff_odd_card_odd, Finset.filter_filter]
      congr! 2
      ext x
      simp only [mem_filter, mem_univ, true_and]
      rw [hgood x, and_comm]
    simp only [hpar]
    constructor
    · rintro ⟨j, hj⟩
      obtain ⟨x, hx⟩ := Finset.card_pos.1 hj.pos
      exact ⟨x, (mem_filter.1 hx).1⟩
    · intro hS
      obtain ⟨j, hj⟩ := hiso hS
      exact ⟨j, by rw [hIso] at hj; rw [hj]; exact odd_one⟩
  -- the inner randomness is bad with probability at most `2 ^ (M - e')`
  have hAbound : 2 ^ e' * #A ≤ 2 ^ M * 2 ^ R := two_pow_mul_card_filter_exists_le hc
  -- no isolation in any round has probability at most `(13 / 16) ^ t`
  have hBbound : S.Nonempty → 16 ^ t * #Bc ≤ 13 ^ t * (2 ^ B) ^ T := by
    intro hS
    set k₀ := Nat.log 2 #S + 2 with hk₀
    have hk₀M : k₀ ≤ M + 2 := by
      have hcard : #S ≤ 2 ^ M := (card_le_univ S).trans (by simp)
      have := Nat.log_mono_right (b := 2) hcard
      rw [Nat.log_pow (by decide)] at this
      omega
    have hk₀B : k₀ * M + k₀ ≤ B := by nlinarith
    set Fbad := (univ.filter fun σ : Fin B → Bool =>
      ¬#{x ∈ S | hashesToZero k₀ (List.ofFn σ) (List.ofFn x)} = 1) with hFbad
    have hgood : 3 * 2 ^ B ≤ 16 * (univ.filter fun σ : Fin B → Bool =>
        #{x ∈ S | hashesToZero k₀ (List.ofFn σ) (List.ofFn x)} = 1).card :=
      three_mul_two_pow_le_card_filter_card_eq_one (B := B) hS hk₀B
    have hsplit := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin B → Bool)))
      (fun σ => #{x ∈ S | hashesToZero k₀ (List.ofFn σ) (List.ofFn x)} = 1)
    simp only [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hsplit
    have hF : 16 * #Fbad ≤ 13 * 2 ^ B := by rw [hFbad]; omega
    -- the rounds use the level `k₀` at the indices `i * (M + 3) + k₀`
    let idx : Fin t → Fin T := fun i => ⟨i * (M + 3) + k₀, by
      have := i.2
      calc i * (M + 3) + k₀ < i * (M + 3) + (M + 3) := by omega
        _ = (i + 1) * (M + 3) := by ring
        _ ≤ t * (M + 3) := Nat.mul_le_mul_right _ this⟩
    have hidx : Function.Injective idx := by
      intro i i' h
      simp only [idx, Fin.mk.injEq] at h
      ext
      have h' : (i : ℕ) * (M + 3) = i' * (M + 3) := by omega
      exact Nat.eq_of_mul_eq_mul_right (by omega) h'
    have hmod (i : Fin t) : ((idx i : Fin T) : ℕ) % (M + 3) = k₀ := by
      simp only [idx]
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    have hsub : Bc ⊆ univ.filter fun s : Fin T → BitString B => ∀ i, s (idx i) ∈ Fbad := by
      intro s hs
      simp only [hBc, hIso, mem_filter, mem_univ, true_and] at hs ⊢
      intro i
      simp only [hFbad, mem_filter, mem_univ, true_and]
      have := hs (idx i)
      rwa [hmod i] at this
    have hcount := card_filter_forall_apply_mem idx hidx Fbad
    simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool] at hcount
    calc 16 ^ t * #Bc ≤ 16 ^ t * (#Fbad ^ t * (2 ^ B) ^ (T - t)) := by
          rw [← hcount]; exact Nat.mul_le_mul_left _ (card_le_card hsub)
      _ = (16 * #Fbad) ^ t * (2 ^ B) ^ (T - t) := by ring
      _ ≤ (13 * 2 ^ B) ^ t * (2 ^ B) ^ (T - t) := by gcongr
      _ = 13 ^ t * (2 ^ B) ^ (t + (T - t)) := by ring
      _ = 13 ^ t * (2 ^ B) ^ T := by
          congr 2
          have : t ≤ T := Nat.le_mul_of_pos_right t (by omega)
          omega
  -- combining
  have hT : (2 : ℕ) ^ (4 * (E + 1) * (M + 3) * B) = (2 ^ B) ^ T := by
    rw [← pow_mul, Nat.mul_comm B]
  have hcardS : Fintype.card (Fin T → BitString B) = (2 ^ B) ^ T := by simp
  have hE : 2 ^ (E + 1) * #A ≤ 2 ^ R := by
    have h1 : 2 ^ (E + M + 1) * #A ≤ 2 ^ M * 2 ^ R :=
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) he)).trans hAbound
    rw [show E + M + 1 = M + (E + 1) by ring, pow_add, mul_assoc] at h1
    exact Nat.le_of_mul_le_mul_left h1 (by positivity)
  refine (Nat.mul_le_mul_left _ (card_le_card hcover)).trans ?_
  refine (Nat.mul_le_mul_left _ (card_union_le _ _)).trans ?_
  rw [card_product, card_univ, hcardS, hT]
  by_cases hS : S.Nonempty
  · rw [Finset.filter_true_of_mem fun _ _ => hS, card_product, card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin]
    have hB' := hBbound hS
    have h13 := two_pow_mul_thirteen_pow_le E
    have hE' : 2 ^ (E + 1) * #Bc ≤ (2 ^ B) ^ T := by
      have h2 : 16 ^ t * (2 ^ (E + 1) * #Bc) ≤ 16 ^ t * (2 ^ B) ^ T :=
        calc 16 ^ t * (2 ^ (E + 1) * #Bc) = 2 ^ (E + 1) * (16 ^ t * #Bc) := by ring
          _ ≤ 2 ^ (E + 1) * (13 ^ t * (2 ^ B) ^ T) := Nat.mul_le_mul_left _ hB'
          _ = (2 ^ (E + 1) * 13 ^ t) * (2 ^ B) ^ T := by ring
          _ ≤ 16 ^ t * (2 ^ B) ^ T := Nat.mul_le_mul_right _ h13
      exact Nat.le_of_mul_le_mul_left h2 (by positivity)
    have h2E : 2 ^ (E + 1) = 2 * 2 ^ E := by ring
    rw [h2E] at hE hE'
    have h1 := Nat.mul_le_mul_right ((2 ^ B) ^ T) hE
    have h2 := Nat.mul_le_mul_left (2 ^ R) hE'
    nlinarith
  · rw [Finset.filter_false_of_mem fun _ _ => hS, card_empty, Nat.add_zero]
    have h2E : 2 ^ (E + 1) = 2 * 2 ^ E := by ring
    rw [h2E] at hE
    have h1 := Nat.mul_le_mul_right ((2 ^ B) ^ T) hE
    nlinarith [Nat.zero_le (2 ^ E * #A * (2 ^ B) ^ T)]

end Cslib.Complexity.Toda
