/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.RP
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Foundations.Data.BitString.WordCount
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The class ZPP

`ZPP` is defined like `RP` (`Cslib.Complexity.RP`), through deterministic polynomial-time machines
that read a random string, but with zero error: `A ∈ ZPP enc` when there are a polynomial `p` and
a function `V : α × List Bool → Option Bool`, computable in polynomial time on inputs
`frame (enc a) ++ r`, such that for every instance `a` an answer `V (a, r) = some b` is always
right, `b = true` exactly when `a ∈ A`, and at least half of the random strings `r` of length
`p (enc a).length` give an answer (`Cslib.Complexity.DecidesWithZeroError`). These are the
algorithms that never err and say "don't know" with probability at most `1 / 2`
[Arora and Barak, Section 7.3][AroraBarak09]; the definition through expected polynomial running
time defines the same class, but expected running time is not modelled here.

`ZPP = RP ∩ coRP` [Arora and Barak, Section 7.3][AroraBarak09]
(`Cslib.Complexity.ZPP_eq_RP_inter_coRP`). Answering `true` only on the answer `some true` decides
a problem in `ZPP` with one-sided error, and so does answering `false` only on `some false` for its
complement. Conversely, for one-sided-error deciders of a problem and of its complement, which
read disjoint parts of the random string, the first accepting gives the answer `some true`, the
second the answer `some false`, and neither errs; on a member the first accepts on at least half of
the random strings, and on a non-member the second does.

## Main definitions

* `Cslib.Complexity.DecidesWithZeroError`: the zero-error condition.
* `Cslib.Complexity.ZPP`.

## Main results

* `Cslib.Complexity.ZPP_subset_RP`, `Cslib.Complexity.ZPP_subset_coRP`.
* `Cslib.Complexity.RP_inter_coRP_subset_ZPP`.
* `Cslib.Complexity.ZPP_eq_RP_inter_coRP`: `ZPP = RP ∩ coRP`.
* `Cslib.Complexity.compl_mem_ZPP`: `ZPP` is closed under complement.

## References

* [J. Gill, *Computational complexity of probabilistic Turing machines*][Gill1977]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type}

/-- `V` decides `A` with zero error, using random strings whose length is `p` evaluated at the
length of the encoded instance: for every instance `a`, an answer `V (a, r) = some b` is right,
`b = true` exactly when `a ∈ A`, and at least half of the random strings give an answer. -/
def DecidesWithZeroError (enc : α ↪ List Bool) (p : Polynomial ℕ)
    (V : α × List Bool → Option Bool) (A : Set α) : Prop :=
  ∀ a, (∀ r : Fin (p.eval (enc a).length) → Bool, ∀ b, V (a, List.ofFn r) = some b →
      (b = true ↔ a ∈ A)) ∧
    2 ^ p.eval (enc a).length ≤
      2 * (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        (V (a, List.ofFn r)).isSome = true).card

/-- The problems decided with zero error by polynomial-time machines reading polynomially long
random strings, with respect to the encoding `enc` of instances [Gill][Gill1977],
[Arora and Barak, Section 7.3][AroraBarak09]. -/
def ZPP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (p : Polynomial ℕ) (V : α × List Bool → Option Bool),
    ComputableInPolyTime V (encPair enc encBits) (encOption encBool) ∧
      DecidesWithZeroError enc p V A}

variable {enc : α ↪ List Bool}

theorem mem_ZPP {A : Set α} : A ∈ ZPP enc ↔ ∃ (p : Polynomial ℕ)
    (V : α × List Bool → Option Bool),
    ComputableInPolyTime V (encPair enc encBits) (encOption encBool) ∧
      DecidesWithZeroError enc p V A :=
  Iff.rfl

namespace DecidesWithZeroError

variable {p : Polynomial ℕ} {V : α × List Bool → Option Bool} {A : Set α}

/-- Accepting exactly on the answer `some true` decides the problem with one-sided error. -/
theorem decidesWithOneSidedError (h : DecidesWithZeroError enc p V A) :
    DecidesWithOneSidedError enc p (fun x => (V x).getD false) A := fun a => by
  obtain ⟨hright, hhalf⟩ := h a
  refine ⟨fun ha => hhalf.trans (Nat.mul_le_mul_left 2 (Finset.card_le_card fun r => ?_)),
    fun ha r => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_iff_exists]
    rintro ⟨b, hb⟩
    rw [hb, Option.getD_some, (hright r b hb).mpr ha]
  · change (V (a, List.ofFn r)).getD false = false
    cases hV : V (a, List.ofFn r) with
    | none => rfl
    | some b =>
      have := (hright r b hV).not.mpr ha
      simpa using this

/-- Negating the answers decides the complement with zero error. -/
theorem compl (h : DecidesWithZeroError enc p V A) :
    DecidesWithZeroError enc p (fun x => (V x).map Bool.not) Aᶜ := fun a => by
  obtain ⟨hright, hhalf⟩ := h a
  refine ⟨fun r b hb => ?_, by simpa only [Option.isSome_map] using hhalf⟩
  obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
  have := hright r b' hb'
  cases b' <;> simp_all

end DecidesWithZeroError

/-- **`ZPP` is closed under complement.** -/
theorem compl_mem_ZPP {A : Set α} (hA : A ∈ ZPP enc) : Aᶜ ∈ ZPP enc := by
  obtain ⟨p, V, hV, h⟩ := mem_ZPP.mp hA
  refine mem_ZPP.mpr ⟨p, fun x => (V x).map Bool.not, ?_, h.compl⟩
  have : ComputableTidilyInPolyTime (fun x => (V x).elim none fun b => some !b)
      (encPair enc encBits) (encOption encBool) :=
    ComputableTidilyInPolyTime.optionElimWithInput hV.tidy (.const none)
      ((ComputableTidilyInPolyTime.optionSome encBool).comp
        (ComputableTidilyInPolyTime.bool_not.comp (.snd _ _)))
  refine .of_tidy ?_
  convert this using 2 with x
  cases V x <;> rfl

/-- **`ZPP ⊆ RP`**: accept exactly on the answer `some true`. -/
theorem ZPP_subset_RP : ZPP enc ⊆ RP enc := fun _ ⟨p, V, hV, h⟩ =>
  ⟨p, fun x => (V x).getD false,
    .of_tidy (ComputableTidilyInPolyTime.optionGetDWithInput hV.tidy (.const false)),
    h.decidesWithOneSidedError⟩

/-- **`ZPP ⊆ coRP`**: the complement is in `ZPP`, hence in `RP`. -/
theorem ZPP_subset_coRP : ZPP enc ⊆ coRP enc := fun _ hA => ZPP_subset_RP (compl_mem_ZPP hA)

/-! ### Splitting random strings -/

/-- Counting the random strings of length `m + k` by their first `m` and last `k` bits. -/
private theorem card_filter_take_drop (m k : ℕ) (P : List Bool → List Bool → Prop)
    [∀ u v, Decidable (P u v)] :
    (Finset.univ.filter fun r : Fin (m + k) → Bool =>
      P ((List.ofFn r).take m) ((List.ofFn r).drop m)).card =
      (Finset.univ.filter fun x : (Fin m → Bool) × (Fin k → Bool) =>
        P (List.ofFn x.1) (List.ofFn x.2)).card := by
  rw [BitString.card_filter_ofFn_add m k P, Finset.card_filter, Fintype.sum_prod_type]
  simp only [Finset.card_filter]

/-- The random strings of length `m + k` whose last `k` bits satisfy `P`. -/
private theorem card_filter_drop (m k : ℕ) (P : List Bool → Prop) [DecidablePred P] :
    (Finset.univ.filter fun r : Fin (m + k) → Bool => P ((List.ofFn r).drop m)).card =
      2 ^ m * (Finset.univ.filter fun v : Fin k → Bool => P (List.ofFn v)).card := by
  rw [card_filter_take_drop m k fun _ v => P v, ← Finset.univ_product_univ,
    Finset.filter_product_right (fun v : Fin k → Bool => P (List.ofFn v)), Finset.card_product]
  simp

/-- A prefix of the right length is a random string of that length. -/
private theorem exists_ofFn_eq_take {m k : ℕ} (r : Fin (m + k) → Bool) :
    ∃ u : Fin m → Bool, List.ofFn u = (List.ofFn r).take m :=
  ⟨_, by rw [List.ofFn_add, List.take_left' List.length_ofFn]⟩

/-- A suffix of the right length is a random string of that length. -/
private theorem exists_ofFn_eq_drop {m k : ℕ} (r : Fin (m + k) → Bool) :
    ∃ v : Fin k → Bool, List.ofFn v = (List.ofFn r).drop m :=
  ⟨_, by rw [List.ofFn_add, List.drop_left' List.length_ofFn]⟩

/-! ### `RP ∩ coRP ⊆ ZPP` -/

/-- **`RP ∩ coRP ⊆ ZPP`**: with one-sided-error deciders `V₁` of `A` and `V₂` of its complement,
reading the first and the last part of the random string, answer `some true` when `V₁` accepts,
`some false` when `V₂` does, and `none` otherwise. -/
theorem RP_inter_coRP_subset_ZPP : RP enc ∩ coRP enc ⊆ ZPP enc := by
  rintro A ⟨hA₁, hA₂⟩
  obtain ⟨p₁, V₁, hV₁, h₁⟩ := mem_RP.mp hA₁
  obtain ⟨p₂, V₂, hV₂, h₂⟩ := mem_RP.mp (mem_coRP.mp hA₂)
  let len (a : α) : ℕ := p₁.eval (enc a).length
  let V (x : α × List Bool) : Option Bool :=
    if V₁ (x.1, x.2.take (len x.1)) then some true
    else if V₂ (x.1, x.2.drop (len x.1)) then some false else none
  have hlen : ComputableTidilyInPolyTime (fun x : α × List Bool => len x.1) (encPair enc encBits)
      encUnary :=
    ((ComputableTidilyInPolyTime.unary_eval p₁).comp
      (ComputableTidilyInPolyTime.encoding_length enc)).comp (.fst _ _)
  have hpoly : ComputableTidilyInPolyTime V (encPair enc encBits) (encOption encBool) :=
    ComputableTidilyInPolyTime.cond
      (hV₁.tidy.comp ((ComputableTidilyInPolyTime.fst _ _).prod
        (ComputableTidilyInPolyTime.bitsTakeWithInput (.snd _ _) hlen)))
      (.const _)
      (ComputableTidilyInPolyTime.cond
        (hV₂.tidy.comp ((ComputableTidilyInPolyTime.fst _ _).prod
          (ComputableTidilyInPolyTime.bitsDropWithInput (.snd _ _) hlen)))
        (.const _) (.const _))
  refine ⟨p₁ + p₂, V, .of_tidy hpoly, fun a => ?_⟩
  have heval : (p₁ + p₂).eval (enc a).length = len a + p₂.eval (enc a).length :=
    Polynomial.eval_add
  rw [heval]
  -- `V₁` never accepts a non-member, and `V₂` never accepts a member
  have hV₁ (ha : a ∉ A) (r : Fin (len a + p₂.eval (enc a).length) → Bool) :
      V₁ (a, (List.ofFn r).take (len a)) = false := by
    obtain ⟨u, hu⟩ := exists_ofFn_eq_take r
    rw [← hu]
    exact (h₁ a).2 ha u
  have hV₂ (ha : a ∈ A) (r : Fin (len a + p₂.eval (enc a).length) → Bool) :
      V₂ (a, (List.ofFn r).drop (len a)) = false := by
    obtain ⟨v, hv⟩ := exists_ofFn_eq_drop r
    rw [← hv]
    exact (h₂ a).2 (not_not.mpr ha) v
  refine ⟨fun r b hb => ?_, ?_⟩
  · simp only [V] at hb
    split_ifs at hb with hacc hrej <;> cases hb
    · simp only [true_iff]
      by_contra ha
      rw [hV₁ ha r] at hacc
      exact Bool.false_ne_true hacc
    · simp only [Bool.false_eq_true, false_iff]
      intro ha
      rw [hV₂ ha r] at hrej
      exact Bool.false_ne_true hrej
  · by_cases ha : a ∈ A
    · -- on a member, `V₁` accepts on at least half of its random strings
      have hcount : (Finset.univ.filter fun r : Fin (len a + p₂.eval (enc a).length) → Bool =>
            V₁ (a, (List.ofFn r).take (len a)) = true).card =
          (Finset.univ.filter fun u : Fin (len a) → Bool => V₁ (a, List.ofFn u) = true).card *
            2 ^ p₂.eval (enc a).length := by
        rw [BitString.card_filter_take (Nat.le_add_right _ _) fun u => V₁ (a, u) = true,
          Nat.add_sub_cancel_left, Nat.mul_comm]
      have hhalf := (h₁ a).1 ha
      calc 2 ^ (len a + p₂.eval (enc a).length)
          = 2 ^ len a * 2 ^ p₂.eval (enc a).length := pow_add _ _ _
        _ ≤ 2 * (Finset.univ.filter fun u : Fin (len a) → Bool =>
              V₁ (a, List.ofFn u) = true).card * 2 ^ p₂.eval (enc a).length :=
            Nat.mul_le_mul_right _ hhalf
        _ = 2 * (Finset.univ.filter fun r : Fin (len a + p₂.eval (enc a).length) → Bool =>
              V₁ (a, (List.ofFn r).take (len a)) = true).card := by
            rw [hcount, Nat.mul_assoc]
        _ ≤ _ := Nat.mul_le_mul_left 2 (Finset.card_le_card fun r => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, V]
            intro hr
            simp [hr])
    · -- on a non-member, `V₂` accepts on at least half of its random strings
      have hcount := card_filter_drop (len a) (p₂.eval (enc a).length)
        fun v => V₂ (a, v) = true
      have hhalf := (h₂ a).1 ha
      calc 2 ^ (len a + p₂.eval (enc a).length)
          = 2 ^ len a * 2 ^ p₂.eval (enc a).length := pow_add _ _ _
        _ ≤ 2 ^ len a * (2 * (Finset.univ.filter fun v : Fin (p₂.eval (enc a).length) → Bool =>
              V₂ (a, List.ofFn v) = true).card) :=
            Nat.mul_le_mul_left _ hhalf
        _ = 2 * (Finset.univ.filter fun r : Fin (len a + p₂.eval (enc a).length) → Bool =>
              V₂ (a, (List.ofFn r).drop (len a)) = true).card := by
            rw [hcount]
            ring
        _ ≤ _ := Nat.mul_le_mul_left 2 (Finset.card_le_card fun r => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, V]
            intro hr
            simp [hr, hV₁ ha r])

/-- **`ZPP = RP ∩ coRP`** [Arora and Barak, Section 7.3][AroraBarak09]. -/
theorem ZPP_eq_RP_inter_coRP : ZPP enc = RP enc ∩ coRP enc :=
  Set.Subset.antisymm (fun _ hA => ⟨ZPP_subset_RP hA, ZPP_subset_coRP hA⟩)
    RP_inter_coRP_subset_ZPP

end Cslib.Complexity
