/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BPP
public import Complexity.Computability.Complexity.Classes.NP
public import Complexity.Computability.Complexity.Reduction
public import Complexity.Foundations.Data.BitString.List

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Foundations.Data.BitString.WordCount

/-!
# The Arthur–Merlin classes MA and AM

The two-message public-coin proof systems of [Babai][Babai1985] and
[Babai and Moran][BabaiMoran1988] are defined, like `BPP` (`Cslib.Complexity.BPP`), through
deterministic polynomial-time verifiers that read their messages as one string
[Arora and Barak, Section 8.2][AroraBarak09]. Write `n` for the length of the encoded
instance `enc a`.

* In `MA` (`Cslib.Complexity.MA`) Merlin speaks first: a proof `y` of `q(n)` bits, then Arthur
  flips `p(n)` coins `r` and accepts when `V (a, y ++ r) = true`. On a member some proof is
  accepted on at least two thirds of the random strings; on a non-member every proof is rejected
  on at least two thirds of them.
* In `AM` (`Cslib.Complexity.AM`) Arthur speaks first: he sends his `p(n)` random bits `r`,
  Merlin replies with `y` of `q(n)` bits and the verifier accepts when `V (a, r ++ y) = true`. On
  a member, at least two thirds of the random strings admit an accepted reply; on a non-member at
  least two thirds of them admit none.

As in `NP`, the lengths are polynomials of `n`, the messages have exactly these lengths, and the
probabilities are counts of random strings, which are functions `Fin (p n) → Bool`. Merlin's
messages also range over functions `Fin (q n) → Bool`, so that the counted condition of `AM` is
decidable. The characterisations by interactive machines and the round-collapse theorem
`AM[k] = AM` are not proved here.

Both classes contain `NP` (no coins) and `BPP` (no proof), and are closed under polynomial-time
many-one reductions. A reduction changes the lengths the verifier expects, so the new verifier
reads only prefixes of the proof and of the random string of the lengths it needs; the ignored
random bits multiply every count by the same power of two (`Cslib.BitString.card_filter_take`).
Error reduction, `MA ⊆ AM` and `MA ⊆ SBP` are in
`Complexity.Computability.Complexity.Classes.ArthurMerlin.Amplification`, and the placements in
the second level of the polynomial hierarchy in
`Complexity.Computability.Complexity.Classes.ArthurMerlin.PH`.

## Main definitions

* `Cslib.Complexity.IsMerlinArthurVerifier`, `Cslib.Complexity.MA`.
* `Cslib.Complexity.IsArthurMerlinVerifier`, `Cslib.Complexity.AM`.

## Main results

* `Cslib.Complexity.NP_subset_MA`, `Cslib.Complexity.BPP_subset_MA`.
* `Cslib.Complexity.PolyTimeReducible.mem_MA`, `Cslib.Complexity.PolyTimeReducible.mem_AM`:
  closure under polynomial-time many-one reductions.

## References

* [L. Babai, *Trading group theory for randomness*][Babai1985]
* [L. Babai, S. Moran, *Arthur–Merlin games: a randomized proof system, and a hierarchy of
  complexity classes*][BabaiMoran1988]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM

variable {α β : Type} {enc : α ↪ List Bool} {A : Set α}

/-! ### Merlin–Arthur -/

/-- `V` is a Merlin–Arthur verifier for `A`, with proofs of length `q` and random strings of
length `p`, both evaluated at the length of the encoded instance: on a member `a` some proof `y`
makes at least two thirds of the random strings `r` accepted, `V (a, y ++ r) = true`; on a
non-member every proof leaves at least two thirds of the random strings rejected. -/
def IsMerlinArthurVerifier (enc : α ↪ List Bool) (q p : Polynomial ℕ) (V : α × List Bool → Bool)
    (A : Set α) : Prop :=
  ∀ a, (a ∈ A → ∃ y : Fin (q.eval (enc a).length) → Bool, 2 * 2 ^ p.eval (enc a).length ≤
      3 * (univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        V (a, List.ofFn y ++ List.ofFn r) = true).card) ∧
    (a ∉ A → ∀ y : Fin (q.eval (enc a).length) → Bool, 2 * 2 ^ p.eval (enc a).length ≤
      3 * (univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        V (a, List.ofFn y ++ List.ofFn r) = false).card)

/-- The problems with polynomial-time Merlin–Arthur verifiers, with polynomially long proofs and
random strings, with respect to the encoding `enc` of instances [Babai][Babai1985]. -/
def MA (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (q p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧ IsMerlinArthurVerifier enc q p V A}

theorem mem_MA : A ∈ MA enc ↔ ∃ (q p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧
      IsMerlinArthurVerifier enc q p V A :=
  Iff.rfl

/-! ### Arthur–Merlin -/

/-- `V` is an Arthur–Merlin verifier for `A`, with random strings of length `p` and replies of
length `q`, both evaluated at the length of the encoded instance: on a member `a` at least two
thirds of the random strings `r` have a reply `y` with `V (a, r ++ y) = true`; on a non-member at
least two thirds of them have none. -/
def IsArthurMerlinVerifier (enc : α ↪ List Bool) (p q : Polynomial ℕ) (V : α × List Bool → Bool)
    (A : Set α) : Prop :=
  ∀ a, (a ∈ A → 2 * 2 ^ p.eval (enc a).length ≤
      3 * (univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        ∃ y : Fin (q.eval (enc a).length) → Bool, V (a, List.ofFn r ++ List.ofFn y) = true).card) ∧
    (a ∉ A → 2 * 2 ^ p.eval (enc a).length ≤
      3 * (univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        ∀ y : Fin (q.eval (enc a).length) → Bool, V (a, List.ofFn r ++ List.ofFn y) = false).card)

/-- The problems with polynomial-time Arthur–Merlin verifiers, with polynomially long random
strings and replies, with respect to the encoding `enc` of instances
[Babai][Babai1985], [Babai and Moran][BabaiMoran1988]. -/
def AM (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (p q : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧ IsArthurMerlinVerifier enc p q V A}

theorem mem_AM : A ∈ AM enc ↔ ∃ (p q : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧
      IsArthurMerlinVerifier enc p q V A :=
  Iff.rfl

/-! ### `NP` and `BPP` -/

/-- With no random bits, the single random string is accepted or rejected. -/
private theorem two_mul_two_pow_le_card_filter_of_eq_zero {m : ℕ} (hm : m = 0)
    (g : (Fin m → Bool) → Prop) [DecidablePred g] (h : ∀ r, g r) :
    2 * 2 ^ m ≤ 3 * (univ.filter g).card := by
  subst hm
  rw [filter_true_of_mem fun r _ => h r]
  simp

/-- **`NP ⊆ MA`**: an `NP` verifier is a Merlin–Arthur verifier that flips no coins. -/
theorem NP_subset_MA : NP enc ⊆ MA enc := by
  rintro A ⟨p, V, hV, hA⟩
  refine ⟨p, 0, V, hV, fun a => ⟨fun ha => ?_, fun ha y => ?_⟩⟩
  · obtain ⟨w, hw, hVw⟩ := (hA a).1 ha
    refine ⟨BitString.ofList _ w, two_mul_two_pow_le_card_filter_of_eq_zero
      (Polynomial.eval_zero) _ fun r => ?_⟩
    rw [BitString.ofFn_ofList hw,
      List.eq_nil_of_length_eq_zero (by simp : (List.ofFn r).length = 0), List.append_nil, hVw]
  · refine two_mul_two_pow_le_card_filter_of_eq_zero (Polynomial.eval_zero) _ fun r => ?_
    rw [List.eq_nil_of_length_eq_zero (by simp : (List.ofFn r).length = 0), List.append_nil]
    by_contra hVy
    exact ha ((hA a).2 ⟨_, List.length_ofFn, by simpa using hVy⟩)

/-- **`BPP ⊆ MA`**: a bounded-error verifier is a Merlin–Arthur verifier that reads no proof. -/
theorem BPP_subset_MA : BPP enc ⊆ MA enc := by
  rintro A ⟨p, V, hV, hA⟩
  have hnil (a : α) (y : Fin ((0 : Polynomial ℕ).eval (enc a).length) → Bool) :
      List.ofFn y = [] :=
    List.eq_nil_of_length_eq_zero (by simp)
  refine ⟨0, p, V, hV, fun a => ⟨fun ha => ⟨fun _ => false, ?_⟩, fun ha y => ?_⟩⟩
  · simpa only [hnil, List.nil_append] using (hA a).1 ha
  · simpa only [hnil, List.nil_append] using (hA a).2 ha

/-! ### Closure under reductions -/

private theorem two_mul_two_pow_le_card_filter_take {m M : ℕ} (hle : m ≤ M)
    (g : List Bool → Prop) [DecidablePred g]
    (h : 2 * 2 ^ m ≤ 3 * (univ.filter fun r : Fin m → Bool => g (List.ofFn r)).card) :
    2 * 2 ^ M ≤ 3 * (univ.filter fun r : Fin M → Bool => g ((List.ofFn r).take m)).card := by
  rw [BitString.card_filter_take hle g]
  have hpow : 2 ^ M = 2 ^ (M - m) * 2 ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [hpow, mul_left_comm, mul_left_comm 3]
  exact Nat.mul_le_mul_left _ h

private theorem exists_truncated_verifier {encB : β ↪ List Bool} {f : α → β}
    (hf : ComputableTidilyInPolyTime f enc encB) (p₁ p₂ : Polynomial ℕ)
    {V : β × List Bool → Bool}
    (hV : ComputableTidilyInPolyTime V (encPair encB encBits) encBool) :
    ∃ (P₁ P₂ : Polynomial ℕ) (V' : α × List Bool → Bool),
      ComputableTidilyInPolyTime V' (encPair enc encBits) encBool ∧
      (∀ a, p₁.eval (encB (f a)).length ≤ P₁.eval (enc a).length) ∧
      (∀ a, p₂.eval (encB (f a)).length ≤ P₂.eval (enc a).length) ∧
      ∀ (a : α) (u : Fin (P₁.eval (enc a).length) → Bool)
        (v : Fin (P₂.eval (enc a).length) → Bool),
        V' (a, List.ofFn u ++ List.ofFn v) =
          V (f a, (List.ofFn u).take (p₁.eval (encB (f a)).length) ++
            (List.ofFn v).take (p₂.eval (encB (f a)).length)) := by
  have hp₁ : ComputableTidilyInPolyTime (fun a => p₁.eval (encB (f a)).length) enc encUnary :=
    (ComputableTidilyInPolyTime.unary_eval p₁).comp
      ((ComputableTidilyInPolyTime.encoding_length encB).comp hf)
  have hp₂ : ComputableTidilyInPolyTime (fun a => p₂.eval (encB (f a)).length) enc encUnary :=
    (ComputableTidilyInPolyTime.unary_eval p₂).comp
      ((ComputableTidilyInPolyTime.encoding_length encB).comp hf)
  obtain ⟨P₁, hP₁⟩ := hp₁.polyBounded.exists_polynomial
  obtain ⟨P₂, hP₂⟩ := hp₂.polyBounded.exists_polynomial
  have hP₁u : ComputableTidilyInPolyTime (fun a => P₁.eval (enc a).length) enc encUnary :=
    (ComputableTidilyInPolyTime.unary_eval P₁).comp (ComputableTidilyInPolyTime.encoding_length enc)
  refine ⟨P₁, P₂, fun x => V (f x.1, x.2.take (p₁.eval (encB (f x.1)).length) ++
      (x.2.drop (P₁.eval (enc x.1).length)).take (p₂.eval (encB (f x.1)).length)),
    hV.comp ((hf.comp (.fst enc encBits)).prod
      (.bitsAppend (.bitsTakeWithInput (.snd enc encBits) (hp₁.comp (.fst enc encBits)))
        (.bitsTakeWithInput (.bitsDropWithInput (.snd enc encBits) (hP₁u.comp (.fst enc encBits)))
          (hp₂.comp (.fst enc encBits))))),
    hP₁, hP₂, fun a u v => ?_⟩
  dsimp only
  rw [List.take_append_of_le_length (by simpa using hP₁ a), List.drop_left' List.length_ofFn]

/-- **`MA` is closed under polynomial-time reductions.** The verifier runs the verifier of the
target problem on the reduced instance, on the prefix of the proof and the prefix of the random
string of the lengths that it expects. -/
theorem PolyTimeReducible.mem_MA {encB : β ↪ List Bool} {B : Set β}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ MA encB) : A ∈ MA enc := by
  obtain ⟨f, hf, hAB⟩ := h
  obtain ⟨q, p, V, hV, hVB⟩ := hB
  obtain ⟨Q, P, V', hV', hQe, hPe, hsplit⟩ := exists_truncated_verifier hf.tidy q p hV.tidy
  refine ⟨Q, P, V', .of_tidy hV', fun a => ?_⟩
  simp only [hsplit]
  constructor
  · intro ha
    obtain ⟨y, hy⟩ := (hVB (f a)).1 ((hAB a).1 ha)
    refine ⟨BitString.ofList _ (List.ofFn y), ?_⟩
    rw [BitString.take_ofFn_ofList (hQe a)]
    exact two_mul_two_pow_le_card_filter_take (hPe a)
      (fun w => V (f a, List.ofFn y ++ w) = true) hy
  · intro ha y
    have hy := (hVB (f a)).2 (fun hb => ha ((hAB a).2 hb))
      (BitString.ofList _ ((List.ofFn y).take (q.eval (encB (f a)).length)))
    rw [BitString.ofFn_ofList (by simp [hQe a])] at hy
    exact two_mul_two_pow_le_card_filter_take (hPe a)
      (fun w => V (f a, (List.ofFn y).take (q.eval (encB (f a)).length) ++ w) = false) hy

/-- **`AM` is closed under polynomial-time reductions.** The verifier runs the verifier of the
target problem on the reduced instance, on the prefix of the random string and the prefix of the
reply of the lengths that it expects. -/
theorem PolyTimeReducible.mem_AM {encB : β ↪ List Bool} {B : Set β}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ AM encB) : A ∈ AM enc := by
  obtain ⟨f, hf, hAB⟩ := h
  obtain ⟨p, q, V, hV, hVB⟩ := hB
  obtain ⟨P, Q, V', hV', hPe, hQe, hsplit⟩ := exists_truncated_verifier hf.tidy p q hV.tidy
  refine ⟨P, Q, V', .of_tidy hV', fun a => ?_⟩
  have hex (r : Fin (P.eval (enc a).length) → Bool) :
      (∃ y : Fin (Q.eval (enc a).length) → Bool, V (f a, (List.ofFn r).take
          (p.eval (encB (f a)).length) ++ (List.ofFn y).take (q.eval (encB (f a)).length)) = true) ↔
        ∃ y : Fin (q.eval (encB (f a)).length) → Bool,
          V (f a, (List.ofFn r).take (p.eval (encB (f a)).length) ++ List.ofFn y) = true :=
    BitString.exists_take_ofFn_iff (hQe a)
      (g := fun w => V (f a, (List.ofFn r).take (p.eval (encB (f a)).length) ++ w) = true)
  have hall (r : Fin (P.eval (enc a).length) → Bool) :
      (∀ y : Fin (Q.eval (enc a).length) → Bool, V (f a, (List.ofFn r).take
          (p.eval (encB (f a)).length) ++ (List.ofFn y).take (q.eval (encB (f a)).length)) =
            false) ↔
        ∀ y : Fin (q.eval (encB (f a)).length) → Bool,
          V (f a, (List.ofFn r).take (p.eval (encB (f a)).length) ++ List.ofFn y) = false :=
    BitString.forall_take_ofFn_iff (hQe a)
      (g := fun w => V (f a, (List.ofFn r).take (p.eval (encB (f a)).length) ++ w) = false)
  simp only [hsplit, hex, hall]
  exact ⟨fun ha => two_mul_two_pow_le_card_filter_take (hPe a)
      (fun w => ∃ y : Fin (q.eval (encB (f a)).length) → Bool, V (f a, w ++ List.ofFn y) = true)
      ((hVB (f a)).1 ((hAB a).1 ha)),
    fun ha => two_mul_two_pow_le_card_filter_take (hPe a)
      (fun w => ∀ y : Fin (q.eval (encB (f a)).length) → Bool, V (f a, w ++ List.ofFn y) = false)
      ((hVB (f a)).2 fun hb => ha ((hAB a).2 hb))⟩

end Cslib.Complexity
