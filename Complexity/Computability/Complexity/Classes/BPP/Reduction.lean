/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BPP
public import Complexity.Computability.Complexity.Reduction
public import Complexity.Foundations.Data.BitString.WordCount
import Complexity.Computability.Complexity.Classes.SharpP.Combinators
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# BPP is closed under polynomial-time reductions

If `A` reduces to `B` in polynomial time and `B` is in `BPP`, then so is `A`
(`Cslib.Complexity.PolyTimeReducible.mem_BPP`): run the decider of `B` on the reduced instance.
The random string for an instance `a` of `A` must have a length fixed by the length of `a` alone,
so it is taken polynomially long enough for the reduced instance, and the decider reads only the
prefix it expects (`Cslib.Complexity.andVerifier` with a trivial second part). Every prefix is
extended by the same number of strings, so the fractions of right answers are unchanged
(`Cslib.Complexity.acceptCount_andVerifier_true`), as for `PP`
(`Cslib.Complexity.PolyTimeReducible.mem_PP`).

## Main results

* `Cslib.Complexity.PolyTimeReducible.mem_BPP`: `BPP` is closed under polynomial-time reductions.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}

/-- **`BPP` is closed under polynomial-time reductions.** The decider of `A` runs the decider of
`B` on the reduced instance and on the prefix of the random string that this decider expects. -/
theorem PolyTimeReducible.mem_BPP (h : PolyTimeReducible enc encB A B) (hB : B ∈ BPP encB) :
    A ∈ BPP enc := by
  rw [Complexity.mem_BPP] at hB ⊢
  obtain ⟨g, hg, hAB⟩ := h
  obtain ⟨q, W, hW, hWB⟩ := hB
  have hg := hg.tidy
  have hW := hW.tidy
  have hlen : ComputableTidilyInPolyTime (fun a => q.eval (encB (g a)).length) enc encUnary :=
    (ComputableTidilyInPolyTime.unary_eval q).comp
      ((ComputableTidilyInPolyTime.encoding_length encB).comp hg)
  obtain ⟨p, hle⟩ := hlen.polyBounded.exists_polynomial
  refine ⟨p,
    andVerifier (fun a => q.eval (encB (g a)).length) (fun x => W (g x.1, x.2)) fun _ => true,
    .of_tidy (computableTidilyInPolyTime_andVerifier hlen
      (hW.comp ((hg.comp (.fst enc encBits)).prod (.snd enc encBits))) (.const true)),
    fun a => ?_⟩
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (hle a)
  rw [hj]
  set k := q.eval (encB (g a)).length
  set V := andVerifier (fun a => q.eval (encB (g a)).length) (fun x => W (g x.1, x.2))
    fun _ => true
  -- Accepting strings of `V` are the accepting prefixes of `W`, each extended `2 ^ j` ways.
  have hacc : acceptCount V a (k + j) = acceptCount W (g a) k * 2 ^ j :=
    acceptCount_andVerifier_true _ _ a j
  have hsumA := acceptCount_add_card_filter_eq_false (V := V) (a := a) (n := k + j)
  have hsumB := acceptCount_add_card_filter_eq_false (V := W) (a := g a) (n := k)
  rw [pow_add] at hsumA
  have hrej : (Finset.univ.filter fun r : Fin (k + j) → Bool => V (a, List.ofFn r) = false).card =
      (Finset.univ.filter fun r : Fin k → Bool => W (g a, List.ofFn r) = false).card * 2 ^ j := by
    have := congrArg (· * 2 ^ j) hsumB
    simp only [Nat.add_mul] at this
    omega
  change (a ∈ A → 2 * 2 ^ (k + j) ≤ 3 * acceptCount V a (k + j)) ∧
    (a ∉ A → 2 * 2 ^ (k + j) ≤
      3 * (Finset.univ.filter fun r : Fin (k + j) → Bool => V (a, List.ofFn r) = false).card)
  rw [hacc, hrej, pow_add]
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · have h : 2 * 2 ^ k ≤ 3 * acceptCount W (g a) k := (hWB (g a)).1 ((hAB a).1 ha)
    have := Nat.mul_le_mul_right (2 ^ j) h
    linarith
  · have := Nat.mul_le_mul_right (2 ^ j) ((hWB (g a)).2 fun hgB => ha ((hAB a).2 hgB))
    linarith

end Cslib.Complexity
