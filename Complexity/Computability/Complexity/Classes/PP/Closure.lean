/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.NP
public import Complexity.Computability.Complexity.Classes.PP
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Closure properties of `PP`

`PP` contains `NP` [Gill][Gill1977]: on random strings `b :: w`, accept when `b = false` and run the
verifier on `w` when `b = true`, so the majority accepts exactly when some certificate does. `PP` is
closed under complement [Gill][Gill1977]: with two more random bits, accept on a quarter of the
random strings and one more, and on half of them reject what the verifier accepts; the majority
accepts exactly when the verifier accepts at most half of its random strings. Hence also
`coNP ⊆ PP`.

## Main results

* `Cslib.Complexity.NP_subset_PP`, `Cslib.Complexity.coNP_subset_PP`.
* `Cslib.Complexity.compl_mem_PP`, `Cslib.Complexity.PP_eq_preimage_compl_PP`: closure under
  complement.

## References

* [J. Gill, *Computational complexity of probabilistic Turing machines*][Gill1977]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- Counting the words of length `n + 1` by their first bit. -/
private theorem card_filter_ofFn_succ (n : ℕ) (P : List Bool → Prop) [DecidablePred P] :
    (Finset.univ.filter fun r : Fin (n + 1) → Bool => P (List.ofFn r)).card =
      (Finset.univ.filter fun w : Fin n → Bool => P (false :: List.ofFn w)).card +
        (Finset.univ.filter fun w : Fin n → Bool => P (true :: List.ofFn w)).card := by
  simp only [Finset.card_filter]
  rw [← (Fin.consEquiv fun _ : Fin (n + 1) => Bool).sum_comp, Fintype.sum_prod_type,
    Fintype.sum_bool, add_comm]
  simp [List.ofFn_succ, Fin.consEquiv]

/-- **`NP ⊆ PP`** [Gill][Gill1977]: on random strings `b :: w`, accept when `b = false` and run
the verifier on `w` when `b = true`. The majority accepts exactly when the verifier accepts some
certificate. -/
theorem NP_subset_PP : NP enc ⊆ PP enc := by
  rintro A ⟨p, V, hV, hA⟩
  let V' (x : α × List Bool) : Bool := !(x.2.headD false) || V (x.1, x.2.tail)
  have hV' : ComputableTidilyInPolyTime V' (encPair enc encBits) encBool :=
    ComputableTidilyInPolyTime.bool_or.comp
      ((ComputableTidilyInPolyTime.bool_not.comp
        ((ComputableTidilyInPolyTime.headD (encA := encBool) false).comp (.snd _ _))).prod
        (hV.tidy.comp ((ComputableTidilyInPolyTime.fst _ _).prod
          (ComputableTidilyInPolyTime.bitsTail.comp (.snd _ _)))))
  refine ⟨p + 1, V', .of_tidy hV', fun a => ?_⟩
  have hcount (m : ℕ) : acceptCount V' a (m + 1) = 2 ^ m + acceptCount V a m := by
    rw [acceptCount, card_filter_ofFn_succ m fun l => V' (a, l) = true]
    simp [V', acceptCount]
  have heval : (p + 1).eval (enc a).length = p.eval (enc a).length + 1 := by simp
  rw [heval, hcount, hA a, ← acceptCount_pos_iff, pow_succ]
  omega

/-- **`PP` is closed under complement** [Gill][Gill1977]. On random strings `b₁ :: b₂ :: w`,
accept when `b₁ = b₂ = false` and on `b₁ = false, b₂ = true` only for `w` all zeros, and reject
what the verifier accepts on `w` when `b₁ = true`. With `acc` accepted and `rej` rejected strings
of length `m`, this accepts `2 ^ m + 1 + 2 * rej` of the `4 * 2 ^ m` strings, more than half
exactly when `2 * acc ≤ 2 ^ m`. -/
theorem compl_mem_PP (hA : A ∈ PP enc) : Aᶜ ∈ PP enc := by
  rw [mem_PP] at hA ⊢
  obtain ⟨p, V, hV, hA⟩ := hA
  let V' (x : α × List Bool) : Bool :=
    if x.2.headD false then !V (x.1, x.2.tail.tail)
    else !(x.2.tail.headD false) || !(x.2.tail.tail.any fun b => b)
  have hV' : ComputableTidilyInPolyTime V' (encPair enc encBits) encBool := by
    have hw : ComputableTidilyInPolyTime (fun x : α × List Bool => x.2.tail.tail)
        (encPair enc encBits) encBits :=
      ComputableTidilyInPolyTime.bitsTail.comp
        (ComputableTidilyInPolyTime.bitsTail.comp (.snd _ _))
    exact ComputableTidilyInPolyTime.cond
      ((ComputableTidilyInPolyTime.headD (encA := encBool) false).comp (.snd _ _))
      (ComputableTidilyInPolyTime.bool_not.comp
        (hV.comp (.of_tidy ((ComputableTidilyInPolyTime.fst _ _).prod hw))).tidy)
      (ComputableTidilyInPolyTime.bool_or.comp
        ((ComputableTidilyInPolyTime.bool_not.comp
          ((ComputableTidilyInPolyTime.headD (encA := encBool) false).comp
            (ComputableTidilyInPolyTime.bitsTail.comp (.snd _ _)))).prod
          (ComputableTidilyInPolyTime.bool_not.comp
            (ComputableTidilyInPolyTime.bitsAnyWithInput (test := fun _ b => b) hw
              (.snd _ _)))))
  refine ⟨p + 2, V', (.of_tidy hV'), fun a => ?_⟩
  -- exactly one word of length `m` is all zeros
  have hzero (m : ℕ) : (Finset.univ.filter fun w : Fin m → Bool =>
      ((List.ofFn w).any fun b => b) = false).card = 1 := by
    refine Finset.card_eq_one.mpr ⟨fun _ => false, Finset.ext fun w => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.any_eq_false, List.mem_ofFn,
      forall_exists_index, forall_apply_eq_imp_iff, Finset.mem_singleton, Bool.not_eq_true]
    exact ⟨fun h => funext h, fun h i => by rw [h]⟩
  have hcount (m : ℕ) : acceptCount V' a (m + 1 + 1) = 2 ^ m + 1 +
      2 * (Finset.univ.filter fun w : Fin m → Bool => V (a, List.ofFn w) = false).card := by
    rw [acceptCount, card_filter_ofFn_succ (m + 1) fun l => V' (a, l) = true,
      card_filter_ofFn_succ m fun l => V' (a, false :: l) = true,
      card_filter_ofFn_succ m fun l => V' (a, true :: l) = true]
    simp only [V', List.headD_cons, List.tail_cons, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.true_or, Bool.not_true, Bool.false_or, Finset.filter_true, Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Bool.not_eq_true', hzero]
    ring
  have heval : (p + 2).eval (enc a).length = p.eval (enc a).length + 1 + 1 := by simp
  have hsum := acceptCount_add_card_filter_eq_false (V := V) (a := a) (n := p.eval (enc a).length)
  rw [heval, hcount, Set.mem_compl_iff, hA a, pow_succ, pow_succ]
  omega

/-- `PP` equals its preimage under complement. -/
theorem PP_eq_preimage_compl_PP (enc : α ↪ List Bool) : PP enc = compl ⁻¹' PP enc := by
  ext A
  refine ⟨compl_mem_PP, fun hA => ?_⟩
  simpa using compl_mem_PP hA

/-- **`coNP ⊆ PP`**: `NP ⊆ PP` and `PP` is closed under complement. -/
theorem coNP_subset_PP : coNP enc ⊆ PP enc := fun _ hA => by
  simpa using compl_mem_PP (NP_subset_PP hA)

end Cslib.Complexity
