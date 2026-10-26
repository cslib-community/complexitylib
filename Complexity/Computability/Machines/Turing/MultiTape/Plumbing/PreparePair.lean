/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Encoding
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes
import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape
import Cslib.Foundations.Data.Fin.Tuple
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Tactic.Linarith

/-!
# Preparing both components of an encoded pair

The two certified pair projections write their outputs to separate work tapes. Both output
heads finish at zero, every scratch tape is cleared, and the input head is restored. The
preparation cost includes both computations and both rewinds.

## Main results

* `Turing.MultiTapeTM.PairEncoding.exists_prepare`: one finite machine prepares both words in
  linear time and space, uniformly over all encoded pairs.

## References

This uses Christian Reitwiessner's `PairEncoding` interface and output-to-word compiler.
-/

@[expose] public section

namespace Turing.MultiTapeTM.PairEncoding

universe u

private def firstTapes (k l : ℕ) : Fin (k + 1) ↪ Fin (k + l + 2) :=
  Fin.Embedding.snoc ((Fin.castAddEmb l).trans (Fin.castAddEmb 2))
    (a := Fin.natAdd (k + l) 0) (by
      rintro ⟨i, h⟩
      have : (i : ℕ) = k + l := congrArg Fin.val h
      lia)

private def secondTapes (k l : ℕ) : Fin (l + 1) ↪ Fin (k + l + 2) :=
  Fin.Embedding.snoc ((Fin.natAddEmb k).trans (Fin.castAddEmb 2))
    (a := Fin.natAdd (k + l) 1) (by
      rintro ⟨i, h⟩
      have : k + (i : ℕ) = k + l + 1 := congrArg Fin.val h
      lia)

private lemma secondTapes_ne_first_last (k l : ℕ) (j : Fin (l + 1)) :
    secondTapes k l j ≠ firstTapes k l (Fin.last k) := by
  induction j using Fin.lastCases <;>
    simp [firstTapes, secondTapes, Fin.castAdd_ne_natAdd]

/-- Prepare the two encoded components on the last two work tapes, clearing all scratch tapes
and restoring all heads. The machine and its linear bound are independent of the pair. -/
theorem exists_prepare {α β : Type u} (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool)
    (enc : α × β ↪ List Bool) [PairEncoding enc₁ enc₂ enc] :
    ∃ (r : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapeTM (r + 2) Bool State)
      (c : ℕ), ∀ p : α × β,
      TransformsTapes machine (fun input ws => input = enc p ∧ ws = fun _ => [])
        (fun _ _ ws' emitted =>
          ws' = Fin.append (fun _ : Fin r => []) ![enc₁ p.1, enc₂ p.2] ∧ emitted = [])
        (c * ((enc p).length + 1)) (c * ((enc p).length + 1)) := by
  obtain ⟨c₀, k, Q₀, _, m₀, h₀⟩ :=
    Internal.NormalForm.linear (PairEncoding.fst (enc₁ := enc₁) (enc₂ := enc₂) (enc := enc))
  obtain ⟨c₁, l, Q₁, _, m₁, h₁⟩ :=
    Internal.NormalForm.linear (PairEncoding.snd (enc₁ := enc₁) (enc₂ := enc₂) (enc := enc))
  refine ⟨k + l, (Q₀ ⊕ RewindWorkState) ⊕ (Q₁ ⊕ RewindWorkState), inferInstance,
    (m₀.outputToWord.extendTapes (firstTapes k l)).seq
      (m₁.outputToWord.extendTapes (secondTapes k l)),
    3 * (c₀ + c₁) + 3 * (k + l) + 12, fun p => ?_⟩
  have hfirst := ((h₀ p).outputToWord_extendTapes (firstTapes k l)).imp
    (P' := fun input ws => input = enc p ∧ ws = fun _ => [])
    (fun _ _ h => ⟨h.1, fun _ => congrFun h.2 _⟩)
    (fun _ _ _ _ _ h => h) le_rfl le_rfl
  have hsecond := (h₁ p).outputToWord_extendTapes (secondTapes k l)
  have hseq := transformsTapes_seq hfirst hsecond (by
    rintro input ws ws' emitted ⟨hin, rfl⟩ ⟨rfl, rfl⟩
    exact ⟨hin, fun j => Function.update_of_ne (secondTapes_ne_first_last k l j) _ _⟩)
  refine hseq.imp (fun _ _ h => h) ?_ ?_ ?_
  · rintro _ _ _ _ ⟨_, rfl⟩ ⟨_, _, _, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩
    refine ⟨?_, rfl⟩
    funext i
    cases i using Fin.addCases with
    | left i => simp [firstTapes, secondTapes, Fin.Embedding.snoc_last,
        Fin.castAdd_ne_natAdd]
    | right i =>
      match i with
      | 0 | 1 => simp [firstTapes, secondTapes, Fin.Embedding.snoc_last, Function.update_apply]
  · have hlen₀ := (h₀ p).length_output_le
    have hlen₁ := (h₁ p).length_output_le
    nlinarith
  · have hlen₀ := (h₀ p).length_output_le
    have hlen₁ := (h₁ p).length_output_le
    nlinarith [Nat.sub_le (k + l + 2) (k + 1), Nat.sub_le (k + l + 2) (l + 1)]

end Turing.MultiTapeTM.PairEncoding
