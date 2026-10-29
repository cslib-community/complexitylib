/-
Copyright (c) 2026 lean-canny contributors, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Binary-counted folds in polynomial space

`Nat.fold` visits the indices below a binary count in increasing order. The step receives the
original input, current index and accumulator. Its native computation may use arbitrary time in
polynomial space. A polynomial bound on all encoded accumulator prefixes suffices for the fold;
the count itself need not be polynomially bounded.

## Main results

* `Turing.MultiTapeTM.ComputableInPolySpace.natFold`: a fold with bounded accumulators.
* `Turing.MultiTapeTM.ComputableInPolySpace.natFold_spec`: a prefix invariant gives both
  the space certificate and the final postcondition.

## References

Adapted from the lean-canny contributors' Computation/TidyBoundedFold.lean at
[`2a50a2ee`](https://github.com/SamuelSchlesinger/lean-canny/blob/2a50a2ee00ae0699cc3f0c2bff5100c4687d2d8e/LeanCanny/Computation/TidyBoundedFold.lean).
The port uses the standard `Nat.fold` and the existing plain space calculus, with no separate
machine or computability predicate.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolySpace

variable {α β : Type} {encIn : α ↪ List Bool} {encState : β ↪ List Bool}

private def advance (step : α → ℕ → β → β) (p : α × ℕ × β) : α × ℕ × β :=
  (p.1, p.2.1 + 1, step p.1 p.2.1 p.2.2)

private theorem iterate_advance (step : α → ℕ → β → β) (x : α) (init : β) (k : ℕ) :
    (advance step)^[k] (x, 0, init) = (x, k, k.fold (fun i _ a => step x i a) init) := by
  induction k with
  | zero => simp only [Function.iterate_zero_apply, Nat.fold_zero]
  | succ k ih => rw [Function.iterate_succ_apply', ih, Nat.fold_succ]; rfl

/-- A fold over a binary count is polynomial-space when its step and seed are polynomial-space
and every accumulator prefix has polynomially bounded encoded length. -/
theorem natFold [Inhabited α] [Inhabited β]
    {step : α → ℕ → β → β} {init : α → β} {count bound : α → ℕ}
    (hcount : ComputableInPolyTime count encIn encNat)
    (hinit : ComputableInPolySpace init encIn encState)
    (hstep : ComputableInPolySpace (fun p : α × ℕ × β => step p.1 p.2.1 p.2.2)
      (encPair encIn (encPair encNat encState)) encState)
    (hbound : PolyBounded (fun x => (encIn x).length) bound)
    (hstates : ∀ x k, k ≤ count x →
      (encState (k.fold (fun i _ a => step x i a) (init x))).length ≤ bound x) :
    ComputableInPolySpace
      (fun x => (count x).fold (fun i _ a => step x i a) (init x)) encIn encState := by
  have hinput := of_polyTime (ComputableInPolyTime.fst encIn (encPair encNat encState))
  have hrest := of_polyTime (ComputableInPolyTime.snd encIn (encPair encNat encState))
  have hindex := (of_polyTime (ComputableInPolyTime.fst encNat encState)).comp hrest
  have hsucc := of_polyTime computableTidilyInPolyTime_succ.computableInPolyTime
  have hadvance : ComputableInPolySpace (advance step)
      (encPair encIn (encPair encNat encState)) (encPair encIn (encPair encNat encState)) :=
    hinput.prod ((hsucc.comp hindex).prod hstep)
  have hstart : ComputableInPolySpace (fun x => (x, 0, init x))
      encIn (encPair encIn (encPair encNat encState)) :=
    id'.prod ((of_polyTime (ComputableInPolyTime.const 0)).prod hinit)
  have hsize : PolyBounded (fun x => (encIn x).length)
      (fun x => 2 * (encIn x).length + 2 * (encNat (count x)).length + bound x + 2) :=
    ((((PolyBounded.const 2).mul PolyBounded.self).add
      ((PolyBounded.const 2).mul hcount.polyBounded_length)).add hbound).add (PolyBounded.const 2)
  have hrun := iterate hcount hstart hadvance hsize (fun x k hk => by
    rw [iterate_advance]
    have hi := ComputableTidilyInO.length_encNat_mono hk
    have ha := hstates x k hk
    simp only [length_encPair]
    omega)
  have hout := (of_polyTime (ComputableInPolyTime.snd encNat encState)).comp
    ((of_polyTime (ComputableInPolyTime.snd encIn (encPair encNat encState))).comp hrun)
  exact hout.congr fun x => by rw [iterate_advance]

/-- A prefix invariant proves the fold's polynomial-space certificate and its final
postcondition. The invariant and bound are proof data; only the count, seed and step run. -/
theorem natFold_spec [Inhabited α] [Inhabited β]
    {step : α → ℕ → β → β} {init : α → β} {count bound : α → ℕ}
    (hcount : ComputableInPolyTime count encIn encNat)
    (hinit : ComputableInPolySpace init encIn encState)
    (hstep : ComputableInPolySpace (fun p : α × ℕ × β => step p.1 p.2.1 p.2.2)
      (encPair encIn (encPair encNat encState)) encState)
    (invariant : α → ℕ → β → Prop)
    (hzero : ∀ x, invariant x 0 (init x))
    (hnext : ∀ x k a, k < count x → invariant x k a → invariant x (k + 1) (step x k a))
    (hbound : PolyBounded (fun x => (encIn x).length) bound)
    (hsize : ∀ x k a, k ≤ count x → invariant x k a → (encState a).length ≤ bound x) :
    ComputableInPolySpace
      (fun x => (count x).fold (fun i _ a => step x i a) (init x)) encIn encState ∧
      ∀ x, invariant x (count x) ((count x).fold (fun i _ a => step x i a) (init x)) := by
  have htrace (x : α) (k : ℕ) (hk : k ≤ count x) :
      invariant x k (k.fold (fun i _ a => step x i a) (init x)) := by
    induction k with
    | zero => simpa only [Nat.fold_zero] using hzero x
    | succ k ih =>
      rw [Nat.fold_succ]
      exact hnext x k _ (by omega) (ih (by omega))
  exact ⟨natFold hcount hinit hstep hbound (fun x k hk => hsize x k _ hk (htrace x k hk)),
    fun x => htrace x (count x) le_rfl⟩

end Turing.MultiTapeTM.ComputableInPolySpace
