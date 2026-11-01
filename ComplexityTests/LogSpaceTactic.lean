/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Tactic.LogSpace
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Words

/-! # Bounded logspace automation and its resource boundary -/

namespace ComplexityTests.LogSpaceTactic

open Turing.MultiTapeTM

-- Existing compositional coverage remains available.
example : ComputableInLogSpace (fun p : List Bool × List Bool => p.2 ++ p.1)
    (encPair encBits encBits) encBits := by
  logspace

-- The constant bound selects a recipe which fun_prop alone does not provide.
example {α : Type} {enc : α ↪ List Bool} {r : α → ℕ} {f : α × ℕ → Bool}
    (k : ℕ) (hr : ComputableInLogSpace r enc encUnary) (hk : ∀ a, r a ≤ k)
    (hf : ComputableInLogSpace f (encPair enc encUnary) encBool) :
    ComputableInLogSpace (fun a => (List.range (r a)).map fun i => f (a, i)) enc encBits := by
  fail_if_success fun_prop
  logspace

-- A callback can itself call a supplied routine on computed arguments.
example {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {r : α → ℕ} {q : α × ℕ → β} {f : β → Bool} (k : ℕ)
    (hr : ComputableInLogSpace r encA encUnary) (hk : ∀ a, r a ≤ k)
    (hq : ComputableInLogSpace q (encPair encA encUnary) encB)
    (hf : ComputableInLogSpace f encB encBool) :
    ComputableInLogSpace (fun a => (List.range (r a)).map fun i => f (q (a, i)))
      encA encBits := by
  logspace

-- Nested bounded construction prepares an evaluator's tuple without a hand-built chain.
example {α : Type} {enc : α ↪ List Bool} {r : α → ℕ}
    {f : α × ℕ → Bool} {d : α × List Bool → Bool} (k : ℕ)
    (hr : ComputableInLogSpace r enc encUnary) (hk : ∀ a, r a ≤ k)
    (hf : ComputableInLogSpace f (encPair enc encUnary) encBool)
    (hd : ComputableInLogSpace d (encPair enc encBits) encBool) :
    ComputableInLogSpace (fun a => d (a, (List.range (r a)).map fun i => f (a, i)))
      enc encBool := by
  logspace

-- A closed instance: three copies of the first input bit, including on the empty word.
example : ComputableInLogSpace
    (fun a : List Bool => (List.range 3).map fun _ => a.headD false) encBits encBits := by
  have hbound : ∀ _ : List Bool, 3 ≤ 3 := fun _ => le_rfl
  logspace

-- Unrelated bounds must not commit search to the wrong count function.
example {α : Type} {enc : α ↪ List Bool} {r s : α → ℕ} {f : α × ℕ → Bool}
    (k j : ℕ) (_hs : ∀ a, s a ≤ j)
    (hr : ComputableInLogSpace r enc encUnary) (hk : ∀ a, r a ≤ k)
    (hf : ComputableInLogSpace f (encPair enc encUnary) encBool) :
    ComputableInLogSpace (fun a => (List.range (r a)).map fun i => f (a, i)) enc encBits := by
  logspace

-- Bounds are essential. Failure leaves the original goal available for an explicit proof.
example {α : Type} {enc : α ↪ List Bool} {r : α → ℕ} {f : α × ℕ → Bool}
    (_hr : ComputableInLogSpace r enc encUnary)
    (_hf : ComputableInLogSpace f (encPair enc encUnary) encBool)
    (h : ComputableInLogSpace (fun a => (List.range (r a)).map fun i => f (a, i)) enc encBits) :
    ComputableInLogSpace (fun a => (List.range (r a)).map fun i => f (a, i)) enc encBits := by
  fail_if_success (clear h; logspace)
  exact h

-- The existing inclusion remains one-way, even with the tactic imported.
example {f : List Bool → Bool} (_hf : ComputableInPolyTime f encBits encBool)
    (h : ComputableInLogSpace f encBits encBool) :
    ComputableInLogSpace f encBits encBool := by
  fail_if_success (clear h; logspace)
  exact h

example {f : List Bool → Bool} (hf : ComputableInLogSpace f encBits encBool) :
    ComputableInPolyTime (fun p : List Bool × List Bool => f (p.1 ++ p.2))
      (encPair encBits encBits) encBool := by
  fun_prop

end ComplexityTests.LogSpaceTactic
