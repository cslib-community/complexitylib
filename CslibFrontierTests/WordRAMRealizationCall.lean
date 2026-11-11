/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (realize certificate-call regression tests)

public import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic

/-!
# Calls to separately certified memory methods

The methods are parameters, so their implementations cannot be unfolded. Calls select existing
live words, may alias inputs, and carry their method domain to the reached memory. Computed
arguments are automatically staged with charged glue in the callee's input encoding.
-/

public section

namespace Cslib.WordRAM.Realization.Tests.Call

open Cslib.DataStructure

private abbrev word : ℕ ↪ (Fin 1 → ℕ) := (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
private abbrev pairWords : ℕ × ℕ ↪ (Fin 2 → ℕ) := appendWords word word
private abbrev unitWords : Unit ↪ (Fin 0 → ℕ) := (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding

-- This encoding has an unsupported glue coordinate, while its second word retains injectivity.
private def squaredWords : ℕ ↪ (Fin 2 → ℕ) where
  toFun n := ![n ^ 2, n]
  inj' := fun _ _ h => congrFun h 1

-- A separately certified method consumes a projection of a larger live environment.
theorem projection_call (m : ℕ → Memory.Prog ℕ) (P : ℕ → ℕ → Memory.State → Prop)
    (hm : Realizes .exact m (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := ℕ))
      P (fun _ _ => 0)) :
    Realizes .exact (fun d : ℕ × ℕ => m d.2) (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ)) (fun w d s => P w d.2 s) (fun _ _ => 0) := by
  realize
  exact h

-- A tuple-argument certificate can certify a curried method without unfolding its body.
example (m : ℕ → ℕ → Memory.Prog ℕ) (P : ℕ → ℕ × ℕ → Memory.State → Prop)
    (hm : Realizes .exact (fun d : ℕ × ℕ => m d.1 d.2) pairWords word P (fun _ _ => 0)) :
    Realizes .exact (fun d : ℕ × ℕ => m d.2 d.1) pairWords word
      (fun w d s => P w (d.2, d.1) s) (fun _ _ => 0) := by
  realize
  exact h

-- A curried opaque extraction feeds the canonical three-word optional-pair continuation.
example (extract : ℕ → ℕ → Memory.Prog (Option (ℕ × ℕ)))
    (P : ℕ → ℕ × ℕ → Memory.State → Prop)
    (hm : Realizes .exact (fun d : ℕ × ℕ => extract d.1 d.2) pairWords
      (WordEncoding.encode (α := Option (ℕ × ℕ))) P (fun _ _ => 0)) :
    Realizes .exact (fun d : ℕ × ℕ => do
      match ← extract d.2 d.1 with
      | none => pure (0, 0)
      | some (v, k) => pure (v, k)) pairWords pairWords
      (fun w d s => P w (d.2, d.1) s) (fun _ _ => 0) := by
  realize
  exact h

-- A small faithful dependent-index fixture pins the actual staged-call failure.
private def indexedWords : (Σ n : ℕ, Fin n) ↪ (Fin 2 → ℕ) where
  toFun d := ![d.1, d.2.val]
  inj' := by
    rintro ⟨n, i⟩ ⟨m, j⟩ h
    have hn : n = m := congrFun h 0
    subst m
    have hi : i = j := Fin.ext (congrFun h 1)
    cases hi
    rfl

private abbrev IndexedArgument := ((Σ n : ℕ, Fin n) × ℕ) × ℕ
private abbrev indexedInput : IndexedArgument ↪ (Fin 4 → ℕ) :=
  appendWords (appendWords indexedWords word) word

-- The implicit index must be solved before its dependent argument after charged pair staging.
example (m : {n : ℕ} → Fin n → ℕ → ℕ → Memory.Prog Unit)
    (P : ℕ → IndexedArgument → Memory.State → Prop)
    (hm : Realizes .exact (fun d : IndexedArgument => m d.1.1.2 d.1.2 d.2)
      indexedInput unitWords P (fun _ _ => 0)) :
    Realizes .exact (fun d : IndexedArgument => do
      let a ← pure (d.1.2, d.2)
      m d.1.1.2 a.1 a.2) indexedInput unitWords P (fun _ _ => 0) := by
  realize
  exact h

-- Scalar staging also charges the subtraction and constant before entering the method domain.
example (m : {n : ℕ} → Fin n → ℕ → ℕ → Memory.Prog Unit)
    (P : ℕ → IndexedArgument → Memory.State → Prop)
    (hm : Realizes .exact (fun d : IndexedArgument => m d.1.1.2 d.1.2 d.2)
      indexedInput unitWords P (fun _ _ => 0)) :
    Realizes .exact (fun d : IndexedArgument => do
      let size ← pure (d.1.2 - 1)
      let start ← pure 1
      m d.1.1.2 size start) indexedInput unitWords
      (fun w d s => 1 ≤ d.1.2 ∧ P w ((d.1.1, d.1.2 - 1), 1) s)
      (fun _ _ => 0) := by
  realize <;> first | exact h.1 | exact h.2 | exact (hwords 2).of_le h.1

-- Input registers need not be distinct: the existing reindex rule permits aliasing.
example (m : ℕ × ℕ → Memory.Prog ℕ) (P : ℕ → ℕ × ℕ → Memory.State → Prop)
    (hm : Realizes .exact m pairWords word P (fun _ _ => 0)) :
    Realizes .exact (fun d : ℕ => m (d, d)) word word
      (fun w d s => P w (d, d) s) (fun _ _ => 0) := by
  realize
  exact h

-- The returned word is live in the continuation, without revealing the method body.
example (m : ℕ → Memory.Prog ℕ) (P : ℕ → ℕ → Memory.State → Prop)
    (hm : Realizes .exact m word word P (fun _ _ => 0)) :
    Realizes .exact (fun d : ℕ × ℕ => do
      let a ← m d.1
      Memory.write d.2 a) pairWords unitWords
      (fun w d s => P w d.1 s) (fun _ _ => 0) := by
  realize
  exact h

-- A call's domain is required at the actual state reached after a write.
example (m : ℕ → Memory.Prog ℕ) (P : ℕ → ℕ → Memory.State → Prop)
    (hm : Realizes .exact m word word P (fun _ _ => 0)) :
    Realizes .exact (fun d : ℕ × ℕ => do
      Memory.write d.1 d.2
      m d.2) pairWords word
      (fun w d s => P w d.2 ⟨Function.update s.mem d.1 d.2, s.frontier⟩)
      (fun _ _ => 0) := by
  realize
  exact h

-- Automatic staging still requires the arithmetic result to fit; it is not free rewiring.
example (m : ℕ → Memory.Prog ℕ)
    (_hm : Realizes .exact m word word (fun _ _ _ => True) (fun _ _ => 0)) : True := by
  fail_if_success
    have _ : Realizes .exact (fun d : ℕ => m (d + 1)) word word
        (fun _ _ _ => True) (fun _ _ => 0) := by realize
  trivial

-- A computed scalar argument needs no handwritten `pure` stage.
example (m : ℕ → Memory.Prog ℕ) (P : ℕ → ℕ → Memory.State → Prop)
    (hm : Realizes .exact m word word P (fun _ _ => 0)) :
    Realizes .exact (fun d : ℕ => m (d + 1)) word word
      (fun w d s => Fits w (d + 1) ∧ P w (d + 1) s) (fun _ _ => 0) := by
  realize <;> first | exact h.1 | exact h.2

-- Its explicit pure step is certified glue; the fitting arithmetic result stays visible.
example (m : ℕ → Memory.Prog ℕ) (P : ℕ → ℕ → Memory.State → Prop)
    (hm : Realizes .exact m word word P (fun _ _ => 0)) :
    Realizes .exact (fun d : ℕ => do
      let a ← pure (d + 1)
      m a) word word
      (fun w d s => Fits w (d + 1) ∧ P w (d + 1) s) (fun _ _ => 0) := by
  realize <;> first | exact h.1 | exact h.2

-- Curried methods can combine computed coordinates, including repeated arguments.
example (m : ℕ → ℕ → Memory.Prog ℕ) (P : ℕ → ℕ × ℕ → Memory.State → Prop)
    (hm : Realizes .exact (fun d : ℕ × ℕ => m d.1 d.2) pairWords word P (fun _ _ => 0)) :
    Realizes .exact (fun d : ℕ => m (d + 1) (d + 1)) word word
      (fun w d s => Fits w (d + 1) ∧ P w (d + 1, d + 1) s) (fun _ _ => 0) := by
  realize <;> first | exact h.1 | exact h.2

-- The whole dependent argument uses its supplied encoding; no `WordEncoding` is inferred.
example (m : {n : ℕ} → Fin n → ℕ → ℕ → Memory.Prog Unit)
    (P : ℕ → IndexedArgument → Memory.State → Prop)
    (hm : Realizes .exact (fun d : IndexedArgument => m d.1.1.2 d.1.2 d.2)
      indexedInput unitWords P (fun _ _ => 0)) :
    Realizes .exact (fun d : IndexedArgument => m d.1.1.2 (d.1.2 - 1) 1)
      indexedInput unitWords
      (fun w d s => 1 ≤ d.1.2 ∧ P w ((d.1.1, d.1.2 - 1), 1) s)
      (fun _ _ => 0) := by
  realize <;> first | exact h.1 | exact h.2 | exact (hwords 2).of_le h.1

-- Staging preserves the callee's obligation at the memory reached after an earlier write.
example (m : ℕ → Memory.Prog ℕ) (P : ℕ → ℕ → Memory.State → Prop)
    (hm : Realizes .exact m word word P (fun _ _ => 0)) :
    Realizes .exact (fun d : ℕ × ℕ => do
      Memory.write d.1 d.2
      m (d.2 + 1)) pairWords word
      (fun w d s => Fits w (d.2 + 1) ∧
        P w (d.2 + 1) ⟨Function.update s.mem d.1 d.2, s.frontier⟩)
      (fun _ _ => 0) := by
  realize <;> first | exact h.1 | exact h.2

-- Standard-basis truncated subtraction has no exact-subtraction domain obligation.
example (m : ℕ → Memory.Prog ℕ)
    (hm : Realizes .standard m word word (fun _ _ _ => True) (fun _ _ => 0)) :
    Realizes .standard (fun d : ℕ × ℕ => m (d.1 - d.2)) pairWords word
      (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

-- Exact subtraction still requires definedness, even when its truncated result fits.
example (m : ℕ → Memory.Prog ℕ)
    (_hm : Realizes .exact m word word (fun _ _ _ => True) (fun _ _ => 0)) : True := by
  fail_if_success
    have _ : Realizes .exact (fun d : ℕ × ℕ => m (d.1 - d.2)) pairWords word
        (fun _ _ _ => True) (fun _ _ => 0) := by realize
  trivial

-- A fitting quotient does not grant exact division by zero.
example (m : ℕ → Memory.Prog ℕ)
    (_hm : Realizes .exact m word word (fun _ _ _ => True) (fun _ _ => 0)) : True := by
  fail_if_success
    have _ : Realizes .exact (fun d : ℕ × ℕ => m (d.1 / d.2)) pairWords word
        (fun _ _ _ => True) (fun _ _ => 0) := by realize
  trivial

example (m : ℕ → Memory.Prog ℕ)
    (hm : Realizes .exact m word word (fun _ _ _ => True) (fun _ _ => 0)) :
    Realizes .exact (fun d : ℕ × ℕ => m (d.1 / d.2)) pairWords word
      (fun _ d _ => d.2 ≠ 0) (fun _ _ => 0) := by
  realize
  exact h

-- Frontier-bounded certificates use the same staging path and preserve their stronger contract.
example (m : ℕ → Memory.Prog ℕ) (P : ℕ → ℕ → Memory.State → Prop)
    (hm : RealizesBounded .exact m word word P (fun _ _ => 0)) :
    RealizesBounded .exact (fun d : ℕ => m (d + 1)) word word
      (fun w d s => Fits w (d + 1) ∧ P w (d + 1) s) (fun _ _ => 0) := by
  realize <;> first | exact h.1 | exact h.2

-- Failed staging of the first candidate's unsupported power must roll back its argument
-- unification before trying a later certificate for the same method and basis.
example (m : ℕ → Memory.Prog ℕ)
    (_wrong : Realizes .exact m squaredWords word (fun _ _ _ => True) (fun _ _ => 0))
    (hm : Realizes .exact m word word (fun _ _ _ => True) (fun _ _ => 0)) :
    Realizes .exact (fun d : ℕ => m (d + 1)) word word
      (fun w d _ => Fits w (d + 1)) (fun _ _ => 0) := by
  realize
  exact h

end Cslib.WordRAM.Realization.Tests.Call
