/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (conditional-result realization regression tests)

public import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic

/-!
# Conditional results in memory-client programs

These clients retain their original `pure` expressions, including selections inside returned
constructors, natural minima/maxima and Boolean decisions. Their certificates must charge the
native branch and require fit and exact-operation safety only for the selected alternative.
-/

public section

namespace CslibFrontierTests.WordRAMRealizeValues

open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization

private abbrev word : ℕ ↪ (Fin 1 → ℕ) := WordEncoding.encode
private abbrev pairWords : ℕ × ℕ ↪ (Fin 2 → ℕ) := WordEncoding.encode
private abbrev boolWords : Bool ↪ (Fin 2 → ℕ) := WordEncoding.encode
private abbrev optionalPairWords : Option (ℕ × ℕ) ↪ (Fin 3 → ℕ) := WordEncoding.encode

private def selectedWords (P : ℕ → Prop) [DecidablePred P] : ℕ ↪ (Fin 2 → ℕ) where
  toFun n := ![if P n then 0 else 1, n]
  inj' := fun _ _ h => congrFun h 1

private def shiftedSelectionWords (P : ℕ → Prop) [DecidablePred P] : ℕ ↪ (Fin 2 → ℕ) where
  toFun n := ![(if P n then 0 else 1) + 1, n]
  inj' := fun _ _ h => congrFun h 1

-- Choices fixed before runtime remain constant instructions, even for an arbitrary predicate.
example (P : Prop) [Decidable P] : Realizes .exact
    (fun _ : ℕ => pure (if P then 0 else 1)) word word
    (fun w _ _ => Fits w (if P then 0 else 1)) (fun _ _ => 0) := by
  realize
  exact h

-- Only a fixed minimum's result must fit; neither comparison operand has to fit.
example (a b : ℕ) : Realizes .exact (fun _ : ℕ => pure (min a b)) word word
    (fun w _ _ => Fits w (min a b)) (fun _ _ => 0) := by
  realize
  exact h

-- Fixed selections must also stay constant when a sibling result needs a runtime branch.
example (P : Prop) [Decidable P] : Realizes .exact
    (fun d : ℕ × ℕ => pure (if P then 0 else 1, min d.1 d.2)) pairWords pairWords
    (fun w _ _ => Fits w (if P then 0 else 1)) (fun _ _ => 0) := by
  realize <;> exact h

example (a b : ℕ) : Realizes .exact
    (fun d : ℕ × ℕ => pure (min a b, max d.1 d.2)) pairWords pairWords
    (fun w _ _ => Fits w (min a b)) (fun _ _ => 0) := by
  realize <;> exact h

-- A choice supplied by the input encoding is already a live word, including in a mixed result.
example (P : ℕ → Prop) [DecidablePred P] : Realizes .exact
    (fun n : ℕ => pure (if P n then 0 else 1, max n 0)) (selectedWords P) pairWords
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

-- An already live arithmetic context must likewise stay opaque when a sibling needs branching.
example (P : ℕ → Prop) [DecidablePred P] : Realizes .exact
    (fun n : ℕ => pure ((if P n then 0 else 1) + 1, max n 0))
    (shiftedSelectionWords P) pairWords (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

-- Returning a selected word does not require an explicit branch around the two `pure`s.
/-- A selected input word needs no fit premise beyond the encoded inputs. -/
theorem conditional_realizes : Realizes .exact
    (fun d : ℕ × ℕ => pure (if d.1 < d.2 then d.1 else d.2))
    (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

-- The choice may occur in a component of the result rather than at its outermost constructor.
example : Realizes .exact
    (fun d : ℕ × ℕ => pure (d.1, if d.1 = d.2 then d.1 else d.2)) pairWords pairWords
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

-- The option's presence tag is charged and must fit independently of its word payload.
example : Realizes .exact
    (fun d : ℕ × ℕ => pure (some (if d.1 < d.2 then (d.1, d.2) else (d.2, d.1))))
    pairWords optionalPairWords (fun w _ _ => Fits w 1) (fun _ _ => 0) := by
  realize <;> exact h

-- Minima and maxima select an input word; no successor or larger fitting envelope is needed.
example : Realizes .exact
    (fun d : ℕ × ℕ => pure (min d.1 d.2, max d.1 d.2)) pairWords pairWords
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

-- In particular, selecting at a maximal fitting word does not introduce an overflow boundary.
example : Fits 8 255 ∧
    (Memory.spec 8).clientResult (Memory.State.init [])
      (pure (min 255 0, max 255 0) : Memory.Prog (ℕ × ℕ)) = (0, 255) := by
  decide

-- Boolean source code is kept as a decision, with its conventional zero/one result encoding.
example : Realizes .exact (fun n : ℕ => pure (decide (n = 0))) word boolWords
    (fun w _ _ => Fits w 1) (fun _ _ => 0) := by
  realize
  exact h

-- An arithmetic comparison operand is computed and charged before the returned selection.
example : Realizes .exact
    (fun d : ℕ × ℕ => pure (if d.1 + 1 < d.2 then d.1 else d.2)) pairWords word
    (fun w d _ => Fits w (d.1 + 1)) (fun _ _ => 0) := by
  realize
  exact h

-- A zero divisor in the inactive branch does not prevent a valid selection.
example : Realizes .exact
    (fun d : ℕ × ℕ => pure (if d.2 = 0 then 0 else d.1 / d.2)) pairWords word
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize
  exact hc

-- Exact subtraction is defined on its chosen path, without a global subtraction hypothesis.
example : Realizes .exact
    (fun d : ℕ × ℕ => pure (if d.1 < d.2 then 0 else d.1 - d.2)) pairWords word
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize
  omega

-- Division by zero in the chosen alternative remains a genuine failure.
example : True := by
  fail_if_success
    have _ : Realizes .exact
        (fun d : ℕ × ℕ => pure (if d.2 = 0 then d.1 / d.2 else 0)) pairWords word
        (fun _ _ _ => True) (fun _ _ => 0) := by
      realize
      omega
  trivial

-- Selecting a newly computed word does not make overflow obligations disappear.
example : True := by
  fail_if_success
    have _ : Realizes .exact
        (fun n : ℕ => pure (if n = 0 then n + 1 else n)) word word
        (fun _ _ _ => True) (fun _ _ => 0) := by
      realize
  trivial

-- The standard basis retains its total division and truncated subtraction conventions.
example : Realizes .standard
    (fun d : ℕ × ℕ => pure (if d.2 = 0 then d.1 / d.2 else d.1 - d.2)) pairWords word
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

-- The stronger frontier-bounded judgment uses the same conditional-result normalization.
example : RealizesBounded .exact
    (fun d : ℕ × ℕ => pure (max d.1 d.2)) pairWords word
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

-- Automatically staged method arguments use the same returned-choice rules.
example (method : ℕ → Memory.Prog ℕ)
    (cert : Realizes .exact method word word (fun _ _ _ => True) (fun _ _ => 0)) :
    Realizes .exact (fun d : ℕ × ℕ => method (max d.1 d.2)) pairWords word
      (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

-- A certificate survives the definitionally equal direct/inherited `Pure` paths used by
-- the record interpreter; no method body is available for the tactic to unfold.
example (method : Pure Memory.Prog → ℕ → Memory.Prog ℕ)
    (cert : Realizes .exact (method (inferInstance : Pure Memory.Prog)) word word
      (fun _ _ _ => True) (fun _ _ => 0)) :
    Realizes .exact (method (inferInstance : Monad Memory.Prog).toApplicative.toPure)
      word word (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

@[instance_reducible] private def readingPure : Pure Memory.Prog where
  pure a := do
    let _ ← Memory.read 0
    pure a

-- This instance really adds a query and is not definitionally the certified one.
example (method : Pure Memory.Prog → ℕ → Memory.Prog ℕ)
    (_cert : Realizes .exact (method (inferInstance : Pure Memory.Prog)) word word
      (fun _ _ _ => True) (fun _ _ => 0)) : True := by
  fail_if_success
    have _ : Realizes .exact (method readingPure) word word
        (fun _ _ _ => True) (fun _ _ => 0) := by realize
  trivial

-- An arbitrary host predicate is not a certified machine comparison.
example (P : ℕ → Prop) [DecidablePred P] : True := by
  fail_if_success
    have _ : Realizes .exact
        (fun n : ℕ => pure (if P n then 1 else 0)) word word
        (fun w _ _ => Fits w 1) (fun _ _ => 0) := by
      realize
  trivial

end CslibFrontierTests.WordRAMRealizeValues
