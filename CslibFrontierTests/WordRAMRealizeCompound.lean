/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (compound word-guard realization regression tests)

public import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
public import CslibFrontier.DataStructure.PriorityQueue.Spec

/-!
# Compound and named guards in memory clients

The priority-queue predicate supplies an actual named disjunction/conjunction client. Further
fixtures require short-circuit execution to retain the safety and fit conditions only of reached
comparison operands, including operands whose encoded values already contain a host predicate.
-/

public section

namespace CslibFrontierTests.WordRAMRealizeCompound

open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure.PriorityQueue

private abbrev word : ℕ ↪ (Fin 1 → ℕ) := WordEncoding.encode
private abbrev pairWords : ℕ × ℕ ↪ (Fin 2 → ℕ) := WordEncoding.encode
private abbrev priorityWords : (ℕ × ℕ) × (ℕ × ℕ) ↪ (Fin 4 → ℕ) := WordEncoding.encode

/-- Select the smaller key, resolving equal-key ties by the smaller raw handle, directly through
the shared indexed-priority predicate. All four input words retain their explicit encoding. -/
theorem priority_choice_realizes : Realizes .exact
    (fun d : (ℕ × ℕ) × (ℕ × ℕ) =>
      if IndexedMinPQ.RawPrioLT d.1 d.2 then pure d.1 else pure d.2)
    (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ × ℕ)) (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

-- Key order takes precedence over handle order.
example : (Memory.spec 4).clientResult (Memory.State.init [])
    (if IndexedMinPQ.RawPrioLT (7, 1) (3, 2) then pure (7, 1) else pure (3, 2) :
      Memory.Prog (ℕ × ℕ)) = (7, 1) := by
  decide

-- Equal keys use the smaller handle; no successor of either key is computed.
example : (Memory.spec 8).clientResult (Memory.State.init [])
    (if IndexedMinPQ.RawPrioLT (7, 255) (3, 255) then pure (7, 255) else pure (3, 255) :
      Memory.Prog (ℕ × ℕ)) = (3, 255) := by
  decide

private def priorityAlias (a b : ℕ × ℕ) : Prop := IndexedMinPQ.RawPrioLT a b
private instance (a b : ℕ × ℕ) : Decidable (priorityAlias a b) :=
  inferInstanceAs (Decidable (IndexedMinPQ.RawPrioLT a b))

private def priorityAliasAgain (a b : ℕ × ℕ) : Prop := priorityAlias a b
private instance (a b : ℕ × ℕ) : Decidable (priorityAliasAgain a b) :=
  inferInstanceAs (Decidable (priorityAlias a b))

-- Transparent aliases compose without a client-written unfolding or nested-if restatement.
example : Realizes .exact
    (fun d : (ℕ × ℕ) × (ℕ × ℕ) =>
      if priorityAliasAgain d.1 d.2 then pure d.1 else pure d.2)
    priorityWords pairWords (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

-- A false first conjunct avoids the undefined quotient at n = 0.
example : Realizes .exact
    (fun n : ℕ => if n ≠ 0 ∧ 0 < n / n then pure n else pure 0) word word
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize
  omega

-- A true first disjunct likewise avoids that quotient.
example : Realizes .exact
    (fun n : ℕ => if n = 0 ∨ 0 < n / n then pure n else pure 0) word word
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize
  omega

-- Both short-circuit forms also protect exact subtraction below zero.
example : Realizes .exact
    (fun n : ℕ => if n ≠ 0 ∧ n - 1 < n then pure n else pure 0) word word
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize
  omega

example : Realizes .exact
    (fun n : ℕ => if n = 0 ∨ n - 1 < n then pure n else pure 0) word word
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize
  omega

-- The fitting increment is needed only when the first disjunct is false.
example : Realizes .exact
    (fun d : ℕ × ℕ => if d.1 = 0 ∨ d.2 + 1 ≤ d.1 then pure d.1 else pure d.2)
    pairWords word (fun w d _ => d.1 ≠ 0 → Fits w (d.2 + 1)) (fun _ _ => 0) := by
  realize
  exact h (by assumption)

-- The same reached-path condition is retained by conjunction.
example : Realizes .exact
    (fun d : ℕ × ℕ => if d.1 ≠ 0 ∧ d.2 + 1 ≤ d.1 then pure d.1 else pure d.2)
    pairWords word (fun w d _ => d.1 ≠ 0 → Fits w (d.2 + 1)) (fun _ _ => 0) := by
  realize
  exact h (by assumption)

example : True := by
  fail_if_success
    have _ : Realizes .exact
        (fun d : ℕ × ℕ => if d.1 = 0 ∨ d.2 + 1 ≤ d.1 then pure d.1 else pure d.2)
        pairWords word (fun _ _ _ => True) (fun _ _ => 0) := by
      realize
  trivial

-- Here the division by zero is reached, so the compound syntax must not hide its failure.
example : True := by
  fail_if_success
    have _ : Realizes .exact
        (fun n : ℕ => if n = 0 ∧ n / n = 0 then pure 0 else pure n) word word
        (fun _ _ _ => True) (fun _ _ => 0) := by
      realize
      omega
  trivial

-- Formula normalization composes with negation, nonstrict comparisons and returned choices.
example : Realizes .exact
    (fun d : ℕ × ℕ => pure
      (if ¬(d.1 ≤ d.2 ∧ ¬(d.1 = d.2)) ∨ d.1 = d.2 then d.1 else d.2))
    pairWords word (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

example : Realizes .exact
    (fun d : ℕ × ℕ => @ite (Memory.Prog ℕ) (d.1 ≤ d.2 ∧ d.2 ≠ 0)
      (Classical.propDecidable _) (pure d.1) (pure d.2))
    pairWords word (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

private def namedLe (a b : ℕ) : Prop := a ≤ b

-- Only the whole formula supplies decidability; its named leaf needs no separate instance.
example : Realizes .exact
    (fun d : ℕ × ℕ => @ite (Memory.Prog ℕ) (¬namedLe d.1 d.2)
      (Classical.propDecidable _) (pure d.1) (pure d.2))
    pairWords word (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

example : Realizes .exact
    (fun d : ℕ × ℕ => @ite (Memory.Prog ℕ) (namedLe d.1 d.2 ∧ d.2 ≠ 0)
      (Classical.propDecidable _) (pure d.1) (pure d.2))
    pairWords word (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

-- Standard arithmetic remains total on a reached zero-divisor path.
example : Realizes .standard
    (fun n : ℕ => if n = 0 ∧ n / n = 0 then pure 0 else pure n) word word
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

example : RealizesBounded .exact
    (fun d : ℕ × ℕ => if d.1 ≤ d.2 ∧ d.2 ≠ 0 then pure d.1 else pure d.2)
    pairWords word (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

private def selectedWords (P : ℕ → Prop) [DecidablePred P] : ℕ ↪ (Fin 2 → ℕ) where
  toFun n := ![if P n then 0 else 1, n]
  inj' := fun _ _ h => congrFun h 1

-- The host predicate inside an already encoded word must stay opaque while guards are expanded.
example (P : ℕ → Prop) [DecidablePred P] : Realizes .exact
    (fun n : ℕ =>
      if ((if P n then 0 else 1) ≤ n ∧ n ≠ 0) ∨
          (n = 0 ∧ (if P n then 0 else 1) = 0) then
        pure (if P n then 0 else 1) else pure n)
    (selectedWords P) word (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

private def wrappedHost (P : ℕ → Prop) (n : ℕ) : Prop := P n
private instance (P : ℕ → Prop) [DecidablePred P] (n : ℕ) : Decidable (wrappedHost P n) :=
  inferInstanceAs (Decidable (P n))

-- Naming an arbitrary runtime predicate does not supply a native comparison certificate.
example (P : ℕ → Prop) [DecidablePred P] : True := by
  fail_if_success
    have _ : Realizes .exact
        (fun n : ℕ => if wrappedHost P n then pure n else pure 0) word word
        (fun _ _ _ => True) (fun _ _ => 0) := by
      realize
  trivial

end CslibFrontierTests.WordRAMRealizeCompound
