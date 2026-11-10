/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Complexity.FineGrained.WeightedCountingResources

/-! # Actual weighted native counting, reconstruction and binary-output resource clients -/

public section

namespace WeightedCountingResourcesTests

open Cslib.Logic.PL Cslib.Logic.PL.WeightedRow BinaryPlan Turing.MultiTapeTM
open Cslib.GenericRAM

/-- Repeated positive occurrences aggregate before the partial-rank query is constructed. -/
def repeatedRow : Occurrences 3 2 where
  var := fun _ => 0
  sign := fun _ => true
  weight := fun i => if i == 0 then 2 else 3
  positive := by decide
  target := 5

/-- Repeated occurrences give a full-rank rational candidate with a half-integral coordinate. -/
def fractionalRows (j : Fin 2) : Occurrences 2 2 where
  var := fun _ => j
  sign := fun _ => true
  weight := fun _ => 1
  positive := by decide
  target := if j == 0 then 1 else 0

example : (compile 1 3 [BinaryNormalization.ofOccurrences repeatedRow]).isLeft = false := by
  decide

/-- A large binary coefficient, positive weight and normalized demand zero. -/
def largeRow : Occurrences 2 1 where
  var := fun _ => 0
  sign := fun _ => true
  weight := fun _ => 2 ^ 80
  positive := fun _ => Nat.two_pow_pos _
  target := 2 ^ 80

/-- One certified actual algorithm handles a positive partial-rank query, non-Boolean full rank,
a large binary weight and an 81-bit direct answer, preserving unused variables. -/
example : ∃ count : ℕ × List BinaryNormalization.Input → ℕ,
    ∃ cs : NativeCertificate count
      (encPair encUnary (encList BinaryNormalization.encInput)) encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C *
        ((encPair encUnary (encList BinaryNormalization.encInput) x).length + 1) ^ e) ∧
      count (3, (List.finRange 1).map fun _ =>
        BinaryNormalization.ofOccurrences repeatedRow) = 4 ∧
      count (2, (List.finRange 2).map fun j =>
        BinaryNormalization.ofOccurrences (fractionalRows j)) = 0 ∧
      count (2, [BinaryNormalization.ofOccurrences largeRow]) = 2 ∧
      count (80, []) = 2 ^ 80 ∧
      let x := (3, (List.finRange 1).map fun _ =>
        BinaryNormalization.ofOccurrences repeatedRow)
      cs.time x ≤ C * ((encPair encUnary (encList BinaryNormalization.encInput) x).length + 1) ^ e *
        2 ^ (A * Nat.logLogSqrtLogScale 3) := by
  obtain ⟨count, cs, C, e, A, hs, h⟩ := exists_count_sharp_certificate 1
  refine ⟨count, cs, C, e, A, hs, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(h (fun _ : Fin 1 => repeatedRow) (by decide)).1]
    decide
  · rw [(h fractionalRows (by decide)).1]
    decide
  · have hc := (h (fun _ : Fin 1 => largeRow) (by decide)).1
    simpa using hc.trans (show _ = 2 by decide)
  · have hc := (h (fun j : Fin 0 => Fin.elim0 j : Fin 0 → Occurrences 80 0)
      (by intro j; exact Fin.elim0 j)).1
    simpa using hc
  · exact (h (fun _ : Fin 1 => repeatedRow) (by decide)).2

/-- The real resource witness counts a declared empty system at arbitrary size. Its answer is
written in binary; no assignment enumeration is used by the direct tag. -/
example : ∃ count : ℕ × List BinaryNormalization.Input → ℕ,
    ∃ cs : NativeCertificate count
      (encPair encUnary (encList BinaryNormalization.encInput)) encNat, ∃ C e A : ℕ,
      ∀ n, 16 ≤ n → count (n, []) = 2 ^ n ∧
        (cs.time (n, []) : ℝ) ≤ (C : ℝ) *
          ((encPair encUnary (encList BinaryNormalization.encInput) (n, [])).length + 1 : ℕ) ^ e *
          (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n) := by
  obtain ⟨count, cs, C, e, A, _hs, h⟩ := exists_count_real_sharp_certificate 1
  refine ⟨count, cs, C, e, A, fun n hn => ?_⟩
  have hc := h (fun j : Fin 0 => Fin.elim0 j : Fin 0 → Occurrences n 0)
    (by intro j; exact Fin.elim0 j)
  exact ⟨by simpa using hc.1, by simpa using hc.2 hn⟩

end WeightedCountingResourcesTests
