/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import CslibFrontier.Computability.Complexity.FineGrained.SignedDegreePartition
public import CslibFrontierTests.PaperEndpoints.BoundedDegreePartition
meta import CslibFrontier.Computability.Complexity.FineGrained.SignedDegreePartition
meta import CslibFrontierTests.PaperEndpoints.BoundedDegreePartition

/-! # Actual signed normalization followed by original-label counting on tiny graphs -/

public section
open Cslib.Logic.PL
set_option linter.hashCommand false

/-- Tiny original-label test oracle after actual signed input normalization. -/
@[expose] def signedPartitionTest (x : DegreePartition.Signed.Input) : ℕ :=
  boundedPartitionTestCount (q := 2) (D := 1) (fun _ _ _ => true)
    (DegreePartition.Signed.normalize x)

/-- info: (4, 2, 0, 0, 1, 0) -/
#guard_msgs in
#eval (signedPartitionTest (boundedPartitionEdge, [(-2, 2 ^ 512), (-1, 2)]),
  signedPartitionTest (boundedPartitionEdge, [(1, 1), (-1, 2)]),
  signedPartitionTest (boundedPartitionEdge, [(-5, -1), (-1, 2)]),
  signedPartitionTest (boundedPartitionEdge, [(2, 1), (0, 2)]),
  signedPartitionTest ((0, []), [(-2, 0), (-1, 2 ^ 512)]),
  signedPartitionTest ((0, []), [(-2, -1), (0, 0)]))

open Classical in
example : ∃ count : DegreePartition.Signed.Input → ℕ,
    ∃ cs : Cslib.GenericRAM.NativeCertificate count DegreePartition.Signed.encInput
      Turing.MultiTapeTM.encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((DegreePartition.Signed.encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : Fin 2 → ℤ),
        count (DegreePartition.Signed.ofGraph G lo hi) = Fintype.card
          {S : Fin 2 → Set (Fin n) // G.IsDegreePartition (fun _ _ => Set.univ) S ∧
            ∀ i, lo i ≤ (Nat.card (S i) : ℤ) ∧ (Nat.card (S i) : ℤ) ≤ hi i} ∧
        (16 ≤ n → (cs.time (DegreePartition.Signed.ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
          ((DegreePartition.Signed.encInput (DegreePartition.Signed.ofGraph G lo hi)).length + 1 :
            ℕ) ^ e * (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) :=
  DegreePartition.Signed.exists_count_finiteCofinite_certificate (fun _ _ => Set.univ)
    (by intro _ _; simp)
