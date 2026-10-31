/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryAddition
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib

/-!
# Binary addition: independent resource clients

The quadratic-time, linear-space addition certificate is weakened from the linear zip
transducer. The composed client doubles a computed sum while retaining resource degree two,
output degree one and the original space budget.
-/

open Turing.MultiTapeTM

-- Pair framing is asymmetric despite the equal sums. A seventeenth output bit must be charged.
example :
    let L (p : ℕ × ℕ) := (encPair encNat encNat p).length;
    L (65535, 1) = 34 ∧ L (1, 65535) = 19 ∧
    (L (65535, 1) + 1) ^ 2 = 1225 ∧ (L (1, 65535) + 1) ^ 2 = 400 ∧
    (encNat (65535 + 1)).length = 17 ∧ (encNat (1 + 65535)).length = 17 := by
  decide +kernel

-- Testing whether a computed sum is empty consumes the independent quadratic-time/linear-space
-- contract through a linear outer machine; the workspace budget must not become quadratic.
example :
    let emptySum (p : ℕ × ℕ) := decide (p.1 + p.2 = 0);
    ComputableInO emptySum (encPair encNat encNat) encBool
      (fun p => ((encPair encNat encNat p).length + 1) ^ 2)
      (fun p => (encPair encNat encNat p).length + 1) ∧
    emptySum (0, 0) = true ∧ emptySum (0, 9) = false ∧ emptySum (9, 0) = false := by
  exact ⟨ComputableInO.natIsZero.comp_linear ComputableInO.natAdd,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

-- A supplied addition certificate composes at degree (2,1), rather than multiplying time
-- degrees to four or replacing linear output degree by the quadratic time degree.
example :
    let total (p : ℕ × ℕ) := (p.1 + p.2) + (p.1 + p.2);
    ComputableInDegree total (encPair encNat encNat) encNat 2 1 ∧
    ComputableInSpace total (encPair encNat encNat) encNat
      (fun p => (encPair encNat encNat p).length) ∧
    total (0, 0) = 0 ∧ total (3, 10) = 26 ∧ total (10, 3) = 26 ∧
    total (65535, 1) = 131072 := by
  dsimp only
  refine ⟨?_, ?_, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · fail_if_success fun_prop
    have hinputs : ComputableInDegree (fun p : ℕ × ℕ => (p.1, p.2))
        (encPair encNat encNat) (encPair encNat encNat) 1 1 := by
      fun_prop (disch := first | apply le_refl | omega)
    have hsum := computableInDegree_add.comp hinputs
    exact (computableInDegree_add.comp (hsum.prod hsum)).mono
  · have hsum := ComputableInSpace.budget_natAdd
      (ComputableInSpace.fst encNat encNat) (ComputableInSpace.snd encNat encNat)
    exact ComputableInSpace.budget_natAdd hsum hsum
