/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.Step
public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n
public import CslibFrontier.Computability.Complexity.Problems.XORSAT.Dense
public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.Refuter

/-!
# Refuter correctness and time bound

Proofs for the deterministic refuter algorithm.
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser4n

open Cslib.Circuits.Boolean.AffineDisperserCore
open Cslib.Circuits.Boolean.AffineDisperserCore.State
open Cslib.Circuits.Boolean.SemiCircuit
open Cslib.Complexity.XORSAT.Dense Cslib.Circuits Cslib.BitString

theorem applyStep_valid {n} {f : BooleanFunction n} {S : State n} (hS : S.Valid f)
    (choice : StepChoice) (hchoice : chooseStep? S = some choice) :
    Step f S (applyStep S choice) := by
  sorry

theorem refuterLoop_valid {n} {f : BooleanFunction n} {S : State n}
    (hS : S.Valid f) (fuel : ℕ) : (refuterLoop S fuel).Valid f := by
  sorry

theorem refute_correct {n d : ℕ} (C : Circuit (fullSignature 2 Bool) n 1)
    (f : BitString n → Bool) (hf : IsAffineDisperser f d)
    (hC : C.size + 10 * d < 4 * n) :
    C.eval fullInterpretation (@refute n d C f) 0 ≠ f (@refute n d C f) := by
  sorry

end Cslib.Circuits.Boolean.AffineDisperser4n
