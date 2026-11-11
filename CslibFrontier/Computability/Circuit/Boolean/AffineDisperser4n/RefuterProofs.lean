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
public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.RefuterAffineRep
public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.RefuterSearch
import all CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.Refuter

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
    refuterMeasure (applyStep S choice) < refuterMeasure S ∧
    (applyStep S choice).Valid f ∧
    (applyStep S choice).W + 10 * S.a ≤ S.W + 10 * (applyStep S choice).a ∧
    (applyStep S choice).a ≤ S.a := by
  sorry

theorem refuterLoop_valid {n} {f : BooleanFunction n} {S : State n}
    (hS : S.Valid f) (fuel : ℕ) (hfuel : refuterMeasure S ≤ fuel) :
    chooseStep? (refuterLoop S fuel) = none ∧
    (refuterLoop S fuel).Valid f ∧
    (refuterLoop S fuel).W + 10 * S.a ≤ S.W + 10 * (refuterLoop S fuel).a ∧
    (refuterLoop S fuel).a ≤ S.a := by
  sorry

theorem refute_correct {n d : ℕ} (C : Circuit (fullSignature 2 Bool) n 1)
    (f : BitString n → Bool) (hf : IsAffineDisperser f d)
    (hC : C.size + 10 * d < 4 * n) :
    C.eval fullInterpretation (@refute n d C f) 0 ≠ f (@refute n d C f) := by
  have hinit : (initialState C).Valid (fun x => C.eval fullInterpretation x 0) :=
    initialState_valid fun x => by
      ext i
      rw [Fin.eq_zero i]
      rfl
  obtain ⟨hterm, hval, hpot, -⟩ :=
    refuterLoop_valid hinit (refuterMeasure (initialState C)) le_rfl
  have ha : d < (refuterLoop (initialState C) (refuterMeasure (initialState C))).a := by
    have := initialState_a C
    have := initialState_W_le C
    omega
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (findCounterexample_isSome C f hf hval hterm ha
    fun u hu => findAffineRep_spec hval.wf hu)
  have hr : @refute n d C f = x := by
    unfold refute
    simp only [hx]
  rw [hr]
  exact findCounterexample_spec C f _ hx

end Cslib.Circuits.Boolean.AffineDisperser4n
