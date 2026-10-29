/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Arithmetic
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryAddition
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib

/-!
# Schoolbook addition: consuming carry execution and independent resource clients

The first fold consumes the first operand and a cursor into the second. The finishing fold
consumes the remaining cursor and emits the final carry. Asymmetric executions distinguish these
stages even though addition is commutative. The composed client doubles a computed sum while
retaining resource degree two, output degree one and the original space budget.
-/

open Turing.MultiTapeTM

-- Empty inputs, equality and a no-carry sum inspect the consuming fold's actual state.
example :
    let run (a b : ℕ) := a.bits.foldl NatAdd.addStep (false, b.bits, []);
    run 0 0 = (false, [], []) ∧
    run 0 9 = (false, [true, false, false, true], []) ∧
    run 9 0 = (false, [], [true, false, false, true]) ∧
    run 7 7 = (true, [], [false, true, true]) ∧
    run 10 5 = (false, [], [true, true, true, true]) := by
  decide +kernel

-- Swapping a long-carry input moves work from the first fold to the finishing fold. Both
-- executions must emit the seventeenth digit, including when the right cursor is already empty.
example :
    let run (a b : ℕ) := a.bits.foldl NatAdd.addStep (false, b.bits, []);
    let finish (s : Bool × List Bool × List Bool) :=
      NatSucc.succFinish (s.2.1.foldl NatSucc.succStep (s.1, s.2.2));
    run 65535 1 = (true, [], List.replicate 16 false) ∧
    run 1 65535 = (true, List.replicate 15 true, [false]) ∧
    finish (run 65535 1) = List.replicate 16 false ++ [true] ∧
    finish (run 1 65535) = List.replicate 16 false ++ [true] ∧
    finish (run 0 9) = [true, false, false, true] ∧
    finish (run 7 7) = [false, true, true, true] ∧
    finish (run 0 0) = [] := by
  decide +kernel

-- Reuse the retained correctness laws to connect precisely those two folds to addition.
example (a b : ℕ) :
    let s := a.bits.foldl NatAdd.addStep (false, b.bits, []);
    NatSucc.succFinish (s.2.1.foldl NatSucc.succStep (s.1, s.2.2)) = (a + b).bits := by
  dsimp only
  rw [NatSucc.succFinish_foldl, ← NatAdd.foldl_addStep, List.nil_append, NatAdd.addBits_bits]
  rfl

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
