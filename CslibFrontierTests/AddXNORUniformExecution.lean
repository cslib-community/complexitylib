/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import all CslibFrontier.Cryptanalysis.AddXNORUniformExecution
import all CslibFrontier.Computability.WordRAM.Interpreter.Step
import all CslibFrontier.Computability.WordRAM.Interpreter.Run
import all CslibFrontier.Computability.WordRAM.Interpreter.Output
import all CslibFrontier.Computability.WordRAM.Defs
import all CslibFrontier.Computability.WordRAM.Basis
import all CslibFrontier.Computability.GenericRAM.Simulation.Run
import all CslibFrontier.Cryptanalysis.AddXNORNativeClassCounts

/-!
# Uniform runtime-program execution clients

The same interpreter accepts different instruction fields, labels and lengths.
Checked execution covers real addition, overflow, empty programs and huge binary
jump labels. The single source machine produces an original-chain witness on
unequal quarters/colliding keys and proves an exhaustive empty-quarter miss.
-/

set_option linter.privateModule false

open Turing.MultiTapeTM Cslib.GenericRAM Cslib.WordRAM
open Cslib.Cryptanalysis.AddXNOR Cslib.Cryptanalysis.AddXNOR.Native.Driver
open ProgramGeneration UniformExecution Native.Quarter

private def small (literal : ℕ) : Program .standard 2 :=
  [.op (.const 0 1), .op (.const 1 literal), .op (.bin .add 0 0 1), .halt 0]

/-- One and the same program-input certificate accepts every runtime literal and clock. -/
noncomputable example : NativeCertificate
    (fun x : Interpreter.RunInput 2 => FiniteState.run x.2.1.1 x.2.1.2.toGeneric x.1 x.2.2)
    (Interpreter.runInputEncoding 2) (FiniteState.resultEncoding Basis.standard.encoding) :=
  Interpreter.runCertificate

example (literal w : ℕ) :
    Interpreter.step ((w, ProgramLiterals.serialize (small literal)),
      Interpreter.toTuple (initState .standard 2 [])) =
    Interpreter.toResult (FiniteState.step w (small literal).toGeneric
      (initState .standard 2 [])) :=
  Interpreter.step_serialize w (small literal) _

/-- Addition is not being replaced by an involution or XOR. -/
example : FiniteState.output (FiniteState.run (M := Basis.standard.genericModel)
    3 (small 3).toGeneric 4 (initState .standard 2 [])) = Option.some 4 := by decide +kernel

example : FiniteState.run (M := Basis.standard.genericModel)
    2 (small 3).toGeneric 4 (initState .standard 2 []) = none :=
  by decide +kernel

example : Interpreter.step ((8, ([] : List (List ℕ))),
    Interpreter.toTuple (initState .standard 2 [])) = none := rfl

/-- An out-of-range runtime label faults, with no unary expansion requirement in its certificate. -/
example : FiniteState.run (M := Basis.standard.genericModel) 1
    (Program.toGeneric (B := Basis.standard) ([.jump (2 ^ 100)] : Program .standard 2)) 2
    (initState .standard 2 []) = none := by decide +kernel

example (p : Program .standard 2) : Interpreter.parkRows 2 (ProgramLiterals.serialize p) =
    ProgramLiterals.serialize p.parkHalts := Interpreter.parkRows_serialize p

example : ∃ C d : ℕ, ∀ x : Interpreter.RunInput 2,
    Interpreter.clockedCertificate.time x ≤ 3 * (Interpreter.runInputEncoding 2 x).length +
      (x.1 + 1) * (C * (Interpreter.trajectoryLength x + 1) ^ d +
        Interpreter.trajectoryLength x + ((encNat x.1).length + 1) ^ 2) ∧
    Interpreter.clockedCertificate.space x ≤ 3 * (Interpreter.runInputEncoding 2 x).length +
      C * (Interpreter.trajectoryLength x + 1) ^ d + Interpreter.trajectoryLength x +
        (encNat x.1).length := Interpreter.clocked_resources 2

private def first : List (BitVec 3) := [1#3, 2#3, 4#3]
private def middle : List (BitVec 3) := [1#3]

/-- The very same finite-control source machine covers a colliding strict-inverse retained
class, real non-self-inverse additions, and exhaustive empty-quarter misses. -/
example : ∃ (c k : ℕ) (Q : Type) (_ : Finite Q) (machine : Turing.MultiTapeTM k Bool Q),
    (∃ ops : List Bool,
      machine.ComputesInTimeAndSpace
        (sourceEncoding (originalSource 2 first middle middle middle 1#3 2#3)) (true :: ops)
        (c * (sourceCertificate.time (originalSource 2 first middle middle middle 1#3 2#3) + 1))
        (c * (sourceCertificate.space (originalSource 2 first middle middle middle 1#3 2#3) + 1)) ∧
      ops.length = 6 ∧ eval (ops.zip ((first ++ middle) ++ (middle ++ middle))) 1#3 = 2#3) ∧
    machine.ComputesInTimeAndSpace
      (sourceEncoding (originalSource 1 [] [] [] [] 0#1 1#1)) []
      (c * (sourceCertificate.time (originalSource 1 [] [] [] [] 0#1 1#1) + 1))
      (c * (sourceCertificate.space (originalSource 1 [] [] [] [] 0#1 1#1) + 1)) := by
  obtain ⟨c, k, Q, hQ, machine, computes⟩ := original_machine
  refine ⟨c, k, Q, hQ, machine, ?_, ?_⟩
  · obtain ⟨out, run, miss, sound⟩ := computes 3 2 (by decide) first middle middle middle 1#3 2#3
    have sol : Solvable ((first ++ middle) ++ (middle ++ middle)) 1#3 2#3 :=
      ⟨decode 3 4 ++ decode 1 0 ++ decode 1 0 ++ decode 1 0, by decide, by decide +kernel⟩
    obtain ⟨ops, hout⟩ := Option.ne_none_iff_exists'.mp (fun h => miss.mp h sol)
    refine ⟨ops, ?_, (sound ops hout).1, (sound ops hout).2⟩
    simpa only [hout, encOption_some, encBits_apply] using run
  · obtain ⟨out, run, miss, _⟩ := computes 1 1 (by decide) [] [] [] [] 0#1 1#1
    have no : ¬Solvable (([] ++ []) ++ ([] ++ [])) 0#1 1#1 := by
      rintro ⟨ops, hlen, heval⟩
      have empty : ops = [] := List.length_eq_zero_iff.mp hlen
      subst ops
      exact (by decide : (0#1 : BitVec 1) ≠ 1#1) heval
    simpa only [miss.mpr no, encOption_none] using run

example : backwardCount middle middle 2#3 0#2 = 1 ∧
    forwardCount first middle 1#3 0#2 = 4 := by decide +kernel
