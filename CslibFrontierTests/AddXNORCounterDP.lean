/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import all CslibFrontier.Cryptanalysis.AddXNORCounterDPResources

/-!
# Original-input reachable-state counting clients

Execute initialization, repeated pull/pair/add updates and numeric reindexing.
The reverse client distinguishes inverse addition and reverse operand order.
Physical zeros, empty chains and indexed multiplicity are retained in the output.
-/

public section
open Turing.MultiTapeTM Cslib.Cryptanalysis.AddXNOR
namespace CslibFrontierTests.AddXNORCounterDP

example : CounterInitialization.run (0, 17) = [(0, 1)] := by decide
example : CounterInitialization.run (2, 1) = [(0, 0), (1, 1), (2, 0), (3, 0)] := by decide
example : IndexNat.run [0, 7, 7, 0] = [(0, 0), (1, 7), (2, 7), (3, 0)] := rfl
example : IndexNat.run [] = [] := rfl

example : CounterDP.run (CounterDP.ofWords false 0#0 [0#0, 0#0, 0#0]) = [(0, 8)] := by decide
example : CounterDP.run (CounterDP.ofWords true 0#0 [0#0, 0#0, 0#0]) = [(0, 8)] := by decide
example : CounterDP.run (CounterDP.ofWords false 1#2 []) =
    [(0, 0), (1, 1), (2, 0), (3, 0)] := by decide
example : CounterDP.run (CounterDP.ofWords true 1#2 []) =
    [(0, 0), (1, 1), (2, 0), (3, 0)] := by decide

/-- Non-self-inverse addition and the reverse operand loop give different full tables. -/
example : CounterDP.run (CounterDP.ofWords false 0#3 [1#3, 2#3]) =
    [(0, 1), (1, 0), (2, 0), (3, 2), (4, 1), (5, 0), (6, 0), (7, 0)] := by decide
example : CounterDP.run (CounterDP.ofWords true 0#3 [1#3, 2#3]) =
    [(0, 1), (1, 0), (2, 0), (3, 1), (4, 1), (5, 1), (6, 0), (7, 0)] := by decide

/-- General correctness uses the original chain, including multiplicities. -/
example {m : ℕ} (as : List (BitVec m)) (seed : BitVec m) (inverse : Bool) :
    CounterDP.run (CounterDP.ofWords inverse seed as) = CounterPull.graph
      (if inverse then WordTable.backwardCounters as seed
        else WordTable.classCounters as seed).read := CounterDP.run_words as seed inverse

/-- One fixed native machine handles original inputs of every width and length. -/
example : Turing.MultiTapeTM.IsComputable CounterDP.run CounterDP.encoding encNatPairList :=
  CounterDP.runCertificate.isComputable

/-- Every prefix, including saturated lengths, has the original-width wire bound. -/
example {m : ℕ} (as : List (BitVec m)) (seed : BitVec m) (j : ℕ) :
    (encNatPairList
      (((CounterDP.orderedOperands (CounterDP.ofWords true seed as)).take j).foldl
        (CounterDP.step (m, true)) (CounterInitialization.run (m, seed.toNat)))).length ≤
      2^m*(4*m+2*as.length+5) := CounterDP.prefix_wire as seed true j

/-- Initialization has an actual uniform exponential-in-width resource witness. -/
example : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    Turing.MultiTapeTM.ComputableInO CounterInitialization.run CounterInitialization.encoding
      encNatPairList
      (fun input => 2^input.1*P ((CounterInitialization.encoding input).length+1))
      (fun input => 2^input.1*P ((CounterInitialization.encoding input).length+1)) :=
  CounterInitialization.run_computable

/-- General source resources for the actual installed machine, without a runtime premise. -/
example : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∀ m (as : List (BitVec m)) (seed : BitVec m) (inverse : Bool),
      CounterDP.runCertificate.time (CounterDP.ofWords inverse seed as) ≤
        2^m*P (m+as.length+1) ∧
      CounterDP.runCertificate.space (CounterDP.ofWords inverse seed as) ≤
        2^m*P (m+as.length+1) := CounterDP.source_certificate

end CslibFrontierTests.AddXNORCounterDP
