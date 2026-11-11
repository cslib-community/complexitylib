/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

-- Evaluate the actual precheck/projected-DP/readback bodies on original finite inputs.
import all CslibFrontier.Cryptanalysis.AddXNORSmallDP
-- Evaluate the threshold scan and native original-input preparation, excluding the seed.
import all CslibFrontier.Cryptanalysis.AddXNORSmallAutomatic

/-!
# Small-operand native decision and resource clients

The large seed is unrestricted. Low-bit aliases must be rejected by the scalar
check; wraparound and XNOR hits must be retained. No supplied projected answer,
runtime, completed table or witness is an endpoint premise.
-/

public section
namespace CslibFrontierTests.AddXNORSmallDP
open Turing.MultiTapeTM Cslib.Cryptanalysis.AddXNOR

/-- A 32-bit full-state array would be enormous; the actual projected DP has only 32 entries. -/
example : SmallDP.run (SmallDP.ofWords 1 4294967295#32 [1#32]) = true := by decide
example : SmallDP.run (SmallDP.ofWords 1 0#8 [1#8]) = false := by decide
example : SmallDP.run (SmallDP.ofWords 0 16#8 [0#8]) = false := by decide
/-- Projection alone accepts this high-seed alias; the original instance has no solution. -/
example : SmallDP.readZero (CounterProjection.run
    (SmallDP.prepare (SmallDP.ofWords 0 16#8 [0#8]))) = true := by decide
example : SmallDP.near (SmallDP.ofWords 0 16#8 [0#8]) = false := by decide
example : SmallDP.run (SmallDP.ofWords 0 255#8 [0#8]) = true := by decide
example : SmallDP.run (SmallDP.ofWords 0 0#0 [0#0, 0#0]) = true := by decide
example : SmallDP.run (SmallDP.ofWords 0 0#8 []) = true := by decide
example : SmallDP.run (SmallDP.ofWords 0 255#8 []) = false := by decide
example : SmallDP.run (SmallDP.ofWords 12 0#1 [1#1]) = true := by decide

example {m : ℕ} (s : ℕ) (seed : BitVec m) (as : List (BitVec m))
    (small : ∀ a ∈ as, a.toNat < 2 ^ s) :
    SmallDP.run (SmallDP.ofWords s seed as) = true ↔ Solvable as seed 0 :=
  SmallDP.original_correct s seed as small

example : IsComputable SmallDP.run SmallDP.encoding encBool := SmallDP.runCertificate.isComputable

example : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∀ m s (seed : BitVec m) (as : List (BitVec m)),
      SmallDP.runCertificate.time (SmallDP.ofWords s seed as) ≤ 2^s*P (m+s+as.length+1) ∧
      SmallDP.runCertificate.space (SmallDP.ofWords s seed as) ≤ 2^s*P (m+s+as.length+1) :=
  SmallDP.source_parameter_bounds

example : SmallAutomatic.computedBound ((32, 4294967295), [1]) = 1 := by decide
example : SmallAutomatic.run ((32, 4294967295), [1]) = true := by decide
example : SmallAutomatic.run ((8, 16), [0]) = false := by decide
example : SmallAutomatic.run ((8, 255), []) = false := by decide
example : SmallAutomatic.run ((0, 0), [0, 0]) = true := by decide

/-- The installed front end needs no bound as input, even in its correctness theorem. -/
example {m : ℕ} (seed : BitVec m) (as : List (BitVec m)) :
    SmallAutomatic.run ((m, seed.toNat), as.map BitVec.toNat) = true ↔ Solvable as seed 0 :=
  SmallAutomatic.original_correct seed as

example : IsComputable SmallAutomatic.run SortedQuarterMachine.encoding encBool :=
  SmallAutomatic.runCertificate.isComputable

example : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∀ m s (seed : BitVec m) (as : List (BitVec m)), (∀ a ∈ as, a.toNat < 2^s) →
      SmallAutomatic.runCertificate.time ((m, seed.toNat), as.map BitVec.toNat) ≤
        2^s*P (m+as.length+1) ∧
      SmallAutomatic.runCertificate.space ((m, seed.toNat), as.map BitVec.toNat) ≤
        2^s*P (m+as.length+1) :=
  SmallAutomatic.source_parameter_bounds

end CslibFrontierTests.AddXNORSmallDP
