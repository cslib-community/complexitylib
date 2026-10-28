/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.GenericRAM.SparseMemory.Turing
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.IterateWhile

/-!
# Sparse memory examples and native machine certificates

Addresses are binary encoded and may be large despite a tiny store. Overwrites preserve its
cardinality; storing zero retains a binding. The native read certificate is uniform in the
input-supplied default. The examples also instantiate distinct address and value types.
-/

@[expose] public section

namespace ComplexityTests.SparseMemory

open Cslib.GenericRAM Cslib.GenericRAM.SparseMemory Turing.MultiTapeTM

/-- A large binary address that does not require a large store. -/
def high : ℕ := 2 ^ 128
/-- Two cells, one at a large address. -/
def sample : SparseMemory ℕ ℕ := ((∅ : SparseMemory ℕ ℕ).insert high 7).insert 3 11

example : entries sample = [(3, 11), (high, 7)] := by decide
example : read 19 4 sample = 19 := by decide
example : read 0 high sample = 7 := by decide
example : read 0 high (sample.insert high 0) = 0 := by decide
example : (entries (sample.insert high 0)).length = 2 := by decide
example : (entries (sample.insert 4 0)).length = 3 := by decide
example : read 91 high (∅ : SparseMemory ℕ ℕ) = 91 := rfl

-- No hypothesis restricts the numeric magnitude of the queried address.
example (a v d : ℕ) : read d a ((∅ : SparseMemory ℕ ℕ).insert a v) = v := by
  simpa using congrFun (read_insert d a v ∅) a

example : (encoding encNat encNat (∅ : SparseMemory ℕ ℕ)).length = 0 := rfl

example : ComputableTidilyInO
    (fun q : (ℕ × SparseMemory ℕ ℕ) × ℕ => read q.2 q.1.1 q.1.2)
    (readEncoding encNat encNat) encNat (readTime encNat encNat) (readSpace encNat encNat) :=
  read_inO encNat encNat

example : ComputableTidilyInO
    (fun q : (ℕ × Bool) × SparseMemory ℕ Bool => q.2.insert q.1.1 q.1.2)
    (writeEncoding encNat encBool) (encoding encNat encBool)
    (writeTime encNat encBool) (writeSpace encNat encBool) := insert_inO encNat encBool

example : ComputableTidilyInPolyTime
    (fun q : (ℕ × SparseMemory ℕ Bool) × Bool => read q.2 q.1.1 q.1.2)
    (readEncoding encNat encBool) encBool := by fun_prop

example : ComputableTidilyInPolyTime
    (fun q : (ℕ × Bool) × SparseMemory ℕ Bool => q.2.insert q.1.1 q.1.2)
    (writeEncoding encNat encBool) (encoding encNat encBool) := by fun_prop

-- Compose actual native machines: prepare the write, keep its address, then read it back.
example : ∃ T S, ComputableTidilyInO
    (fun q : (ℕ × ℕ) × SparseMemory ℕ ℕ => read 0 q.1.1 (q.2.insert q.1.1 q.1.2))
    (writeEncoding encNat encNat) encNat T S := by
  have hb := ComputableTidilyInO.fst (encPair encNat encNat) (encoding encNat encNat)
  have hw := insert_inO encNat encNat
  have hp := (hb.fst'.prod hw).prod
    (ComputableTidilyInO.const (encIn := writeEncoding encNat encNat) (encMid := encNat) 0)
  have h := (read_inO encNat encNat).comp hp
  exact ⟨_, _, h⟩

example (q : (ℕ × ℕ) × SparseMemory ℕ ℕ) :
    read 0 q.1.1 (q.2.insert q.1.1 q.1.2) = q.1.2 := by
  simpa using congrFun (read_insert 0 q.1.1 q.1.2 q.2) q.1.1

-- Extract an actual native finite-state machine that handles this concrete large-address input.
theorem large_address_native :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State)
      (t s : ℕ),
    tm.ComputesTidilyInTimeAndSpace (readEncoding encNat encNat ((high, sample), 0))
      (encNat 7) t s := by
  obtain ⟨c, ⟨k, State, hfinite, tm, htm⟩, _⟩ := read_inO encNat encNat
  refine ⟨k, State, hfinite, tm,
    c * (readTime encNat encNat ((high, sample), 0) + 1),
    c * (readSpace encNat encNat ((high, sample), 0) + 1), ?_⟩
  have h := htm ((high, sample), 0)
  have hr : read 0 high sample = 7 := by decide
  simpa only [hr] using h

/--
info: 'Cslib.GenericRAM.SparseMemory.read_insert' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.GenericRAM.SparseMemory.read_insert

end ComplexityTests.SparseMemory
