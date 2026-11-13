/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.PolyTime.CountingLeaf.RawCost

namespace CslibFrontierTests.CountingLeafRawCost

open Cslib.CountingLeaf Turing Turing.MultiTapeTM

theorem true_inO : ComputableInO (fun _ : List Bool × ℕ => true)
    (encPair encBits encNat) encBool (fun _ => 0) (fun _ => 0) := by
  obtain ⟨c, h⟩ := computableInTimeAndSpace_of_const
    (encIn := encPair encBits encNat) (encOut := encBool) true
  exact .of_bounds h (c + 1) (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)

def query (context : List Bool) (active carry : Bool) : RawInput :=
  ⟨context, if active then [true, false, false] else [], [true, false],
    [false, false], carry, [false, false]⟩

private theorem query_size (context : List Bool) (active carry : Bool) :
    (query context active carry).localSize ≤ 10 := by
  cases active <;> simp [query, RawInput.localSize]

theorem query_answer (context : List Bool) (active carry : Bool) :
    runRaw (fun _ => true) (query context active carry) = (active && !carry) := by
  cases active <;> cases carry <;>
    simp [runRaw, run, RawInput.normalize, query, Cslib.BitString.binaryValue, ofBits]

-- A constant-time primitive predicate does not pay for the arbitrarily long context itself.
-- The actual leaf machine adds that cost linearly, handles padded numeric words, and rejects
-- either an empty count or the carry component. One machine and both constants are uniform.
example : ∃ (d c k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
    ∀ (context : List Bool) (active carry : Bool),
      tm.ComputesInTimeAndSpace (encRawInput (query context active carry)) [active && !carry]
        (c * (context.length + 11 ^ d + 1))
        (c * (context.length + 11 ^ d + 1)) := by
  obtain ⟨d, c, ⟨k, State, hState, tm, htm⟩, _⟩ :=
    computableInO_runRaw (fun _ => true) true_inO
  refine ⟨d, c, k, State, hState, tm, ?_⟩
  intro context active carry
  have hp : ((query context active carry).localSize + 1) ^ d ≤ 11 ^ d :=
    Nat.pow_le_pow_left (by have := query_size context active carry; omega) d
  have h := htm (query context active carry)
  rw [query_answer] at h
  refine ⟨h.1, h.2.1.mono ?_, h.2.2.mono ?_⟩ <;>
    apply Nat.mul_le_mul_left <;> change context.length + _ + 0 + 1 ≤ _ <;> omega

end CslibFrontierTests.CountingLeafRawCost
