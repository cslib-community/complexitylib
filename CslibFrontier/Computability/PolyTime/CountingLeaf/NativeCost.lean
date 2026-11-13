/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CountingLeaf.Native
public import CslibFrontier.Computability.PolyTime.CountingLeaf.RawCost

/-!
# Physical counting leaves with an input-indexed predicate clock

The exact serializer and work-tape runner retain the raw evaluator's additive context cost.
Only the local fields enter the polynomial overhead. The primitive predicate's own time is
charged at the decoded path; its workspace need not be bounded by that supplied time function.
-/

public section

namespace Cslib.CountingLeaf.Native

open Turing Turing.MultiTapeTM

/-- Physical serialization followed by the context-linear raw evaluator. -/
@[expose] def cost (c d : ℕ) (T : List Bool × ℕ → ℕ) (q : RawInput) : ℕ :=
  2 * (encRawInput q).length + 5 +
    c * (q.context.length + (q.localSize + 1) ^ d +
      T (q.context, BitString.binaryValue q.path) + 1)

/-- A primitive predicate with separate time and workspace bounds gives one physical counting
leaf machine. The clock includes query construction, normalization, execution and cleanup. -/
theorem exists_counting_of_inO (predicate : List Bool × ℕ → Bool)
    {T S : List Bool × ℕ → ℕ}
    (hp : ComputableInO predicate (encPair encBits encNat) encBool T S) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State)
      (tm : MultiTapeTM (6 + (k + 2)) Bool State) (c d : ℕ),
      ∀ (q : RawInput) (input : List Bool),
        tm.runFrom ((initial k input q).withState (some tm.q₀)) (cost c d T q) =
          (final k input q [runRaw predicate q]).withState none := by
  obtain ⟨d, hraw⟩ := computableInO_runRaw predicate hp
  obtain ⟨k, State, hState, runner, c, hr⟩ := WorkTapePredicate.exists_of_inO hraw
  let := hState
  refine ⟨k, _, inferInstance, machine runner, c, d, ?_⟩
  intro q input
  exact runFrom_machine runner q input (runRaw predicate q) _ (hr q input)

end Cslib.CountingLeaf.Native
