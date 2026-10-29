/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT
public import Complexity.Logics.Propositional.CNF.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# A native syntax guard for finite 3SAT-3

The scan checks clause widths and counts literal positions, including repetitions. It makes no
satisfiability or planarity assertion. Total reductions use it to reject inputs outside their
source syntax.

## Main definitions

* `Cslib.Complexity.ThreeSATThree.syntaxCheck`: the Boolean guard.

## Main results

* `Cslib.Complexity.ThreeSATThree.syntaxCheck_iff`: exact width and literal-count semantics.
* `Cslib.Complexity.ThreeSATThree.computableInPolyTime_syntaxCheck`: native polynomial time.

## References

Uses the existing CNF list representation and binary formula encoding.
-/

@[expose] public section
namespace Cslib.Complexity.ThreeSATThree
open Cslib.Logic.PL Turing.MultiTapeTM

/-- Check width and literal-occurrence bounds three, independently of satisfiability. -/
def syntaxCheck (φ : CNF ℕ) : Bool :=
  (φ.all fun c => decide (c.length ≤ 3)) &&
    (φ.vars.all fun v => decide (φ.vars.count v ≤ 3))

/-- The finite scan checks exactly the two syntactic restrictions of 3SAT-3. -/
theorem syntaxCheck_iff (φ : CNF ℕ) :
    syntaxCheck φ = true ↔
      (∀ c ∈ φ, c.length ≤ 3) ∧ (∀ v, φ.vars.count v ≤ 3) := by
  simp only [syntaxCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hw, hv⟩
    refine ⟨hw, fun v => ?_⟩
    by_cases hm : v ∈ φ.vars
    · exact hv v hm
    · simp [List.count_eq_zero.mpr hm]
  · exact fun h => ⟨h.1, fun v _ => h.2 v⟩

/-- The syntactic guard is computed in native polynomial time under binary CNF encoding. -/
@[fun_prop]
theorem computableInPolyTime_syntaxCheck :
    ComputableInPolyTime syntaxCheck encCNF encBool := by
  unfold syntaxCheck encCNF
  simp only [List.count_eq_countP]
  fun_prop

end Cslib.Complexity.ThreeSATThree
