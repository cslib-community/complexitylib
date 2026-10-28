/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.IP.Shamir
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests: the interactive proof for quantified Boolean formulas

The arithmetization of concrete closed formulas over `ZMod 7`, prenex and not, with their values
at the origin and their round degrees; the variables and the size of a formula; perfect
completeness on a true formula and a concrete soundness bound below `1` on a false one over
`ZMod 101`, against every prover; the decision of closedness and the parameters of the machine
verifier on concrete formulas; `TQBF ∈ IP`, `IP = PSPACE` and its corollaries; and the axioms of
the headline theorems.
-/

namespace ComplexityTests.QBFProtocol

open Cslib Cslib.Complexity Cslib.Logic.PL Cslib.Complexity.QBFProtocol
open Cslib.ProbOracleComp (acceptProbWith)
open scoped ENNReal

/-- `∀ x, ∃ y, x ↔ y`, with `x = 0` and `y = 1`. -/
private def forallExistsIff : QBF ℕ := .all 0 (.ex 1 (QBF.or (.and (.var 0) (.var 1))
  (.and (.not (.var 0)) (.not (.var 1)))))

/-- `∀ x, x`, a false closed formula. -/
private def forallVar : QBF ℕ := .all 0 (.var 0)

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

instance : Fact (Nat.Prime 101) := ⟨by norm_num⟩

/-! ### Arithmetization -/

example : forallExistsIff.vars = [0, 1, 0, 1, 0, 1] := rfl

example : forallExistsIff.size = 11 := rfl

/-- The arithmetization of a true closed formula has value `1` at the origin. -/
example : ((QBF.all 0 (.ex 1 ((QBF.var 0).or (.var 1)))).arithmetize [0, 1]).eval
    (0 : ℕ → ZMod 7) = 1 := by
  decide

/-- The arithmetization of a false closed formula has value `0` at the origin. -/
example : (forallVar.arithmetize forallVar.vars).eval (0 : ℕ → ZMod 7) = 0 := by decide

/-- A formula not in prenex form: `(∃ x, x) ∧ ¬∀ y, y`. -/
example : (((QBF.ex 0 (.var 0)).and (QBF.all 1 (.var 1)).not).arithmetize [0, 1]).eval
    (0 : ℕ → ZMod 7) = 1 := by
  decide

/-- Away from `0`-`1` points the value is not a truth value: linearizing `x` in the formula `x ∧ x`
gives `x`, while `x ∧ x` itself has value `x * x`. -/
example : ((QBF.and (.var 0) (.var 0)).arithmetize []).eval (fun _ => (3 : ZMod 7)) = 2 := by
  decide

example : (ArithQBF.op .lin 0 ((QBF.and (.var 0) (.var 0)).arithmetize [])).eval
    (fun _ => (3 : ZMod 7)) = 3 := by
  decide

/-- The round degrees of a concrete arithmetization, within the bound
`(2 * |xs| + 1) * size ^ 2 = 1573`. -/
example : (forallExistsIff.arithmetize forallExistsIff.vars).roundDegree = 19 := by decide

example : (2 * forallExistsIff.vars.length + 1) * forallExistsIff.size ^ 2 = 1573 := by decide

/-! ### Completeness and soundness -/

example : forallExistsIff ∈ TQBF := ⟨by decide, rfl⟩

example : forallVar ∉ TQBF := fun h => absurd h.2 (by decide)

/-- The honest prover is accepted on a true formula with probability `1`. -/
example (sampler : ProbComp (ZMod 7)) :
    acceptProbWith honest
      (verify sampler (forallExistsIff.arithmetize forallExistsIff.vars) 0 1) () = 1 :=
  acceptProb_honest_of_mem_TQBF sampler ⟨by decide, rfl⟩

/-- On a false formula of size `2`, over `ZMod 101`, no prover is accepted with probability more
than `24 / 101`. -/
example {S : Type} (respond : Query ℕ (ZMod 101) → StateT S PMF (List (ZMod 101))) (s : S) :
    acceptProbWith respond
      (verify (ProbComp.uniform (ZMod 101)) (forallVar.arithmetize forallVar.vars) 0 1) s ≤
        24 / 101 := by
  refine (acceptProb_le_of_notMem_TQBF (by decide) (fun h => absurd h.2 (by decide)) respond
    s).trans_eq ?_
  rw [ZMod.card]
  rfl

example : (24 : ℝ≥0∞) / 101 < 1 := by
  rw [ENNReal.div_lt_iff (by norm_num) (by norm_num)]
  norm_num

/-- The general soundness bound applies to the prover that always replies with the empty list. -/
example (e : ArithQBF ℕ) (r : ℕ → ZMod 101) (c : ZMod 101) (hc : e.eval r ≠ c) :
    acceptProbWith (fun _ (s : Unit) => PMF.pure ([], s))
      (verify (ProbComp.uniform (ZMod 101)) e r c) () ≤ e.roundDegree / 101 :=
  (acceptProb_verify_uniform_le _ e hc ()).trans_eq (by rw [ZMod.card, Nat.cast_ofNat])

/-! ### The machine verifier -/

example : QBF.isClosed (QBF.ex 0 (.var 0)).tokens = true := by decide

example : QBF.isClosed (QBF.all 1 (.var 0)).tokens = false := by decide

example : QBF.isClosed forallExistsIff.tokens = true := by decide

/-- The parameters on `∃ x, x`: two tokens, so `D = 4`, and a prime modulus above `144`. -/
example : linVars (QBF.ex 0 (.var 0)) = [0, 0] := rfl

example : degreeBound (QBF.ex 0 (.var 0)) = 4 := rfl

example : primeBound (QBF.ex 0 (.var 0)) = 144 := rfl

/-- A formula with a free variable is rejected without interaction. -/
example : verifier (QBF.var 0) = pure false := by
  rw [verifier, decide_eq_false (by decide)]
  rfl

example : TQBFᶜ ∈ IP encQBF :=
  IP_eq_PSPACE encQBF ▸ compl_mem_PSPACE (IP_eq_PSPACE encQBF ▸ TQBF_mem_IP)

example {α : Type} (enc : α ↪ List Bool) {A : Set α} (hA : A ∈ coNP enc) : Aᶜ ∈ IP enc :=
  IP_eq_PSPACE enc ▸ compl_mem_PSPACE (IP_eq_PSPACE enc ▸ coNP_subset_IP enc hA)

example {α : Type} (enc : α ↪ List Bool) (k : ℕ) : SigmaP k enc ⊆ PSPACE enc :=
  IP_eq_PSPACE enc ▸ (SigmaP_subset_PH k).trans (PH_subset_IP enc)

/-! ### Axioms -/

/--
info: 'Cslib.Logic.PL.QBF.degBound_arithmetize_le' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.QBF.degBound_arithmetize_le

end ComplexityTests.QBFProtocol
