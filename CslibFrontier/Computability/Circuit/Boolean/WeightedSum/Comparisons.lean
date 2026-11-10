/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.WeightedSum.Circuit

/-!
# Functional 3-CNF for polynomial-weight comparisons

The actual grouped circuits implement all three comparisons of [ChenJiangZhu2027], Lemma A.1
(PDF pp.28–29), and the two strict comparisons by integer target shifts. Weights are explicitly
nonnegative, bounded by n^c for a fixed natural exponent c; signed literals share the original
inputs. A real fixed exponent can be enlarged to an integral one for n≥1. Zero/one inputs are
included. Full truth tables preserve exactly one extension, also with an arbitrary correlated
predicate on the original assignments.

These are executable circuit/CNF constructors with explicit linear gate and clause counts.
They do not yet certify binary generation time or the Corollary A.2 counting/distribution machine.

## Main definitions

* `Comparison`: weak, equality and strict integer comparisons.
* `test`, `formula`: actual circuit and full functional 3-CNF constructors.

## Main results

* `eval_test`, `eval_formula_iff`, `count_formula`: exact original semantics and unique extensions.
* `linear_bounds`: actual linear gates/clauses, width three and bounded literal indices.
-/

public section

namespace Cslib.Circuits.Boolean.WeightedSum

/-- All integer comparison modes, including target-shifted strict comparisons. -/
inductive Comparison where
  | le | ge | eq | lt | gt
  deriving DecidableEq, Repr

/-- Ordinary integer relation, with no modular or truncated interpretation. -/
abbrev Comparison.Holds : Comparison → ℤ → ℤ → Prop
  | .le, a, b => a ≤ b
  | .ge, a, b => b ≤ a
  | .eq, a, b => a = b
  | .lt, a, b => a < b
  | .gt, a, b => b < a

instance (op : Comparison) (a b : ℤ) : Decidable (op.Holds a b) := by
  cases op <;> unfold Comparison.Holds <;> infer_instance

private def negate {n : ℕ} (c : Circuit signature n 1) : Circuit signature n 1 :=
  (Circuit.oneGate (σ := signature) Op.not (fun _ => (0 : Fin 1))).comp c

private def both {n : ℕ} (a b : Circuit signature n 1) : Circuit signature n 1 :=
  ((Formula.input (0 : Fin 2)).and (Formula.input 1)).toCircuit.comp (a.append b)

private theorem eval_negate {n : ℕ} (c : Circuit signature n 1) (x : BitString n) :
    (negate c).eval interpretation x = fun _ => !(c.eval interpretation x 0) := by
  simp only [negate, Circuit.eval_comp]
  rfl

private theorem eval_both {n : ℕ} (a b : Circuit signature n 1) (x : BitString n) :
    (both a b).eval interpretation x = fun _ =>
      a.eval interpretation x 0 && b.eval interpretation x 0 := by
  simp only [both, Circuit.eval_comp, Circuit.eval_append]
  rfl

/-- Actual integer comparison circuit. Equality uses two independently functional sums; the
constant number of copies preserves the linear budget and cannot add extension multiplicity. -/
def test {n : ℕ} (op : Comparison) (c : ℕ) (weights : Fin n → ℕ)
    (positive : Fin n → Bool) (target : ℤ) : Circuit signature n 1 :=
  match op with
  | .le => leCircuit c weights positive target
  | .ge => negate (leCircuit c weights positive (target - 1))
  | .eq => both (leCircuit c weights positive target)
      (negate (leCircuit c weights positive (target - 1)))
  | .lt => leCircuit c weights positive (target - 1)
  | .gt => negate (leCircuit c weights positive target)

/-- All ordinary integer comparisons, with strictness normalized without off-by-one loss. -/
theorem eval_test {n : ℕ} (op : Comparison) (c : ℕ) (weights : Fin n → ℕ)
    (positive x : Fin n → Bool) (target : ℤ) (hw : ∀ i, weights i ≤ n ^ c) :
    (test op c weights positive target).eval interpretation x =
      fun _ => decide (op.Holds (value weights positive x) target) := by
  cases op <;> simp only [test, eval_both, eval_negate, eval_leCircuit c weights positive x _ hw]
  all_goals
    funext j
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not, Comparison.Holds]; omega

/-- Concrete gate constant for each fixed coefficient exponent and every comparison mode. -/
@[expose] def comparisonBudget (c : ℕ) : ℕ :=
  2 * (sumBudget c + 5 * (4 * c + 5) + 3) + 2

/-- No runtime target magnitude enters the linear auxiliary-variable count. -/
theorem size_test_linear {n : ℕ} (op : Comparison) (c : ℕ) (weights : Fin n → ℕ)
    (positive : Fin n → Bool) (target : ℤ) :
    (test op c weights positive target).size ≤ comparisonBudget c * (n + 1) := by
  have h1 := size_leCircuit_linear c weights positive target
  have h2 := size_leCircuit_linear c weights positive (target - 1)
  cases op <;> simp only [test, negate, both, Circuit.size_comp, Circuit.size_oneGate,
    Circuit.size_append, Formula.size_toCircuit, Formula.size_and, Formula.size_input]
  all_goals unfold comparisonBudget; nlinarith

/-- Actual full truth-table writing; no satisfying gate assignment is supplied. -/
@[expose] def formula {n : ℕ} (op : Comparison) (c : ℕ) (weights : Fin n → ℕ)
    (positive : Fin n → Bool) (target : ℤ) : Logic.PL.CNF ℕ :=
  FunctionalCNF.write (FunctionalCNF.ofCircuit (test op c weights positive target) (fun _ => true))

/-- Precisely the deterministic gate trace extends an input, and only if its comparison holds. -/
theorem eval_formula_iff {n : ℕ} (op : Comparison) (c : ℕ) (weights : Fin n → ℕ)
    (positive x : Fin n → Bool) (target : ℤ) (hw : ∀ i, weights i ≤ n ^ c)
    (σ : ℕ → Bool) (hin : ∀ i : Fin n, σ i.val = x i) :
    (formula op c weights positive target).eval σ = true ↔
      (∀ j : Fin (n + (test op c weights positive target).size), σ j.val =
        FunctionalCNF.wireValues (test op c weights positive target) x j) ∧
      op.Holds (value weights positive x) target := by
  rw [formula, FunctionalCNF.eval_write_iff _ _ x σ hin,
    eval_test op c weights positive x target hw]
  simp only [funext_iff, Fin.forall_fin_one, decide_eq_true_eq]

open Classical in
/-- Parsimonious on the original inputs even when a separate predicate correlates their values.
This never removes annotation multiplicity already present in that predicate. -/
theorem count_formula {n : ℕ} (op : Comparison) (c : ℕ) (weights : Fin n → ℕ)
    (positive : Fin n → Bool) (target : ℤ) (hw : ∀ i, weights i ≤ n ^ c)
    (P : (Fin n → Bool) → Prop) :
    Fintype.card {y : Fin (n + (test op c weights positive target).size) → Bool //
      (formula op c weights positive target).eval
        (Function.extend Fin.val y (fun _ => false)) = true ∧
        P (fun i => y (Fin.castAdd (test op c weights positive target).size i))} =
      Fintype.card {x : Fin n → Bool // op.Holds (value weights positive x) target ∧ P x} := by
  calc _ = Fintype.card {x : Fin n → Bool //
        (test op c weights positive target).eval interpretation x = (fun _ => true) ∧ P x} :=
          FunctionalCNF.count_extensions _ _ P
    _ = _ := Fintype.card_congr (Equiv.subtypeEquivRight fun x => by
      rw [eval_test op c weights positive x target hw]
      simp only [funext_iff, Fin.forall_fin_one, decide_eq_true_eq])

/-- The complete actual written formula has linear gates/clauses, width three and valid indices. -/
theorem linear_bounds {n : ℕ} (op : Comparison) (c : ℕ) (weights : Fin n → ℕ)
    (positive : Fin n → Bool) (target : ℤ) :
    (test op c weights positive target).size ≤ comparisonBudget c * (n + 1) ∧
    (formula op c weights positive target).length ≤ 1 + 3 * comparisonBudget c * (n + 1) ∧
    (∀ clause ∈ formula op c weights positive target, clause.length ≤ 3) ∧
    (∀ clause ∈ formula op c weights positive target, ∀ l ∈ clause,
      l.1 < n + (test op c weights positive target).size) := by
  have hs := size_test_linear op c weights positive target
  refine ⟨hs, ?_, ?_, ?_⟩
  · rw [formula, FunctionalCNF.write_length]
    nlinarith
  · intro clause hc
    exact (FunctionalCNF.write_bounds _ _ clause hc).1.le
  · intro clause hc
    exact (FunctionalCNF.write_bounds _ _ clause hc).2

end Cslib.Circuits.Boolean.WeightedSum
