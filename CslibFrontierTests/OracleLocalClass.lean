/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.Oracle.LocalCircuit
import CslibFrontier.Computability.Circuit.Boolean.OracleFormula

/-!
# Tests: local classes of oracle formulas and oracle circuits

The measures of the circuit model on single gates: the locality bound sees oracle gates only, so
an AND gate has query arity zero although its fan-in is two. Every language is in a local circuit
class with one oracle gate reading the whole input, so the class is inhabited, and the formula
class is the generic class of the formula model by definition.
-/

namespace CslibFrontierTests.OracleLocalClass

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

/-- One oracle gate reading two inputs. -/
private def oneQuery : Circuit oracleSignature 2 1 := Circuit.oneGate (.query 2) ![0, 1]

example : circuitModel.size oneQuery = 1 := rfl

example : circuitModel.queryCount oneQuery = 1 := rfl

example : circuitModel.adaptivity oneQuery = 1 := by
  simp [circuitModel, oneQuery]

example : oneQuery.QueryArityAtMost 2 := by decide

example : ¬ oneQuery.QueryArityAtMost 1 := by decide

/-- One AND gate: fan-in two, but no oracle gate, so query arity zero. -/
private def oneAnd : Circuit oracleSignature 2 1 := Circuit.oneGate (.base .and) ![0, 1]

example : oneAnd.QueryArityAtMost 0 := by decide

example : ¬ oneAnd.FanInAtMost 1 := by decide

example : oneAnd.QueryArityAtMost 2 :=
  .of_fanInAtMost ((Circuit.fanInAtMost_oneGate _ _ _).2 le_rfl)

/-- Every language is in `[1, m, 1]–Circuit[1]`: its own oracle, queried once on the whole input. -/
example (L : Language Bool) :
    LocalCircuitClass (fun _ => 1) (fun m => m) (fun _ => 1) (fun _ => 1) L {w | w ∉ L} := by
  refine ⟨L, fun m => ⟨Circuit.oneGate (.query m) id, ?_, ?_, ?_, ?_, fun x hx => ?_,
    fun x hx => ?_⟩⟩
  · rfl
  · exact (Circuit.cost_program_oneGate (σ := oracleSignature) (.query m) id
      OracleOp.queryWeight).le
  · exact (Circuit.queryArityAtMost_oneGate _ _ _).2 le_rfl
  · simp [circuitModel]
  · simpa [circuitModel] using hx
  · simp only [circuitModel, Circuit.eval_oneGate, oracleInterpretation_query]
    exact Bool.eq_false_iff.2 fun h => hx (Language.slice_eq_true_iff.1 h)

/-- `LocalFormulaClass` is `OracleModel.LocalClass` for `formulaModel`, by definition, and unfolds
to the explicit statement of #4388. -/
example (q ℓ a S : ℕ → ℕ) (Yes No : Language Bool) :
    LocalFormulaClass q ℓ a S Yes No ↔
      ∃ O : Language Bool, ∀ m, ∃ E : OracleFormula m,
        E.leafSize ≤ S m ∧ OracleFormula.queryCount E ≤ q m ∧
          OracleFormula.maxQueryArity E ≤ ℓ m ∧ OracleFormula.adaptivity E ≤ a m ∧
          (∀ x : Fin m → Bool, List.ofFn x ∈ Yes → E.eval (oracleInterpretation O) x = true) ∧
          (∀ x : Fin m → Bool, List.ofFn x ∈ No → E.eval (oracleInterpretation O) x = false) :=
  Iff.rfl

/-- The class lemmas apply to `LocalFormulaClass` by dot notation through the abbreviation. -/
example {q ℓ a S : ℕ → ℕ} {Yes No : Language Bool} (h : LocalFormulaClass q ℓ a S Yes No) :
    LocalFormulaClass (q + 1) ℓ a S Yes ⊥ :=
  (h.anti le_rfl bot_le).mono (fun _ => Nat.le_succ _) le_rfl le_rfl le_rfl

end CslibFrontierTests.OracleLocalClass
