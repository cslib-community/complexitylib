import Complexity.Logics.BooleanClone.Formula
import Complexity.Logics.Polymorphism.BooleanClone

/-! Post's criterion uses the same clone interface as Schaefer, at every positive arity. -/

open Cslib.Logic Cslib.Logic.BooleanClone Cslib.Circuits

private def nand (a : Fin 2 → Bool) : Bool := !(a 0 && a 1)

private def nandBasis : (n : ℕ) → Set ((Fin n → Bool) → Bool)
  | 2 => {nand}
  | _ => ∅

private theorem nand_criterion : PostCriterion nandBasis := by
  refine ⟨⟨2, by decide, nand, rfl, by decide⟩,
    ⟨2, by decide, nand, rfl, by decide⟩,
    ⟨2, by decide, nand, rfl, by decide⟩,
    ⟨2, by decide, nand, rfl, by decide⟩,
    ⟨2, by decide, nand, rfl, by decide⟩⟩

-- A single binary connective supplies all five witnesses.
example : FunctionallyComplete nandBasis :=
  (functionallyComplete_iff nandBasis).mpr nand_criterion

-- Construct a NAND formula for XOR and check its output on two concrete inputs.
example : ∃ F : Formula (signature nandBasis) 2,
    F.Computes (interpretation nandBasis) (fun a : Fin 2 → Bool => a 0 ^^ a 1) ∧
      F.eval (interpretation nandBasis) ![false, true] = true ∧
      F.eval (interpretation nandBasis) ![true, true] = false := by
  obtain ⟨F, hF⟩ := exists_formula_of_postCriterion nand_criterion (by decide : 0 < 2)
    (fun a : Fin 2 → Bool => a 0 ^^ a 1)
  exact ⟨F, hF, hF _, hF _⟩

-- The theorem constructs circuits for functions of arity beyond the binary/ternary proof cases.
example : ∃ c : Circuit (signature nandBasis) 7 1,
    c.Computes (interpretation nandBasis) (single (fun a => if a 0 then a 3 else a 6)) :=
  exists_circuit_of_postCriterion nand_criterion (by decide) _

-- The affine family includes constants, NOT and XOR, but cannot be complete.
example : ¬ FunctionallyComplete
    (fun n => {f : (Fin n → Bool) → Bool | Cslib.BitString.IsAffine f}) := by
  intro h
  obtain ⟨n, hn, f, hf, hbad⟩ := ((functionallyComplete_iff _).mp h).2.2.2.2
  exact hbad hf

-- Monotone gates cannot generate NOT, even when constants are included.
example : ¬ FunctionallyComplete (fun n => {f : (Fin n → Bool) → Bool | Monotone f}) := by
  intro h
  obtain ⟨n, hn, f, hf, hbad⟩ := ((functionallyComplete_iff _).mp h).2.2.1
  exact hbad hf

-- NAND has no zero-input circuit despite its positive-arity functional completeness.
example : ¬ (interpretation nandBasis).IsComplete := not_isComplete_interpretation nandBasis

-- Reuse the extracted Schaefer classification unchanged with the generated NAND clone.
example : andOp ∈ (generated nandBasis).operations 2 :=
  ((functionallyComplete_iff _).mpr nand_criterion) 2 (by decide) andOp
