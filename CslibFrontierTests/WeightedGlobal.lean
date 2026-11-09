/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import CslibFrontier.Logics.Propositional.CNF.WeightedGlobal
import CslibFrontier.Logics.Propositional.CNF.WeightedNormalization

/-! # Global weighted query clients, including cross-row duplicates -/

open Cslib.Logic.PL Cslib.Logic.PL.WeightedRow

namespace WeightedGlobalTests

/-- Demand zero with two opposite-polarity variables. -/
def row : Row Bool 0 where
  support := Finset.univ
  sign := id
  weight := fun _ => 1
  demand := 0
  positive := by intros; decide
  bounded := by decide
  capped := by intros; decide

example : upperKeys (fun _ : Fin 2 => row) = upperKeys (fun _ : Fin 1 => row) := by
  ext s
  simp [upperKeys, base, List.mem_flatMap]

example : (globalBase (fun _ : Fin 2 => row)).length =
    (globalBase (fun _ : Fin 1 => row)).length := by
  have he : upperKeys (fun _ : Fin 2 => row) = upperKeys (fun _ : Fin 1 => row) := by
    ext s
    simp [upperKeys, base, List.mem_flatMap]
  simp only [globalBase, he]

example : (globalBase (fun _ : Fin 2 => row)).eval Bool.not = true := by
  rw [globalBase_upper_eval]
  simp [row, Row.value, Row.active]

example : (globalBase (fun _ : Fin 2 => row)).eval id = false := by
  apply Bool.eq_false_iff.mpr
  simp only [ne_eq, globalBase_upper_eval]
  simp [row, Row.value, Row.active]

example (β : Bool) : (globalQuery (fun _ : Fin 2 => row) β).length ≤ 14 := by
  have hb := globalQuery_polynomial (fun _ : Fin 2 => row) β
  simpa using hb

example : Fintype.card {σ : Bool → Bool // ∀ _j : Fin 2, row.value σ = row.demand} =
    Fintype.card {σ : Bool ⊕ Fin 1 → Bool //
      (globalQuery (fun _ : Fin 2 => row) false).eval σ = true} -
    Fintype.card {σ : Bool ⊕ Fin 1 → Bool //
      (globalQuery (fun _ : Fin 2 => row) true).eval σ = true} :=
  global_counting_identity _

/-- Normalized/capped original occurrences use the global queries on all declared bits. -/
example {n m h d : ℕ} (R : Fin (h + 1) → Occurrences n m)
    (hd : ∀ j, (R j).demand ≤ d)
    (hv : ∀ j, 0 ≤ (R j).shifted ∧ (R j).shifted ≤ ((R j).total : ℤ)) :
    Fintype.card {σ : Fin n → Bool // ∀ j, ((R j).value σ : ℤ) = (R j).target} =
      Fintype.card {σ : Fin n ⊕ Fin h → Bool //
        (globalQuery (fun j => (R j).toRow d (hd j)) false).eval σ = true} -
      Fintype.card {σ : Fin n ⊕ Fin h → Bool //
        (globalQuery (fun j => (R j).toRow d (hd j)) true).eval σ = true} := by
  classical
  rw [← global_counting_identity]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro σ
  exact forall_congr' fun j => ((R j).toRow_iff d (hd j) (hv j) σ).symm

end WeightedGlobalTests
