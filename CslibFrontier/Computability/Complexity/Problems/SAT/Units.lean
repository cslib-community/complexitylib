/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SAT
import CslibFrontier.Logics.Propositional.CNF.Vars
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Tactic.EncLen

/-!
# Unit clauses fixing variables

Search procedures for `SAT` fix variables one at a time by adding unit clauses: the unit clauses
of a list of literals `a` (`Cslib.Complexity.SAT.units`) hold exactly when the literals do, so
`units a ++ φ` is the formula `φ` with the values in `a` fixed. This file collects their
semantics and the bounds on their encoded length that the self-reduction of `SAT`
(`CslibFrontier/Computability/Complexity/Classes/NP/SelfReduction.lean`) and the pruned searches
of Fortune and Mahaney (`CslibFrontier/Computability/Complexity/Classes/Sparse/`) use.

## Main definitions

* `Cslib.Complexity.SAT.units`: the unit clauses of a list of literals.

## Main results

* `Cslib.Complexity.SAT.eval_units`, `Cslib.Complexity.SAT.vars_units`: unit clauses hold when
  their literals do, and have the variables of their literals.
* `Cslib.Complexity.SAT.eval_units_append`, `Cslib.Complexity.SAT.eval_append_units`: a formula
  with unit clauses before or after it holds exactly when the formula and the literals do.
* `Cslib.Complexity.SAT.length_encCNF_append`: encoded length is additive under concatenation.
* `Cslib.Complexity.SAT.length_encList_le_of_mem_vars`,
  `Cslib.Complexity.SAT.length_encCNF_units_le`: the literals and the unit clauses fixing
  variables of `φ` are short.
-/

@[expose] public section

namespace Cslib.Complexity.SAT

open Cslib.Logic.PL Turing.MultiTapeTM

/-- The unit clauses of a list of literals. -/
def units (answers : List (Literal ℕ)) : CNF ℕ := answers.map ([·])

/-! ### Semantics -/

/-- Unit clauses hold exactly when their literals do. -/
theorem eval_units (σ : ℕ → Bool) (answers : List (Literal ℕ)) :
    (units answers).eval σ = true ↔ ∀ l ∈ answers, σ l.1 = l.2 := by
  simp only [units, CNF.eval_eq_true_iff, List.forall_mem_map, Clause.eval_cons, Clause.eval_nil,
    Bool.or_false, Literal.eval_eq_true_iff]

/-- The variables of unit clauses are those of their literals. -/
theorem vars_units (answers : List (Literal ℕ)) : (units answers).vars = answers.map Prod.fst := by
  induction answers with
  | nil => rfl
  | cons l answers ih => simpa [units, CNF.vars] using ih

/-- The variables of a formula after unit clauses are those of the literals, then those of the
formula. -/
theorem vars_units_append (answers : List (Literal ℕ)) (φ : CNF ℕ) :
    (units answers ++ φ).vars = answers.map Prod.fst ++ φ.vars := by
  rw [CNF.vars_append, vars_units]

/-- A formula after unit clauses holds exactly when the literals and the formula do. -/
theorem eval_units_append (σ : ℕ → Bool) (answers : List (Literal ℕ)) (φ : CNF ℕ) :
    (units answers ++ φ).eval σ = true ↔ (∀ l ∈ answers, σ l.1 = l.2) ∧ φ.eval σ = true := by
  rw [CNF.eval_append, Bool.and_eq_true, eval_units]

/-- A formula with unit clauses holds exactly when the formula holds and the literals do. -/
theorem eval_append_units (σ : ℕ → Bool) (φ : CNF ℕ) (answers : List (Literal ℕ)) :
    (φ ++ units answers).eval σ = true ↔ φ.eval σ = true ∧ ∀ l ∈ answers, σ l.1 = l.2 := by
  rw [CNF.eval_append, Bool.and_eq_true, eval_units]

/-! ### Encoded length -/

/-- The encoding of a concatenation of formulas is as long as the two encodings together. -/
theorem length_encCNF_append (φ ψ : CNF ℕ) :
    (encCNF (φ ++ ψ)).length = (encCNF φ).length + (encCNF ψ).length := by
  simp [encCNF]

/-- A variable of a formula takes fewer bits than the formula. -/
theorem length_encNat_le_of_mem_vars {φ : CNF ℕ} {v : ℕ} (hv : v ∈ φ.vars) :
    (encNat v).length ≤ (encCNF φ).length := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hv
  obtain ⟨c, hc, hl⟩ := List.mem_flatten.1 hl
  calc (encNat l.1).length ≤ (encPair encNat encBool l).length := length_le_encPair_left _ _ _
    _ ≤ (encList (encPair encNat encBool) c).length := SizedListEncoding.length_elem_le c _ hl
    _ ≤ (encCNF φ).length :=
      SizedListEncoding.length_elem_le (encL := encList (encList (encPair encNat encBool))) φ c hc

/-- Literals fixing variables of `φ` have short encodings: each takes at most `4 L + 5` bits,
where `L` is the length of `φ`. -/
theorem length_encList_le_of_mem_vars {φ : CNF ℕ} {answers : List (Literal ℕ)}
    (hanswers : ∀ l ∈ answers, l.1 ∈ φ.vars) :
    (encList (encPair encNat encBool) answers).length ≤
      answers.length * (4 * (encCNF φ).length + 5) := by
  have h := length_encList_le (encPair encNat encBool) answers (b := 2 * (encCNF φ).length + 2)
    fun l hl => by
      have := length_encNat_le_of_mem_vars (hanswers l hl)
      enc_len
  calc _ ≤ answers.length * (2 * (2 * (encCNF φ).length + 2) + 1) := h
    _ = answers.length * (4 * (encCNF φ).length + 5) := by ring

/-- The unit clause of a literal on `v` takes `8 b + 11` bits, where `b` is the length of the
binary digits of `v`. -/
private theorem length_encCNF_unit (l : Literal ℕ) :
    (encCNF [[l]]).length = 8 * (encNat l.1).length + 11 := by
  enc_len [encCNF, List.append_nil]

/-- The unit clause of a literal on a variable of `φ` takes at most `8 L + 11` bits, where `L`
is the length of `φ`. -/
theorem length_encCNF_unit_le {φ : CNF ℕ} {l : Literal ℕ} (hl : l.1 ∈ φ.vars) :
    (encCNF [[l]]).length ≤ 8 * (encCNF φ).length + 11 := by
  have := length_encNat_le_of_mem_vars hl
  rw [length_encCNF_unit]
  omega

/-- Unit clauses fixing variables of `φ` take at most `8 L + 11` bits each, where `L` is the
length of `φ`. -/
theorem length_encCNF_units_le {φ : CNF ℕ} {answers : List (Literal ℕ)}
    (hanswers : ∀ l ∈ answers, l.1 ∈ φ.vars) :
    (encCNF (units answers)).length ≤ answers.length * (8 * (encCNF φ).length + 11) := by
  induction answers with
  | nil => simp [units, encCNF]
  | cons l answers ih =>
    have h₁ := length_encCNF_unit_le (hanswers l (List.mem_cons_self ..))
    have h₂ := ih fun l' hl' => hanswers l' (List.mem_cons_of_mem _ hl')
    rw [show units (l :: answers) = [[l]] ++ units answers from rfl, length_encCNF_append,
      List.length_cons, Nat.succ_mul]
    omega

end Cslib.Complexity.SAT
