/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.ToCNF

/-!
# Exact violation counts for forbidden-pattern CNF compilation

Each violated Boolean constraint contributes exactly one falsified clause to the existing
forbidden-pattern compiler, even when its scope repeats variables. The unique falsified clause
forbids the local pattern induced by the assignment. Thus compilation preserves the number of
violated constraints, although the total number of clauses can grow.
The exact-count formulation is an original library lemma about the existing compiler.

## Main results

* `Cslib.Logic.PL.Constraint.countUnsat_toCNF`: one falsified clause per violated constraint.
* `Cslib.Logic.PL.CSP.countUnsat_toCNF`, `Cslib.Logic.PL.CSP.countUnsat_toCNFBounded`:
  exact counts for systems and for the width-guarded compiler on its valid domain.
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {Rel V : Type*}

/-- Exactly one forbidden-pattern clause is false when the constraint is violated; otherwise
all its clauses are true. No distinctness assumption on the scope is needed. -/
theorem Constraint.countUnsat_toCNF (sem : Rel → List Bool → Bool)
    (c : Constraint Rel V) (σ : V → Bool) :
    (toCNF sem c).countUnsat σ = if eval sem σ c then 0 else 1 := by
  rw [CNF.countUnsat, toCNF, List.countP_map, List.countP_filter]
  simp only [Function.comp_def]
  have hcongr : ∀ w ∈ BitString.enumList c.2.length,
      (!(forbidClause c.2 w).eval σ && !sem c.1 w) ↔
        (!eval sem σ c && (w == c.2.map σ)) := by
    intro w hw
    rw [eval_forbidClause c.2 (BitString.length_of_mem_enumList hw) σ]
    by_cases heq : w = c.2.map σ
    · subst w
      simp [eval]
    · simp [heq, Ne.symm heq]
  rw [List.countP_congr hcongr]
  have hnodup : (BitString.enumList c.2.length).Nodup :=
    (BitString.nodup_enum _).map List.ofFn_injective
  cases eval sem σ c with
  | false =>
    simp only [Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
    change (BitString.enumList c.2.length).count (c.2.map σ) = 1
    exact hnodup.count_of_mem (BitString.mem_enumList.mpr (List.length_map _))
  | true => simp

/-- Forbidden-pattern compilation preserves the number of violated constraints, counted with
multiplicity. -/
theorem CSP.countUnsat_toCNF (sem : Rel → List Bool → Bool) (F : CSP Rel V)
    (σ : V → Bool) :
    (F.toCNF sem).countUnsat σ = F.countP fun c => !Constraint.eval sem σ c := by
  induction F with
  | nil => rfl
  | cons c F ih =>
    change (Constraint.toCNF sem c ++ CSP.toCNF sem F).countUnsat σ = _
    rw [CNF.countUnsat, List.countP_append, ← CNF.countUnsat, ← CNF.countUnsat,
      Constraint.countUnsat_toCNF, ih, List.countP_cons]
    cases Constraint.eval sem σ c <;> simp [Nat.add_comm]

/-- The width-guarded compiler preserves violation counts when every scope satisfies its width
bound. -/
theorem CSP.countUnsat_toCNFBounded {k : ℕ} (sem : Rel → List Bool → Bool)
    {F : CSP Rel V} (hF : ∀ c ∈ F, c.2.length ≤ k) (σ : V → Bool) :
    (F.toCNFBounded k sem).countUnsat σ = F.countP fun c => !Constraint.eval sem σ c := by
  rw [toCNFBounded_eq_toCNF hF, countUnsat_toCNF]

end Cslib.Logic.PL
