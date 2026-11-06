/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.CSP.Basic
public import Complexity.Computability.PolyTime.CSP.AffineTemplate
public import Complexity.Computability.Complexity.Problems.XORSAT

/-!
# Native tractability from a common parity polymorphism

For each relation, affine normal form on `Fin (arity R)` supplies a fixed system. Relabeling its
local coordinates by natural numbers and substituting constraint scopes gives a polynomial-time
reduction to ordinary XORSAT. Malformed arities produce the inconsistent system `[([], true)]`.
All fixed arities, empty/nullary relations and repeated scope variables are supported.

This proves the parity case of [Chen2006CSP], Theorem 3.20 (arXiv v1, p. 12), using Theorem 4.3
and the ensuing Gaussian-elimination argument, pp. 15–16. The affine characterization is also
[Bodirsky2026], Definition 26.14 and Lemma 26.15 (arXiv v3, Section 26.3).
The formal input uses framed lists and
binary variable labels. The relation alphabet, encoding and templates are fixed; no uniform bound
in the size of a supplied language or truth table is asserted.

## Main results

* `Cslib.Complexity.CSPSAT.exists_affine_templates`: normal forms for parity-preserved relations.
* `Cslib.Complexity.CSPSAT.polyTimeReducible_XORSAT_of_templates`: certified fixed compilation.
* `Cslib.Complexity.CSPSAT.mem_P_of_parity`: native tractability without solver assumptions.
-/

public section

namespace Cslib.Complexity.CSPSAT

open Cslib.Logic.PL Turing.MultiTapeTM

variable {Rel : Type}

/-- A common ternary parity polymorphism supplies correct fixed affine templates, without
auxiliary variables or restrictions on arity. -/
theorem exists_affine_templates (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (h : CSP.HasPolymorphism arity sem (Cslib.parity 3)) :
    ∃ template : Rel → AffineSystem ℕ, CSP.AffineTemplates arity sem template := by
  classical
  have hex (R : Rel) := (isPolymorphism_parity_iff_exists_affineSystem
    (CSP.booleanRelation arity sem R)).mp (h R)
  choose φ hφ using hex
  exact ⟨fun R => (φ R).relabel Fin.val, CSP.affineTemplates_relabel_fin hφ⟩

/-- Compile well-formed scopes to affine equations; reject every malformed instance. -/
@[expose] def toXORSAT (arity : Rel → ℕ) (template : Rel → AffineSystem ℕ)
    (F : CSP Rel ℕ) : XORSAT.System :=
  if F.validArity arity then F.instantiateAffine 0 template else [([], true)]

/-- Correct fixed templates give a native polynomial-time reduction to ordinary XORSAT. -/
theorem polyTimeReducible_XORSAT_of_templates [Finite Rel] (encRel : Rel ↪ List Bool)
    (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) (template : Rel → AffineSystem ℕ)
    (ht : CSP.AffineTemplates arity sem template) :
    PolyTimeReducible (encCSP encRel encNat) XORSAT.encoding (CSPSAT arity sem)
      {F | XORSAT.Satisfiable F} := by
  have hp : ComputableInPolyTime (toXORSAT arity template)
      (encCSP encRel encNat) XORSAT.encoding :=
    (Cslib.Complexity.CSP.computableInPolyTime_validArity encRel arity).ite
      (CSP.computableInPolyTime_instantiateAffine encRel template)
      (ComputableInPolyTime.const [([], true)])
  refine ⟨toXORSAT arity template, hp, fun F => ?_⟩
  by_cases hF : F.WellFormed arity
  · have heq : toXORSAT arity template F = F.instantiateAffine 0 template := by
      simp [toXORSAT, (CSP.validArity_eq_true_iff arity F).mpr hF]
    rw [mem_iff, Set.mem_ofPred_eq, heq, XORSAT.Satisfiable,
      CSP.satisfiable_instantiateAffine ht 0 hF]
    exact and_iff_right hF
  · have hguard : F.validArity arity = false := by
      cases hg : F.validArity arity
      · rfl
      · exact (hF ((CSP.validArity_eq_true_iff arity F).mp hg)).elim
    simp [toXORSAT, hguard, mem_iff, hF, XORSAT.Satisfiable,
      AffineSystem.Holds, AffineEquation.Holds, Bool.zero_eq_false]

/-- **Native P membership for every fixed finite parity-preserved Boolean language.** The
input has exact declared arities and binary natural-number variable labels. Empty and nullary
relations are allowed; malformed scopes are rejected. -/
theorem mem_P_of_parity [Finite Rel] (encRel : Rel ↪ List Bool) (arity : Rel → ℕ)
    (sem : Rel → List Bool → Bool)
    (h : CSP.HasPolymorphism arity sem (Cslib.parity 3)) :
    CSPSAT arity sem ∈ P (encCSP encRel encNat) := by
  obtain ⟨template, ht⟩ := exists_affine_templates arity sem h
  exact (polyTimeReducible_XORSAT_of_templates encRel arity sem template ht).mem_P
    XORSAT.satisfiable_mem_P

end Cslib.Complexity.CSPSAT
