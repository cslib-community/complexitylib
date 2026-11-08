/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CSP.Boolean
public import Complexity.Computability.Complexity.Reduction
import Complexity.Computability.Complexity.Classes.NP.Witness
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Native satisfiability for fixed finite Boolean constraint languages

`Cslib.Complexity.CSPSAT arity sem` contains exactly the well-formed satisfiable instances in
the existing CSP representation, with variables numbered by arbitrary natural numbers. Its
encoding is the existing `encCSP encRel encNat`: framed lists/pairs and binary variable indices.
The relation alphabet, its encoding, arities and semantics are fixed independently of the
instance [Chen2006CSP], Definitions 3.1–3.3. Repeated variables and empty scopes are allowed;
incorrect scope lengths are rejected, and empty relations are interpreted as false.

For every finite relation alphabet this problem belongs to native `NP`. The proof compiles
forbidden local assignments to CNF using the existing fixed-width polynomial-time compiler;
malformed inputs produce an empty clause. No uniform bound in the size of the language is
claimed.

## Main definitions

* `Cslib.Complexity.CSPSAT`: well-formed satisfiable instances of a fixed Boolean language.

## Main results

* `Cslib.Complexity.CSPSAT.mem_NP`: membership in native NP for a finite relation alphabet.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- The well-formed satisfiable instances of a fixed Boolean constraint language. -/
@[expose] def CSPSAT {Rel : Type} (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) :
    Set (CSP Rel ℕ) :=
  {F | F.WellFormed arity ∧ F.Satisfiable sem}

namespace CSPSAT

variable {Rel : Type}

/-- Membership separates exact-arity syntax from satisfiability. -/
theorem mem_iff (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) (F : CSP Rel ℕ) :
    F ∈ CSPSAT arity sem ↔ F.WellFormed arity ∧ F.Satisfiable sem := Iff.rfl

private def toSAT (k : ℕ) (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (F : CSP Rel ℕ) : CNF ℕ :=
  if F.validArity arity then F.toCNFBounded k sem else [[]]

/-- Every fixed finite Boolean constraint language has a native NP satisfiability problem,
under framed list/pair encodings with binary variable indices. -/
theorem mem_NP [Finite Rel] (encRel : Rel ↪ List Bool) (arity : Rel → ℕ)
    (sem : Rel → List Bool → Bool) : CSPSAT arity sem ∈ NP (encCSP encRel encNat) := by
  classical
  let _ := Fintype.ofFinite Rel
  let k := Finset.univ.sup arity
  have hbound (R : Rel) : arity R ≤ k := Finset.le_sup (Finset.mem_univ R)
  have hf : ComputableInPolyTime (toSAT k arity sem) (encCSP encRel encNat) encCNF := by
    exact (CSP.computableInPolyTime_validArity encRel arity).ite
      (CSP.computableInPolyTime_toCNFBounded_of_finite encRel encNat k sem)
      (ComputableInPolyTime.const [[]])
  have hred : PolyTimeReducible (encCSP encRel encNat) encCNF (CSPSAT arity sem) SAT := by
    refine ⟨toSAT k arity sem, hf, fun F => ?_⟩
    by_cases hF : F.WellFormed arity
    · have hw : ∀ c ∈ F, c.2.length ≤ k := fun c hc => (hF c hc).le.trans (hbound c.1)
      simp [toSAT, (CSP.validArity_eq_true_iff arity F).mpr hF, mem_iff, hF, mem_SAT,
        CSP.toCNFBounded_eq_toCNF hw, CSP.satisfiable_toCNF]
    · have hguard : F.validArity arity = false := by
        cases hg : F.validArity arity
        · rfl
        · exact (hF ((CSP.validArity_eq_true_iff arity F).mp hg)).elim
      simp [toSAT, hguard, mem_iff, hF, mem_SAT, CNF.Satisfiable, CNF.eval, Clause.eval]
  exact hred.mem_NP SAT.mem_NP

end CSPSAT

end Cslib.Complexity
