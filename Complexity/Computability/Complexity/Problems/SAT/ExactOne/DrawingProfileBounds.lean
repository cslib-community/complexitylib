/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.DrawingProfiles
public import Complexity.Logics.Propositional.CNF.ExactOne.BlockBounds

/-!
# Unique ownership of local drawing auxiliaries

The original-clause index distinguishes signed auxiliaries; disjoint signed-clause prefix
intervals distinguish positive auxiliaries. Source placeholders may coincide when source
variables are repeated, and are deliberately excluded from these injectivity statements.

## Main results

* `profileVariableMap_aux_injective`: an actual auxiliary identifies its unique source block
  and local profile variable.
* `profileVariableMap_aux_ne_source`: private auxiliary names cannot be source names.

## References

These are original support and prefix-index arguments for the actual drawing compiler.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Cslib.Logic.PL

/-- Signed block length depends on the clause length, independently of source variable names
and polarities. The selected profile has exactly the actual signed block length. -/
theorem profile_signed_length (i : ℕ) (c : Clause ℕ) :
    (CNF.FromSAT.clause 0 (profileSource (clauseProfile c))).length =
      (CNF.FromSAT.clause i c).length := by
  rcases c with _ | ⟨⟨p, bp⟩, _ | ⟨⟨q, bq⟩, _ | ⟨⟨r, br⟩, rest⟩⟩⟩
  · rfl
  · cases bp <;> rfl
  · cases bp <;> cases bq <;> rfl
  · cases bp <;> cases bq <;> cases br <;> rfl

/-- A private auxiliary never becomes an inherited source-variable name. -/
theorem profileVariableMap_aux_ne_source {i offset : ℕ} {c : Clause ℕ}
    {v : CNF.PositiveExactOneCompile.Variable ℕ}
    (hv : ∀ n, v ≠ Sum.inl (Sum.inl n)) (n : ℕ) :
    profileVariableMap i offset c v ≠ Sum.inl (Sum.inl n) := by
  rcases v with (_ | _) | _
  · exact False.elim (hv _ rfl)
  · simp [profileVariableMap]
  · simp [profileVariableMap]

/-- The actual global name of an auxiliary determines its source block and its local profile
name. Source placeholders, whose variables can coincide, are excluded explicitly. -/
theorem profileVariableMap_aux_injective (φ : CNF ℕ) {i j : ℕ}
    (hi : i < φ.length) (hj : j < φ.length)
    {v w : CNF.PositiveExactOneCompile.Variable ℕ}
    (hv : v ∈ profileVariables (clauseProfile φ[i]))
    (hw : w ∈ profileVariables (clauseProfile φ[j]))
    (hvs : ∀ n, v ≠ Sum.inl (Sum.inl n))
    (hws : ∀ n, w ≠ Sum.inl (Sum.inl n))
    (he : profileVariableMap i (CNF.PositiveExactOneCompile.signedOffset φ i) φ[i] v =
      profileVariableMap j (CNF.PositiveExactOneCompile.signedOffset φ j) φ[j] w) :
    i = j ∧ v = w := by
  have hscopeV := profileVariables_scope (clauseProfile φ[i]) v hv
  have hscopeW := profileVariables_scope (clauseProfile φ[j]) w hw
  rcases v with (a | ⟨a, b⟩) | ⟨⟨a, b⟩, s⟩
  · exact False.elim (hvs a rfl)
  · rcases w with (c | ⟨c, d⟩) | ⟨⟨c, d⟩, t⟩
    · exact False.elim (hws c rfl)
    · simp only [profileVariableMap, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq] at he
      exact ⟨he.1, by simp only [hscopeV, hscopeW, he.2]⟩
    · simp [profileVariableMap] at he
  · rcases w with (c | ⟨c, d⟩) | ⟨⟨c, d⟩, t⟩
    · exact False.elim (hws c rfl)
    · simp [profileVariableMap] at he
    · simp only [profileVariableMap, Sum.inr.injEq, Prod.mk.injEq] at he
      have ha : a < (CNF.FromSAT.clause i φ[i]).length := by
        simpa only [profile_signed_length i φ[i]] using hscopeV
      have hc : c < (CNF.FromSAT.clause j φ[j]).length := by
        simpa only [profile_signed_length j φ[j]] using hscopeW
      obtain ⟨hij, hac⟩ := CNF.PositiveExactOneCompile.signedOffset_range_injective
        φ hi hj ha hc he.1.1
      exact ⟨hij, by simp only [hac, he.1.2, he.2]⟩

end Cslib.Complexity.SAT.ExactOne
