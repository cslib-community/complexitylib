/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Cryptanalysis.AddXNORSparsification

/-! # Materialized sparse-reduction clients

Empty, contradictory and branching formulas exercise the actual collector. The parameter client
checks the unrestricted real-rate quantifier without supplying a family or semantic oracle.
-/

public section
namespace CslibFrontierTests.AddXNORSparsification

open Cslib.Logic.PL Cslib.Complexity
open Cslib.Cryptanalysis.AddXNOR

example : Sparsify.Family.collect 3 1 3 100 [] = [[]] := by decide

example : Sparsify.Family.collect 3 1 3 100 [[]] = [[[]]] := by decide

/-- Four clauses sharing a heart force an actual branching step. -/
def branching : CNF ℕ :=
  [[(0, true), (1, true)], [(0, true), (2, true)],
   [(0, true), (3, true)], [(0, true), (4, true)]]

example : (Sparsify.Family.collect 2 1 2 100 branching).length = 2 := by decide

example : (Sparsification.instances 1 100 []).length = 1 := by decide

example : 2 ≤ ((Sparsification.instances 1 100 []).headD (0, [])).1 := by decide

example : ∃ α C : ℕ, ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ 3) →
    ((Sparsification.instances α 7 φ).length : ℝ) ≤ 2 ^ ((1 / 10 : ℝ) * φ.numVars) ∧
      (φ.Satisfiable ↔ ∃ x ∈ Sparsification.instances α 7 φ, x ∈ Decision) ∧
      ∀ x ∈ Sparsification.instances α 7 φ, x.1 ≤ C * (φ.numVars + 1) := by
  obtain ⟨α, C, -, -, h⟩ := Sparsification.exists_parameters (M := 7)
    (η := 1 / 10) (by norm_num) (by omega)
  exact ⟨α, C, fun φ hφ => ⟨(h φ hφ).1, (h φ hφ).2.1,
    fun x hx => ((h φ hφ).2.2 x hx).1⟩⟩

example (α M : ℕ) : Turing.MultiTapeTM.IsComputable
    (Sparsification.instances α M) encCNF
      (Turing.MultiTapeTM.encList encInstance) :=
  (Sparsification.certificate α M).isComputable

end CslibFrontierTests.AddXNORSparsification
