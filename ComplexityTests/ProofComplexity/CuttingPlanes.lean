/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.CuttingPlanes.Resolution
import Complexity.Logics.Propositional.CuttingPlanes.Separation

/-!
# Tests: cutting planes

Clause translations and their semantics; a three-line refutation of `x ∧ ¬x`; a rounding step
that cuts off a fractional point; the unsoundness of division without the divisibility condition;
soundness on a satisfiable CNF; a resolution refutation translated into cutting planes; the
pigeonhole refutations at small sizes and the separation from resolution.
-/

namespace ComplexityTests.ProofComplexity.CuttingPlanes

open Cslib Cslib.Logic.PL Cslib.Logic.PL.Ineq Cslib.Logic.PL.CuttingPlanes

/-! ### Clause translations -/

/-- `x₀ ∨ ¬x₁` translates to `x₀ - x₁ ≥ 0`. -/
example : Clause.toIneq [((0 : ℕ), true), (1, false)] =
    ⟨Finsupp.single 0 1 + Finsupp.single 1 (-1), 0⟩ := by
  rw [Clause.toIneq_of_nodup (by decide)]
  ext <;> simp [add_comm]

/-- A repeated literal is counted once: `x₀ ∨ x₀` translates to `x₀ ≥ 1`. -/
example : Clause.toIneq [((0 : ℕ), true), (0, true)] = Clause.toIneq [((0 : ℕ), true)] := by
  simp [Clause.toIneq]

/-- The translation of `x₀ ∨ ¬x₁` holds where the clause does and fails where it does not. -/
example : (Clause.toIneq [((0 : ℕ), true), (1, false)]).Holds (fun _ => false) ∧
    ¬ (Clause.toIneq [((0 : ℕ), true), (1, false)]).Holds (fun v => v == 1) := by
  rw [Clause.holds_toIneq_iff, Clause.holds_toIneq_iff]
  decide

/-! ### A refutation of `x ∧ ¬x` -/

/-- `x₀ ∧ ¬x₀`. -/
private def ψ : CNF ℕ := [[(0, true)], [(0, false)]]

/-- `x₀ ≥ 1` plus `-x₀ ≥ 0` is `0 ≥ 1`: a three-line refutation. -/
example : RefutableInSize ψ.toIneqs 3 := by
  have h := (DerivableInSize.hyp (Γ := ψ.toIneqs) (CNF.toIneq_mem_toIneqs (c := [(0, true)])
    (by decide))).add (DerivableInSize.hyp (CNF.toIneq_mem_toIneqs (c := [(0, false)])
    (by decide)))
  have hsum : Clause.toIneq [((0 : ℕ), true)] + Clause.toIneq [(0, false)] = contra := by
    ext v <;> simp [Clause.toIneq]
  rwa [hsum] at h

/-! ### Rounding -/

/-- `x₀ + x₁ ≥ 1`. -/
private noncomputable def sumGeOne : Ineq ℕ := ⟨Finsupp.single 0 1 + Finsupp.single 1 1, 1⟩

/-- From `2 x₀ + 2 x₁ ≥ 1`, which the fractional point `(1/4, 1/4)` satisfies, rounding derives
`x₀ + x₁ ≥ 1`, which it does not. -/
example : DerivableInSize {⟨2 • sumGeOne.coeff, 1⟩} sumGeOne 2 := by
  have h := (DerivableInSize.hyp (Set.mem_singleton (⟨2 • sumGeOne.coeff, 1⟩ : Ineq ℕ))).div 2
    Nat.two_pos fun v => ⟨sumGeOne.coeff v, by simp⟩
  rwa [div_eq_of (J := sumGeOne) Nat.two_pos (by ext; simp) (by simp [sumGeOne])
    (by simp [sumGeOne])] at h

/-- The rounded bound is the ceiling: `-x ≥ -3` divided by `2` is `-x/2 ≥ -1`. -/
example : (⟨Finsupp.single (0 : ℕ) (-2), -3⟩ : Ineq ℕ).div 2 =
    ⟨Finsupp.single 0 (-1), -1⟩ := by
  ext v
  · by_cases hv : v = 0 <;> simp [hv, eq_comm]
  · decide

/-- The divisibility condition of `CuttingPlanes.IsProof.div` is needed: `x₀ ≥ 1` is satisfiable,
but dividing it by `2` would give `0 ≥ 1`. -/
example : (⟨Finsupp.single (0 : ℕ) 1, 1⟩ : Ineq ℕ).Holds (fun _ => true) ∧
    (⟨Finsupp.single (0 : ℕ) 1, 1⟩ : Ineq ℕ).div 2 = contra := by
  refine ⟨by simp [Holds], ?_⟩
  ext v
  · by_cases hv : v = 0 <;> simp [hv]
  · decide

/-! ### Soundness and the simulation of resolution -/

/-- `(x₀ ∨ x₁) ∧ (¬x₀ ∨ x₁)`. -/
private def φ : CNF ℕ := [[(0, true), (1, true)], [(0, false), (1, true)]]

/-- `φ` is satisfiable, so its inequalities have no refutation. -/
example (s : ℕ) : ¬ RefutableInSize φ.toIneqs s :=
  fun h => h.not_satisfiable ⟨fun _ => true, by decide⟩

/-- The resolution refutation `x₀`, `¬x₀`, `[]` of `ψ` gives a cutting planes refutation of at most
`(8 · 1 + 1) · 3 = 27` lines. -/
example : RefutableInSize ψ.toIneqs 27 := by
  have hp : ψ.IsProof [[], [(0, false)], [(0, true)]] :=
    ((CNF.IsProof.nil.mem (by decide)).mem (by decide)).resolvent (c₁ := [(0, true)])
      (c₂ := [(0, false)]) 0 (by decide) (by decide) (by decide) (by decide)
  have hvars : (ψ.vars.toFinset).card = 1 := by decide
  simpa [hvars] using (CNF.RefutableInSize.cuttingPlanes ⟨_, hp, by simp, le_rfl⟩ :
    RefutableInSize ψ.toIneqs ((8 * ψ.vars.toFinset.card + 1) * 3))

/-- One resolution step: from `x₀ ∨ x₁` and `¬x₀ ∨ x₁`, derive `x₁ ≥ 1` in at most
`2 · 2 + 2 · 2 = 8` lines. -/
example : DerivableInSize {Clause.toIneq [((0 : ℕ), true), (1, true)],
    Clause.toIneq [((0 : ℕ), false), (1, true)]} (Clause.toIneq [((1 : ℕ), true), (1, true)]) 8 :=
  derivableInSize_toIneq_resolvent (v := 0) (by decide) (by decide)

/-! ### Pigeonhole -/

/-- `PHP^3_2` has a cutting planes refutation of at most `3 · 4² = 48` lines, and `PHP^4_2` one of
at most `3 · 5² = 75` lines. -/
example : RefutableInSize (CNF.pigeonhole 3 2).toIneqs 48 ∧
    RefutableInSize (CNF.pigeonhole 4 2).toIneqs 75 :=
  ⟨refutableInSize_pigeonhole_succ 2, refutableInSize_pigeonhole (by decide)⟩

/-- `PHP^1_0` is refuted by its empty pigeon clause in one line. -/
example : RefutableInSize (CNF.pigeonhole 1 0).toIneqs 1 := by
  have h := DerivableInSize.hyp (CNF.toIneq_mem_toIneqs (φ := CNF.pigeonhole 1 0)
    (c := CNF.pigeonClause 0 0) (CNF.mem_pigeonhole.2 (Or.inl ⟨0, rfl⟩)))
  rwa [show CNF.pigeonClause 0 (0 : Fin 1) = [] from rfl, Clause.toIneq_nil] at h

/-- The hypothesis `n < m` is needed: `PHP^2_2` is satisfiable, so it has no refutation. -/
example (s : ℕ) : ¬ RefutableInSize (CNF.pigeonhole 2 2).toIneqs s :=
  fun h => h.not_satisfiable (CNF.satisfiable_pigeonhole_iff.2 le_rfl)

/-- At most one of three pigeons sits in hole `0`, in at most `3 · 6 = 18` lines. -/
example : DerivableInSize (CNF.pigeonhole 3 2).toIneqs (holeSum Finset.univ 0) 18 :=
  derivableInSize_holeSum Finset.univ_nonempty 0

/-! ### Separation from resolution -/

/-- Resolution cannot keep the number of lines of cutting planes refutations of `PHP^{n+1}_n`:
at `n = 720` that would give `2 ^ 30 ≤ 721 · 722²`. -/
example : ¬ ∀ n s, RefutableInSize (CNF.pigeonhole (n + 1) n).toIneqs s →
    (CNF.pigeonhole (n + 1) n).RefutableInSize s := fun h => by
  have := two_pow_le_of_forall_refutableInSize_pigeonhole (f := id) (h 720)
  norm_num at this

example : ¬ ∃ f : ℕ → ℕ, PolynomiallyBounded f ∧ ∀ n s,
    RefutableInSize (CNF.pigeonhole (n + 1) n).toIneqs s →
      (CNF.pigeonhole (n + 1) n).RefutableInSize (f s) :=
  not_exists_polynomiallyBounded_refutableInSize_pigeonhole

end ComplexityTests.ProofComplexity.CuttingPlanes
