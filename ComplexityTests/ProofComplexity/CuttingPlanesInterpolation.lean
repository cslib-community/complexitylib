/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.CuttingPlanes.Interpolation
import Mathlib.Tactic.FinCases

/-!
# Tests: feasible interpolation for cutting planes

Alice's system `Γ_A(x₀, y) = {y ≥ 1, x₀ - y ≥ 0}` has one shared and one private variable, and
Bob's system `Γ_B(x₀) = {-x₀ ≥ 0}` has no private variable. The private variable matters: neither
inequality of `Γ_A` alone contradicts `Γ_B`, but their sum `x₀ ≥ 1` does. So the five-line cutting
planes refutation `l₁ = y ≥ 1`, `l₂ = x₀ - y ≥ 0`, `l₁ + l₂ = x₀ ≥ 1`, `l₄ = -x₀ ≥ 0`, `0 ≥ 1`
(`ls`, newest line first) passes through `y`.

* Deciding a line costs `⌈log₂ 3⌉ + 1 = 3` bits (Alice sends `q`'s contribution, in `{-1, 0, 1}`),
  and the search costs `⌈log₂ 1⌉ (⌈log₂ 3⌉ + 1) = 0` bits, so with `t = 3`
  `CuttingPlanes.IsProof.exists_monotone_circuit` gives a monotone circuit with at most
  `(5 · 2 ⁶ + 1) · 2 ⁷ = 41088` gates that is true on `x₀ = 1` and false on `x₀ = 0`. Hence it
  computes `x₀`: both promises are satisfiable, so the interpolant is not vacuous.
* `CuttingPlanes.IsProof.exists_circuit_of_abs_coeff_le` applies with `M = 1`.
* The search at `x₀ + x₁ ≥ 1` over two shared variables costs at most
  `⌈log₂ 2⌉ (⌈log₂ 5⌉ + 1) = 4` bits.
-/

namespace ComplexityTests.CuttingPlanesInterpolation

open Cslib Cslib.Communication Cslib.Circuits Cslib.Logic.PL Cslib.Logic.PL.CuttingPlanes
open Cslib.Logic.PL.SemanticDerivation

/-- `y ≥ 1`. -/
private noncomputable def EA₁ : Ineq (Fin 1 ⊕ Unit) := ⟨Finsupp.single (.inr ()) 1, 1⟩

/-- `x₀ - y ≥ 0`. -/
private noncomputable def EA₂ : Ineq (Fin 1 ⊕ Unit) :=
  ⟨Finsupp.single (.inl 0) 1 + Finsupp.single (.inr ()) (-1), 0⟩

/-- `-x₀ ≥ 0`. -/
private noncomputable def EB : Ineq (Fin 1 ⊕ Empty) := ⟨Finsupp.single (.inl 0) (-1), 0⟩

/-- Alice's system. -/
private noncomputable def ΓA : Set (Ineq (Fin 1 ⊕ Unit)) := {EA₁, EA₂}

/-- Bob's system. -/
private noncomputable def ΓB : Set (Ineq (Fin 1 ⊕ Empty)) := {EB}

/-- The variables of both systems. -/
private abbrev W := Fin 1 ⊕ (Unit ⊕ Empty)

private noncomputable def l₁ : Ineq W := EA₁.relabel (Sum.map id Sum.inl)
private noncomputable def l₂ : Ineq W := EA₂.relabel (Sum.map id Sum.inl)
private noncomputable def l₄ : Ineq W := EB.relabel (Sum.map id Sum.inr)

/-- The refutation, newest line first. -/
private noncomputable def ls : List (Ineq W) := [l₁ + l₂ + l₄, l₄, l₁ + l₂, l₂, l₁]

private theorem coeff_l₁ : l₁.coeff = Finsupp.single (.inr (.inl ())) 1 := by
  simp only [l₁, EA₁, Ineq.coeff_relabel, Finsupp.mapDomain_single, Sum.map_inr]

private theorem coeff_l₂ :
    l₂.coeff = Finsupp.single (.inl 0) 1 + Finsupp.single (.inr (.inl ())) (-1) := by
  simp only [l₂, EA₂, Ineq.coeff_relabel, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
    Sum.map_inl, Sum.map_inr, id_eq]

private theorem coeff_l₄ : l₄.coeff = Finsupp.single (.inl 0) (-1) := by
  simp only [l₄, EB, Ineq.coeff_relabel, Finsupp.mapDomain_single, Sum.map_inl, id_eq]

/-- The last line is `0 ≥ 1`. -/
private theorem contra_eq : l₁ + l₂ + l₄ = Ineq.contra := by
  ext w
  · simp only [Ineq.coeff_add, coeff_l₁, coeff_l₂, coeff_l₄, Finsupp.coe_add, Pi.add_apply,
      Ineq.coeff_contra, Finsupp.coe_zero, Pi.zero_apply]
    rcases w with i | (_ | e)
    · rw [Subsingleton.elim i 0]
      simp
    · simp
    · exact e.elim
  · simp [l₁, l₂, l₄, EA₁, EA₂, EB]

private theorem isProof_ls :
    IsProof (Ineq.relabel (Sum.map id Sum.inl) '' ΓA ∪
      Ineq.relabel (Sum.map id Sum.inr) '' ΓB) ls := by
  have h₁ : l₁ ∈ Ineq.relabel (Sum.map id Sum.inl) '' ΓA ∪
      Ineq.relabel (Sum.map id Sum.inr) '' ΓB := Or.inl ⟨EA₁, by simp [ΓA], rfl⟩
  have h₂ : l₂ ∈ Ineq.relabel (Sum.map id Sum.inl) '' ΓA ∪
      Ineq.relabel (Sum.map id Sum.inr) '' ΓB := Or.inl ⟨EA₂, by simp [ΓA], rfl⟩
  have h₄ : l₄ ∈ Ineq.relabel (Sum.map id Sum.inl) '' ΓA ∪
      Ineq.relabel (Sum.map id Sum.inr) '' ΓB := Or.inr ⟨EB, rfl, rfl⟩
  exact ((((IsProof.nil.hyp h₁).hyp h₂).add (by simp) (by simp)).hyp h₄).add (by simp) (by simp)

private theorem contra_mem_ls : Ineq.contra ∈ ls := by
  rw [← contra_eq]
  exact List.mem_cons_self

/-- Every coefficient of the refutation is at most `1` in absolute value. -/
private theorem abs_coeff_le (I : Ineq W) (hI : I ∈ ls) (w : W) : |I.coeff w| ≤ (1 : ℕ) := by
  simp only [ls, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Ineq.coeff_add, coeff_l₁, coeff_l₂, coeff_l₄, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_apply] <;>
    rcases w with i | (_ | e) <;>
    first | exact e.elim | (rw [Subsingleton.elim i 0]; simp) | simp

/-- `Γ_A` holds where `x₀ = 1` and `y = 1`. -/
private theorem holds_ΓA (u : Fin 1 → Bool) (hu : u 0 = true) :
    ∀ E ∈ ΓA, E.Holds (Sum.elim u fun _ => true) := by
  intro E hE
  rcases hE with rfl | rfl <;> simp [Ineq.Holds, Ineq.lhs, EA₁, EA₂, hu]

/-- `Γ_B` holds exactly where `x₀ = 0`. -/
private theorem holds_ΓB (v : Fin 1 → Bool) (hv : v 0 = false) (r : Empty → Bool) :
    ∀ E ∈ ΓB, E.Holds (Sum.elim v r) := by
  rintro E rfl
  simp [Ineq.Holds, Ineq.lhs, EB, hv]

/-- Deciding a line costs `⌈log₂ 3⌉ + 1 = 3` bits. -/
private theorem ht₂ : Nat.clog 2 (2 * 1 * Fintype.card Unit + 1) + 1 ≤ 3 := by
  have : Nat.clog 2 3 ≤ 2 := Nat.clog_le_of_le_pow (by norm_num)
  rw [Fintype.card_unit]
  exact Nat.add_le_add_right this 1

/-- The refutation through the private variable gives a monotone circuit with at most `41088`
gates computing `x₀`. -/
example : ∃ C : Circuit Monotone.signature 1 1, C.size ≤ 41088 ∧
    ∀ u, C.eval Monotone.interpretation u 0 = u 0 := by
  obtain ⟨C, hsize, hU, hV⟩ := isProof_ls.exists_monotone_circuit contra_mem_ls (M₀ := 1)
    (M := 1) (t := 3)
    (by rintro E (rfl | rfl) i <;> rw [Subsingleton.elim i 0] <;> simp [EA₁, EA₂])
    (by rintro E (rfl | rfl) i <;> rw [Subsingleton.elim i 0] <;> simp [EA₁, EA₂])
    (fun I hI _ => abs_coeff_le I hI _) ht₂ (by simp)
  refine ⟨C, hsize.trans (by simp [ls]), fun u => ?_⟩
  cases hu : u 0
  · exact hV u Empty.elim (holds_ΓB u hu _)
  · exact hU u _ (holds_ΓA u hu)

/-- Krajíček's form, with one bound `M = 1` on every coefficient of the refutation. -/
example : ∃ C : Circuit Boolean.signature 1 1, C.size ≤ 41088 ∧
    ∀ u, C.eval Boolean.interpretation u 0 = u 0 := by
  obtain ⟨C, hsize, hU, hV⟩ := isProof_ls.exists_circuit_of_abs_coeff_le contra_mem_ls (M := 1)
    (t := 3) abs_coeff_le ht₂ (by simp)
  refine ⟨C, hsize.trans (by simp [ls]), fun u => ?_⟩
  cases hu : u 0
  · exact hV u Empty.elim (holds_ΓB u hu _)
  · exact hU u _ (holds_ΓA u hu)

/-- The semantic refutation behind the circuit has as many lines as the cutting planes
refutation. -/
example : IsSemanticRefutation (initSets ((fun E => {σ | E.Holds σ}) '' ΓA)
    ((fun E => {σ | E.Holds σ}) '' ΓB)) fun j : Fin ls.reverse.length =>
      {σ | ls.reverse[j].Holds σ} :=
  isProof_ls.isSemanticRefutation contra_mem_ls

/-- `x₀ + x₁ ≥ 1`. -/
private noncomputable def E₂ : Ineq (Fin 2 ⊕ Unit) :=
  ⟨Finsupp.single (.inl 0) 1 + Finsupp.single (.inl 1) 1, 1⟩

/-- The search at `x₀ + x₁ ≥ 1` over two shared variables costs at most `4` bits. -/
example (A : Set ((Fin 2 → Bool) × (Unit → Bool))) (B : Set ((Fin 2 → Bool) × (Unit → Bool))) :
    Protocol.ecomplexity (Search {σ | E₂.Holds σ} ExceedsAt) A B ≤ 4 := by
  have h₂ : Nat.clog 2 2 ≤ 1 := Nat.clog_le_of_le_pow (by norm_num)
  have h₅ : Nat.clog 2 5 ≤ 3 := Nat.clog_le_of_le_pow (by norm_num)
  have hle : Nat.clog 2 2 * (Nat.clog 2 (2 * 1 * 2 + 1) + 1) ≤ 4 :=
    (Nat.mul_le_mul h₂ (Nat.add_le_add_right h₅ 1)).trans (by norm_num)
  refine (ecomplexity_search_holds_le E₂ (M₀ := 1) (fun i => ?_) (fun u v i h => ?_) A B).trans
    (by exact_mod_cast hle)
  · fin_cases i <;> simp [E₂]
  · cases hu : u i <;> cases hv : v i <;> fin_cases i <;> simp_all [E₂]

end ComplexityTests.CuttingPlanesInterpolation
