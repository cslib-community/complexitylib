/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Logics.Propositional.Algebraic.CNF.Boolean
import CslibFrontier.Logics.Propositional.Algebraic.SubsetSum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.LinearCombination

/-!
# Tests: algebraic refutations over the Boolean cube

An explicit Nullstellensatz refutation of `1/2 - x` of degree two, which has no polynomial
calculus refutation of degree one; the Impagliazzo–Pudlák–Sgall degree lower bound for the
unsatisfiable subset-sum instance `x₁ + x₂ + x₃ + x₄ = 5` over `ℚ` and over `ZMod 7`, next to the
refutations given by completeness; an instance over the field with nine elements, where `3!`
vanishes but `⌈3/2⌉! = 2` does not; the instance with no variables, which shows that the lower
bound needs `n ≥ 1`; a satisfiable system without refutations; and the clause polynomials of a
contradictory and of a satisfiable CNF formula.
-/

namespace CslibFrontierTests.ProofComplexity.Algebraic

open Cslib Cslib.BitString Cslib.Logic.PL Cslib.Logic.PL.Algebraic MvPolynomial

/-! ### The polynomial `1/2 - x` -/

/-- The polynomial `1/2 - x` in one variable over `ℚ`. -/
private noncomputable abbrev half : MvPolynomial (Fin 1) ℚ :=
  subsetSumPoly (fun _ => 1) (1 / 2)

/-- The identity `(1/2 - x) (2 - 4x) + (x² - x) (-4) = 1`. -/
private theorem half_identity :
    half * (C 2 - C 4 * X 0) + boolAxiom 0 * C (-4) = 1 := by
  have h2 : (C (1 / 2 : ℚ) : MvPolynomial (Fin 1) ℚ) * 2 = 1 := by
    rw [← map_ofNat C 2, ← C_mul]; norm_num
  simp only [half, subsetSumPoly, boolAxiom, Fin.sum_univ_one, map_one, one_mul, map_neg,
    map_ofNat C 2, map_ofNat C 4]
  linear_combination (1 - 2 * X 0) * h2

private theorem totalDegree_X_le (i : Fin 1) : (X i : MvPolynomial (Fin 1) ℚ).totalDegree ≤ 1 :=
  (totalDegree_monomial_le _ _).trans (by simp)

/-- The identity `half_identity` is a Nullstellensatz refutation of `1/2 - x` with the Boolean
axiom, of degree two. -/
theorem half_ns : NS.RefutableInDegree ([half] ++ boolAxioms (Fin 1) ℚ) 2 := by
  have hmem : ∀ t ∈ (Finset.univ : Finset Bool),
      (if t then half else boolAxiom 0) ∈ [half] ++ boolAxioms (Fin 1) ℚ := by
    intro t _
    cases t
    · exact List.mem_append_right _ (boolAxiom_mem_boolAxioms 0)
    · exact List.mem_append_left _ (List.mem_singleton_self _)
  have hdeg : ∀ t ∈ (Finset.univ : Finset Bool),
      (if t then C 2 - C 4 * X 0 else C (-4) : MvPolynomial (Fin 1) ℚ) ≠ 0 →
        (if t then half else boolAxiom 0).totalDegree +
          (if t then C 2 - C 4 * X 0 else C (-4) : MvPolynomial (Fin 1) ℚ).totalDegree ≤ 2 := by
    intro t _ _
    cases t
    · simp only [Bool.false_eq_true, ite_false, totalDegree_C, add_zero]
      exact totalDegree_boolAxiom_le 0
    · simp only [ite_true]
      have h1 : half.totalDegree ≤ 1 := totalDegree_subsetSumPoly_le _ _
      have h2 : (C 2 - C 4 * X 0 : MvPolynomial (Fin 1) ℚ).totalDegree ≤ 1 :=
        (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_C]; omega)
          ((totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add]; exact totalDegree_X_le 0)))
      omega
  obtain ⟨P, hP, hPd⟩ := NS.exists_isProof_of_sum Finset.univ _ _ hmem hdeg
  refine ⟨P, ?_, hPd⟩
  convert hP using 1
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
  exact half_identity.symm

/-- By the simulation of Nullstellensatz, `1/2 - x` is refuted by polynomial calculus in degree
two. -/
example : PC.RefutableInDegree ([half] ++ boolAxioms (Fin 1) ℚ) 2 := .of_ns half_ns

/-- Theorem 5.1 of Impagliazzo–Pudlák–Sgall for `n = 1`: no polynomial calculus refutation of
`1/2 - x` has degree one, so degree two is optimal. -/
example : ¬ PC.RefutableInDegree ([half] ++ boolAxioms (Fin 1) ℚ) 1 :=
  PC.not_refutableInDegree_subsetSumPoly (fun _ => one_ne_zero) _
    (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)) (by simp)

/-- A satisfiable system has no refutation of any degree: `x = 1` solves `1 - x = 0`. -/
example (d : ℕ) : ¬ NS.RefutableInDegree
    ([subsetSumPoly (fun _ : Fin 1 => (1 : ℚ)) 1] ++ boolAxioms (Fin 1) ℚ) d := fun h =>
  h.not_isBoolSolution (fun _ => true) ((isBoolSolution_subsetSumPoly_iff _ _ _).2 (by simp))

/-- With no variables the subset-sum polynomial is the constant `m`, which refutes itself in
degree `0` when `m ≠ 0`. So Theorem 5.1 needs at least one variable. -/
example : PC.RefutableInDegree
    ([subsetSumPoly (fun _ : Fin 0 => (1 : ℚ)) 1] ++ boolAxioms (Fin 0) ℚ) 0 := by
  refine ⟨[1], .mem .nil ?_, List.mem_singleton_self _, by simp⟩
  simp [subsetSumPoly]

/-! ### Unsatisfiable subset-sum instances -/

/-- `x₁ + x₂ + x₃ + x₄ = 5` has no `0/1` solution over `ℚ`. -/
theorem five_ne (x : Fin 4 → Bool) : ∑ i, (fun _ => (1 : ℚ)) i * bitVal ℚ (x i) ≠ 5 := by
  rw [Fin.sum_univ_four]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> norm_num

/-- By completeness, `x₁ + x₂ + x₃ + x₄ = 5` is refuted by polynomial calculus in degree
`4 + 1`. -/
example : PC.RefutableInDegree
    ([subsetSumPoly (fun _ : Fin 4 => (1 : ℚ)) 5] ++ boolAxioms (Fin 4) ℚ) 5 :=
  (PC.refutableInDegree_subsetSumPoly_iff _ _).2 five_ne

/-- Theorem 5.1 of Impagliazzo–Pudlák–Sgall: `x₁ + x₂ + x₃ + x₄ = 5` has no polynomial calculus
refutation of degree `⌈4/2⌉ = 2` over `ℚ`. -/
example : ¬ PC.RefutableInDegree
    ([subsetSumPoly (fun _ : Fin 4 => (1 : ℚ)) 5] ++ boolAxioms (Fin 4) ℚ) 2 :=
  PC.not_refutableInDegree_subsetSumPoly (fun _ => one_ne_zero) _
    (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)) (by simp)

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- `x₁ + x₂ + x₃ + x₄ = 5` has no `0/1` solution over `ZMod 7`. -/
theorem five_ne_zmod (x : Fin 4 → Bool) :
    ∑ i, (fun _ => (1 : ZMod 7)) i * bitVal (ZMod 7) (x i) ≠ 5 := by
  rw [Fin.sum_univ_four]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> decide

/-- Over `ZMod 7`, where `⌈4/2⌉! = 2` is nonzero, the same instance is refuted in degree `5` but has
no Nullstellensatz refutation of degree `2`. -/
example :
    PC.RefutableInDegree
      ([subsetSumPoly (fun _ : Fin 4 => (1 : ZMod 7)) 5] ++ boolAxioms (Fin 4) (ZMod 7)) 5 ∧
    ¬ NS.RefutableInDegree
      ([subsetSumPoly (fun _ : Fin 4 => (1 : ZMod 7)) 5] ++ boolAxioms (Fin 4) (ZMod 7)) 2 :=
  ⟨(PC.refutableInDegree_subsetSumPoly_iff _ _).2 five_ne_zmod,
    NS.not_refutableInDegree_subsetSumPoly (fun _ => one_ne_zero) _ (by decide) (by simp)⟩

/-- The field with nine elements, of characteristic three. -/
private abbrev GF9 := GaloisField 3 2

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- Some element of the field with nine elements is not among `0, 1, 2, 3`. -/
private theorem exists_ne_natCast : ∃ m : GF9, ∀ k : ℕ, k ≤ 3 → (k : GF9) ≠ m := by
  by_contra h
  push Not at h
  choose k hk hkm using h
  have hinj : Function.Injective fun m : GF9 => (⟨k m, by have := hk m; omega⟩ : Fin 4) := by
    intro a b hab
    simp only [Fin.mk.injEq] at hab
    rw [← hkm a, ← hkm b, hab]
  have := Nat.card_le_card_of_injective _ hinj
  rw [GaloisField.card 3 2 (by norm_num), Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

/-- The degree bound needs only `⌈n/2⌉!` to be nonzero. Over the field with nine elements, where
`3! = 6` vanishes, `x₁ + x₂ + x₃ = m` for an `m` outside `0, 1, 2, 3` is refuted in degree `3 + 1`,
but not in degree `⌈3/2⌉ = 2`, since `2! = 2` is nonzero. -/
example : ((Fintype.card (Fin 3)).factorial : GF9) = 0 ∧ ∃ m : GF9,
    PC.RefutableInDegree ([subsetSumPoly (fun _ : Fin 3 => (1 : GF9)) m] ++ boolAxioms (Fin 3) GF9)
      4 ∧
    ¬ PC.RefutableInDegree
      ([subsetSumPoly (fun _ : Fin 3 => (1 : GF9)) m] ++ boolAxioms (Fin 3) GF9) 2 := by
  refine ⟨?_, ?_⟩
  · rw [Fintype.card_fin, CharP.cast_eq_zero_iff GF9 3]
    decide
  obtain ⟨m, hm⟩ := exists_ne_natCast
  refine ⟨m, (PC.refutableInDegree_subsetSumPoly_iff _ _).2 fun x => ?_,
    PC.not_refutableInDegree_subsetSumPoly (fun _ => one_ne_zero) m ?_ (by simp)⟩
  · have hsum : ∑ i, (fun _ => (1 : GF9)) i * bitVal GF9 (x i) =
        ((∑ i, if x i then 1 else 0 : ℕ) : GF9) := by
      rw [Nat.cast_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      cases x i <;> simp
    have hle : (∑ i, if x i then 1 else 0 : ℕ) ≤ 3 :=
      calc (∑ i, if x i then 1 else 0 : ℕ) ≤ ∑ _i : Fin 3, 1 :=
            Finset.sum_le_sum fun i _ => by split <;> omega
        _ = 3 := by simp
    rw [hsum]
    exact hm _ hle
  · have h2 : ((2 : ℕ) : GF9) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff GF9 3]
      decide
    exact h2

/-! ### CNF formulas -/

/-- The clause `x₀ ∨ ¬x₁` becomes `(1 - x₀) x₁`, which vanishes exactly where it is satisfied. -/
example : Clause.toBoolPoly ℚ [((0 : Fin 2), true), (1, false)] = (1 - X 0) * X 1 := by
  simp [Literal.truthPoly]

/-- The contradictory formula `v ∧ ¬v`. -/
def contra : CNF (Fin 1) := [[(0, true)], [(0, false)]]

/-- `v ∧ ¬v` is refuted by polynomial calculus in degree one, by adding its two clause
polynomials `1 - X v` and `X v`. -/
theorem contra_pc : PC.RefutableInDegree (contra.toBoolPolys ℚ ++ boolAxioms (Fin 1) ℚ) 1 := by
  have hpos : (1 - X 0 : MvPolynomial (Fin 1) ℚ) ∈ contra.toBoolPolys ℚ ++ boolAxioms (Fin 1) ℚ :=
    List.mem_append_left _ (by simp [contra, CNF.toBoolPolys, Literal.truthPoly])
  have hneg : (X 0 : MvPolynomial (Fin 1) ℚ) ∈ contra.toBoolPolys ℚ ++ boolAxioms (Fin 1) ℚ :=
    List.mem_append_left _ (by simp [contra, CNF.toBoolPolys, Literal.truthPoly])
  have h := PC.IsProof.linear 1 1 ((PC.IsProof.nil.mem hpos).mem hneg)
    (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (List.mem_cons_self ..)
  rw [map_one, one_mul, one_mul, sub_add_cancel] at h
  refine ⟨_, h, List.mem_cons_self .., ?_⟩
  rw [PC.degree_le_iff]
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · simp
  · exact totalDegree_X_le 0
  · exact (totalDegree_sub _ _).trans (max_le (by simp) (totalDegree_X_le 0))

/-- Soundness for CNF formulas: `v ∧ ¬v` is unsatisfiable. -/
example : ¬ contra.Satisfiable :=
  let ⟨_, hls, h1, _⟩ := contra_pc
  CNF.not_satisfiable_of_pc hls h1

/-- Completeness for CNF formulas: `v ∧ ¬v` is refuted by Nullstellensatz in degree `1 + 1`. -/
example : NS.RefutableInDegree (contra.toBoolPolys ℚ ++ boolAxioms (Fin 1) ℚ)
    (Fintype.card (Fin 1) + 1) :=
  (CNF.ns_refutableInDegree_iff (w := 1) (by decide)).2
    (let ⟨_, hls, h1, _⟩ := contra_pc; CNF.not_satisfiable_of_pc hls h1)

/-- The satisfiable formula `v` has no refutation of any degree. -/
example (d : ℕ) : ¬ NS.RefutableInDegree
    (CNF.toBoolPolys ℚ [[((0 : Fin 1), true)]] ++ boolAxioms (Fin 1) ℚ) d := fun ⟨_, hP, _⟩ =>
  CNF.not_satisfiable_of_ns hP ⟨fun _ => true, by decide⟩

end CslibFrontierTests.ProofComplexity.Algebraic
