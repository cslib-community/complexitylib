/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexity.Foundations.Combinatorics.SimpleGraph.Pentagon

public section

open SimpleGraph Filter Topology
open scoped RealInnerProductSpace

namespace Cslib.Tests.LovaszTheta

/-! ### Strong products are decidable -/

example : (cycleGraph 5 ⊠ cycleGraph 5).Adj (0, 0) (1, 4) := by decide
example : ¬(cycleGraph 5 ⊠ cycleGraph 5).Adj (0, 0) (2, 1) := by decide
example : ¬(cycleGraph 5 ⊠ cycleGraph 5).Adj (3, 3) (3, 3) := by decide
example : ((cycleGraph 5).strongPow 2).Adj ![0, 0] ![1, 0] := by decide

/-! ### Orthonormal representations: an instance and a non-instance -/

/-- The umbrella is an orthonormal representation of `C₅`. -/
example : (cycleGraph 5).IsOrthonormalRepresentation pentagonUmbrella :=
  isOrthonormalRepresentation_pentagonUmbrella

/-- A constant unit vector is not an orthonormal representation of `C₅`: the nonadjacent vertices
`0` and `2` get the same vector. -/
example : ¬(cycleGraph 5).IsOrthonormalRepresentation
    (fun _ => EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) := by
  intro h
  have := h.inner_eq_zero (v := 0) (w := 2) (by decide) (by decide)
  simp at this

/-! ### The pentagon: `α(C₅) = 2 < √5 = Θ(C₅) = ϑ(C₅)` -/

example : (cycleGraph 5).indepNum = 2 := indepNum_cycleGraph_five
example : (cycleGraph 5).shannonCapacity = √5 := shannonCapacity_cycleGraph_five
example : (cycleGraph 5).lovaszTheta = √5 := lovaszTheta_cycleGraph_five

/-- The capacity of `C₅` strictly exceeds its independence number. -/
example : ((cycleGraph 5).indepNum : ℝ) < (cycleGraph 5).shannonCapacity := by
  rw [indepNum_cycleGraph_five, shannonCapacity_cycleGraph_five, Real.lt_sqrt (by norm_num)]
  norm_num

/-- The clique-cover form of the upper sandwich bound: three cliques cover `C₅`, so
`ϑ(C₅) ≤ 3`. This is weaker than `ϑ(C₅) = √5`, as it should be. -/
example : (cycleGraph 5).lovaszTheta ≤ 3 := by
  have h := lovaszTheta_le_of_cliqueCover (G := cycleGraph 5) (S := {{0, 1}, {2, 3}, {4}})
    (by decide) (by decide)
  have hcard : ({{0, 1}, {2, 3}, {4}} : Finset (Finset (Fin 5))).card = 3 := by decide
  rw [hcard] at h
  exact_mod_cast h

/-! ### Edge cases: empty, complete and edgeless graphs -/

example : (⊥ : SimpleGraph (Fin 0)).lovaszTheta = 0 := lovaszTheta_eq_zero_of_isEmpty
example : (⊥ : SimpleGraph (Fin 0)).shannonCapacity = 0 := shannonCapacity_eq_zero_of_isEmpty

/-- `ϑ(Kₙ) = 1` for `n ≥ 1`: the complement is edgeless, hence `1`-colourable, and `α(Kₙ) = 1`. -/
example (n : ℕ) : (⊤ : SimpleGraph (Fin (n + 1))).lovaszTheta = 1 := by
  refine le_antisymm ?_ ?_
  · simpa using lovaszTheta_le_of_colorable_compl (G := (⊤ : SimpleGraph (Fin (n + 1))))
      (k := 1) (by simp)
  · have h := indepNum_le_lovaszTheta (G := (⊤ : SimpleGraph (Fin (n + 1))))
    rw [← cliqueNum_compl, compl_top, cliqueNum_bot, Nat.cast_one] at h
    exact h

/-- The edgeless graph on `n` vertices has `α = Θ = ϑ = n`. -/
example (n : ℕ) : (⊥ : SimpleGraph (Fin n)).shannonCapacity = n ∧
    (⊥ : SimpleGraph (Fin n)).lovaszTheta = n := by
  have hα : ((⊥ : SimpleGraph (Fin n)).indepNum : ℝ) = n := by
    rw [← cliqueNum_compl, compl_bot, cliqueNum_top, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hϑ : (⊥ : SimpleGraph (Fin n)).lovaszTheta ≤ n := by
    simpa using lovaszTheta_le_natCard (G := (⊥ : SimpleGraph (Fin n)))
  have h₁ := indepNum_le_shannonCapacity (G := (⊥ : SimpleGraph (Fin n)))
  have h₂ := shannonCapacity_le_lovaszTheta (G := (⊥ : SimpleGraph (Fin n)))
  rw [hα] at h₁
  exact ⟨le_antisymm (h₂.trans hϑ) h₁, le_antisymm hϑ (h₁.trans h₂)⟩

/-! ### An independent restatement of `Θ(C₅) = √5`

The definitions below restate the problem `shannon_capacity_pentagon` of the lean-eval benchmark
(`LeanEval/Combinatorics/ShannonCapacityPentagon.lean` in `leanprover/lean-eval`, Apache-2.0)
from scratch, without the library's `indepNum`, `strongPow` or `shannonCapacity`: independent sets
as finsets, the independence number as a supremum of their sizes, the strong power on words, and
the capacity as the limit of the normalized independence numbers. -/

/-- No two distinct members of `s` are adjacent. -/
def IsIndependent {V : Type*} (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ ⦃v⦄, v ∈ s → ∀ ⦃w⦄, w ∈ s → v ≠ w → ¬G.Adj v w

/-- The largest size of an independent finset. -/
noncomputable def independenceNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sSup {m : ℕ | ∃ s : Finset V, IsIndependent G s ∧ s.card = m}

/-- Distinct words are confusable when every coordinate is equal or confusable. -/
def strongPower {V : Type*} (G : SimpleGraph V) (k : ℕ) : SimpleGraph (Fin k → V) where
  Adj x y := x ≠ y ∧ ∀ i, x i = y i ∨ G.Adj (x i) (y i)
  symm := ⟨fun _ _ ⟨hxy, h⟩ => ⟨hxy.symm, fun i => (h i).imp Eq.symm Adj.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- `θ` is the Shannon capacity: `α(Gᵏ)^(1/k) → θ`. -/
def HasShannonCapacity {V : Type*} (G : SimpleGraph V) (θ : ℝ) : Prop :=
  Tendsto (fun k : ℕ => Real.rpow (independenceNumber (strongPower G (k + 1)) : ℝ) ((k + 1 : ℝ)⁻¹))
    atTop (𝓝 θ)

theorem independenceNumber_eq_indepNum {V : Type*} (G : SimpleGraph V) :
    independenceNumber G = G.indepNum := by
  simp only [independenceNumber, indepNum, isNIndepSet_iff]
  rfl

theorem strongPower_eq_strongPow {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    strongPower G k = G.strongPow k := by
  ext
  rfl

/-- **Lovász**: the Shannon capacity of the pentagon is `√5`, in the restated form. -/
theorem shannon_capacity_pentagon : HasShannonCapacity (cycleGraph 5) √5 := by
  simp only [HasShannonCapacity, strongPower_eq_strongPow, independenceNumber_eq_indepNum]
  exact tendsto_indepNum_strongPow_cycleGraph_five

end Cslib.Tests.LovaszTheta
