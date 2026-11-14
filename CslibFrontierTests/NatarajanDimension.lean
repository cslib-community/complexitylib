/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.MachineLearning.PACLearning.NatarajanDimension
public import CslibFrontier.MachineLearning.PACLearning.Halfspaces

/-!
# Checks for the Natarajan dimension

Exercises `CslibFrontier.MachineLearning.PACLearning.NatarajanDimension`:

* **All labelings:** with two distinct labels, the class of all functions N-shatters every set.
  On a finite domain its Natarajan dimension is the number of points, and with `Bool` labels on
  three points Natarajan's lemma is attained.
* **Constant functions:** they N-shatter a single point and never two points, so their Natarajan
  dimension is `1`. Natarajan's lemma then bounds every class on four points with three labels and
  Natarajan dimension at most `1` by `13`, far below the `81` functions.
* **Two labels:** the Natarajan dimension of homogeneous halfspaces in the plane is their VC
  dimension `2`.
-/

public section

namespace CslibFrontierTests.NatarajanDimension

open Cslib.MachineLearning.PACLearning

variable {α β : Type*}

/-- With two distinct labels the class of all functions N-shatters every set: the constant
labelings witness it, and for `B ⊆ W` the indicator of `B` realizes `B`. -/
theorem natarajanShatters_univ {b₀ b₁ : β} (hb : b₀ ≠ b₁) (W : Set α) :
    NatarajanShatters (Set.univ : ConceptClass α β) W := by
  classical
  refine ⟨fun _ => b₀, fun _ => b₁, fun _ _ => hb, fun B _ => ?_⟩
  exact ⟨fun x => if x ∈ B then b₀ else b₁, Set.mem_univ _, fun x hx => by simp [hx],
    fun x hx => by simp [hx.2]⟩

/-- On a finite domain, the class of all functions to a type with two labels has Natarajan
dimension equal to the number of points. -/
theorem natarajanDim_univ [Fintype α] {b₀ b₁ : β} (hb : b₀ ≠ b₁) :
    natarajanDim (Set.univ : ConceptClass α β) = Fintype.card α :=
  le_antisymm (natarajanDim_le fun W _ => W.card_le_univ)
    ((natarajanShatters_univ hb _).card_le_natarajanDim (hasFiniteNatarajanDim_of_finite _)
      (W := Finset.univ) |>.trans_eq' Finset.card_univ.symm)

example : natarajanDim (Set.univ : ConceptClass (Fin 5) (Fin 3)) = 5 := by
  rw [natarajanDim_univ (b₀ := 0) (b₁ := 1) (by decide), Fintype.card_fin]

/-- With `Bool` labels on three points the bound of Natarajan's lemma is attained by the class of
all `8` functions. -/
example : (Set.univ : ConceptClass (Fin 3) Bool).ncard = natarajanSum 3 (Fintype.card Bool) 3 := by
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool]
  decide

/-- The constant functions. -/
def constants (β : Type*) : ConceptClass α β := Set.range fun b : β => fun _ : α => b

/-- The constant functions N-shatter no two-point set: the labeling that agrees with the first
witness at one point and with the second at the other cannot be constant. -/
theorem not_natarajanShatters_constants_pair {x y : α} (hxy : x ≠ y) :
    ¬ NatarajanShatters (constants (α := α) β) {x, y} := by
  rintro ⟨f₀, f₁, hne, h⟩
  obtain ⟨_, ⟨b, rfl⟩, -, h₁⟩ := h ∅ (Set.empty_subset _)
  obtain ⟨_, ⟨b', rfl⟩, h₀', h₁'⟩ := h {x} (by simp)
  have hx : b = f₁ x := h₁ x ⟨by simp, Set.notMem_empty x⟩
  have hy : b = f₁ y := h₁ y ⟨by simp, Set.notMem_empty y⟩
  have hx' : b' = f₀ x := h₀' x rfl
  have hy' : b' = f₁ y := h₁' y ⟨by simp, fun h => hxy (Set.mem_singleton_iff.1 h).symm⟩
  exact hne x (by simp) (by rw [← hx', hy', ← hy, hx])

/-- With two distinct labels the constant functions N-shatter every single point. -/
theorem natarajanShatters_constants_singleton {b₀ b₁ : β} (hb : b₀ ≠ b₁) (x : α) :
    NatarajanShatters (constants (α := α) β) {x} := by
  classical
  refine ⟨fun _ => b₀, fun _ => b₁, fun _ _ => hb, fun B hB => ?_⟩
  by_cases hx : x ∈ B
  · refine ⟨fun _ => b₀, ⟨b₀, rfl⟩, fun _ _ => rfl, fun y hy => ?_⟩
    exact absurd (Set.mem_singleton_iff.1 hy.1 ▸ hx) hy.2
  · refine ⟨fun _ => b₁, ⟨b₁, rfl⟩, fun y hy => ?_, fun _ _ => rfl⟩
    exact absurd (Set.mem_singleton_iff.1 (hB hy) ▸ hy) hx

/-- Every finite set N-shattered by the constant functions has at most one point. -/
theorem card_le_one_of_natarajanShatters_constants {W : Finset α}
    (hW : NatarajanShatters (constants (α := α) β) ↑W) : W.card ≤ 1 := by
  by_contra h
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (not_le.1 h)
  exact not_natarajanShatters_constants_pair hxy
    (hW.subset (by simp [Set.insert_subset_iff, hx, hy]))

/-- With at least two labels the constant functions on a nonempty domain have Natarajan
dimension `1`. -/
theorem natarajanDim_constants [Nonempty α] {b₀ b₁ : β} (hb : b₀ ≠ b₁) :
    natarajanDim (constants (α := α) β) = 1 := by
  obtain ⟨x⟩ := ‹Nonempty α›
  refine le_antisymm (natarajanDim_le fun W hW => card_le_one_of_natarajanShatters_constants hW) ?_
  have hfin : HasFiniteNatarajanDim (constants (α := α) β) :=
    hasFiniteNatarajanDim_iff.2 ⟨1, fun W hW => card_le_one_of_natarajanShatters_constants hW⟩
  have h := natarajanShatters_constants_singleton (α := α) hb x
  rw [← Finset.coe_singleton] at h
  simpa using h.card_le_natarajanDim hfin

/-- Natarajan's lemma on four points with three labels: a class whose N-shattered sets have at
most one point has at most `1 + 4 · 3 = 13` of the `81` functions. -/
theorem ncard_le_thirteen {C : ConceptClass (Fin 4) (Fin 3)}
    (hC : ∀ W : Finset (Fin 4), NatarajanShatters C ↑W → W.card ≤ 1) : C.ncard ≤ 13 :=
  (ncard_le_natarajanSum hC).trans (by rw [Fintype.card_fin]; decide)

/-- The constant functions on four points satisfy the hypothesis of `ncard_le_thirteen`. -/
example : (constants (α := Fin 4) (Fin 3)).ncard ≤ 13 :=
  ncard_le_thirteen fun _ hW => card_le_one_of_natarajanShatters_constants hW

/-- All `81` functions from four points to three labels N-shatter a two-point set, so
`ncard_le_thirteen` does not apply to them. -/
example : NatarajanShatters (Set.univ : ConceptClass (Fin 4) (Fin 3)) ↑({0, 1} : Finset (Fin 4)) :=
  natarajanShatters_univ (b₀ := 0) (b₁ := 1) (by decide) _

/-- With two labels the Natarajan dimension is the VC dimension: homogeneous halfspaces in the
plane have Natarajan dimension `2`. -/
example : natarajanDim (homogeneousHalfspaces 2) = 2 := by
  rw [natarajanDim_eq_vcDim, vcDim_homogeneousHalfspaces]

end CslibFrontierTests.NatarajanDimension
