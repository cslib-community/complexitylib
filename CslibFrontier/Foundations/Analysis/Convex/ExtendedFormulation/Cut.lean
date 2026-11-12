/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation.Correlation
public import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Tactic.NormNum

/-!
# Exponential extension-complexity lower bound for the cut polytope

The **cut polytope** `cutPolytope K V` (`CUT(n)` for `|V| = n`) is the convex hull of the
characteristic vectors of all cuts `δ(X)` of the complete graph on `V`
[FioriniMassarPokuttaTiwaryDeWolf2015, Section 3.2].

Using the covariance linear isomorphism between `CORR(α)` and `CUT(Option α)` due to
[DeSimone1990] (cited as Theorem 5 in [FioriniMassarPokuttaTiwaryDeWolf2015, Section 3.2]), we
prove `extensionComplexity (cutPolytope K (Option α)) = extensionComplexity (corrPolytope K α)`.
Transporting along `V ≃ Option {v : V // v ≠ v₀}` for any nontrivial finite vertex type `V`
yields the `(3 / 2) ^ (|V| - 1)` lower bound on `xc (cutPolytope K V)`
([FioriniMassarPokuttaTiwaryDeWolf2015, Theorem 7], strengthened via [KaibelWeltge2015, Theorem 1]
to base `3 / 2`).

## Main definitions

* `cutVertex`: the edge characteristic vector of a cut `δ(X)` in the complete graph on `V`.
* `cutPolytope`: `CUT(V) = conv {cutVertex K X | X : Finset V}`.

## Main results

* `extensionComplexity_cutPolytope_option_eq`:
  `extensionComplexity (cutPolytope K (Option α)) = extensionComplexity (corrPolytope K α)`.
* `three_pow_le_two_pow_mul_extensionComplexity_cutPolytope`:
  `(3 : ℕ) ^ (|V| - 1) ≤ 2 ^ (|V| - 1) * extensionComplexity (cutPolytope K V)` for `2 ≤ |V|`.
* `HasExtendedFormulation.three_div_two_pow_le_of_cutPolytope`:
  `(3 / 2 : F) ^ (|V| - 1) ≤ r` whenever `HasExtendedFormulation (cutPolytope K V) r`.

## References

* [DeSimone1990] (via [FioriniMassarPokuttaTiwaryDeWolf2015, Theorem 5]).
* [FioriniMassarPokuttaTiwaryDeWolf2015], Section 3.2 (Theorems 5 and 7).
* [KaibelWeltge2015], Section 2 (Theorem 1).
-/

public section

section Defs

variable (K : Type*) [Semiring K] [PartialOrder K]

/-- The characteristic vector of the cut `δ(X)` in the complete graph on `V`
[FioriniMassarPokuttaTiwaryDeWolf2015, Section 3.2]. -/
@[expose] def cutVertex {V : Type*} [DecidableEq V] (X : Finset V) :
    ↥(⊤ : SimpleGraph V).edgeSet → K :=
  fun e =>
    Sym2.lift ⟨fun u v => if (u ∈ X) ≠ (v ∈ X) then 1 else 0, fun _ _ => by simp only [ne_comm]⟩
      e.1

/-- The **cut polytope** `CUT(V) = conv {χ_{δ(X)} | X ⊆ V}`
[FioriniMassarPokuttaTiwaryDeWolf2015, Section 3.2]. -/
@[expose] def cutPolytope (V : Type*) [DecidableEq V] :
    Set (↥(⊤ : SimpleGraph V).edgeSet → K) :=
  convexHull K (Set.range (cutVertex K))

end Defs

section Iso

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private def corrToCutSym {α : Type*} (y : (α × α) → K) : Option α → Option α → K
  | none, none => 0
  | none, some j => y (j, j)
  | some i, none => y (i, i)
  | some i, some j => y (i, i) + y (j, j) - y (i, j) - y (j, i)

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem corrToCutSym_symm {α : Type*} (y : (α × α) → K) (u v : Option α) :
    corrToCutSym y u v = corrToCutSym y v u := by
  cases u <;> cases v <;> simp only [corrToCutSym]
  abel

private def corrToCutLinear (K : Type*) [Field K]
    (α : Type*) : ((α × α) → K) →ₗ[K] (↥(⊤ : SimpleGraph (Option α)).edgeSet → K) where
  toFun y e := Sym2.lift ⟨corrToCutSym y, corrToCutSym_symm y⟩ e.1
  map_add' y₁ y₂ := by
    ext ⟨e, he⟩
    induction e using Sym2.ind with
    | _ u v =>
        cases u <;> cases v <;> simp only [corrToCutSym, Sym2.lift_mk, Pi.add_apply] <;> ring
  map_smul' c y := by
    ext ⟨e, he⟩
    induction e using Sym2.ind with
    | _ u v =>
        cases u <;> cases v <;> simp only [corrToCutSym, Sym2.lift_mk, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply] <;> ring

private theorem top_edge_none_some {α : Type*} (i : α) :
    s(none, some i) ∈ (⊤ : SimpleGraph (Option α)).edgeSet := by
  simp only [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj, ne_eq, reduceCtorEq, not_false_eq_true]

private theorem top_edge_some_some {α : Type*} {i j : α} (hij : i ≠ j) :
    s(some i, some j) ∈ (⊤ : SimpleGraph (Option α)).edgeSet := by
  simpa only [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj, ne_eq, Option.some.injEq] using hij

private def cutToCorrLinear (K : Type*) [Field K]
    (α : Type*) [DecidableEq α] :
    (↥(⊤ : SimpleGraph (Option α)).edgeSet → K) →ₗ[K] ((α × α) → K) where
  toFun z p := (1 / 2 : K) *
    (z ⟨s(none, some p.1), top_edge_none_some p.1⟩ +
      z ⟨s(none, some p.2), top_edge_none_some p.2⟩ -
      if h : p.1 = p.2 then 0 else z ⟨s(some p.1, some p.2), top_edge_some_some h⟩)
  map_add' z₁ z₂ := by
    ext ⟨i, j⟩
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c z := by
    ext ⟨i, j⟩
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem cutVertex_compl {V : Type*} [Fintype V] [DecidableEq V] (X : Finset V) :
    cutVertex K (Finset.univ \ X) = cutVertex K X := by
  ext ⟨e, he⟩
  induction e using Sym2.ind with
  | _ u v =>
      have hiff : ((u ∈ Finset.univ \ X) ≠ (v ∈ Finset.univ \ X)) ↔ ((u ∈ X) ≠ (v ∈ X)) := by
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        by_cases hu : u ∈ X <;> by_cases hv : v ∈ X <;>
          simp only [hu, hv, not_true_eq_false, not_false_eq_true, ne_eq, true_ne_false,
            false_ne_true]
      simp only [cutVertex, Sym2.lift_mk, hiff]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem corrToCutLinear_corrVertex {α : Type*} [DecidableEq α] (b : Finset α) :
    corrToCutLinear K α (corrVertex K b) = cutVertex K (b.image some) := by
  ext ⟨e, he⟩
  induction e using Sym2.ind with
  | _ u v =>
      cases u <;> cases v
      · simp only [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj, ne_eq, not_true_eq_false] at he
      · rename_i j
        simp only [corrToCutLinear, LinearMap.coe_mk, AddHom.coe_mk, Sym2.lift_mk,
          corrToCutSym, corrVertex, Finset.mem_image, Option.some.injEq, reduceCtorEq,
          and_false, exists_false, cutVertex]
        by_cases hj : j ∈ b
        · simp only [hj, ↓reduceIte, ne_eq, exists_eq_right, false_ne_true, not_false_eq_true,
            and_self]
        · simp only [hj, ↓reduceIte, ne_eq, false_and, exists_eq_right, not_true_eq_false]
      · rename_i i
        simp only [corrToCutLinear, LinearMap.coe_mk, AddHom.coe_mk, Sym2.lift_mk,
          corrToCutSym, corrVertex, Finset.mem_image, Option.some.injEq, reduceCtorEq,
          and_false, exists_false, cutVertex]
        by_cases hi : i ∈ b
        · simp only [hi, ↓reduceIte, ne_eq, exists_eq_right, true_ne_false, not_false_eq_true,
            and_self]
        · simp only [hi, ↓reduceIte, ne_eq, false_and, exists_eq_right, not_true_eq_false]
      · rename_i i j
        simp only [corrToCutLinear, LinearMap.coe_mk, AddHom.coe_mk, Sym2.lift_mk,
          corrToCutSym, corrVertex, cutVertex, Finset.mem_image, Option.some.injEq,
          exists_eq_right]
        by_cases hi : i ∈ b <;> by_cases hj : j ∈ b <;>
          simp only [hi, hj, and_self, and_true, ↓reduceIte, ne_eq, not_true_eq_false,
            true_ne_false, false_ne_true] <;> norm_num

private theorem cutToCorrLinear_cutVertex_image {α : Type*} [DecidableEq α] (b : Finset α) :
    cutToCorrLinear K α (cutVertex K (b.image some)) = corrVertex K b := by
  ext ⟨i, j⟩
  simp only [cutToCorrLinear, LinearMap.coe_mk, AddHom.coe_mk, cutVertex,
    Sym2.lift_mk, Finset.mem_image, Option.some.injEq, exists_eq_right, reduceCtorEq, and_false,
    exists_false, corrVertex]
  by_cases hij : i = j <;> by_cases hi : i ∈ b <;> by_cases hj : j ∈ b <;>
    simp only [hij, hi, hj, ↓reduceDIte, ↓reduceIte, ne_eq, not_true_eq_false, and_self,
      and_true, true_ne_false, false_ne_true] <;>
    norm_num

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem cutVertex_eq_image_some {α : Type*} [Finite α] [DecidableEq α]
    (X : Finset (Option α)) :
    ∃ b : Finset α, cutVertex K X = cutVertex K (b.image some) := by
  let : Fintype α := Fintype.ofFinite α
  let X' : Finset (Option α) := if none ∈ X then Finset.univ \ X else X
  have hX' : cutVertex K X' = cutVertex K X := by
    dsimp only [X']
    split_ifs
    · exact cutVertex_compl X
    · rfl
  have hnone : none ∉ X' := by
    dsimp only [X']
    split_ifs with h
    · simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, h, not_true_eq_false,
        not_false_eq_true]
    · exact h
  refine ⟨Finset.univ.filter fun i => some i ∈ X', ?_⟩
  rw [← hX']
  congr 1
  ext u
  cases u with
  | none =>
      simp only [hnone, Finset.mem_image, reduceCtorEq, and_false, exists_false]
  | some i =>
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Option.some.injEq,
        exists_eq_right]

/-- `CUT(Option α)` and `CORR(α)` have identical extension complexity
[DeSimone1990]; [FioriniMassarPokuttaTiwaryDeWolf2015, Theorem 5]. -/
theorem extensionComplexity_cutPolytope_option_eq (α : Type*) [Fintype α] [DecidableEq α] :
    extensionComplexity (cutPolytope K (Option α)) = extensionComplexity (corrPolytope K α) := by
  have him₁ : corrToCutLinear K α '' Set.range (corrVertex K) = Set.range (cutVertex K) := by
    ext z
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
      exact ⟨b.image some, (corrToCutLinear_corrVertex b).symm⟩
    · rintro ⟨X, rfl⟩
      obtain ⟨b, hb⟩ := cutVertex_eq_image_some (K := K) X
      exact ⟨corrVertex K b, ⟨b, rfl⟩, by rw [hb, corrToCutLinear_corrVertex]⟩
  have him₂ : cutToCorrLinear K α '' Set.range (cutVertex K) = Set.range (corrVertex K) := by
    ext y
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨X, rfl⟩, rfl⟩
      obtain ⟨b, hb⟩ := cutVertex_eq_image_some (K := K) X
      exact ⟨b, by rw [hb, cutToCorrLinear_cutVertex_image]⟩
    · rintro ⟨b, rfl⟩
      exact ⟨cutVertex K (b.image some), ⟨b.image some, rfl⟩, cutToCorrLinear_cutVertex_image b⟩
  refine extensionComplexity_eq_of_linearMaps (corrToCutLinear K α) (cutToCorrLinear K α) ?_ ?_
  · rw [corrPolytope, LinearMap.image_convexHull, him₁, cutPolytope]
  · rw [cutPolytope, LinearMap.image_convexHull, him₂, corrPolytope]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem cutVertex_funLeft {V₁ V₂ : Type*} [DecidableEq V₁] [DecidableEq V₂]
    (e : V₁ ≃ V₂) (Y : Finset V₂) :
    LinearMap.funLeft K K (SimpleGraph.Iso.completeGraph e).mapEdgeSet (cutVertex K Y) =
      cutVertex K (Y.image e.symm) := by
  ext ⟨s, hs⟩
  induction s using Sym2.ind with
  | _ u v =>
      change cutVertex K Y ⟨s(e u, e v), _⟩ = cutVertex K (Y.image e.symm) ⟨s(u, v), hs⟩
      simp only [cutVertex, Sym2.lift_mk, Finset.mem_image]
      have hiff : ∀ w : V₁, (∃ a ∈ Y, e.symm a = w) ↔ e w ∈ Y := fun w =>
        ⟨fun ⟨a, ha, haw⟩ => haw ▸ (e.apply_symm_apply a).symm ▸ ha,
          fun hw => ⟨e w, hw, e.symm_apply_apply w⟩⟩
      simp only [hiff]

omit [IsStrictOrderedRing K] in
private theorem image_cutPolytope_funLeft {V W : Type*}
    [DecidableEq V] [DecidableEq W] (e : V ≃ W) :
    (LinearMap.funLeft K K (SimpleGraph.Iso.completeGraph e).mapEdgeSet) ''
        (cutPolytope K (V := W)) =
      cutPolytope K (V := V) := by
  rw [cutPolytope, LinearMap.image_convexHull, cutPolytope]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨Y, rfl⟩, rfl⟩
    exact ⟨Y.image e.symm, (cutVertex_funLeft e Y).symm⟩
  · rintro ⟨X, rfl⟩
    refine ⟨cutVertex K (X.image e), ⟨X.image e, rfl⟩, ?_⟩
    rw [cutVertex_funLeft e, Finset.image_image]
    simp only [Equiv.symm_comp_self, Finset.image_id]

omit [IsStrictOrderedRing K] in
private theorem extensionComplexity_cutPolytope_congr {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (e : V ≃ W) :
    extensionComplexity (cutPolytope K V) = extensionComplexity (cutPolytope K W) := by
  let f : (↥(⊤ : SimpleGraph V).edgeSet → K) →ₗ[K] (↥(⊤ : SimpleGraph W).edgeSet → K) :=
    LinearMap.funLeft K K (SimpleGraph.Iso.completeGraph e.symm).mapEdgeSet
  let g : (↥(⊤ : SimpleGraph W).edgeSet → K) →ₗ[K] (↥(⊤ : SimpleGraph V).edgeSet → K) :=
    LinearMap.funLeft K K (SimpleGraph.Iso.completeGraph e).mapEdgeSet
  refine extensionComplexity_eq_of_linearMaps g f ?_ ?_
  · exact image_cutPolytope_funLeft e
  · simpa only [Equiv.symm_symm] using image_cutPolytope_funLeft e.symm

end Iso

section LowerBound

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Every extended formulation of `cutPolytope K (Option α)` (`|α| ≥ 1`) satisfies
`3 ^ |α| ≤ 2 ^ |α| * xc (cutPolytope K (Option α))`
[FioriniMassarPokuttaTiwaryDeWolf2015, Theorems 5 and 7]; [KaibelWeltge2015, Theorem 1]. -/
theorem three_pow_le_two_pow_mul_extensionComplexity_cutPolytope_option
    (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α] :
    ((3 ^ Fintype.card α : ℕ) : ℕ∞) ≤
      (2 ^ Fintype.card α : ℕ∞) * extensionComplexity (cutPolytope K (Option α)) := by
  rw [extensionComplexity_cutPolytope_option_eq]
  exact three_pow_le_two_pow_mul_extensionComplexity_corrPolytope

/-- Exponential lower bound on the extension complexity of `cutPolytope K V` for any finite
vertex type `V` with `|V| ≥ 2` [FioriniMassarPokuttaTiwaryDeWolf2015, Theorem 7]. -/
theorem three_pow_le_two_pow_mul_extensionComplexity_cutPolytope
    (V : Type*) [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V) :
    ((3 ^ (Fintype.card V - 1) : ℕ) : ℕ∞) ≤
      (2 ^ (Fintype.card V - 1) : ℕ∞) * extensionComplexity (cutPolytope K V) := by
  have hnt : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  let v₀ : V := Classical.arbitrary V
  obtain ⟨v₁, hv₁⟩ := exists_ne v₀
  let α := {v : V // v ≠ v₀}
  have : Nonempty α := ⟨⟨v₁, hv₁⟩⟩
  let e : V ≃ Option α :=
    { toFun := fun v => if h : v = v₀ then none else some ⟨v, h⟩
      invFun := Option.elim' v₀ Subtype.val
      left_inv := fun v => by
        by_cases h : v = v₀ <;> simp only [h, ↓reduceDIte, Option.elim'_none, Option.elim'_some]
      right_inv := fun o => by
        cases o with
        | none => simp only [Option.elim'_none, ↓reduceDIte]
        | some a =>
            dsimp only [Option.elim'_some]
            simp only [a.2, ↓reduceDIte]
            rfl }
  have hcard : Fintype.card α = Fintype.card V - 1 := by
    have := Fintype.card_congr e
    rw [Fintype.card_option] at this
    omega
  rw [extensionComplexity_cutPolytope_congr e, ← hcard]
  exact three_pow_le_two_pow_mul_extensionComplexity_cutPolytope_option α

/-- Field-valued exponential lower bound: any extended formulation of `cutPolytope K V`
(`|V| ≥ 2`) with `r` inequalities satisfies `(3 / 2 : F) ^ (|V| - 1) ≤ r`. -/
theorem HasExtendedFormulation.three_div_two_pow_le_of_cutPolytope
    {V : Type*} [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V)
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {r : ℕ} (hr : HasExtendedFormulation (cutPolytope K V) r) :
    (3 / 2 : F) ^ (Fintype.card V - 1) ≤ r :=
  hr.three_div_two_pow_le_of_mul_le (three_pow_le_two_pow_mul_extensionComplexity_cutPolytope V hV)

end LowerBound
