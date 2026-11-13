/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.AffineDisperser.Basic
public import CslibFrontier.Foundations.Combinatorics.AffineDisperser.AffineSubspace
public import CslibFrontier.Foundations.Data.BitString.AffineSubspace
public import CslibFrontier.Probability.MinEntropy
public import CslibFrontier.Probability.Product
public import CslibFrontier.Probability.StatisticalDistance
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Foundations.Data.BitString.ZModTwo
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith

/-!
# Affine sources, conditioning, block decomposition, and disperser bridges

This module provides the foundational theory of affine sources over `𝔽₂` (`Bool`) needed for
explicit affine condensers and extractors ([Li2023], [LiZhong2024]):

* `Cslib.AffineDisperser.Li.uniformAffine`: the uniform distribution on a nonempty affine subspace
  of `BitString n`.
* `Cslib.AffineDisperser.Li.IsAffineSource`: an `(n, k)` affine source (`[Li2023, Def. 3.1]`,
  `[LiZhong2024, Def. 15]`).
* `Cslib.AffineDisperser.Li.blockEquiv`: canonical isomorphism between `BitString (∑ i, b i)`
  and partitioned bit-blocks `∀ i : Fin t, BitString (b i)`.
* `Cslib.AffineDisperser.Li.IsAffineExtractor`: seedless `(k, ε)`-affine extractors.
* `Cslib.AffineDisperser.Li.IsSumsetExtractor`: `(k₁, k₂, ε)`-sumset extractors
  (`[Li2023, Thm. 7.13]`).

## Main results

* `Cslib.AffineDisperser.Li.minEntropy_of_isAffineSource`: an `(n, k)` affine source has
  min-entropy `k`.
* `Cslib.AffineDisperser.Li.isAffineSource_map_of_isAffine`: any affine image of an affine source
  is an affine source whose dimension is the rank of the linear part on its direction.
* `Cslib.AffineDisperser.Li.affineConditioning`: **Affine Conditioning Lemma**
  (`[Li2023, Lemma 3.9]`, `[LiZhong2024, Lemma 8]`), decomposing `X = A + B` for any affine map
  `L` so that `A` and `B` are independent affine sources, `L` is constant on `B`, `A` is
  affinely recoverable from `L(A)`, and conditioning `X` on `L(x) = ℓ` yields a translate of `B`.
* `Cslib.AffineDisperser.Li.affineBlockDecomposition`: **Affine Block Decomposition**
  (`[Li2023, Lemma 3.10]`), expressing an affine source of codimension `≤ r` on partitioned blocks
  as a mixture of independent product affine sources (`PMF.pi`) of codimension `≤ r` in every
  block.
* `Cslib.AffineDisperser.Li.isAffineDisperser_of_isAffineExtractor`,
  `Cslib.AffineDisperser.Li.isAffineExtractor_of_isSumsetExtractor`,
  `Cslib.AffineDisperser.Li.isAffineDisperser_of_isSumsetExtractor`: bridges from sumset and affine
  extractors to `Cslib.BitString.IsAffineDisperser` (`[Li2023, Cor. 7.14]`).

## References

* [X. Li, *Two Source Extractors for Asymptotically Optimal Entropy, and (Many) More*][Li2023],
  Section 3 (Definition 3.1, Lemma 3.9, Lemma 3.10) and Section 7 (Theorem 7.13, Corollary 7.14)
* [X. Li and Y. Zhong, *Explicit Directional Affine Extractors and Improved Hardness for Linear
  Branching Programs*][LiZhong2024], Section 3 and Appendix B (Lemma 8, Definition 15)
-/

public section

namespace Cslib.AffineDisperser.Li

open Cslib.BitString Cslib.Probability Cslib.Probability.PMF Module

/-! ### Transfer between `Bool`-modules and `(ZMod 2)`-vector spaces -/

section BoolVectorSpace

private def toZModBits (ι : Type*) : (ι → Bool) ≃+ (ι → ZMod 2) where
  toFun v i := bitEquiv.symm (v i)
  invFun v i := bitEquiv (v i)
  left_inv v := funext fun i => bitEquiv.apply_symm_apply (v i)
  right_inv v := funext fun i => bitEquiv.symm_apply_apply (v i)
  map_add' u v := funext fun i => map_add bitEquiv.symm (u i) (v i)

private theorem toZModBits_smul {ι : Type*} (c : Bool) (v : ι → Bool) :
    toZModBits ι (c • v) = bitEquiv.symm c • toZModBits ι v :=
  funext fun i => map_mul bitEquiv.symm c (v i)

private theorem symm_toZModBits_smul {ι : Type*} (c : ZMod 2) (v : ι → ZMod 2) :
    (toZModBits ι).symm (c • v) = bitEquiv c • (toZModBits ι).symm v := by
  apply (toZModBits ι).injective
  rw [toZModBits_smul, (toZModBits ι).apply_symm_apply, (toZModBits ι).apply_symm_apply,
    bitEquiv.symm_apply_apply]

private def toZModSub {ι : Type*} (V : Submodule Bool (ι → Bool)) :
    Submodule (ZMod 2) (ι → ZMod 2) where
  carrier := toZModBits ι '' (V : Set (ι → Bool))
  zero_mem' := ⟨0, V.zero_mem, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, V.add_mem hx hy, map_add _ x y⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, rfl⟩
    refine ⟨bitEquiv c • x, V.smul_mem _ hx, ?_⟩
    rw [toZModBits_smul, bitEquiv.symm_apply_apply]

private def ofZModSub {ι : Type*} (W : Submodule (ZMod 2) (ι → ZMod 2)) :
    Submodule Bool (ι → Bool) where
  carrier := (toZModBits ι).symm '' (W : Set (ι → ZMod 2))
  zero_mem' := ⟨0, W.zero_mem, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, W.add_mem hx hy, map_add _ x y⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, rfl⟩
    refine ⟨bitEquiv.symm c • x, W.smul_mem _ hx, ?_⟩
    rw [symm_toZModBits_smul, bitEquiv.apply_symm_apply]

private theorem mem_toZModSub {ι : Type*} {V : Submodule Bool (ι → Bool)} {x : ι → Bool} :
    toZModBits ι x ∈ toZModSub V ↔ x ∈ V := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [← (toZModBits ι).injective hyx]
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem mem_ofZModSub {ι : Type*} {W : Submodule (ZMod 2) (ι → ZMod 2)} {x : ι → Bool} :
    x ∈ ofZModSub W ↔ toZModBits ι x ∈ W := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [← hyx, (toZModBits ι).apply_symm_apply]
  · intro hx
    exact ⟨toZModBits ι x, hx, (toZModBits ι).symm_apply_apply x⟩

private theorem toZModSub_le_iff {ι : Type*} {U V : Submodule Bool (ι → Bool)} :
    toZModSub U ≤ toZModSub V ↔ U ≤ V := by
  constructor
  · intro h x hx
    exact mem_toZModSub.mp (h (mem_toZModSub.mpr hx))
  · rintro h _ ⟨x, hx, rfl⟩
    exact mem_toZModSub.mpr (h hx)

private theorem toZModSub_inf {ι : Type*} (U V : Submodule Bool (ι → Bool)) :
    toZModSub (U ⊓ V) = toZModSub U ⊓ toZModSub V := by
  ext y
  obtain ⟨x, rfl⟩ := (toZModBits ι).surjective y
  rw [mem_toZModSub, Submodule.mem_inf, Submodule.mem_inf, mem_toZModSub, mem_toZModSub]

private theorem toZModSub_sup {ι : Type*} (U V : Submodule Bool (ι → Bool)) :
    toZModSub (U ⊔ V) = toZModSub U ⊔ toZModSub V := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hz
    rw [map_add]
    exact Submodule.add_mem_sup (mem_toZModSub.mpr hu) (mem_toZModSub.mpr hv)
  · refine sup_le ?_ ?_ <;> rw [toZModSub_le_iff]
    · exact le_sup_left
    · exact le_sup_right

private def toZModSubEquiv {ι : Type*} (V : Submodule Bool (ι → Bool)) :
    V ≃+ toZModSub V where
  toFun v := ⟨toZModBits ι v.1, mem_toZModSub.mpr v.2⟩
  invFun w := ⟨(toZModBits ι).symm w.1, by
    rw [← mem_toZModSub, (toZModBits ι).apply_symm_apply]; exact w.2⟩
  left_inv v := Subtype.ext ((toZModBits ι).symm_apply_apply v.1)
  right_inv w := Subtype.ext ((toZModBits ι).apply_symm_apply w.1)
  map_add' u v := Subtype.ext (map_add (toZModBits ι) u.1 v.1)

private theorem finrank_bool_eq_finrank_toZMod {ι : Type*} (V : Submodule Bool (ι → Bool)) :
    finrank Bool V = finrank (ZMod 2) (toZModSub V) := by
  have h := rank_eq_of_equiv_equiv (R := Bool) (R' := ZMod 2) (M := V) (M₁ := toZModSub V)
    bitEquiv.symm (toZModSubEquiv V) bitEquiv.symm.bijective fun c v =>
    Subtype.ext (toZModBits_smul c v.1)
  exact congrArg Cardinal.toNat h

private theorem natCard_submodule_bool {ι : Type*} [Finite ι] (V : Submodule Bool (ι → Bool)) :
    Nat.card V = 2 ^ finrank Bool V := by
  have eV := (toZModSubEquiv V).toEquiv
  have hcard : Nat.card V = Nat.card (toZModSub V) := Nat.card_congr eV
  have : Finite (toZModSub V) := Finite.of_equiv V eV
  let _ : Fintype (toZModSub V) := Fintype.ofFinite _
  let B := Module.finBasis (ZMod 2) (toZModSub V)
  have hcard2 : Fintype.card (toZModSub V) = 2 ^ finrank (ZMod 2) (toZModSub V) := by
    rw [Fintype.card_congr B.equivFun.toEquiv, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  rw [hcard, Nat.card_eq_fintype_card, hcard2, finrank_bool_eq_finrank_toZMod]

/-- Complementing a `Bool`-submodule inside another `Bool`-submodule of `ι → Bool`. -/
theorem exists_isCompl_submodule {ι : Type*} (K V : Submodule Bool (ι → Bool))
    (hKV : K ≤ V) :
    ∃ U : Submodule Bool (ι → Bool), U ≤ V ∧ U ⊓ K = ⊥ ∧ U ⊔ K = V := by
  let KZ : Submodule (ZMod 2) (toZModSub V) := (toZModSub K).comap (toZModSub V).subtype
  obtain ⟨UZ, hUZ⟩ := Submodule.exists_isCompl KZ
  let U : Submodule Bool (ι → Bool) := ofZModSub (UZ.map (toZModSub V).subtype)
  have hUZ_eq : toZModSub U = UZ.map (toZModSub V).subtype := by
    ext y
    obtain ⟨x, rfl⟩ := (toZModBits ι).surjective y
    rw [mem_toZModSub, mem_ofZModSub]
  refine ⟨U, ?_, ?_, ?_⟩
  · rw [← toZModSub_le_iff, hUZ_eq]
    exact Submodule.map_subtype_le _ _
  · have hinf : toZModSub (U ⊓ K) = ⊥ := by
      rw [toZModSub_inf, hUZ_eq, eq_bot_iff]
      rintro y ⟨hy1, hy2⟩
      obtain ⟨⟨w, hwV⟩, hwU, rfl⟩ := Submodule.mem_map.mp hy1
      have hmem : (⟨w, hwV⟩ : toZModSub V) ∈ KZ ⊓ UZ := ⟨hy2, hwU⟩
      rw [hUZ.inf_eq_bot, Submodule.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    ext x
    rw [← mem_toZModSub, hinf, Submodule.mem_bot, Submodule.mem_bot,
      (toZModBits ι).map_eq_zero_iff]
  · apply le_antisymm
    · exact sup_le (by rw [← toZModSub_le_iff, hUZ_eq]; exact Submodule.map_subtype_le _ _) hKV
    · rw [← toZModSub_le_iff, toZModSub_sup, hUZ_eq]
      intro w hw
      have hmem : (⟨w, hw⟩ : toZModSub V) ∈ KZ ⊔ UZ := by
        rw [hUZ.sup_eq_top]; trivial
      obtain ⟨k, hk, u, hu, hku⟩ := Submodule.mem_sup.mp hmem
      rw [sup_comm]
      refine Submodule.mem_sup.mpr ⟨k.1, hk, u.1, Submodule.mem_map.mpr ⟨u, hu, rfl⟩, ?_⟩
      exact congrArg Subtype.val hku

/-- Dimension formula for the sum and intersection of two `Bool`-submodules of `ι → Bool`. -/
theorem finrank_sup_add_finrank_inf_bitString {ι : Type*} [Finite ι]
    (U K : Submodule Bool (ι → Bool)) :
    finrank Bool ↥(U ⊔ K) + finrank Bool ↥(U ⊓ K) =
      finrank Bool U + finrank Bool K := by
  have : Finite (ι → ZMod 2) := Finite.of_equiv (ι → Bool) (toZModBits ι).toEquiv
  rw [finrank_bool_eq_finrank_toZMod (U ⊔ K), finrank_bool_eq_finrank_toZMod (U ⊓ K),
    finrank_bool_eq_finrank_toZMod U, finrank_bool_eq_finrank_toZMod K,
    toZModSub_sup, toZModSub_inf]
  exact Submodule.finrank_sup_add_finrank_inf_eq (toZModSub U) (toZModSub K)

/-- Rank-nullity for linear maps between `Bool`-vector spaces `ι₁ → Bool` and `ι₂ → Bool`. -/
theorem finrank_range_add_finrank_ker_bitString {ι₁ ι₂ : Type*} [Finite ι₁]
    (f : (ι₁ → Bool) →ₗ[Bool] (ι₂ → Bool)) (V : Submodule Bool (ι₁ → Bool)) :
    finrank Bool ↥(V.map f) + finrank Bool ↥(V ⊓ LinearMap.ker f) = finrank Bool V := by
  let fZ : (ι₁ → ZMod 2) →ₗ[ZMod 2] (ι₂ → ZMod 2) :=
    { toFun := fun z => toZModBits ι₂ (f ((toZModBits ι₁).symm z))
      map_add' := fun a b => by simp only [map_add]
      map_smul' := fun c a => by
        rw [symm_toZModBits_smul, map_smul, toZModBits_smul, bitEquiv.symm_apply_apply]
        rfl }
  have hmap : toZModSub (V.map f) = (toZModSub V).map fZ := by
    ext y
    obtain ⟨w, rfl⟩ := (toZModBits ι₂).surjective y
    simp only [mem_toZModSub, Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨toZModBits ι₁ x, mem_toZModSub.mpr hx, by
        simp only [fZ, LinearMap.coe_mk, AddHom.coe_mk, (toZModBits ι₁).symm_apply_apply]⟩
    · rintro ⟨z, hz, hz_eq⟩
      obtain ⟨x, hx, rfl⟩ := hz
      refine ⟨x, hx, (toZModBits ι₂).injective ?_⟩
      simpa only [fZ, LinearMap.coe_mk, AddHom.coe_mk, (toZModBits ι₁).symm_apply_apply] using hz_eq
  have hker : toZModSub (V ⊓ LinearMap.ker f) = toZModSub V ⊓ LinearMap.ker fZ := by
    ext z
    obtain ⟨x, rfl⟩ := (toZModBits ι₁).surjective z
    rw [mem_toZModSub, Submodule.mem_inf, Submodule.mem_inf, mem_toZModSub,
      LinearMap.mem_ker, LinearMap.mem_ker]
    simp only [fZ, LinearMap.coe_mk, AddHom.coe_mk, (toZModBits ι₁).symm_apply_apply,
      (toZModBits ι₂).map_eq_zero_iff]
  have : Finite (ι₁ → ZMod 2) := Finite.of_equiv (ι₁ → Bool) (toZModBits ι₁).toEquiv
  have hres := LinearMap.finrank_range_add_finrank_ker (fZ.domRestrict (toZModSub V))
  have hrange : LinearMap.range (fZ.domRestrict (toZModSub V)) = (toZModSub V).map fZ := by
    ext y
    simp only [LinearMap.mem_range, LinearMap.domRestrict_apply, Submodule.mem_map, Subtype.exists]
    exact ⟨fun ⟨a, ha, hfa⟩ => ⟨a, ha, hfa⟩, fun ⟨a, ha, hfa⟩ => ⟨a, ha, hfa⟩⟩
  have hker_res : finrank (ZMod 2) (LinearMap.ker (fZ.domRestrict (toZModSub V))) =
      finrank (ZMod 2) ↥(toZModSub V ⊓ LinearMap.ker fZ) := by
    let eK : LinearMap.ker (fZ.domRestrict (toZModSub V)) ≃ₗ[ZMod 2]
        ↥(toZModSub V ⊓ LinearMap.ker fZ) :=
      { toFun := fun v => ⟨v.1.1, v.1.2, LinearMap.mem_ker.mpr v.2⟩
        invFun := fun w => ⟨⟨w.1, w.2.1⟩, LinearMap.mem_ker.mpr w.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact eK.finrank_eq
  rw [hrange, hker_res] at hres
  rw [finrank_bool_eq_finrank_toZMod (V.map f),
    finrank_bool_eq_finrank_toZMod (V ⊓ LinearMap.ker f),
    finrank_bool_eq_finrank_toZMod V, hmap, hker]
  exact hres

/-- Existence of a `k₁`-dimensional `Bool`-submodule inside any `Bool`-submodule of `ι → Bool`
of dimension at least `k₁`. -/
theorem exists_submodule_finrank_eq_bitString {ι : Type*} [Finite ι]
    (V : Submodule Bool (ι → Bool)) (k₁ : ℕ) (hk₁ : k₁ ≤ finrank Bool V) :
    ∃ U : Submodule Bool (ι → Bool), U ≤ V ∧ finrank Bool U = k₁ := by
  have : Finite (ι → ZMod 2) := Finite.of_equiv (ι → Bool) (toZModBits ι).toEquiv
  rw [finrank_bool_eq_finrank_toZMod] at hk₁
  let B0 := Module.finBasis (ZMod 2) (toZModSub V)
  let idx : Fin k₁ → Fin (finrank (ZMod 2) (toZModSub V)) := Fin.castLE hk₁
  let UZ : Submodule (ZMod 2) (ι → ZMod 2) :=
    Submodule.span (ZMod 2) (Set.range fun i : Fin k₁ => (B0 (idx i) : ι → ZMod 2))
  have hli : LinearIndependent (ZMod 2) (fun i : Fin k₁ => (B0 (idx i) : ι → ZMod 2)) :=
    (B0.linearIndependent.comp idx (Fin.castLE_injective hk₁)).map'
      (toZModSub V).subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hUZ_dim : finrank (ZMod 2) UZ = k₁ := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hUZ_le : UZ ≤ toZModSub V := Submodule.span_le.mpr (by
    rintro _ ⟨i, rfl⟩; exact (B0 (idx i)).2)
  have hto : toZModSub (ofZModSub UZ) = UZ := by
    ext y
    obtain ⟨x, rfl⟩ := (toZModBits ι).surjective y
    rw [mem_toZModSub, mem_ofZModSub]
  refine ⟨ofZModSub UZ, ?_, ?_⟩
  · rw [← toZModSub_le_iff, hto]; exact hUZ_le
  · rw [finrank_bool_eq_finrank_toZMod, hto, hUZ_dim]

end BoolVectorSpace

/-! ### Uniform distributions on affine subspaces -/

section AffineSource

/-- The uniform distribution on a nonempty affine subspace of `BitString n`. -/
@[expose] noncomputable def uniformAffine {n : ℕ} (A : AffineSubspace Bool (BitString n))
    (hA : (A : Set (BitString n)).Nonempty) : PMF (BitString n) :=
  PMF.uniformOfFinset (Set.toFinite (A : Set (BitString n))).toFinset
    (by
      obtain ⟨x, hx⟩ := hA
      exact ⟨x, (Set.Finite.mem_toFinset _).mpr hx⟩)

/-- An **`(n, k)` affine source** over `𝔽₂`: the uniform distribution on an affine subspace of
`BitString n` of dimension `k` ([Li2023, Def. 3.1], [LiZhong2024, Def. 15]). -/
@[expose] def IsAffineSource {n : ℕ} (X : PMF (BitString n)) (k : ℕ) : Prop :=
  ∃ (A : AffineSubspace Bool (BitString n)) (hA : (A : Set (BitString n)).Nonempty),
    finrank Bool A.direction = k ∧ X = uniformAffine A hA

private theorem natCard_affineSubspace_eq_direction {ι : Type*}
    (A : AffineSubspace Bool (ι → Bool)) {x₀ : ι → Bool} (hx₀ : x₀ ∈ A) :
    Nat.card (A : Set (ι → Bool)) = Nat.card A.direction := by
  let e : A.direction ≃ (A : Set (ι → Bool)) :=
    { toFun := fun v => ⟨v.1 +ᵥ x₀, AffineSubspace.vadd_mem_of_mem_direction v.2 hx₀⟩
      invFun := fun y => ⟨y.1 -ᵥ x₀, AffineSubspace.vsub_mem_direction y.2 hx₀⟩
      left_inv := fun v => Subtype.ext (vadd_vsub v.1 x₀)
      right_inv := fun y => Subtype.ext (vsub_vadd y.1 x₀) }
  exact (Nat.card_congr e).symm

/-- The cardinality of the `Finset` of points of a nonempty affine subspace of `BitString n` equals
`2 ^ finrank Bool A.direction`. -/
theorem card_affineSubspace_toFinset {n : ℕ}
    (A : AffineSubspace Bool (BitString n)) (hA : (A : Set (BitString n)).Nonempty) :
    (Set.toFinite (A : Set (BitString n))).toFinset.card = 2 ^ finrank Bool A.direction := by
  obtain ⟨x₀, hx₀⟩ := hA
  let S := (Set.toFinite (A : Set (BitString n))).toFinset
  let eS : S ≃ (A : Set (BitString n)) :=
    Equiv.subtypeEquivRight (fun x => Set.Finite.mem_toFinset _)
  rw [← Fintype.card_coe S, ← Nat.card_eq_fintype_card, Nat.card_congr eS,
    natCard_affineSubspace_eq_direction A hx₀, natCard_submodule_bool]

/-- Pointwise mass of `uniformAffine A hA`. -/
@[simp]
theorem uniformAffine_apply {n : ℕ} (A : AffineSubspace Bool (BitString n))
    (hA : (A : Set (BitString n)).Nonempty) (x : BitString n) :
    uniformAffine A hA x =
      @ite ENNReal (x ∈ A) (Classical.propDecidable (x ∈ A))
        ((2 ^ finrank Bool A.direction : ℕ) : ENNReal)⁻¹ 0 := by
  classical
  rw [uniformAffine, PMF.uniformOfFinset_apply, card_affineSubspace_toFinset A hA]
  simp only [Set.Finite.mem_toFinset]
  convert rfl

/-- The uniform distribution on a nonempty affine subspace `A` has min-entropy `dim(A)`. -/
theorem minEntropy_uniformAffine {n : ℕ} (A : AffineSubspace Bool (BitString n))
    (hA : (A : Set (BitString n)).Nonempty) :
    minEntropy (uniformAffine A hA) = (finrank Bool A.direction : ℝ) := by
  rw [uniformAffine, minEntropy_uniformOfFinset, card_affineSubspace_toFinset A hA]
  push_cast
  rw [Real.logb_two_pow]

/-- Every `(n, k)` affine source has min-entropy `k`. -/
theorem minEntropy_of_isAffineSource {n k : ℕ} {X : PMF (BitString n)}
    (hX : IsAffineSource X k) : minEntropy X = (k : ℝ) := by
  rcases hX with ⟨A, hA, hdim, rfl⟩
  rw [minEntropy_uniformAffine, hdim]

/-- Support of `uniformAffine A hA` is `A`. -/
theorem mem_support_uniformAffine_iff {n : ℕ} (A : AffineSubspace Bool (BitString n))
    (hA : (A : Set (BitString n)).Nonempty) (x : BitString n) :
    x ∈ (uniformAffine A hA).support ↔ x ∈ A := by
  rw [uniformAffine, mem_support_uniformOfFinset_iff, Set.Finite.mem_toFinset]
  rfl

/-- An affine map pushes `uniformAffine A hA` forward to `uniformAffine (A.map L.toAffineMap)`. -/
theorem uniformAffine_map_of_isAffine {n m : ℕ} (A : AffineSubspace Bool (BitString n))
    (hA : (A : Set (BitString n)).Nonempty) {L : BitString n → BitString m} (hL : IsAffine L) :
    (uniformAffine A hA).map L =
      uniformAffine (A.map hL.toAffineMap) (by
        obtain ⟨x₀, hx₀⟩ := hA
        exact ⟨L x₀, AffineSubspace.mem_map.mpr ⟨x₀, hx₀, rfl⟩⟩) := by
  classical
  set A' := A.map hL.toAffineMap
  have hA' : (A' : Set (BitString m)).Nonempty := by
    obtain ⟨x₀, hx₀⟩ := hA
    exact ⟨L x₀, AffineSubspace.mem_map.mpr ⟨x₀, hx₀, rfl⟩⟩
  let K : Submodule Bool (BitString n) := A.direction ⊓ LinearMap.ker hL.linearMap
  have hrank : finrank Bool A.direction = finrank Bool K + finrank Bool A'.direction := by
    have hdir : A'.direction = A.direction.map hL.linearMap := AffineSubspace.map_direction _ _
    rw [hdir, add_comm]
    exact (finrank_range_add_finrank_ker_bitString hL.linearMap A.direction).symm
  ext y
  rw [PMF.map_apply]
  trans (∑ x ∈ Finset.univ.filter (fun x => x ∈ A ∧ L x = y),
      ((2 ^ finrank Bool A.direction : ℕ) : ENNReal)⁻¹)
  · rw [tsum_eq_sum (s := Finset.univ.filter (fun x => x ∈ A ∧ L x = y))]
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.mem_filter] at hx
      rw [uniformAffine_apply]
      split_ifs with h1 h2
      · rfl
      · exact False.elim (h2 hx.2.1)
      · exact False.elim (h1 hx.2.2.symm)
    · intro x hx
      rw [Finset.mem_filter] at hx
      by_cases hyx : y = L x
      · rw [ite_eq_left hyx, uniformAffine_apply, ite_eq_right]
        intro hxA
        exact hx ⟨Finset.mem_univ _, hxA, hyx.symm⟩
      · rw [ite_eq_right hyx]
  · rw [Finset.sum_const, nsmul_eq_mul, uniformAffine_apply]
    by_cases hyA : y ∈ A'
    · rw [ite_eq_left hyA]
      obtain ⟨x₀, hx₀, hx₀y⟩ := AffineSubspace.mem_map.mp hyA
      rw [IsAffine.coe_toAffineMap] at hx₀y
      subst hx₀y
      have hfiber : (Finset.univ.filter (fun x => x ∈ A ∧ L x = L x₀)).card = Nat.card K := by
        let e : K ≃ (Finset.univ.filter (fun x => x ∈ A ∧ L x = L x₀)) :=
          { toFun := fun v => ⟨v.1 +ᵥ x₀, Finset.mem_filter.mpr
              ⟨Finset.mem_univ _,
                AffineSubspace.vadd_mem_of_mem_direction v.2.1 hx₀, by
                have hL0 : hL.linearMap v.1 = 0 := v.2.2
                have hv := hL.toAffineMap.map_vadd x₀ v.1
                rw [IsAffine.coe_toAffineMap] at hv
                change L (v.1 +ᵥ x₀) = hL.linearMap v.1 +ᵥ L x₀ at hv
                rw [hv, hL0, zero_vadd]⟩⟩
            invFun := fun z => ⟨z.1 -ᵥ x₀,
              AffineSubspace.vsub_mem_direction (Finset.mem_filter.mp z.2).2.1 hx₀, by
                have hzL : L z.1 = L x₀ := (Finset.mem_filter.mp z.2).2.2
                have hv := hL.toAffineMap.linear_apply_vsub z.1 x₀
                rw [IsAffine.coe_toAffineMap] at hv
                rw [SetLike.mem_coe, LinearMap.mem_ker]
                change hL.linearMap (z.1 -ᵥ x₀) = L z.1 -ᵥ L x₀ at hv
                rw [hv, hzL, vsub_self]⟩
            left_inv := fun v => Subtype.ext (vadd_vsub v.1 x₀)
            right_inv := fun z => Subtype.ext (vsub_vadd z.1 x₀) }
        rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card, ← Nat.card_congr e]
      have hcardK : Nat.card K = 2 ^ finrank Bool K := natCard_submodule_bool K
      rw [hfiber, hcardK, hrank, pow_add, Nat.cast_mul]
      have h1 : ((2 ^ finrank Bool K : ℕ) : ENNReal) ≠ 0 := by positivity
      have h2 : ((2 ^ finrank Bool K : ℕ) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
      rw [ENNReal.mul_inv (Or.inl h1) (Or.inl h2), ← mul_assoc,
        ENNReal.mul_inv_cancel h1 h2, one_mul]
    · rw [ite_eq_right hyA]
      have hempty : Finset.univ.filter (fun x => x ∈ A ∧ L x = y) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        rintro x _ ⟨hxA, hLx⟩
        exact hyA (AffineSubspace.mem_map.mpr ⟨x, hxA, hLx⟩)
      simp [hempty]

/-- An affine image of an affine source is an affine source whose dimension is the dimension of the
pushed-forward subspace. -/
theorem isAffineSource_map_of_isAffine {n m k : ℕ} {X : PMF (BitString n)}
    (hX : IsAffineSource X k) {L : BitString n → BitString m} (hL : IsAffine L) :
    ∃ k', k' ≤ k ∧ k' ≤ m ∧ IsAffineSource (X.map L) k' := by
  rcases hX with ⟨A, hA, hdim, rfl⟩
  have hle_k : finrank Bool (A.direction.map hL.linearMap) ≤ k := by
    rw [← hdim]
    calc finrank Bool (A.direction.map hL.linearMap)
        ≤ finrank Bool (A.direction.map hL.linearMap) +
            finrank Bool ↥(A.direction ⊓ LinearMap.ker hL.linearMap) := Nat.le_add_right _ _
      _ = finrank Bool A.direction :=
            finrank_range_add_finrank_ker_bitString hL.linearMap A.direction
  have hle_m : finrank Bool (A.direction.map hL.linearMap) ≤ m := by
    rw [finrank_bool_eq_finrank_toZMod]
    calc finrank (ZMod 2) (toZModSub (A.direction.map hL.linearMap))
        ≤ finrank (ZMod 2) (Fin m → ZMod 2) := Submodule.finrank_le _
      _ = m := by simp
  have hA' :
      ((A.map hL.toAffineMap : AffineSubspace Bool (BitString m)) :
        Set (BitString m)).Nonempty := by
    obtain ⟨x₀, hx₀⟩ := hA
    exact ⟨L x₀, AffineSubspace.mem_map.mpr ⟨x₀, hx₀, rfl⟩⟩
  refine ⟨finrank Bool (A.direction.map hL.linearMap), hle_k, hle_m,
    A.map hL.toAffineMap, hA', ?_, ?_⟩
  · rw [AffineSubspace.map_direction]
    rfl
  · exact uniformAffine_map_of_isAffine A hA hL

/-! ### Affine Conditioning Lemma ([Li2023, Lemma 3.9], [LiZhong2024, Lemma 8]) -/

/-- Helper: decomposing an affine subspace `A = x₀ + (U ⊕ K)` expresses `uniformAffine A` as the
independent sum `uniformAffine (x₀ + U) + uniformAffine (0 + K)`. -/
private theorem uniformAffine_eq_bind_add_of_isCompl {n : ℕ}
    (A : AffineSubspace Bool (BitString n)) {x₀ : BitString n} (hx₀ : x₀ ∈ A)
    {U K : Submodule Bool (BitString n)} (hU : U ≤ A.direction) (hK : K ≤ A.direction)
    (hcompl : U ⊓ K = ⊥ ∧ U ⊔ K = A.direction) :
    uniformAffine A ⟨x₀, hx₀⟩ =
      (uniformAffine (AffineSubspace.mk' x₀ U) ⟨x₀, AffineSubspace.self_mem_mk' x₀ U⟩).bind
        fun a => (uniformAffine (AffineSubspace.mk' 0 K) ⟨0, AffineSubspace.self_mem_mk' 0 K⟩).map
          fun b => a + b := by
  classical
  let Au := AffineSubspace.mk' x₀ U
  let Bk := AffineSubspace.mk' (0 : BitString n) K
  have hAu : (Au : Set (BitString n)).Nonempty := ⟨x₀, AffineSubspace.self_mem_mk' x₀ U⟩
  have hBk : (Bk : Set (BitString n)).Nonempty := ⟨0, AffineSubspace.self_mem_mk' 0 K⟩
  have hrank : finrank Bool A.direction = finrank Bool U + finrank Bool K := by
    have hsum := finrank_sup_add_finrank_inf_bitString U K
    rw [hcompl.1, hcompl.2, finrank_bot, add_zero] at hsum
    exact hsum
  ext z
  rw [PMF.bind_apply, uniformAffine_apply A ⟨x₀, hx₀⟩ z]
  have hinner : ∀ a : BitString n,
      (uniformAffine (AffineSubspace.mk' 0 K) ⟨0, AffineSubspace.self_mem_mk' 0 K⟩).map
        (fun b => a + b) z = uniformAffine Bk hBk (z + a) := by
    intro a
    rw [PMF.map_apply]
    have huniq : ∀ b : BitString n, z = a + b ↔ b = z + a := fun b => by
      constructor
      · rintro rfl
        rw [add_comm a b, add_assoc, BitString.add_self, add_zero]
      · rintro rfl
        rw [add_comm z a, ← add_assoc, BitString.add_self, zero_add]
    rw [tsum_eq_single (z + a)]
    · rw [ite_eq_left ((huniq _).mpr rfl)]
    · intro b hb
      rw [ite_eq_right (fun h => hb ((huniq b).mp h))]
  have hsum_inner :
      (∑' a, uniformAffine Au hAu a *
        (uniformAffine (AffineSubspace.mk' 0 K) ⟨0, AffineSubspace.self_mem_mk' 0 K⟩).map
          (fun b => a + b) z) =
      ∑' a, uniformAffine Au hAu a * uniformAffine Bk hBk (z + a) :=
    tsum_congr fun a => congrArg (uniformAffine Au hAu a * ·) (hinner a)
  rw [hsum_inner]
  by_cases hz : z ∈ A
  · rw [ite_eq_left hz]
    have hzV : z -ᵥ x₀ ∈ U ⊔ K := by
      rw [hcompl.2]
      exact AffineSubspace.vsub_mem_direction hz hx₀
    obtain ⟨u₀, hu₀, k₀, hk₀, huk₀⟩ := Submodule.mem_sup.mp hzV
    let a₀ := x₀ + u₀
    have ha₀_U : a₀ ∈ Au := by simpa [Au, a₀, AffineSubspace.mem_mk', vsub_eq_sub] using hu₀
    have hza₀_K : z + a₀ ∈ Bk := by
      have hz_eq : z = a₀ + k₀ := by
        simp only [vsub_eq_sub] at huk₀
        rw [← add_sub_cancel x₀ z, add_comm x₀ (z - x₀)]
        calc z - x₀ + x₀ = (u₀ + k₀) + x₀ := by rw [huk₀]
          _ = a₀ + k₀ := by dsimp only [a₀]; abel
      rw [hz_eq, add_assoc, add_comm k₀ a₀, ← add_assoc, BitString.add_self, zero_add]
      simpa [Bk, AffineSubspace.mem_mk', vsub_eq_sub] using hk₀
    have huniq_a : ∀ a : BitString n, a ∈ Au ∧ z + a ∈ Bk → a = a₀ := by
      rintro a ⟨haA, hzaB⟩
      have haU : a - x₀ ∈ U := by simpa [Au, AffineSubspace.mem_mk', vsub_eq_sub] using haA
      have hkK : z + a ∈ K := by simpa [Bk, AffineSubspace.mem_mk'] using hzaB
      have hzkK : z + a₀ ∈ K := by simpa [Bk, AffineSubspace.mem_mk'] using hza₀_K
      have ha₀U : a₀ - x₀ ∈ U := by simpa [Au, AffineSubspace.mem_mk', vsub_eq_sub] using ha₀_U
      have hdiffU : a - a₀ ∈ U := by
        have h := U.sub_mem haU ha₀U
        rwa [show (a - x₀) - (a₀ - x₀) = a - a₀ by abel] at h
      have hdiffK : a - a₀ ∈ K := by
        have h := K.sub_mem hkK hzkK
        rwa [show (z + a) - (z + a₀) = a - a₀ by abel] at h
      have hbot : a - a₀ ∈ U ⊓ K := ⟨hdiffU, hdiffK⟩
      rw [hcompl.1, Submodule.mem_bot] at hbot
      exact sub_eq_zero.mp hbot
    rw [tsum_eq_single a₀]
    · rw [uniformAffine_apply Au hAu a₀, uniformAffine_apply Bk hBk (z + a₀),
        ite_eq_left ha₀_U, ite_eq_left hza₀_K,
        AffineSubspace.direction_mk', AffineSubspace.direction_mk', hrank, pow_add, Nat.cast_mul,
        ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (ENNReal.natCast_ne_top _))]
    · intro a ha
      rw [uniformAffine_apply Au hAu a, uniformAffine_apply Bk hBk (z + a)]
      by_cases ha1 : a ∈ Au
      · by_cases ha2 : z + a ∈ Bk
        · exact absurd (huniq_a a ⟨ha1, ha2⟩) ha
        · rw [ite_eq_right ha2, mul_zero]
      · rw [ite_eq_right ha1, zero_mul]
  · rw [ite_eq_right hz]
    symm
    have hzero : ∀ a : BitString n, uniformAffine Au hAu a * uniformAffine Bk hBk (z + a) = 0 := by
      intro a
      rw [uniformAffine_apply Au hAu a, uniformAffine_apply Bk hBk (z + a)]
      by_cases ha1 : a ∈ Au
      · by_cases ha2 : z + a ∈ Bk
        · exfalso
          apply hz
          have haU : a -ᵥ x₀ ∈ U := by simpa [Au, AffineSubspace.mem_mk'] using ha1
          have hkK : z + a ∈ K := by simpa [Bk, AffineSubspace.mem_mk', vsub_eq_sub] using ha2
          have hsum : (a -ᵥ x₀) + (z + a) ∈ A.direction := A.direction.add_mem (hU haU) (hK hkK)
          have hmem := AffineSubspace.vadd_mem_of_mem_direction hsum hx₀
          have hz_eq : ((a -ᵥ x₀) + (z + a)) +ᵥ x₀ = z := by
            simp only [vadd_eq_add, vsub_eq_sub]
            calc a - x₀ + (z + a) + x₀ = z + (a + a) := by abel
              _ = z := by rw [BitString.add_self, add_zero]
          rwa [hz_eq] at hmem
        · rw [ite_eq_right ha2, mul_zero]
      · rw [ite_eq_right ha1, zero_mul]
    simp_rw [hzero]
    exact tsum_zero

/-- **Affine Conditioning Lemma** ([Li2023, Lemma 3.9], [LiZhong2024, Lemma 8]):
for any `(n, k)` affine source `X` on `BitString n` and affine map `L : BitString n → BitString m`,
there exist independent affine sources `A` and `B` of dimensions `kA` and `kB` with `k = kA + kB`,
`k ≤ kB + m`, a constant `c`, and an affine map `L_inv` such that `X = A + B`, `L b = c` for all
`b ∈ B.support`, `L_inv (L a) = a` for all `a ∈ A.support`, and every fiber
`{x ∈ X.support | L x = ℓ}` is an affine subspace of dimension `kB`. -/
theorem affineConditioning {n m k : ℕ} {X : PMF (BitString n)} (hX : IsAffineSource X k)
    {L : BitString n → BitString m} (hL : IsAffine L) :
    ∃ (kA kB : ℕ) (A B : PMF (BitString n)) (c : BitString m)
      (L_inv : BitString m → BitString n),
      IsAffineSource A kA ∧ IsAffineSource B kB ∧
      k = kA + kB ∧ k ≤ kB + m ∧
      X = (A.bind fun a => B.map fun b => a + b) ∧
      (∀ b ∈ B.support, L b = c) ∧
      IsAffine L_inv ∧ (∀ a ∈ A.support, L_inv (L a) = a) ∧
      (∀ ℓ ∈ (X.map L).support, ∃ Aℓ : AffineSubspace Bool (BitString n),
        (Aℓ : Set (BitString n)).Nonempty ∧
        finrank Bool Aℓ.direction = kB ∧
        (Aℓ : Set (BitString n)) = {x ∈ X.support | L x = ℓ}) := by
  classical
  rcases hX with ⟨Asub, hAsub, hdim, rfl⟩
  obtain ⟨x₀, hx₀⟩ := hAsub
  let K : Submodule Bool (BitString n) := Asub.direction ⊓ LinearMap.ker hL.linearMap
  obtain ⟨U, hU_le, hcompl_inf, hcompl_sup⟩ :=
    exists_isCompl_submodule K Asub.direction inf_le_left
  let AsrcSub := AffineSubspace.mk' x₀ U
  let BsrcSub := AffineSubspace.mk' (0 : BitString n) K
  have hAsrcSub : (AsrcSub : Set (BitString n)).Nonempty := ⟨x₀, AffineSubspace.self_mem_mk' x₀ U⟩
  have hBsrcSub : (BsrcSub : Set (BitString n)).Nonempty := ⟨0, AffineSubspace.self_mem_mk' 0 K⟩
  let A := uniformAffine AsrcSub hAsrcSub
  let B := uniformAffine BsrcSub hBsrcSub
  let LZ : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) :=
    { toFun := fun z => toZModBits (Fin m) (hL.linearMap ((toZModBits (Fin n)).symm z))
      map_add' := fun a b => by simp only [map_add]
      map_smul' := fun c a => by
        rw [symm_toZModBits_smul, map_smul, toZModBits_smul, bitEquiv.symm_apply_apply]
        rfl }
  let fU : toZModSub U →ₗ[ZMod 2] (Fin m → ZMod 2) := LZ.domRestrict (toZModSub U)
  have hfU_inj : Function.Injective fU := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro ⟨z, hz⟩ hfz
    obtain ⟨u, hu, rfl⟩ := hz
    have hLu : hL.linearMap u = 0 := (toZModBits (Fin m)).injective (by
      have hfz' : fU ⟨toZModBits (Fin n) u, mem_toZModSub.mpr hu⟩ = 0 := hfz
      simpa only [fU, LZ, LinearMap.domRestrict_apply, LinearMap.coe_mk, AddHom.coe_mk,
        (toZModBits (Fin n)).symm_apply_apply, map_zero] using hfz')
    have huK : u ∈ U ⊓ K := ⟨hu, hU_le hu, LinearMap.mem_ker.mpr hLu⟩
    rw [hcompl_inf, Submodule.mem_bot] at huK
    exact Subtype.ext (by simp [huK])
  let eU : toZModSub U ≃ₗ[ZMod 2] LinearMap.range fU := LinearEquiv.ofInjective fU hfU_inj
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.range fU)
  let proj : (Fin m → ZMod 2) →ₗ[ZMod 2] LinearMap.range fU :=
    Submodule.projectionOnto _ _ hW
  let TZ : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
    ((toZModSub U).subtype.comp eU.symm.toLinearMap).comp proj
  let T : BitString m → BitString n :=
    fun y => (toZModBits (Fin n)).symm (TZ (toZModBits (Fin m) y))
  let L_inv : BitString m → BitString n := fun y => x₀ + T (y + L x₀)
  have hL_inv : IsAffine L_inv := by
    intro y₁ y₂ y₃
    have hadd_self_m (z : BitString m) : z + z = 0 := BitString.add_self z
    simp only [L_inv]
    have T_add (a b : BitString m) : T (a + b) = T a + T b := by
      simp only [T, map_add]
    have hTsum : T (y₁ + L x₀) + T (y₂ + L x₀) + T (y₃ + L x₀) =
        T ((y₁ + y₂ + y₃) + L x₀) := by
      rw [← T_add, ← T_add]
      congr 1
      calc (y₁ + L x₀) + (y₂ + L x₀) + (y₃ + L x₀)
          = (y₁ + y₂ + y₃) + (L x₀ + L x₀) + L x₀ := by abel
        _ = (y₁ + y₂ + y₃) + L x₀ := by rw [hadd_self_m, add_zero]
    rw [← hTsum]
    calc x₀ + (T (y₁ + L x₀) + T (y₂ + L x₀) + T (y₃ + L x₀))
        = x₀ + (x₀ + x₀) + (T (y₁ + L x₀) + T (y₂ + L x₀) + T (y₃ + L x₀)) := by
          rw [BitString.add_self x₀, add_zero]
      _ = (x₀ + T (y₁ + L x₀)) + (x₀ + T (y₂ + L x₀)) + (x₀ + T (y₃ + L x₀)) := by abel
  have hkdim : finrank Bool Asub.direction = finrank Bool U + finrank Bool K := by
    have hsum := finrank_sup_add_finrank_inf_bitString U K
    rw [hcompl_inf, hcompl_sup, finrank_bot, add_zero] at hsum
    exact hsum
  have hU_le_m : finrank Bool U ≤ m := by
    rw [finrank_bool_eq_finrank_toZMod]
    calc finrank (ZMod 2) (toZModSub U)
        = finrank (ZMod 2) (LinearMap.range fU) := eU.finrank_eq
      _ ≤ finrank (ZMod 2) (Fin m → ZMod 2) := Submodule.finrank_le _
      _ = m := by simp
  refine ⟨finrank Bool U, finrank Bool K, A, B, L 0, L_inv,
    ⟨AsrcSub, hAsrcSub, by rw [AffineSubspace.direction_mk'], rfl⟩,
    ⟨BsrcSub, hBsrcSub, by rw [AffineSubspace.direction_mk'], rfl⟩,
    by rw [← hdim, hkdim], by omega,
    uniformAffine_eq_bind_add_of_isCompl Asub hx₀ hU_le inf_le_left ⟨hcompl_inf, hcompl_sup⟩,
    ?_, hL_inv, ?_, ?_⟩
  · intro b hb
    rw [mem_support_uniformAffine_iff] at hb
    have hbK : b ∈ K := by simpa [BsrcSub, vsub_eq_sub] using hb
    have hLb := hL.toAffineMap.map_vadd (0 : BitString n) b
    rw [vadd_eq_add, add_zero, vadd_eq_add, IsAffine.coe_toAffineMap] at hLb
    have hbker : hL.toAffineMap.linear b = 0 := hbK.2
    rw [hbker, zero_add] at hLb
    exact hLb
  · intro a ha
    rw [mem_support_uniformAffine_iff] at ha
    have haU : a -ᵥ x₀ ∈ U := by simpa [AsrcSub] using ha
    have hLa : L a = hL.linearMap (a -ᵥ x₀) +ᵥ L x₀ := by
      have := hL.toAffineMap.map_vadd x₀ (a -ᵥ x₀)
      rw [vsub_vadd, IsAffine.coe_toAffineMap] at this
      exact this
    have hy : L a + L x₀ = hL.linearMap (a -ᵥ x₀) := by
      rw [hLa, vadd_eq_add, add_assoc, BitString.add_self, add_zero]
    dsimp only [L_inv, T]
    rw [hy]
    have hyZ : toZModBits (Fin m) (hL.linearMap (a -ᵥ x₀)) =
        fU ⟨toZModBits (Fin n) (a -ᵥ x₀), mem_toZModSub.mpr haU⟩ := by
      simp only [fU, LZ, LinearMap.domRestrict_apply, LinearMap.coe_mk, AddHom.coe_mk,
        (toZModBits (Fin n)).symm_apply_apply]
    rw [hyZ]
    have hproj : proj (fU ⟨toZModBits (Fin n) (a -ᵥ x₀), mem_toZModSub.mpr haU⟩) =
        ⟨fU ⟨toZModBits (Fin n) (a -ᵥ x₀), mem_toZModSub.mpr haU⟩, LinearMap.mem_range_self fU _⟩ :=
      Submodule.projectionOnto_apply_left hW
        ⟨fU ⟨toZModBits (Fin n) (a -ᵥ x₀), mem_toZModSub.mpr haU⟩, LinearMap.mem_range_self fU _⟩
    have heU : eU ⟨toZModBits (Fin n) (a -ᵥ x₀), mem_toZModSub.mpr haU⟩ =
        ⟨fU ⟨toZModBits (Fin n) (a -ᵥ x₀), mem_toZModSub.mpr haU⟩,
          LinearMap.mem_range_self fU _⟩ := rfl
    have hTZ : TZ (fU ⟨toZModBits (Fin n) (a -ᵥ x₀), mem_toZModSub.mpr haU⟩) =
        toZModBits (Fin n) (a -ᵥ x₀) := by
      simp only [TZ, LinearMap.comp_apply, LinearEquiv.coe_coe, hproj, ← heU,
        LinearEquiv.symm_apply_apply, Submodule.coe_subtype]
    rw [hTZ, (toZModBits (Fin n)).symm_apply_apply, vsub_eq_sub]
    abel
  · intro ℓ hℓ
    rw [PMF.mem_support_iff, PMF.map_apply] at hℓ
    have hex : ∃ x ∈ Asub, L x = ℓ := by
      by_contra hno
      push Not at hno
      apply hℓ
      refine (tsum_congr fun x => ?_).trans tsum_zero
      by_cases hx : x ∈ Asub
      · split_ifs with hEq
        · exact False.elim (hno x hx hEq.symm)
        · rfl
      · split_ifs
        · exact (PMF.apply_eq_zero_iff _ _).mpr
            ((mem_support_uniformAffine_iff Asub ⟨x₀, hx₀⟩ x).not.mpr hx)
        · rfl
    obtain ⟨xℓ, hxℓ, rfl⟩ := hex
    refine ⟨AffineSubspace.mk' xℓ K, ⟨xℓ, AffineSubspace.self_mem_mk' xℓ K⟩,
      by rw [AffineSubspace.direction_mk'], ?_⟩
    ext x
    simp only [SetLike.mem_coe, AffineSubspace.mem_mk', Set.mem_ofPred_eq]
    rw [mem_support_uniformAffine_iff Asub ⟨x₀, hx₀⟩ x]
    constructor
    · intro hxK
      refine ⟨?_, ?_⟩
      · have := AffineSubspace.vadd_mem_of_mem_direction
          (inf_le_left (b := LinearMap.ker hL.linearMap) hxK) hxℓ
        rwa [vsub_vadd] at this
      · have := hL.toAffineMap.map_vadd xℓ (x -ᵥ xℓ)
        rw [vsub_vadd, IsAffine.coe_toAffineMap] at this
        have hker : hL.toAffineMap.linear (x -ᵥ xℓ) = 0 := hxK.2
        rw [this, hker, zero_vadd]
    · rintro ⟨hxA, hLx⟩
      refine ⟨AffineSubspace.vsub_mem_direction hxA hxℓ, ?_⟩
      have hlin := hL.toAffineMap.linear_apply_vsub x xℓ
      rw [IsAffine.coe_toAffineMap] at hlin
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      change hL.linearMap (x -ᵥ xℓ) = L x -ᵥ L xℓ at hlin
      rw [hlin, hLx, vsub_self]

/-! ### Affine Block Decomposition ([Li2023, Lemma 3.10]) -/

/-- Canonical additive equivalence between flat bit strings `BitString (∑ i, b i)` and
partitioned bit-blocks `∀ i : Fin t, BitString (b i)`. -/
@[expose] def blockEquiv {t : ℕ} (b : Fin t → ℕ) :
    BitString (∑ i, b i) ≃+ (∀ i : Fin t, BitString (b i)) where
  toFun x i j := x (finSigmaFinEquiv ⟨i, j⟩)
  invFun g k := g (finSigmaFinEquiv.symm k).1 (finSigmaFinEquiv.symm k).2
  left_inv x := funext fun k => by simp
  right_inv g := funext fun i => funext fun j => by
    change g (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨i, j⟩)).1
      (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨i, j⟩)).2 = g i j
    rw [finSigmaFinEquiv.symm_apply_apply]
  map_add' _ _ := rfl

private theorem blockEquiv_symm_smul {t : ℕ} {b : Fin t → ℕ} (c : Bool)
    (g : ∀ i : Fin t, BitString (b i)) :
    (blockEquiv b).symm (c • g) = c • (blockEquiv b).symm g := rfl

/-- **Affine Block Decomposition** ([Li2023, Lemma 3.10]):
if `X` is an affine source over `t` bit-blocks `∀ i : Fin t, BitString (b i)` of codimension
`≤ r` (i.e. `(∑ i, b i) - r ≤ k`), then `X` is a convex mixture (`μ.bind`) of independent
product affine sources `PMF.pi (P c)` whose `i`-th block `P c i` is an affine source on
`BitString (b i)` of dimension at least `b i - r`. -/
theorem affineBlockDecomposition {t r k : ℕ} {b : Fin t → ℕ}
    {X : PMF (∀ i : Fin t, BitString (b i))}
    (hX : IsAffineSource (X.map (blockEquiv b).symm) k)
    (hr : (∑ i, b i) ≤ k + r) :
    ∃ (C : Type) (_ : Fintype C) (μ : PMF C)
      (P : C → ∀ i : Fin t, PMF (BitString (b i))),
      (∀ c i, ∃ kᵢ, b i ≤ kᵢ + r ∧ IsAffineSource (P c i) kᵢ) ∧
      X = μ.bind fun c => PMF.pi (P c) := by
  classical
  rcases hX with ⟨A_flat, hA_flat, hdim_flat, hX_flat⟩
  let eB : (∀ i : Fin t, BitString (b i)) ≃ₗ[Bool] BitString (∑ i, b i) :=
    { toAddEquiv := (blockEquiv b).symm
      map_smul' := fun c g => blockEquiv_symm_smul c g }
  have hX_eq : X = (uniformAffine A_flat hA_flat).map (blockEquiv b) := by
    calc X = (X.map (blockEquiv b).symm).map (blockEquiv b) := by
          rw [PMF.map_comp]
          have hcomp : (⇑(blockEquiv b) ∘ ⇑(blockEquiv b).symm :
              (∀ i : Fin t, BitString (b i)) → ∀ i : Fin t, BitString (b i)) = id :=
            funext fun g => (blockEquiv b).apply_symm_apply g
          rw [hcomp, PMF.map_id]
      _ = (uniformAffine A_flat hA_flat).map (blockEquiv b) := by rw [hX_flat]
  let A : AffineSubspace Bool (∀ i : Fin t, BitString (b i)) :=
    A_flat.map eB.symm.toAffineEquiv.toAffineMap
  obtain ⟨x₀_flat, hx₀_flat⟩ := hA_flat
  let x₀ := blockEquiv b x₀_flat
  have hx₀ : x₀ ∈ A := AffineSubspace.mem_map.mpr ⟨x₀_flat, hx₀_flat, rfl⟩
  let V : Submodule Bool (∀ i : Fin t, BitString (b i)) := A.direction
  let V_flat : Submodule Bool (BitString (∑ i, b i)) := A_flat.direction
  have hV_flat : V.map eB.toLinearMap = V_flat := by
    ext z
    simp only [V, A, AffineSubspace.map_direction, Submodule.mem_map]
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      change eB (eB.symm w) ∈ V_flat
      rwa [eB.apply_symm_apply]
    · intro hz
      exact ⟨eB.symm z, ⟨z, hz, rfl⟩, eB.apply_symm_apply z⟩
  let W : ∀ i : Fin t, Submodule Bool (BitString (b i)) :=
    fun i => V.comap (LinearMap.single Bool (fun j => BitString (b j)) i)
  let Wprod : Submodule Bool (∀ i : Fin t, BitString (b i)) :=
    ⨆ i : Fin t, (W i).map (LinearMap.single Bool (fun j => BitString (b j)) i)
  have hWprod_le : Wprod ≤ V := iSup_le fun i => Submodule.map_le_iff_le_comap.mpr le_rfl
  let Wprod_flat : Submodule Bool (BitString (∑ i, b i)) := Wprod.map eB.toLinearMap
  have hWprod_flat_le : Wprod_flat ≤ V_flat := by
    rw [← hV_flat]
    exact Submodule.map_mono hWprod_le
  obtain ⟨C_flat, hC_le, hC_inf, hC_sup⟩ :=
    exists_isCompl_submodule Wprod_flat V_flat hWprod_flat_le
  let C : Submodule Bool (∀ i : Fin t, BitString (b i)) := C_flat.map eB.symm.toLinearMap
  have hC_le_V : C ≤ V := by
    intro c hc
    obtain ⟨cf, hcf, rfl⟩ := Submodule.mem_map.mp hc
    have hcfV : cf ∈ V_flat := hC_le hcf
    rw [← hV_flat] at hcfV
    obtain ⟨v, hv, hv_eq⟩ := Submodule.mem_map.mp hcfV
    have hcv : eB.symm cf = v := eB.injective (by
      change eB (eB.symm cf) = eB v
      rw [eB.apply_symm_apply]
      exact hv_eq.symm)
    change eB.symm cf ∈ V
    rwa [hcv]
  have hCW_inf : C ⊓ Wprod = ⊥ := by
    rw [eq_bot_iff]
    intro v ⟨hvC, hvW⟩
    have hvCf : eB v ∈ C_flat := by
      obtain ⟨cf, hcf, rfl⟩ := Submodule.mem_map.mp hvC
      simpa using hcf
    have hvWf : eB v ∈ Wprod_flat := Submodule.mem_map.mpr ⟨v, hvW, rfl⟩
    have hbot : eB v ∈ C_flat ⊓ Wprod_flat := ⟨hvCf, hvWf⟩
    rw [hC_inf, Submodule.mem_bot] at hbot
    exact eB.map_eq_zero_iff.mp hbot
  have hCW_sup : C ⊔ Wprod = V := by
    apply le_antisymm (sup_le hC_le_V hWprod_le)
    intro v hv
    have hv_flat : eB v ∈ V_flat := by
      rw [← hV_flat]
      exact Submodule.mem_map.mpr ⟨v, hv, rfl⟩
    have hmem : eB v ∈ C_flat ⊔ Wprod_flat := by
      rw [hC_sup]; exact hv_flat
    obtain ⟨cf, hcf, wf, hwf, hsum⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨w, hw, hw_eq⟩ := hwf
    refine Submodule.mem_sup.mpr ⟨eB.symm cf, Submodule.mem_map.mpr ⟨cf, hcf, rfl⟩, w, hw, ?_⟩
    apply eB.injective
    rw [map_add, eB.apply_symm_apply]
    have hw_eq' : eB w = wf := hw_eq
    rw [hw_eq', hsum]
  let SA_flat := (Set.toFinite (A_flat : Set (BitString (∑ i, b i)))).toFinset
  let _ : Fintype C := Fintype.ofFinite C
  let _ (i : Fin t) : Fintype (W i) := Fintype.ofFinite (W i)
  have hpi_single_apply (f : ∀ c : Fin t, BitString (b c)) (i : Fin t) :
      (∑ c : Fin t, Pi.single c (f c)) i = f i := by
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · exact Pi.single_eq_same i _
    · intro c _ hc; exact Pi.single_eq_of_ne (Ne.symm hc) _
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hbool_sub_of_add_eq : ∀ p q r s u : Bool, p + q + s = p + r + u → q - r = u - s := by
    decide
  have hbool_add_of_sub_eq : ∀ p q r s : Bool, q + r = s - p → p + q + r = s := by
    decide
  have hmem_flat (c : C) (w : ∀ i : Fin t, W i) :
      (blockEquiv b).symm (fun i => x₀ i + c.1 i + (w i).1) ∈ SA_flat := by
    rw [Set.Finite.mem_toFinset]
    have hcV : c.1 ∈ V := hC_le_V c.2
    have hwV : (∑ i : Fin t, Pi.single i (w i).1 : ∀ i, BitString (b i)) ∈ V := by
      refine Submodule.sum_mem V fun i _ => hWprod_le (Submodule.mem_iSup_of_mem i ?_)
      exact Submodule.mem_map.mpr ⟨(w i).1, (w i).2, rfl⟩
    have hsum_in_A : x₀ + (c.1 + ∑ i : Fin t, Pi.single i (w i).1) ∈ A := by
      have := AffineSubspace.vadd_mem_of_mem_direction (V.add_mem hcV hwV) hx₀
      rw [vadd_eq_add, add_comm _ x₀] at this
      exact this
    have heq : (x₀ + (c.1 + ∑ i : Fin t, Pi.single i (w i).1)) =
        fun i => x₀ i + c.1 i + (w i).1 := by
      funext i
      simp only [Pi.add_apply, hpi_single_apply, add_assoc]
    rw [heq] at hsum_in_A
    obtain ⟨y, hy, hy_eq⟩ := AffineSubspace.mem_map.mp hsum_in_A
    have hy_eq' : y = (blockEquiv b).symm (fun i => x₀ i + c.1 i + (w i).1) :=
      (blockEquiv b).injective (by simpa [eB] using hy_eq)
    rwa [← hy_eq']
  have hbij : Function.Bijective (fun p : C × (∀ i : Fin t, W i) =>
      (⟨(blockEquiv b).symm (fun i => x₀ i + p.1.1 i + (p.2 i).1),
        hmem_flat p.1 p.2⟩ : SA_flat)) := by
    constructor
    · rintro ⟨⟨c₁, hc₁⟩, w₁⟩ ⟨⟨c₂, hc₂⟩, w₂⟩ h
      have hvec_blk : (fun i => x₀ i + c₁ i + (w₁ i).1) = fun i => x₀ i + c₂ i + (w₂ i).1 :=
        (blockEquiv b).symm.injective (congrArg Subtype.val h)
      have hvec : c₁ - c₂ = (∑ i, Pi.single i (w₂ i).1) - (∑ i, Pi.single i (w₁ i).1) := by
        funext i j
        have hij := congrFun (congrFun hvec_blk i) j
        simp only [Pi.sub_apply, hpi_single_apply] at hij ⊢
        exact hbool_sub_of_add_eq (x₀ i j) (c₁ i j) (c₂ i j) ((w₁ i).1 j) ((w₂ i).1 j) hij
      have hdiff_in_W : c₁ - c₂ ∈ Wprod := by
        rw [hvec]
        refine Wprod.sub_mem ?_ ?_ <;>
          exact Submodule.sum_mem Wprod fun i _ =>
            Submodule.mem_iSup_of_mem i (Submodule.mem_map.mpr ⟨_, (Subtype.coe_prop _), rfl⟩)
      have hdiff_in_C : c₁ - c₂ ∈ C := C.sub_mem hc₁ hc₂
      have hbot : c₁ - c₂ ∈ C ⊓ Wprod := ⟨hdiff_in_C, hdiff_in_W⟩
      rw [hCW_inf, Submodule.mem_bot] at hbot
      have hc_eq : c₁ = c₂ := sub_eq_zero.mp hbot
      subst hc_eq
      refine Prod.ext (Subtype.ext rfl) (funext fun i => Subtype.ext (funext fun j => ?_))
      have hij := congrFun (congrFun hvec_blk i) j
      simp only [Pi.add_apply, add_right_inj] at hij
      exact hij
    · rintro ⟨y_flat, hy_flat⟩
      let y := blockEquiv b y_flat
      have hyA : y ∈ A := AffineSubspace.mem_map.mpr
        ⟨y_flat, (Set.Finite.mem_toFinset _).mp hy_flat, rfl⟩
      have hyV : y -ᵥ x₀ ∈ C ⊔ Wprod := by
        rw [hCW_sup]
        exact AffineSubspace.vsub_mem_direction hyA hx₀
      obtain ⟨c, hc, u, hu, hcu⟩ := Submodule.mem_sup.mp hyV
      have hwmem : ∀ i : Fin t, u i ∈ W i := by
        have hWprod_coord : ∀ x ∈ Wprod, ∀ i : Fin t, x i ∈ W i := by
          intro x hx
          induction hx using Submodule.iSup_induction' with
          | mem j z hz =>
            obtain ⟨z₀, hz₀, rfl⟩ := Submodule.mem_map.mp hz
            intro i
            by_cases hij : i = j
            · subst hij
              simpa [W] using hz₀
            · simp only [LinearMap.single_apply, Pi.single_eq_of_ne hij]
              exact (W i).zero_mem
          | zero => intro i; exact (W i).zero_mem
          | add x y _ _ ihx ihy => intro i; exact (W i).add_mem (ihx i) (ihy i)
        exact hWprod_coord u hu
      refine ⟨⟨⟨c, hc⟩, fun i => ⟨u i, hwmem i⟩⟩, Subtype.ext ?_⟩
      apply (blockEquiv b).injective
      change (blockEquiv b) ((blockEquiv b).symm fun i => x₀ i + c i + u i) = (blockEquiv b) y_flat
      rw [(blockEquiv b).apply_symm_apply]
      funext i j
      have hij := congrFun (congrFun hcu i) j
      simp only [Pi.add_apply, vsub_eq_sub, Pi.sub_apply] at hij
      exact hbool_add_of_sub_eq (x₀ i j) (c i j) (u i j) (y i j) hij
  have hW_codim : ∀ i : Fin t, b i ≤ finrank Bool (W i) + r := by
    intro i
    let single_flat : BitString (b i) →ₗ[Bool] BitString (∑ j, b j) :=
      eB.toLinearMap.comp (LinearMap.single Bool (fun j => BitString (b j)) i)
    let liftZ : (Fin (b i) → ZMod 2) →ₗ[ZMod 2] (Fin (∑ j, b j) → ZMod 2) :=
      { toFun := fun z => toZModBits (Fin (∑ j, b j))
          (single_flat ((toZModBits (Fin (b i))).symm z))
        map_add' := fun a b => by simp only [map_add]
        map_smul' := fun c a => by
          rw [symm_toZModBits_smul, map_smul, toZModBits_smul, bitEquiv.symm_apply_apply]
          rfl }
    let gZ : (Fin (b i) → ZMod 2) →ₗ[ZMod 2]
        ((Fin (∑ j, b j) → ZMod 2) ⧸ toZModSub V_flat) :=
      (toZModSub V_flat).mkQ.comp liftZ
    have hker : LinearMap.ker gZ = toZModSub (W i) := by
      ext z
      obtain ⟨x, rfl⟩ := (toZModBits (Fin (b i))).surjective z
      change (toZModSub V_flat).mkQ (toZModBits (Fin (∑ j, b j))
        (single_flat ((toZModBits (Fin (b i))).symm ((toZModBits (Fin (b i))) x)))) = 0 ↔
        toZModBits (Fin (b i)) x ∈ toZModSub (W i)
      rw [(toZModBits (Fin (b i))).symm_apply_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, mem_toZModSub, mem_toZModSub]
      simp only [W, Submodule.mem_comap]
      constructor
      · intro hx
        rw [← hV_flat] at hx
        obtain ⟨y, hy, hy_eq⟩ := Submodule.mem_map.mp hx
        have hy_eq' : y = (LinearMap.single Bool (fun j => BitString (b j)) i) x :=
          eB.injective (show eB y = eB ((LinearMap.single Bool (fun j => BitString (b j)) i) x)
            from hy_eq)
        rwa [← hy_eq']
      · intro hx
        rw [← hV_flat]
        exact Submodule.mem_map.mpr
          ⟨(LinearMap.single Bool (fun j => BitString (b j)) i) x, hx, rfl⟩
    have hrank := LinearMap.finrank_range_add_finrank_ker gZ
    have hdom : finrank (ZMod 2) (Fin (b i) → ZMod 2) = b i := by simp
    have hker_dim : finrank (ZMod 2) (LinearMap.ker gZ) = finrank Bool (W i) := by
      rw [hker, finrank_bool_eq_finrank_toZMod]
    have hrange_le : finrank (ZMod 2) (LinearMap.range gZ) ≤
        finrank (ZMod 2) ((Fin (∑ j, b j) → ZMod 2) ⧸ toZModSub V_flat) :=
      Submodule.finrank_le _
    have hquot := Submodule.finrank_quotient_add_finrank (toZModSub V_flat)
    have hflat_tot : finrank (ZMod 2) (Fin (∑ j, b j) → ZMod 2) = ∑ j : Fin t, b j := by simp
    have hVflat_dim : finrank (ZMod 2) (toZModSub V_flat) = k := by
      rw [← finrank_bool_eq_finrank_toZMod, hdim_flat]
    rw [hdom, hker_dim] at hrank
    rw [hflat_tot, hVflat_dim] at hquot
    omega
  let P : C → ∀ i : Fin t, PMF (BitString (b i)) := fun c i =>
    uniformAffine (AffineSubspace.mk' (x₀ i + c.1 i) (W i))
      ⟨x₀ i + c.1 i, AffineSubspace.self_mem_mk' _ _⟩
  have hP_src : ∀ c i, ∃ kᵢ, b i ≤ kᵢ + r ∧ IsAffineSource (P c i) kᵢ := fun c i =>
    ⟨finrank Bool (W i), hW_codim i, AffineSubspace.mk' (x₀ i + c.1 i) (W i),
      ⟨x₀ i + c.1 i, AffineSubspace.self_mem_mk' _ _⟩, by rw [AffineSubspace.direction_mk'], rfl⟩
  have hpi_eq : ∀ c : C,
      ((PMF.uniformOfFintype (∀ i : Fin t, W i)).map fun w i => x₀ i + c.1 i + (w i).1) =
        PMF.pi (P c) := by
    intro c
    ext y
    rw [PMF.map_apply, PMF.pi_apply]
    simp only [PMF.uniformOfFintype_apply, P, uniformAffine, PMF.uniformOfFinset_apply]
    have hcard_prod : (Fintype.card (∀ i : Fin t, W i) : ENNReal) =
        ∏ i : Fin t, ((Set.toFinite (AffineSubspace.mk' (x₀ i + c.1 i) (W i) :
          Set (BitString (b i)))).toFinset.card : ENNReal) := by
      rw [Fintype.card_pi, Nat.cast_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [card_affineSubspace_toFinset _ ⟨x₀ i + c.1 i, AffineSubspace.self_mem_mk' _ _⟩,
        AffineSubspace.direction_mk', ← natCard_submodule_bool (W i), Nat.card_eq_fintype_card]
    by_cases hy : ∀ i : Fin t, y i ∈ (Set.toFinite
        (AffineSubspace.mk' (x₀ i + c.1 i) (W i) : Set (BitString (b i)))).toFinset
    · let w₀ : ∀ i : Fin t, W i := fun i => ⟨y i - (x₀ i + c.1 i), by
        have hyi := (Set.Finite.mem_toFinset _).mp (hy i)
        simpa [AffineSubspace.mem_mk', vsub_eq_sub] using hyi⟩
      have hw_uniq : ∀ w : (∀ i : Fin t, W i),
          (y = fun i => x₀ i + c.1 i + (w i).1) ↔ w = w₀ := by
        intro w
        constructor
        · intro hyw
          funext i
          ext1
          have hi := congrFun hyw i
          simp only [w₀, hi]
          abel
        · rintro rfl
          funext i
          simp only [w₀]
          abel
      have htsum : (∑' w : (∀ i : Fin t, W i),
          if y = (fun i => x₀ i + c.1 i + (w i).1) then
            (Fintype.card (∀ i : Fin t, W i) : ENNReal)⁻¹
          else 0) = (Fintype.card (∀ i : Fin t, W i) : ENNReal)⁻¹ := by
        rw [tsum_eq_single w₀]
        · rw [ite_eq_left ((hw_uniq w₀).mpr rfl)]
        · intro w hw
          rw [ite_eq_right (fun h => hw ((hw_uniq w).mp h))]
      rw [htsum, hcard_prod,
        ENNReal.prod_inv_distrib fun _ _ _ _ _ => Or.inr (ENNReal.natCast_ne_top _)]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [ite_eq_left (hy i)]
    · push Not at hy
      obtain ⟨i₀, hi₀⟩ := hy
      have hno : ∀ w : (∀ i : Fin t, W i), y ≠ fun i => x₀ i + c.1 i + (w i).1 := by
        intro w hyw
        apply hi₀
        rw [Set.Finite.mem_toFinset]
        have hi := congrFun hyw i₀
        simp [AffineSubspace.mem_mk', vsub_eq_sub, hi]
      have hzero : (∑' w : (∀ i : Fin t, W i),
          if y = (fun i => x₀ i + c.1 i + (w i).1) then
            (Fintype.card (∀ i : Fin t, W i) : ENNReal)⁻¹
          else 0) = 0 :=
        (tsum_congr fun w => ite_eq_right (hno w)).trans tsum_zero
      rw [hzero]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i₀) (ite_eq_right hi₀)
  refine ⟨C, inferInstance, PMF.uniformOfFintype C, P, hP_src, ?_⟩
  let e : C × (∀ i : Fin t, W i) ≃ SA_flat := Equiv.ofBijective _ hbij
  have : Nonempty SA_flat := ⟨⟨x₀_flat, (Set.Finite.mem_toFinset _).mpr hx₀_flat⟩⟩
  rw [hX_eq]
  calc (uniformAffine A_flat ⟨x₀_flat, hx₀_flat⟩).map (blockEquiv b)
      = ((PMF.uniformOfFintype SA_flat).map Subtype.val).map (blockEquiv b) := by
          congr 1
          exact (uniformOfFintype_finset_map_val SA_flat).symm
    _ = ((PMF.uniformOfFintype (C × (∀ i : Fin t, W i))).map
          (fun p => blockEquiv b (e p).1)) := by
          rw [← uniformOfFintype_map_equiv e, PMF.map_comp, PMF.map_comp]
          rfl
    _ = (PMF.uniformOfFintype C).bind (fun c =>
          (PMF.uniformOfFintype (∀ i : Fin t, W i)).map fun w i => x₀ i + c.1 i + (w i).1) := by
          rw [← uniformOfFintype_bind_map (fun c w => blockEquiv b (e (c, w)).1)]
          simp only [e, Equiv.ofBijective_apply, (blockEquiv b).apply_symm_apply]
    _ = (PMF.uniformOfFintype C).bind (fun c => PMF.pi (P c)) := by
          congr 1
          funext c
          exact hpi_eq c

/-! ### Bridges from affine and sumset extractors to `IsAffineDisperser` ([Li2023, Cor. 7.14]) -/

/-- A seedless **`(k, ε)` affine extractor** maps every `(n, k)` affine source to within statistical
distance `ε` of the uniform distribution on `BitString m` ([Li2023]). -/
@[expose] def IsAffineExtractor {n m : ℕ} (ext : BitString n → BitString m)
    (k : ℕ) (ε : ℝ) : Prop :=
  ∀ X : PMF (BitString n), IsAffineSource X k →
    dist (X.map ext) (PMF.uniformOfFintype (BitString m)) ≤ ε

/-- A **`(k₁, k₂, ε)` sumset extractor** maps the XOR-sum `A + B` of any two independent sources
`A, B` of min-entropy at least `k₁` and `k₂` to within statistical distance `ε` of uniform
([Li2023, Thm. 7.13]). -/
@[expose] def IsSumsetExtractor {n m : ℕ} (ext : BitString n → BitString m) (k₁ k₂ : ℕ)
    (ε : ℝ) : Prop :=
  ∀ A B : PMF (BitString n), (k₁ : ℝ) ≤ minEntropy A → (k₂ : ℝ) ≤ minEntropy B →
    dist ((A.bind fun a => B.map fun b => a + b).map ext)
      (PMF.uniformOfFintype (BitString m)) ≤ ε

/-- Extracting one bit of an `m`-bit affine extractor with error `< 1 / 2` gives an
`IsAffineDisperser` for dimension `k`. -/
theorem isAffineDisperser_of_isAffineExtractor {n m k : ℕ} {ε : ℝ}
    {ext : BitString n → BitString m} (hm : 0 < m) (hε : ε < 1 / 2)
    (hext : IsAffineExtractor ext k ε) :
    IsAffineDisperser (fun x => ext x ⟨0, hm⟩) k := by
  have proj_uniform : (PMF.uniformOfFintype (BitString m)).map (fun y : BitString m => y ⟨0, hm⟩) =
      PMF.uniformOfFintype Bool := by
    have he := uniformOfFintype_pi_map_restrict (ι := Fin m) (π := fun _ => Bool)
      ({⟨0, hm⟩} : Finset (Fin m))
    let e1 : ((i : ({⟨0, hm⟩} : Finset (Fin m))) → Bool) ≃ Bool :=
      { toFun := fun f => f ⟨⟨0, hm⟩, Finset.mem_singleton_self _⟩
        invFun := fun b _ => b
        left_inv := fun f => by
          funext ⟨i, hi⟩
          obtain rfl : i = ⟨0, hm⟩ := Finset.mem_singleton.mp hi
          rfl
        right_inv := fun _ => rfl }
    calc (PMF.uniformOfFintype (BitString m)).map (fun y : BitString m => y ⟨0, hm⟩)
        = ((PMF.uniformOfFintype (BitString m)).map
            ({⟨0, hm⟩} : Finset (Fin m)).restrict).map e1 := by
            rw [PMF.map_comp]; rfl
      _ = (PMF.uniformOfFintype ((i : ({⟨0, hm⟩} : Finset (Fin m))) → Bool)).map e1 := by
            rw [he]
      _ = PMF.uniformOfFintype Bool := uniformOfFintype_map_equiv e1
  have hk_pos : 0 < k := by
    by_contra hk0
    have hk : k = 0 := by omega
    subst hk
    let A0 : AffineSubspace Bool (BitString n) := AffineSubspace.mk' 0 ⊥
    have hA0 : (A0 : Set (BitString n)).Nonempty := ⟨0, AffineSubspace.self_mem_mk' 0 ⊥⟩
    have hsrc : IsAffineSource (uniformAffine A0 hA0) 0 :=
      ⟨A0, hA0, by rw [AffineSubspace.direction_mk', finrank_bot], rfl⟩
    have hdist0 : dist ((uniformAffine A0 hA0).map ext) (PMF.uniformOfFintype (BitString m)) ≤ ε :=
      hext _ hsrc
    have hdist_bit :
        dist (((uniformAffine A0 hA0).map ext).map (fun y : BitString m => y ⟨0, hm⟩))
          ((PMF.uniformOfFintype (BitString m)).map (fun y : BitString m => y ⟨0, hm⟩)) ≤ ε :=
      (dist_map_le _ _ _).trans hdist0
    have hpure : uniformAffine A0 hA0 = PMF.pure 0 := by
      ext x
      rw [uniformAffine_apply, AffineSubspace.direction_mk', finrank_bot, pow_zero, Nat.cast_one,
        inv_one, PMF.pure_apply]
      by_cases hx : x = 0
      · subst hx
        rw [ite_eq_left (AffineSubspace.self_mem_mk' 0 ⊥), ite_eq_left rfl]
      · have hnot : x ∉ A0 := by
          simp only [A0, AffineSubspace.mem_mk', Submodule.mem_bot,
            vsub_eq_sub, sub_zero]
          exact hx
        rw [ite_eq_right hnot, ite_eq_right hx]
    rw [PMF.map_comp, proj_uniform, hpure, PMF.pure_map, dist_uniformOfFintype_bool] at hdist_bit
    cases hbx : ext 0 ⟨0, hm⟩ <;> simp [hbx] at hdist_bit <;> norm_num at hdist_bit <;> linarith
  refine isAffineDisperser_of_forall_exists_ne fun A hdim => ?_
  have hA : (A : Set (BitString n)).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have hbot : A = ⊥ := SetLike.coe_injective (by simpa using hempty)
    rw [hbot, AffineSubspace.direction_bot, finrank_bot] at hdim
    omega
  by_contra hconst
  push Not at hconst
  obtain ⟨x₀, hx₀⟩ := hA
  have hpure : (uniformAffine A ⟨x₀, hx₀⟩).map (fun x => ext x ⟨0, hm⟩) =
      PMF.pure (ext x₀ ⟨0, hm⟩) := by
    ext b
    rw [PMF.map_apply, PMF.pure_apply]
    trans (∑' x, if b = ext x₀ ⟨0, hm⟩ then uniformAffine A ⟨x₀, hx₀⟩ x else 0)
    · refine tsum_congr fun x => ?_
      by_cases hx : x ∈ A
      · rw [hconst x hx x₀ hx₀]
        split_ifs <;> rfl
      · have h0 : uniformAffine A ⟨x₀, hx₀⟩ x = 0 :=
          (PMF.apply_eq_zero_iff _ _).mpr ((mem_support_uniformAffine_iff A ⟨x₀, hx₀⟩ x).not.mpr hx)
        rw [h0]
        split_ifs <;> rfl
    · by_cases hb : b = ext x₀ ⟨0, hm⟩
      · rw [ite_eq_left hb]
        trans ∑' x, uniformAffine A ⟨x₀, hx₀⟩ x
        · refine tsum_congr fun x => ite_eq_left hb
        · exact PMF.tsum_coe _
      · simp [hb]
  have hdist : dist (((uniformAffine A ⟨x₀, hx₀⟩).map ext).map (fun y : BitString m => y ⟨0, hm⟩))
      ((PMF.uniformOfFintype (BitString m)).map (fun y : BitString m => y ⟨0, hm⟩)) ≤ ε :=
    (dist_map_le _ _ _).trans (hext _ ⟨A, ⟨x₀, hx₀⟩, hdim, rfl⟩)
  rw [PMF.map_comp, show (fun y : BitString m => y ⟨0, hm⟩) ∘ ext = fun x => ext x ⟨0, hm⟩ from rfl,
    hpure, proj_uniform, dist_uniformOfFintype_bool] at hdist
  cases hbx : ext x₀ ⟨0, hm⟩ <;> simp [hbx] at hdist <;> norm_num at hdist <;> linarith

/-- Splitting an `(n, k)` affine source with `k₁ + k₂ ≤ k` into a sum `A + B` of two
independent affine sources of dimensions `k₁` and `k - k₁ ≥ k₂`. -/
theorem exists_independent_affine_sum_of_isAffineSource {n k k₁ k₂ : ℕ}
    {X : PMF (BitString n)} (hX : IsAffineSource X k) (hk : k₁ + k₂ ≤ k) :
    ∃ A B : PMF (BitString n), IsAffineSource A k₁ ∧ IsAffineSource B (k - k₁) ∧
      (k₂ : ℝ) ≤ minEntropy B ∧ X = A.bind fun a => B.map fun b => a + b := by
  rcases hX with ⟨Asub, hAsub, hdim, rfl⟩
  obtain ⟨x₀, hx₀⟩ := hAsub
  obtain ⟨V₁, hV₁_le, hV₁_dim⟩ :=
    exists_submodule_finrank_eq_bitString Asub.direction k₁ (by omega)
  obtain ⟨V₂, hV₂_le, hcompl_inf, hcompl_sup⟩ :=
    exists_isCompl_submodule V₁ Asub.direction hV₁_le
  have hV₂_dim : finrank Bool V₂ = k - k₁ := by
    have hsum := finrank_sup_add_finrank_inf_bitString V₂ V₁
    rw [hcompl_inf, hcompl_sup, finrank_bot, add_zero, hdim, hV₁_dim] at hsum
    omega
  let A := uniformAffine (AffineSubspace.mk' x₀ V₁) ⟨x₀, AffineSubspace.self_mem_mk' x₀ V₁⟩
  let B := uniformAffine (AffineSubspace.mk' 0 V₂) ⟨0, AffineSubspace.self_mem_mk' 0 V₂⟩
  have hA : IsAffineSource A k₁ :=
    ⟨AffineSubspace.mk' x₀ V₁, _, by rw [AffineSubspace.direction_mk', hV₁_dim], rfl⟩
  have hB : IsAffineSource B (k - k₁) :=
    ⟨AffineSubspace.mk' 0 V₂, _, by rw [AffineSubspace.direction_mk', hV₂_dim], rfl⟩
  refine ⟨A, B, hA, hB, ?_,
    uniformAffine_eq_bind_add_of_isCompl Asub hx₀ hV₁_le hV₂_le
      ⟨by rw [inf_comm]; exact hcompl_inf, by rw [sup_comm]; exact hcompl_sup⟩⟩
  rw [minEntropy_of_isAffineSource hB]
  exact_mod_cast (by omega : k₂ ≤ k - k₁)

/-- A `(k₁, k₂, ε)` sumset extractor is a `(k, ε)` affine extractor whenever `k₁ + k₂ ≤ k`
([Li2023, Cor. 7.14]). -/
theorem isAffineExtractor_of_isSumsetExtractor {n m k k₁ k₂ : ℕ} {ε : ℝ}
    {ext : BitString n → BitString m} (hk : k₁ + k₂ ≤ k)
    (hext : IsSumsetExtractor ext k₁ k₂ ε) :
    IsAffineExtractor ext k ε := by
  intro X hX
  obtain ⟨A, B, hA, hB, hkB, rfl⟩ := exists_independent_affine_sum_of_isAffineSource hX hk
  have hkA : (k₁ : ℝ) ≤ minEntropy A := by
    rw [minEntropy_of_isAffineSource hA]
  exact hext A B hkA hkB

/-- A `(k₁, k₂, ε)` sumset extractor outputting at least one bit with `ε < 1 / 2` yields an
`IsAffineDisperser` for dimension `k ≥ k₁ + k₂` ([Li2023, Cor. 7.14]). -/
theorem isAffineDisperser_of_isSumsetExtractor {n m k k₁ k₂ : ℕ} {ε : ℝ}
    {ext : BitString n → BitString m} (hm : 0 < m) (hε : ε < 1 / 2) (hk : k₁ + k₂ ≤ k)
    (hext : IsSumsetExtractor ext k₁ k₂ ε) :
    IsAffineDisperser (fun x => ext x ⟨0, hm⟩) k :=
  isAffineDisperser_of_isAffineExtractor hm hε (isAffineExtractor_of_isSumsetExtractor hk hext)

end AffineSource

end Cslib.AffineDisperser.Li
