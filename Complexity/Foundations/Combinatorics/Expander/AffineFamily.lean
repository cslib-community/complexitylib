/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.AffineTower
public import Complexity.Foundations.Combinatorics.Expander.Family
public import Complexity.Foundations.Combinatorics.Expander.TowerFamily
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

/-!
# Arithmetic expanders on every vertex count

The affine-plane base, recursive tower numbering, and bounded-fiber contraction give a computable
rotation on exactly `Fin n` for every `n`. An explicit numbering of a field of size `q ≥ 256`
gives degree `2*q^12` and spectral expansion at most `1 - 9/(400*q^16)`.

`arithmeticExpander` instantiates the construction at `ZMod 257`, using its arithmetic equivalence
with `Fin 257`. It performs no finite graph search or nonconstructive enumeration. The constants
are enormous: executing one rotation and enumerating all edges are very different workloads.
The uniform polynomial-time realization is certified in
`Computability/Machines/Turing/MultiTape/Complexity/PolyTime/RotationMap/Family`; it constructs
complete tables in time polynomial in the vertex count, rather than in its bit length.

## Main definitions

* `Cslib.RotationMap.affinePlaneTowerBaseNumbering`: number the eight field coordinates.
* `Cslib.RotationMap.AffinePlaneFamilyLabel`: the fixed labels of the contracted lazy arithmetic
  tower.
* `Cslib.RotationMap.affinePlaneFamily`: contract the arithmetic tower to each requested size.
* `Cslib.RotationMap.arithmeticExpander`: the concrete family over `ZMod 257`.
* `Cslib.RotationMap.arithmeticExpanderFamily`: its interpretation on arbitrary finite types.

## Main results

* `Cslib.RotationMap.spectralExpansion_affinePlaneFamily_le`: a uniform gap for numbered fields.
* `Cslib.RotationMap.spectralExpansion_arithmeticExpander_le`: the concrete spectral bound.

## References

* [O. Reingold, S. Vadhan, A. Wigderson, *Entropy waves, the zig-zag graph product, and new
  constant-degree expanders*][ReingoldVadhanWigderson2002], Sections 1.2 and 5.1 for the tower
  and arithmetic base; the arbitrary-size contraction is supplied separately here.
-/

@[expose] public section

namespace Cslib.RotationMap

variable {K : Type*} {q : ℕ}

/-- Number eight field coordinates by pairing their explicit indices, without enumeration. -/
def affinePlaneTowerBaseNumbering (numbering : K ≃ Fin q) :
    AffinePlaneTowerBaseVertex K ≃ Fin (q ^ 8) :=
  let pair := (numbering.prodCongr numbering).trans finProdFinEquiv
  (IteratedProd.equivFin pair pair 3).trans (finCongr (by ring))

/-- The fixed label type of the contracted lazy arithmetic tower over a field with `q` elements. -/
abbrev AffinePlaneFamilyLabel (K : Type*) (q : ℕ) : Type _ :=
  (Fin (q ^ 8) × ((K × K) × (K × K))) ⊕ (Fin (q ^ 8) × ((K × K) × (K × K)))

/-- Use a numbered field as an arithmetic base, then contract the tower to the requested size. -/
def affinePlaneFamily [Field K] (numbering : K ≃ Fin q) (hq : 1 < q) (n : ℕ) :
    RotationMap (Fin n) (AffinePlaneFamilyLabel K q) :=
  zigzagTowerFamily (affinePlaneTowerBase K) (affinePlaneTowerBaseEquiv K)
    (affinePlaneTowerBaseNumbering numbering) (Nat.one_lt_pow (by decide) hq) n

/-- The arithmetic family has degree `2*q^12`, independently of the requested vertex count. -/
theorem card_affinePlaneFamilyLabel [Fintype K] (numbering : K ≃ Fin q) :
    Fintype.card (AffinePlaneFamilyLabel K q) = 2 * q ^ 12 := by
  have hq : Fintype.card K = q := (Fintype.card_congr numbering).trans (Fintype.card_fin q)
  simp only [AffinePlaneFamilyLabel, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, hq]
  ring

/-- A numbered field with at least 256 elements yields a positive uniform spectral gap. -/
theorem spectralExpansion_affinePlaneFamily_le [Field K] [Fintype K]
    (numbering : K ≃ Fin q) (hq : 256 ≤ q) (n : ℕ) :
    (affinePlaneFamily numbering (by lia) n).spectralExpansion ≤
      1 - 9 / (400 * q ^ 16) := by
  have hcard : Fintype.card K = q :=
    (Fintype.card_congr numbering).trans (Fintype.card_fin q)
  have hH := spectralExpansion_affinePlaneTowerBase_le_one_div_five K (by lia)
  have hH0 := (affinePlaneTowerBase K).spectralExpansion_nonneg
  have hc : (2 / 5 : ℝ) ^ 2 + (affinePlaneTowerBase K).spectralExpansion +
      (affinePlaneTowerBase K).spectralExpansion ^ 2 ≤ 2 / 5 := by nlinarith
  have h := spectralExpansion_zigzagTowerFamily_le (affinePlaneTowerBase K)
    (affinePlaneTowerBaseEquiv K) (affinePlaneTowerBaseNumbering numbering)
    (Nat.one_lt_pow (by decide) (by lia)) hc (by norm_num) n
  convert h using 1
  · rfl
  · push_cast
    ring

/-- A concrete arithmetic expander on exactly `n` vertices, with a fixed degree. -/
def arithmeticExpander (n : ℕ) : RotationMap (Fin n) (AffinePlaneFamilyLabel (ZMod 257) 257) :=
  have : Fact (Nat.Prime 257) := ⟨by norm_num⟩
  affinePlaneFamily (ZMod.finEquiv 257).toEquiv.symm (by decide) n

/-- The concrete family has a positive spectral gap independent of `n`. -/
theorem spectralExpansion_arithmeticExpander_le (n : ℕ) :
    (arithmeticExpander n).spectralExpansion ≤ 1 - 9 / (400 * (257 : ℝ) ^ 16) := by
  have : Fact (Nat.Prime 257) := ⟨by norm_num⟩
  exact spectralExpansion_affinePlaneFamily_le (ZMod.finEquiv 257).toEquiv.symm (by decide) n

/-- Every member of the concrete family has positive spectral gap. -/
theorem spectralExpansion_arithmeticExpander_lt_one (n : ℕ) :
    (arithmeticExpander n).spectralExpansion < 1 :=
  (spectralExpansion_arithmeticExpander_le n).trans_lt (by norm_num)

/-- The arithmetic construction interpreted as an expander family on arbitrary finite types.
The numbering chosen by this wrapper is noncomputable; `arithmeticExpander` itself is executable
on `Fin n`, and an explicit equivalence allows executable transport to other representations. -/
noncomputable def arithmeticExpanderFamily :
    ExpanderFamily (AffinePlaneFamilyLabel (ZMod 257) 257) (1 - 9 / (400 * (257 : ℝ) ^ 16)) :=
  .ofFin arithmeticExpander spectralExpansion_arithmeticExpander_le

end Cslib.RotationMap
