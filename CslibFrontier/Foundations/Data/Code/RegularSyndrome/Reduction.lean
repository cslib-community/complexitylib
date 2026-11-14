/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.RegularSyndrome
public import CslibFrontier.Foundations.Data.Finset.Density
public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination

/-!
# Exact core of the syndrome-to-regular-syndrome reduction

The SD-in-the-Head v3 reduction first permutes the columns of a parity-check matrix, restricts
the resulting instance to fewer rows, invokes a regular-syndrome solver, validates the returned
word against the full permuted matrix, and finally applies the inverse coordinate permutation.
This module formalizes that deterministic core and the exact probability that a uniformly
permuted fixed-weight support becomes regular [SDitH2026, Section 5.1, pp. 42--43].

The source next estimates the probability that the truncated instance has a unique regular
solution heuristically. No such estimate, and in particular no `exp (-1 / theta)` factor, is a
result of this module.

## Main definitions

* `Cslib.Code.permuteWord`, `Cslib.Code.permuteColumns`: coordinated reindexing of a word and
  parity-check matrix.
* `Cslib.Code.restrictRows`, `Cslib.Code.restrictSyndrome`: restriction to the retained checks.
* `Cslib.Code.sdToRsdPermutationCore`: the source reduction's deterministic solver wrapper.
* `Cslib.Code.regularCombinations`: the fixed-cardinality supports with one position per chunk.

## Main results

* `Cslib.Code.syndrome_permuteColumns_permuteWord`: column permutation preserves the syndrome.
* `Cslib.Code.IsRegularSyndromeSolution.restrictRows`: a full regular-syndrome solution remains a
  solution after retaining fewer checks.
* `Cslib.Code.sdToRsdPermutationCore_sound`: every accepted wrapper output has the requested
  syndrome and Hamming weight.
* `Cslib.Code.sdToRsdPermutationCore_eq_some_of_unique`: uniqueness of the truncated regular
  solution makes a successful solver output pass the full validation.
* `Cslib.Code.dens_permute_mem_regularCombinations`: the exact regularization probability is
  `chunkSize ^ chunks / Nat.choose (chunks * chunkSize) chunks`.

## References

* [*The Syndrome Decoding in the Head Signature Scheme*, v3.0][SDitH2026]
-/

public section

open scoped Pointwise

namespace Cslib.Code

open Finset Matrix

/-- Reindex a word so that its old coordinate `i` moves to the new coordinate `sigma i`. -/
@[expose]
def permuteWord {ι R : Type*} (sigma : Equiv.Perm ι) (x : ι → R) : ι → R :=
  x ∘ sigma.symm

/-- Apply the same coordinate permutation to the columns of a matrix. -/
@[expose]
def permuteColumns {κ ι R : Type*} (sigma : Equiv.Perm ι) (H : Matrix κ ι R) :
    Matrix κ ι R :=
  H.submatrix id sigma.symm

/-- Undo the coordinate permutation on a returned word. -/
@[expose]
def unpermuteWord {ι R : Type*} (sigma : Equiv.Perm ι) (x : ι → R) : ι → R :=
  x ∘ sigma

@[simp]
theorem unpermuteWord_permuteWord {ι R : Type*} (sigma : Equiv.Perm ι) (x : ι → R) :
    unpermuteWord sigma (permuteWord sigma x) = x := by
  funext i
  simp [unpermuteWord, permuteWord]

@[simp]
theorem permuteWord_unpermuteWord {ι R : Type*} (sigma : Equiv.Perm ι) (x : ι → R) :
    permuteWord sigma (unpermuteWord sigma x) = x := by
  funext i
  simp [unpermuteWord, permuteWord]

@[simp]
theorem permuteColumns_symm_permuteColumns {κ ι R : Type*}
    (sigma : Equiv.Perm ι) (H : Matrix κ ι R) :
    permuteColumns sigma.symm (permuteColumns sigma H) = H := by
  ext i j
  simp [permuteColumns]

@[simp]
theorem permuteColumns_permuteColumns_symm {κ ι R : Type*}
    (sigma : Equiv.Perm ι) (H : Matrix κ ι R) :
    permuteColumns sigma (permuteColumns sigma.symm H) = H := by
  ext i j
  simp [permuteColumns]

/-- Permuting both a word and the columns of its parity-check matrix preserves its syndrome. -/
theorem syndrome_permuteColumns_permuteWord {κ ι R : Type*} [Fintype ι] [CommRing R]
    (sigma : Equiv.Perm ι) (H : Matrix κ ι R) (x : ι → R) :
    syndrome (permuteColumns sigma H) (permuteWord sigma x) = syndrome H x := by
  rw [syndrome_eq, syndrome_eq]
  simpa [permuteColumns, permuteWord, Function.comp_def] using
    submatrix_mulVec_equiv H (permuteWord sigma x) id sigma.symm

/-- A coordinate permutation preserves Hamming weight. -/
theorem hammingNorm_permuteWord {ι R : Type*} [Fintype ι] [DecidableEq R] [Zero R]
    (sigma : Equiv.Perm ι) (x : ι → R) :
    hammingNorm (permuteWord sigma x) = hammingNorm x := by
  classical
  let e :
      {i : ι // permuteWord sigma x i ≠ 0} ≃ {i : ι // x i ≠ 0} :=
    { toFun := fun i => ⟨sigma.symm i, i.2⟩
      invFun := fun i => ⟨sigma i, by simpa [permuteWord] using i.2⟩
      left_inv := fun i => by simp
      right_inv := fun i => by simp }
  rw [hammingNorm, ← Fintype.card_subtype, hammingNorm, ← Fintype.card_subtype]
  exact Fintype.card_congr e

/-- Keep only the checks selected by `rows`. -/
@[expose]
def restrictRows {κ' κ ι R : Type*} (rows : κ' ↪ κ) (H : Matrix κ ι R) :
    Matrix κ' ι R :=
  H.submatrix rows id

/-- Keep the syndrome coordinates selected by `rows`. -/
@[expose]
def restrictSyndrome {κ' κ R : Type*} (rows : κ' ↪ κ) (y : κ → R) : κ' → R :=
  y ∘ rows

/-- Restricting matrix rows and syndrome coordinates commutes with syndrome evaluation. -/
theorem syndrome_restrictRows {κ' κ ι R : Type*} [Fintype ι] [CommRing R]
    (rows : κ' ↪ κ) (H : Matrix κ ι R) (x : ι → R) :
    syndrome (restrictRows rows H) x = restrictSyndrome rows (syndrome H x) := by
  rw [syndrome_eq, syndrome_eq]
  simpa [restrictRows, restrictSyndrome, Function.comp_def] using
    submatrix_mulVec_equiv H x rows (Equiv.refl ι)

/-- A regular-syndrome solution remains a solution after retaining fewer parity checks. -/
theorem IsRegularSyndromeSolution.restrictRows
    {retainedChecks fullChecks chunks chunkSize : ℕ}
    (rows : Fin retainedChecks ↪ Fin fullChecks)
    {H : Matrix (Fin fullChecks) (Fin chunks × Fin chunkSize) Bool}
    {y : Fin fullChecks → Bool} {x : Fin chunks × Fin chunkSize → Bool}
    (hx : IsRegularSyndromeSolution H y x) :
    IsRegularSyndromeSolution (restrictRows rows H) (restrictSyndrome rows y) x := by
  refine ⟨hx.1, ?_⟩
  rw [syndrome_restrictRows, hx.2]

/-- The retained instance given to the regular-syndrome solver. -/
@[expose]
def restrictedPermutedMatrix {retainedChecks fullChecks : ℕ} {ι : Type*}
    (rows : Fin retainedChecks ↪ Fin fullChecks) (sigma : Equiv.Perm ι)
    (H : Matrix (Fin fullChecks) ι Bool) : Matrix (Fin retainedChecks) ι Bool :=
  restrictRows rows (permuteColumns sigma H)

/-- The source reduction's deterministic wrapper around one regular-syndrome solver call.

The solver is intentionally an explicit argument. This finite relation-level definition does not
assign it a distribution, success probability, running time, or program-description size. -/
@[expose]
def sdToRsdPermutationCore {retainedChecks fullChecks chunks chunkSize : ℕ}
    (rows : Fin retainedChecks ↪ Fin fullChecks)
    (sigma : Equiv.Perm (Fin chunks × Fin chunkSize))
    (solver : Matrix (Fin retainedChecks) (Fin chunks × Fin chunkSize) Bool →
      (Fin retainedChecks → Bool) →
      Option (Fin chunks × Fin chunkSize → Bool))
    (H : Matrix (Fin fullChecks) (Fin chunks × Fin chunkSize) Bool)
    (y : Fin fullChecks → Bool) :
    Option (Fin chunks × Fin chunkSize → Bool) :=
  match solver (restrictedPermutedMatrix rows sigma H) (restrictSyndrome rows y) with
  | none => none
  | some xHat =>
      if syndrome (permuteColumns sigma H) xHat = y then
        some (unpermuteWord sigma xHat)
      else
        none

/-- Every output accepted by the full-syndrome check is a standard syndrome solution of weight
`chunks`, provided the solver's returned word satisfies the retained regular instance. -/
theorem sdToRsdPermutationCore_sound {retainedChecks fullChecks chunks chunkSize : ℕ}
    (rows : Fin retainedChecks ↪ Fin fullChecks)
    (sigma : Equiv.Perm (Fin chunks × Fin chunkSize))
    (solver : Matrix (Fin retainedChecks) (Fin chunks × Fin chunkSize) Bool →
      (Fin retainedChecks → Bool) →
      Option (Fin chunks × Fin chunkSize → Bool))
    (H : Matrix (Fin fullChecks) (Fin chunks × Fin chunkSize) Bool)
    (y : Fin fullChecks → Bool)
    (x : Fin chunks × Fin chunkSize → Bool)
    (hsolver : ∀ xHat,
      solver (restrictedPermutedMatrix rows sigma H) (restrictSyndrome rows y) = some xHat →
        IsRegularSyndromeSolution (restrictedPermutedMatrix rows sigma H)
          (restrictSyndrome rows y) xHat)
    (hcore : sdToRsdPermutationCore rows sigma solver H y = some x) :
    hammingNorm x = chunks ∧ syndrome H x = y := by
  unfold sdToRsdPermutationCore at hcore
  split at hcore <;> rename_i hrun
  · contradiction
  · split at hcore <;> rename_i hfull
    · simp only [Option.some.injEq] at hcore
      subst x
      have hregular := (hsolver _ hrun).1
      constructor
      · have hweight := hammingNorm_permuteWord sigma (unpermuteWord sigma xHat)
        rw [permuteWord_unpermuteWord] at hweight
        exact hweight.symm.trans hregular.hammingNorm_eq
      · calc
          syndrome H (unpermuteWord sigma xHat) =
              syndrome (permuteColumns sigma H)
                (permuteWord sigma (unpermuteWord sigma xHat)) :=
            (syndrome_permuteColumns_permuteWord sigma H _).symm
          _ = syndrome (permuteColumns sigma H) xHat := by
            rw [permuteWord_unpermuteWord]
          _ = y := hfull
    · contradiction

/-- If the retained regular instance has a unique solution, a successful sound solver call
returns the permuted original solution, which passes the full validation. This is the exact step
immediately preceding the heuristic uniqueness estimate in the source. -/
theorem sdToRsdPermutationCore_eq_some_of_unique
    {retainedChecks fullChecks chunks chunkSize : ℕ}
    (rows : Fin retainedChecks ↪ Fin fullChecks)
    (sigma : Equiv.Perm (Fin chunks × Fin chunkSize))
    (solver : Matrix (Fin retainedChecks) (Fin chunks × Fin chunkSize) Bool →
      (Fin retainedChecks → Bool) →
      Option (Fin chunks × Fin chunkSize → Bool))
    (H : Matrix (Fin fullChecks) (Fin chunks × Fin chunkSize) Bool)
    (y : Fin fullChecks → Bool)
    (x xHat : Fin chunks × Fin chunkSize → Bool)
    (hxSyndrome : syndrome H x = y)
    (hxRegular : IsRegularWord (permuteWord sigma x))
    (hsolver : solver (restrictedPermutedMatrix rows sigma H) (restrictSyndrome rows y) =
      some xHat)
    (hxHat : IsRegularSyndromeSolution (restrictedPermutedMatrix rows sigma H)
      (restrictSyndrome rows y) xHat)
    (hunique : ∃! z, IsRegularSyndromeSolution (restrictedPermutedMatrix rows sigma H)
      (restrictSyndrome rows y) z) :
    sdToRsdPermutationCore rows sigma solver H y = some x := by
  have hxPermutedSyndrome : syndrome (permuteColumns sigma H) (permuteWord sigma x) = y := by
    rw [syndrome_permuteColumns_permuteWord, hxSyndrome]
  have hxRetained : IsRegularSyndromeSolution (restrictedPermutedMatrix rows sigma H)
      (restrictSyndrome rows y) (permuteWord sigma x) := by
    apply IsRegularSyndromeSolution.restrictRows rows
    exact ⟨hxRegular, hxPermutedSyndrome⟩
  have hxHatEq : xHat = permuteWord sigma x := hunique.unique hxHat hxRetained
  unfold sdToRsdPermutationCore
  rw [hsolver, hxHatEq]
  simp [hxPermutedSyndrome]

/-- The support of a Boolean word. -/
def boolSupport {ι : Type*} [Fintype ι] (x : ι → Bool) : Finset ι :=
  Finset.univ.filter fun i => x i = true

@[simp]
theorem card_boolSupport {ι : Type*} [Fintype ι] (x : ι → Bool) :
    (boolSupport x).card = hammingNorm x := by
  rw [hammingNorm]
  apply congrArg Finset.card
  ext i
  simp only [boolSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  cases x i <;> simp

private theorem boolSupport_injective {ι : Type*} [Fintype ι] :
    Function.Injective (boolSupport : (ι → Bool) → Finset ι) := by
  intro x z h
  funext i
  have hi : (x i = true) = (z i = true) := by
    apply propext
    simpa [boolSupport] using Finset.ext_iff.mp h i
  cases hxi : x i <;> cases hzi : z i <;> simp_all

/-- The support containing the selected position in every regular chunk. -/
def regularSupport {chunks chunkSize : ℕ} (positions : Fin chunks → Fin chunkSize) :
    Finset (Fin chunks × Fin chunkSize) :=
  boolSupport (regularWord positions)

@[simp]
theorem mem_regularSupport {chunks chunkSize : ℕ} (positions : Fin chunks → Fin chunkSize)
    (p : Fin chunks × Fin chunkSize) :
    p ∈ regularSupport positions ↔ p.2 = positions p.1 := by
  rw [regularSupport, boolSupport, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  exact regularWord_eq_true_iff

@[simp]
theorem card_regularSupport {chunks chunkSize : ℕ}
    (positions : Fin chunks → Fin chunkSize) :
    (regularSupport positions).card = chunks := by
  rw [regularSupport, card_boolSupport, hammingNorm_regularWord]

/-- A regular support as a fixed-cardinality combination. -/
def regularCombination {chunks chunkSize : ℕ} (positions : Fin chunks → Fin chunkSize) :
    Set.powersetCard (Fin chunks × Fin chunkSize) chunks :=
  ⟨regularSupport positions, card_regularSupport positions⟩

private theorem regularCombination_injective {chunks chunkSize : ℕ} :
    Function.Injective (regularCombination :
      (Fin chunks → Fin chunkSize) → Set.powersetCard (Fin chunks × Fin chunkSize) chunks) := by
  intro positions positions' h
  have hsupport : regularSupport positions = regularSupport positions' := congrArg Subtype.val h
  have hword : regularWord positions = regularWord positions' :=
    boolSupport_injective hsupport
  funext i
  have hvalue := congrFun hword (i, positions i)
  have htrue : regularWord positions' (i, positions i) = true := by
    calc
      regularWord positions' (i, positions i) = regularWord positions (i, positions i) :=
        hvalue.symm
      _ = true := regularWord_eq_true_iff.mpr rfl
  exact regularWord_eq_true_iff.mp htrue

/-- All fixed-cardinality supports containing exactly one coordinate from every chunk. -/
def regularCombinations (chunks chunkSize : ℕ) :
    Finset (Set.powersetCard (Fin chunks × Fin chunkSize) chunks) :=
  Finset.univ.map ⟨regularCombination, regularCombination_injective⟩

@[simp]
theorem card_regularCombinations (chunks chunkSize : ℕ) :
    (regularCombinations chunks chunkSize).card = chunkSize ^ chunks := by
  simp [regularCombinations, Fintype.card_fun]

/-- Regard the support of a word of weight `chunks` as a fixed-cardinality combination. -/
def supportCombination {chunks chunkSize : ℕ} (x : Fin chunks × Fin chunkSize → Bool)
    (hx : hammingNorm x = chunks) :
    Set.powersetCard (Fin chunks × Fin chunkSize) chunks :=
  ⟨boolSupport x, by
    show (boolSupport x).card = chunks
    rw [card_boolSupport, hx]⟩

/-- Membership among regular combinations is exactly the existing regular-word predicate. -/
theorem supportCombination_mem_regularCombinations_iff {chunks chunkSize : ℕ}
    (x : Fin chunks × Fin chunkSize → Bool) (hx : hammingNorm x = chunks) :
    supportCombination x hx ∈ regularCombinations chunks chunkSize ↔ IsRegularWord x := by
  constructor
  · intro h
    rw [regularCombinations, Finset.mem_map] at h
    obtain ⟨positions, _, hpositions⟩ := h
    have hsupport : boolSupport x = regularSupport positions :=
      congrArg Subtype.val hpositions.symm
    have hword : x = regularWord positions := boolSupport_injective hsupport
    rw [hword]
    exact isRegular_regularWord positions
  · intro hxRegular
    rw [isRegularWord_iff_exists_positions] at hxRegular
    obtain ⟨positions, rfl⟩ := hxRegular
    rw [regularCombinations, Finset.mem_map]
    exact ⟨positions, Finset.mem_univ _, by apply Subtype.ext; rfl⟩

private theorem card_filter_smul_mem_mul_card {G X : Type*} [Group G] [Fintype G]
    [Fintype X] [MulAction G X] [MulAction.IsPretransitive G X]
    (x : X) (T : Finset X) :
    (Finset.univ.filter fun g : G => g • x ∈ T).card * Fintype.card X =
      T.card * Fintype.card G := by
  classical
  let fiber : X → Finset G := fun y => Finset.univ.filter fun g => g • x = y
  have hfiber : ∀ y : X, (fiber y).card = (fiber x).card := by
    intro y
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
    refine Finset.card_nbij' (fun h => g * h) (fun h => g⁻¹ * h) ?_ ?_ ?_ ?_
    · intro h hh
      simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
      rw [mul_smul, hh, hg]
    · intro h hh
      simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
      rw [mul_smul, hh, ← hg, inv_smul_smul]
    · intro h _
      simp
    · intro h _
      simp
  have hdisjoint : (Finset.univ : Set X).PairwiseDisjoint fiber := by
    intro y _ z _ hyz
    refine Finset.disjoint_left.2 fun g hgy hgz => ?_
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hgy hgz
    exact hyz (hgy.symm.trans hgz)
  have hcover : (Finset.univ : Finset G) = Finset.univ.biUnion fiber := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_biUnion, true_iff]
    exact ⟨g • x, Finset.mem_univ _, by simp [fiber]⟩
  have hevent : (Finset.univ.filter fun g : G => g • x ∈ T) = T.biUnion fiber := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro hg
      exact ⟨g • x, hg, by simp [fiber]⟩
    · rintro ⟨y, hyT, hgy⟩
      simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hgy
      simpa [hgy] using hyT
  have heventCard : (Finset.univ.filter fun g : G => g • x ∈ T).card =
      T.card * (fiber x).card := by
    rw [hevent, Finset.card_biUnion (hdisjoint.mono Finset.subset_univ)]
    simp_rw [hfiber]
    rw [Finset.sum_const, nsmul_eq_mul]
  have htotalCard : Fintype.card G = Fintype.card X * (fiber x).card := by
    rw [← Finset.card_univ, hcover, Finset.card_biUnion hdisjoint]
    simp_rw [hfiber]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [heventCard, htotalCard]
  ac_rfl

private theorem dens_filter_smul_mem {G X : Type*} [Group G] [Fintype G]
    [Fintype X] [MulAction G X] [MulAction.IsPretransitive G X]
    (x : X) (T : Finset X) :
    Finset.dens (Finset.univ.filter fun g : G => g • x ∈ T) = Finset.dens T := by
  classical
  rw [Finset.dens_eq_card_div_card, Finset.dens_eq_card_div_card]
  apply (div_eq_div_iff (by exact_mod_cast Fintype.card_ne_zero)
    (by exact_mod_cast Fintype.card_ne_zero)).2
  exact_mod_cast card_filter_smul_mem_mul_card x T

/-- A uniform coordinate permutation sends any fixed `chunks`-element support to a regular
support with exact probability `chunkSize ^ chunks / choose (chunks * chunkSize) chunks`. -/
theorem dens_permute_mem_regularCombinations {chunks chunkSize : ℕ}
    (support : Set.powersetCard (Fin chunks × Fin chunkSize) chunks) :
    Finset.dens {sigma : Equiv.Perm (Fin chunks × Fin chunkSize) |
      sigma • support ∈ regularCombinations chunks chunkSize} =
      (chunkSize ^ chunks : ℚ≥0) / Nat.choose (chunks * chunkSize) chunks := by
  rw [dens_filter_smul_mem support (regularCombinations chunks chunkSize),
    Finset.dens_eq_card_div_card, card_regularCombinations]
  congr 1
  rw [← Nat.card_eq_fintype_card, Set.powersetCard.card, Nat.card_prod]
  simp

/-- Permuting a word permutes its support by the same action. -/
theorem supportCombination_permuteWord {chunks chunkSize : ℕ}
    (sigma : Equiv.Perm (Fin chunks × Fin chunkSize))
    (x : Fin chunks × Fin chunkSize → Bool) (hx : hammingNorm x = chunks) :
    supportCombination (permuteWord sigma x) ((hammingNorm_permuteWord sigma x).trans hx) =
      sigma • supportCombination x hx := by
  apply Subtype.ext
  ext p
  change x (sigma.symm p) = true ↔ p ∈ sigma • boolSupport x
  rw [Finset.mem_smul_finset]
  constructor
  · intro hp
    exact ⟨sigma.symm p, by simpa [boolSupport] using hp, by simp⟩
  · rintro ⟨q, hq, hqp⟩
    have hqeq : q = sigma.symm p := by
      rw [← hqp]
      simp
    rw [← hqeq]
    simpa [boolSupport] using hq

/-- Exact source regularization factor for a fixed binary word of weight `chunks` under a
uniform coordinate permutation. -/
theorem dens_permuteWord_isRegular {chunks chunkSize : ℕ}
    (x : Fin chunks × Fin chunkSize → Bool) (hx : hammingNorm x = chunks) :
    Finset.dens {sigma : Equiv.Perm (Fin chunks × Fin chunkSize) |
      IsRegularWord (permuteWord sigma x)} =
      (chunkSize ^ chunks : ℚ≥0) / Nat.choose (chunks * chunkSize) chunks := by
  rw [← dens_permute_mem_regularCombinations (supportCombination x hx)]
  congr 1
  ext sigma
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rw [← supportCombination_permuteWord sigma x hx,
    supportCombination_mem_regularCombinations_iff]

end Cslib.Code
