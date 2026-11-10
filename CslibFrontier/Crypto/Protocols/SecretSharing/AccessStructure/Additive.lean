/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.Basic
public import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.Privacy
public import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.Designs
public import CslibFrontier.Probability.Uniform
import Mathlib.Algebra.BigOperators.Fin

/-!
# Additive All-of-n Secret Sharing as an Access-Structure Instance

This module instantiates `Cslib.Crypto.Protocols.SecretSharing.AccessScheme` for `(m + 1)`-out-of-
`(m + 1)` additive secret sharing over an arbitrary `AddCommGroup G` ([KatzLindell2020]):

- `additiveShare`: assigns `r i` to party `i < m` and `secret - ∑ i, r i` to party `m`.
- `additiveAccessScheme`: perfectly correct and private for the class `additiveSources` of all
  translation-invariant pad distributions on `Fin m → G`.
- `additiveUniformAccessScheme`: uniform finite-group instance, with `additiveUniform_viewDist_eq`
  proving uniform marginal views on every proper coalition.
- `additiveAuxSources`, `additiveAuxAccessScheme`: finite/general imperfect-source instances
  with auxiliary key material `(Fin m → G) × Aux` whose pad marginal is translation-invariant
  while the auxiliary component may be skewed, deterministic, or correlated.
- `additiveToTwoTwo`: `(m + 1, m + 1) → (2, 2)` composition for `1 ≤ m` via
  `ThresholdDesign.toTwoTwo` ([ACOR22]).

## Main definitions

* `Cslib.Crypto.Protocols.SecretSharing.additiveAccessStructure`: `(m + 1)`-threshold access
  structure on `Fin (m + 1)`.
* `Cslib.Crypto.Protocols.SecretSharing.additiveShare`,
  `Cslib.Crypto.Protocols.SecretSharing.additiveReconstruct`: additive sharing and reconstruction.
* `Cslib.Crypto.Protocols.SecretSharing.additiveSources`,
  `Cslib.Crypto.Protocols.SecretSharing.additiveAccessScheme`,
  `Cslib.Crypto.Protocols.SecretSharing.additiveUniformAccessScheme`: additive `AccessScheme`
  instances.
* `Cslib.Crypto.Protocols.SecretSharing.additiveAuxSources`,
  `Cslib.Crypto.Protocols.SecretSharing.additiveAuxAccessScheme`: auxiliary-key imperfect-source
  additive instances.
* `Cslib.Crypto.Protocols.SecretSharing.additiveToTwoTwo`: `(2, 2)` scheme via ACOR22 design
  composition from `(m + 1)`-out-of-`(m + 1)` sharing (`1 ≤ m`).

## Main results

* `Cslib.Crypto.Protocols.SecretSharing.additiveUniform_viewDist_eq`: every proper coalition has a
  uniform marginal share distribution under uniform additive pads.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020].
* [D. Aggarwal, E. Chung, M. Obremski, J. Ribeiro, *On Secret Sharing, Randomness, and
  Random-less Reductions for Secret Sharing*][ACOR22].
-/

public section

namespace Cslib.Crypto.Protocols.SecretSharing

open Cslib.Probability Cslib.Probability.PMF

section AdditiveInstance

/-- The `(m + 1)`-out-of-`(m + 1)` threshold access structure on `Fin (m + 1)`. -/
@[expose] def additiveAccessStructure (m : ℕ) : AccessStructure (Fin (m + 1)) :=
  AccessStructure.threshold (Fin (m + 1)) (m + 1)

@[simp]
theorem additiveAccessStructure_authorized_iff (m : ℕ) (s : Finset (Fin (m + 1))) :
    (additiveAccessStructure m).authorized s ↔ s = Finset.univ := by
  simp only [additiveAccessStructure, AccessStructure.threshold_authorized_iff]
  constructor
  · intro h
    have hle := s.card_le_univ
    rw [Fintype.card_fin] at hle
    exact Finset.eq_univ_of_card s (by rw [Fintype.card_fin]; exact le_antisymm hle h)
  · intro h
    subst h
    simp

/-- Additive secret sharing of `secret : G` among `m + 1` parties using `m` pads `r : Fin m → G`.
-/
@[expose] def additiveShare {m : ℕ} {G : Type*} [AddCommGroup G]
    (r : Fin m → G) (secret : G) (j : Fin (m + 1)) : G :=
  Fin.snoc (α := fun _ => G) r (secret - ∑ i : Fin m, r i) j

/-- Reconstruction for `(m + 1)`-out-of-`(m + 1)` additive sharing sums all parties' shares when
all `m + 1` parties are present. -/
@[expose] def additiveReconstruct {m : ℕ} {G : Type*} [AddCommGroup G]
    (s : Finset (Fin (m + 1))) (v : (j : s) → G) : G :=
  open scoped Classical in
  if hs : ∀ j : Fin (m + 1), j ∈ s then ∑ j : Fin (m + 1), v ⟨j, hs j⟩ else 0

theorem additiveReconstruct_share {m : ℕ} {G : Type*} [AddCommGroup G]
    (r : Fin m → G) (secret : G) {s : Finset (Fin (m + 1))}
    (hs : (additiveAccessStructure m).authorized s) :
    additiveReconstruct s (fun j => additiveShare r secret j.1) = secret := by
  classical
  have huniv : s = Finset.univ := (additiveAccessStructure_authorized_iff m s).mp hs
  have hall : ∀ j : Fin (m + 1), j ∈ s := fun j => huniv ▸ Finset.mem_univ j
  simp only [additiveReconstruct, additiveShare]
  split_ifs
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, add_sub_cancel]

private theorem exists_not_mem_of_ne_univ {α : Type*} [Fintype α] {s : Finset α}
    (h : s ≠ Finset.univ) : ∃ x : α, x ∉ s :=
  not_forall.mp (mt Finset.eq_univ_iff_forall.mpr h)

/-- The class of translation-invariant distributions on `Fin m → G`. -/
@[expose] def additiveSources (m : ℕ) (G : Type*) [AddCommGroup G] :
    SourceClass (Fin m → G) :=
  { P | ∀ δ : Fin m → G, P.map (· + δ) = P }

theorem uniformOfFintype_mem_additiveSources (m : ℕ) (G : Type*)
    [AddCommGroup G] [Fintype G] [Nonempty G] :
    uniformOfFintype (Fin m → G) ∈ additiveSources m G := fun δ => by
  simpa using uniformOfFintype_map_equiv (Equiv.addRight δ)

private theorem additiveView_eq_of_not_authorized {m : ℕ} {G : Type*} [AddCommGroup G]
    {P : PMF (Fin m → G)} (hP : ∀ δ, P.map (· + δ) = P)
    {s : Finset (Fin (m + 1))} (hs : ¬ (additiveAccessStructure m).authorized s)
    (m₀ m₁ : G) :
    AccessStructure.viewDistOf P additiveShare s m₀ =
      AccessStructure.viewDistOf P additiveShare s m₁ := by
  have hne : s ≠ Finset.univ := mt (additiveAccessStructure_authorized_iff m s).mpr hs
  obtain ⟨j₀, hj₀⟩ := exists_not_mem_of_ne_univ hne
  induction j₀ using Fin.lastCases with
  | last =>
    have hfun : (fun r (j : s) => additiveShare r m₀ j.1) =
        fun r (j : s) => additiveShare r m₁ j.1 := by
      ext r j
      have hj_ne : j.1 ≠ Fin.last m := fun h => hj₀ (h ▸ j.2)
      obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.mpr hj_ne
      simp only [additiveShare, ← hi, Fin.snoc_castSucc]
    simp only [AccessStructure.viewDistOf, hfun]
  | cast i₀ =>
    let δ : Fin m → G := Pi.single i₀ (m₁ - m₀)
    have hshift : ∀ r, (fun j : s => additiveShare r m₀ j.1) =
        fun j : s => additiveShare (r + δ) m₁ j.1 := by
      intro r
      ext j
      induction j using Subtype.rec with | mk j hj =>
      induction j using Fin.lastCases with
      | last =>
        simp only [additiveShare, Fin.snoc_last, Pi.add_apply]
        have hsum : ∑ i : Fin m, (r i + δ i) = (∑ i : Fin m, r i) + (m₁ - m₀) := by
          rw [Finset.sum_add_distrib]
          simp [δ]
        rw [hsum]
        abel
      | cast i =>
        have hi : i ≠ i₀ := fun h => hj₀ (h ▸ hj)
        simp only [additiveShare, Fin.snoc_castSucc, Pi.add_apply, δ,
          Pi.single_eq_of_ne hi, add_zero]
    have hcongr :
        AccessStructure.viewDistOf P additiveShare s m₀ =
          AccessStructure.viewDistOf (P.map (· + δ)) additiveShare s m₁ := by
      simp only [AccessStructure.viewDistOf, PMF.map_comp]
      congr 1
      funext r
      exact hshift r
    rw [hcongr, hP δ]

/-- `(m + 1)`-out-of-`(m + 1)` additive secret sharing over translation-invariant key sources. -/
@[expose] noncomputable def additiveAccessScheme (m : ℕ) (G : Type*) [AddCommGroup G] :
    AccessScheme G (Fin m → G) (Fin (m + 1)) (fun _ => G) where
  access := additiveAccessStructure m
  sources := additiveSources m G
  share := additiveShare
  reconstruct := additiveReconstruct
  correct r secret _ hs := by exact additiveReconstruct_share r secret hs
  view_indist _ hP _ hs := by exact additiveView_eq_of_not_authorized hP hs

@[simp]
theorem additiveAccessScheme_access (m : ℕ) (G : Type*) [AddCommGroup G] :
    (additiveAccessScheme m G).access = additiveAccessStructure m :=
  rfl

/-- Canonical finite-group `(m + 1)`-out-of-`(m + 1)` additive secret sharing with uniform pads. -/
@[expose] noncomputable def additiveUniformAccessScheme (m : ℕ) (G : Type*)
    [AddCommGroup G] [Fintype G] [Nonempty G] :
    AccessScheme G (Fin m → G) (Fin (m + 1)) (fun _ => G) :=
  (additiveAccessScheme m G).monoSources
    (Set.singleton_subset_iff.mpr (uniformOfFintype_mem_additiveSources m G))

@[simp]
theorem additiveUniformAccessScheme_access (m : ℕ) (G : Type*)
    [AddCommGroup G] [Fintype G] [Nonempty G] :
    (additiveUniformAccessScheme m G).access = additiveAccessStructure m :=
  rfl

private noncomputable def additiveZeroRestrictHom {m : ℕ} {G : Type*} [AddCommGroup G]
    (s : Finset (Fin (m + 1))) : (Fin m → G) →+ (s → G) where
  toFun r j := additiveShare r 0 j.1
  map_zero' := by
    ext j
    induction j using Subtype.rec with | mk j _ =>
    induction j using Fin.lastCases with
    | last => simp [additiveShare]
    | cast i => simp [additiveShare]
  map_add' r₁ r₂ := by
    ext j
    induction j using Subtype.rec with | mk j _ =>
    induction j using Fin.lastCases with
    | last =>
      simp only [additiveShare, Fin.snoc_last, Pi.add_apply, Finset.sum_add_distrib, zero_sub]
      abel
    | cast i => simp [additiveShare]

private theorem additiveZeroRestrictHom_surjective {m : ℕ} {G : Type*} [AddCommGroup G]
    {s : Finset (Fin (m + 1))} (hs : ¬ (additiveAccessStructure m).authorized s) :
    Function.Surjective (additiveZeroRestrictHom s (G := G)) := by
  classical
  intro σ
  have hne : s ≠ Finset.univ := mt (additiveAccessStructure_authorized_iff m s).mpr hs
  obtain ⟨j₀, hj₀⟩ := exists_not_mem_of_ne_univ hne
  let full : Fin (m + 1) → G := fun j =>
    if hj : j ∈ s then σ ⟨j, hj⟩
    else if j = j₀ then -∑ x : s, σ x else 0
  have hsum : ∑ j : Fin (m + 1), full j = 0 := by
    have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin (m + 1))) full
      (Finset.mem_univ j₀)
    have hj₀_val : full j₀ = -∑ x : s, σ x := by simp [full, hj₀]
    have herase : ∑ j ∈ Finset.univ.erase j₀, full j = ∑ x : s, σ x := by
      have hsub : s ⊆ Finset.univ.erase j₀ := by
        intro j hj
        exact Finset.mem_erase.mpr ⟨fun h => hj₀ (h ▸ hj), Finset.mem_univ j⟩
      rw [← Finset.sum_subset hsub]
      · rw [← Finset.sum_coe_sort s]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [full, j.2]
      · intro j _ hjs
        have hjn : j ≠ j₀ := by
          intro h
          subst h
          exact False.elim (by simp_all)
        simp [full, hjs, hjn]
    rw [← hsplit, hj₀_val, herase, neg_add_cancel]
  refine ⟨fun i => full i.castSucc, ?_⟩
  ext j
  induction j using Subtype.rec with | mk j hj =>
  induction j using Fin.lastCases with
  | last =>
    have hlast : full (Fin.last m) = -∑ i : Fin m, full i.castSucc := by
      have hsum' := hsum
      rw [Fin.sum_univ_castSucc] at hsum'
      exact eq_neg_of_add_eq_zero_right hsum'
    simp only [additiveZeroRestrictHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, additiveShare,
      Fin.snoc_last, zero_sub, ← hlast]
    simp [full, hj]
  | cast i =>
    simp [additiveZeroRestrictHom, additiveShare, full, hj]

/-- Under uniform additive pads, every proper coalition's view distribution is uniform on `s → G`.
-/
theorem additiveUniform_viewDist_eq (m : ℕ) (G : Type*)
    [AddCommGroup G] [Fintype G] [Nonempty G]
    {s : Finset (Fin (m + 1))} (hs : ¬ (additiveAccessStructure m).authorized s)
    (secret : G) :
    (additiveUniformAccessScheme m G).viewDist (uniformOfFintype (Fin m → G)) s secret =
      uniformOfFintype (s → G) := by
  have hshift :
      (fun r (j : s) => additiveShare r secret j.1) =
        (Equiv.addLeft (fun j : s => if j.1 = Fin.last m then secret else 0)) ∘
          additiveZeroRestrictHom s := by
    ext r j
    induction j using Subtype.rec with | mk j hj =>
    induction j using Fin.lastCases with
    | last =>
      simp only [Function.comp_apply, Equiv.coe_addLeft, Pi.add_apply, additiveZeroRestrictHom,
        AddMonoidHom.coe_mk, ZeroHom.coe_mk, additiveShare, Fin.snoc_last, ↓reduceIte, zero_sub]
      abel
    | cast i =>
      simp only [Function.comp_apply, Equiv.coe_addLeft, Pi.add_apply, additiveZeroRestrictHom,
        AddMonoidHom.coe_mk, ZeroHom.coe_mk, additiveShare, Fin.snoc_castSucc,
        Fin.castSucc_ne_last, ↓reduceIte, zero_add]
  change (uniformOfFintype (Fin m → G)).map (fun r (j : s) => additiveShare r secret j.1) =
    uniformOfFintype (s → G)
  have hhom := uniformOfFintype_map_addHom
    (additiveZeroRestrictHom s (G := G)) (additiveZeroRestrictHom_surjective hs)
  rw [hshift, ← PMF.map_comp, hhom, uniformOfFintype_map_equiv]

/-- Auxiliary-extended imperfect key sources for additive `(m + 1)`-out-of-`(m + 1)` sharing:
`(r, aux)` with translation-invariant `r`-marginal and arbitrary `aux` distribution. -/
@[expose] noncomputable def additiveAuxSources (m : ℕ) (G Aux : Type*) [AddCommGroup G] :
    SourceClass ((Fin m → G) × Aux) :=
  { P | P.map Prod.fst ∈ additiveSources m G }

/-- Additive `(m + 1)`-out-of-`(m + 1)` secret sharing over auxiliary-extended imperfect key
sources `(Fin m → G) × Aux`. -/
@[expose] noncomputable def additiveAuxAccessScheme (m : ℕ) (G Aux : Type*) [AddCommGroup G] :
    AccessScheme G ((Fin m → G) × Aux) (Fin (m + 1)) (fun _ => G) :=
  (additiveAccessScheme m G).comapKey Prod.fst (additiveAuxSources m G Aux) (fun _ hP => hP)

@[simp]
theorem additiveAuxAccessScheme_access (m : ℕ) (G Aux : Type*) [AddCommGroup G] :
    (additiveAuxAccessScheme m G Aux).access = additiveAccessStructure m :=
  rfl

/-- ACOR22 `(m + 1, m + 1) → (2, 2)` distribution-design reduction applied to additive sharing
for `1 ≤ m`. -/
@[expose] noncomputable def additiveToTwoTwo (m : ℕ) (G : Type*) [AddCommGroup G]
    (hm : 1 ≤ m) :=
  (additiveAccessScheme m G).toTwoTwoFin (rfl : (additiveAccessScheme m G).access =
    AccessStructure.threshold (Fin (m + 1)) (m + 1))
    (by omega) le_rfl

@[simp]
theorem additiveToTwoTwo_access (m : ℕ) (G : Type*) [AddCommGroup G] (hm : 1 ≤ m) :
    (additiveToTwoTwo m G hm).access = AccessStructure.threshold (Fin 2) 2 :=
  rfl

end AdditiveInstance

end Cslib.Crypto.Protocols.SecretSharing
