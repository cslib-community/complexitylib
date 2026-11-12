/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.Additive
import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.Basic
import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.Designs
import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.Privacy
import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.Shamir
import CslibFrontier.Probability.PMF.Coin
import Mathlib.Algebra.Field.ZMod

/-!
# Tests for General Access-Structure Secret Sharing and Distribution Designs

Concrete, non-vacuous checks exercising:
1. Monotone access structures (`AccessStructure`), duals, `IsNontrivial`, `inter`, `union`,
   minimal coalitions, and a non-monotone counterexample.
2. Shamir `(2, 3)` and `(3, 4)` instances over `ZMod 5` (`shamirUniformAccessScheme`,
   `shamirPaddedAccessScheme`), including concrete reconstruction, `PerfectlyCorrect`, `shareDist`,
   `SourceClass.map`/`flat`, `restrictSecret`, `mapShare`, `relabelParty`, uniform unauthorized
   views, vanishing mutual information, posterior privacy, zero conditional entropy on authorized
   sets, and upstream `Cslib.Crypto.Protocols.SecretSharing.Scheme` bridges.
3. Distribution-design composition (`ThresholdDesign.toTwoTwo`, `shamirToTwoTwo`,
   `DistributionDesign.comp`) from `(2, 3)` and `(3, 4)` Shamir schemes to `(2, 2)`, plus
   non-existence of `(2, 3, 2, 2)`, `(3, 3, 2, 2)`, `(4, 4, 2, 2)`, and `(3, 5, 2, 2)` designs.
4. Additive `3`-out-of-`3` secret sharing over `ZMod 4`, a finite `ZMod 3` `2`-out-of-`2`
   source-dependent scheme (`taggedPadScheme`) whose unauthorized marginal views genuinely vary
   with the chosen source `q`, `δ`-statistical privacy under design composition, and a leaky
   counterexample with positive mutual information.
-/

namespace CslibFrontierTests.SecretSharingAccessStructure

open Cslib.Probability Cslib.Probability.PMF
open Cslib.Crypto.Protocols.SecretSharing
open Cslib.Crypto.Protocols.SecretSharing.Shamir

instance : Fact (Nat.Prime 5) := ⟨by decide⟩
instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-! ### 1. Monotone access structures and non-monotone counterexample -/

def graphAccess3 : AccessStructure (Fin 3) :=
  AccessStructure.ofSets {{0, 1}, {1, 2}}

example : graphAccess3.authorized {0, 1} := ⟨{0, 1}, by simp, Finset.Subset.rfl⟩
example : graphAccess3.authorized {0, 1, 2} := ⟨{0, 1}, by simp, by decide⟩
example : ¬ graphAccess3.authorized {0, 2} := by
  rintro ⟨b, (rfl | rfl), hsub⟩ <;> revert hsub <;> decide
example : ¬ graphAccess3.authorized {1} := by
  rintro ⟨b, (rfl | rfl), hsub⟩ <;> revert hsub <;> decide

example : graphAccess3.IsMinimalAuthorized {0, 1} := by
  refine ⟨⟨{0, 1}, by simp, Finset.Subset.rfl⟩, fun t ht ⟨b, hb, hbs⟩ => ?_⟩
  rcases hb with rfl | rfl
  · have hlt := Finset.card_lt_card ht
    have hle := Finset.card_le_card hbs
    omega
  · have h2 : (2 : Fin 3) ∈ ({0, 1} : Finset (Fin 3)) := ht.1 (hbs (by decide))
    revert h2; decide

example : ¬ graphAccess3.IsMinimalAuthorized {0, 1, 2} := by
  intro ⟨_, hmin⟩
  exact hmin {0, 1} (by decide) ⟨{0, 1}, by simp, Finset.Subset.rfl⟩

example : (AccessStructure.threshold (Fin 3) 2).dual = AccessStructure.threshold (Fin 3) 2 := by
  ext s
  rw [AccessStructure.dual_authorized_iff, AccessStructure.threshold_authorized_iff,
    AccessStructure.threshold_authorized_iff, Finset.card_sdiff_of_subset (Finset.subset_univ s),
    Finset.card_univ, Fintype.card_fin]
  omega

example : (AccessStructure.threshold (Fin 4) 2).dual = AccessStructure.threshold (Fin 4) 3 := by
  ext s
  rw [AccessStructure.dual_authorized_iff, AccessStructure.threshold_authorized_iff,
    AccessStructure.threshold_authorized_iff, Finset.card_sdiff_of_subset (Finset.subset_univ s),
    Finset.card_univ, Fintype.card_fin]
  omega

example : ¬ Monotone (fun s : Finset (Fin 3) => s.card = 2) := by
  intro hm
  have h12 : ({0, 1} : Finset (Fin 3)) ⊆ {0, 1, 2} := by decide
  have h : ({0, 1, 2} : Finset (Fin 3)).card = 2 := hm h12 (by decide)
  revert h; decide

example : graphAccess3.IsNontrivial := by
  refine ⟨?_, ⟨{0, 1}, by simp, by decide⟩⟩
  rintro ⟨b, (rfl | rfl), hsub⟩ <;> revert hsub <;> decide

example :
    ((AccessStructure.threshold (Fin 3) 2).inter (AccessStructure.ofSets {{0, 1}})).authorized
      {0, 1, 2} :=
  ⟨by decide, ⟨{0, 1}, by simp, by decide⟩⟩

example :
    ¬ ((AccessStructure.threshold (Fin 3) 2).inter (AccessStructure.ofSets {{0, 1}})).authorized
      {0, 2} := by
  rintro ⟨_, b, hb, hsub⟩
  rw [Set.mem_singleton_iff.mp hb] at hsub
  revert hsub; decide

example :
    ((AccessStructure.threshold (Fin 3) 2).union (AccessStructure.ofSets {{2}})).authorized
      {2} :=
  Or.inr ⟨{2}, by simp, Finset.Subset.rfl⟩

example :
    ¬ ((AccessStructure.threshold (Fin 3) 2).union (AccessStructure.ofSets {{2}})).authorized
      {0} := by
  rintro (h | ⟨b, hb, hsub⟩)
  · revert h; decide
  · rw [Set.mem_singleton_iff.mp hb] at hsub
    revert hsub; decide

/-! ### 2. Shamir instances, mutual information, and upstream bridges -/

def params3 : Params (ZMod 5) (Fin 3) where
  threshold := 1
  threshold_lt_card := by decide
  point i := (i.val + 1 : ZMod 5)
  point_injective := by decide
  point_nonzero := by decide

def params4 : Params (ZMod 5) (Fin 4) where
  threshold := 2
  threshold_lt_card := by decide
  point i := (i.val + 1 : ZMod 5)
  point_injective := by decide
  point_nonzero := by decide

def r3 : Randomness params3 := ![2]
def r4 : Randomness params4 := ![1, 3]

noncomputable def priorZMod5 : PMF (ZMod 5) :=
  (coin ⟨1 / 4, by norm_num⟩).map fun b => if b then (1 : ZMod 5) else 0

example :
    (shamirUniformAccessScheme params3).reconstruct {0, 1}
      ((shamirUniformAccessScheme params3).view {0, 1} r3 3) = (3 : ZMod 5) :=
  (shamirUniformAccessScheme params3).reconstruct_view_eq_secret r3 3 (by
    simp only [shamirUniformAccessScheme_access, shamirAccessStructure,
      AccessStructure.threshold_authorized_iff]
    decide)

example :
    (shamirUniformAccessScheme params3).viewDist
        (uniformOfFintype (Randomness params3)) {0} 3 =
      uniformOfFintype (({0} : Finset (Fin 3)) → ZMod 5) :=
  shamirUniform_viewDist_eq params3 (by
    simp only [shamirUniformAccessScheme_access, shamirAccessStructure,
      AccessStructure.threshold_authorized_iff]
    decide) 3

example :
    mutualInfo (jointSecretView (uniformOfFintype (Randomness params3))
      (shamirUniformAccessScheme params3).share {0} priorZMod5) = 0 :=
  shamirUniform_mutualInfo_eq_zero params3 (by
    simp only [shamirUniformAccessScheme_access, shamirAccessStructure,
      AccessStructure.threshold_authorized_iff]
    decide) priorZMod5

example :
    conditionalEntropy ((jointSecretView (uniformOfFintype (Randomness params3))
      (shamirUniformAccessScheme params3).share {0, 1} priorZMod5).map Prod.swap) = 0 :=
  (shamirUniformAccessScheme params3).conditionalEntropy_secret_given_view_eq_zero _ (by
    simp only [shamirUniformAccessScheme_access, shamirAccessStructure,
      AccessStructure.threshold_authorized_iff]
    decide) priorZMod5

example :
    mutualInfo (jointSecretView (uniformOfFintype (Randomness params3))
      (shamirUniformAccessScheme params3).share {0, 1} priorZMod5) =
      entropy priorZMod5 :=
  (shamirUniformAccessScheme params3).mutualInfo_authorized_eq_entropy _ (by
    simp only [shamirUniformAccessScheme_access, shamirAccessStructure,
      AccessStructure.threshold_authorized_iff]
    decide) priorZMod5

example (v : (({0} : Finset (Fin 3)) → ZMod 5))
    (hv : v ∈ (priorZMod5.bind ((shamirUniformAccessScheme params3).viewDist
      (uniformOfFintype (Randomness params3)) {0})).support) :
    (shamirUniformAccessScheme params3).posteriorSecretDist
      (uniformOfFintype (Randomness params3)) {0} priorZMod5 v hv = priorZMod5 :=
  (shamirUniformAccessScheme params3).perfectlyPrivate _ (Set.mem_singleton _) {0} (by
    simp only [shamirUniformAccessScheme_access, shamirAccessStructure,
      AccessStructure.threshold_authorized_iff]
    decide) priorZMod5 v hv

example :
    ((AccessScheme.ofCslibScheme (Shamir.scheme params3)).toCslibScheme
      (Set.mem_singleton _)).gen = uniformOfFintype (Randomness params3) :=
  rfl

example :
    PerfectlyCorrect (shamirUniformAccessScheme params3).access
      (shamirUniformAccessScheme params3).share
      (shamirUniformAccessScheme params3).reconstruct :=
  (shamirUniformAccessScheme params3).perfectlyCorrect

example :
    ((shamirUniformAccessScheme params3).shareDist
      (uniformOfFintype (Randomness params3)) 3).map (fun v (i : ({0} : Finset (Fin 3))) =>
        v i.1) = uniformOfFintype (({0} : Finset (Fin 3)) → ZMod 5) := by
  rw [AccessScheme.shareDist, PMF.map_comp]
  exact shamirUniform_viewDist_eq params3 (by
    simp only [shamirUniformAccessScheme_access, shamirAccessStructure,
      AccessStructure.threshold_authorized_iff]
    decide) 3

example :
    uniformOfFintype (Randomness params3) ∈ SourceClass.flat (Randomness params3) :=
  ⟨Finset.univ, Finset.univ_nonempty, by
    ext x
    simp [uniformOfFintype_apply, uniformOfFinset_apply]⟩

noncomputable def shamirBoolScheme :=
  (shamirUniformAccessScheme params3).restrictSecret
    (fun b => if b then (1 : ZMod 5) else 0) (fun z => decide (z = 1))
    (fun b => by cases b <;> decide)

example :
    shamirBoolScheme.reconstruct {0, 1} (shamirBoolScheme.view {0, 1} r3 true) = true :=
  shamirBoolScheme.reconstruct_view_eq_secret r3 true (by
    simp only [shamirBoolScheme, AccessScheme.restrictSecret, shamirUniformAccessScheme_access,
      shamirAccessStructure, AccessStructure.threshold_authorized_iff]
    decide)

noncomputable def shamirShiftedShareScheme :=
  (shamirUniformAccessScheme params3).mapShare (fun i => Equiv.addRight (i.val : ZMod 5))

example :
    shamirShiftedShareScheme.reconstruct {0, 1}
      (shamirShiftedShareScheme.view {0, 1} r3 3) = (3 : ZMod 5) :=
  shamirShiftedShareScheme.reconstruct_view_eq_secret r3 3 (by
    simp only [shamirShiftedShareScheme, AccessScheme.mapShare, shamirUniformAccessScheme_access,
      shamirAccessStructure, AccessStructure.threshold_authorized_iff]
    decide)

noncomputable def shamirSwappedPartyScheme :=
  (shamirUniformAccessScheme params3).relabelParty (Equiv.swap (0 : Fin 3) 2)

example :
    shamirSwappedPartyScheme.access.authorized {0, 1} := by
  simp only [shamirSwappedPartyScheme, AccessScheme.relabelParty, shamirUniformAccessScheme_access,
    shamirAccessStructure, AccessStructure.threshold_authorized_iff, Finset.card_map]
  decide

/-! ### 3. Shamir with auxiliary-key padding (unused `Aux` component) -/

noncomputable def paddedSourceFalse : PMF (Randomness params3 × Bool) :=
  (uniformOfFintype (Randomness params3)).map (·, false)

noncomputable def paddedSourceBiased : PMF (Randomness params3 × Bool) :=
  (uniformOfFintype (Randomness params3)).bind fun r =>
    (coin ⟨1 / 4, by norm_num⟩).map (r, ·)

theorem paddedSourceFalse_mem : paddedSourceFalse ∈ shamirPaddedSources params3 Bool := by
  have hfst : paddedSourceFalse.map Prod.fst = uniformOfFintype (Randomness params3) := by
    simp only [paddedSourceFalse, PMF.map_comp]
    exact PMF.map_id _
  change paddedSourceFalse.map Prod.fst ∈ shamirSources params3
  rw [hfst]
  exact uniformOfFintype_mem_shamirSources params3

theorem paddedSourceBiased_mem : paddedSourceBiased ∈ shamirPaddedSources params3 Bool :=
  bind_mem_shamirPaddedSources (uniformOfFintype_mem_shamirSources params3) _

example :
    uniformOfFintype (Randomness params3) ∈
      SourceClass.map Prod.fst (shamirPaddedSources params3 Bool) :=
  ⟨paddedSourceBiased, paddedSourceBiased_mem, by
    simpa only [paddedSourceBiased] using map_fst_bind_pair _ _⟩

theorem paddedSourceFalse_ne_paddedSourceBiased : paddedSourceFalse ≠ paddedSourceBiased := by
  intro h
  have hnot : (r3, true) ∉ paddedSourceFalse.support := by
    simp [paddedSourceFalse, PMF.support_map]
  have hin : (r3, true) ∈ paddedSourceBiased.support := by
    simp only [paddedSourceBiased, PMF.support_bind, Set.mem_iUnion, PMF.support_map,
      Set.mem_image, mem_support_uniformOfFintype]
    have hcoin : true ∈ (coin ⟨1 / 4, by norm_num⟩).support := by
      rw [PMF.mem_support_iff, coin_apply]
      norm_num
    exact ⟨r3, trivial, true, hcoin, rfl⟩
  rw [h] at hnot
  exact hnot hin

example :
    (shamirPaddedAccessScheme params3 Bool).reconstruct {0, 2}
      ((shamirPaddedAccessScheme params3 Bool).view {0, 2} (r3, true) 3) = (3 : ZMod 5) :=
  (shamirPaddedAccessScheme params3 Bool).reconstruct_view_eq_secret (r3, true) 3 (by
    simp only [shamirPaddedAccessScheme_access, shamirAccessStructure,
      AccessStructure.threshold_authorized_iff]
    decide)

example :
    (shamirPaddedAccessScheme params3 Bool).viewDist paddedSourceBiased {2} 1 =
      (shamirPaddedAccessScheme params3 Bool).viewDist paddedSourceBiased {2} 4 :=
  (shamirPaddedAccessScheme params3 Bool).viewDist_eq_of_not_authorized
    paddedSourceBiased_mem (by
      simp only [shamirPaddedAccessScheme_access, shamirAccessStructure,
        AccessStructure.threshold_authorized_iff]
      decide) 1 4

/-! ### 4. ACOR22 distribution-design composition and non-existence -/

noncomputable def shamir3ToTwoTwo := shamirToTwoTwo params3 (by decide)
noncomputable def shamir4ToTwoTwo := shamirToTwoTwo params4 (by decide)

example :
    shamir4ToTwoTwo.reconstruct {0, 1}
      (shamir4ToTwoTwo.view {0, 1} r4 4) = (4 : ZMod 5) :=
  shamir4ToTwoTwo.reconstruct_view_eq_secret r4 4 (by
    simp only [shamir4ToTwoTwo, shamirToTwoTwo_access, AccessStructure.threshold_authorized_iff]
    decide)

example : ¬ shamir4ToTwoTwo.access.authorized {0} := by
  simp only [shamir4ToTwoTwo, shamirToTwoTwo_access, AccessStructure.threshold_authorized_iff]
  decide

example : ¬ shamir4ToTwoTwo.access.authorized {1} := by
  simp only [shamir4ToTwoTwo, shamirToTwoTwo_access, AccessStructure.threshold_authorized_iff]
  decide

example :
    shamir4ToTwoTwo.viewDist (uniformOfFintype (Randomness params4)) {0} 1 =
      shamir4ToTwoTwo.viewDist (uniformOfFintype (Randomness params4)) {0} 4 :=
  shamir4ToTwoTwo.viewDist_eq_of_not_authorized
    (uniformOfFintype_mem_shamirSources params4) (by
      simp only [shamir4ToTwoTwo, shamirToTwoTwo_access, AccessStructure.threshold_authorized_iff]
      decide) 1 4

example :
    mutualInfo (jointSecretView (uniformOfFintype (Randomness params4))
      shamir4ToTwoTwo.share {0} priorZMod5) = 0 :=
  shamir4ToTwoTwo.mutualInfo_view_eq_zero
    (uniformOfFintype_mem_shamirSources params4) (by
      simp only [shamir4ToTwoTwo, shamirToTwoTwo_access, AccessStructure.threshold_authorized_iff]
      decide) priorZMod5

example :
    (DistributionDesign.comp (ThresholdDesign.toTwoTwo (n' := 4) (by decide) (by decide))
      (DistributionDesign.id (AccessStructure.threshold (Fin 4) 3))).assign 0 = {0, 1} := by
  ext i
  fin_cases i <;> decide

example : ¬ Nonempty (ThresholdDesign 2 3 2 2) :=
  not_nonempty_iff.mpr not_exists_design_2_3_2_2

example : ¬ Nonempty (ThresholdDesign 3 3 2 2) :=
  not_nonempty_iff.mpr (not_exists_design_r_r_2_2 (by decide))

example : ¬ Nonempty (ThresholdDesign 4 4 2 2) :=
  not_nonempty_iff.mpr (not_exists_design_r_r_2_2 (by decide))

example : ¬ Nonempty (ThresholdDesign 3 5 2 2) :=
  not_nonempty_iff.mpr (no_thresholdDesign_two_two (by decide) (by decide) (by decide))

/-! ### 5. Additive sharing over `ZMod 4` and non-uniform source-dependent marginals -/

example : (fun j : Fin 3 => additiveShare (![1, 2] : Fin 2 → ZMod 4) 3 j) = ![1, 2, 0] := by
  ext j
  fin_cases j <;> decide

example :
    (additiveUniformAccessScheme 2 (ZMod 4)).reconstruct Finset.univ
      ((additiveUniformAccessScheme 2 (ZMod 4)).view Finset.univ ![1, 2] 3) = (3 : ZMod 4) :=
  (additiveUniformAccessScheme 2 (ZMod 4)).reconstruct_view_eq_secret ![1, 2] 3 (by
    simp only [additiveUniformAccessScheme_access, additiveAccessStructure_authorized_iff])

example :
    (additiveUniformAccessScheme 2 (ZMod 4)).viewDist (uniformOfFintype (Fin 2 → ZMod 4))
        {0, 2} 1 =
      uniformOfFintype (({0, 2} : Finset (Fin 3)) → ZMod 4) :=
  additiveUniform_viewDist_eq 2 (ZMod 4) (by
    simp only [additiveAccessStructure_authorized_iff]
    decide) 1

noncomputable def additive3ToTwoTwo := additiveToTwoTwo 2 (ZMod 4) (by decide)

example :
    additive3ToTwoTwo.reconstruct {0, 1}
      (additive3ToTwoTwo.view {0, 1} ![1, 2] 3) = (3 : ZMod 4) :=
  additive3ToTwoTwo.reconstruct_view_eq_secret ![1, 2] 3 (by
    simp only [additive3ToTwoTwo, additiveToTwoTwo_access,
      AccessStructure.threshold_authorized_iff]
    decide)

/-- A concrete finite 2-out-of-2 source-dependent scheme over `ZMod 3` where party `0`'s
unauthorized view distribution genuinely depends on which source `P ∈ sources` is chosen, while
remaining independent of the secret for every `P ∈ sources`. -/
def taggedPadShare (k : Bool × ZMod 3) (m : ZMod 3) : Fin 2 → ZMod 3 ⊕ ZMod 3
  | 0 => if k.1 then .inr k.2 else .inl k.2
  | 1 => .inl (m - k.2)

def taggedPadReconstruct (s : Finset (Fin 2)) (v : (i : s) → ZMod 3 ⊕ ZMod 3) : ZMod 3 :=
  if hs : (0 : Fin 2) ∈ s ∧ (1 : Fin 2) ∈ s then
    Sum.elim id id (v ⟨0, hs.1⟩) + Sum.elim id id (v ⟨1, hs.2⟩)
  else 0

noncomputable def taggedPadSource (q : PMF Bool) : PMF (Bool × ZMod 3) :=
  q.bind fun b => (uniformOfFintype (ZMod 3)).map (b, ·)

noncomputable def taggedPadScheme :
    AccessScheme (ZMod 3) (Bool × ZMod 3) (Fin 2) (fun _ => ZMod 3 ⊕ ZMod 3) where
  access := AccessStructure.threshold (Fin 2) 2
  sources := { P | ∃ q : PMF Bool, P = taggedPadSource q }
  share := taggedPadShare
  reconstruct := taggedPadReconstruct
  correct k m s hs := by
    have hcard := s.card_le_univ
    rw [Fintype.card_fin] at hcard
    have hs2 : 2 ≤ s.card := by simpa only [AccessStructure.threshold_authorized_iff] using hs
    have hs_univ : s = Finset.univ := Finset.eq_univ_of_card s (by rw [Fintype.card_fin]; omega)
    have h01 : (0 : Fin 2) ∈ s ∧ (1 : Fin 2) ∈ s := by rw [hs_univ]; exact ⟨by simp, by simp⟩
    simp only [taggedPadReconstruct, h01, taggedPadShare]
    cases k.1 <;> simp [add_sub_cancel]
  view_indist P hP s hs m₀ m₁ := by
    obtain ⟨q, rfl⟩ := hP
    have hlt : s.card < 2 := by simpa using hs
    have hsub : s = ∅ ∨ s = {0} ∨ s = {1} := by
      have : s.card = 0 ∨ s.card = 1 := by omega
      rcases this with h0 | h1
      · exact Or.inl (Finset.card_eq_zero.mp h0)
      · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
        fin_cases i
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
    rcases hsub with rfl | rfl | rfl
    · have hfun (m : ZMod 3) :
          (fun k (i : (∅ : Finset (Fin 2))) => taggedPadShare k m i.1) =
            fun _ i => (Finset.notMem_empty i.1 i.2).elim := by
        ext k i; exact (Finset.notMem_empty i.1 i.2).elim
      simp only [AccessStructure.viewDistOf, hfun]
    · have hfun (m : ZMod 3) :
          (fun k (i : ({0} : Finset (Fin 2))) => taggedPadShare k m i.1) =
            fun k _ => if k.1 then .inr k.2 else .inl k.2 := by
        ext k i
        have hi : i.1 = 0 := Finset.mem_singleton.mp i.2
        simp [hi, taggedPadShare]
      simp only [AccessStructure.viewDistOf, hfun]
    · have hfun (m : ZMod 3) :
          AccessStructure.viewDistOf (taggedPadSource q) taggedPadShare {1} m =
            (uniformOfFintype (ZMod 3)).map fun x _ => .inl x := by
        simp only [AccessStructure.viewDistOf, taggedPadSource, PMF.map_bind, PMF.map_comp]
        have hinner : ∀ b : Bool,
            (uniformOfFintype (ZMod 3)).map (fun k (i : ({1} : Finset (Fin 2))) =>
              taggedPadShare (b, k) m i.1) =
              (uniformOfFintype (ZMod 3)).map fun x _ => .inl x := by
          intro b
          have hcomp :
              (fun k (i : ({1} : Finset (Fin 2))) => taggedPadShare (b, k) m i.1) =
                (fun x (_ : ({1} : Finset (Fin 2))) => Sum.inl x) ∘
                  (fun k => m - k) := by
            ext k i
            have hi : i.1 = 1 := Finset.mem_singleton.mp i.2
            simp [hi, taggedPadShare]
          rw [hcomp, ← PMF.map_comp]
          have heq : Equiv.subLeft m = (fun k => m - k) := rfl
          rw [← heq, uniformOfFintype_map_equiv (Equiv.subLeft m)]
        simp_rw [Function.comp_def] at hinner ⊢
        have hbind :
            (q.bind fun b => (uniformOfFintype (ZMod 3)).map
              (fun x (i : ({1} : Finset (Fin 2))) => taggedPadShare (b, x) m i.1)) =
              q.bind fun _ => (uniformOfFintype (ZMod 3)).map fun x _ => .inl x :=
          congrArg q.bind (funext hinner)
        exact hbind.trans (PMF.bind_const q _)
      rw [hfun m₀, hfun m₁]

example :
    taggedPadScheme.viewDist (taggedPadSource (PMF.pure false)) {0} 0 ≠
      taggedPadScheme.viewDist (taggedPadSource (PMF.pure true)) {0} 0 := by
  intro h
  let v : (({0} : Finset (Fin 2)) → ZMod 3 ⊕ ZMod 3) := fun _ => .inl 0
  have hin :
      v ∈ (taggedPadScheme.viewDist (taggedPadSource (PMF.pure false)) {0} 0).support := by
    simp only [AccessScheme.viewDist, AccessStructure.viewDistOf, taggedPadSource, PMF.pure_bind,
      PMF.map_comp, Function.comp_def, PMF.support_map, Set.mem_image,
      mem_support_uniformOfFintype, true_and]
    refine ⟨0, ?_⟩
    ext i
    have hi : i.1 = 0 := Finset.mem_singleton.mp i.2
    simp [v, taggedPadScheme, taggedPadShare, hi]
  have hnot :
      v ∉ (taggedPadScheme.viewDist (taggedPadSource (PMF.pure true)) {0} 0).support := by
    simp only [AccessScheme.viewDist, AccessStructure.viewDistOf, taggedPadSource, PMF.pure_bind,
      PMF.map_comp, Function.comp_def, PMF.support_map, Set.mem_image,
      mem_support_uniformOfFintype, true_and, not_exists]
    intro k hk
    have hk0 := congrFun hk ⟨0, Finset.mem_singleton_self 0⟩
    simp [v, taggedPadScheme, taggedPadShare] at hk0
  rw [h] at hin
  exact hnot hin

/-! ### 6. Statistical `δ`-privacy and leaky negative counterexample -/

example :
    let d := ThresholdDesignOn.toTwoTwo (Fin 3) (t' := 2) (by decide) (by decide)
    StatisticallyPrivate (AccessStructure.threshold (Fin 2) 2)
      (shamirAccessScheme params3).sources
      (fun k secret (i : Fin 2) (j : d.assign i) => (shamirAccessScheme params3).share k secret j.1)
      (1 / 4 : NNReal) :=
  StatisticallyPrivate.composeDesign
    (ThresholdDesignOn.toTwoTwo (Fin 3) (t' := 2) (by decide) (by decide))
    ((shamirAccessScheme params3).statisticallyPrivate (1 / 4 : NNReal))

def leakyShare (k : ZMod 3) (m : ZMod 3) : Fin 2 → ZMod 3
  | 0 => k
  | 1 => m

private theorem leakyView_zero :
    AccessStructure.viewDistOf (uniformOfFintype (ZMod 3)) leakyShare {1} 0
      (fun _ => (0 : ZMod 3)) = 1 := by
  simp only [AccessStructure.viewDistOf, PMF.map_apply]
  rw [tsum_eq_sum (s := Finset.univ)]
  · have hsum : ∀ a : ZMod 3, (fun _ : ({1} : Finset (Fin 2)) => (0 : ZMod 3)) =
        fun i => leakyShare a 0 i.1 := by
      intro a; ext i
      have hi : i.1 = 1 := Finset.mem_singleton.mp i.2
      simp [hi, leakyShare]
    rw [Finset.sum_congr (g := fun a => (uniformOfFintype (ZMod 3)) a) rfl
      fun a _ => by simp only [hsum a, ↓reduceIte]]
    simpa using (uniformOfFintype (ZMod 3)).tsum_coe
  · intro a ha; exact absurd (Finset.mem_univ a) ha

private theorem leakyView_one :
    AccessStructure.viewDistOf (uniformOfFintype (ZMod 3)) leakyShare {1} 1
      (fun _ => (0 : ZMod 3)) = 0 := by
  simp only [AccessStructure.viewDistOf, PMF.map_apply]
  rw [tsum_eq_zero_iff]
  intro a
  have hne : (fun _ : ({1} : Finset (Fin 2)) => (0 : ZMod 3)) ≠
      fun i => leakyShare a 1 i.1 := by
    intro heq
    have := congrFun heq ⟨1, Finset.mem_singleton_self 1⟩
    simp [leakyShare] at this
  simp only [hne, ↓reduceIte]

example :
    ¬ ViewIndist (AccessStructure.threshold (Fin 2) 2)
      {uniformOfFintype (ZMod 3)} leakyShare := by
  intro h
  have h1 := h (uniformOfFintype (ZMod 3)) (Set.mem_singleton _) {1} (by decide) 0 1
  have h0 := congrArg (fun p => p (fun _ => (0 : ZMod 3))) h1
  rw [leakyView_zero, leakyView_one] at h0
  exact one_ne_zero h0

example :
    0 < mutualInfo (jointSecretView (uniformOfFintype (ZMod 3)) leakyShare {1}
      (uniformOfFintype (ZMod 3))) := by
  by_contra hle
  have h0 : mutualInfo (jointSecretView (uniformOfFintype (ZMod 3)) leakyShare {1}
      (uniformOfFintype (ZMod 3))) = 0 :=
    le_antisymm (not_lt.mp hle) (mutualInfo_nonneg _)
  have hind := (mutualInfo_eq_zero_iff _).mp h0
  rw [map_fst_jointSecretView _ leakyShare] at hind
  have h00 := congrArg (fun p => p (0, fun _ => (0 : ZMod 3))) hind
  have h10 := congrArg (fun p => p (1, fun _ => (0 : ZMod 3))) hind
  change ((uniformOfFintype (ZMod 3)).bind fun a =>
      (AccessStructure.viewDistOf (uniformOfFintype (ZMod 3)) leakyShare {1} a).bind fun b =>
        PMF.pure (a, b)) (0, fun _ => (0 : ZMod 3)) =
    ((uniformOfFintype (ZMod 3)).bind fun a =>
      ((jointSecretView (uniformOfFintype (ZMod 3)) leakyShare {1}
        (uniformOfFintype (ZMod 3))).map Prod.snd).bind fun b => PMF.pure (a, b))
      (0, fun _ => (0 : ZMod 3)) at h00
  change ((uniformOfFintype (ZMod 3)).bind fun a =>
      (AccessStructure.viewDistOf (uniformOfFintype (ZMod 3)) leakyShare {1} a).bind fun b =>
        PMF.pure (a, b)) (1, fun _ => (0 : ZMod 3)) =
    ((uniformOfFintype (ZMod 3)).bind fun a =>
      ((jointSecretView (uniformOfFintype (ZMod 3)) leakyShare {1}
        (uniformOfFintype (ZMod 3))).map Prod.snd).bind fun b => PMF.pure (a, b))
      (1, fun _ => (0 : ZMod 3)) at h10
  rw [bind_pair_apply, bind_pair_apply] at h00 h10
  have heq : (uniformOfFintype (ZMod 3) 0) = (uniformOfFintype (ZMod 3) 1) := by
    simp [uniformOfFintype_apply]
  have hne : (uniformOfFintype (ZMod 3) 0) ≠ 0 := by simp [uniformOfFintype_apply]
  have hview := (ENNReal.mul_right_inj hne (PMF.apply_ne_top _ _)).mp
    (h00.trans ((heq ▸ h10).symm))
  rw [leakyView_zero, leakyView_one] at hview
  exact one_ne_zero hview

end CslibFrontierTests.SecretSharingAccessStructure
