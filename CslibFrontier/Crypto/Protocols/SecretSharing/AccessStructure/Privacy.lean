/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.Basic
public import CslibFrontier.Probability.MutualInformation
public import CslibFrontier.Probability.StatisticalDistance
import CslibFrontier.Probability.PMF.Map

/-!
# Privacy Notions and Information-Theoretic Characterizations for Access Structures

This module complements `CslibFrontier/Crypto/Protocols/SecretSharing/AccessStructure/Basic.lean`
with unbundled correctness and privacy predicates over general monotone access structures and
source classes, statistical `δ`-privacy ([Aggarwal2026], Definition 2.1), posterior privacy
([KatzLindell2020]), and Shannon mutual-information / conditional-entropy characterizations
([CoverThomas2006], Sections 2.4–2.5).

## Main definitions

* `Cslib.Crypto.Protocols.SecretSharing.PerfectlyCorrect`: universal deterministic
  reconstruction on authorized coalitions.
* `Cslib.Crypto.Protocols.SecretSharing.ViewIndist`: secret-independent unauthorized views for
  every source in a class.
* `Cslib.Crypto.Protocols.SecretSharing.StatisticallyPrivate`: `δ`-statistical distance bound
  between unauthorized views of any two secrets, for every source in a class.
* `Cslib.Crypto.Protocols.SecretSharing.posteriorSecretDistOf`,
  `Cslib.Crypto.Protocols.SecretSharing.PosteriorPrivate`,
  `Cslib.Crypto.Protocols.SecretSharing.AccessScheme.posteriorSecretDist`,
  `Cslib.Crypto.Protocols.SecretSharing.AccessScheme.PerfectlyPrivate`: posterior invariance under
  observing an unauthorized view.
* `Cslib.Crypto.Protocols.SecretSharing.jointSecretView`: joint distribution of a secret prior
  and a coalition's view.

## Main results

* `Cslib.Crypto.Protocols.SecretSharing.statisticallyPrivate_zero_iff`: `0`-statistical privacy
  equals `ViewIndist`.
* `Cslib.Crypto.Protocols.SecretSharing.posteriorPrivate_iff_viewIndist`: posterior privacy equals
  view indistinguishability.
* `Cslib.Crypto.Protocols.SecretSharing.AccessScheme.perfectlyPrivate`: every `AccessScheme`
  satisfies posterior privacy.
* `Cslib.Crypto.Protocols.SecretSharing.mutualInfo_eq_zero_iff_viewIndist`: vanishing mutual
  information across all priors equals `ViewIndist`.
* `Cslib.Crypto.Protocols.SecretSharing.AccessScheme.mutualInfo_view_eq_zero`: zero mutual
  information for unauthorized coalitions.
* `Cslib.Crypto.Protocols.SecretSharing.AccessScheme.conditionalEntropy_secret_given_view_eq_zero`,
  `Cslib.Crypto.Protocols.SecretSharing.AccessScheme.mutualInfo_authorized_eq_entropy`:
  authorized coalitions leave zero conditional secret entropy and capture full secret entropy.

## References

* [D. Aggarwal, *Secret Sharing Despite Non-Extractable Randomness*][Aggarwal2026],
  Definition 2.1 (threshold finite-key definition generalized here to arbitrary `AccessStructure`
  and `Key`).
* [T. M. Cover, J. A. Thomas, *Elements of Information Theory*][CoverThomas2006], Sections 2.4–2.5.
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020].
-/

public section

namespace Cslib.Crypto.Protocols.SecretSharing

open Cslib.Probability Cslib.Probability.PMF
open scoped NNReal ENNReal

section Predicates

variable {Secret Key Party : Type*} {Share : Party → Type*}

/-- Deterministic universal correctness: every authorized coalition reconstructs `secret` for
every ambient key `k`. -/
@[expose] def PerfectlyCorrect (access : AccessStructure Party)
    (share : Key → Secret → (i : Party) → Share i)
    (reconstruct : (s : Finset Party) → ((i : s) → Share i.1) → Secret) : Prop :=
  ∀ (k : Key) (secret : Secret) (s : Finset Party),
    access.authorized s → reconstruct s (fun i => share k secret i.1) = secret

/-- Perfect view-indistinguishability privacy relative to source class `sources`: under every
source `P ∈ sources` and every unauthorized coalition `s`, any two secrets induce identical view
distributions. -/
@[expose] def ViewIndist (access : AccessStructure Party) (sources : SourceClass Key)
    (share : Key → Secret → (i : Party) → Share i) : Prop :=
  ∀ P ∈ sources, ∀ (s : Finset Party), ¬ access.authorized s →
    ∀ secret₀ secret₁ : Secret,
      AccessStructure.viewDistOf P share s secret₀ =
        AccessStructure.viewDistOf P share s secret₁

/-- Statistical `δ`-privacy relative to source class `sources` (generalizing [Aggarwal2026],
Definition 2.1 from threshold structures and finite key spaces to general monotone access structures
and arbitrary `Key`): under every source `P ∈ sources` and every unauthorized coalition `s`, the
views of any two secrets have statistical distance at most `δ`. -/
@[expose] def StatisticallyPrivate [DecidableEq Party] [∀ i, Fintype (Share i)]
    (access : AccessStructure Party) (sources : SourceClass Key)
    (share : Key → Secret → (i : Party) → Share i) (δ : ℝ≥0) : Prop :=
  ∀ P ∈ sources, ∀ (s : Finset Party), ¬ access.authorized s →
    ∀ secret₀ secret₁ : Secret,
      StatisticallyClose (AccessStructure.viewDistOf P share s secret₀)
        (AccessStructure.viewDistOf P share s secret₁) δ

/-- Statistical `0`-privacy is equivalent to exact view indistinguishability. -/
@[simp]
theorem statisticallyPrivate_zero_iff [DecidableEq Party] [∀ i, Fintype (Share i)]
    (access : AccessStructure Party) (sources : SourceClass Key)
    (share : Key → Secret → (i : Party) → Share i) :
    StatisticallyPrivate access sources share 0 ↔ ViewIndist access sources share := by
  simp only [StatisticallyPrivate, ViewIndist, statisticallyClose_zero_iff]

/-- Statistical privacy is monotone in the error tolerance `δ`. -/
theorem StatisticallyPrivate.mono [DecidableEq Party] [∀ i, Fintype (Share i)]
    {access : AccessStructure Party} {sources : SourceClass Key}
    {share : Key → Secret → (i : Party) → Share i} {δ δ' : ℝ≥0}
    (hδ : δ ≤ δ') (h : StatisticallyPrivate access sources share δ) :
    StatisticallyPrivate access sources share δ' :=
  fun P hP s hs m₀ m₁ => StatisticallyClose.mono hδ (h P hP s hs m₀ m₁)

/-- Every `AccessScheme` satisfies `PerfectlyCorrect`. -/
theorem AccessScheme.perfectlyCorrect (scheme : AccessScheme Secret Key Party Share) :
    PerfectlyCorrect scheme.access scheme.share scheme.reconstruct :=
  scheme.correct

/-- Every `AccessScheme` satisfies `ViewIndist`. -/
theorem AccessScheme.viewIndist (scheme : AccessScheme Secret Key Party Share) :
    ViewIndist scheme.access scheme.sources scheme.share :=
  scheme.view_indist

/-- Every `AccessScheme` is statistically `0`-private. -/
theorem AccessScheme.statisticallyPrivate_zero [DecidableEq Party] [∀ i, Fintype (Share i)]
    (scheme : AccessScheme Secret Key Party Share) :
    StatisticallyPrivate scheme.access scheme.sources scheme.share 0 :=
  (statisticallyPrivate_zero_iff _ _ _).mpr scheme.view_indist

/-- Every `AccessScheme` is statistically `δ`-private for every `δ : ℝ≥0`. -/
theorem AccessScheme.statisticallyPrivate [DecidableEq Party] [∀ i, Fintype (Share i)]
    (scheme : AccessScheme Secret Key Party Share) (δ : ℝ≥0) :
    StatisticallyPrivate scheme.access scheme.sources scheme.share δ :=
  scheme.statisticallyPrivate_zero.mono bot_le

end Predicates

section Posterior

variable {Secret Key Party : Type*} {Share : Party → Type*}

/-- Posterior distribution on secrets given an observed coalition view `v` under source `P` and
prior `secretDist`. -/
@[expose] noncomputable def posteriorSecretDistOf
    (P : PMF Key) (share : Key → Secret → (i : Party) → Share i)
    (s : Finset Party) (secretDist : PMF Secret)
    (v : (i : s) → Share i.1)
    (hv : v ∈ (secretDist.bind (AccessStructure.viewDistOf P share s)).support) : PMF Secret :=
  posteriorDist secretDist (AccessStructure.viewDistOf P share s) v hv

@[simp]
theorem posteriorSecretDistOf_apply
    (P : PMF Key) (share : Key → Secret → (i : Party) → Share i)
    (s : Finset Party) (secretDist : PMF Secret)
    (v : (i : s) → Share i.1)
    (hv : v ∈ (secretDist.bind (AccessStructure.viewDistOf P share s)).support)
    (secret : Secret) :
    posteriorSecretDistOf P share s secretDist v hv secret =
      (secretDist.bind fun secret' =>
        (AccessStructure.viewDistOf P share s secret').bind fun v' =>
          PMF.pure (secret', v')) (secret, v) /
        (secretDist.bind (AccessStructure.viewDistOf P share s)) v :=
  posteriorDist_apply secretDist (AccessStructure.viewDistOf P share s) v hv secret

/-- Posterior privacy: under every source `P ∈ sources` and unauthorized coalition `s`,
conditioning on any positive-probability view leaves every secret prior unchanged. -/
@[expose] def PosteriorPrivate (access : AccessStructure Party) (sources : SourceClass Key)
    (share : Key → Secret → (i : Party) → Share i) : Prop :=
  ∀ P ∈ sources, ∀ (s : Finset Party), ¬ access.authorized s →
    ∀ (secretDist : PMF Secret) (v : (i : s) → Share i.1)
      (hv : v ∈ (secretDist.bind (AccessStructure.viewDistOf P share s)).support),
        posteriorSecretDistOf P share s secretDist v hv = secretDist

/-- Posterior privacy is equivalent to view indistinguishability. -/
theorem posteriorPrivate_iff_viewIndist
    (access : AccessStructure Party) (sources : SourceClass Key)
    (share : Key → Secret → (i : Party) → Share i) :
    PosteriorPrivate access sources share ↔ ViewIndist access sources share := by
  classical
  constructor
  · intro h P hP s hs secret₀ secret₁
    ext v
    let μ := uniformOfFinset ({secret₀, secret₁} : Finset Secret) ⟨secret₀, by simp⟩
    by_cases hv : v ∈ (μ.bind (AccessStructure.viewDistOf P share s)).support
    · have key (m : Secret) (hm : m ∈ ({secret₀, secret₁} : Finset Secret)) :
          AccessStructure.viewDistOf P share s m v =
            (μ.bind (AccessStructure.viewDistOf P share s)) v := by
        have hpost := congrFun (congrArg DFunLike.coe (h P hP s hs μ v hv)) m
        simp only [posteriorSecretDistOf_apply, bind_pair_apply] at hpost
        have hne_zero : (μ.bind (AccessStructure.viewDistOf P share s)) v ≠ 0 :=
          (PMF.mem_support_iff _ _).mp hv
        have hne_top : (μ.bind (AccessStructure.viewDistOf P share s)) v ≠ ⊤ :=
          PMF.apply_ne_top _ _
        have hmul := congrArg (· * (μ.bind (AccessStructure.viewDistOf P share s)) v) hpost
        rw [ENNReal.div_mul_cancel hne_zero hne_top] at hmul
        have hμ_zero : μ m ≠ 0 :=
          (PMF.mem_support_iff _ _).mp
            ((mem_support_uniformOfFinset_iff ⟨secret₀, by simp⟩ m).mpr hm)
        exact (ENNReal.mul_right_inj hμ_zero (PMF.apply_ne_top μ m)).mp hmul
      exact (key secret₀ (by simp)).trans (key secret₁ (by simp)).symm
    · have hzero : (μ.bind (AccessStructure.viewDistOf P share s)) v = 0 :=
        (PMF.apply_eq_zero_iff _ _).mpr hv
      rw [PMF.bind_apply, tsum_eq_zero_iff] at hzero
      have h0 : AccessStructure.viewDistOf P share s secret₀ v = 0 := by
        have hmul := hzero secret₀
        have hμ0 : μ secret₀ ≠ 0 :=
          (PMF.mem_support_iff _ _).mp
            ((mem_support_uniformOfFinset_iff ⟨secret₀, by simp⟩ secret₀).mpr (by simp))
        exact (mul_eq_zero.mp hmul).resolve_left hμ0
      have h1 : AccessStructure.viewDistOf P share s secret₁ v = 0 := by
        have hmul := hzero secret₁
        have hμ1 : μ secret₁ ≠ 0 :=
          (PMF.mem_support_iff _ _).mp
            ((mem_support_uniformOfFinset_iff ⟨secret₀, by simp⟩ secret₁).mpr (by simp))
        exact (mul_eq_zero.mp hmul).resolve_left hμ1
      exact h0.trans h1.symm
  · intro h P hP s hs secretDist v hv
    exact posteriorDist_eq_prior_of_outputIndist secretDist
      (AccessStructure.viewDistOf P share s) (h P hP s hs) v hv

/-- The posterior distribution on secrets given an observed view of an `AccessScheme`. -/
@[expose] noncomputable def AccessScheme.posteriorSecretDist
    (scheme : AccessScheme Secret Key Party Share)
    (P : PMF Key) (s : Finset Party) (secretDist : PMF Secret)
    (v : (i : s) → Share i.1)
    (hv : v ∈ (secretDist.bind (scheme.viewDist P s)).support) : PMF Secret :=
  posteriorSecretDistOf P scheme.share s secretDist v hv

/-- Perfect posterior privacy for an `AccessScheme`: conditioning on any unauthorized coalition
view leaves every prior on secrets unchanged. -/
@[expose] def AccessScheme.PerfectlyPrivate (scheme : AccessScheme Secret Key Party Share) : Prop :=
  PosteriorPrivate scheme.access scheme.sources scheme.share

/-- Every `AccessScheme` has posterior privacy. -/
theorem AccessScheme.perfectlyPrivate (scheme : AccessScheme Secret Key Party Share) :
    scheme.PerfectlyPrivate :=
  (posteriorPrivate_iff_viewIndist _ _ _).mpr scheme.view_indist

end Posterior

section MutualInformation

variable {Secret Key Party : Type*} {Share : Party → Type*}

/-- The joint distribution of a secret drawn from `secretDist` paired with coalition `s`'s view
under key source `P`. -/
@[expose] noncomputable def jointSecretView
    (P : PMF Key) (share : Key → Secret → (i : Party) → Share i)
    (s : Finset Party) (secretDist : PMF Secret) :
    PMF (Secret × ((i : s) → Share i.1)) :=
  secretDist.bind fun m => (AccessStructure.viewDistOf P share s m).map (m, ·)

@[simp]
theorem map_fst_jointSecretView
    (P : PMF Key) (share : Key → Secret → (i : Party) → Share i)
    (s : Finset Party) (secretDist : PMF Secret) :
    (jointSecretView P share s secretDist).map Prod.fst = secretDist :=
  map_fst_bind_pair secretDist (AccessStructure.viewDistOf P share s)

/-- Under `ViewIndist`, every secret prior has zero mutual information with any unauthorized
coalition's view. -/
theorem mutualInfo_jointSecretView_eq_zero_of_viewIndist
    [Finite Secret] [∀ i, Finite (Share i)]
    {access : AccessStructure Party} {sources : SourceClass Key}
    {share : Key → Secret → (i : Party) → Share i}
    (h : ViewIndist access sources share)
    {P : PMF Key} (hP : P ∈ sources) {s : Finset Party} (hs : ¬ access.authorized s)
    (secretDist : PMF Secret) :
    mutualInfo (jointSecretView P share s secretDist) = 0 := by
  obtain ⟨m₀, _⟩ := secretDist.support_nonempty
  have hlaw : jointSecretView P share s secretDist =
      secretDist.bind fun m => (AccessStructure.viewDistOf P share s m₀).map (m, ·) := by
    refine congrArg secretDist.bind (funext fun m => ?_)
    rw [h P hP s hs m m₀]
  rw [hlaw]
  exact mutualInfo_bind_map_prodMk secretDist (AccessStructure.viewDistOf P share s m₀)

/-- Vanishing mutual information across all secret priors is equivalent to `ViewIndist`. -/
theorem mutualInfo_eq_zero_iff_viewIndist
    [Finite Secret] [∀ i, Finite (Share i)]
    (access : AccessStructure Party) (sources : SourceClass Key)
    (share : Key → Secret → (i : Party) → Share i) :
    (∀ P ∈ sources, ∀ (s : Finset Party), ¬ access.authorized s →
      ∀ secretDist : PMF Secret, mutualInfo (jointSecretView P share s secretDist) = 0) ↔
      ViewIndist access sources share := by
  classical
  constructor
  · intro h P hP s hs m₀ m₁
    let μ := uniformOfFinset ({m₀, m₁} : Finset Secret) ⟨m₀, by simp⟩
    have hind := (mutualInfo_eq_zero_iff (jointSecretView P share s μ)).mp (h P hP s hs μ)
    rw [map_fst_jointSecretView] at hind
    ext v
    have key (m : Secret) (hm : m ∈ ({m₀, m₁} : Finset Secret)) :
        AccessStructure.viewDistOf P share s m v =
          ((jointSecretView P share s μ).map Prod.snd) v := by
      have happly := congrArg (fun p => p (m, v)) hind
      change (μ.bind fun a =>
          (AccessStructure.viewDistOf P share s a).bind fun b => PMF.pure (a, b)) (m, v) =
        (μ.bind fun a =>
          ((jointSecretView P share s μ).map Prod.snd).bind fun b => PMF.pure (a, b)) (m, v)
        at happly
      rw [bind_pair_apply, bind_pair_apply] at happly
      have hμ : μ m ≠ 0 :=
        (PMF.mem_support_iff _ _).mp
          ((mem_support_uniformOfFinset_iff ⟨m₀, by simp⟩ m).mpr hm)
      exact (ENNReal.mul_right_inj hμ (PMF.apply_ne_top μ m)).mp happly
    exact (key m₀ (by simp)).trans (key m₁ (by simp)).symm
  · intro h P hP s hs secretDist
    exact mutualInfo_jointSecretView_eq_zero_of_viewIndist h hP hs secretDist

/-- For an `AccessScheme`, any unauthorized coalition has zero mutual information with the
secret under every source in `sources`. -/
theorem AccessScheme.mutualInfo_view_eq_zero
    [Finite Secret] [∀ i, Finite (Share i)]
    (scheme : AccessScheme Secret Key Party Share)
    {P : PMF Key} (hP : P ∈ scheme.sources) {s : Finset Party}
    (hs : ¬ scheme.access.authorized s) (secretDist : PMF Secret) :
    mutualInfo (jointSecretView P scheme.share s secretDist) = 0 :=
  mutualInfo_jointSecretView_eq_zero_of_viewIndist scheme.view_indist hP hs secretDist

/-- For an `AccessScheme`, any authorized coalition leaves zero conditional entropy in the
secret given its view. -/
theorem AccessScheme.conditionalEntropy_secret_given_view_eq_zero
    [Finite Secret] [∀ i, Finite (Share i)]
    (scheme : AccessScheme Secret Key Party Share)
    (P : PMF Key) {s : Finset Party} (hs : scheme.access.authorized s)
    (secretDist : PMF Secret) :
    conditionalEntropy ((jointSecretView P scheme.share s secretDist).map Prod.swap) = 0 := by
  let ν := (jointSecretView P scheme.share s secretDist).map Prod.swap
  have hsupp : ∀ p ∈ ν.support, id p = (p.1, scheme.reconstruct s p.1) := by
    intro p hp
    rcases p with ⟨v, m⟩
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨⟨m', v'⟩, hmv', hswap⟩ := hp
    simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hswap
    obtain ⟨rfl, rfl⟩ := hswap
    rw [jointSecretView, PMF.mem_support_bind_iff] at hmv'
    obtain ⟨m'', _, hm''⟩ := hmv'
    rw [PMF.mem_support_map_iff] at hm''
    obtain ⟨v'', hv'', hpair⟩ := hm''
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    rw [AccessStructure.viewDistOf, PMF.mem_support_map_iff] at hv''
    obtain ⟨k, _, hk⟩ := hv''
    simp only [id_eq, Prod.mk.injEq, true_and]
    rw [← hk]
    exact (scheme.correct k m'' s hs).symm
  have hent := entropy_map_eq_of_comp ν (F := Prod.fst) (G := id)
    (e := fun v => (v, scheme.reconstruct s v))
    (fun _ _ h => congrArg Prod.fst h) hsupp
  rw [PMF.map_id] at hent
  rw [conditionalEntropy, hent, sub_self]

/-- For an `AccessScheme`, any authorized coalition's view has mutual information equal to the
full Shannon entropy of the secret prior. -/
theorem AccessScheme.mutualInfo_authorized_eq_entropy
    [Finite Secret] [∀ i, Finite (Share i)]
    (scheme : AccessScheme Secret Key Party Share)
    (P : PMF Key) {s : Finset Party} (hs : scheme.access.authorized s)
    (secretDist : PMF Secret) :
    mutualInfo (jointSecretView P scheme.share s secretDist) = entropy secretDist := by
  let joint := jointSecretView P scheme.share s secretDist
  have hswap_mi : mutualInfo (joint.map Prod.swap) = mutualInfo joint := by
    have hL : mutualInfo (joint.map Prod.swap) =
        entropy (joint.map Prod.snd) + entropy (joint.map Prod.fst) -
          entropy (joint.map Prod.swap) :=
      mutualInfo_map joint Prod.snd Prod.fst
    have hR : mutualInfo joint =
        entropy (joint.map Prod.fst) + entropy (joint.map Prod.snd) - entropy joint := by
      have hid := mutualInfo_map joint Prod.fst Prod.snd
      rw [show (fun ω : Secret × ((i : s) → Share i.1) => (ω.1, ω.2)) = id from rfl,
        PMF.map_id] at hid
      exact hid
    rw [hL, hR, entropy_map_of_injective joint Prod.swap_injective]
    ring
  have hsnd : (joint.map Prod.swap).map Prod.snd = secretDist := by
    have h2 : (joint.map Prod.swap).map Prod.snd = joint.map Prod.fst := by
      rw [PMF.map_comp]
      rfl
    rw [h2]
    exact map_fst_jointSecretView P scheme.share s secretDist
  rw [← hswap_mi, mutualInfo_eq_entropy_map_snd_sub_conditionalEntropy, hsnd,
    scheme.conditionalEntropy_secret_given_view_eq_zero P hs secretDist, sub_zero]

end MutualInformation

end Cslib.Crypto.Protocols.SecretSharing
