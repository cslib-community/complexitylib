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
public import CslibFrontier.Crypto.Protocols.SecretSharing.Shamir.Linear
import CslibFrontier.Probability.PMF.Map

/-!
# Shamir Threshold Secret Sharing as an Access-Structure Instance

This module instantiates `Cslib.Crypto.Protocols.SecretSharing.AccessScheme` for Shamir
secret sharing over a field `F`, using the linear reconstruction lemma
`Shamir.reconstruct_share_eq_secret` and unauthorized marginal uniformity lemma
`Shamir.uniformOfFintype_map_restrict_share` from
`CslibFrontier/Crypto/Protocols/SecretSharing/Shamir/Linear.lean` ([Shamir1979]; [KatzLindell2020]).

It provides:

1. `shamirAccessStructure`: the `(params.threshold + 1)`-threshold access structure.
2. `shamirSources`, `shamirAccessScheme`: Shamir sharing over the class of all
   translation-invariant tail-coefficient distributions. Note that when `F` is finite,
   `shamirSources` consists solely of the uniform distribution (`{uniformOfFintype}`), whereas
   when `F` is infinite and `params.threshold ≥ 1`, no translation-invariant `PMF` on
   `Fin params.threshold → F` exists (`shamirSources = ∅`), so `shamirAccessScheme` has vacuous
   privacy over infinite fields (while universal correctness still holds for all keys).
3. `shamirUniformAccessScheme`: canonical finite-field Shamir sharing over the uniform tail
   distribution, together with `shamirUniform_viewDist_eq` (marginal uniformity) and
   `shamirUniform_mutualInfo_eq_zero` (vanishing mutual information).
4. `shamirPaddedSources`, `shamirPaddedAccessScheme`: auxiliary-key padding of `shamirAccessScheme`
   via `comapKey Prod.fst`, pairing `Randomness params` with an arbitrary ignored component
   `Aux` (not an imperfect-randomness construction in [Aggarwal2026]'s sense).
5. `shamirToTwoTwo`: `(2, 2)`-threshold sharing derived from Shamir (`1 ≤ params.threshold`) via
   design composition (`ThresholdDesignOn.toTwoTwo`, [Aggarwal2026], Section 5; [ACOR22]
   attribution unverified directly).

## Main definitions

* `Cslib.Crypto.Protocols.SecretSharing.shamirAccessStructure`: `(params.threshold + 1)`-threshold
  access structure for Shamir parameters.
* `Cslib.Crypto.Protocols.SecretSharing.shamirSources`: class of translation-invariant tail
  distributions (`{uniform}` for finite `F`; `∅` for infinite `F` with `params.threshold ≥ 1`).
* `Cslib.Crypto.Protocols.SecretSharing.shamirAccessSchemeOf`,
  `Cslib.Crypto.Protocols.SecretSharing.shamirAccessScheme`,
  `Cslib.Crypto.Protocols.SecretSharing.shamirUniformAccessScheme`: Shamir `AccessScheme`
  instances.
* `Cslib.Crypto.Protocols.SecretSharing.shamirPaddedSources`,
  `Cslib.Crypto.Protocols.SecretSharing.shamirPaddedAccessScheme`: auxiliary-key padding of
  Shamir sharing (ignores `Aux`).
* `Cslib.Crypto.Protocols.SecretSharing.shamirToTwoTwo`: `(2, 2)` scheme via design composition
  from Shamir (`1 ≤ params.threshold`).

## Main results

* `Cslib.Crypto.Protocols.SecretSharing.uniformOfFintype_mem_shamirSources`: uniform tail
  coefficients belong to `shamirSources`.
* `Cslib.Crypto.Protocols.SecretSharing.shamirUniform_viewDist_eq`: unauthorized coalitions have
  uniform view distributions under uniform Shamir randomness.
* `Cslib.Crypto.Protocols.SecretSharing.shamirUniform_mutualInfo_eq_zero`: unauthorized coalitions
  have zero mutual information with the secret under uniform Shamir randomness.
* `Cslib.Crypto.Protocols.SecretSharing.bind_mem_shamirPaddedSources`: any correlated auxiliary
  distribution paired with a translation-invariant Shamir tail lies in `shamirPaddedSources`.

## References

* [A. Shamir, *How to Share a Secret*][Shamir1979].
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020].
* [D. Aggarwal, *Secret Sharing Despite Non-Extractable Randomness*][Aggarwal2026],
  Section 5 (checked locator for design reduction).
* [D. Aggarwal, E. Chung, M. Obremski, J. Ribeiro, *On Secret Sharing, Randomness, and
  Random-less Reductions for Secret Sharing*][ACOR22] (unverified directly; attributed via
  [Aggarwal2026], Section 5).
-/

public section

namespace Cslib.Crypto.Protocols.SecretSharing

open Cslib.Probability Cslib.Probability.PMF

section ShamirInstance

variable {F Party : Type*} [Field F] [Fintype Party]

/-- The threshold access structure of Shamir secret sharing: coalitions of size at least
`params.threshold + 1` are authorized. -/
@[expose] def shamirAccessStructure (params : Shamir.Params F Party) : AccessStructure Party :=
  AccessStructure.threshold Party (params.threshold + 1)

@[simp]
theorem shamirAccessStructure_authorized_iff (params : Shamir.Params F Party)
    (s : Finset Party) :
    (shamirAccessStructure params).authorized s ↔ Shamir.authorized params s :=
  Iff.rfl

/-- The source class of translation-invariant distributions on Shamir tail coefficients. When `F`
is finite, this is `{uniformOfFintype}`; when `F` is infinite and `params.threshold ≥ 1`, no
translation-invariant `PMF` exists (`shamirSources = ∅`), so privacy over it is vacuous. -/
@[expose] def shamirSources (params : Shamir.Params F Party) :
    SourceClass (Shamir.Randomness params) :=
  { P | ∀ δ : Shamir.Randomness params, P.map (· + δ) = P }

/-- Uniform tail coefficients belong to `shamirSources`. -/
theorem uniformOfFintype_mem_shamirSources [Fintype F] [Nonempty F]
    (params : Shamir.Params F Party) :
    uniformOfFintype (Shamir.Randomness params) ∈ shamirSources params :=
  (Shamir.uniformTailSampler params).map_add_eq_self

/-- Shamir threshold secret sharing over any subclass of translation-invariant tail samplers. -/
@[expose] noncomputable def shamirAccessSchemeOf (params : Shamir.Params F Party)
    (sources : SourceClass (Shamir.Randomness params))
    (hsources : sources ⊆ shamirSources params) :
    AccessScheme F (Shamir.Randomness params) Party (fun _ => F) where
  access := shamirAccessStructure params
  sources := sources
  share := Shamir.share params
  reconstruct := Shamir.reconstruct params
  correct coeffs secret _ hs := Shamir.reconstruct_share_eq_secret params coeffs secret hs
  view_indist P hP s hs m₀ m₁ :=
    Shamir.view_indist_of_tailSampler params ⟨P, hsources hP⟩ s hs m₀ m₁

@[simp]
theorem shamirAccessSchemeOf_access (params : Shamir.Params F Party)
    (sources : SourceClass (Shamir.Randomness params))
    (hsources : sources ⊆ shamirSources params) :
    (shamirAccessSchemeOf params sources hsources).access = shamirAccessStructure params :=
  rfl

/-- Shamir secret sharing over `shamirSources`. Note that for infinite fields `F` with
`params.threshold ≥ 1`, `shamirSources params = ∅`, so privacy is vacuous and only universal
correctness is nontrivial; use `shamirUniformAccessScheme` for finite fields. -/
@[expose] noncomputable def shamirAccessScheme (params : Shamir.Params F Party) :
    AccessScheme F (Shamir.Randomness params) Party (fun _ => F) :=
  shamirAccessSchemeOf params (shamirSources params) Set.Subset.rfl

@[simp]
theorem shamirAccessScheme_access (params : Shamir.Params F Party) :
    (shamirAccessScheme params).access = shamirAccessStructure params :=
  rfl

/-- Canonical finite-field Shamir secret sharing over the singleton uniform tail source. -/
@[expose] noncomputable def shamirUniformAccessScheme (params : Shamir.Params F Party)
    [Fintype F] [Nonempty F] :
    AccessScheme F (Shamir.Randomness params) Party (fun _ => F) :=
  shamirAccessSchemeOf params
    (SourceClass.singleton (uniformOfFintype (Shamir.Randomness params)))
    (Set.singleton_subset_iff.mpr (uniformOfFintype_mem_shamirSources params))

@[simp]
theorem shamirUniformAccessScheme_access (params : Shamir.Params F Party)
    [Fintype F] [Nonempty F] :
    (shamirUniformAccessScheme params).access = shamirAccessStructure params :=
  rfl

/-- Under uniform Shamir randomness, any unauthorized coalition's view distribution is uniform
on `s → F` (via `Shamir.uniformOfFintype_map_restrict_share`). -/
theorem shamirUniform_viewDist_eq [Fintype F] [Nonempty F] [DecidableEq Party]
    (params : Shamir.Params F Party) {s : Finset Party}
    (hs : ¬ (shamirUniformAccessScheme params).access.authorized s) (secret : F) :
    (shamirUniformAccessScheme params).viewDist
        (uniformOfFintype (Shamir.Randomness params)) s secret =
      uniformOfFintype (s → F) := by
  have hle : s.card ≤ params.threshold := by
    have hs' : ¬ params.threshold + 1 ≤ s.card := by
      simpa only [shamirUniformAccessScheme, shamirAccessSchemeOf, shamirAccessStructure,
        AccessStructure.threshold_authorized_iff] using hs
    omega
  exact Shamir.uniformOfFintype_map_restrict_share params s hle secret

/-- Under uniform Shamir randomness, any unauthorized coalition's view has zero mutual
information with the secret. -/
theorem shamirUniform_mutualInfo_eq_zero [Fintype F] [Nonempty F]
    (params : Shamir.Params F Party) {s : Finset Party}
    (hs : ¬ (shamirUniformAccessScheme params).access.authorized s) (secretDist : PMF F) :
    mutualInfo (jointSecretView (uniformOfFintype (Shamir.Randomness params))
      (shamirUniformAccessScheme params).share s secretDist) = 0 :=
  (shamirUniformAccessScheme params).mutualInfo_view_eq_zero (Set.mem_singleton _) hs secretDist

/-- Auxiliary-key-padded sources for Shamir sharing: pairs `(r, aux)` whose tail-coefficient
marginal `P.map Prod.fst` is translation-invariant (uniform when `F` is finite), paired with
unused auxiliary material `aux` that the scheme ignores. -/
@[expose] noncomputable def shamirPaddedSources (params : Shamir.Params F Party) (Aux : Type*) :
    SourceClass (Shamir.Randomness params × Aux) :=
  { P | P.map Prod.fst ∈ shamirSources params }

/-- Any correlated auxiliary distribution paired with a translation-invariant tail source lies in
`shamirPaddedSources`. -/
theorem bind_mem_shamirPaddedSources {params : Shamir.Params F Party} {Aux : Type*}
    {P : PMF (Shamir.Randomness params)} (hP : P ∈ shamirSources params)
    (Q : Shamir.Randomness params → PMF Aux) :
    (P.bind fun r => (Q r).map (r, ·)) ∈ shamirPaddedSources params Aux := by
  simpa only [shamirPaddedSources, Set.mem_ofPred_eq, map_fst_bind_pair] using hP

/-- Auxiliary-key padding of `shamirAccessScheme` onto `Randomness params × Aux` via
`comapKey Prod.fst` (ignoring the auxiliary component `Aux`; not an imperfect-randomness
construction in [Aggarwal2026]'s sense). -/
@[expose] noncomputable def shamirPaddedAccessScheme (params : Shamir.Params F Party)
    (Aux : Type*) :
    AccessScheme F (Shamir.Randomness params × Aux) Party (fun _ => F) :=
  (shamirAccessScheme params).comapKey Prod.fst (shamirPaddedSources params Aux) (fun _ hP => hP)

@[simp]
theorem shamirPaddedAccessScheme_access (params : Shamir.Params F Party) (Aux : Type*) :
    (shamirPaddedAccessScheme params Aux).access = shamirAccessStructure params :=
  rfl

/-- `(t', n') → (2, 2)` distribution-design reduction applied to Shamir secret sharing whenever
`1 ≤ params.threshold` ([Aggarwal2026], Section 5; [ACOR22] attribution unverified directly). -/
@[expose] noncomputable def shamirToTwoTwo [DecidableEq Party]
    (params : Shamir.Params F Party) (ht : 1 ≤ params.threshold) :=
  (shamirAccessScheme params).toTwoTwo (rfl : (shamirAccessScheme params).access =
    AccessStructure.threshold Party (params.threshold + 1))
    (by omega) params.threshold_lt_card

@[simp]
theorem shamirToTwoTwo_access [DecidableEq Party]
    (params : Shamir.Params F Party) (ht : 1 ≤ params.threshold) :
    (shamirToTwoTwo params ht).access = AccessStructure.threshold (Fin 2) 2 :=
  rfl

end ShamirInstance

end Cslib.Crypto.Protocols.SecretSharing
