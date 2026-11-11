/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.PMF
public import Cslib.Crypto.Protocols.SecretSharing.Scheme

/-!
# Secret Sharing over General Monotone Access Structures and Source Classes

This module generalizes `Cslib.Crypto.Protocols.SecretSharing.Scheme` beyond threshold,
finite-key Definition 2.1 of [Aggarwal2026] in two orthogonal directions:

1. **First-class monotone access structures (`AccessStructure`):** monotone upward-closed
   families of authorized coalitions `Finset Party`, supporting threshold structures
   (`AccessStructure.threshold`), all-party sharing (`AccessStructure.all`), upward closures
   (`AccessStructure.ofSets`), preimages under share assignments (`AccessStructure.pullback`),
   lattice operations (`AccessStructure.inter`, `AccessStructure.union`), duals
   (`AccessStructure.dual`), and minimal authorized sets (`AccessStructure.IsMinimalAuthorized`).
2. **Source-class secret sharing (`SourceClass`, `AccessScheme`):** deterministic sharing and
   reconstruction maps paired with a class `SourceClass Key := Set (PMF Key)` of allowed key
   distributions, generalizing [Aggarwal2026], Definition 2.1 (stated there for threshold
   structures and finite key spaces) to general monotone access structures, arbitrary `Key` types,
   and party-indexed share types `Share : Party → Type*`. A scheme is perfectly correct for every
   key and perfectly private for every distribution in `sources`, while marginal view distributions
   may vary across sources in the class.

Bridges to and from upstream `Cslib.Crypto.Protocols.SecretSharing.Scheme` are provided via
`AccessScheme.ofCslibScheme` and `AccessScheme.toCslibScheme`, along with key-source pullbacks
(`AccessScheme.comapKey`), secret restrictions (`AccessScheme.restrictSecret`), share relabelings
(`AccessScheme.mapShare`), and party relabelings (`AccessScheme.relabelParty`).

## Main definitions

* `Cslib.Crypto.Protocols.SecretSharing.AccessStructure`: monotone access structure on `Party`.
* `Cslib.Crypto.Protocols.SecretSharing.AccessStructure.threshold`,
  `Cslib.Crypto.Protocols.SecretSharing.AccessStructure.all`,
  `Cslib.Crypto.Protocols.SecretSharing.AccessStructure.ofSets`,
  `Cslib.Crypto.Protocols.SecretSharing.AccessStructure.pullback`,
  `Cslib.Crypto.Protocols.SecretSharing.AccessStructure.dual`: standard access structures and
  combinators.
* `Cslib.Crypto.Protocols.SecretSharing.SourceClass`: class of key distributions `Set (PMF Key)`.
* `Cslib.Crypto.Protocols.SecretSharing.AccessStructure.viewDistOf`: coalition view distribution.
* `Cslib.Crypto.Protocols.SecretSharing.AccessScheme`: secret-sharing scheme over a monotone
  access structure relative to a class of key sources.
* `Cslib.Crypto.Protocols.SecretSharing.AccessScheme.ofCslibScheme`,
  `Cslib.Crypto.Protocols.SecretSharing.AccessScheme.toCslibScheme`,
  `Cslib.Crypto.Protocols.SecretSharing.AccessScheme.comapKey`,
  `Cslib.Crypto.Protocols.SecretSharing.AccessScheme.restrictSecret`,
  `Cslib.Crypto.Protocols.SecretSharing.AccessScheme.mapShare`,
  `Cslib.Crypto.Protocols.SecretSharing.AccessScheme.relabelParty`: bridges and combinators.

## Main results

* `Cslib.Crypto.Protocols.SecretSharing.AccessStructure.exists_minimalAuthorized_subset`: every
  authorized coalition contains a minimal authorized sub-coalition.
* `Cslib.Crypto.Protocols.SecretSharing.AccessScheme.reconstruct_view_eq_secret`: authorized
  coalitions reconstruct the secret.
* `Cslib.Crypto.Protocols.SecretSharing.AccessScheme.viewDist_eq_of_not_authorized`:
  unauthorized coalitions have secret-independent views under every source in `sources`.

## References

* [D. Aggarwal, *Secret Sharing Despite Non-Extractable Randomness*][Aggarwal2026],
  Definition 2.1 (checked locator; generalized here from threshold finite-key schemes to arbitrary
  `AccessStructure` and `Key`).
* [D. Aggarwal, E. Chung, M. Obremski, J. Ribeiro, *On Secret Sharing, Randomness, and
  Random-less Reductions for Secret Sharing*][ACOR22] (unverified directly; attributed via
  [Aggarwal2026]).
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020].
-/

public section

namespace Cslib.Crypto.Protocols.SecretSharing

/-- A monotone access structure on party type `Party`, specifying which coalitions are
authorized to reconstruct the secret. -/
@[ext]
structure AccessStructure (Party : Type*) where
  /-- Predicate characterizing authorized coalitions. -/
  authorized : Finset Party → Prop
  /-- Every superset of an authorized coalition is authorized. -/
  mono : Monotone authorized

namespace AccessStructure

section Basic

variable {Party : Type*}

/-- Any sub-coalition of an unauthorized coalition is unauthorized. -/
theorem not_authorized_of_subset (A : AccessStructure Party) {s t : Finset Party}
    (hst : s ⊆ t) (ht : ¬ A.authorized t) : ¬ A.authorized s :=
  mt (A.mono hst) ht

/-- A coalition is minimally authorized when it is authorized and no proper subset is. -/
@[expose] def IsMinimalAuthorized (A : AccessStructure Party) (s : Finset Party) : Prop :=
  A.authorized s ∧ ∀ t ⊂ s, ¬ A.authorized t

/-- An access structure is nontrivial when the empty coalition is unauthorized and the full
party set is authorized. -/
@[expose] def IsNontrivial (A : AccessStructure Party) [Fintype Party] : Prop :=
  ¬ A.authorized ∅ ∧ A.authorized Finset.univ

/-- Every authorized coalition contains a minimally authorized sub-coalition. -/
theorem exists_minimalAuthorized_subset (A : AccessStructure Party) {s : Finset Party}
    (hs : A.authorized s) : ∃ t ⊆ s, A.IsMinimalAuthorized t := by
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hmin : ∀ t ⊂ s, ¬ A.authorized t
    · exact ⟨s, Finset.Subset.rfl, hs, hmin⟩
    · push Not at hmin
      obtain ⟨t, hts, ht⟩ := hmin
      obtain ⟨u, hut, hu⟩ := ih t hts ht
      exact ⟨u, hut.trans (Finset.ssubset_iff_subset_ne.mp hts).1, hu⟩

/-- The `t`-threshold access structure: coalitions of size at least `t` are authorized. -/
@[expose] def threshold (Party : Type*) (t : ℕ) : AccessStructure Party where
  authorized s := t ≤ s.card
  mono _ _ hst hs := le_trans hs (Finset.card_le_card hst)

@[simp]
theorem threshold_authorized_iff (Party : Type*) (t : ℕ) (s : Finset Party) :
    (threshold Party t).authorized s ↔ t ≤ s.card :=
  Iff.rfl

instance (Party : Type*) (t : ℕ) (s : Finset Party) :
    Decidable ((threshold Party t).authorized s) :=
  inferInstanceAs (Decidable (t ≤ s.card))

/-- The all-party access structure: a coalition is authorized iff it contains every party. -/
@[expose] def all (Party : Type*) : AccessStructure Party where
  authorized s := ∀ i : Party, i ∈ s
  mono _ _ hst hs i := hst (hs i)

@[simp]
theorem all_authorized_iff (Party : Type*) (s : Finset Party) :
    (all Party).authorized s ↔ ∀ i : Party, i ∈ s :=
  Iff.rfl

theorem all_authorized_iff_eq_univ [Fintype Party] (s : Finset Party) :
    (all Party).authorized s ↔ s = Finset.univ := by
  simp only [all_authorized_iff, Finset.eq_univ_iff_forall]

theorem all_eq_threshold [Fintype Party] :
    all Party = threshold Party (Fintype.card Party) := by
  ext s
  rw [all_authorized_iff_eq_univ, threshold_authorized_iff]
  exact ⟨fun h => by subst h; simp,
    fun h => Finset.eq_univ_of_card s (le_antisymm s.card_le_univ h)⟩

/-- Upward closure of a collection `B` of generating coalitions. -/
@[expose] def ofSets {Party : Type*} (B : Set (Finset Party)) : AccessStructure Party where
  authorized s := ∃ b ∈ B, b ⊆ s
  mono _ _ hst := fun ⟨b, hb, hbs⟩ => ⟨b, hb, hbs.trans hst⟩

@[simp]
theorem ofSets_authorized_iff (B : Set (Finset Party)) (s : Finset Party) :
    (ofSets B).authorized s ↔ ∃ b ∈ B, b ⊆ s :=
  Iff.rfl

/-- Pullback of an access structure `A'` along a share-assignment map `assign : Party → Finset
Party'`: a coalition `s` is authorized iff `s.biUnion assign` is authorized in `A'`. -/
@[expose] def pullback {Party' : Type*} [DecidableEq Party']
    (assign : Party → Finset Party') (A' : AccessStructure Party') : AccessStructure Party where
  authorized s := A'.authorized (s.biUnion assign)
  mono _ _ hst hs := A'.mono (Finset.biUnion_subset_biUnion_of_subset_left assign hst) hs

@[simp]
theorem pullback_authorized_iff {Party' : Type*} [DecidableEq Party']
    (assign : Party → Finset Party') (A' : AccessStructure Party') (s : Finset Party) :
    (pullback assign A').authorized s ↔ A'.authorized (s.biUnion assign) :=
  Iff.rfl

/-- Intersection of two access structures: authorized coalitions must be authorized in both. -/
@[expose] def inter (A B : AccessStructure Party) : AccessStructure Party where
  authorized s := A.authorized s ∧ B.authorized s
  mono _ _ hst hs := ⟨A.mono hst hs.1, B.mono hst hs.2⟩

@[simp]
theorem inter_authorized_iff (A B : AccessStructure Party) (s : Finset Party) :
    (inter A B).authorized s ↔ A.authorized s ∧ B.authorized s :=
  Iff.rfl

/-- Union of two access structures: authorized coalitions are authorized in at least one. -/
@[expose] def union (A B : AccessStructure Party) : AccessStructure Party where
  authorized s := A.authorized s ∨ B.authorized s
  mono _ _ hst hs := hs.elim (fun h => Or.inl (A.mono hst h)) (fun h => Or.inr (B.mono hst h))

@[simp]
theorem union_authorized_iff (A B : AccessStructure Party) (s : Finset Party) :
    (union A B).authorized s ↔ A.authorized s ∨ B.authorized s :=
  Iff.rfl

/-- Dual of a finite access structure: `s` is dual-authorized iff `Finset.univ \ s` is not
authorized in `A`. -/
@[expose] def dual [Fintype Party] [DecidableEq Party] (A : AccessStructure Party) :
    AccessStructure Party where
  authorized s := ¬ A.authorized (Finset.univ \ s)
  mono _ _ hst hs hsup := hs (A.mono (Finset.sdiff_subset_sdiff Finset.Subset.rfl hst) hsup)

@[simp]
theorem dual_authorized_iff [Fintype Party] [DecidableEq Party]
    (A : AccessStructure Party) (s : Finset Party) :
    A.dual.authorized s ↔ ¬ A.authorized (Finset.univ \ s) :=
  Iff.rfl

@[simp]
theorem dual_dual [Fintype Party] [DecidableEq Party] (A : AccessStructure Party) :
    A.dual.dual = A := by
  ext s
  simp [Finset.sdiff_sdiff_eq_self (Finset.subset_univ s)]

end Basic

/-- The coalition view distribution induced by a key source `source`, sharing map `share`,
coalition `s`, and `secret`, supporting party-indexed share types. -/
@[expose] noncomputable def viewDistOf {Secret Key Party : Type*} {Share : Party → Type*}
    (source : PMF Key) (share : Key → Secret → (i : Party) → Share i)
    (s : Finset Party) (secret : Secret) : PMF ((i : s) → Share i.1) :=
  source.map fun k i => share k secret i.1

end AccessStructure

/-- A class of allowed key / randomness distributions on `Key` ([Aggarwal2026], Definition 2.1). -/
abbrev SourceClass (Key : Type*) := Set (PMF Key)

namespace SourceClass

/-- The singleton source class containing a single fixed distribution. -/
abbrev singleton {Key : Type*} (P : PMF Key) : SourceClass Key := {P}

/-- Pushforward of a source class along a key transformation `f : Key → Key'`. -/
@[expose] noncomputable def map {Key Key' : Type*} (f : Key → Key') (S : SourceClass Key) :
    SourceClass Key' :=
  PMF.map f '' S

/-- The class of all flat distributions (uniform on nonempty finite subsets of `Key`). -/
@[expose] noncomputable def flat (Key : Type*) : SourceClass Key :=
  { P | ∃ (s : Finset Key) (hs : s.Nonempty), P = Cslib.Probability.PMF.uniformOfFinset s hs }

end SourceClass

/-- A secret-sharing scheme over a general monotone access structure `access`, relative to a class
`sources` of allowed key distributions (an original generalization of the threshold, finite-key
Definition 2.1 in [Aggarwal2026] to general `AccessStructure Party` and arbitrary `Key`).

Correctness is universal over keys `k : Key`: every authorized coalition deterministically
reconstructs the secret. Privacy is relative to `sources`: for every source `P ∈ sources` and
every unauthorized coalition `s`, the induced view distribution does not depend on the secret
(though it may vary with `P`). -/
structure AccessScheme (Secret Key Party : Type*) (Share : Party → Type*) where
  /-- The monotone access structure specifying authorized coalitions. -/
  access : AccessStructure Party
  /-- The class of allowed key distributions. -/
  sources : SourceClass Key
  /-- Sharing algorithm mapping a key, a secret, and a party to that party's share. -/
  share : Key → Secret → (i : Party) → Share i
  /-- Reconstruction algorithm from a coalition's observed shares. -/
  reconstruct (s : Finset Party) : ((i : s) → Share i.1) → Secret
  /-- Every authorized coalition reconstructs the secret for every key. -/
  correct :
    ∀ (k : Key) (secret : Secret) (s : Finset Party),
      access.authorized s → reconstruct s (fun i => share k secret i.1) = secret
  /-- For every allowed key source, unauthorized coalitions receive secret-independent views. -/
  view_indist :
    ∀ P ∈ sources, ∀ (s : Finset Party), ¬ access.authorized s →
      ∀ secret₀ secret₁ : Secret,
        AccessStructure.viewDistOf P share s secret₀ =
          AccessStructure.viewDistOf P share s secret₁

namespace AccessScheme

section Operations

variable {Secret Key Party : Type*} {Share : Party → Type*}

/-- The restricted shares observed by coalition `s`. -/
@[expose] def view (scheme : AccessScheme Secret Key Party Share) (s : Finset Party)
    (k : Key) (secret : Secret) : (i : s) → Share i.1 :=
  fun i => scheme.share k secret i.1

@[simp]
theorem view_apply (scheme : AccessScheme Secret Key Party Share) (s : Finset Party)
    (k : Key) (secret : Secret) (i : s) :
    scheme.view s k secret i = scheme.share k secret i.1 :=
  rfl

/-- The full share distribution for a fixed key source `P` and `secret`. -/
@[expose] noncomputable def shareDist (scheme : AccessScheme Secret Key Party Share)
    (P : PMF Key) (secret : Secret) : PMF ((i : Party) → Share i) :=
  P.map fun k => scheme.share k secret

/-- The coalition view distribution induced by key source `P` on coalition `s`. -/
@[expose] noncomputable def viewDist (scheme : AccessScheme Secret Key Party Share)
    (P : PMF Key) (s : Finset Party) (secret : Secret) : PMF ((i : s) → Share i.1) :=
  AccessStructure.viewDistOf P scheme.share s secret

/-- Authorized coalitions reconstruct the secret from their view. -/
theorem reconstruct_view_eq_secret (scheme : AccessScheme Secret Key Party Share)
    (k : Key) (secret : Secret) {s : Finset Party} (hs : scheme.access.authorized s) :
    scheme.reconstruct s (scheme.view s k secret) = secret :=
  scheme.correct k secret s hs

/-- Unauthorized coalitions receive secret-independent view distributions under any allowed
source. -/
theorem viewDist_eq_of_not_authorized (scheme : AccessScheme Secret Key Party Share)
    {P : PMF Key} (hP : P ∈ scheme.sources) {s : Finset Party}
    (hs : ¬ scheme.access.authorized s) (secret₀ secret₁ : Secret) :
    scheme.viewDist P s secret₀ = scheme.viewDist P s secret₁ :=
  scheme.view_indist P hP s hs secret₀ secret₁

/-- Any sub-coalition of an unauthorized coalition is unauthorized. -/
theorem not_authorized_of_subset (scheme : AccessScheme Secret Key Party Share)
    {s t : Finset Party} (hst : s ⊆ t) (ht : ¬ scheme.access.authorized t) :
    ¬ scheme.access.authorized s :=
  scheme.access.not_authorized_of_subset hst ht

/-- Restrict a scheme to a smaller source class `S' ⊆ scheme.sources`. -/
@[expose] def monoSources (scheme : AccessScheme Secret Key Party Share)
    {S' : SourceClass Key} (hsub : S' ⊆ scheme.sources) :
    AccessScheme Secret Key Party Share where
  access := scheme.access
  sources := S'
  share := scheme.share
  reconstruct := scheme.reconstruct
  correct := scheme.correct
  view_indist P hP := scheme.view_indist P (hsub hP)

@[simp]
theorem monoSources_access (scheme : AccessScheme Secret Key Party Share)
    {S' : SourceClass Key} (hsub : S' ⊆ scheme.sources) :
    (scheme.monoSources hsub).access = scheme.access :=
  rfl

@[simp]
theorem monoSources_sources (scheme : AccessScheme Secret Key Party Share)
    {S' : SourceClass Key} (hsub : S' ⊆ scheme.sources) :
    (scheme.monoSources hsub).sources = S' :=
  rfl

/-- Pull back a scheme's key space along `f : Key' → Key` for any source class `S'` whose
pushforward under `f` lies in `scheme.sources`. -/
@[expose] def comapKey {Key' : Type*} (scheme : AccessScheme Secret Key Party Share)
    (f : Key' → Key) (S' : SourceClass Key')
    (hf : ∀ P' ∈ S', P'.map f ∈ scheme.sources) :
    AccessScheme Secret Key' Party Share where
  access := scheme.access
  sources := S'
  share k' := scheme.share (f k')
  reconstruct := scheme.reconstruct
  correct k' := scheme.correct (f k')
  view_indist P' hP' s hs secret₀ secret₁ := by
    have hmap (secret : Secret) :
        AccessStructure.viewDistOf P' (fun k' => scheme.share (f k')) s secret =
          AccessStructure.viewDistOf (P'.map f) scheme.share s secret := by
      simp only [AccessStructure.viewDistOf, PMF.map_comp]
      rfl
    rw [hmap secret₀, hmap secret₁]
    exact scheme.view_indist (P'.map f) (hf P' hP') s hs secret₀ secret₁

@[simp]
theorem comapKey_access {Key' : Type*} (scheme : AccessScheme Secret Key Party Share)
    (f : Key' → Key) (S' : SourceClass Key')
    (hf : ∀ P' ∈ S', P'.map f ∈ scheme.sources) :
    (scheme.comapKey f S' hf).access = scheme.access :=
  rfl

@[simp]
theorem comapKey_sources {Key' : Type*} (scheme : AccessScheme Secret Key Party Share)
    (f : Key' → Key) (S' : SourceClass Key')
    (hf : ∀ P' ∈ S', P'.map f ∈ scheme.sources) :
    (scheme.comapKey f S' hf).sources = S' :=
  rfl

/-- Restrict the secret space via an encoding `enc : Secret' → Secret` with left inverse `dec`. -/
@[expose] def restrictSecret {Secret' : Type*} (scheme : AccessScheme Secret Key Party Share)
    (enc : Secret' → Secret) (dec : Secret → Secret')
    (hinv : Function.LeftInverse dec enc) :
    AccessScheme Secret' Key Party Share where
  access := scheme.access
  sources := scheme.sources
  share k m := scheme.share k (enc m)
  reconstruct s v := dec (scheme.reconstruct s v)
  correct k m s hs := by simp [scheme.correct k (enc m) s hs, hinv m]
  view_indist P hP s hs m₀ m₁ :=
    scheme.view_indist P hP s hs (enc m₀) (enc m₁)

/-- Relabel each party's share alphabet by an equivalence `e : ∀ i, Share i ≃ Share' i`. -/
@[expose] def mapShare {Share' : Party → Type*} (scheme : AccessScheme Secret Key Party Share)
    (e : ∀ i : Party, Share i ≃ Share' i) :
    AccessScheme Secret Key Party Share' where
  access := scheme.access
  sources := scheme.sources
  share k m i := e i (scheme.share k m i)
  reconstruct s v := scheme.reconstruct s fun i => (e i.1).symm (v i)
  correct k m s hs := by
    simp only [Equiv.symm_apply_apply]
    exact scheme.correct k m s hs
  view_indist P hP s hs m₀ m₁ := by
    have hmap (m : Secret) :
        AccessStructure.viewDistOf P (fun k m' i => e i (scheme.share k m' i)) s m =
          (scheme.viewDist P s m).map (fun v i => e i.1 (v i)) := by
      simp only [AccessStructure.viewDistOf, viewDist, PMF.map_comp]
      rfl
    rw [hmap m₀, hmap m₁]
    exact congrArg (PMF.map _) (scheme.view_indist P hP s hs m₀ m₁)

private theorem eqRec_share {Party : Type*} {Share : Party → Type*}
    {a b : Party} (h : a = b) (f : ∀ p, Share p) :
    (h ▸ f a) = f b := by
  subst h
  rfl

/-- Relabel the party type along an equivalence `e : Party' ≃ Party`. -/
@[expose] def relabelParty {Party' : Type*} (scheme : AccessScheme Secret Key Party Share)
    (e : Party' ≃ Party) :
    AccessScheme Secret Key Party' (fun i' => Share (e i')) where
  access :=
    { authorized s' := scheme.access.authorized (s'.map e.toEmbedding)
      mono _ _ hst hs := scheme.access.mono (Finset.map_subset_map.mpr hst) hs }
  sources := scheme.sources
  share k m i' := scheme.share k m (e i')
  reconstruct s' v' :=
    scheme.reconstruct (s'.map e.toEmbedding) fun i =>
      (e.apply_symm_apply i.1) ▸ v' ⟨e.symm i.1, by
        obtain ⟨j', hj', he⟩ := Finset.mem_map.mp i.2
        simpa [← he] using hj'⟩
  correct k m s' hs' := by
    have hcongr :
        (fun i : s'.map e.toEmbedding =>
          (e.apply_symm_apply i.1) ▸
            scheme.share k m (e (e.symm i.1))) =
          fun i : s'.map e.toEmbedding => scheme.share k m i.1 := by
      ext i
      exact eqRec_share (e.apply_symm_apply i.1) (scheme.share k m)
    change scheme.reconstruct (s'.map e.toEmbedding)
        (fun i => (e.apply_symm_apply i.1) ▸ scheme.share k m (e (e.symm i.1))) = m
    rw [hcongr]
    exact scheme.correct k m (s'.map e.toEmbedding) hs'
  view_indist P hP s' hs' m₀ m₁ := by
    let proj : ((i : s'.map e.toEmbedding) → Share i.1) → ((i' : s') → Share (e i')) :=
      fun v i' => v ⟨e i', Finset.mem_map_of_mem e.toEmbedding i'.2⟩
    have hmap (m : Secret) :
        AccessStructure.viewDistOf P (fun k m' i' => scheme.share k m' (e i')) s' m =
          (scheme.viewDist P (s'.map e.toEmbedding) m).map proj := by
      simp only [AccessStructure.viewDistOf, viewDist, PMF.map_comp]
      rfl
    rw [hmap m₀, hmap m₁]
    exact congrArg (PMF.map proj) (scheme.view_indist P hP (s'.map e.toEmbedding) hs' m₀ m₁)

end Operations

section CslibBridge

variable {Secret Key Party S : Type*}

/-- Lift an upstream `Cslib.Crypto.Protocols.SecretSharing.Scheme` into an `AccessScheme` over
the singleton source class `{scheme.gen}`. -/
@[expose] def ofCslibScheme (scheme : Scheme Secret Key Party S) :
    AccessScheme Secret Key Party (fun _ => S) where
  access :=
    { authorized := scheme.authorized
      mono := scheme.authorized_mono }
  sources := SourceClass.singleton scheme.gen
  share := scheme.share
  reconstruct := scheme.reconstruct
  correct := scheme.correct
  view_indist P hP s hs secret₀ secret₁ := by
    rw [Set.mem_singleton_iff.mp hP]
    exact scheme.view_indist s hs secret₀ secret₁

@[simp]
theorem ofCslibScheme_authorized_iff (scheme : Scheme Secret Key Party S) (s : Finset Party) :
    (ofCslibScheme scheme).access.authorized s ↔ scheme.authorized s :=
  Iff.rfl

@[simp]
theorem ofCslibScheme_sources (scheme : Scheme Secret Key Party S) :
    (ofCslibScheme scheme).sources = {scheme.gen} :=
  rfl

/-- Project an `AccessScheme` with uniform share type `S` and an allowed source `P ∈ sources`
back to an upstream `Cslib.Crypto.Protocols.SecretSharing.Scheme`. -/
@[expose] def toCslibScheme (scheme : AccessScheme Secret Key Party (fun _ => S))
    {P : PMF Key} (hP : P ∈ scheme.sources) :
    Scheme Secret Key Party S where
  gen := P
  share := scheme.share
  reconstruct := scheme.reconstruct
  authorized := scheme.access.authorized
  authorized_mono := scheme.access.mono
  correct := scheme.correct
  view_indist s hs := scheme.view_indist P hP s hs

@[simp]
theorem toCslibScheme_gen (scheme : AccessScheme Secret Key Party (fun _ => S))
    {P : PMF Key} (hP : P ∈ scheme.sources) :
    (scheme.toCslibScheme hP).gen = P :=
  rfl

end CslibBridge

end AccessScheme

end Cslib.Crypto.Protocols.SecretSharing
