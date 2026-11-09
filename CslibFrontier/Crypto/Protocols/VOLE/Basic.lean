/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Basic
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Linear
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Uniform

/-!
# Vector Oblivious Linear Evaluation (VOLE), IT-MACs, and VOLE-in-the-Head

Vector Oblivious Linear Evaluation (VOLE) ([BoyleCGIKS2019]; [BaumBMRS2023]) is a two-party
correlation generator over a commutative ring `R`: for a vector length `n`, the sender receives
vectors `(u, v) : (Fin n → R) × (Fin n → R)` and the receiver receives a global scalar MAC key
`Δ : R` together with a tag vector `w : Fin n → R` satisfying the information-theoretic MAC
(IT-MAC) relation

`∀ i, w i = u i * Δ + v i`.

VOLE correlations are additively homomorphic (`VOLECorrelation.add`, `VOLECorrelation.smul`,
`VOLECorrelation.addConst`, `VOLECorrelation.Valid.linearComb`). To commit to an arbitrary secret
witness `x : Fin n → R` using a random VOLE correlation `(u, v)`, the prover sends the correction
vector `δ = x - u` (`voleCommitWitness`), which is uniformly distributed and statistically
independent of `x` (`voleCommitWitness_uniform`, `voleCommitWitness_indep`), and the receiver
adjusts its tags to `w' i = w i + δ i * Δ = x i * Δ + v i` (`voleAdjustReceiver`).

Over a field `F`, IT-MAC openings are unconditionally binding up to soundness error `1 / |F|`:
if a cheating prover opens `x' ≠ x`, at most one global key `Δ ∈ F` accepts the opening
(`voleOpen_unique_delta_of_ne`, `card_filter_voleVerifyOpening_le_one`,
`toOuterMeasure_voleVerifyOpening_le`). Multiplication gates satisfy the Quicksilver / VOLE
degree-2 algebraic identity (`voleMulCheck_sub_eq`, `voleMulCheck`), which collapses to a relation
linear in `Δ` whenever `x * y = z`.

In the VOLE-in-the-head paradigm ([BaumBMRS2023]), the prover emulates the VOLE ideal functionality
in the head and the verifier supplies the global key `Δ` as a public-coin challenge, yielding a
three-move `SigmaProtocol` (`voleInTheHeadSigma`) with completeness, special soundness, and special
honest-verifier zero knowledge.

## Main definitions

* `Cslib.Crypto.Protocols.VOLE.VOLECorrelation`: sender vectors `(u, v)`, receiver key `delta`, and
  receiver tags `w`.
* `Cslib.Crypto.Protocols.VOLE.VOLECorrelation.Valid`: the IT-MAC invariant
  `∀ i, w i = u i * delta + v i`.
* `Cslib.Crypto.Protocols.VOLE.voleSample`, `Cslib.Crypto.Protocols.VOLE.voleIdealDist`:
  deterministic correlation constructor and ideal functionality distribution.
* `Cslib.Crypto.Protocols.VOLE.voleCommitWitness`,
  `Cslib.Crypto.Protocols.VOLE.voleAdjustReceiver`: witness commitment via VOLE mask derandomization
  and receiver tag adjustment.
* `Cslib.Crypto.Protocols.VOLE.voleVerifyOpening`: IT-MAC opening verification predicate.
* `Cslib.Crypto.Protocols.VOLE.voleMulCrossTerm`, `Cslib.Crypto.Protocols.VOLE.voleMulConstTerm`:
  Quicksilver / VOLE degree-2 multiplication check coefficients.
* `Cslib.Crypto.Protocols.VOLE.voleInTheHeadSigma`,
  `Cslib.Crypto.Protocols.VOLE.voleInTheHeadExtract`,
  `Cslib.Crypto.Protocols.VOLE.voleInTheHeadSimulate`: VOLE-in-the-head Sigma protocol for linear
  relations over `ZMod q`.

## Main results

* `Cslib.Crypto.Protocols.VOLE.valid_of_mem_support_voleIdealDist`: every correlation sampled from
  `voleIdealDist` satisfies `Valid`.
* `Cslib.Crypto.Protocols.VOLE.VOLECorrelation.Valid.add`,
  `Cslib.Crypto.Protocols.VOLE.VOLECorrelation.Valid.smul`,
  `Cslib.Crypto.Protocols.VOLE.VOLECorrelation.Valid.addConst`,
  `Cslib.Crypto.Protocols.VOLE.VOLECorrelation.Valid.linearComb`: linear homomorphism of IT-MACs.
* `Cslib.Crypto.Protocols.VOLE.voleCommitWitness_uniform`,
  `Cslib.Crypto.Protocols.VOLE.voleCommitWitness_indep`: perfect hiding of `voleCommitWitness`.
* `Cslib.Crypto.Protocols.VOLE.voleOpen_unique_delta_of_ne`,
  `Cslib.Crypto.Protocols.VOLE.card_filter_voleVerifyOpening_le_one`,
  `Cslib.Crypto.Protocols.VOLE.toOuterMeasure_voleVerifyOpening_le`: IT-MAC unforgeability over a
  field.
* `Cslib.Crypto.Protocols.VOLE.voleMulCheck_sub_eq`, `Cslib.Crypto.Protocols.VOLE.voleMulCheck`:
  degree-2 multiplication check identity.
* `Cslib.Crypto.Protocols.VOLE.voleInTheHeadSigma_complete`,
  `Cslib.Crypto.Protocols.VOLE.voleInTheHeadSigma_specialSoundness`,
  `Cslib.Crypto.Protocols.VOLE.voleInTheHeadSigma_specialHVZK`: completeness, special soundness,
  and special HVZK of `voleInTheHeadSigma`.

## References

* [E. Boyle, G. Couteau, N. Gilboa, Y. Ishai, L. Kohl, P. Rindal, P. Scholl, *Efficient Two-Round
  OT Extension and Silent Non-Interactive Secure Computation*][BoyleCGIKS2019]
* [C. Baum, L. Braun, C. Delpech de Saint Guilhem, M. Klooß, E. Orsini, L. Roy, P. Scholl,
  *Publicly Verifiable Zero-Knowledge and Post-Quantum Signatures from
  VOLE-in-the-Head*][BaumBMRS2023]
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.VOLE

open Probability
open scoped ENNReal

universe u

/-! ### VOLE Correlations and Ideal Functionality -/

/-- A Vector Oblivious Linear Evaluation (VOLE) correlation of length `n` over `R`
([BoyleCGIKS2019]; [BaumBMRS2023]). The sender holds `(u, v)` and the receiver holds
`(delta, w)`. -/
@[ext]
structure VOLECorrelation (R : Type u) (n : ℕ) where
  /-- The sender's vector of authenticated ring elements. -/
  u : Fin n → R
  /-- The sender's vector of additive MAC masks. -/
  v : Fin n → R
  /-- The receiver's global scalar MAC key `Δ`. -/
  delta : R
  /-- The receiver's vector of MAC tags. -/
  w : Fin n → R
  deriving DecidableEq, Fintype

namespace VOLECorrelation

variable {R : Type u} {n : ℕ}

/-- The sender's view `(u, v)` of a VOLE correlation. -/
def senderView (c : VOLECorrelation R n) : (Fin n → R) × (Fin n → R) :=
  (c.u, c.v)

/-- The receiver's view `(Δ, w)` of a VOLE correlation. -/
def receiverView (c : VOLECorrelation R n) : R × (Fin n → R) :=
  (c.delta, c.w)

/-- The VOLE correlation invariant `∀ i, w i = u i * Δ + v i`. -/
def Valid [Mul R] [Add R] (c : VOLECorrelation R n) : Prop :=
  ∀ i, c.w i = c.u i * c.delta + c.v i

instance [Mul R] [Add R] [DecidableEq R] (c : VOLECorrelation R n) : Decidable c.Valid :=
  inferInstanceAs (Decidable (∀ i, c.w i = c.u i * c.delta + c.v i))

end VOLECorrelation

section IdealFunctionality

variable {R : Type u} [CommRing R] {n : ℕ}

/-- Construct a valid VOLE correlation from sender vectors `(u, v)` and receiver key `delta`. -/
def voleSample (u v : Fin n → R) (delta : R) : VOLECorrelation R n where
  u := u
  v := v
  delta := delta
  w i := u i * delta + v i

@[simp]
theorem voleSample_u (u v : Fin n → R) (delta : R) : (voleSample u v delta).u = u := rfl

@[simp]
theorem voleSample_v (u v : Fin n → R) (delta : R) : (voleSample u v delta).v = v := rfl

@[simp]
theorem voleSample_delta (u v : Fin n → R) (delta : R) :
    (voleSample u v delta).delta = delta := rfl

@[simp]
theorem voleSample_w (u v : Fin n → R) (delta : R) (i : Fin n) :
    (voleSample u v delta).w i = u i * delta + v i := rfl

/-- Every correlation constructed by `voleSample` satisfies `VOLECorrelation.Valid`. -/
@[simp]
theorem valid_voleSample (u v : Fin n → R) (delta : R) : (voleSample u v delta).Valid :=
  fun _ => rfl

/-- The ideal VOLE functionality distribution over a finite commutative ring `R`: sample
`u, v : Fin n → R` and `delta : R` independently and uniformly, and set
`w i = u i * delta + v i`. -/
noncomputable def voleIdealDist (R : Type u) [CommRing R] [Fintype R] [Nonempty R] (n : ℕ) :
    PMF (VOLECorrelation R n) := do
  let u ← PMF.uniformOfFintype (Fin n → R)
  let v ← PMF.uniformOfFintype (Fin n → R)
  let delta ← PMF.uniformOfFintype R
  return voleSample u v delta

/-- Every sample in the support of `voleIdealDist R n` satisfies the VOLE invariant `Valid`. -/
theorem valid_of_mem_support_voleIdealDist [Fintype R] [Nonempty R]
    {c : VOLECorrelation R n} (hc : c ∈ (voleIdealDist R n).support) :
    c.Valid := by
  simp only [voleIdealDist, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hc
  obtain ⟨u, -, v, -, delta, -, rfl⟩ := hc
  exact valid_voleSample u v delta

/-- A correlation belongs to the support of `voleIdealDist R n` if and only if it is `Valid`. -/
theorem mem_support_voleIdealDist_iff [Fintype R] [Nonempty R] (c : VOLECorrelation R n) :
    c ∈ (voleIdealDist R n).support ↔ c.Valid := by
  constructor
  · exact valid_of_mem_support_voleIdealDist
  · intro hc
    simp only [voleIdealDist, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
    refine ⟨c.u, PMF.mem_support_uniformOfFintype _, c.v, PMF.mem_support_uniformOfFintype _,
      c.delta, PMF.mem_support_uniformOfFintype _, ?_⟩
    exact (VOLECorrelation.ext (x := voleSample c.u c.v c.delta) (y := c) rfl rfl rfl
      (funext fun i => (hc i).symm)).symm

/-- Under `voleIdealDist R n`, the receiver's global key `delta` is uniformly distributed in `R`. -/
theorem voleIdealDist_map_delta [Fintype R] [Nonempty R] (n : ℕ) :
    (voleIdealDist R n).map VOLECorrelation.delta = PMF.uniformOfFintype R := by
  simp only [pmf_norm, voleIdealDist, voleSample_delta, PMF.bind_const]

end IdealFunctionality

/-! ### Linear Homomorphism and VOLE Witness Commitment -/

namespace VOLECorrelation

variable {R : Type u} [CommRing R] {n : ℕ}

/-- Componentwise addition of two VOLE correlations sharing the same global key `delta`. -/
def add (c₁ c₂ : VOLECorrelation R n) : VOLECorrelation R n where
  u := c₁.u + c₂.u
  v := c₁.v + c₂.v
  delta := c₁.delta
  w := c₁.w + c₂.w

/-- Public scalar multiplication of a VOLE correlation by `a : R`. -/
def smul (a : R) (c : VOLECorrelation R n) : VOLECorrelation R n where
  u := a • c.u
  v := a • c.v
  delta := c.delta
  w := a • c.w

/-- Public constant shift of a VOLE correlation by `a : Fin n → R`: adds `a` to `u` and
`a i * delta` to `w i` while keeping the MAC mask `v` unchanged. -/
def addConst (a : Fin n → R) (c : VOLECorrelation R n) : VOLECorrelation R n where
  u := c.u + a
  v := c.v
  delta := c.delta
  w i := c.w i + a i * c.delta

/-- Componentwise addition preserves `Valid` when both correlations share the same `delta`. -/
theorem Valid.add {c₁ c₂ : VOLECorrelation R n} (h₁ : c₁.Valid) (h₂ : c₂.Valid)
    (hdelta : c₁.delta = c₂.delta) : (c₁.add c₂).Valid := by
  intro i
  simp only [VOLECorrelation.add, Pi.add_apply, h₁ i, h₂ i, ← hdelta]
  ring

/-- Public scalar multiplication preserves `Valid`. -/
theorem Valid.smul {c : VOLECorrelation R n} (hc : c.Valid) (a : R) :
    (c.smul a).Valid := by
  intro i
  simp only [VOLECorrelation.smul, Pi.smul_apply, smul_eq_mul, hc i]
  ring

/-- Public constant addition preserves `Valid`. -/
theorem Valid.addConst {c : VOLECorrelation R n} (hc : c.Valid) (a : Fin n → R) :
    (c.addConst a).Valid := by
  intro i
  simp only [VOLECorrelation.addConst, Pi.add_apply, hc i]
  ring

/-- Any public linear combination `∑ i, coeff i * w i` of valid VOLE tags is a valid IT-MAC tag
for `∑ i, coeff i * u i` with MAC mask `∑ i, coeff i * v i`. -/
theorem Valid.linearComb {c : VOLECorrelation R n} (hc : c.Valid) (coeff : Fin n → R) :
    ∑ i, coeff i * c.w i =
      (∑ i, coeff i * c.u i) * c.delta + ∑ i, coeff i * c.v i := by
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hc i]
  ring

end VOLECorrelation

section WitnessCommitment

variable {R : Type u} [CommRing R] {n : ℕ}

/-- VOLE witness commitment (mask derandomization): to commit to a secret witness `x : Fin n → R`
using a sender VOLE vector `u : Fin n → R`, the prover sends the correction vector `δ = x - u`. -/
def voleCommitWitness (x u : Fin n → R) : Fin n → R :=
  x - u

/-- Receiver tag adjustment: given initial VOLE tags `w : Fin n → R`, correction vector
`d : Fin n → R`, and global key `delta : R`, the receiver computes `w' i = w i + d i * delta`. -/
def voleAdjustReceiver (w d : Fin n → R) (delta : R) : Fin n → R :=
  fun i => w i + d i * delta

/-- Update a VOLE correlation to authenticate a chosen witness `x : Fin n → R` via
`voleCommitWitness` and `voleAdjustReceiver`. -/
def VOLECorrelation.commitWitness (c : VOLECorrelation R n) (x : Fin n → R) :
    VOLECorrelation R n where
  u := x
  v := c.v
  delta := c.delta
  w := voleAdjustReceiver c.w (voleCommitWitness x c.u) c.delta

/-- After `voleCommitWitness` and `voleAdjustReceiver`, the receiver's adjusted tags satisfy the
IT-MAC relation `w' i = x i * delta + v i` for the witness `x`. -/
@[simp]
theorem voleAdjustReceiver_voleCommitWitness {c : VOLECorrelation R n} (hc : c.Valid)
    (x : Fin n → R) (i : Fin n) :
    voleAdjustReceiver c.w (voleCommitWitness x c.u) c.delta i = x i * c.delta + c.v i := by
  simp only [voleAdjustReceiver, voleCommitWitness, Pi.sub_apply, hc i]
  ring

/-- Updating a valid VOLE correlation with any witness `x` via `commitWitness` produces a valid
VOLE correlation authenticating `x`. -/
theorem VOLECorrelation.Valid.commitWitness {c : VOLECorrelation R n} (hc : c.Valid)
    (x : Fin n → R) : (c.commitWitness x).Valid :=
  voleAdjustReceiver_voleCommitWitness hc x

/-- **Perfect hiding of VOLE witness commitment**: for every witness `x : Fin n → R`, when the
sender's VOLE vector `u` is drawn uniformly from `Fin n → R`, the correction message
`voleCommitWitness x u = x - u` is uniformly distributed on `Fin n → R`. -/
theorem voleCommitWitness_uniform [Fintype R] [Nonempty R] (x : Fin n → R) :
    (PMF.uniformOfFintype (Fin n → R)).map (voleCommitWitness x) =
      PMF.uniformOfFintype (Fin n → R) :=
  PMF.uniformOfFintype_map_equiv (Equiv.subLeft x)

/-- **Statistical independence of VOLE witness commitment**: any two witnesses `x₁, x₂ : Fin n → R`
induce identical correction-message distributions under a uniform VOLE mask `u`. -/
theorem voleCommitWitness_indep [Fintype R] [Nonempty R] (x₁ x₂ : Fin n → R) :
    (PMF.uniformOfFintype (Fin n → R)).map (voleCommitWitness x₁) =
      (PMF.uniformOfFintype (Fin n → R)).map (voleCommitWitness x₂) := by
  rw [voleCommitWitness_uniform, voleCommitWitness_uniform]

end WitnessCommitment

/-! ### IT-MAC Opening Verification, Unforgeability, and Degree-2 Multiplication Check -/

section ITMAC

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The receiver accepts an opened value vector `x' : Fin n → R` and MAC tag vector `v' : Fin n → R`
against adjusted tags `w' : Fin n → R` and global key `delta : R` when
`∀ i, w' i = x' i * delta + v' i`. -/
def voleVerifyOpening (w' : Fin n → R) (delta : R) (x' v' : Fin n → R) : Prop :=
  ∀ i, w' i = x' i * delta + v' i

instance [DecidableEq R] (w' : Fin n → R) (delta : R) (x' v' : Fin n → R) :
    Decidable (voleVerifyOpening w' delta x' v') :=
  inferInstanceAs (Decidable (∀ i, w' i = x' i * delta + v' i))

/-- Honest openings of a valid VOLE correlation are always accepted. -/
theorem VOLECorrelation.Valid.voleVerifyOpening {c : VOLECorrelation R n} (hc : c.Valid) :
    VOLE.voleVerifyOpening c.w c.delta c.u c.v :=
  hc

/-- Honest openings after `voleCommitWitness` and `voleAdjustReceiver` are always accepted. -/
theorem voleVerifyOpening_voleAdjustReceiver {c : VOLECorrelation R n} (hc : c.Valid)
    (x : Fin n → R) :
    voleVerifyOpening (voleAdjustReceiver c.w (voleCommitWitness x c.u) c.delta) c.delta x c.v :=
  voleAdjustReceiver_voleCommitWitness hc x

variable {F : Type u} [Field F]

/-- **IT-MAC unforgeability at a disagreed coordinate**: over a field `F`, if the true relation is
`w' i = x i * delta + v i` and a forged opening `(x', v')` with `x' i ≠ x i` also satisfies
`w' i = x' i * delta + v' i`, then `delta` is uniquely determined as
`(v' i - v i) / (x i - x' i)`. -/
theorem voleOpen_unique_delta_of_ne {w' x v x' v' : Fin n → F} {delta : F} {i : Fin n}
    (htrue : w' i = x i * delta + v i) (hforge : w' i = x' i * delta + v' i)
    (hne : x' i ≠ x i) :
    delta = (v' i - v i) / (x i - x' i) := by
  have hsub : (x i - x' i) * delta = v' i - v i := by
    calc (x i - x' i) * delta = (x i * delta + v i) - (x' i * delta + v' i) + (v' i - v i) := by
          ring
      _ = v' i - v i := by rw [← htrue, ← hforge, sub_self, zero_add]
  have hne' : x i - x' i ≠ 0 := sub_ne_zero.mpr hne.symm
  rw [← hsub, mul_div_cancel_left₀ _ hne']

/-- If both `(x, v)` and `(x', v')` pass `voleVerifyOpening w' delta`, then either `x' = x`
(and `v' = v`) or there is a coordinate `i` where `x' i ≠ x i` and
`delta = (v' i - v i) / (x i - x' i)`. -/
theorem voleOpen_forger_eq_or_unique_delta
    {w' x v x' v' : Fin n → F} {delta : F}
    (htrue : voleVerifyOpening w' delta x v) (hforge : voleVerifyOpening w' delta x' v') :
    (x' = x ∧ v' = v) ∨ ∃ i, x' i ≠ x i ∧ delta = (v' i - v i) / (x i - x' i) := by
  by_cases hx : x' = x
  · left
    refine ⟨hx, funext fun i => ?_⟩
    have h1 := htrue i
    have h2 := hforge i
    rw [hx] at h2
    exact add_left_cancel (h2.symm.trans h1)
  · right
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact ⟨i, hi, voleOpen_unique_delta_of_ne (htrue i) (hforge i) hi⟩

/-- For any forged value `x' ≠ x` over a finite field `F`, at most one global key `delta : F`
satisfies the IT-MAC verification equation `∀ i, x i * delta + v i = x' i * delta + v' i`. -/
theorem card_filter_voleVerifyOpening_le_one [Fintype F] [DecidableEq F]
    {x v x' v' : Fin n → F} (hne : x' ≠ x) :
    (Finset.univ.filter fun delta : F =>
      ∀ i, x i * delta + v i = x' i * delta + v' i).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun d₁ hd₁ d₂ hd₂ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd₁ hd₂
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have eq₁ := voleOpen_unique_delta_of_ne (w' := fun j => x j * d₁ + v j) rfl (hd₁ i) hi
  have eq₂ := voleOpen_unique_delta_of_ne (w' := fun j => x j * d₂ + v j) rfl (hd₂ i) hi
  exact eq₁.trans eq₂.symm

/-- **IT-MAC soundness bound**: for any forged witness `x' ≠ x` and tag vector `v'`, the probability
over a uniform global key `delta ← PMF.uniformOfFintype F` that `(x', v')` passes verification is at
most `1 / Fintype.card F`. -/
theorem toOuterMeasure_voleVerifyOpening_le [Fintype F]
    {x v x' v' : Fin n → F} (hne : x' ≠ x) :
    (PMF.uniformOfFintype F).toOuterMeasure
      {delta : F | ∀ i, x i * delta + v i = x' i * delta + v' i} ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype]
  have hcard : (Finset.univ.filter (· ∈ {delta : F |
      ∀ i, x i * delta + v i = x' i * delta + v' i})).card ≤ 1 :=
    card_filter_voleVerifyOpening_le_one hne
  have hcard' : ((Finset.univ.filter (· ∈ {delta : F |
      ∀ i, x i * delta + v i = x' i * delta + v' i})).card : ℝ≥0∞) ≤ 1 := by
    exact_mod_cast hcard
  calc ((Finset.univ.filter (· ∈ {delta : F |
        ∀ i, x i * delta + v i = x' i * delta + v' i})).card : ℝ≥0∞) *
        (Fintype.card F : ℝ≥0∞)⁻¹
      ≤ 1 * (Fintype.card F : ℝ≥0∞)⁻¹ := mul_le_mul_of_nonneg_right hcard' zero_le
    _ = (Fintype.card F : ℝ≥0∞)⁻¹ := one_mul _

end ITMAC

section MulCheck

variable {R : Type u} [CommRing R]

/-- The prover's linear-in-`Δ` coefficient `x * v_y + y * v_x - v_z` in the Quicksilver / VOLE
degree-2 multiplication check ([BaumBMRS2023]). -/
def voleMulCrossTerm (x v_x y v_y v_z : R) : R :=
  x * v_y + y * v_x - v_z

/-- The prover's constant term `v_x * v_y` in the Quicksilver / VOLE degree-2 multiplication
check. -/
def voleMulConstTerm (v_x v_y : R) : R :=
  v_x * v_y

/-- **Algebraic identity for VOLE multiplication check**: for authenticated wires
`w_x = x * delta + v_x`, `w_y = y * delta + v_y`, and `w_z = z * delta + v_z`, the quadratic
combination `w_x * w_y - w_z * delta` decomposes into `(x * y - z) * delta ^ 2` plus a linear
function of `delta`. -/
theorem voleMulCheck_sub_eq {x y z v_x v_y v_z w_x w_y w_z delta : R}
    (hwx : w_x = x * delta + v_x) (hwy : w_y = y * delta + v_y) (hwz : w_z = z * delta + v_z) :
    w_x * w_y - w_z * delta =
      (x * y - z) * delta ^ 2 + voleMulCrossTerm x v_x y v_y v_z * delta +
        voleMulConstTerm v_x v_y := by
  rw [hwx, hwy, hwz]
  simp only [voleMulCrossTerm, voleMulConstTerm]
  ring

/-- **Quicksilver / VOLE degree-2 multiplication check**: when `x * y = z`, the quadratic term
vanishes and `w_x * w_y - w_z * delta` is affine-linear in `delta` with slope
`voleMulCrossTerm x v_x y v_y v_z` and constant term `voleMulConstTerm v_x v_y`. -/
theorem voleMulCheck {x y z v_x v_y v_z w_x w_y w_z delta : R}
    (hwx : w_x = x * delta + v_x) (hwy : w_y = y * delta + v_y) (hwz : w_z = z * delta + v_z)
    (hxyz : x * y = z) :
    w_x * w_y - w_z * delta =
      voleMulCrossTerm x v_x y v_y v_z * delta + voleMulConstTerm v_x v_y := by
  rw [voleMulCheck_sub_eq hwx hwy hwz, sub_eq_zero.mpr hxyz, zero_mul, zero_add]

/-- Over a field `F`, if the prover uses the honest cross and constant terms at a nonzero global
key `delta ≠ 0`, then the multiplication check passes if and only if `x * y = z`. -/
theorem voleMulCheck_iff_of_ne_zero {F : Type u} [Field F]
    {x y z v_x v_y v_z w_x w_y w_z delta : F}
    (hwx : w_x = x * delta + v_x) (hwy : w_y = y * delta + v_y) (hwz : w_z = z * delta + v_z)
    (hdelta : delta ≠ 0) :
    w_x * w_y - w_z * delta =
      voleMulCrossTerm x v_x y v_y v_z * delta + voleMulConstTerm v_x v_y ↔ x * y = z := by
  rw [voleMulCheck_sub_eq hwx hwy hwz]
  constructor
  · intro h
    have hzero : (x * y - z) * delta ^ 2 = 0 := by
      linear_combination h
    rcases mul_eq_zero.mp hzero with hsub | hpow
    · exact sub_eq_zero.mp hsub
    · exact False.elim (pow_ne_zero 2 hdelta hpow)
  · intro hxyz
    rw [sub_eq_zero.mpr hxyz, zero_mul, zero_add]

end MulCheck

/-! ### VOLE-in-the-Head Sigma Protocol -/

section VOLEInTheHead

variable {q n : ℕ} [NeZero q] {Y N C : Type} [AddCommGroup N] [Module (ZMod q) N] [DecidableEq N]

/-- **VOLE-in-the-head Sigma protocol** ([BaumBMRS2023]) for a linear relation
`ψ y x = target y` over `ZMod q` with witness `x : Fin n → ZMod q`:
1. The prover samples a random VOLE mask vector `v ← PMF.uniformOfFintype (Fin n → ZMod q)` and
   commits to the aggregate MAC mask `t = ψ y v : N`.
2. The verifier sends a challenge `c : C`, determining the VOLE global key `Δ = ι c : ZMod q`.
3. The prover emulates the VOLE ideal functionality in the head via `voleSample x v (ι c)` and
   outputs the receiver's VOLE tag vector `w = (voleSample x v (ι c)).w`.
4. The verifier checks that `ψ y w` equals the IT-MAC tag `t + ι c • target y`. -/
noncomputable def voleInTheHeadSigma (ψ : Y → (Fin n → ZMod q) →ₗ[ZMod q] N) (target : Y → N)
    (ι : C ↪ ZMod q) :
    SigmaProtocol (Fin n → ZMod q) Y N C (Fin n → ZMod q) where
  State := Fin n → ZMod q
  commit _ y := (PMF.uniformOfFintype (Fin n → ZMod q)).map fun v => (ψ y v, v)
  respond x _ v c := (voleSample x v (ι c)).w
  verify y t c w := decide (ψ y w = t + ι c • target y)

/-- Witness extractor for `voleInTheHeadSigma` from two accepting conversations with a common
commitment and distinct challenges `c ≠ c'`. -/
def voleInTheHeadExtract (ι : C ↪ ZMod q) :
    Y → N → C → (Fin n → ZMod q) → C → (Fin n → ZMod q) → (Fin n → ZMod q) :=
  SigmaProtocol.linearExtract ι

/-- Simulator for `voleInTheHeadSigma`: samples a uniform VOLE receiver tag vector
`w : Fin n → ZMod q` and solves the IT-MAC verification equation for the commitment `t`. -/
noncomputable def voleInTheHeadSimulate (ψ : Y → (Fin n → ZMod q) →ₗ[ZMod q] N) (target : Y → N)
    (ι : C ↪ ZMod q) (y : Y) (c : C) : PMF (N × (Fin n → ZMod q)) :=
  SigmaProtocol.linearSimulate ψ target ι y c

variable (ψ : Y → (Fin n → ZMod q) →ₗ[ZMod q] N) (target : Y → N) (ι : C ↪ ZMod q)

omit [NeZero q] in
/-- The VOLE-in-the-head response `(voleSample x v (ι c)).w` equals the linear Sigma response
`v + ι c • x`. -/
theorem voleSample_w_eq_linear_respond (x v : Fin n → ZMod q) (c : C) :
    (voleSample x v (ι c)).w = v + ι c • x := by
  ext i
  simp only [voleSample_w, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- `voleInTheHeadSigma` coincides with `SigmaProtocol.linear` on `Fin n → ZMod q`. -/
theorem voleInTheHeadSigma_eq_linear :
    voleInTheHeadSigma ψ target ι = SigmaProtocol.linear ψ target ι := by
  simp only [voleInTheHeadSigma, SigmaProtocol.linear]
  congr
  funext x y v c
  exact voleSample_w_eq_linear_respond ι x v c

@[simp]
theorem voleInTheHeadSigma_accepts_iff {y : Y} {t : N} {c : C} {w : Fin n → ZMod q} :
    (voleInTheHeadSigma ψ target ι).Accepts y t c w ↔ ψ y w = t + ι c • target y := by
  simp only [voleInTheHeadSigma_eq_linear, SigmaProtocol.linear_accepts_iff]

/-- Completeness of `voleInTheHeadSigma` ([BaumBMRS2023]). -/
theorem voleInTheHeadSigma_complete :
    (voleInTheHeadSigma ψ target ι).Complete fun x y => ψ y x = target y := by
  rw [voleInTheHeadSigma_eq_linear]
  exact SigmaProtocol.linear_complete ψ target ι

/-- Special soundness of `voleInTheHeadSigma` when `q` is prime ([BaumBMRS2023]). -/
theorem voleInTheHeadSigma_specialSoundness [Fact q.Prime] :
    (voleInTheHeadSigma ψ target ι).SpecialSoundness (fun x y => ψ y x = target y)
      (voleInTheHeadExtract ι) := by
  rw [voleInTheHeadSigma_eq_linear]
  exact SigmaProtocol.linear_specialSoundness ψ target ι

/-- Special honest-verifier zero knowledge of `voleInTheHeadSigma` ([BaumBMRS2023]). -/
theorem voleInTheHeadSigma_specialHVZK :
    (voleInTheHeadSigma ψ target ι).SpecialHVZK (fun x y => ψ y x = target y)
      (voleInTheHeadSimulate ψ target ι) := by
  rw [voleInTheHeadSigma_eq_linear]
  exact SigmaProtocol.linear_specialHVZK ψ target ι

end VOLEInTheHead

end Cslib.Crypto.Protocols.VOLE
