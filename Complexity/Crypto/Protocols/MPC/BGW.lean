/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.MPC.Advantage
public import Complexity.Crypto.Protocols.MPC.Broadcast
public import Complexity.Probability.Uniform
public import Cslib.Crypto.Protocols.SecretSharing.Shamir
import Complexity.Probability.PMF.Uniform
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Shamir Secret-Sharing Homomorphisms and BGW Semi-Honest Arithmetic MPC Gates

This module extends `Cslib.Crypto.Protocols.SecretSharing.Shamir` with the linear and
multiplicative algebraic homomorphisms of Shamir secret sharing, Lagrange weight functional
identities at zero, unauthorized-coalition marginal uniformity, and synchronous $m$-party
Ben-Or–Goldwasser–Wigderson (BGW) semi-honest arithmetic gate protocols over finite fields
([Shamir1979]; [BenOrGoldwasserWigderson1988]; [GennaroRabinRabin1998]; [AsharovLindell2017];
[Goldreich2004]; [KatzLindell2020]):

1. **Shamir Algebraic Homomorphisms and Lagrange Weights at Zero:**
   - Linearity of `Polynomial.tailPolynomial`, `Polynomial.sharingPolynomial`, and `Shamir.share`
     under addition, scalar multiplication, constant shifts, and finite sums (`share_zero`,
     `share_zero_randomness`, `share_add`, `share_smul`, `share_add_const`, `share_sum`).
   - Explicit Lagrange weights at zero (`lagrangeWeightAtZero`) and the linear-functional
     expansion `reconstruct_eq_sum_lagrangeWeightAtZero`, yielding linearity of
     `Polynomial.reconstruct` and `Shamir.reconstruct` (`reconstruct_add`, `reconstruct_smul`,
     `reconstruct_sum`, `shamirReconstruct_add`, `shamirReconstruct_smul`,
     `shamirReconstruct_sum`) and homomorphic secret recovery on authorized coalitions
     (`reconstruct_share_add`, `reconstruct_share_smul`, `reconstruct_share_sum`).
2. **Multiplicative Property and BGW Degree-Reduction Algebra ($2t < |\text{Party}|$):**
   - Multiplying two degree-$\le t$ Shamir sharing polynomials with secrets $a, b$ and randomness
     $r_1, r_2$ produces a degree-$\le 2t$ sharing polynomial with secret $a \cdot b$ and tail
     coefficient vector `mulTailCoeffs a r₁ b r₂`
     (`sharingPolynomial_mul_eq_sharingPolynomial_mulTailCoeffs`, `eval_sharingPolynomial_mul`).
   - When $2t < |\text{Party}|$ (i.e., $t < n / 2$), Lagrange reconstruction of pointwise share
     products `share params r₁ a i * share params r₂ b i`—or of degree-$2t$ zero-randomized
     products `bgwMulStep params r₁ a r₂ b r_z`—recovers $a \cdot b$
     (`reconstruct_mul_share_eq_mul`, `reconstruct_bgwMulStep_eq_mul`).
   - **Commutativity of Lagrange Reconstruction and Shamir Sharing (`bgwDegreeReduceShare_share`):**
     in the Gennaro–Rabin–Rabin simplification of the BGW degree-reduction step
     ([GennaroRabinRabin1998]; [AsharovLindell2017], Section 6.1), each party $j$ reshares its
     degree-$2t$ intermediate value $d_j$ using fresh degree-$t$ Shamir randomness
     $r_{\text{sub}}(j)$, and each party $i$ applies Lagrange reconstruction
     (`bgwDegreeReduceShare`) to its column of received sub-shares. This produces genuine
     degree-$t$ Shamir shares of `Polynomial.reconstruct params.point d` with combined randomness
     `bgwReducedRandomness params r_sub` (`bgwDegreeReduceShare_mul_eq_share`,
     `bgwDegreeReduceShare_bgwMulStep_eq_share`, `reconstruct_bgwDegreeReduceShare_mul_eq_mul`).
3. **Lagrange Share Interpolation and Unauthorized-Coalition Marginal Uniformity:**
   - Given any unauthorized coalition $I \subseteq \text{Party}$ with $|I| \le t$, secret $y$, and
     target coalition shares $\sigma : I \to F$, `interpCoeffs params I hI y σ` interpolates a
     degree-$< t$ tail polynomial whose shares of $y$ restrict to $\sigma$ on $I$
     (`share_interpCoeffs`).
   - Via `uniformOfFintype_map_addHom`, the zero-secret restriction homomorphism
     `shareZeroRestrictHom params I` is surjective for $|I| \le t$, so for every secret $y \in F$
     the marginal distribution of $I$'s Shamir shares under uniform randomness is uniform on
     $I \to F$ (`uniformOfFintype_map_restrict_share`).
4. **Pairwise All-to-All Step Combinator and Synchronous BGW Gate Protocols:**
   - `pairwiseSteps` and `deliverPairwise` generalize `broadcastSteps`
     (`Complexity.Crypto.Protocols.MPC.Broadcast`) to receiver-dependent point-to-point message
     exchange along `broadcastSchedule m spec Msg`, where party $i$'s delivered transcript depends
     only on its own inbox `Fin m → Msg` (`evalWith_pairwiseSteps`, `outputAt_pairwiseSteps`).
   - `PerfectSemiHonestPrivateLe` defines $t$-privacy (`I.card ≤ t`) in the synchronous MPC
     framework of `Complexity.Crypto.Protocols.MPC.Basic`, with deterministic bridge
     `perfectSemiHonestPrivateLe_of_deterministic`, proper-coalition specialization
     `PerfectSemiHonestPrivateLe.proper_of_succ_eq`, and zero-advantage bridge
     `PerfectSemiHonestPrivateLe.semiHonestAdvantage_eq_zero`.
   - `bgwDegreeReductionProtocol` formalizes the 1-round $m$-party BGW degree-reduction
     multiplication gate over `noOracleSpec`: we prove that every supported execution on degree-$t$
     shares of $a, b$ ($2t < m$) outputs degree-$t$ Shamir shares of $a \cdot b$
     (`output_bgwDegreeReductionProtocol_eq_share_mul`,
     `reconstruct_output_bgwDegreeReductionProtocol_eq_mul`), and that for every coalition $I$ with
     $|I| \le t$, the marginal distribution of $I$'s views equals `bgwDegreeReductionViewSim`
     (`map_restrict_evalWith_bgwDegreeReductionProtocol`), independent of honest parties' inputs.
   - `bgwSumProtocol` formalizes the 2-round $m$-party BGW input-sharing, local addition, and
     output-reconstruction protocol over `noOracleSpec`, proving exact output correctness
     (`output_bgwSumProtocol`) and full joint view-and-output $t$-privacy
     (`perfectSemiHonestPrivateLe_bgwSum`) for all coalitions $I$ with $|I| \le t$.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.BGW.lagrangeWeightAtZero`: explicit Lagrange interpolation weight at
  `0` for evaluation points `x : ι → F`.
* `Cslib.Crypto.Protocols.MPC.BGW.mulTailPolynomial`,
  `Cslib.Crypto.Protocols.MPC.BGW.mulTailCoeffs`,
  `Cslib.Crypto.Protocols.MPC.BGW.bgwMulStep`: degree-$2t$ product tail polynomial, coefficient
  vector, and degree-$2t$ zero-randomized BGW multiplication step.
* `Cslib.Crypto.Protocols.MPC.BGW.bgwReducedRandomness`,
  `Cslib.Crypto.Protocols.MPC.BGW.bgwDegreeReduceShare`: Lagrange-recombined degree-$t$ randomness
  and BGW degree-reduction share recombination.
* `Cslib.Crypto.Protocols.MPC.BGW.interpTailPolynomial`,
  `Cslib.Crypto.Protocols.MPC.BGW.interpCoeffs`,
  `Cslib.Crypto.Protocols.MPC.BGW.shareZeroRestrictHom`: Lagrange tail interpolation and
  zero-secret coalition restriction homomorphism.
* `Cslib.Crypto.Protocols.MPC.BGW.pairwiseSteps`,
  `Cslib.Crypto.Protocols.MPC.BGW.deliverPairwise`: synchronous point-to-point all-to-all step
  combinator and inbox-indexed received transcript.
* `Cslib.Crypto.Protocols.MPC.BGW.PerfectSemiHonestPrivateLe`: threshold ($t$-private) perfect
  semi-honest MPC privacy against coalitions `I` with `I.card ≤ t`.
* `Cslib.Crypto.Protocols.MPC.BGW.bgwDegreeReductionProtocol`,
  `Cslib.Crypto.Protocols.MPC.BGW.bgwDegreeReductionViewSim`: 1-round synchronous $m$-party BGW
  degree-reduction multiplication gate protocol and $t$-private coalition view simulator.
* `Cslib.Crypto.Protocols.MPC.BGW.bgwSumSchedule`,
  `Cslib.Crypto.Protocols.MPC.BGW.bgwSumFunctionality`,
  `Cslib.Crypto.Protocols.MPC.BGW.bgwSumProtocol`,
  `Cslib.Crypto.Protocols.MPC.BGW.bgwSumSim`: 2-round synchronous $m$-party BGW sum protocol and
  $t$-private coalition simulator.

## Main results

* `Cslib.Crypto.Protocols.MPC.BGW.share_add`,
  `Cslib.Crypto.Protocols.MPC.BGW.share_smul`,
  `Cslib.Crypto.Protocols.MPC.BGW.share_sum`,
  `Cslib.Crypto.Protocols.MPC.BGW.reconstruct_eq_sum_lagrangeWeightAtZero`,
  `Cslib.Crypto.Protocols.MPC.BGW.reconstruct_add`,
  `Cslib.Crypto.Protocols.MPC.BGW.reconstruct_smul`,
  `Cslib.Crypto.Protocols.MPC.BGW.reconstruct_sum`: linearity of Shamir sharing and Lagrange
  reconstruction.
* `Cslib.Crypto.Protocols.MPC.BGW.sharingPolynomial_mul_eq_sharingPolynomial_mulTailCoeffs`,
  `Cslib.Crypto.Protocols.MPC.BGW.reconstruct_mul_share_eq_mul`,
  `Cslib.Crypto.Protocols.MPC.BGW.reconstruct_bgwMulStep_eq_mul`: multiplicative property of
  Shamir shares for $2t < |\text{Party}|$.
* `Cslib.Crypto.Protocols.MPC.BGW.bgwDegreeReduceShare_share`,
  `Cslib.Crypto.Protocols.MPC.BGW.bgwDegreeReduceShare_mul_eq_share`,
  `Cslib.Crypto.Protocols.MPC.BGW.reconstruct_bgwDegreeReduceShare_mul_eq_mul`: commutativity of
  Lagrange reconstruction with Shamir sharing and correctness of BGW degree reduction.
* `Cslib.Crypto.Protocols.MPC.BGW.share_interpCoeffs`,
  `Cslib.Crypto.Protocols.MPC.BGW.uniformOfFintype_map_restrict_share`: Lagrange share
  interpolation and marginal uniformity of unauthorized coalitions ($|I| \le t$).
* `Cslib.Crypto.Protocols.MPC.BGW.evalWith_pairwiseSteps`,
  `Cslib.Crypto.Protocols.MPC.BGW.outputAt_pairwiseSteps`: structural evaluation and output rules
  for `pairwiseSteps`.
* `Cslib.Crypto.Protocols.MPC.BGW.output_bgwDegreeReductionProtocol_eq_share_mul`,
  `Cslib.Crypto.Protocols.MPC.BGW.reconstruct_output_bgwDegreeReductionProtocol_eq_mul`,
  `Cslib.Crypto.Protocols.MPC.BGW.map_restrict_evalWith_bgwDegreeReductionProtocol`: degree-$t$
  output correctness and coalition view simulation of `bgwDegreeReductionProtocol`.
* `Cslib.Crypto.Protocols.MPC.BGW.output_bgwSumProtocol`,
  `Cslib.Crypto.Protocols.MPC.BGW.perfectSemiHonestPrivateLe_bgwSum`: output correctness and
  full joint view-and-output $t$-privacy of `bgwSumProtocol`.

## References

* [A. Shamir, *How to Share a Secret*][Shamir1979].
* [M. Ben-Or, S. Goldwasser, A. Wigderson, *Completeness Theorems for Non-Cryptographic
  Fault-Tolerant Distributed Computation*][BenOrGoldwasserWigderson1988].
* [R. Gennaro, M. O. Rabin, T. Rabin, *Simplified VSS and Fast-Track Multiparty Computations with
  Applications to Threshold Cryptography*][GennaroRabinRabin1998].
* [G. Asharov, Y. Lindell, *A Full Proof of the BGW Protocol for Perfectly Secure Multiparty
  Computation*][AsharovLindell2017].
* [O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*][Goldreich2004],
  Chapter 7.
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020].
-/

public section

namespace Cslib.Crypto.Protocols.MPC.BGW

open Cslib.Probability Cslib.ProbComp Cslib.Crypto Cslib.Crypto.Protocols.MPC
open Cslib.Crypto.Protocols.SecretSharing Cslib.Crypto.Protocols.SecretSharing.Shamir
open scoped ENNReal NNReal

section ShamirAlgebra

variable {F Party : Type*} [Field F] [Fintype Party]

/-! ### 1. Shamir secret-sharing algebraic homomorphisms and Lagrange weights at zero -/

/-- `Polynomial.tailPolynomial` maps the zero coefficient vector to the zero polynomial. -/
@[simp] theorem tailPolynomial_zero (n : ℕ) :
    Polynomial.tailPolynomial (F := F) n 0 = 0 := by
  simp [Polynomial.tailPolynomial]

/-- `Polynomial.tailPolynomial` is `F`-linear with respect to scalar multiplication. -/
theorem tailPolynomial_smul (n : ℕ) (c : F) (a : Fin n → F) :
    Polynomial.tailPolynomial (F := F) n (c • a) = c • Polynomial.tailPolynomial n a := by
  simp [Polynomial.tailPolynomial]

/-- `Polynomial.tailPolynomial` commutes with finite sums of coefficient vectors. -/
theorem tailPolynomial_sum {ι : Type*} (S : Finset ι) (n : ℕ) (f : ι → Fin n → F) :
    Polynomial.tailPolynomial (F := F) n (∑ j ∈ S, f j) =
      ∑ j ∈ S, Polynomial.tailPolynomial n (f j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert _ _ hnotMem ih =>
    rw [Finset.sum_insert hnotMem, Polynomial.tailPolynomial_add, ih, Finset.sum_insert hnotMem]

/-- The sharing polynomial with zero secret and zero tail is the zero polynomial. -/
@[simp] theorem sharingPolynomial_zero :
    Polynomial.sharingPolynomial (0 : F) 0 = 0 := by
  simp [Polynomial.sharingPolynomial]

/-- `Polynomial.sharingPolynomial` is additive in the secret and tail polynomial. -/
theorem sharingPolynomial_add (s₁ s₂ : F) (t₁ t₂ : _root_.Polynomial F) :
    Polynomial.sharingPolynomial (s₁ + s₂) (t₁ + t₂) =
      Polynomial.sharingPolynomial s₁ t₁ + Polynomial.sharingPolynomial s₂ t₂ := by
  simp only [Polynomial.sharingPolynomial, map_add]
  ring

/-- `Polynomial.sharingPolynomial` is homogeneous under scalar multiplication by `c : F`. -/
theorem sharingPolynomial_smul (c s : F) (t : _root_.Polynomial F) :
    Polynomial.sharingPolynomial (c * s) (c • t) =
      c • Polynomial.sharingPolynomial s t := by
  simp only [Polynomial.sharingPolynomial, _root_.Polynomial.smul_eq_C_mul, map_mul]
  ring

/-- `Polynomial.sharingPolynomial` commutes with finite sums of secrets and tail polynomials. -/
theorem sharingPolynomial_sum {ι : Type*} (S : Finset ι)
    (s : ι → F) (t : ι → _root_.Polynomial F) :
    Polynomial.sharingPolynomial (∑ j ∈ S, s j) (∑ j ∈ S, t j) =
      ∑ j ∈ S, Polynomial.sharingPolynomial (s j) (t j) := by
  simp only [Polynomial.sharingPolynomial, map_sum, Finset.mul_sum, Finset.sum_add_distrib]

/-- Sharing secret `s` with zero randomness gives constant share `s` at every party. -/
@[simp] theorem share_zero_randomness (params : Params F Party) (s : F) (i : Party) :
    share params 0 s i = s := by
  simp [share]

/-- Sharing secret `0` with zero randomness gives share `0` at every party. -/
theorem share_zero (params : Params F Party) (i : Party) :
    share params 0 0 i = 0 :=
  share_zero_randomness params 0 i

/-- Additive homomorphism of Shamir sharing ([AsharovLindell2017], Section 4.1, addition gates):
adding two share values at party `i` produces party `i`'s share of `s₁ + s₂` under randomness
`r₁ + r₂`. -/
theorem share_add (params : Params F Party) (r₁ r₂ : Randomness params) (s₁ s₂ : F) (i : Party) :
    share params (r₁ + r₂) (s₁ + s₂) i = share params r₁ s₁ i + share params r₂ s₂ i := by
  simp only [share, Polynomial.sharingPolynomial_eval, Polynomial.tailPolynomial_add,
    _root_.Polynomial.eval_add]
  ring

/-- Scalar-multiplication homomorphism of Shamir sharing: scaling party `i`'s share by `c`
produces party `i`'s share of `c * s` under randomness `c • r`. -/
theorem share_smul (params : Params F Party) (c : F) (r : Randomness params) (s : F) (i : Party) :
    share params (c • r) (c * s) i = c * share params r s i := by
  simp only [share, Polynomial.sharingPolynomial_eval, tailPolynomial_smul,
    _root_.Polynomial.eval_smul, smul_eq_mul]
  ring

/-- Adding a public constant `c` to party `i`'s share shifts the shared secret by `c` under the
same randomness `r`. -/
theorem share_add_const (params : Params F Party) (r : Randomness params) (s c : F) (i : Party) :
    share params r (s + c) i = share params r s i + c := by
  simp only [share, Polynomial.sharingPolynomial_eval]
  ring

/-- Multi-party summation homomorphism of Shamir sharing: summing shares across a finite index set
`S` yields the share of `∑ j ∈ S, s j` under randomness `∑ j ∈ S, r j`. -/
theorem share_sum {ι : Type*} (S : Finset ι) (params : Params F Party)
    (r : ι → Randomness params) (s : ι → F) (i : Party) :
    share params (∑ j ∈ S, r j) (∑ j ∈ S, s j) i =
      ∑ j ∈ S, share params (r j) (s j) i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert _ _ hnotMem ih =>
    rw [Finset.sum_insert hnotMem, Finset.sum_insert hnotMem, share_add, ih,
      Finset.sum_insert hnotMem]

/-- Explicit Lagrange interpolation weight at `0` for evaluation points `x : ι → F`: the constant
coefficient of the `i`-th Lagrange basis polynomial over `Finset.univ`. -/
noncomputable def lagrangeWeightAtZero {ι : Type*} [Fintype ι] (x : ι → F) (i : ι) : F :=
  open scoped Classical in
  (_root_.Lagrange.basis Finset.univ x i).constantCoeff

/-- `Polynomial.reconstruct` is the `F`-linear combination of share values weighted by
`lagrangeWeightAtZero`. -/
theorem reconstruct_eq_sum_lagrangeWeightAtZero {ι : Type*} [Fintype ι] (x σ : ι → F) :
    Polynomial.reconstruct x σ = ∑ i : ι, σ i * lagrangeWeightAtZero x i := by
  classical
  simp [Polynomial.reconstruct, _root_.Lagrange.interpolate_apply, lagrangeWeightAtZero,
    _root_.Polynomial.constantCoeff_apply]

/-- Reconstructing the zero share vector returns `0`. -/
@[simp] theorem reconstruct_zero {ι : Type*} [Fintype ι] (x : ι → F) :
    Polynomial.reconstruct x (0 : ι → F) = 0 := by
  simp [reconstruct_eq_sum_lagrangeWeightAtZero]

/-- `Polynomial.reconstruct` is additive in the share vector `σ`. -/
theorem reconstruct_add {ι : Type*} [Fintype ι] (x σ₁ σ₂ : ι → F) :
    Polynomial.reconstruct x (σ₁ + σ₂) =
      Polynomial.reconstruct x σ₁ + Polynomial.reconstruct x σ₂ := by
  simp only [reconstruct_eq_sum_lagrangeWeightAtZero, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]

/-- `Polynomial.reconstruct` is homogeneous with respect to scalar multiplication. -/
theorem reconstruct_smul {ι : Type*} [Fintype ι] (x : ι → F) (c : F) (σ : ι → F) :
    Polynomial.reconstruct x (c • σ) = c * Polynomial.reconstruct x σ := by
  simp only [reconstruct_eq_sum_lagrangeWeightAtZero, Pi.smul_apply, smul_eq_mul, mul_assoc,
    ← Finset.mul_sum]

/-- `Polynomial.reconstruct` commutes with finite sums of share vectors. -/
theorem reconstruct_sum {ι κ : Type*} [Fintype ι] (S : Finset κ) (x : ι → F) (σ : κ → ι → F) :
    Polynomial.reconstruct x (∑ k ∈ S, σ k) =
      ∑ k ∈ S, Polynomial.reconstruct x (σ k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert _ _ hnotMem ih =>
    rw [Finset.sum_insert hnotMem, reconstruct_add, ih, Finset.sum_insert hnotMem]

/-- `Shamir.reconstruct` is additive in the coalition's share vector. -/
theorem shamirReconstruct_add (params : Params F Party) (s : Finset Party) (σ₁ σ₂ : s → F) :
    reconstruct params s (σ₁ + σ₂) = reconstruct params s σ₁ + reconstruct params s σ₂ :=
  reconstruct_add (fun i : s => params.point i) σ₁ σ₂

/-- `Shamir.reconstruct` commutes with scalar multiplication of the coalition's share vector. -/
theorem shamirReconstruct_smul (params : Params F Party) (s : Finset Party) (c : F) (σ : s → F) :
    reconstruct params s (c • σ) = c * reconstruct params s σ :=
  reconstruct_smul (fun i : s => params.point i) c σ

/-- `Shamir.reconstruct` commutes with finite sums of coalition share vectors. -/
theorem shamirReconstruct_sum {κ : Type*} (S : Finset κ) (params : Params F Party)
    (s : Finset Party) (σ : κ → s → F) :
    reconstruct params s (∑ k ∈ S, σ k) = ∑ k ∈ S, reconstruct params s (σ k) :=
  reconstruct_sum S (fun i : s => params.point i) σ

/-- Reconstructing a Shamir sharing across all parties via `Polynomial.reconstruct params.point`
recovers `secretValue`. -/
@[simp] theorem polynomialReconstruct_share_eq_secret (params : Params F Party)
    (coeffs : Randomness params) (secretValue : F) :
    Polynomial.reconstruct params.point (fun i => share params coeffs secretValue i) =
      secretValue := by
  refine Polynomial.reconstruct_sharingPolynomial_eq_secret params.point_injective ?_
  refine lt_of_lt_of_le
    (Polynomial.degree_sharingPolynomial_tailPolynomial_lt_succ
      secretValue params.threshold coeffs) ?_
  exact_mod_cast Nat.succ_le_of_lt params.threshold_lt_card

/-- Reconstructing a Shamir sharing over any authorized coalition `s`
(`params.threshold + 1 ≤ s.card`) recovers `secretValue` directly, without requiring a
`TailSampler`. -/
@[simp] theorem reconstruct_share_eq_secret (params : Params F Party)
    (coeffs : Randomness params) (secretValue : F) {s : Finset Party}
    (hs : authorized params s) :
    reconstruct params s (fun i : s => share params coeffs secretValue i) = secretValue := by
  have hdeg₀ :
      (Polynomial.sharingPolynomial secretValue
          (Polynomial.tailPolynomial params.threshold coeffs)).degree <
        (params.threshold + 1 : WithBot ℕ) :=
    Polynomial.degree_sharingPolynomial_tailPolynomial_lt_succ
      secretValue params.threshold coeffs
  have hdeg :
      (Polynomial.sharingPolynomial secretValue
          (Polynomial.tailPolynomial params.threshold coeffs)).degree <
        Fintype.card s := by
    simp [(lt_of_lt_of_le hdeg₀ (by exact_mod_cast hs) :
      (Polynomial.sharingPolynomial secretValue
        (Polynomial.tailPolynomial params.threshold coeffs)).degree <
          s.card)]
  have hx : Function.Injective (fun i : s => params.point i) := by
    intro i j hij
    exact Subtype.ext (params.point_injective hij)
  simpa [share, reconstruct] using
    Polynomial.reconstruct_sharingPolynomial_eq_secret
      (x := fun i : s => params.point i)
      (secretValue := secretValue)
      (tail := Polynomial.tailPolynomial params.threshold coeffs)
      hx
      hdeg

/-- Reconstructing the pointwise sum of two Shamir sharings over any authorized coalition `s`
recovers the sum of the secrets `s₁ + s₂`. -/
theorem reconstruct_share_add (params : Params F Party) (r₁ r₂ : Randomness params) (s₁ s₂ : F)
    {s : Finset Party} (hs : authorized params s) :
    reconstruct params s (fun i : s => share params r₁ s₁ i + share params r₂ s₂ i) = s₁ + s₂ := by
  have hcongr :
      (fun i : s => share params r₁ s₁ i + share params r₂ s₂ i) =
        fun i : s => share params (r₁ + r₂) (s₁ + s₂) i := by
    ext i
    exact (share_add params r₁ r₂ s₁ s₂ i).symm
  rw [hcongr]
  exact reconstruct_share_eq_secret params (r₁ + r₂) (s₁ + s₂) hs

/-- Reconstructing a scalar multiple of a Shamir sharing over any authorized coalition `s`
recovers `c * secretValue`. -/
theorem reconstruct_share_smul (params : Params F Party) (c : F) (r : Randomness params)
    (secretValue : F) {s : Finset Party} (hs : authorized params s) :
    reconstruct params s (fun i : s => c * share params r secretValue i) = c * secretValue := by
  have hcongr :
      (fun i : s => c * share params r secretValue i) =
        fun i : s => share params (c • r) (c * secretValue) i := by
    ext i
    exact (share_smul params c r secretValue i).symm
  rw [hcongr]
  exact reconstruct_share_eq_secret params (c • r) (c * secretValue) hs

/-- Reconstructing the pointwise sum of a finite family of Shamir sharings over any authorized
coalition `s` recovers the sum of the secrets. -/
theorem reconstruct_share_sum {κ : Type*} (S : Finset κ) (params : Params F Party)
    (r : κ → Randomness params) (sec : κ → F) {s : Finset Party} (hs : authorized params s) :
    reconstruct params s (fun i : s => ∑ k ∈ S, share params (r k) (sec k) i) =
      ∑ k ∈ S, sec k := by
  have hcongr :
      (fun i : s => ∑ k ∈ S, share params (r k) (sec k) i) =
        fun i : s => share params (∑ k ∈ S, r k) (∑ k ∈ S, sec k) i := by
    ext i
    exact (share_sum S params r sec i).symm
  rw [hcongr]
  exact reconstruct_share_eq_secret params (∑ k ∈ S, r k) (∑ k ∈ S, sec k) hs

/-! ### 2. Multiplicative property of Shamir shares and BGW degree-reduction algebra -/

/-- Tail polynomial of the product of two Shamir sharing polynomials
`sharingPolynomial a t₁ * sharingPolynomial b t₂`. -/
noncomputable def mulTailPolynomial (a : F) (t₁ : _root_.Polynomial F)
    (b : F) (t₂ : _root_.Polynomial F) : _root_.Polynomial F :=
  _root_.Polynomial.C a * t₂ + _root_.Polynomial.C b * t₁ + _root_.Polynomial.X * (t₁ * t₂)

/-- Multiplying two Shamir sharing polynomials with secrets `a` and `b` yields a Shamir sharing
polynomial with secret `a * b` and tail `mulTailPolynomial a t₁ b t₂`. -/
theorem sharingPolynomial_mul_sharingPolynomial (a : F) (t₁ : _root_.Polynomial F)
    (b : F) (t₂ : _root_.Polynomial F) :
    Polynomial.sharingPolynomial a t₁ * Polynomial.sharingPolynomial b t₂ =
      Polynomial.sharingPolynomial (a * b) (mulTailPolynomial a t₁ b t₂) := by
  simp only [Polynomial.sharingPolynomial, mulTailPolynomial, map_mul]
  ring

private theorem natDegree_lt_of_degree_lt {p : _root_.Polynomial F} {t : ℕ} (htpos : 0 < t)
    (hp : p.degree < t) : p.natDegree < t := by
  by_cases h0 : p = 0
  · subst h0
    simpa using htpos
  · rw [_root_.Polynomial.degree_eq_natDegree h0] at hp
    exact_mod_cast hp

/-- If `t₁` and `t₂` have degree `< t`, then `mulTailPolynomial a t₁ b t₂` has degree `< 2 * t`. -/
theorem degree_mulTailPolynomial_lt {t : ℕ} (a : F) {t₁ : _root_.Polynomial F}
    (ht₁ : t₁.degree < t) (b : F) {t₂ : _root_.Polynomial F} (ht₂ : t₂.degree < t) :
    (mulTailPolynomial a t₁ b t₂).degree < (2 * t : WithBot ℕ) := by
  rcases Nat.eq_zero_or_pos t with rfl | htpos
  · have ht₁0 : t₁ = 0 := _root_.Polynomial.degree_eq_bot.mp
      (WithBot.lt_coe_bot.mp (by simpa using ht₁))
    have ht₂0 : t₂ = 0 := _root_.Polynomial.degree_eq_bot.mp
      (WithBot.lt_coe_bot.mp (by simpa using ht₂))
    simp [mulTailPolynomial, ht₁0, ht₂0]
  · by_cases hmul : mulTailPolynomial a t₁ b t₂ = 0
    · rw [hmul, _root_.Polynomial.degree_zero]
      exact WithBot.bot_lt_coe (2 * t)
    · have hcast : ((2 * t : ℕ) : WithBot ℕ) = (2 * t : WithBot ℕ) := by norm_cast
      rw [_root_.Polynomial.degree_eq_natDegree hmul, ← hcast]
      have hn1 : t₁.natDegree < t := natDegree_lt_of_degree_lt htpos ht₁
      have hn2 : t₂.natDegree < t := natDegree_lt_of_degree_lt htpos ht₂
      have hterm1 : (_root_.Polynomial.C a * t₂).natDegree < 2 * t := by
        have hle := _root_.Polynomial.natDegree_C_mul_le a t₂
        omega
      have hterm2 : (_root_.Polynomial.C b * t₁).natDegree < 2 * t := by
        have hle := _root_.Polynomial.natDegree_C_mul_le b t₁
        omega
      have hterm3 : (_root_.Polynomial.X * (t₁ * t₂)).natDegree < 2 * t := by
        by_cases h12 : t₁ * t₂ = 0
        · simp [h12, htpos]
        · rw [_root_.Polynomial.natDegree_X_mul h12]
          have hle := _root_.Polynomial.natDegree_mul_le (p := t₁) (q := t₂)
          omega
      have hadd1 := _root_.Polynomial.natDegree_add_le
        (_root_.Polynomial.C a * t₂ + _root_.Polynomial.C b * t₁)
        (_root_.Polynomial.X * (t₁ * t₂))
      have hadd2 := _root_.Polynomial.natDegree_add_le
        (_root_.Polynomial.C a * t₂) (_root_.Polynomial.C b * t₁)
      have hnat : (mulTailPolynomial a t₁ b t₂).natDegree < 2 * t := by
        unfold mulTailPolynomial
        omega
      exact_mod_cast hnat

/-- Coefficient vector in `Fin (2 * t) → F` of the degree-`< 2 * t` tail polynomial of the product
of two degree-$\le t$ Shamir sharing polynomials. -/
noncomputable def mulTailCoeffs {t : ℕ} (a : F) (r₁ : Fin t → F) (b : F) (r₂ : Fin t → F) :
    Fin (2 * t) → F :=
  _root_.Polynomial.degreeLTEquiv F (2 * t)
    ⟨mulTailPolynomial a (Polynomial.tailPolynomial t r₁) b (Polynomial.tailPolynomial t r₂),
      _root_.Polynomial.mem_degreeLT.2
        (by
          have h := degree_mulTailPolynomial_lt a (Polynomial.tailPolynomial_degree_lt t r₁)
            b (Polynomial.tailPolynomial_degree_lt t r₂)
          exact_mod_cast h)⟩

@[simp] theorem tailPolynomial_mulTailCoeffs {t : ℕ} (a : F) (r₁ : Fin t → F)
    (b : F) (r₂ : Fin t → F) :
    Polynomial.tailPolynomial (2 * t) (mulTailCoeffs a r₁ b r₂) =
      mulTailPolynomial a (Polynomial.tailPolynomial t r₁) b (Polynomial.tailPolynomial t r₂) := by
  simp [mulTailCoeffs, Polynomial.tailPolynomial]

/-- Multiplying two degree-$\le t$ Shamir sharing polynomials produces the degree-$\le 2t$ Shamir
sharing polynomial with secret `a * b` and tail coefficients `mulTailCoeffs a r₁ b r₂`. -/
theorem sharingPolynomial_mul_eq_sharingPolynomial_mulTailCoeffs {t : ℕ}
    (a : F) (r₁ : Fin t → F) (b : F) (r₂ : Fin t → F) :
    Polynomial.sharingPolynomial a (Polynomial.tailPolynomial t r₁) *
        Polynomial.sharingPolynomial b (Polynomial.tailPolynomial t r₂) =
      Polynomial.sharingPolynomial (a * b)
        (Polynomial.tailPolynomial (2 * t) (mulTailCoeffs a r₁ b r₂)) := by
  rw [tailPolynomial_mulTailCoeffs, sharingPolynomial_mul_sharingPolynomial]

/-- Pointwise product of party `i`'s degree-$t$ Shamir shares of `a` and `b` equals the evaluation
at `params.point i` of the degree-$\le 2t$ sharing polynomial with secret `a * b` and tail
coefficients `mulTailCoeffs a r₁ b r₂`. -/
theorem eval_sharingPolynomial_mul (params : Params F Party)
    (r₁ r₂ : Randomness params) (a b : F) (i : Party) :
    (Polynomial.sharingPolynomial (a * b)
      (Polynomial.tailPolynomial (2 * params.threshold) (mulTailCoeffs a r₁ b r₂))).eval
        (params.point i) =
      share params r₁ a i * share params r₂ b i := by
  rw [← sharingPolynomial_mul_eq_sharingPolynomial_mulTailCoeffs, _root_.Polynomial.eval_mul]
  rfl

/-- When `2 * params.threshold < Fintype.card Party` ($t < n / 2$), Lagrange reconstruction of the
pointwise product of degree-$t$ Shamir shares over `Party` recovers `a * b`. -/
theorem reconstruct_mul_share_eq_mul (params : Params F Party)
    (h2t : 2 * params.threshold < Fintype.card Party)
    (r₁ r₂ : Randomness params) (a b : F) :
    Polynomial.reconstruct params.point (fun i => share params r₁ a i * share params r₂ b i) =
      a * b := by
  have hcongr :
      (fun i => share params r₁ a i * share params r₂ b i) =
        fun i => (Polynomial.sharingPolynomial (a * b)
          (Polynomial.tailPolynomial (2 * params.threshold)
            (mulTailCoeffs a r₁ b r₂))).eval (params.point i) := by
    ext i
    exact (eval_sharingPolynomial_mul params r₁ r₂ a b i).symm
  rw [hcongr]
  refine Polynomial.reconstruct_sharingPolynomial_eq_secret params.point_injective ?_
  refine lt_of_lt_of_le
    (Polynomial.degree_sharingPolynomial_tailPolynomial_lt_succ
      (a * b) (2 * params.threshold) (mulTailCoeffs a r₁ b r₂)) ?_
  exact_mod_cast Nat.succ_le_of_lt h2t

/-- Local BGW degree-$2t$ zero-randomized multiplication step ([AsharovLindell2017], Section 4.3,
Protocol 4.5, steps 1–2): party `i` multiplies its degree-$t$ shares of `a` and `b` and adds a
degree-$2t$ Shamir share of `0` with randomness `r_z : Fin (2 * params.threshold) → F`. -/
noncomputable def bgwMulStep (params : Params F Party)
    (r₁ : Randomness params) (a : F) (r₂ : Randomness params) (b : F)
    (r_z : Fin (2 * params.threshold) → F) (i : Party) : F :=
  share params r₁ a i * share params r₂ b i +
    (Polynomial.sharingPolynomial 0
      (Polynomial.tailPolynomial (2 * params.threshold) r_z)).eval (params.point i)

/-- `bgwMulStep` evaluates the degree-$\le 2t$ sharing polynomial of `a * b` with tail randomness
`mulTailCoeffs a r₁ b r₂ + r_z`. -/
theorem bgwMulStep_eq_eval_sharingPolynomial (params : Params F Party)
    (r₁ : Randomness params) (a : F) (r₂ : Randomness params) (b : F)
    (r_z : Fin (2 * params.threshold) → F) (i : Party) :
    bgwMulStep params r₁ a r₂ b r_z i =
      (Polynomial.sharingPolynomial (a * b)
        (Polynomial.tailPolynomial (2 * params.threshold)
          (mulTailCoeffs a r₁ b r₂ + r_z))).eval (params.point i) := by
  rw [bgwMulStep, ← eval_sharingPolynomial_mul, ← _root_.Polynomial.eval_add,
    ← sharingPolynomial_add, add_zero, ← Polynomial.tailPolynomial_add]

/-- When `2 * params.threshold < Fintype.card Party` ($t < n / 2$), Lagrange reconstruction of
`bgwMulStep` across all parties recovers `a * b`. -/
theorem reconstruct_bgwMulStep_eq_mul (params : Params F Party)
    (h2t : 2 * params.threshold < Fintype.card Party)
    (r₁ : Randomness params) (a : F) (r₂ : Randomness params) (b : F)
    (r_z : Fin (2 * params.threshold) → F) :
    Polynomial.reconstruct params.point (bgwMulStep params r₁ a r₂ b r_z) = a * b := by
  have hcongr :
      bgwMulStep params r₁ a r₂ b r_z =
        fun i => (Polynomial.sharingPolynomial (a * b)
          (Polynomial.tailPolynomial (2 * params.threshold)
            (mulTailCoeffs a r₁ b r₂ + r_z))).eval (params.point i) := by
    ext i
    exact bgwMulStep_eq_eval_sharingPolynomial params r₁ a r₂ b r_z i
  rw [hcongr]
  refine Polynomial.reconstruct_sharingPolynomial_eq_secret params.point_injective ?_
  refine lt_of_lt_of_le
    (Polynomial.degree_sharingPolynomial_tailPolynomial_lt_succ
      (a * b) (2 * params.threshold) (mulTailCoeffs a r₁ b r₂ + r_z)) ?_
  exact_mod_cast Nat.succ_le_of_lt h2t

/-- Combined degree-$t$ Shamir randomness resulting from Lagrange recombination of per-party
resharing polynomials `r_sub : Party → Randomness params` ([GennaroRabinRabin1998];
[AsharovLindell2017], Section 6.1). -/
noncomputable def bgwReducedRandomness (params : Params F Party)
    (r_sub : Party → Randomness params) : Randomness params :=
  ∑ j : Party, lagrangeWeightAtZero params.point j • r_sub j

/-- BGW degree-reduction recombination step ([GennaroRabinRabin1998]; [AsharovLindell2017],
Section 6.1): party `i` applies Lagrange reconstruction at zero (`Polynomial.reconstruct
params.point`) to the column `j ↦ subShares j i` of sub-shares sent to `i`. -/
noncomputable def bgwDegreeReduceShare (params : Params F Party)
    (subShares : Party → Party → F) (i : Party) : F :=
  Polynomial.reconstruct params.point (fun j => subShares j i)

/-- **Commutativity of Lagrange Reconstruction and Shamir Sharing** ([GennaroRabinRabin1998];
[AsharovLindell2017], Section 6.1): when each party `j` shares its intermediate value `d j` using
degree-$t$ Shamir randomness `r_sub j`, applying `bgwDegreeReduceShare` at party `i` yields party
`i`'s degree-$t$ Shamir share of `Polynomial.reconstruct params.point d` under randomness
`bgwReducedRandomness params r_sub`. -/
theorem bgwDegreeReduceShare_share (params : Params F Party)
    (r_sub : Party → Randomness params) (d : Party → F) (i : Party) :
    bgwDegreeReduceShare params (fun j k => share params (r_sub j) (d j) k) i =
      share params (bgwReducedRandomness params r_sub)
        (Polynomial.reconstruct params.point d) i := by
  rw [bgwDegreeReduceShare, reconstruct_eq_sum_lagrangeWeightAtZero,
    bgwReducedRandomness, reconstruct_eq_sum_lagrangeWeightAtZero]
  have hsum := share_sum Finset.univ params
    (fun j => lagrangeWeightAtZero params.point j • r_sub j)
    (fun j => lagrangeWeightAtZero params.point j * d j) i
  have hsum' :
      (∑ j : Party, lagrangeWeightAtZero params.point j * d j) =
        ∑ j : Party, d j * lagrangeWeightAtZero params.point j := by
    refine Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [← hsum', hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [share_smul, mul_comm]

/-- When `2 * params.threshold < Fintype.card Party`, BGW degree reduction on the unmasked product
shares `d j = share params r₁ a j * share params r₂ b j` produces a genuine degree-$t$ Shamir
sharing of `a * b` ([GennaroRabinRabin1998]; [AsharovLindell2017], Section 6.1). -/
theorem bgwDegreeReduceShare_mul_eq_share (params : Params F Party)
    (h2t : 2 * params.threshold < Fintype.card Party)
    (r₁ r₂ : Randomness params) (a b : F)
    (r_sub : Party → Randomness params) (i : Party) :
    bgwDegreeReduceShare params
        (fun j k => share params (r_sub j) (share params r₁ a j * share params r₂ b j) k) i =
      share params (bgwReducedRandomness params r_sub) (a * b) i := by
  rw [bgwDegreeReduceShare_share, reconstruct_mul_share_eq_mul params h2t]

/-- When `2 * params.threshold < Fintype.card Party`, BGW degree reduction on the degree-$2t$
zero-randomized product shares `bgwMulStep params r₁ a r₂ b r_z` also produces a genuine degree-$t$
Shamir sharing of `a * b`. -/
theorem bgwDegreeReduceShare_bgwMulStep_eq_share (params : Params F Party)
    (h2t : 2 * params.threshold < Fintype.card Party)
    (r₁ : Randomness params) (a : F) (r₂ : Randomness params) (b : F)
    (r_z : Fin (2 * params.threshold) → F) (r_sub : Party → Randomness params) (i : Party) :
    bgwDegreeReduceShare params
        (fun j k => share params (r_sub j) (bgwMulStep params r₁ a r₂ b r_z j) k) i =
      share params (bgwReducedRandomness params r_sub) (a * b) i := by
  rw [bgwDegreeReduceShare_share, reconstruct_bgwMulStep_eq_mul params h2t]

/-- Any degree-$t$ authorized coalition `s` (`params.threshold + 1 ≤ s.card`) reconstructs `a * b`
from the BGW degree-reduced shares whenever `2 * params.threshold < Fintype.card Party`. -/
theorem reconstruct_bgwDegreeReduceShare_mul_eq_mul (params : Params F Party)
    (h2t : 2 * params.threshold < Fintype.card Party)
    (r₁ r₂ : Randomness params) (a b : F) (r_sub : Party → Randomness params)
    {s : Finset Party} (hs : authorized params s) :
    reconstruct params s
      (fun i : s => bgwDegreeReduceShare params
        (fun j k => share params (r_sub j) (share params r₁ a j * share params r₂ b j) k) i) =
      a * b := by
  have hcongr :
      (fun i : s => bgwDegreeReduceShare params
        (fun j k => share params (r_sub j) (share params r₁ a j * share params r₂ b j) k) i) =
      fun i : s => share params (bgwReducedRandomness params r_sub) (a * b) i := by
    ext i
    exact bgwDegreeReduceShare_mul_eq_share params h2t r₁ r₂ a b r_sub i
  rw [hcongr]
  exact reconstruct_share_eq_secret params (bgwReducedRandomness params r_sub) (a * b) hs

/-! ### 3. Lagrange share interpolation and unauthorized-coalition marginal uniformity -/

/-- Interpolating tail polynomial of degree `< |I|` that maps each `i : I` to
`(σ i - y) / params.point i`, so that `sharingPolynomial y` evaluates to `σ i` at `params.point i`.
-/
noncomputable def interpTailPolynomial (params : Params F Party) (I : Finset Party)
    (y : F) (σ : I → F) : _root_.Polynomial F :=
  open scoped Classical in
  _root_.Lagrange.interpolate I.attach (fun i : I => params.point i)
    (fun i : I => (σ i - y) / params.point i)

private theorem points_injOn_attach (params : Params F Party) (I : Finset Party) :
    Set.InjOn (fun i : I => params.point i) (I.attach : Finset I) := by
  intro i _ j _ hij
  exact Subtype.ext (params.point_injective hij)

theorem interpTailPolynomial_eval (params : Params F Party) (I : Finset Party)
    (y : F) (σ : I → F) (i : I) :
    (interpTailPolynomial params I y σ).eval (params.point i) =
      (σ i - y) / params.point i := by
  classical
  simpa [interpTailPolynomial] using
    (_root_.Lagrange.eval_interpolate_at_node
      (s := I.attach)
      (v := fun j : I => params.point j)
      (r := fun j : I => (σ j - y) / params.point j)
      (points_injOn_attach params I)
      (Finset.mem_attach I i))

theorem interpTailPolynomial_degree_lt (params : Params F Party) (I : Finset Party)
    (hI : I.card ≤ params.threshold) (y : F) (σ : I → F) :
    (interpTailPolynomial params I y σ).degree < params.threshold := by
  classical
  refine lt_of_lt_of_le
    (_root_.Lagrange.degree_interpolate_lt
      (s := I.attach)
      (v := fun i : I => params.point i)
      (r := fun i : I => (σ i - y) / params.point i)
      (points_injOn_attach params I))
    ?_
  simp [hI]

/-- Coefficient vector in `Randomness params` interpolating target shares `σ : I → F` on an
unauthorized coalition `I` (`I.card ≤ params.threshold`) for secret `y : F`. -/
noncomputable def interpCoeffs (params : Params F Party) (I : Finset Party)
    (hI : I.card ≤ params.threshold) (y : F) (σ : I → F) : Randomness params :=
  _root_.Polynomial.degreeLTEquiv F params.threshold
    ⟨interpTailPolynomial params I y σ,
      _root_.Polynomial.mem_degreeLT.2 (interpTailPolynomial_degree_lt params I hI y σ)⟩

@[simp] theorem tailPolynomial_interpCoeffs (params : Params F Party) (I : Finset Party)
    (hI : I.card ≤ params.threshold) (y : F) (σ : I → F) :
    Polynomial.tailPolynomial params.threshold (interpCoeffs params I hI y σ) =
      interpTailPolynomial params I y σ := by
  simp [interpCoeffs, Polynomial.tailPolynomial]

/-- Sharing secret `y` with randomness `interpCoeffs params I hI y σ` reproduces `σ i` at every
coalition member `i : I`. -/
@[simp] theorem share_interpCoeffs (params : Params F Party) (I : Finset Party)
    (hI : I.card ≤ params.threshold) (y : F) (σ : I → F) (i : I) :
    share params (interpCoeffs params I hI y σ) y i = σ i := by
  unfold share
  rw [Polynomial.sharingPolynomial_eval, tailPolynomial_interpCoeffs, interpTailPolynomial_eval]
  have hnz : params.point i ≠ 0 := params.point_nonzero i
  field_simp [hnz]
  ring

/-- Additive group homomorphism restricting a zero-secret Shamir sharing to a coalition `I`. -/
noncomputable def shareZeroRestrictHom (params : Params F Party) (I : Finset Party) :
    Randomness params →+ (I → F) where
  toFun r i := share params r 0 i
  map_zero' := by ext i; exact share_zero params i
  map_add' r₁ r₂ := by
    ext i
    simpa using share_add params r₁ r₂ 0 0 i

/-- For any unauthorized coalition `I` (`I.card ≤ params.threshold`), `shareZeroRestrictHom` is
surjective. -/
theorem shareZeroRestrictHom_surjective (params : Params F Party) (I : Finset Party)
    (hI : I.card ≤ params.threshold) :
    Function.Surjective (shareZeroRestrictHom params I) := by
  intro σ
  refine ⟨interpCoeffs params I hI 0 σ, ?_⟩
  ext i
  exact share_interpCoeffs params I hI 0 σ i

/-- **Unauthorized-Coalition Marginal Uniformity** ([Shamir1979]; [AsharovLindell2017], Claim 3.2):
for any coalition `I` with `I.card ≤ params.threshold` and any secret `secret : F`, the restriction
of `share params coeffs secret` to `I` under uniform `coeffs : Randomness params` is uniformly
distributed on `I → F`. -/
theorem uniformOfFintype_map_restrict_share [Fintype F] [DecidableEq Party]
    (params : Params F Party) (I : Finset Party) (hI : I.card ≤ params.threshold) (secret : F) :
    (PMF.uniformOfFintype (Randomness params)).map
        (fun coeffs (i : I) => share params coeffs secret i) =
      PMF.uniformOfFintype (I → F) := by
  have hshift :
      (fun coeffs (i : I) => share params coeffs secret i) =
        (Equiv.addLeft (fun _ : I => secret)) ∘ shareZeroRestrictHom params I := by
    ext coeffs i
    have hadd := share_add params 0 coeffs secret 0 i
    rw [zero_add, add_zero, share_zero_randomness] at hadd
    exact hadd
  rw [hshift, ← PMF.map_comp,
    Cslib.Probability.PMF.uniformOfFintype_map_addHom (shareZeroRestrictHom params I)
      (shareZeroRestrictHom_surjective params I hI),
    PMF.uniformOfFintype_map_equiv]

end ShamirAlgebra

/-! ### 4. Pairwise all-to-all step combinator and threshold semi-honest privacy -/

/-- Extract the sender's single-slot vector `Pi.single p.1 msg` at the intended receiver `p.2`
(`0` at all other parties). -/
private def extractPairwise {m : ℕ} {spec : MultiOracleSpec} {Msg : Type} [Zero Msg]
    (p : Fin m × Fin m) (i : Fin m)
    (recv : (broadcastRound spec Msg p).Received i) : Fin m → Msg :=
  if h : i = p.2 then Pi.single p.1 (recv h) else 0

/-- Auxiliary step-by-step execution for pairwise point-to-point message exchange along `L`. -/
private def pairwiseStepsAux {m : ℕ} {spec : MultiOracleSpec} {Msg : Type} [AddCommMonoid Msg]
    {State Out : Fin m → Type} (send : (s r : Fin m) → State s → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i) :
    (L : List (Fin m × Fin m)) →
      Steps (fun i : Fin m => State i × (Fin m → Msg)) Out (broadcastPairsSchedule m spec Msg L)
  | [] => .done fun i st => finish i st.1 st.2
  | p :: L =>
    .message (sender := p.1) (receiver := p.2)
      (fun st => send p.1 p.2 st.1)
      ((pairwiseStepsAux send finish L).mapState fun i ((st_i, acc), recv) =>
        (st_i, acc + extractPairwise p i recv))

/-- Synchronous pairwise point-to-point all-to-all step combinator over `broadcastSchedule`:
every sender `s : Fin m` sends `send s r (st s)` to every receiver `r : Fin m`, and each party `i`
computes `finish i (st i) inbox_i` from the sender-indexed vector `inbox_i : Fin m → Msg` of
messages addressed to `i`. -/
def pairwiseSteps (m : ℕ) {spec : MultiOracleSpec} {Msg : Type} [AddCommMonoid Msg]
    {State Out : Fin m → Type} (send : (s r : Fin m) → State s → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i) :
    Steps State Out (broadcastSchedule m spec Msg) :=
  (pairwiseStepsAux send finish (broadcastPairs m)).mapState fun _ st => (st, 0)

/-- Auxiliary received-transcript constructor for party `i` along `L` from party `i`'s own inbox
`inbox : Fin m → Msg` (where `inbox s` is the message sent by `s` to `i`). -/
private def deliverPairwiseAux {m : ℕ} {spec : MultiOracleSpec} {Msg : Type}
    (inbox : Fin m → Msg) (i : Fin m) :
    (L : List (Fin m × Fin m)) → (broadcastPairsSchedule m spec Msg L).Received i
  | [] => ()
  | p :: L => (fun _ => inbox p.1, deliverPairwiseAux inbox i L)

/-- Received transcript for party `i` along `broadcastSchedule m spec Msg` determined solely by
party `i`'s own inbox `inbox : Fin m → Msg` (`s ↦ message from s to i`). Because
`Round.Received (.message s r Msg) i` has proof domain `i = r`, rounds with `i ≠ r` carry an empty
function domain and do not depend on messages sent to other parties `r ≠ i`. -/
def deliverPairwise {m : ℕ} {spec : MultiOracleSpec} {Msg : Type}
    (inbox : Fin m → Msg) (i : Fin m) :
    (broadcastSchedule m spec Msg).Received i :=
  deliverPairwiseAux (spec := spec) inbox i (broadcastPairs m)

private def sumReceivedPairwise {m : ℕ} {spec : MultiOracleSpec} {Msg : Type}
    [AddCommMonoid Msg] :
    (L : List (Fin m × Fin m)) → (i : Fin m) →
      (broadcastPairsSchedule m spec Msg L).Received i → Fin m → Msg
  | [], _, _ => 0
  | p :: L, i, r => extractPairwise p i r.1 + sumReceivedPairwise L i r.2

private theorem outputAt_pairwiseStepsAux {m : ℕ} {spec : MultiOracleSpec} {Msg : Type}
    [AddCommMonoid Msg] {State Out : Fin m → Type}
    (send : (s r : Fin m) → State s → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i)
    (L : List (Fin m × Fin m)) (i : Fin m) (st_i : State i × (Fin m → Msg))
    (recv_i : (broadcastPairsSchedule m spec Msg L).Received i) :
    (pairwiseStepsAux send finish L).outputAt i st_i recv_i =
      finish i st_i.1 (st_i.2 + sumReceivedPairwise L i recv_i) := by
  induction L generalizing st_i with
  | nil =>
    cases recv_i
    simp [pairwiseStepsAux, Steps.outputAt, sumReceivedPairwise]
  | cons p L ih =>
    rcases recv_i with ⟨r_head, r_tail⟩
    simp [pairwiseStepsAux, Steps.outputAt, ih, sumReceivedPairwise, add_assoc]

private theorem evalWith_pairwiseStepsAux {m : ℕ} {spec : MultiOracleSpec} {Msg : Type}
    [AddCommMonoid Msg] {State Out : Fin m → Type}
    (send : (s r : Fin m) → State s → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i)
    (L : List (Fin m × Fin m)) (W : MultiOracleWorld spec)
    (st : (i : Fin m) → State i × (Fin m → Msg)) :
    (pairwiseStepsAux send finish L).evalWith W st =
      PMF.pure (fun i => deliverPairwiseAux (spec := spec) (fun s => send s i (st s).1) i L) := by
  induction L generalizing st with
  | nil => rfl
  | cons p L ih =>
    simp only [pairwiseStepsAux, Steps.evalWith_message, Steps.evalWith_mapState, ih,
      PMF.pure_map]
    refine congrArg PMF.pure (funext fun i => Prod.ext ?_ rfl)
    funext h
    subst h
    rfl

private theorem sumReceivedPairwise_deliverPairwise {m : ℕ} {spec : MultiOracleSpec}
    {Msg : Type} [AddCommMonoid Msg] (inbox : Fin m → Msg) (i : Fin m) :
    sumReceivedPairwise (spec := spec) (broadcastPairs m) i
      (deliverPairwiseAux (spec := spec) inbox i (broadcastPairs m)) = inbox := by
  have hL : ∀ L : List (Fin m × Fin m),
      sumReceivedPairwise (spec := spec) L i (deliverPairwiseAux (spec := spec) inbox i L) =
        (L.map fun p => extractPairwise (spec := spec) p i (fun _ => inbox p.1)).sum := by
    intro L
    induction L with
    | nil => rfl
    | cons p L ih => simp [sumReceivedPairwise, deliverPairwiseAux, ih]
  rw [hL]
  ext s₀
  have hextr : ∀ p : Fin m × Fin m,
      extractPairwise (spec := spec) p i (fun _ => inbox p.1) =
        if i = p.2 then Pi.single p.1 (inbox p.1) else 0 := by
    intro p
    by_cases h : i = p.2 <;> simp [extractPairwise, h]
  simp [broadcastPairs, hextr, List.flatMap_def, Function.comp_def, ← Fin.sum_univ_def,
    Finset.sum_apply, Pi.single_apply]

/-- Evaluating `pairwiseSteps` in any world `W` deterministically delivers each party `i`'s inbox
`fun s => send s i (st s)`. -/
@[simp] theorem evalWith_pairwiseSteps (m : ℕ) {spec : MultiOracleSpec} {Msg : Type}
    [AddCommMonoid Msg] {State Out : Fin m → Type}
    (send : (s r : Fin m) → State s → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i)
    (W : MultiOracleWorld spec) (st : (i : Fin m) → State i) :
    (pairwiseSteps m send finish).evalWith W st =
      PMF.pure (fun i => deliverPairwise (fun s => send s i (st s)) i) :=
  (Steps.evalWith_mapState _ _ W st).trans
    (evalWith_pairwiseStepsAux send finish (broadcastPairs m) W (fun i => (st i, 0)))

/-- Extracting party `i`'s output after `deliverPairwise inbox i` applies `finish i st_i inbox`. -/
@[simp] theorem outputAt_pairwiseSteps (m : ℕ) {spec : MultiOracleSpec} {Msg : Type}
    [AddCommMonoid Msg] {State Out : Fin m → Type}
    (send : (s r : Fin m) → State s → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i)
    (i : Fin m) (st_i : State i) (inbox : Fin m → Msg) :
    (pairwiseSteps m send finish).outputAt i st_i
        (deliverPairwise (spec := spec) inbox i) =
      finish i st_i inbox := by
  simp [pairwiseSteps, deliverPairwise, outputAt_pairwiseStepsAux,
    sumReceivedPairwise_deliverPairwise]

/-- Threshold ($t$-private) perfect semi-honest privacy against all static coalitions `I` of size
at most `t` (`I.card ≤ t`, following [BenOrGoldwasserWigderson1988] and [AsharovLindell2017],
Definition 2.1; cf. [Goldreich2004], Definition 7.5.1). -/
def PerfectSemiHonestPrivateLe {m : ℕ} {spec : MultiOracleSpec} {sc : Schedule m spec}
    {In Coins Out : Fin m → Type} (t : ℕ) (proto : Protocol m spec sc In Coins Out)
    (W : MultiOracleWorld spec) (f : Functionality m In Out)
    (S : (I : Finset (Fin m)) → CoalitionSimulator sc In Coins Out I) : Prop :=
  ∀ (I : Finset (Fin m)), I.card ≤ t → ∀ (x : (i : Fin m) → In i),
    ProbComp.eval (idealJoint f I (S I) x) = proto.realJoint W I x

/-- Deterministic bridge lemma for threshold semi-honest privacy (cf.
`perfectSemiHonestPrivate_of_deterministic` in `Complexity.Crypto.Protocols.MPC.Basic`): for a
deterministic functionality `f`, matching the marginal coalition view distribution whenever
`I.card ≤ t` together with output correctness on the support yields `PerfectSemiHonestPrivateLe t`.
-/
theorem perfectSemiHonestPrivateLe_of_deterministic
    {m : ℕ} {spec : MultiOracleSpec} {sc : Schedule m spec} {In Coins Out : Fin m → Type}
    (t : ℕ) (proto : Protocol m spec sc In Coins Out) (W : MultiOracleWorld spec)
    (f : ((i : Fin m) → In i) → (i : Fin m) → Out i)
    (S : (I : Finset (Fin m)) → CoalitionSimulator sc In Coins Out I)
    (hView : ∀ I, I.card ≤ t → ∀ x,
      ProbComp.eval (S I (I.restrict x) (I.restrict (f x))) =
        (proto.evalWith W x).map (fun r => I.restrict r.1))
    (hOut : ∀ x r, r ∈ (proto.evalWith W x).support → r.2 = f x) :
    PerfectSemiHonestPrivateLe t proto W (Functionality.ofDeterministic f) S := by
  intro I hI x
  simp only [idealJoint, Functionality.ofDeterministic, pure_bind, bind_pure_comp,
    ProbComp.eval_map, hView I hI x, PMF.map_comp, Protocol.realJoint]
  refine PMF.map_congr_on_support (proto.evalWith W x) _ _ fun r hr => ?_
  simp [Prod.map, hOut x r hr]

/-- When `t + 1 = m`, threshold privacy `PerfectSemiHonestPrivateLe t` implies proper-coalition
privacy `PerfectSemiHonestPrivateProper` (`I ≠ Finset.univ`). -/
theorem PerfectSemiHonestPrivateLe.proper_of_succ_eq
    {m : ℕ} {spec : MultiOracleSpec} {sc : Schedule m spec} {In Coins Out : Fin m → Type}
    {t : ℕ} {proto : Protocol m spec sc In Coins Out} {W : MultiOracleWorld spec}
    {f : Functionality m In Out}
    {S : (I : Finset (Fin m)) → CoalitionSimulator sc In Coins Out I}
    (h : PerfectSemiHonestPrivateLe t proto W f S) (htm : t + 1 = m) :
    PerfectSemiHonestPrivateProper proto W f S := by
  intro I hI x
  have hlt : I.card < m := by
    simpa [Fintype.card_fin] using Finset.card_lt_card (Ne.lt_top hI)
  exact h I (by omega) x

/-- Threshold perfect semi-honest privacy implies zero distinguishing advantage
`semiHonestAdvantage` for every coalition `I` with `I.card ≤ t` and every distinguisher `D`. -/
theorem PerfectSemiHonestPrivateLe.semiHonestAdvantage_eq_zero
    {m : ℕ} {spec : MultiOracleSpec} {sc : Schedule m spec} {In Coins Out : Fin m → Type}
    {t : ℕ} {proto : Protocol m spec sc In Coins Out} {W : MultiOracleWorld spec}
    {f : Functionality m In Out}
    {S : (I : Finset (Fin m)) → CoalitionSimulator sc In Coins Out I}
    (h : PerfectSemiHonestPrivateLe t proto W f S)
    {I : Finset (Fin m)} (hI : I.card ≤ t) (x : (i : Fin m) → In i)
    (D : ((i : I) → PartyView In Coins sc i) × ((i : Fin m) → Out i) → ProbComp Bool) :
    semiHonestAdvantage proto W f I (S I) x D = 0 :=
  (semiHonestAdvantage_eq_zero_iff proto W f I (S I) x).mpr (h I hI x) D

/-! ### 5. Synchronous $m$-party BGW gate protocols and $t$-privacy -/

variable {F : Type} [Field F]

/-- Additive group homomorphism extracting corrupted parties' coins `I → Randomness params` and
honest parties' zero-secret sub-shares `Iᶜ → I → F` from all parties' coins
`Fin m → Randomness params`. -/
private noncomputable def degreeReductionCoinsHom {m : ℕ} (params : Params F (Fin m))
    (I : Finset (Fin m)) :
    (Fin m → Randomness params) →+
      (((i : I) → Randomness params) × ((s : (Iᶜ : Finset (Fin m))) → (I → F))) where
  toFun r := (I.restrict r, fun s i => share params (r s.1) 0 i.1)
  map_zero' := by
    refine Prod.ext rfl ?_
    ext s i
    exact share_zero params i.1
  map_add' r₁ r₂ := by
    refine Prod.ext rfl ?_
    ext s i
    simpa using share_add params (r₁ s.1) (r₂ s.1) 0 0 i.1

private theorem degreeReductionCoinsHom_surjective {m : ℕ} (params : Params F (Fin m))
    (I : Finset (Fin m)) (hI : I.card ≤ params.threshold) :
    Function.Surjective (degreeReductionCoinsHom params I) := by
  rintro ⟨rI, h0⟩
  classical
  refine ⟨fun s => if hs : s ∈ I then rI ⟨s, hs⟩ else interpCoeffs params I hI 0 (h0 ⟨s,
    Finset.mem_compl.mpr hs⟩), ?_⟩
  dsimp only [degreeReductionCoinsHom]
  refine Prod.ext ?_ ?_
  · ext ⟨i, hi⟩ k
    simp [Finset.restrict, hi]
  · ext ⟨s, hs⟩ i
    have hs' : s ∉ I := Finset.mem_compl.mp hs
    simp [hs', share_interpCoeffs]

/-- Additive group homomorphism mapping `r : Fin m → Randomness params` to
`(∑ s, r s, I.restrict r, fun (s : Iᶜ.erase j₀) (i : I) => share params (r s.1) 0 i.1)`. -/
private noncomputable def bgwSumCoinsHom {m : ℕ} (params : Params F (Fin m))
    (I : Finset (Fin m)) (j₀ : Fin m) :
    (Fin m → Randomness params) →+
      (Randomness params × ((i : I) → Randomness params) ×
        ((s : (Iᶜ.erase j₀ : Finset (Fin m))) → (I → F))) where
  toFun r :=
    (∑ s : Fin m, r s, I.restrict r, fun s i => share params (r s.1) 0 i.1)
  map_zero' := by
    refine Prod.ext (by simp) (Prod.ext rfl ?_)
    ext s i
    exact share_zero params i.1
  map_add' r₁ r₂ := by
    refine Prod.ext (by simp [Finset.sum_add_distrib]) (Prod.ext rfl ?_)
    ext s i
    simpa using share_add params (r₁ s.1) (r₂ s.1) 0 0 i.1

private theorem bgwSumCoinsHom_surjective {m : ℕ} (params : Params F (Fin m))
    (I : Finset (Fin m)) (hI : I.card ≤ params.threshold)
    (j₀ : Fin m) (hj₀ : j₀ ∉ I) :
    Function.Surjective (bgwSumCoinsHom params I j₀) := by
  rintro ⟨R_tot, rI, h0⟩
  classical
  let H' : Finset (Fin m) := Iᶜ.erase j₀
  let rBase (s : Fin m) : Randomness params :=
    if hsI : s ∈ I then
      rI ⟨s, hsI⟩
    else if hsH : s ∈ H' then
      interpCoeffs params I hI 0 (h0 ⟨s, hsH⟩)
    else
      0
  let r (s : Fin m) : Randomness params :=
    if s = j₀ then
      R_tot - ∑ s' ∈ Finset.univ.erase j₀, rBase s'
    else
      rBase s
  refine ⟨r, ?_⟩
  simp only [bgwSumCoinsHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
    have hr0 : r j₀ = R_tot - ∑ s' ∈ Finset.univ.erase j₀, rBase s' := by simp [r]
    have hrest : ∑ s' ∈ Finset.univ.erase j₀, r s' = ∑ s' ∈ Finset.univ.erase j₀, rBase s' := by
      refine Finset.sum_congr rfl fun s' hs' => ?_
      have hne : s' ≠ j₀ := (Finset.mem_erase.mp hs').1
      simp [r, hne]
    rw [hr0, hrest, sub_add_cancel]
  · ext ⟨i, hi⟩ k
    have hne : i ≠ j₀ := fun h => hj₀ (h ▸ hi)
    simp [Finset.restrict, r, rBase, hne, hi]
  · ext ⟨s, hsH⟩ i
    have hne : s ≠ j₀ := (Finset.mem_erase.mp hsH).1
    have hsI : s ∉ I := Finset.mem_compl.mp (Finset.mem_erase.mp hsH).2
    simp [r, rBase, H', hne, hsI, share_interpCoeffs]

variable [Fintype F]

private theorem eval_pi_uniform_randomness {m : ℕ} (params : Params F (Fin m)) :
    ProbComp.eval (OracleComp.pi (fun _ : Fin m => ProbComp.uniform (Randomness params))) =
      PMF.uniformOfFintype (Fin m → Randomness params) := by
  rw [ProbComp.eval_pi]
  simp only [ProbComp.eval_uniform]
  exact PMF.pi_uniformOfFintype

/-- 1-round synchronous $m$-party BGW degree-reduction multiplication gate protocol over
`noOracleSpec` ([GennaroRabinRabin1998]; [AsharovLindell2017], Section 6.1):
1. Each party `s : Fin m` holds input share pair `uv_s = (u_s, v_s) : F × F` and samples fresh
   degree-$t$ Shamir randomness `r_s : Randomness params`.
2. Each party `s` sends the sub-share `share params r_s (u_s * v_s) i` to each party `i : Fin m`
   via `pairwiseSteps`.
3. Each party `i` outputs the Lagrange-recombined share
   `Polynomial.reconstruct params.point inbox_i`. -/
noncomputable def bgwDegreeReductionProtocol {m : ℕ} (params : Params F (Fin m)) :
    Protocol m noOracleSpec (broadcastSchedule m noOracleSpec F)
      (fun _ => F × F) (fun _ => Randomness params) (fun _ => F) where
  sampleCoins _ := ProbComp.uniform (Randomness params)
  steps :=
    pairwiseSteps m (spec := noOracleSpec) (Msg := F)
      (State := fun _ => (F × F) × Randomness params)
      (Out := fun _ => F)
      (fun _ rcv (uv_s, r_s) => share params r_s (uv_s.1 * uv_s.2) rcv)
      (fun _ _ inbox => Polynomial.reconstruct params.point inbox)

/-- Construct party `i`'s `PartyView` in `bgwDegreeReductionProtocol` from its input `uv_i`,
its coins `r_i`, and its received sub-share inbox `inbox_i : Fin m → F`. -/
def bgwDegreeReductionViewOf {m : ℕ} (params : Params F (Fin m)) (i : Fin m)
    (uv_i : F × F) (r_i : Randomness params) (inbox_i : Fin m → F) :
    PartyView (fun _ => F × F) (fun _ => Randomness params)
      (broadcastSchedule m noOracleSpec F) i where
  input := uv_i
  coins := r_i
  received := deliverPairwise (spec := noOracleSpec) inbox_i i

theorem evalWith_bgwDegreeReductionProtocol {m : ℕ} (params : Params F (Fin m))
    (uv : Fin m → F × F) :
    (bgwDegreeReductionProtocol params).evalWith noOracleWorld uv =
      (PMF.uniformOfFintype (Fin m → Randomness params)).map fun r =>
        (fun i => bgwDegreeReductionViewOf params i (uv i) (r i)
          (fun s => share params (r s) ((uv s).1 * (uv s).2) i),
         fun i => bgwDegreeReduceShare params
          (fun s k => share params (r s) ((uv s).1 * (uv s).2) k) i) := by
  rw [Protocol.evalWith_eq]
  dsimp only [bgwDegreeReductionProtocol]
  rw [eval_pi_uniform_randomness]
  simp only [evalWith_pairwiseSteps, PMF.pure_map]
  rw [PMF.map]
  refine congrArg (PMF.bind (PMF.uniformOfFintype (Fin m → Randomness params)))
    (funext fun r => congrArg PMF.pure ?_)
  refine Prod.ext (funext fun i => rfl) (funext fun i => ?_)
  simp [Protocol.outputOfView, outputAt_pairwiseSteps, bgwDegreeReduceShare]

/-- Output correctness of `bgwDegreeReductionProtocol`: when `2 * params.threshold < m`
($t < m / 2$) and the inputs `uv` are degree-$t$ Shamir shares of `a` and `b`, every supported
execution outputs a genuine degree-$t$ Shamir sharing of `a * b` under
`bgwReducedRandomness params`. -/
theorem output_bgwDegreeReductionProtocol_eq_share_mul {m : ℕ} (params : Params F (Fin m))
    (h2t : 2 * params.threshold < m)
    (r₁ r₂ : Randomness params) (a b : F)
    {res : ((i : Fin m) → PartyView (fun _ => F × F) (fun _ => Randomness params)
        (broadcastSchedule m noOracleSpec F) i) × (Fin m → F)}
    (hres : res ∈ ((bgwDegreeReductionProtocol params).evalWith noOracleWorld
        (fun i => (share params r₁ a i, share params r₂ b i))).support) :
    res.2 = fun i =>
      share params (bgwReducedRandomness params (fun j => (res.1 j).coins)) (a * b) i := by
  rw [evalWith_bgwDegreeReductionProtocol, PMF.mem_support_map_iff] at hres
  obtain ⟨r, _, rfl⟩ := hres
  ext i
  exact bgwDegreeReduceShare_mul_eq_share params (by simpa [Fintype.card_fin] using h2t)
    r₁ r₂ a b r i

/-- On any supported execution of `bgwDegreeReductionProtocol` with degree-$t$ Shamir shares of
`a` and `b` ($2t < m$), reconstructing the output shares over any degree-$t$ authorized coalition
`s` (`params.threshold + 1 ≤ s.card`) recovers `a * b`. -/
theorem reconstruct_output_bgwDegreeReductionProtocol_eq_mul {m : ℕ} (params : Params F (Fin m))
    (h2t : 2 * params.threshold < m)
    (r₁ r₂ : Randomness params) (a b : F)
    {res : ((i : Fin m) → PartyView (fun _ => F × F) (fun _ => Randomness params)
        (broadcastSchedule m noOracleSpec F) i) × (Fin m → F)}
    (hres : res ∈ ((bgwDegreeReductionProtocol params).evalWith noOracleWorld
        (fun i => (share params r₁ a i, share params r₂ b i))).support)
    {s : Finset (Fin m)} (hs : authorized params s) :
    reconstruct params s (s.restrict res.2) = a * b := by
  rw [output_bgwDegreeReductionProtocol_eq_share_mul params h2t r₁ r₂ a b hres]
  exact reconstruct_share_eq_secret params
    (bgwReducedRandomness params (fun j => (res.1 j).coins)) (a * b) hs

/-- Coalition view simulator for `bgwDegreeReductionProtocol params` ([AsharovLindell2017],
Claim 3.4): given only the coalition's input share pairs `uvI : (i : I) → F × F`, samples uniform
coins `rI` for `i ∈ I` and independent uniform sub-share vectors `hCompl : Iᶜ → I → F` from honest
senders `s ∉ I`, and assembles each corrupted party's inbox. -/
noncomputable def bgwDegreeReductionViewSim {m : ℕ} (params : Params F (Fin m))
    (I : Finset (Fin m)) (uvI : (i : I) → F × F) :
    ProbComp ((i : I) → PartyView (fun _ => F × F) (fun _ => Randomness params)
      (broadcastSchedule m noOracleSpec F) i) := do
  let p ← ProbComp.uniform
    (((i : I) → Randomness params) × ((s : (Iᶜ : Finset (Fin m))) → (I → F)))
  let (rI, hCompl) := p
  return fun i =>
    bgwDegreeReductionViewOf params i.1 (uvI i) (rI i) fun s =>
      if hs : s ∈ I then
        share params (rI ⟨s, hs⟩) ((uvI ⟨s, hs⟩).1 * (uvI ⟨s, hs⟩).2) i.1
      else
        hCompl ⟨s, Finset.mem_compl.mpr hs⟩ i

/-- **$t$-Privacy of BGW Degree-Reduction Views** ([AsharovLindell2017], Claim 3.4): for every
coalition `I` with `I.card ≤ params.threshold` and every input tuple `uv : Fin m → F × F`, the
marginal distribution of `I`'s views in `bgwDegreeReductionProtocol params` equals
`ProbComp.eval (bgwDegreeReductionViewSim params I (I.restrict uv))`, which depends only on
`I.restrict uv` and is independent of all honest parties' input share pairs. -/
theorem map_restrict_evalWith_bgwDegreeReductionProtocol {m : ℕ} (params : Params F (Fin m))
    (I : Finset (Fin m)) (hI : I.card ≤ params.threshold) (uv : Fin m → F × F) :
    ((bgwDegreeReductionProtocol params).evalWith noOracleWorld uv).map (fun r => I.restrict r.1) =
      ProbComp.eval (bgwDegreeReductionViewSim params I (I.restrict uv)) := by
  classical
  rw [evalWith_bgwDegreeReductionProtocol, PMF.map_comp]
  simp only [bgwDegreeReductionViewSim, bind_pure_comp, ProbComp.eval_map, ProbComp.eval_uniform]
  let shift :
      (((i : I) → Randomness params) × ((s : (Iᶜ : Finset (Fin m))) → (I → F))) ≃
      (((i : I) → Randomness params) × ((s : (Iᶜ : Finset (Fin m))) → (I → F))) :=
    Equiv.prodCongr (Equiv.refl _)
      (Equiv.addLeft (fun (s : (Iᶜ : Finset (Fin m))) (_ : I) => (uv s.1).1 * (uv s.1).2))
  have hmap :
      (PMF.uniformOfFintype
        (((i : I) → Randomness params) × ((s : (Iᶜ : Finset (Fin m))) → (I → F)))) =
      (PMF.uniformOfFintype (Fin m → Randomness params)).map
        (shift ∘ degreeReductionCoinsHom params I) := by
    rw [← PMF.map_comp,
      Cslib.Probability.PMF.uniformOfFintype_map_addHom (degreeReductionCoinsHom params I)
        (degreeReductionCoinsHom_surjective params I hI),
      PMF.uniformOfFintype_map_equiv]
  rw [hmap, PMF.map_comp]
  refine congrArg (PMF.map · _) (funext fun r => funext fun ⟨i, hi⟩ => ?_)
  simp only [Function.comp_def, shift, degreeReductionCoinsHom, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, Finset.restrict, Equiv.prodCongr_apply, Equiv.refl_apply,
    Prod.map_fst, Prod.map_snd, Equiv.coe_addLeft]
  refine congrArg (bgwDegreeReductionViewOf params i (uv i) (r i)) (funext fun s => ?_)
  by_cases hs : s ∈ I
  · simp [hs]
  · simp only [hs, ↓reduceDIte, Pi.add_apply]
    have hadd := share_add params 0 (r s) ((uv s).1 * (uv s).2) 0 i
    rw [zero_add, add_zero, share_zero_randomness] at hadd
    exact hadd

/-! ### 6. 2-round synchronous $m$-party BGW sum protocol and full joint $t$-privacy -/

/-- Schedule for `bgwSumProtocol params`: one all-to-all point-to-point Shamir input-sharing phase
followed by one all-to-all broadcast of summed shares. -/
@[expose, reducible] def bgwSumSchedule (m : ℕ) (F : Type) : Schedule m noOracleSpec :=
  broadcastSchedule m noOracleSpec F ++ broadcastSchedule m noOracleSpec F

/-- Deterministic $m$-party functionality returning the sum `∑ j : Fin m, x j` to every party. -/
def bgwSumFunctionality (m : ℕ) : Functionality m (fun _ => F) (fun _ => F) :=
  Functionality.ofDeterministic (fun x _ => ∑ j : Fin m, x j)

/-- 2-round synchronous $m$-party BGW sum protocol over `noOracleSpec`
([AsharovLindell2017], Section 4.2, Protocol 4.1, for a circuit of addition gates):
1. Each party `s : Fin m` samples degree-$t$ Shamir randomness `r_s : Randomness params` and sends
   `share params r_s (x s) rcv` to each receiver `rcv : Fin m` via `pairwiseSteps`.
2. Each party `k : Fin m` sums its received shares `Y_k = ∑ s : Fin m, inbox_k s` and broadcasts
   `Y_k` via `broadcastSteps`.
3. Each party reconstructs `Polynomial.reconstruct params.point Y`. -/
noncomputable def bgwSumProtocol {m : ℕ} (params : Params F (Fin m)) :
    Protocol m noOracleSpec (bgwSumSchedule m F)
      (fun _ => F) (fun _ => Randomness params) (fun _ => F) where
  sampleCoins _ := ProbComp.uniform (Randomness params)
  steps :=
    (pairwiseSteps m (spec := noOracleSpec) (Msg := F)
      (State := fun _ => F × Randomness params)
      (Out := fun _ => Fin m → F)
      (fun _ rcv (x_s, r_s) => share params r_s x_s rcv)
      (fun _ _ inbox => inbox)).append
    (broadcastSteps m (spec := noOracleSpec) (Msg := F)
      (State := fun _ => Fin m → F)
      (Out := fun _ => F)
      (fun _ inbox => ∑ s : Fin m, inbox s)
      (fun _ _ Y => Polynomial.reconstruct params.point Y))

/-- Construct party `i`'s `PartyView` in `bgwSumProtocol` from its input `x_i`, its coins `r_i`,
its Round 1 received share inbox `inbox_i : Fin m → F`, and the Round 2 broadcast vector
`Y : Fin m → F`. -/
def bgwSumViewOf {m : ℕ} (params : Params F (Fin m)) (i : Fin m)
    (x_i : F) (r_i : Randomness params) (inbox_i Y : Fin m → F) :
    PartyView (fun _ => F) (fun _ => Randomness params) (bgwSumSchedule m F) i where
  input := x_i
  coins := r_i
  received :=
    Schedule.Received.append
      (sc₁ := broadcastSchedule m noOracleSpec F)
      (sc₂ := broadcastSchedule m noOracleSpec F)
      (deliverPairwise (spec := noOracleSpec) inbox_i i)
      (deliverBroadcast (spec := noOracleSpec) Y i)

theorem evalWith_bgwSumProtocol {m : ℕ} (params : Params F (Fin m)) (x : Fin m → F) :
    (bgwSumProtocol params).evalWith noOracleWorld x =
      (PMF.uniformOfFintype (Fin m → Randomness params)).map fun r =>
        let inbox : Fin m → Fin m → F := fun i s => share params (r s) (x s) i
        let Y : Fin m → F := fun k => ∑ s : Fin m, share params (r s) (x s) k
        (fun i => bgwSumViewOf params i (x i) (r i) (inbox i) Y,
         fun _ => Polynomial.reconstruct params.point Y) := by
  rw [Protocol.evalWith_eq]
  dsimp only [bgwSumProtocol]
  rw [eval_pi_uniform_randomness]
  simp only [Steps.evalWith_append, evalWith_pairwiseSteps,
    outputAt_pairwiseSteps, evalWith_broadcastSteps, PMF.pure_bind, PMF.pure_map]
  rw [PMF.map]
  refine congrArg (PMF.bind (PMF.uniformOfFintype (Fin m → Randomness params)))
    (funext fun r => congrArg PMF.pure ?_)
  refine Prod.ext (funext fun i => rfl) (funext fun i => ?_)
  simp [Protocol.outputOfView, Steps.outputAt_append, outputAt_pairwiseSteps,
    outputAt_broadcastSteps]

/-- Output correctness of `bgwSumProtocol`: on every execution in the support, every party outputs
`∑ j : Fin m, x j`. -/
theorem output_bgwSumProtocol {m : ℕ} (params : Params F (Fin m)) (x : Fin m → F)
    {res : ((i : Fin m) → PartyView (fun _ => F) (fun _ => Randomness params)
        (bgwSumSchedule m F) i) × (Fin m → F)}
    (hres : res ∈ ((bgwSumProtocol params).evalWith noOracleWorld x).support) :
    res.2 = fun _ => ∑ j : Fin m, x j := by
  rw [evalWith_bgwSumProtocol, PMF.mem_support_map_iff] at hres
  obtain ⟨r, _, rfl⟩ := hres
  ext i₀
  dsimp only
  have hY :
      (fun k : Fin m => ∑ s : Fin m, share params (r s) (x s) k) =
        fun k : Fin m => share params (∑ s : Fin m, r s) (∑ s : Fin m, x s) k := by
    ext k
    exact (share_sum Finset.univ params r x k).symm
  rw [hY]
  exact polynomialReconstruct_share_eq_secret params (∑ s : Fin m, r s) (∑ s : Fin m, x s)

/-- Coalition simulator for `bgwSumProtocol params` against any static coalition `I` with
`I.card ≤ params.threshold`:
1. If `I = Finset.univ` (vacuous when `I.card ≤ params.threshold < m`) or `I = ∅` (empty view),
   handles directly; otherwise picks an honest pivot party `j₀ ∉ I` and sets `H' := Iᶜ.erase j₀`.
2. Samples total Round 2 randomness `R_tot : Randomness params`, corrupted coins
   `rI : (i : I) → Randomness params`, and honest non-pivot Round 1 shares
   `hRest : (s : H') → (I → F)` uniformly.
3. Computes the Round 2 broadcast vector `Y k = share params R_tot y k` from the ideal output `y`
   and sets the pivot honest party `j₀`'s Round 1 share to `i ∈ I` so that the column of shares
   received by `i` sums to `Y i`. -/
noncomputable def bgwSumSim {m : ℕ} (params : Params F (Fin m)) (I : Finset (Fin m)) :
    CoalitionSimulator (bgwSumSchedule m F)
      (fun _ => F) (fun _ => Randomness params) (fun _ => F) I :=
  fun xI yI =>
    open scoped Classical in
    if hI : ∃ j₀ : Fin m, j₀ ∉ I then
      if hne : I.Nonempty then
        let j₀ : Fin m := Classical.choose hI
        let H' : Finset (Fin m) := Iᶜ.erase j₀
        let y : F := yI ⟨hne.choose, hne.choose_spec⟩
        do
          let p ← ProbComp.uniform
            (Randomness params × ((i : I) → Randomness params) × ((s : H') → (I → F)))
          let (R_tot, rI, hRest) := p
          let Y : Fin m → F := fun k => share params R_tot y k
          let nonPivotShare (s : Fin m) (i : I) : F :=
            if hsI : s ∈ I then
              share params (rI ⟨s, hsI⟩) (xI ⟨s, hsI⟩) i.1
            else if hsH : s ∈ H' then
              hRest ⟨s, hsH⟩ i
            else
              0
          let inbox (i : I) (s : Fin m) : F :=
            if s = j₀ then
              Y i.1 - ∑ s' ∈ Finset.univ.erase j₀, nonPivotShare s' i
            else
              nonPivotShare s i
          return fun i => bgwSumViewOf params i.1 (xI i) (rI i) (inbox i) Y
      else
        pure (fun i => (hne ⟨i.1, i.2⟩).elim)
    else
      pure (fun i => bgwSumViewOf params i.1 (xI i) 0 0 0)

/-- **Full Joint View-and-Output $t$-Privacy of `bgwSumProtocol`**
(cf. [AsharovLindell2017], Section 4.2, Protocol 4.1 and Claim 4.3, for addition gates only):
for every static coalition `I` with `I.card ≤ params.threshold`, `bgwSumProtocol params` privately
computes `bgwSumFunctionality m` in `noOracleWorld` with simulator `bgwSumSim params`. -/
theorem perfectSemiHonestPrivateLe_bgwSum {m : ℕ} (params : Params F (Fin m)) :
    PerfectSemiHonestPrivateLe params.threshold (bgwSumProtocol params) noOracleWorld
      (bgwSumFunctionality m) (bgwSumSim params) := by
  classical
  refine perfectSemiHonestPrivateLe_of_deterministic params.threshold
    (bgwSumProtocol params) noOracleWorld (fun x _ => ∑ j : Fin m, x j) (bgwSumSim params)
    (fun I hI x => ?_) (fun x res hres => output_bgwSumProtocol params x hres)
  have hex : ∃ j₀ : Fin m, j₀ ∉ I := by
    by_contra h
    have huniv : I = Finset.univ := by
      ext i
      simp only [Finset.mem_univ, iff_true]
      by_contra hi
      exact h ⟨i, hi⟩
    have hcard : I.card = m := by rw [huniv, Finset.card_univ, Fintype.card_fin]
    have hlt : params.threshold < m := by simpa [Fintype.card_fin] using params.threshold_lt_card
    omega
  by_cases hne : I.Nonempty
  · rw [evalWith_bgwSumProtocol, PMF.map_comp]
    simp only [bgwSumSim, hex, hne, ↓reduceDIte, bind_pure_comp, ProbComp.eval_map,
      ProbComp.eval_uniform]
    let j₀ : Fin m := Classical.choose hex
    have hj₀ : j₀ ∉ I := Classical.choose_spec hex
    let H' : Finset (Fin m) := Iᶜ.erase j₀
    let shift :
        (Randomness params × ((i : I) → Randomness params) × ((s : H') → (I → F))) ≃
        (Randomness params × ((i : I) → Randomness params) × ((s : H') → (I → F))) :=
      Equiv.prodCongr (Equiv.refl _)
        (Equiv.prodCongr (Equiv.refl _)
          (Equiv.addLeft (fun (s : H') (_ : I) => x s.1)))
    have hmap :
        (PMF.uniformOfFintype
          (Randomness params × ((i : I) → Randomness params) × ((s : H') → (I → F)))) =
        (PMF.uniformOfFintype (Fin m → Randomness params)).map
          (shift ∘ bgwSumCoinsHom params I j₀) := by
      rw [← PMF.map_comp,
        Cslib.Probability.PMF.uniformOfFintype_map_addHom (bgwSumCoinsHom params I j₀)
          (bgwSumCoinsHom_surjective params I hI j₀ hj₀),
        PMF.uniformOfFintype_map_equiv]
    rw [hmap, PMF.map_comp]
    refine congrArg (PMF.map · _) (funext fun r => funext fun ⟨i, hi⟩ => ?_)
    have hY :
        (fun k : Fin m => share params (∑ s : Fin m, r s) (∑ j : Fin m, x j) k) =
          fun k : Fin m => ∑ s : Fin m, share params (r s) (x s) k := by
      ext k
      exact share_sum Finset.univ params r x k
    simp only [Function.comp_def, shift, bgwSumCoinsHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Finset.restrict, Equiv.prodCongr_apply, Equiv.refl_apply, Prod.map_fst, Prod.map_snd,
      Equiv.coe_addLeft]
    rw [hY]
    refine congrArg (bgwSumViewOf params i (x i) (r i) · _) (funext fun s => ?_)
    change (if s = j₀ then
        share params (∑ s' : Fin m, r s') (∑ j : Fin m, x j) i -
          ∑ s' ∈ Finset.univ.erase j₀,
            (if hsI : s' ∈ I then share params (r s') (x s') i
             else if hsH : s' ∈ H' then x s' + share params (r s') 0 i
             else 0)
      else
        if hsI : s ∈ I then share params (r s) (x s) i
        else if hsH : s ∈ H' then x s + share params (r s) 0 i
        else 0) = share params (r s) (x s) i
    have hnonPivot : ∀ s' ∈ Finset.univ.erase j₀,
        (if hsI : s' ∈ I then share params (r s') (x s') i
         else if hsH : s' ∈ H' then x s' + share params (r s') 0 i
         else 0) = share params (r s') (x s') i := by
      intro s' hs'
      have hne' : s' ≠ j₀ := (Finset.mem_erase.mp hs').1
      by_cases hsI : s' ∈ I
      · simp [hsI]
      · have hsH : s' ∈ H' :=
          Finset.mem_erase.mpr ⟨hne', Finset.mem_compl.mpr hsI⟩
        simp only [hsI, ↓reduceDIte, hsH]
        have hadd := share_add params 0 (r s') (x s') 0 i
        rw [zero_add, add_zero, share_zero_randomness] at hadd
        exact hadd.symm
    by_cases hs0 : s = j₀
    · simp only [hs0, ↓reduceIte]
      rw [share_sum Finset.univ params r x i,
        Finset.sum_congr rfl hnonPivot,
        ← Finset.add_sum_erase _ (fun s' => share params (r s') (x s') i) (Finset.mem_univ j₀),
        add_sub_cancel_right]
    · simp only [hs0, ↓reduceIte]
      exact hnonPivot s (Finset.mem_erase.mpr ⟨hs0, Finset.mem_univ s⟩)
  · simp only [bgwSumSim, hex, hne, ↓reduceDIte, ProbComp.eval_pure]
    symm
    have hconst :
        (fun r : ((i : Fin m) → PartyView (fun _ => F) (fun _ => Randomness params)
            (bgwSumSchedule m F) i) × (Fin m → F) => I.restrict r.1) =
          Function.const _ (fun i : I => (hne ⟨i.1, i.2⟩).elim) := by
      funext r
      funext i
      exact (hne ⟨i.1, i.2⟩).elim
    rw [hconst, PMF.map_const]

end Cslib.Crypto.Protocols.MPC.BGW
