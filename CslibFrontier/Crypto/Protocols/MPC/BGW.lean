/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Advantage
public import CslibFrontier.Crypto.Protocols.MPC.Broadcast
public import CslibFrontier.Crypto.Protocols.SecretSharing.Shamir.Linear
import CslibFrontier.Probability.PMF.Uniform

/-!
# BGW Semi-Honest Arithmetic MPC Gates and Degree-Reduction Protocol

This module formalizes the degree-reduction algebra and synchronous $m$-party
Ben-Or–Goldwasser–Wigderson (BGW) semi-honest arithmetic gate protocols over finite fields
([BenOrGoldwasserWigderson1988]; [GennaroRabinRabin1998]; [AsharovLindell2017];
[Goldreich2004]; [KatzLindell2020]), building on the Shamir secret-sharing homomorphisms and
unauthorized-coalition marginal uniformity in
`CslibFrontier.Crypto.Protocols.SecretSharing.Shamir.Linear`:

1. **BGW Multiplication Step and Degree-Reduction Algebra ($2t < |\text{Party}|$):**
   - In Asharov–Lindell ([AsharovLindell2017]; numbering as in the full version, ePrint
     2011/136), Section 4.3 (Protocol 4.5, Proposition 4.6, Protocol 4.7, Claims 4.8–4.9, and
     Proposition 4.10) presents the classical two-step
     *randomize-then-reduce* multiplication gate, where parties first add a degree-$2t$ zero-share
     (`bgwMulStep params r₁ a r₂ b r_z`, reconstructing to $a \cdot b$ via
     `reconstruct_bgwMulStep_eq_mul`) and then apply a linear degree-reduction step, whereas
     Section 6.1 explicitly describes the **Gennaro–Rabin–Rabin (GRR, [GennaroRabinRabin1998])
     one-step degree-reduction simplification**, in which each party $j$ directly reshares its
     degree-$2t$ product $a_j \cdot b_j$ using a fresh degree-$t$ Shamir polynomial and all
     parties take a Lagrange linear combination without a separate randomization step.
   - **Commutativity of Lagrange Reconstruction and Shamir Sharing (`bgwDegreeReduceShare_share`):**
     when each party $j$ reshares its intermediate value $d_j$ using fresh degree-$t$ Shamir
     randomness $r_{\text{sub}}(j)$, and each party $i$ applies Lagrange reconstruction
     (`bgwDegreeReduceShare`) to its column of received sub-shares, the result equals party $i$'s
     genuine degree-$t$ Shamir share of `Polynomial.reconstruct params.point d` under combined
     randomness `bgwReducedRandomness params r_sub`. This establishes correctness for both the
     one-step GRR resharing of $a_j \cdot b_j$ (`bgwDegreeReduceShare_mul_eq_share`,
     `reconstruct_bgwDegreeReduceShare_mul_eq_mul`) and the two-step zero-randomized intermediate
     values (`bgwDegreeReduceShare_bgwMulStep_eq_share`).
2. **1-Round Synchronous BGW/GRR Degree-Reduction Multiplication Gate
   (`bgwDegreeReductionProtocol`):**
   - Formalizes the 1-round $m$-party GRR degree-reduction multiplication gate over `noOracleSpec`
     ([GennaroRabinRabin1998]; [AsharovLindell2017], Section 6.1) using `allToAllStepsWith` and
     `receivedScheduleOfInbox` from `CslibFrontier.Crypto.Protocols.MPC.AllToAll`.
   - Every supported execution on degree-$t$ shares of $a, b$ ($2t < m$) outputs genuine
     degree-$t$ Shamir shares of $a \cdot b$ (`output_bgwDegreeReductionProtocol_eq_share_mul`,
     `reconstruct_output_bgwDegreeReductionProtocol_eq_mul`).
   - For every coalition $I$ with $|I| \le t$, the marginal distribution of $I$'s views equals
     `bgwDegreeReductionViewSim` (`map_restrict_evalWith_bgwDegreeReductionProtocol`,
     following [AsharovLindell2017], Section 3.2, Claims 3.2 and 3.4), depending only on $I$'s own
     input share pairs and independent of honest parties' inputs.
3. **2-Round Synchronous BGW Sum Protocol (`bgwSumProtocol`):**
   - Formalizes the 2-round $m$-party BGW input-sharing, local addition, and output-reconstruction
     protocol over `noOracleSpec` ([AsharovLindell2017], Section 4.2, Protocol 4.1 and Claim 4.3,
     specialized to addition gates).
   - Proves exact output correctness (`output_bgwSumProtocol`) and full joint view-and-output
     $t$-privacy `PerfectSemiHonestPrivateLe` (`perfectSemiHonestPrivateLe_bgwSum`,
     [AsharovLindell2017], Section 2.1, Definition 2.1) for all coalitions $I$ with $|I| \le t$.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.BGW.bgwMulStep`: degree-$2t$ zero-randomized BGW multiplication step.
* `Cslib.Crypto.Protocols.MPC.BGW.bgwReducedRandomness`,
  `Cslib.Crypto.Protocols.MPC.BGW.bgwDegreeReduceShare`: Lagrange-recombined degree-$t$ randomness
  and BGW degree-reduction share recombination.
* `Cslib.Crypto.Protocols.MPC.BGW.bgwDegreeReductionProtocol`,
  `Cslib.Crypto.Protocols.MPC.BGW.bgwDegreeReductionViewSim`: 1-round synchronous $m$-party
  BGW/GRR degree-reduction multiplication gate protocol and $t$-private coalition view simulator.
* `Cslib.Crypto.Protocols.MPC.BGW.bgwSumSchedule`,
  `Cslib.Crypto.Protocols.MPC.BGW.bgwSumFunctionality`,
  `Cslib.Crypto.Protocols.MPC.BGW.bgwSumProtocol`,
  `Cslib.Crypto.Protocols.MPC.BGW.bgwSumSim`: 2-round synchronous $m$-party BGW sum protocol and
  $t$-private coalition simulator.

## Main results

* `Cslib.Crypto.Protocols.MPC.BGW.bgwMulStep_eq_eval_sharingPolynomial`,
  `Cslib.Crypto.Protocols.MPC.BGW.reconstruct_bgwMulStep_eq_mul`: algebraic evaluation and
  Lagrange reconstruction of `bgwMulStep` for $2t < |\text{Party}|$.
* `Cslib.Crypto.Protocols.MPC.BGW.bgwDegreeReduceShare_share`,
  `Cslib.Crypto.Protocols.MPC.BGW.bgwDegreeReduceShare_mul_eq_share`,
  `Cslib.Crypto.Protocols.MPC.BGW.bgwDegreeReduceShare_bgwMulStep_eq_share`,
  `Cslib.Crypto.Protocols.MPC.BGW.reconstruct_bgwDegreeReduceShare_mul_eq_mul`: commutativity of
  Lagrange reconstruction with Shamir sharing and correctness of BGW degree reduction.
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

section DegreeReductionAlgebra

variable {F Party : Type*} [Field F] [Fintype Party]

/-! ### 1. BGW multiplication step and degree-reduction algebra -/

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
    ← Polynomial.sharingPolynomial_add, add_zero, ← Polynomial.tailPolynomial_add]

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
  ∑ j : Party, Polynomial.lagrangeWeightAtZero params.point j • r_sub j

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
  rw [bgwDegreeReduceShare, Polynomial.reconstruct_eq_sum_lagrangeWeightAtZero,
    bgwReducedRandomness, Polynomial.reconstruct_eq_sum_lagrangeWeightAtZero]
  have hsum := share_sum Finset.univ params
    (fun j => Polynomial.lagrangeWeightAtZero params.point j • r_sub j)
    (fun j => Polynomial.lagrangeWeightAtZero params.point j * d j) i
  have hsum' :
      (∑ j : Party, Polynomial.lagrangeWeightAtZero params.point j * d j) =
        ∑ j : Party, d j * Polynomial.lagrangeWeightAtZero params.point j := by
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

end DegreeReductionAlgebra

/-! ### 2. Synchronous $m$-party BGW gate protocols and $t$-privacy -/

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
   via `allToAllStepsWith`.
3. Each party `i` outputs the Lagrange-recombined share
   `Polynomial.reconstruct params.point inbox_i`. -/
@[expose] noncomputable def bgwDegreeReductionProtocol {m : ℕ} (params : Params F (Fin m)) :
    Protocol m noOracleSpec (allToAllSchedule m (spec := noOracleSpec) F)
      (fun _ => F × F) (fun _ => Randomness params) (fun _ => F) where
  sampleCoins _ := ProbComp.uniform (Randomness params)
  steps :=
    allToAllStepsWith m (spec := noOracleSpec) (Msg := F)
      (State := fun _ => (F × F) × Randomness params)
      (Out := fun _ => F)
      (fun _ (uv_s, r_s) rcv => share params r_s (uv_s.1 * uv_s.2) rcv)
      (fun _ _ inbox => Polynomial.reconstruct params.point inbox)

/-- Construct party `i`'s `PartyView` in `bgwDegreeReductionProtocol` from its input `uv_i`,
its coins `r_i`, and its received sub-share inbox `inbox_i : Fin m → F`. -/
def bgwDegreeReductionViewOf {m : ℕ} (params : Params F (Fin m)) (i : Fin m)
    (uv_i : F × F) (r_i : Randomness params) (inbox_i : Fin m → F) :
    PartyView (fun _ => F × F) (fun _ => Randomness params)
      (allToAllSchedule m (spec := noOracleSpec) F) i where
  input := uv_i
  coins := r_i
  received := receivedScheduleOfInbox (spec := noOracleSpec) i inbox_i (allPairs m)

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
  simp only [evalWith_allToAllStepsWith, PMF.pure_map]
  rw [PMF.map]
  refine congrArg (PMF.bind (PMF.uniformOfFintype (Fin m → Randomness params)))
    (funext fun r => congrArg PMF.pure ?_)
  refine Prod.ext (funext fun i => rfl) (funext fun i => ?_)
  simp [Protocol.outputOfView, outputAt_allToAllStepsWith, bgwDegreeReduceShare]

/-- Output correctness of `bgwDegreeReductionProtocol`: when `2 * params.threshold < m`
($t < m / 2$) and the inputs `uv` are degree-$t$ Shamir shares of `a` and `b`, every supported
execution outputs a genuine degree-$t$ Shamir sharing of `a * b` under
`bgwReducedRandomness params`. -/
theorem output_bgwDegreeReductionProtocol_eq_share_mul {m : ℕ} (params : Params F (Fin m))
    (h2t : 2 * params.threshold < m)
    (r₁ r₂ : Randomness params) (a b : F)
    {res : ((i : Fin m) → PartyView (fun _ => F × F) (fun _ => Randomness params)
        (allToAllSchedule m (spec := noOracleSpec) F) i) × (Fin m → F)}
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
        (allToAllSchedule m (spec := noOracleSpec) F) i) × (Fin m → F)}
    (hres : res ∈ ((bgwDegreeReductionProtocol params).evalWith noOracleWorld
        (fun i => (share params r₁ a i, share params r₂ b i))).support)
    {s : Finset (Fin m)} (hs : authorized params s) :
    reconstruct params s (s.restrict res.2) = a * b := by
  rw [output_bgwDegreeReductionProtocol_eq_share_mul params h2t r₁ r₂ a b hres]
  exact reconstruct_share_eq_secret params
    (bgwReducedRandomness params (fun j => (res.1 j).coins)) (a * b) hs

/-- Coalition view simulator for `bgwDegreeReductionProtocol params` ([AsharovLindell2017],
Section 3.2, Claims 3.2 and 3.4): given only the coalition's input share pairs
`uvI : (i : I) → F × F`, samples uniform coins `rI` for `i ∈ I` and independent uniform sub-share
vectors `hCompl : Iᶜ → I → F` from honest senders `s ∉ I`, and assembles each corrupted party's
inbox. -/
noncomputable def bgwDegreeReductionViewSim {m : ℕ} (params : Params F (Fin m))
    (I : Finset (Fin m)) (uvI : (i : I) → F × F) :
    ProbComp ((i : I) → PartyView (fun _ => F × F) (fun _ => Randomness params)
      (allToAllSchedule m (spec := noOracleSpec) F) i) := do
  let p ← ProbComp.uniform
    (((i : I) → Randomness params) × ((s : (Iᶜ : Finset (Fin m))) → (I → F)))
  let (rI, hCompl) := p
  return fun i =>
    bgwDegreeReductionViewOf params i.1 (uvI i) (rI i) fun s =>
      if hs : s ∈ I then
        share params (rI ⟨s, hs⟩) ((uvI ⟨s, hs⟩).1 * (uvI ⟨s, hs⟩).2) i.1
      else
        hCompl ⟨s, Finset.mem_compl.mpr hs⟩ i

/-- **$t$-Privacy of BGW Degree-Reduction Views** ([AsharovLindell2017], Section 3.2, Claims 3.2
and 3.4): for every coalition `I` with `I.card ≤ params.threshold` and every input tuple
`uv : Fin m → F × F`, the marginal distribution of `I`'s views in
`bgwDegreeReductionProtocol params` equals `ProbComp.eval (bgwDegreeReductionViewSim params I
(I.restrict uv))`, which depends only on `I.restrict uv` and is independent of all honest parties'
input share pairs. -/
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
    ZeroHom.coe_mk, Finset.restrict, Equiv.prodCongr_apply, Equiv.refl_apply, Prod.map_fst,
    Prod.map_snd, Equiv.coe_addLeft]
  refine congrArg (bgwDegreeReductionViewOf params i (uv i) (r i)) (funext fun s => ?_)
  by_cases hs : s ∈ I
  · simp [hs]
  · simp only [hs, ↓reduceDIte, Pi.add_apply]
    have hadd := share_add params 0 (r s) ((uv s).1 * (uv s).2) 0 i
    rw [zero_add, add_zero, share_zero_randomness] at hadd
    exact hadd

/-! ### 3. 2-round synchronous $m$-party BGW sum protocol and full joint $t$-privacy -/

/-- Schedule for `bgwSumProtocol params`: one all-to-all point-to-point Shamir input-sharing phase
followed by one all-to-all broadcast of summed shares. -/
@[expose, reducible] def bgwSumSchedule (m : ℕ) (F : Type) : Schedule m noOracleSpec :=
  allToAllSchedule m (spec := noOracleSpec) F ++ allToAllSchedule m (spec := noOracleSpec) F

/-- Deterministic $m$-party functionality returning the sum `∑ j : Fin m, x j` to every party. -/
@[expose] def bgwSumFunctionality (m : ℕ) : Functionality m (fun _ => F) (fun _ => F) :=
  Functionality.ofDeterministic (fun x _ => ∑ j : Fin m, x j)

/-- 2-round synchronous $m$-party BGW sum protocol over `noOracleSpec`
([AsharovLindell2017], Section 4.2, Protocol 4.1, for a circuit of addition gates):
1. Each party `s : Fin m` samples degree-$t$ Shamir randomness `r_s : Randomness params` and sends
   `share params r_s (x s) rcv` to each receiver `rcv : Fin m` via `allToAllStepsWith`.
2. Each party `k : Fin m` sums its received shares `Y_k = ∑ s : Fin m, inbox_k s` and broadcasts
   `Y_k` via `broadcastSteps`.
3. Each party reconstructs `Polynomial.reconstruct params.point Y`. -/
@[expose] noncomputable def bgwSumProtocol {m : ℕ} (params : Params F (Fin m)) :
    Protocol m noOracleSpec (bgwSumSchedule m F)
      (fun _ => F) (fun _ => Randomness params) (fun _ => F) where
  sampleCoins _ := ProbComp.uniform (Randomness params)
  steps :=
    (allToAllStepsWith m (spec := noOracleSpec) (Msg := F)
      (State := fun _ => F × Randomness params)
      (Out := fun _ => Fin m → F)
      (fun _ (x_s, r_s) rcv => share params r_s x_s rcv)
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
      (sc₁ := allToAllSchedule m (spec := noOracleSpec) F)
      (sc₂ := allToAllSchedule m (spec := noOracleSpec) F)
      (receivedScheduleOfInbox (spec := noOracleSpec) i inbox_i (allPairs m))
      (receivedScheduleOfInbox (spec := noOracleSpec) i Y (allPairs m))

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
  simp only [Steps.evalWith_append, evalWith_allToAllStepsWith,
    outputAt_allToAllStepsWith, evalWith_broadcastSteps, PMF.pure_bind, PMF.pure_map]
  rw [PMF.map]
  refine congrArg (PMF.bind (PMF.uniformOfFintype (Fin m → Randomness params)))
    (funext fun r => congrArg PMF.pure ?_)
  refine Prod.ext (funext fun i => rfl) (funext fun i => ?_)
  simp [Protocol.outputOfView, Steps.outputAt_append, outputAt_allToAllStepsWith,
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
  exact Polynomial.reconstruct_share_eq_secret params (∑ s : Fin m, r s) (∑ s : Fin m, x s)

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
