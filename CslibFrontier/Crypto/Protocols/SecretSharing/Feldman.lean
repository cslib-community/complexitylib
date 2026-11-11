/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pi
public import CslibFrontier.Crypto.Computational.DiscreteLog
public import CslibFrontier.Crypto.Protocols.SecretSharing.Shamir.Linear
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PowMod
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip
import CslibFrontier.Crypto.Computational.DiffieHellman
import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.PolyTime
import Mathlib.FieldTheory.Finite.Basic

/-!
# Feldman Verifiable Secret Sharing

Feldman's non-interactive verifiable secret sharing (VSS) scheme ([Feldman1987]) over
a `PrimeOrderGroupFamily` `F` and `Shamir.Params (ZMod (F.order d)) Party`. For a sharing
polynomial `f(X) = secret + ∑_{j=1}^t r_j X^j` over `ZMod q` (where `q = F.order d` is prime), the
dealer publishes group-element commitments

`C j = (a_j) • g` for `j = 0, …, t`,

and each party `i : Party` checks its share `s_i = f(x_i)` non-interactively via

`s_i • g = ∑ j, (x_i ^ j) • C j`.

Unlike Pedersen VSS, Feldman's scheme publishes `C 0 = secret • g` in the clear, so it does not
achieve chosen-secret indistinguishability (`advantage_feldmanChosenSecretDistinguisher_eq_one`);
instead, an unauthorized coalition's view `feldmanView` is identically simulated from `secret • g`
by Lagrange interpolation in the exponent (`feldmanSim`, `feldmanView_eq_feldmanSim`), and
uniform-secret secrecy reduces in strict PPT (`IsPPTOn`) to `F.DiscreteLog`.

## Main definitions

* `Cslib.Crypto.Protocols.SecretSharing.Feldman.feldmanCommit`: dealer commitments `C j = a_j • g`.
* `Cslib.Crypto.Protocols.SecretSharing.Feldman.feldmanVerify`,
  `Cslib.Crypto.Protocols.SecretSharing.Feldman.encodeFeldmanVerify`: semantic and encoded public
  share verification.
* `Cslib.Crypto.Protocols.SecretSharing.Feldman.feldmanView`,
  `Cslib.Crypto.Protocols.SecretSharing.Feldman.feldmanSim`: real unauthorized-coalition view and
  its Lagrange-in-the-exponent simulator given only `(secret • g, I)`.
* `Cslib.Crypto.Protocols.SecretSharing.Feldman.feldmanSecrecyGame`,
  `Cslib.Crypto.Protocols.SecretSharing.Feldman.feldmanToDLAdversary`: uniform-secret secrecy
  experiment and strict-PPT reduction to `DiscreteLog`.
* `Cslib.Crypto.Protocols.SecretSharing.Feldman.feldmanChosenSecretDistinguisher`: explicit
  strict-PPT chosen-secret distinguisher reading `C 0 = secret • g`.

## Main results

* `Cslib.Crypto.Protocols.SecretSharing.Feldman.feldmanVerify_share`: honest Shamir shares verify
  with certainty.
* `Cslib.Crypto.Protocols.SecretSharing.Feldman.feldmanVerify_unique_share`,
  `Cslib.Crypto.Protocols.SecretSharing.Feldman.reconstruct_smul_generator_eq_commit_zero`,
  `Cslib.Crypto.Protocols.SecretSharing.Feldman.feldmanVerify_agree_on_authorized`,
  `Cslib.Crypto.Protocols.SecretSharing.Feldman.reconstruct_eq_of_feldmanVerify_commit_zero`:
  malicious-dealer binding and cross-coalition consistency against unbounded dealers.
* `Cslib.Crypto.Protocols.SecretSharing.Feldman.feldmanView_eq_feldmanSim`: zero-distance exact
  simulation of unauthorized coalitions from `secret • g`.
* `Feldman.isPPTOn_feldmanToDLAdversary`,
  `Feldman.succProbability_feldmanSecrecyGame_le_discreteLogGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DiscreteLog.feldmanSecrecy`: strict-PPT reduction from
  uniform-secret Feldman secrecy to `DiscreteLog`.
* `Cslib.Crypto.Protocols.SecretSharing.Feldman.advantage_feldmanChosenSecretDistinguisher_eq_one`:
  chosen-secret indistinguishability fails with exact advantage `1`.

## References

* [P. Feldman, *A Practical Scheme for Non-interactive Verifiable Secret Sharing*][Feldman1987].
* [A. Shamir, *How to Share a Secret*][Shamir1979].
-/

public section

namespace Cslib.Crypto.Protocols.SecretSharing.Feldman

open Cslib Cslib.Crypto Cslib.Probability Cslib.Crypto.Protocols.SecretSharing
open Turing.MultiTapeTM
open scoped ENNReal NNReal BigOperators

section Scheme

variable (F : PrimeOrderGroupFamily) {Party : Type} [Fintype Party]

/-- Dealer polynomial coefficient vector `a : Fin (params.threshold + 1) → ZMod (F.order d)`
with constant term `secret` and tail coefficients `r`. -/
@[expose] def dealerCoeffs (d : F.Desc) (params : Shamir.Params (ZMod (F.order d)) Party)
    (secret : ZMod (F.order d)) (r : Shamir.Randomness params) :
    Fin (params.threshold + 1) → ZMod (F.order d) :=
  Fin.cons secret r

/-- Feldman dealer commitments `C j = (a_j) • g` for `j = 0, …, params.threshold`. -/
@[expose] def feldmanCommit (d : F.Desc) (params : Shamir.Params (ZMod (F.order d)) Party)
    (secret : ZMod (F.order d)) (r : Shamir.Randomness params) :
    Fin (params.threshold + 1) → F.Carrier d :=
  fun j => (dealerCoeffs F d params secret r j) • F.generator d

@[simp] theorem feldmanCommit_zero (d : F.Desc)
    (params : Shamir.Params (ZMod (F.order d)) Party)
    (secret : ZMod (F.order d)) (r : Shamir.Randomness params) :
    feldmanCommit F d params secret r 0 = secret • F.generator d := by
  simp [feldmanCommit, dealerCoeffs]

@[simp] theorem feldmanCommit_succ (d : F.Desc)
    (params : Shamir.Params (ZMod (F.order d)) Party)
    (secret : ZMod (F.order d)) (r : Shamir.Randomness params) (j : Fin params.threshold) :
    feldmanCommit F d params secret r j.succ = r j • F.generator d := by
  simp [feldmanCommit, dealerCoeffs]

private theorem sharingPolynomial_eq_sum_dealerCoeffs (d : F.Desc)
    (params : Shamir.Params (ZMod (F.order d)) Party)
    (secret : ZMod (F.order d)) (r : Shamir.Randomness params) :
    Shamir.Polynomial.sharingPolynomial secret
        (Shamir.Polynomial.tailPolynomial params.threshold r) =
      ∑ j : Fin (params.threshold + 1),
        _root_.Polynomial.C (dealerCoeffs F d params secret r j) *
          _root_.Polynomial.X ^ (j : ℕ) := by
  ext k
  change _ = (_root_.Polynomial.lcoeff _ k)
    (∑ j : Fin (params.threshold + 1),
      _root_.Polynomial.C (dealerCoeffs F d params secret r j) * _root_.Polynomial.X ^ (j : ℕ))
  rw [map_sum]
  simp only [_root_.Polynomial.lcoeff_apply, _root_.Polynomial.coeff_C_mul_X_pow]
  cases k with
  | zero =>
    rw [Shamir.Polynomial.coeff_zero_sharingPolynomial,
      Finset.sum_eq_single (0 : Fin (params.threshold + 1))]
    · simp [dealerCoeffs]
    · intro j _ hj
      have hne : (j : ℕ) ≠ 0 := by intro h0; exact hj (Fin.ext h0)
      simp [hne.symm]
    · simp
  | succ k =>
    simp only [Shamir.Polynomial.sharingPolynomial, _root_.Polynomial.coeff_add,
      _root_.Polynomial.coeff_C_succ, _root_.Polynomial.coeff_X_mul, zero_add]
    by_cases hk : k < params.threshold
    · let idx : Fin (params.threshold + 1) := ⟨k + 1, Nat.succ_lt_succ hk⟩
      rw [Finset.sum_eq_single idx]
      · rw [Shamir.Polynomial.tailPolynomial_coeff params.threshold r ⟨k, hk⟩]
        simp [idx, dealerCoeffs]
        exact (Fin.cons_succ (α := fun _ => ZMod (F.order d)) secret
          (r : Fin params.threshold → ZMod (F.order d)) ⟨k, hk⟩).symm
      · intro j _ hj
        have hne : (j : ℕ) ≠ k + 1 := by
          intro hjk
          exact hj (Fin.ext (by simp [idx, hjk]))
        simp [hne.symm]
      · simp
    · have htail_deg :=
        Shamir.Polynomial.tailPolynomial_degree_lt params.threshold r (F := ZMod (F.order d))
      have hzero :
          (Shamir.Polynomial.tailPolynomial (F := ZMod (F.order d))
            params.threshold r).coeff k = 0 := by
        apply _root_.Polynomial.coeff_eq_zero_of_degree_lt
        exact lt_of_lt_of_le htail_deg (by exact_mod_cast Nat.le_of_not_lt hk)
      rw [hzero]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      have hj : (j : ℕ) < params.threshold + 1 := j.isLt
      have hne : (j : ℕ) ≠ k + 1 := by omega
      simp [hne.symm]

private theorem eval_sharingPolynomial_eq_sum_dealerCoeffs (d : F.Desc)
    (params : Shamir.Params (ZMod (F.order d)) Party)
    (secret : ZMod (F.order d)) (r : Shamir.Randomness params) (x : ZMod (F.order d)) :
    (Shamir.Polynomial.sharingPolynomial secret
        (Shamir.Polynomial.tailPolynomial params.threshold r)).eval x =
      ∑ j : Fin (params.threshold + 1),
        dealerCoeffs F d params secret r j * x ^ (j : ℕ) := by
  rw [sharingPolynomial_eq_sum_dealerCoeffs F d params secret r]
  change (_root_.Polynomial.evalRingHom x) _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [show ∀ q, _root_.Polynomial.evalRingHom x q = q.eval x from fun _ => rfl,
    _root_.Polynomial.eval_mul, _root_.Polynomial.eval_pow,
    _root_.Polynomial.eval_C, _root_.Polynomial.eval_X]

/-- Feldman non-interactive share verification: check `s • g = ∑ j, (x_i ^ j) • C j`. -/
@[expose] def feldmanVerify (d : F.Desc) (params : Shamir.Params (ZMod (F.order d)) Party)
    (C : Fin (params.threshold + 1) → F.Carrier d) (i : Party)
    (shareVal : ZMod (F.order d)) : Bool :=
  haveI : DecidableEq (F.Carrier d) := fun a b =>
    decidable_of_iff (F.encode d a = F.encode d b) (F.encode_injective d).eq_iff
  decide (shareVal • F.generator d =
    ∑ j : Fin (params.threshold + 1), ((params.point i) ^ (j : ℕ)) • C j)

theorem feldmanVerify_eq_true_iff (d : F.Desc)
    (params : Shamir.Params (ZMod (F.order d)) Party)
    (C : Fin (params.threshold + 1) → F.Carrier d) (i : Party)
    (shareVal : ZMod (F.order d)) :
    feldmanVerify F d params C i shareVal = true ↔
      shareVal • F.generator d =
        ∑ j : Fin (params.threshold + 1), ((params.point i) ^ (j : ℕ)) • C j := by
  let : DecidableEq (F.Carrier d) := fun a b =>
    decidable_of_iff (F.encode d a = F.encode d b) (F.encode_injective d).eq_iff
  dsimp only [feldmanVerify]
  exact iff_of_eq decide_eq_true_eq

/-- **Feldman completeness**: every honest Shamir share verifies against `feldmanCommit`. -/
theorem feldmanVerify_share (d : F.Desc) (params : Shamir.Params (ZMod (F.order d)) Party)
    (secret : ZMod (F.order d)) (r : Shamir.Randomness params) (i : Party) :
    feldmanVerify F d params (feldmanCommit F d params secret r) i
      (Shamir.share params r secret i) = true := by
  rw [feldmanVerify_eq_true_iff]
  unfold Shamir.share
  rw [eval_sharingPolynomial_eq_sum_dealerCoeffs F d params secret r (params.point i),
    Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [feldmanCommit, mul_comm, mul_smul]

/-- Polynomial-time encoded linear combination of encoded group elements: computes
`F.encode d (∑ (a, w), (a : ZMod (F.order d)) • dec w)`. -/
@[expose] def groupLinCombWord (d : F.Desc) : List (ℕ × List Bool) → List Bool
  | [] => F.smul (d, 0, F.encode d (F.generator d))
  | (a, w) :: rest => F.add (d, F.smul (d, a, w), groupLinCombWord d rest)

theorem groupLinCombWord_encode (d : F.Desc) (terms : List (ℕ × F.Carrier d)) :
    groupLinCombWord F d (terms.map fun p => (p.1, F.encode d p.2)) =
      F.encode d (terms.map fun p => (p.1 : ZMod (F.order d)) • p.2).sum := by
  induction terms with
  | nil =>
    simp [groupLinCombWord, F.smul_encode]
  | cons hd tl ih =>
    simp only [List.map_cons, groupLinCombWord, F.smul_encode, ih, F.add_encode, List.sum_cons]

/-- Fixed-threshold helper for encoded Feldman share verification. -/
@[expose] def encodeFeldmanVerifyFixed (t : ℕ) (d : F.Desc) (pointVal : ℕ)
    (C : Fin (t + 1) → List Bool) (shareVal : ℕ) : Bool :=
  decide (shareVal < F.order d) &&
    decide (F.smul (d, shareVal, F.encode d (F.generator d)) =
      groupLinCombWord F d
        ((List.finRange (t + 1)).map fun j => ((pointVal ^ j.1) % F.order d, C j)))

/-- Encoded Feldman verification from `(d, C_words, shareVal)`: rejects non-canonical
`shareVal ≥ F.order d` and checks equality of encoded group elements. -/
@[expose] def encodeFeldmanVerify (d : F.Desc)
    (params : Shamir.Params (ZMod (F.order d)) Party)
    (C : Fin (params.threshold + 1) → List Bool) (i : Party) (shareVal : ℕ) : Bool :=
  encodeFeldmanVerifyFixed F params.threshold d (params.point i).val C shareVal

theorem encodeFeldmanVerify_encode (d : F.Desc)
    (params : Shamir.Params (ZMod (F.order d)) Party)
    (C : Fin (params.threshold + 1) → F.Carrier d) (i : Party)
    (shareVal : ZMod (F.order d)) :
    encodeFeldmanVerify F d params (fun j => F.encode d (C j)) i shareVal.val =
      feldmanVerify F d params C i shareVal := by
  have hterm :
      ((List.finRange (params.threshold + 1)).map fun j =>
        (((params.point i).val ^ j.1) % F.order d, F.encode d (C j))) =
      ((List.finRange (params.threshold + 1)).map fun j =>
        (((params.point i).val ^ j.1) % F.order d, C j)).map
          (fun p => (p.1, F.encode d p.2)) := by
    simp [List.map_map, Function.comp_def]
  have hsum :
      (((List.finRange (params.threshold + 1)).map fun j =>
          (((params.point i).val ^ j.1) % F.order d, C j)).map
        fun p => (p.1 : ZMod (F.order d)) • p.2).sum =
      ∑ j : Fin (params.threshold + 1), ((params.point i) ^ (j : ℕ)) • C j := by
    rw [Fin.sum_univ_def, List.map_map]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    simp [ZMod.natCast_mod, Nat.cast_pow]
  unfold encodeFeldmanVerify encodeFeldmanVerifyFixed
  rw [hterm, groupLinCombWord_encode, hsum, F.smul_encode, ZMod.natCast_zmod_val,
    decide_eq_true (ZMod.val_lt shareVal), Bool.true_and,
    Bool.eq_iff_iff, decide_eq_true_eq, feldmanVerify_eq_true_iff]
  exact (F.encode_injective d).eq_iff

private theorem computableInPolyTime_groupLinCombWord
    {α ι : Type} {input : α ↪ List Bool}
    {fd : α → F.Desc} (hd : ComputableInPolyTime fd input F.encDesc)
    (items : List ι)
    {coef : ι → α → ℕ} {word : ι → α → List Bool}
    (hcoef : ∀ x ∈ items, ComputableInPolyTime (coef x) input encNat)
    (hword : ∀ x ∈ items, ComputableInPolyTime (word x) input encBits) :
    ComputableInPolyTime
      (fun a => groupLinCombWord F (fd a) (items.map fun x => (coef x a, word x a)))
      input encBits := by
  induction items with
  | nil =>
    have hg := F.computableInPolyTime_generator.comp hd
    have h0 : ComputableInPolyTime (fun _ : α => (0 : ℕ)) input encNat :=
      ComputableInPolyTime.const 0
    simpa only [List.map_nil, groupLinCombWord, Function.comp_def] using
      F.computableInPolyTime_smul.comp (hd.prod (h0.prod hg))
  | cons x xs ih =>
    have hcx := hcoef x List.mem_cons_self
    have hwx := hword x List.mem_cons_self
    have hhead := F.computableInPolyTime_smul.comp (hd.prod (hcx.prod hwx))
    have htail := ih (fun y hy => hcoef y (List.mem_cons_of_mem x hy))
      (fun y hy => hword y (List.mem_cons_of_mem x hy))
    simpa only [List.map_cons, groupLinCombWord, Function.comp_def] using
      F.computableInPolyTime_add.comp (hd.prod (hhead.prod htail))

/-- For fixed threshold `t`, `encodeFeldmanVerifyFixed` is polynomial-time whenever the evaluation
point `pointVal d` is computable in polynomial time from `d`. -/
theorem computableInPolyTime_encodeFeldmanVerifyFixed (t : ℕ) (pointVal : F.Desc → ℕ)
    (hpoint : ComputableInPolyTime pointVal F.encDesc encNat) :
    ComputableInPolyTime
      (fun p : F.Desc × (Fin (t + 1) → List Bool) × ℕ =>
        encodeFeldmanVerifyFixed F t p.1 (pointVal p.1) p.2.1 p.2.2)
      (encPair F.encDesc (encPair (encPi encBits) encNat)) encBool := by
  let encIn := encPair F.encDesc (encPair (encPi (Index := Fin (t + 1)) encBits) encNat)
  have hd : ComputableInPolyTime (fun p : F.Desc × (Fin (t + 1) → List Bool) × ℕ => p.1)
      encIn F.encDesc := by fun_prop
  have hC : ComputableInPolyTime (fun p : F.Desc × (Fin (t + 1) → List Bool) × ℕ => p.2.1)
      encIn (encPi encBits) := by fun_prop
  have hs : ComputableInPolyTime (fun p : F.Desc × (Fin (t + 1) → List Bool) × ℕ => p.2.2)
      encIn encNat := by fun_prop
  have hord := F.computableInPolyTime_order.comp hd
  have hg := F.computableInPolyTime_generator.comp hd
  have hlhs := F.computableInPolyTime_smul.comp (hd.prod (hs.prod hg))
  have hrhs : ComputableInPolyTime
      (fun p : F.Desc × (Fin (t + 1) → List Bool) × ℕ =>
        groupLinCombWord F p.1
          ((List.finRange (t + 1)).map fun j : Fin (t + 1) =>
            ((pointVal p.1 ^ j.1) % F.order p.1, p.2.1 j)))
      encIn encBits := by
    refine computableInPolyTime_groupLinCombWord F hd (List.finRange (t + 1)) ?_ ?_
    · intro j _
      have hp := hpoint.comp hd
      have hj : ComputableInPolyTime (fun _ : F.Desc × (Fin (t + 1) → List Bool) × ℕ => j.1)
          encIn encUnary := ComputableInPolyTime.const j.1
      have hpow := ComputableInPolyTime.binary_pow' hp hj
      exact .of_tidy (.binary_mod' hpow.tidy hord.tidy)
    · intro j _
      exact ((ComputableTidilyInPolyTime.pi_apply encBits j).computableInPolyTime).comp hC
  have hlt : ComputableInPolyTime
      (fun p : F.Desc × (Fin (t + 1) → List Bool) × ℕ => decide (p.2.2 < F.order p.1))
      encIn encBool := ComputableInPolyTime.binary_lt' hs hord
  have heq : ComputableInPolyTime
      (fun p : F.Desc × (Fin (t + 1) → List Bool) × ℕ =>
        decide (F.smul (p.1, p.2.2, F.encode p.1 (F.generator p.1)) =
          groupLinCombWord F p.1
            ((List.finRange (t + 1)).map fun j : Fin (t + 1) =>
              ((pointVal p.1 ^ j.1) % F.order p.1, p.2.1 j))))
      encIn encBool := by fun_prop
  unfold encodeFeldmanVerifyFixed
  fun_prop

/-- For fixed threshold `t` and party `i`, `encodeFeldmanVerify` is polynomial-time whenever
`params` has fixed threshold `t` and computable evaluation point `i`. -/
theorem computableInPolyTime_encodeFeldmanVerify (t : ℕ) (i : Party)
    (params : ∀ d : F.Desc, Shamir.Params (ZMod (F.order d)) Party)
    (hthresh : ∀ d, (params d).threshold = t)
    (hpoint : ComputableInPolyTime (fun d => ((params d).point i).val) F.encDesc encNat) :
    ComputableInPolyTime
      (fun p : F.Desc × (Fin (t + 1) → List Bool) × ℕ =>
        encodeFeldmanVerify F p.1 (params p.1)
          (fun j => p.2.1 ⟨j.1, Nat.lt_of_lt_of_eq j.2 (congrArg Nat.succ (hthresh p.1))⟩)
          i p.2.2)
      (encPair F.encDesc (encPair (encPi encBits) encNat)) encBool := by
  have hfix := computableInPolyTime_encodeFeldmanVerifyFixed F t
    (fun d => ((params d).point i).val) hpoint
  have hcast : ∀ (d : F.Desc) (C : Fin (t + 1) → List Bool) (s : ℕ) (k : ℕ) (hk : k = t)
      (C' : Fin (k + 1) → List Bool) (hC : ∀ j : Fin (k + 1), C' j = C ⟨j.1, by omega⟩),
      encodeFeldmanVerifyFixed F k d ((params d).point i).val C' s =
        encodeFeldmanVerifyFixed F t d ((params d).point i).val C s := by
    rintro d C s k rfl C' hC
    congr 1
    funext j
    exact hC j
  suffices hfn :
      (fun p : F.Desc × (Fin (t + 1) → List Bool) × ℕ =>
        encodeFeldmanVerifyFixed F t p.1 ((params p.1).point i).val p.2.1 p.2.2) =
      (fun p : F.Desc × (Fin (t + 1) → List Bool) × ℕ =>
        encodeFeldmanVerify F p.1 (params p.1)
          (fun j => p.2.1 ⟨j.1, Nat.lt_of_lt_of_eq j.2 (congrArg Nat.succ (hthresh p.1))⟩)
          i p.2.2) by
    rwa [← hfn]
  ext p : 1
  exact (hcast p.1 p.2.1 p.2.2 (params p.1).threshold (hthresh p.1)
    (fun j => p.2.1 ⟨j.1, Nat.lt_of_lt_of_eq j.2 (congrArg Nat.succ (hthresh p.1))⟩)
    (fun _ => rfl)).symm

end Scheme

section Soundness

variable (F : PrimeOrderGroupFamily) {Party : Type} [Fintype Party]

/-- **Share uniqueness**: for a fixed party `i` and public commitment vector `C` (even maliciously
constructed), at most one scalar in `ZMod (F.order d)` satisfies `feldmanVerify`. -/
theorem feldmanVerify_unique_share (d : F.Desc)
    (params : Shamir.Params (ZMod (F.order d)) Party)
    (C : Fin (params.threshold + 1) → F.Carrier d) (i : Party)
    {s₁ s₂ : ZMod (F.order d)}
    (hs₁ : feldmanVerify F d params C i s₁ = true)
    (hs₂ : feldmanVerify F d params C i s₂ = true) :
    s₁ = s₂ := by
  rw [feldmanVerify_eq_true_iff] at hs₁ hs₂
  exact F.smul_generator_injective d (hs₁.trans hs₂.symm)

private theorem exists_commitPolynomial (d : F.Desc)
    (params : Shamir.Params (ZMod (F.order d)) Party)
    (C : Fin (params.threshold + 1) → F.Carrier d) :
    ∃ P : _root_.Polynomial (ZMod (F.order d)),
      P.degree < (params.threshold + 1 : WithBot ℕ) ∧
      P.constantCoeff • F.generator d = C 0 ∧
      ∀ i : Party, ∀ s : ZMod (F.order d),
        feldmanVerify F d params C i s = true → s = P.eval (params.point i) := by
  classical
  have hcoeff : ∀ j : Fin (params.threshold + 1),
      ∃ α : ZMod (F.order d), α • F.generator d = C j :=
    fun j => F.smul_generator_surjective d (C j)
  choose α hα using hcoeff
  let P : _root_.Polynomial (ZMod (F.order d)) :=
    ∑ j : Fin (params.threshold + 1),
      _root_.Polynomial.C (α j) * _root_.Polynomial.X ^ (j : ℕ)
  refine ⟨P, ?_, ?_, ?_⟩
  · refine lt_of_le_of_lt (_root_.Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro j _
    refine lt_of_le_of_lt (_root_.Polynomial.degree_C_mul_X_pow_le j.1 (α j)) ?_
    exact_mod_cast j.isLt
  · have h0 : P.constantCoeff = α 0 := by
      rw [_root_.Polynomial.constantCoeff_apply]
      dsimp only [P]
      rw [← _root_.Polynomial.lcoeff_apply, map_sum]
      simp only [_root_.Polynomial.lcoeff_apply, _root_.Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_eq_single (0 : Fin (params.threshold + 1))]
      · simp
      · intro j _ hj
        have hne : (j : ℕ) ≠ 0 := fun h0 => hj (Fin.ext h0)
        simp [hne.symm]
      · simp
    rw [h0]
    exact hα 0
  · intro i s hs
    rw [feldmanVerify_eq_true_iff] at hs
    apply F.smul_generator_injective d
    dsimp only
    rw [hs]
    have heval : P.eval (params.point i) =
        ∑ j : Fin (params.threshold + 1), ((params.point i) ^ (j : ℕ)) * α j := by
      change (_root_.Polynomial.evalRingHom (params.point i)) P = _
      dsimp only [P]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [show ∀ q, _root_.Polynomial.evalRingHom (params.point i) q =
          q.eval (params.point i) from fun _ => rfl,
        _root_.Polynomial.eval_mul, _root_.Polynomial.eval_pow,
        _root_.Polynomial.eval_C, _root_.Polynomial.eval_X, mul_comm]
    rw [heval, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul, hα j]

/-- **Malicious-dealer soundness**: for an arbitrary commitment vector `C`, reconstructing shares
over any authorized coalition whose shares verify yields a secret matching `C 0` in the exponent. -/
theorem reconstruct_smul_generator_eq_commit_zero (d : F.Desc)
    (params : Shamir.Params (ZMod (F.order d)) Party)
    (C : Fin (params.threshold + 1) → F.Carrier d)
    (S : Finset Party) (hS : Shamir.authorized params S) (σ : S → ZMod (F.order d))
    (hver : ∀ i : S, feldmanVerify F d params C i.1 (σ i) = true) :
    (Shamir.reconstruct params S σ) • F.generator d = C 0 := by
  obtain ⟨P, hdeg, hconst, hval⟩ := exists_commitPolynomial F d params C
  have hσ : σ = fun i : S => P.eval (params.point i.1) := by
    ext i
    exact hval i.1 (σ i) (hver i)
  have hcard : P.degree < Fintype.card S := by
    refine lt_of_lt_of_le hdeg ?_
    have hS' : (params.threshold + 1 : WithBot ℕ) ≤ S.card := by exact_mod_cast hS
    simpa [Shamir.authorized] using hS'
  have hinj : Function.Injective (fun i : S => params.point i.1) := by
    intro i j hij
    exact Subtype.ext (params.point_injective hij)
  rw [hσ, Shamir.reconstruct, Shamir.Polynomial.reconstruct_eq_constantCoeff_of_eval_eq hinj hcard]
  exact hconst

/-- **Cross-coalition consistency**: for an arbitrary commitment vector `C`, any two authorized
coalitions holding verifying shares reconstruct the exact same secret. -/
theorem feldmanVerify_agree_on_authorized (d : F.Desc)
    (params : Shamir.Params (ZMod (F.order d)) Party)
    (C : Fin (params.threshold + 1) → F.Carrier d)
    {S₁ S₂ : Finset Party} (hS₁ : Shamir.authorized params S₁) (hS₂ : Shamir.authorized params S₂)
    {σ₁ : S₁ → ZMod (F.order d)} {σ₂ : S₂ → ZMod (F.order d)}
    (hver₁ : ∀ i : S₁, feldmanVerify F d params C i.1 (σ₁ i) = true)
    (hver₂ : ∀ i : S₂, feldmanVerify F d params C i.1 (σ₂ i) = true) :
    Shamir.reconstruct params S₁ σ₁ = Shamir.reconstruct params S₂ σ₂ := by
  apply F.smul_generator_injective d
  dsimp only
  rw [reconstruct_smul_generator_eq_commit_zero F d params C S₁ hS₁ σ₁ hver₁,
    reconstruct_smul_generator_eq_commit_zero F d params C S₂ hS₂ σ₂ hver₂]

/-- **Committed-secret recovery**: if `C 0 = secret • g`, every authorized coalition holding
verifying shares reconstructs `secret`. -/
theorem reconstruct_eq_of_feldmanVerify_commit_zero (d : F.Desc)
    (params : Shamir.Params (ZMod (F.order d)) Party)
    (C : Fin (params.threshold + 1) → F.Carrier d) {secret : ZMod (F.order d)}
    (hC0 : C 0 = secret • F.generator d)
    (S : Finset Party) (hS : Shamir.authorized params S) (σ : S → ZMod (F.order d))
    (hver : ∀ i : S, feldmanVerify F d params C i.1 (σ i) = true) :
    Shamir.reconstruct params S σ = secret := by
  apply F.smul_generator_injective d
  dsimp only
  rw [reconstruct_smul_generator_eq_commit_zero F d params C S hS σ hver, hC0]

end Soundness

section Simulation

variable (F : PrimeOrderGroupFamily) {Party : Type} [Fintype Party] [DecidableEq Party]

private theorem exists_superset_card_eq (I : Finset Party) {t : ℕ}
    (hI : I.card ≤ t) (ht : t < Fintype.card Party) :
    ∃ J : Finset Party, I ⊆ J ∧ J.card = t := by
  have hrem : t - I.card ≤ (Finset.univ \ I).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ I), Finset.card_univ]
    omega
  obtain ⟨K, hKsub, hKcard⟩ := Finset.exists_subset_card_eq hrem
  refine ⟨I ∪ K, Finset.subset_union_left, ?_⟩
  have hdisj : Disjoint I K := by
    rw [Finset.disjoint_left]
    intro x hx hxK
    exact (Finset.mem_sdiff.mp (hKsub hxK)).2 hx
  rw [Finset.card_union_of_disjoint hdisj, hKcard]
  omega

/-- Interpolation nodes `none ↦ 0` and `some i ↦ params.point i.1` on `Option J`. -/
@[expose] def simNodes {q : ℕ} (params : Shamir.Params (ZMod q) Party) (J : Finset Party)
    (k : Option J) : ZMod q :=
  Option.elim k 0 (fun i => params.point i.1)

omit [DecidableEq Party] in
theorem simNodes_injective {q : ℕ} (params : Shamir.Params (ZMod q) Party) (J : Finset Party) :
    Function.Injective (simNodes params J) := by
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some j => exact absurd hab.symm (params.point_nonzero j.1)
  | some i =>
    cases b with
    | none => exact absurd hab (params.point_nonzero i.1)
    | some j => exact congrArg some (Subtype.ext (params.point_injective hab))

/-- Lagrange basis polynomial over `Option J` for nodes `simNodes params J`. -/
noncomputable def simLagrangePoly {q : ℕ} [Fact q.Prime]
    (params : Shamir.Params (ZMod q) Party) (J : Finset Party) (k : Option J) :
    _root_.Polynomial (ZMod q) :=
  _root_.Lagrange.basis Finset.univ (simNodes params J) k

/-- `j`-th coefficient of `simLagrangePoly params J k`. -/
noncomputable def simLagrangeCoeff {q : ℕ} [Fact q.Prime]
    (params : Shamir.Params (ZMod q) Party) (J : Finset Party) (k : Option J) (j : ℕ) :
    ZMod q :=
  (simLagrangePoly params J k).coeff j

/-- Simulate Feldman commitments `(C 0, …, C t)` in the exponent from `h = secret • g` and
coalition shares `σJ : J → ZMod (F.order d)` with `|J| = params.threshold`. -/
noncomputable def simCommitFromShares (d : F.Desc)
    (params : Shamir.Params (ZMod (F.order d)) Party) (J : Finset Party)
    (h : F.Carrier d) (σJ : J → ZMod (F.order d)) :
    Fin (params.threshold + 1) → F.Carrier d :=
  fun j =>
    (simLagrangeCoeff params J none j.1) • h +
      (∑ i : J, σJ i * simLagrangeCoeff params J (some i) j.1) • F.generator d

theorem simCommitFromShares_eq_feldmanCommit (d : F.Desc)
    (params : Shamir.Params (ZMod (F.order d)) Party) (J : Finset Party)
    (hJ : J.card = params.threshold)
    (secret : ZMod (F.order d)) (r : Shamir.Randomness params) :
    simCommitFromShares F d params J (secret • F.generator d)
        (fun i : J => Shamir.share params r secret i.1) =
      feldmanCommit F d params secret r := by
  let P := Shamir.Polynomial.sharingPolynomial secret
    (Shamir.Polynomial.tailPolynomial params.threshold r)
  have hdeg : P.degree < Fintype.card (Option J) := by
    have hp := Shamir.Polynomial.degree_sharingPolynomial_tailPolynomial_lt_succ
      secret params.threshold r
    simpa [P, Fintype.card_option, Fintype.card_coe, hJ] using hp
  have hP : P = _root_.Lagrange.interpolate Finset.univ (simNodes params J)
      (fun k => P.eval (simNodes params J k)) :=
    _root_.Lagrange.eq_interpolate (s := Finset.univ) (v := simNodes params J)
      (simNodes_injective params J).injOn (by simpa using hdeg)
  ext j
  have hj_coeff : P.coeff j.1 =
      secret * simLagrangeCoeff params J none j.1 +
        ∑ i : J, Shamir.share params r secret i.1 * simLagrangeCoeff params J (some i) j.1 := by
    have hcoeff := congrArg (fun q : _root_.Polynomial (ZMod (F.order d)) => q.coeff j.1) hP
    rw [_root_.Lagrange.interpolate_apply] at hcoeff
    simp_rw [← _root_.Polynomial.lcoeff_apply] at hcoeff
    rw [map_sum] at hcoeff
    simp only [_root_.Polynomial.lcoeff_apply] at hcoeff
    have hsum :
        (∑ k : Option J,
            (_root_.Polynomial.C (P.eval (simNodes params J k)) *
              _root_.Lagrange.basis Finset.univ (simNodes params J) k).coeff j.1) =
          (P.eval 0 * simLagrangeCoeff params J none j.1) +
            ∑ i : J, P.eval (params.point i.1) * simLagrangeCoeff params J (some i) j.1 := by
      simp only [_root_.Polynomial.coeff_C_mul, simLagrangeCoeff, simLagrangePoly]
      rw [Fintype.sum_option]
      rfl
    have hP0 : P.eval 0 = secret := by simp [P]
    rw [hcoeff, hsum, hP0]
    rfl
  have hdealer : P.coeff j.1 = dealerCoeffs F d params secret r j := by
    dsimp only [P]
    rw [sharingPolynomial_eq_sum_dealerCoeffs F d params secret r,
      ← _root_.Polynomial.lcoeff_apply, map_sum]
    simp only [_root_.Polynomial.lcoeff_apply, _root_.Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      have hne : (k : ℕ) ≠ j.1 := fun hkj => hk (Fin.ext hkj)
      simp [hne.symm]
    · simp
  unfold simCommitFromShares feldmanCommit
  rw [← hdealer, hj_coeff, add_smul, smul_smul, mul_comm (simLagrangeCoeff params J none j.1)]

/-- Real Feldman view seen by coalition `I`: commitments `C` and `I`'s Shamir shares under
uniform tail randomness `r`. -/
noncomputable def feldmanView (d : F.Desc) (params : Shamir.Params (ZMod (F.order d)) Party)
    (I : Finset Party) (secret : ZMod (F.order d)) :
    PMF ((Fin (params.threshold + 1) → F.Carrier d) × (I → ZMod (F.order d))) :=
  (PMF.uniformOfFintype (Shamir.Randomness params)).map fun r =>
    (feldmanCommit F d params secret r, fun i : I => Shamir.share params r secret i.1)

/-- Idealized Feldman simulator given only `(secret • g, I)` (with `I.card ≤ params.threshold`):
samples uniform target shares on a `params.threshold`-element superset `J ⊇ I` and reconstructs
commitments in the exponent via `simCommitFromShares`. -/
noncomputable def feldmanSim (d : F.Desc) (params : Shamir.Params (ZMod (F.order d)) Party)
    (I : Finset Party) (hI : I.card ≤ params.threshold) (h : F.Carrier d) :
    PMF ((Fin (params.threshold + 1) → F.Carrier d) × (I → ZMod (F.order d))) :=
  let hJex := exists_superset_card_eq I hI params.threshold_lt_card
  let J := hJex.choose
  have hIJ : I ⊆ J := hJex.choose_spec.1
  (PMF.uniformOfFintype (J → ZMod (F.order d))).map fun σJ =>
    (simCommitFromShares F d params J h σJ, fun i : I => σJ ⟨i.1, hIJ i.2⟩)

/-- **Exact zero-distance simulation**: for every `d`, `secret`, and unauthorized coalition `I`,
`feldmanView` equals `feldmanSim` on input `secret • F.generator d` identically (`PMF` equality). -/
theorem feldmanView_eq_feldmanSim (d : F.Desc) (params : Shamir.Params (ZMod (F.order d)) Party)
    (I : Finset Party) (hI : I.card ≤ params.threshold) (secret : ZMod (F.order d)) :
    feldmanView F d params I secret =
      feldmanSim F d params I hI (secret • F.generator d) := by
  let hJex := exists_superset_card_eq I hI params.threshold_lt_card
  let J := hJex.choose
  have hIJ : I ⊆ J := hJex.choose_spec.1
  have hJt : J.card = params.threshold := hJex.choose_spec.2
  have hunif := Shamir.uniformOfFintype_map_restrict_share params J (le_of_eq hJt) secret
  have hcomp :
      feldmanSim F d params I hI (secret • F.generator d) =
        ((PMF.uniformOfFintype (Shamir.Randomness params)).map
          (fun r (i : J) => Shamir.share params r secret i.1)).map
            (fun σJ => (simCommitFromShares F d params J (secret • F.generator d) σJ,
              fun i : I => σJ ⟨i.1, hIJ i.2⟩)) := by
    change (PMF.uniformOfFintype (J → ZMod (F.order d))).map _ = _
    rw [hunif]
  rw [hcomp, PMF.map_comp]
  unfold feldmanView
  congr 1 with r : 1
  simp only [Function.comp_apply]
  rw [simCommitFromShares_eq_feldmanCommit F d params J hJt secret r]

end Simulation

/-- Input encoding `(n, d, C, σ)` for Feldman secrecy adversaries and chosen-secret
distinguishers with fixed threshold `t` and coalition `I`. -/
noncomputable abbrev encFeldmanInput (F : PrimeOrderGroupFamily) {Party : Type}
    (t : ℕ) (I : Finset Party) :
    (ℕ × F.Desc × (Fin (t + 1) → List Bool) × (I → ℕ)) ↪ List Bool :=
  encPair encUnary (encPair F.encDesc (encPair (encPi encBits) (encPi encNat)))

section Secrecy

variable (F : PrimeOrderGroupFamily) {Party : Type} [Fintype Party] [DecidableEq Party]

/-- Coefficient step multiplying a polynomial modulo `q` by `(X - a)` on `Fin (t + 1) → ℕ`. -/
@[expose] def mulXSubConstMod {t : ℕ} (q a : ℕ) (c : Fin (t + 1) → ℕ) : Fin (t + 1) → ℕ :=
  Fin.cons ((q - a % q) * c 0 % q)
    (fun j : Fin t => (c j.castSucc + (q - a % q) * c j.succ) % q)

private theorem mulXSubConstMod_spec {t q : ℕ} [Fact q.Prime] (a : ℕ)
    (c : Fin (t + 1) → ℕ) (P : _root_.Polynomial (ZMod q))
    (hc : ∀ j : Fin (t + 1), (c j : ZMod q) = P.coeff j.1) :
    ∀ j : Fin (t + 1), (mulXSubConstMod q a c j : ZMod q) =
      ((_root_.Polynomial.X - _root_.Polynomial.C (a : ZMod q)) * P).coeff j.1 := by
  have hq : 0 < q := (Fact.out : q.Prime).pos
  have hneg : ((q - a % q : ℕ) : ZMod q) = -(a : ZMod q) := by
    rw [Nat.cast_sub (Nat.mod_lt _ hq).le, ZMod.natCast_self, ZMod.natCast_mod, zero_sub]
  intro j
  refine Fin.cases ?_ ?_ j
  · simp only [mulXSubConstMod, Fin.cons_zero, Fin.val_zero, ZMod.natCast_mod, Nat.cast_mul,
      hneg, sub_mul, _root_.Polynomial.coeff_sub, _root_.Polynomial.coeff_X_mul_zero,
      _root_.Polynomial.coeff_C_mul, hc 0]
    ring
  · intro k
    simp only [mulXSubConstMod, Fin.cons_succ, Fin.val_succ, ZMod.natCast_mod, Nat.cast_add,
      Nat.cast_mul, hneg, sub_mul, _root_.Polynomial.coeff_sub, _root_.Polynomial.coeff_X_mul,
      _root_.Polynomial.coeff_C_mul, hc k.castSucc, hc k.succ]
    simp only [Fin.val_castSucc]
    ring

/-- Fixed-list numerator coefficients `(∏ m ∈ ms, (X - x m)) mod q` over `Fin (t + 1) → ℕ`. -/
@[expose] def lagrangeNumMod {ι : Type} (t q : ℕ) (x : ι → ℕ) (ms : List ι) :
    Fin (t + 1) → ℕ :=
  ms.foldr (fun m c => mulXSubConstMod q (x m) c) (Fin.cons 1 (fun _ => 0))

private theorem lagrangeNumMod_spec {ι : Type} {t q : ℕ} [Fact q.Prime]
    (x : ι → ℕ) (ms : List ι) :
    ∀ j : Fin (t + 1), (lagrangeNumMod t q x ms j : ZMod q) =
      (ms.map (fun m => _root_.Polynomial.X - _root_.Polynomial.C (x m : ZMod q))).prod.coeff
        j.1 := by
  induction ms with
  | nil =>
    intro j
    refine Fin.cases ?_ ?_ j <;> simp [lagrangeNumMod, _root_.Polynomial.coeff_one]
  | cons hd tl ih =>
    intro j
    change (mulXSubConstMod q (x hd) (lagrangeNumMod t q x tl) j : ZMod q) = _
    rw [List.map_cons, List.prod_cons]
    exact mulXSubConstMod_spec (x hd) (lagrangeNumMod t q x tl) _ ih j

/-- Fixed-list denominator product `(∏ m ∈ ms, (xk - x m)) mod q`. -/
@[expose] def lagrangeDenomMod {ι : Type} (q : ℕ) (x : ι → ℕ) (xk : ℕ) (ms : List ι) : ℕ :=
  ms.foldr (fun m acc => ((xk + (q - x m % q)) * acc) % q) 1

private theorem lagrangeDenomMod_spec {ι : Type} {q : ℕ} [Fact q.Prime]
    (x : ι → ℕ) (xk : ℕ) (ms : List ι) :
    (lagrangeDenomMod q x xk ms : ZMod q) =
      (ms.map (fun m => (xk : ZMod q) - (x m : ZMod q))).prod := by
  have hq : 0 < q := (Fact.out : q.Prime).pos
  induction ms with
  | nil => simp [lagrangeDenomMod]
  | cons hd tl ih =>
    have hneg : ((q - x hd % q : ℕ) : ZMod q) = -(x hd : ZMod q) := by
      rw [Nat.cast_sub (Nat.mod_lt _ hq).le, ZMod.natCast_self, ZMod.natCast_mod, zero_sub]
    simp only [lagrangeDenomMod, List.foldr_cons, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add,
      hneg, ← sub_eq_add_neg, List.map_cons, List.prod_cons]
    change (((xk : ZMod q) - (x hd : ZMod q)) * (lagrangeDenomMod q x xk tl : ZMod q)) = _
    rw [ih]

/-- Coefficient `j` of `simLagrangePoly` modulo `q` via Fermat inversion `denom ^ (q - 2) % q`. -/
@[expose] def lagrangeCoeffMod {ι : Type} [DecidableEq ι] (t q : ℕ) (x : ι → ℕ)
    (ms : List ι) (k : ι) (j : Fin (t + 1)) : ℕ :=
  ((lagrangeDenomMod q x (x k) ms ^ (q - 2) % q) * lagrangeNumMod t q x ms j) % q

private theorem lagrangeCoeffMod_spec {J : Finset Party} {t : ℕ} (d : F.Desc)
    (params : Shamir.Params (ZMod (F.order d)) Party) (_hJt : J.card = t)
    (k : Option J) (j : Fin (t + 1)) :
    (lagrangeCoeffMod t (F.order d)
        (fun m => Option.elim m 0 (fun i => (params.point i.1).val))
        (Finset.univ.erase k).toList k j : ZMod (F.order d)) =
      simLagrangeCoeff params J k j.1 := by
  let q := F.order d
  have : Fact q.Prime := ⟨F.prime_order d⟩
  let xN : Option J → ℕ := fun m => Option.elim m 0 (fun i => (params.point i.1).val)
  have hxZ : ∀ m : Option J, (xN m : ZMod q) = simNodes params J m := by
    intro m; cases m <;> simp [xN, simNodes]
  let ms := (Finset.univ.erase k).toList
  have hprod_num :
      (ms.map (fun m => _root_.Polynomial.X - _root_.Polynomial.C (xN m : ZMod q))).prod =
        ∏ m ∈ Finset.univ.erase k,
          (_root_.Polynomial.X - _root_.Polynomial.C (simNodes params J m)) := by
    rw [Finset.prod_eq_multiset_prod, ← Multiset.prod_coe, ← Multiset.map_coe, Finset.coe_toList]
    simp [hxZ]
  have hprod_den :
      (ms.map (fun m => (xN k : ZMod q) - (xN m : ZMod q))).prod =
        ∏ m ∈ Finset.univ.erase k, (simNodes params J k - simNodes params J m) := by
    rw [Finset.prod_eq_multiset_prod, ← Multiset.prod_coe, ← Multiset.map_coe, Finset.coe_toList]
    simp [hxZ]
  have hden_ne : (∏ m ∈ Finset.univ.erase k, (simNodes params J k - simNodes params J m)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro m hm
    rw [Finset.mem_erase] at hm
    exact sub_ne_zero.mpr (fun heq => hm.1 (simNodes_injective params J heq.symm))
  have hinv :
      ((lagrangeDenomMod q xN (xN k) ms ^ (q - 2) % q : ℕ) : ZMod q) =
        (∏ m ∈ Finset.univ.erase k, (simNodes params J k - simNodes params J m))⁻¹ := by
    rw [ZMod.natCast_mod, Nat.cast_pow, lagrangeDenomMod_spec, hprod_den]
    set denom := ∏ m ∈ Finset.univ.erase k, (simNodes params J k - simNodes params J m)
    have hpow : denom ^ (q - 2) * denom = 1 := by
      have hq1 : q - 2 + 1 = q - 1 := by have := (Fact.out : q.Prime).two_le; omega
      rw [← pow_succ, hq1]
      exact ZMod.pow_card_sub_one_eq_one hden_ne
    exact eq_inv_of_mul_eq_one_left hpow
  have hbasis :
      simLagrangePoly params J k =
        _root_.Polynomial.C
          ((∏ m ∈ Finset.univ.erase k, (simNodes params J k - simNodes params J m))⁻¹) *
          ∏ m ∈ Finset.univ.erase k,
            (_root_.Polynomial.X - _root_.Polynomial.C (simNodes params J m)) := by
    unfold simLagrangePoly _root_.Lagrange.basis
    simp only [_root_.Lagrange.basisDivisor, Finset.prod_mul_distrib]
    rw [← map_prod, ← Finset.prod_inv_distrib]
  dsimp only [simLagrangeCoeff, lagrangeCoeffMod]
  change ((((lagrangeDenomMod q xN (xN k) ms ^ (q - 2) % q) *
      lagrangeNumMod t q xN ms j) % q : ℕ) : ZMod q) =
    (simLagrangePoly params J k).coeff j.1
  rw [ZMod.natCast_mod, Nat.cast_mul, hinv, lagrangeNumMod_spec, hprod_num, hbasis,
    _root_.Polynomial.coeff_C_mul]

/-- Simulated Feldman commitment words from `(d, hWord, σVec)` for fixed `t`, `J`, `eJ`. -/
@[expose] noncomputable def feldmanSimCommitWords (t : ℕ)
    (params : ∀ d : F.Desc, Shamir.Params (ZMod (F.order d)) Party)
    (J : Finset Party) (eJ : Fin t ≃ J)
    (d : F.Desc) (hWord : List Bool) (σVec : Fin t → ℕ) : Fin (t + 1) → List Bool :=
  let q := F.order d
  let x : Option J → ℕ := fun m => Option.elim m 0 (fun i => ((params d).point i.1).val)
  let msNone := (Finset.univ.erase (none : Option J)).toList
  let js := (Finset.univ : Finset J).toList
  fun j =>
    let cNone := lagrangeCoeffMod t q x msNone none j
    let cShares := js.foldr
      (fun i acc =>
        ((σVec (eJ.symm i) % q) *
          lagrangeCoeffMod t q x (Finset.univ.erase (some i)).toList (some i) j + acc) % q) 0
    F.add (d, F.smul (d, cNone, hWord), F.smul (d, cShares, F.encode d (F.generator d)))

private theorem feldmanSimCommitWords_encode {t : ℕ} (d : F.Desc)
    (params : ∀ d : F.Desc, Shamir.Params (ZMod (F.order d)) Party)
    (hthresh : (params d).threshold = t)
    (J : Finset Party) (hJt : J.card = t) (eJ : Fin t ≃ J)
    (h : F.Carrier d) (σVec : Fin t → ℕ) (j : Fin (t + 1)) :
    feldmanSimCommitWords F t params J eJ d (F.encode d h) σVec j =
      F.encode d (simCommitFromShares F d (params d) J h
        (fun i : J => ((σVec (eJ.symm i) : ℕ) : ZMod (F.order d)))
          ⟨j.1, by rw [hthresh]; exact j.2⟩) := by
  let q := F.order d
  let x : Option J → ℕ := fun m => Option.elim m 0 (fun i => ((params d).point i.1).val)
  let js := (Finset.univ : Finset J).toList
  have hsum_fold :
      ((js.foldr (fun i acc =>
        ((σVec (eJ.symm i) % q) *
          lagrangeCoeffMod t q x (Finset.univ.erase (some i)).toList (some i) j + acc) % q)
        0 : ℕ) : ZMod q) =
      ∑ i : J, (σVec (eJ.symm i) : ZMod q) *
        simLagrangeCoeff (params d) J (some i) j.1 := by
    have hfold : ∀ ls : List J,
        ((ls.foldr (fun i acc =>
          ((σVec (eJ.symm i) % q) *
            lagrangeCoeffMod t q x (Finset.univ.erase (some i)).toList (some i) j + acc) % q)
          0 : ℕ) : ZMod q) =
        (ls.map fun i => (σVec (eJ.symm i) : ZMod q) *
          simLagrangeCoeff (params d) J (some i) j.1).sum := by
      intro ls
      induction ls with
      | nil => simp
      | cons hd tl ih =>
        dsimp only [q, x]
        rw [List.foldr_cons, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, ZMod.natCast_mod,
          lagrangeCoeffMod_spec F d (params d) hJt, ih]
        simp [List.map_cons, List.sum_cons]
    rw [hfold js, ← Multiset.sum_coe, ← Multiset.map_coe, show (js : Multiset J) = Finset.univ.val
      from Finset.coe_toList _, ← Finset.sum_eq_multiset_sum]
  have hnone := lagrangeCoeffMod_spec F d (params d) hJt none j
  dsimp only [feldmanSimCommitWords, simCommitFromShares]
  dsimp only [q, x, js] at hsum_fold
  rw [F.smul_encode, F.smul_encode, F.add_encode, hnone, hsum_fold]

private theorem computableInPolyTime_mulXSubConstMod {α : Type} {input : α ↪ List Bool}
    {t : ℕ} {fq fa : α → ℕ} {fc : α → Fin (t + 1) → ℕ}
    (hq : ComputableInPolyTime fq input encNat)
    (ha : ComputableInPolyTime fa input encNat)
    (hc : ComputableInPolyTime fc input (encPi encNat)) :
    ComputableInPolyTime (fun z => mulXSubConstMod (fq z) (fa z) (fc z))
      input (encPi encNat) := by
  refine .of_tidy (ComputableTidilyInPolyTime.pi fun j => ?_)
  refine Fin.cases ?_ ?_ j
  · have hq' := hq.tidy
    have ha' := ha.tidy
    have hc0 : ComputableTidilyInPolyTime (fun z => fc z 0) input encNat :=
      (ComputableTidilyInPolyTime.pi_apply encNat 0).comp hc.tidy
    simpa [mulXSubConstMod] using
      ComputableTidilyInPolyTime.binary_mod'
        (ComputableTidilyInPolyTime.binary_mul'
          (ComputableTidilyInPolyTime.binary_sub' hq'
            (ComputableTidilyInPolyTime.binary_mod' ha' hq')) hc0) hq'
  · intro k
    have hq' := hq.tidy
    have ha' := ha.tidy
    have hck1 : ComputableTidilyInPolyTime (fun z => fc z k.castSucc) input encNat :=
      (ComputableTidilyInPolyTime.pi_apply encNat k.castSucc).comp hc.tidy
    have hck2 : ComputableTidilyInPolyTime (fun z => fc z k.succ) input encNat :=
      (ComputableTidilyInPolyTime.pi_apply encNat k.succ).comp hc.tidy
    simpa [mulXSubConstMod] using
      ComputableTidilyInPolyTime.binary_mod'
        (ComputableTidilyInPolyTime.binary_add' hck1
          (ComputableTidilyInPolyTime.binary_mul'
            (ComputableTidilyInPolyTime.binary_sub' hq'
              (ComputableTidilyInPolyTime.binary_mod' ha' hq')) hck2)) hq'

private theorem computableInPolyTime_lagrangeCoeffMod {ι : Type} [DecidableEq ι]
    (t : ℕ) (x : ι → F.Desc → ℕ)
    (hx : ∀ m : ι, ComputableInPolyTime (x m) F.encDesc encNat)
    (ms : List ι) (k : ι) (j : Fin (t + 1)) :
    ComputableInPolyTime
      (fun d => lagrangeCoeffMod t (F.order d) (fun m => x m d) ms k j)
      F.encDesc encNat := by
  have hord := F.computableInPolyTime_order
  have hnum : ComputableInPolyTime
      (fun d => lagrangeNumMod t (F.order d) (fun m => x m d) ms)
      F.encDesc (encPi encNat) := by
    induction ms with
    | nil =>
      exact ComputableInPolyTime.const _
    | cons m tl ih =>
      exact computableInPolyTime_mulXSubConstMod hord (hx m) ih
  have hden : ComputableInPolyTime
      (fun d => lagrangeDenomMod (F.order d) (fun m => x m d) (x k d) ms)
      F.encDesc encNat := by
    clear hnum
    induction ms with
    | nil =>
      exact ComputableInPolyTime.const 1
    | cons m tl ih =>
      have hsub := ComputableInPolyTime.binary_sub' hord
        (.of_tidy (.binary_mod' (hx m).tidy hord.tidy))
      have hadd := ComputableInPolyTime.binary_add' (hx k) hsub
      have hmul := ComputableInPolyTime.binary_mul' hadd ih
      exact .of_tidy (.binary_mod' hmul.tidy hord.tidy)
  have h2 : ComputableInPolyTime (fun _ : F.Desc => (2 : ℕ)) F.encDesc encNat :=
    ComputableInPolyTime.const 2
  have hexp := ComputableInPolyTime.binary_sub' hord h2
  have hinv := ComputableInPolyTime.binary_powMod hden hexp hord
    (fun d => (F.prime_order d).pos)
  have hj := ((ComputableTidilyInPolyTime.pi_apply encNat j).computableInPolyTime).comp hnum
  have hmul := ComputableInPolyTime.binary_mul' hinv hj
  exact .of_tidy (.binary_mod' hmul.tidy hord.tidy)

private theorem computableInPolyTime_feldmanSimCommitWords (t : ℕ)
    (params : ∀ d : F.Desc, Shamir.Params (ZMod (F.order d)) Party)
    (hpoint : ∀ i : Party,
      ComputableInPolyTime (fun d => ((params d).point i).val) F.encDesc encNat)
    (J : Finset Party) (eJ : Fin t ≃ J) :
    ComputableInPolyTime
      (fun p : (F.Desc × List Bool) × (Fin t → ℕ) =>
        feldmanSimCommitWords F t params J eJ p.1.1 p.1.2 p.2)
      (encPair (encPair F.encDesc encBits) (encPi encNat)) (encPi encBits) := by
  let encIn := encPair (encPair F.encDesc encBits) (encPi (Index := Fin t) encNat)
  have hd : ComputableInPolyTime (fun p : (F.Desc × List Bool) × (Fin t → ℕ) => p.1.1)
      encIn F.encDesc := by fun_prop
  have hh : ComputableInPolyTime (fun p : (F.Desc × List Bool) × (Fin t → ℕ) => p.1.2)
      encIn encBits := by fun_prop
  have hσ : ComputableInPolyTime (fun p : (F.Desc × List Bool) × (Fin t → ℕ) => p.2)
      encIn (encPi encNat) := by fun_prop
  have hx : ∀ m : Option J,
      ComputableInPolyTime (fun d => Option.elim m 0 (fun i => ((params d).point i.1).val))
        F.encDesc encNat := by
    intro m
    cases m with
    | none => exact ComputableInPolyTime.const 0
    | some i => exact hpoint i.1
  have hord := F.computableInPolyTime_order.comp hd
  have hg := F.computableInPolyTime_generator.comp hd
  refine .of_tidy (ComputableTidilyInPolyTime.pi fun j => ?_)
  have hcNone : ComputableInPolyTime
      (fun p : (F.Desc × List Bool) × (Fin t → ℕ) =>
        lagrangeCoeffMod t (F.order p.1.1)
          (fun m => Option.elim m 0 (fun i => ((params p.1.1).point i.1).val))
          (Finset.univ.erase (none : Option J)).toList none j)
      encIn encNat :=
    (computableInPolyTime_lagrangeCoeffMod F t _ hx _ none j).comp hd
  have hcShares : ∀ ls : List J, ComputableInPolyTime
      (fun p : (F.Desc × List Bool) × (Fin t → ℕ) =>
        ls.foldr (fun i acc =>
          ((p.2 (eJ.symm i) % F.order p.1.1) *
            lagrangeCoeffMod t (F.order p.1.1)
              (fun m => Option.elim m 0 (fun i => ((params p.1.1).point i.1).val))
              (Finset.univ.erase (some i)).toList (some i) j + acc) % F.order p.1.1) 0)
      encIn encNat := by
    intro ls
    induction ls with
    | nil => exact ComputableInPolyTime.const 0
    | cons i tl ih =>
      have hσi : ComputableInPolyTime
          (fun p : (F.Desc × List Bool) × (Fin t → ℕ) => p.2 (eJ.symm i)) encIn encNat :=
        ((ComputableTidilyInPolyTime.pi_apply encNat (eJ.symm i)).computableInPolyTime).comp hσ
      have hσmod : ComputableInPolyTime
          (fun p : (F.Desc × List Bool) × (Fin t → ℕ) => p.2 (eJ.symm i) % F.order p.1.1)
          encIn encNat := .of_tidy (.binary_mod' hσi.tidy hord.tidy)
      have hci := (computableInPolyTime_lagrangeCoeffMod F t
        (fun m d => Option.elim m 0 (fun i => ((params d).point i.1).val))
        hx (Finset.univ.erase (some i)).toList (some i) j).comp hd
      have hterm := ComputableInPolyTime.binary_mul' hσmod hci
      have hsum := ComputableInPolyTime.binary_add' hterm ih
      exact .of_tidy (.binary_mod' hsum.tidy hord.tidy)
  have hleft := F.computableInPolyTime_smul.comp (hd.prod (hcNone.prod hh))
  have hright := F.computableInPolyTime_smul.comp
    (hd.prod ((hcShares (Finset.univ : Finset J).toList).prod hg))
  have hres := F.computableInPolyTime_add.comp (hd.prod (hleft.prod hright))
  exact hres.tidy

/-- Sample `k` candidate exponents sequentially using `F.sampleExp n d`. -/
noncomputable def sampleExpVec (n : ℕ) (d : F.Desc) : (k : ℕ) → ProbComp (Fin k → ℕ)
  | 0 => pure Fin.elim0
  | k + 1 => do
    let head ← F.sampleExp n d
    let tail ← sampleExpVec n d k
    return Fin.cons head tail

private theorem isPPTOn_sampleExpVec (k : ℕ) :
    IsPPTOn (encPair encUnary F.encDesc) (encPi encNat)
      (fun p => sampleExpVec F p.1 p.2 k) := by
  induction k with
  | zero =>
    have hc : ComputableInPolyTime (fun _ : ℕ × F.Desc => (Fin.elim0 : Fin 0 → ℕ))
        (encPair encUnary F.encDesc) (encPi encNat) :=
      .of_tidy (ComputableTidilyInPolyTime.pi fun i => i.elim0)
    exact hc.isPPTOn
  | succ k ih =>
    unfold sampleExpVec
    have hn : ComputableInPolyTime (fun p : ℕ × F.Desc => p.1)
        (encPair encUnary F.encDesc) encUnary := by fun_prop
    have hd : ComputableInPolyTime (fun p : ℕ × F.Desc => p.2)
        (encPair encUnary F.encDesc) F.encDesc := by fun_prop
    refine (F.isPPTOn_sampleExp hn hd).bind_with ?_
    have ih' : IsPPTOn (encPair (encPair encUnary F.encDesc) encNat) (encPi encNat)
        (fun p : (ℕ × F.Desc) × ℕ => sampleExpVec F p.1.1 p.1.2 k) := by
      have hfst : ComputableInPolyTime
          (fun p : (ℕ × F.Desc) × ℕ => p.1)
          (encPair (encPair encUnary F.encDesc) encNat) (encPair encUnary F.encDesc) := by
        fun_prop
      exact IsPPTOn.preprocess ih hfst
    refine ih'.bind_with ?_
    have hcons : ComputableInPolyTime
        (fun p : ((ℕ × F.Desc) × ℕ) × (Fin k → ℕ) => Fin.cons p.1.2 p.2)
        (encPair (encPair (encPair encUnary F.encDesc) encNat) (encPi encNat))
        (encPi encNat) := by
      refine .of_tidy (ComputableTidilyInPolyTime.pi fun i => ?_)
      refine Fin.cases ?_ ?_ i
      · simp only [Fin.cons_zero]
        fun_prop
      · intro j
        simp only [Fin.cons_succ]
        have h2 : ComputableInPolyTime
            (fun p : ((ℕ × F.Desc) × ℕ) × (Fin k → ℕ) => p.2)
            (encPair (encPair (encPair encUnary F.encDesc) encNat) (encPi encNat))
            (encPi encNat) := by fun_prop
        exact ((ComputableTidilyInPolyTime.pi_apply encNat j).comp h2.tidy)
    exact hcons.isPPTOn

private theorem closeTo_sampleExpVec (n : ℕ) (d : F.Desc) (k : ℕ) :
    CloseTo (PMF.uniformOfFintype (Fin k → ZMod (F.order d)))
      ((ProbComp.eval (sampleExpVec F n d k)).map
        (fun v j => (v j : ZMod (F.order d))))
      ((k : ℝ≥0∞) / 2 ^ n) := by
  induction k with
  | zero =>
    have heq : PMF.uniformOfFintype (Fin 0 → ZMod (F.order d)) =
        ((ProbComp.eval (sampleExpVec F n d 0)).map
          (fun v j => (v j : ZMod (F.order d)))) := by
      ext v
      have hv : v = Fin.elim0 := funext fun j => j.elim0
      subst hv
      have hfn : (Fin.elim0 : Fin 0 → ZMod (F.order d)) =
          fun j => ((Fin.elim0 j : ℕ) : ZMod (F.order d)) :=
        funext fun j => j.elim0
      simp [sampleExpVec, ← hfn]
    rw [heq]
    exact (CloseTo.refl _).mono zero_le
  | succ k ih =>
    have h1 : CloseTo (PMF.uniformOfFintype (ZMod (F.order d)))
        ((ProbComp.eval (F.sampleExp n d)).map (Nat.cast : ℕ → ZMod (F.order d)))
        ((1 : ℝ≥0∞) / 2 ^ n) := by
      classical
      refine Game.closeTo_of_coe_advantage_decide_le fun E => ?_
      have hadv := F.advantage_bind_sampleExp_le n d (fun a => PMF.pure (decide (a ∈ E)))
      rw [Game.advantage_comm] at hadv
      rw [PMF.map_comp, ← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
      have hcoe : (((1 : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ≥0∞) = (1 : ℝ≥0∞) / 2 ^ n := by simp
      rw [← hcoe, ENNReal.coe_le_coe]
      simpa only [Function.comp_def] using hadv
    have hunif : PMF.uniformOfFintype (Fin (k + 1) → ZMod (F.order d)) =
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun head =>
          (PMF.uniformOfFintype (Fin k → ZMod (F.order d))).map fun tail =>
            Fin.cons head tail := by
      let e : ZMod (F.order d) × (Fin k → ZMod (F.order d)) ≃
          (Fin (k + 1) → ZMod (F.order d)) :=
        { toFun := fun p => Fin.cons p.1 p.2
          invFun := fun f => (f 0, Fin.tail f)
          left_inv := fun ⟨a, f⟩ => by simp
          right_inv := fun f => Fin.cons_self_tail f }
      have hprod :
          ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun head =>
            (PMF.uniformOfFintype (Fin k → ZMod (F.order d))).map fun tail =>
              Fin.cons head tail) =
          (PMF.uniformOfFintype (ZMod (F.order d) × (Fin k → ZMod (F.order d)))).map e := by
        rw [← PMF.uniformOfFintype_prod, PMF.map_bind]
        congr 1 with a : 1
        rw [PMF.map_comp]
        rfl
      rw [hprod, PMF.uniformOfFintype_map_equiv e]
    have hsim :
        ((ProbComp.eval (sampleExpVec F n d (k + 1))).map
          (fun v j => (v j : ZMod (F.order d)))) =
        ((ProbComp.eval (F.sampleExp n d)).map (Nat.cast : ℕ → ZMod (F.order d))).bind
          fun head =>
            ((ProbComp.eval (sampleExpVec F n d k)).map
              (fun v j => (v j : ZMod (F.order d)))).map fun tail =>
                Fin.cons head tail := by
      simp only [sampleExpVec, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind,
        PMF.bind_map, PMF.pure_map, PMF.map_comp, Function.comp_def]
      congr 1 with a : 1
      rw [← PMF.bind_pure_comp]
      congr 1 with v : 1
      simp only [Function.comp_def]
      congr 1
      ext j
      refine Fin.cases rfl (fun _ => rfl) j
    rw [hunif, hsim]
    have hbind :
        CloseTo
          ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun head =>
            (PMF.uniformOfFintype (Fin k → ZMod (F.order d))).map
              (Fin.cons (α := fun _ => ZMod (F.order d)) head))
          (((ProbComp.eval (F.sampleExp n d)).map (Nat.cast : ℕ → ZMod (F.order d))).bind
            fun head =>
              ((ProbComp.eval (sampleExpVec F n d k)).map
                (fun v j => (v j : ZMod (F.order d)))).map
                (Fin.cons (α := fun _ => ZMod (F.order d)) head))
          ((1 : ℝ≥0∞) / 2 ^ n + (k : ℝ≥0∞) / 2 ^ n) := by
      refine CloseTo.bind h1 fun head _ => ?_
      exact ih.map (Fin.cons (α := fun _ => ZMod (F.order d)) head)
    refine hbind.mono ?_
    rw [← ENNReal.add_div, add_comm (1 : ℝ≥0∞) k, Nat.cast_add, Nat.cast_one]

/-- Uniform-secret Feldman secrecy experiment: draws a uniform secret `s`, publishes Feldman
commitments `C` and coalition `I`'s Shamir shares `σ`, and checks whether `adversary` recovers
`s`. -/
noncomputable def feldmanSecrecyGame (setup : ℕ → PMF F.Desc) {t : ℕ}
    (params : ∀ d : F.Desc, Shamir.Params (ZMod (F.order d)) Party)
    (hthresh : ∀ d, (params d).threshold = t) (I : Finset Party)
    (adversary : ℕ → F.Desc × (Fin (t + 1) → List Bool) × (I → ℕ) → ProbComp (List Bool))
    (n : ℕ) : Game := do
  let d ← setup n
  let secret ← PMF.uniformOfFintype (ZMod (F.order d))
  let r ← PMF.uniformOfFintype (Shamir.Randomness (params d))
  let C : Fin (t + 1) → List Bool := fun j =>
    F.encode d (feldmanCommit F d (params d) secret r ⟨j.1, by rw [hthresh d]; exact j.2⟩)
  let σ : I → ℕ := fun i => (Shamir.share (params d) r secret i.1).val
  let guess ← ProbComp.eval (adversary n (d, C, σ))
  return decide ((ofBits guess : ZMod (F.order d)) = secret)

/-- Discrete-logarithm adversary simulating Feldman commitments and `I`'s shares in the
exponent from challenge `hWord = F.encode d (α • g)` via Lagrange interpolation. -/
noncomputable def feldmanToDLAdversary {t : ℕ}
    (params : ∀ d : F.Desc, Shamir.Params (ZMod (F.order d)) Party)
    (I : Finset Party) (hI : I.card ≤ t) (ht : t < Fintype.card Party)
    (adversary : ℕ → F.Desc × (Fin (t + 1) → List Bool) × (I → ℕ) → ProbComp (List Bool))
    (n : ℕ) (input : F.Desc × List Bool) : ProbComp (List Bool) :=
  let J := (exists_superset_card_eq I hI ht).choose
  let eJ : Fin t ≃ J :=
    (Fintype.equivFinOfCardEq
      (by simp only [Fintype.card_coe]; exact (exists_superset_card_eq I hI ht).choose_spec.2)).symm
  do
    let σVec ← sampleExpVec F n input.1 t
    let C := feldmanSimCommitWords F t params J eJ input.1 input.2 σVec
    let σ : I → ℕ := fun i =>
      σVec (eJ.symm ⟨i.1, (exists_superset_card_eq I hI ht).choose_spec.1 i.2⟩) %
        F.order input.1
    adversary n (input.1, C, σ)

/-- **Strict-PPT preservation**: `feldmanToDLAdversary` is uniform strict PPT whenever
`adversary` and the evaluation points `params.point` are. -/
theorem isPPTOn_feldmanToDLAdversary {t : ℕ}
    (params : ∀ d : F.Desc, Shamir.Params (ZMod (F.order d)) Party)
    (hpoint : ∀ i : Party,
      ComputableInPolyTime (fun d => ((params d).point i).val) F.encDesc encNat)
    (I : Finset Party) (hI : I.card ≤ t) (ht : t < Fintype.card Party)
    (adversary : ℕ → F.Desc × (Fin (t + 1) → List Bool) × (I → ℕ) → ProbComp (List Bool))
    (hadv : IsPPTOn (encFeldmanInput F t I) encBits (fun p => adversary p.1 p.2)) :
    IsPPTOn (encPair encUnary (encPair F.encDesc encBits)) encBits
      (fun p => feldmanToDLAdversary F params I hI ht adversary p.1 p.2) := by
  let hJex := exists_superset_card_eq I hI ht
  let J := hJex.choose
  have hIJ : I ⊆ J := hJex.choose_spec.1
  have hJt : J.card = t := hJex.choose_spec.2
  let eJ : Fin t ≃ J := (Fintype.equivFinOfCardEq (by simp [hJt])).symm
  let encDL := encPair encUnary (encPair F.encDesc encBits)
  let encAdv := encPair encUnary
    (encPair F.encDesc (encPair (encPi (Index := Fin (t + 1)) encBits) (encPi (Index := I) encNat)))
  change IsPPTOn encDL encBits fun p : ℕ × F.Desc × List Bool =>
    sampleExpVec F p.1 p.2.1 t >>= fun σVec =>
      adversary p.1 (p.2.1, feldmanSimCommitWords F t params J eJ p.2.1 p.2.2 σVec,
        fun i => σVec (eJ.symm ⟨i.1, hIJ i.2⟩) % F.order p.2.1)
  have hsamp : IsPPTOn encDL (encPi encNat) (fun p => sampleExpVec F p.1 p.2.1 t) := by
    have hproj : ComputableInPolyTime (fun p : ℕ × F.Desc × List Bool => (p.1, p.2.1))
        encDL (encPair encUnary F.encDesc) := by fun_prop
    exact IsPPTOn.preprocess (isPPTOn_sampleExpVec F t) hproj
  refine hsamp.bind_with ?_
  let encMid := encPair encDL (encPi (Index := Fin t) encNat)
  have hpre : ComputableInPolyTime
      (fun p : (ℕ × F.Desc × List Bool) × (Fin t → ℕ) =>
        (p.1.1, (p.1.2.1, feldmanSimCommitWords F t params J eJ p.1.2.1 p.1.2.2 p.2,
          fun i : I => p.2 (eJ.symm ⟨i.1, hIJ i.2⟩) % F.order p.1.2.1)))
      encMid encAdv := by
    have hn : ComputableInPolyTime (fun p : (ℕ × F.Desc × List Bool) × (Fin t → ℕ) => p.1.1)
        encMid encUnary := by fun_prop
    have hd : ComputableInPolyTime (fun p : (ℕ × F.Desc × List Bool) × (Fin t → ℕ) => p.1.2.1)
        encMid F.encDesc := by fun_prop
    have hdh : ComputableInPolyTime
        (fun p : (ℕ × F.Desc × List Bool) × (Fin t → ℕ) => (p.1.2, p.2))
        encMid (encPair (encPair F.encDesc encBits) (encPi encNat)) := by fun_prop
    have hC := (computableInPolyTime_feldmanSimCommitWords F t params hpoint J eJ).comp hdh
    have hσ : ComputableInPolyTime (fun p : (ℕ × F.Desc × List Bool) × (Fin t → ℕ) => p.2)
        encMid (encPi encNat) := by fun_prop
    have hord := F.computableInPolyTime_order.comp hd
    have hshares : ComputableInPolyTime
        (fun p : (ℕ × F.Desc × List Bool) × (Fin t → ℕ) =>
          fun i : I => p.2 (eJ.symm ⟨i.1, hIJ i.2⟩) % F.order p.1.2.1)
        encMid (encPi encNat) := by
      refine .of_tidy (ComputableTidilyInPolyTime.pi fun i => ?_)
      have hsel := (ComputableTidilyInPolyTime.pi_apply encNat (eJ.symm ⟨i.1, hIJ i.2⟩)).comp
        hσ.tidy
      exact ComputableTidilyInPolyTime.binary_mod' hsel hord.tidy
    exact hn.prod (hd.prod (hC.prod hshares))
  exact IsPPTOn.preprocess hadv hpre

/-- **Concrete security reduction**: `feldmanSecrecyGame` success probability exceeds that of
`F.discreteLogGame setup (feldmanToDLAdversary ...)` by at most `t / 2 ^ n`. -/
theorem succProbability_feldmanSecrecyGame_le_discreteLogGame
    (setup : ℕ → PMF F.Desc) {t : ℕ}
    (params : ∀ d : F.Desc, Shamir.Params (ZMod (F.order d)) Party)
    (hthresh : ∀ d, (params d).threshold = t)
    (I : Finset Party) (hI : I.card ≤ t) (ht : t < Fintype.card Party)
    (adversary : ℕ → F.Desc × (Fin (t + 1) → List Bool) × (I → ℕ) → ProbComp (List Bool))
    (n : ℕ) :
    Game.succProbability (feldmanSecrecyGame F setup params hthresh I adversary n) ≤
      Game.succProbability
        (F.discreteLogGame setup (feldmanToDLAdversary F params I hI ht adversary) n) +
        (t : ℝ≥0) / 2 ^ n := by
  let hJex := exists_superset_card_eq I hI ht
  let J := hJex.choose
  have hIJ : I ⊆ J := hJex.choose_spec.1
  have hJt : J.card = t := hJex.choose_spec.2
  let eJ : Fin t ≃ J := (Fintype.equivFinOfCardEq (by simp [hJt])).symm
  let idealDL : Game := do
    let d ← setup n
    let s ← PMF.uniformOfFintype (ZMod (F.order d))
    let σVec ← PMF.uniformOfFintype (Fin t → ZMod (F.order d))
    let σJ : J → ZMod (F.order d) := fun i => σVec (eJ.symm i)
    let C : Fin (t + 1) → List Bool := fun j =>
      F.encode d (simCommitFromShares F d (params d) J (s • F.generator d) σJ
        ⟨j.1, by rw [hthresh d]; exact j.2⟩)
    let σ : I → ℕ := fun i => (σJ ⟨i.1, hIJ i.2⟩).val
    let guess ← ProbComp.eval (adversary n (d, C, σ))
    return decide ((ofBits guess : ZMod (F.order d)) = s)
  have hreal_eq : feldmanSecrecyGame F setup params hthresh I adversary n = idealDL := by
    unfold feldmanSecrecyGame idealDL
    refine bind_congr fun d => ?_
    refine bind_congr fun s => ?_
    have hJ_unif :
        (PMF.uniformOfFintype (Fin t → ZMod (F.order d))).map
            (fun σVec (i : J) => σVec (eJ.symm i)) =
          PMF.uniformOfFintype (J → ZMod (F.order d)) := by
      let eqJ : (Fin t → ZMod (F.order d)) ≃ (J → ZMod (F.order d)) :=
        { toFun := fun f i => f (eJ.symm i)
          invFun := fun g j => g (eJ j)
          left_inv := fun f => by ext j; simp
          right_inv := fun g => by ext i; simp }
      exact PMF.uniformOfFintype_map_equiv eqJ
    have hview_J :
        ((PMF.uniformOfFintype (Shamir.Randomness (params d))).map fun r =>
          (feldmanCommit F d (params d) s r,
            fun i : I => Shamir.share (params d) r s i.1)) =
        ((PMF.uniformOfFintype (J → ZMod (F.order d))).map fun σJ =>
          (simCommitFromShares F d (params d) J (s • F.generator d) σJ,
            fun i : I => σJ ⟨i.1, hIJ i.2⟩)) := by
      rw [← Shamir.uniformOfFintype_map_restrict_share (params d) J
        (by rw [hJt, hthresh d]) s, PMF.map_comp]
      congr 1 with r : 1
      simp only [Function.comp_apply]
      rw [simCommitFromShares_eq_feldmanCommit F d (params d) J (by rw [hJt, hthresh d]) s r]
    let cont : ((Fin ((params d).threshold + 1) → F.Carrier d) × (I → ZMod (F.order d))) →
        Game := fun p =>
      (ProbComp.eval (adversary n (d,
        fun j => F.encode d (p.1 ⟨j.1, by rw [hthresh d]; exact j.2⟩),
        fun i => (p.2 i).val))).bind fun guess =>
          PMF.pure (decide ((ofBits guess : ZMod (F.order d)) = s))
    have hl :
        ((PMF.uniformOfFintype (Shamir.Randomness (params d))).bind fun r =>
          let C : Fin (t + 1) → List Bool := fun j =>
            F.encode d (feldmanCommit F d (params d) s r ⟨j.1, by rw [hthresh d]; exact j.2⟩)
          let σ : I → ℕ := fun i => (Shamir.share (params d) r s i.1).val
          (ProbComp.eval (adversary n (d, C, σ))).bind fun guess =>
            PMF.pure (decide ((ofBits guess : ZMod (F.order d)) = s))) =
        ((PMF.uniformOfFintype (Shamir.Randomness (params d))).map fun r =>
          (feldmanCommit F d (params d) s r,
            fun i : I => Shamir.share (params d) r s i.1)).bind cont := by
      rw [PMF.bind_map]
      rfl
    have hr :
        ((PMF.uniformOfFintype (Fin t → ZMod (F.order d))).bind fun σVec =>
          let σJ : J → ZMod (F.order d) := fun i => σVec (eJ.symm i)
          let C : Fin (t + 1) → List Bool := fun j =>
            F.encode d (simCommitFromShares F d (params d) J (s • F.generator d) σJ
              ⟨j.1, by rw [hthresh d]; exact j.2⟩)
          let σ : I → ℕ := fun i => (σJ ⟨i.1, hIJ i.2⟩).val
          (ProbComp.eval (adversary n (d, C, σ))).bind fun guess =>
            PMF.pure (decide ((ofBits guess : ZMod (F.order d)) = s))) =
        ((PMF.uniformOfFintype (J → ZMod (F.order d))).map fun σJ =>
          (simCommitFromShares F d (params d) J (s • F.generator d) σJ,
            fun i : I => σJ ⟨i.1, hIJ i.2⟩)).bind cont := by
      have hr0 :
          ((PMF.uniformOfFintype (Fin t → ZMod (F.order d))).bind fun σVec =>
            cont (simCommitFromShares F d (params d) J (s • F.generator d)
                (fun i => σVec (eJ.symm i)),
              fun i => σVec (eJ.symm ⟨i.1, hIJ i.2⟩))) =
          ((PMF.uniformOfFintype (Fin t → ZMod (F.order d))).map
              (fun σVec (i : J) => σVec (eJ.symm i))).bind
            (fun σJ => cont (simCommitFromShares F d (params d) J (s • F.generator d) σJ,
              fun i => σJ ⟨i.1, hIJ i.2⟩)) := by
        rw [PMF.bind_map]
        rfl
      dsimp only [cont] at hr0 ⊢
      rw [hr0, hJ_unif, PMF.bind_map]
      rfl
    change ((PMF.uniformOfFintype (Shamir.Randomness (params d))).bind fun r =>
        let C : Fin (t + 1) → List Bool := fun j =>
          F.encode d (feldmanCommit F d (params d) s r ⟨j.1, by rw [hthresh d]; exact j.2⟩)
        let σ : I → ℕ := fun i => (Shamir.share (params d) r s i.1).val
        (ProbComp.eval (adversary n (d, C, σ))).bind fun guess =>
          PMF.pure (decide ((ofBits guess : ZMod (F.order d)) = s))) =
      ((PMF.uniformOfFintype (Fin t → ZMod (F.order d))).bind fun σVec =>
        let σJ : J → ZMod (F.order d) := fun i => σVec (eJ.symm i)
        let C : Fin (t + 1) → List Bool := fun j =>
          F.encode d (simCommitFromShares F d (params d) J (s • F.generator d) σJ
            ⟨j.1, by rw [hthresh d]; exact j.2⟩)
        let σ : I → ℕ := fun i => (σJ ⟨i.1, hIJ i.2⟩).val
        (ProbComp.eval (adversary n (d, C, σ))).bind fun guess =>
          PMF.pure (decide ((ofBits guess : ZMod (F.order d)) = s)))
    rw [hl, hr, hview_J]
  have hclose : CloseTo idealDL
      (F.discreteLogGame setup (feldmanToDLAdversary F params I hI ht adversary) n)
      ((t : ℝ≥0∞) / 2 ^ n) := by
    unfold idealDL PrimeOrderGroupFamily.discreteLogGame
    refine CloseTo.bind_right _ fun d _ => ?_
    refine CloseTo.bind_right _ fun s _ => ?_
    let cont : (Fin t → ZMod (F.order d)) → Game := fun σVec =>
      let σJ : J → ZMod (F.order d) := fun i => σVec (eJ.symm i)
      let C : Fin (t + 1) → List Bool := fun j =>
        F.encode d (simCommitFromShares F d (params d) J (s • F.generator d) σJ
          ⟨j.1, by rw [hthresh d]; exact j.2⟩)
      let σ : I → ℕ := fun i => (σJ ⟨i.1, hIJ i.2⟩).val
      (ProbComp.eval (adversary n (d, C, σ))).bind fun guess =>
        PMF.pure (decide ((ofBits guess : ZMod (F.order d)) = s))
    have hc := (closeTo_sampleExpVec F n d t).bind_left cont
    rw [PMF.bind_map] at hc
    have hrhs :
        ((ProbComp.eval (sampleExpVec F n d t)).bind fun v =>
          cont (fun j => (v j : ZMod (F.order d)))) =
        ((ProbComp.eval (feldmanToDLAdversary F params I hI ht adversary n
          (d, F.encode d (s • F.generator d)))).bind fun guess =>
            PMF.pure (decide ((ofBits guess : ZMod (F.order d)) = s))) := by
      unfold feldmanToDLAdversary
      dsimp only
      simp only [ProbComp.eval_bind, PMF.bind_bind]
      congr 1 with v : 1
      dsimp only [cont]
      congr 2
      congr 1
      refine Prod.ext rfl (Prod.ext (funext fun j => ?_) (funext fun i => ?_))
      · exact (feldmanSimCommitWords_encode F d params (hthresh d) J hJt eJ
          (s • F.generator d) v j).symm
      · simp [ZMod.val_natCast, eJ]
    change CloseTo _
      ((ProbComp.eval
        (feldmanToDLAdversary F params I hI ht adversary n
          (d, F.encode d (s • F.generator d)))).bind
        fun guess => PMF.pure (decide ((ofBits guess : ZMod (F.order d)) = s))) _
    rw [← hrhs]
    exact hc
  have hmem := hclose {true}
  rw [← hreal_eq, PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_apply_singleton] at hmem
  rw [← ENNReal.coe_le_coe, ENNReal.coe_add, Game.succProbability,
    ENNReal.coe_toNNReal ((feldmanSecrecyGame _ _ _ _ _ _ _).apply_ne_top true),
    Game.succProbability, ENNReal.coe_toNNReal ((F.discreteLogGame _ _ _).apply_ne_top true),
    ENNReal.coe_div (pow_ne_zero _ two_ne_zero), ENNReal.coe_natCast, ENNReal.coe_pow,
    ENNReal.coe_ofNat]
  exact hmem

/-- **Uniform-secret Feldman secrecy from `DiscreteLog`**: if `F.DiscreteLog setup` holds, then
every uniform strict PPT adversary has negligible success probability in `feldmanSecrecyGame`. -/
theorem discreteLog_implies_feldmanSecrecy
    (setup : ℕ → PMF F.Desc) {t : ℕ}
    (params : ∀ d : F.Desc, Shamir.Params (ZMod (F.order d)) Party)
    (hthresh : ∀ d, (params d).threshold = t)
    (hpoint : ∀ i : Party,
      ComputableInPolyTime (fun d => ((params d).point i).val) F.encDesc encNat)
    (I : Finset Party) (hI : I.card ≤ t) (ht : t < Fintype.card Party)
    (hDL : F.DiscreteLog setup)
    (adversary : ℕ → F.Desc × (Fin (t + 1) → List Bool) × (I → ℕ) → ProbComp (List Bool))
    (hadv : IsPPTOn (encFeldmanInput F t I) encBits (fun p => adversary p.1 p.2)) :
    Negligible fun n =>
      Game.succProbability (feldmanSecrecyGame F setup params hthresh I adversary n) := by
  have hdl := hDL (feldmanToDLAdversary F params I hI ht adversary)
    (isPPTOn_feldmanToDLAdversary F params hpoint I hI ht adversary hadv)
  have herr : Negligible (fun n => (t : ℝ≥0) / 2 ^ n) := by
    simpa only [div_eq_mul_inv, inv_pow] using
      (negligible_geometric (ratio := 2⁻¹) (by norm_num)).polynomiallyBounded_mul
        (PolynomiallyBounded.const t)
  exact negligible_of_le (hdl.add herr)
    (fun n => succProbability_feldmanSecrecyGame_le_discreteLogGame F setup params hthresh I hI ht
      adversary n)

/-- Dot-notation alias on `F.DiscreteLog setup` for uniform-secret Feldman secrecy. -/
theorem _root_.Cslib.Crypto.PrimeOrderGroupFamily.DiscreteLog.feldmanSecrecy
    {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (hDL : F.DiscreteLog setup) {Party : Type} [Fintype Party] [DecidableEq Party] {t : ℕ}
    (params : ∀ d : F.Desc, Shamir.Params (ZMod (F.order d)) Party)
    (hthresh : ∀ d, (params d).threshold = t)
    (hpoint : ∀ i : Party,
      ComputableInPolyTime (fun d => ((params d).point i).val) F.encDesc encNat)
    (I : Finset Party) (hI : I.card ≤ t) (ht : t < Fintype.card Party)
    (adversary : ℕ → F.Desc × (Fin (t + 1) → List Bool) × (I → ℕ) → ProbComp (List Bool))
    (hadv : IsPPTOn (encFeldmanInput F t I) encBits (fun p => adversary p.1 p.2)) :
    Negligible fun n =>
      Game.succProbability (feldmanSecrecyGame F setup params hthresh I adversary n) :=
  discreteLog_implies_feldmanSecrecy F setup params hthresh hpoint I hI ht hDL adversary hadv

end Secrecy

section ChosenSecretAttack

variable (F : PrimeOrderGroupFamily) {Party : Type} [Fintype Party]

/-- Chosen-secret distinguishing experiment for Feldman VSS: reveals commitment `C` and coalition
`I`'s shares for `secret = if b then s₁ d else s₀ d` and runs a Boolean distinguisher. -/
noncomputable def feldmanChosenSecretGame (setup : ℕ → PMF F.Desc) {t : ℕ}
    (params : ∀ d : F.Desc, Shamir.Params (ZMod (F.order d)) Party)
    (hthresh : ∀ d, (params d).threshold = t) (I : Finset Party)
    (distinguisher : ℕ → F.Desc × (Fin (t + 1) → List Bool) × (I → ℕ) → ProbComp Bool)
    (s₀ s₁ : ∀ d, ZMod (F.order d)) (b : Bool) (n : ℕ) : Game := do
  let d ← setup n
  let r ← PMF.uniformOfFintype (Shamir.Randomness (params d))
  let s := if b then s₁ d else s₀ d
  let C : Fin (t + 1) → List Bool := fun j =>
    F.encode d (feldmanCommit F d (params d) s r ⟨j.1, by rw [hthresh d]; exact j.2⟩)
  let σ : I → ℕ := fun i => (Shamir.share (params d) r s i.1).val
  ProbComp.eval (distinguisher n (d, C, σ))

/-- Explicit chosen-secret distinguisher against Feldman VSS: tests `C 0 == encode (1 • g)` to
distinguish secret `1` from secret `0` directly from the constant-term commitment `C 0`. -/
@[expose] def feldmanChosenSecretDistinguisher {t : ℕ} {I : Finset Party}
    (_n : ℕ) (input : F.Desc × (Fin (t + 1) → List Bool) × (I → ℕ)) : ProbComp Bool :=
  let (d, C, _) := input
  pure (decide (C 0 = F.smul (d, 1, F.encode d (F.generator d))))

omit [Fintype Party] in
/-- `feldmanChosenSecretDistinguisher` runs in uniform strict PPT. -/
theorem isPPTOn_feldmanChosenSecretDistinguisher {t : ℕ} {I : Finset Party} :
    IsPPTOn (encFeldmanInput F t I) encBool
      (fun p => feldmanChosenSecretDistinguisher F (t := t) (I := I) p.1 p.2) := by
  let encIn := encPair encUnary
    (encPair F.encDesc (encPair (encPi (Index := Fin (t + 1)) encBits) (encPi (Index := I) encNat)))
  have hdet : ComputableInPolyTime
      (fun p : ℕ × F.Desc × (Fin (t + 1) → List Bool) × (I → ℕ) =>
        decide (p.2.2.1 0 = F.smul (p.2.1, 1, F.encode p.2.1 (F.generator p.2.1))))
      encIn encBool := by
    have hd : ComputableInPolyTime
        (fun p : ℕ × F.Desc × (Fin (t + 1) → List Bool) × (I → ℕ) => p.2.1)
        encIn F.encDesc := by fun_prop
    have hC : ComputableInPolyTime
        (fun p : ℕ × F.Desc × (Fin (t + 1) → List Bool) × (I → ℕ) => p.2.2.1)
        encIn (encPi encBits) := by fun_prop
    have hC0 : ComputableInPolyTime
        (fun p : ℕ × F.Desc × (Fin (t + 1) → List Bool) × (I → ℕ) => p.2.2.1 0)
        encIn encBits :=
      ((ComputableTidilyInPolyTime.pi_apply encBits 0).computableInPolyTime).comp hC
    have hg := F.computableInPolyTime_generator.comp hd
    have h1 : ComputableInPolyTime
        (fun _ : ℕ × F.Desc × (Fin (t + 1) → List Bool) × (I → ℕ) => (1 : ℕ))
        encIn encNat := ComputableInPolyTime.const 1
    have h1g := F.computableInPolyTime_smul.comp (hd.prod (h1.prod hg))
    fun_prop
  exact hdet.isPPTOn

/-- **Chosen-secret indistinguishability failure**: because `C 0 = secret • g` is published in the
clear, `feldmanChosenSecretDistinguisher` distinguishes `secret = 0` from `secret = 1` with exact
advantage `1` at every security parameter `n`. -/
theorem advantage_feldmanChosenSecretDistinguisher_eq_one
    (setup : ℕ → PMF F.Desc) {t : ℕ}
    (params : ∀ d : F.Desc, Shamir.Params (ZMod (F.order d)) Party)
    (hthresh : ∀ d, (params d).threshold = t) (I : Finset Party) (n : ℕ) :
    Game.advantage
      (feldmanChosenSecretGame F setup params hthresh I
        (feldmanChosenSecretDistinguisher F) (fun _ => 0) (fun _ => 1) false n)
      (feldmanChosenSecretGame F setup params hthresh I
        (feldmanChosenSecretDistinguisher F) (fun _ => 0) (fun _ => 1) true n) = 1 := by
  have hf :
      feldmanChosenSecretGame F setup params hthresh I
        (feldmanChosenSecretDistinguisher F) (fun _ => 0) (fun _ => 1) false n =
      PMF.pure false := by
    unfold feldmanChosenSecretGame feldmanChosenSecretDistinguisher
    have hconst : ∀ d : F.Desc,
        decide (F.encode d (0 : F.Carrier d) =
          F.smul (d, 1, F.encode d (F.generator d))) = false := by
      intro d
      rw [decide_eq_false_iff_not]
      intro heq
      have h0 := congrArg (F.encode d) (zero_smul (ZMod (F.order d)) (F.generator d))
      rw [F.smul_encode, Nat.cast_one] at heq
      have h01 := F.smul_generator_injective d (a₁ := 0) (a₂ := 1)
        (F.encode_injective d (h0.trans heq))
      have : Fact (1 < F.order d) := ⟨(F.prime_order d).one_lt⟩
      exact zero_ne_one h01
    simp [Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure, hconst, PMF.bind_const]
  have ht :
      feldmanChosenSecretGame F setup params hthresh I
        (feldmanChosenSecretDistinguisher F) (fun _ => 0) (fun _ => 1) true n =
      PMF.pure true := by
    unfold feldmanChosenSecretGame feldmanChosenSecretDistinguisher
    have hconst : ∀ d : F.Desc,
        decide (F.encode d (F.generator d) =
          F.smul (d, 1, F.encode d (F.generator d))) = true := by
      intro d
      have h1 := congrArg (F.encode d) (one_smul (ZMod (F.order d)) (F.generator d))
      rw [F.smul_encode, Nat.cast_one, decide_eq_true_iff]
      exact h1.symm
    simp [↓reduceIte, ProbComp.eval_pure, hconst, PMF.bind_const]
  rw [hf, ht, Game.advantage]
  simp [Game.succProbability]

end ChosenSecretAttack

end Cslib.Crypto.Protocols.SecretSharing.Feldman
