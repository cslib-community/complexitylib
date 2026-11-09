/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceNetworkPolyTime
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceEntryBounds
public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.TruncatedSum
public import CslibFrontier.Foundations.Data.Nat.CeilQuarterSqrt
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends

/-!
# Native streaming contraction over the actual degree arrays

Construct one network at a time from the input system and a binary array index. All degree caps,
group counts, precisions and arrays are computed. The proved native truncated contraction sums
their residues with polynomial workspace, at the per-network sharp scale of [OpenAI2026ETH],
Lemma D.2, PDF pp. 55–57. Exact reconstruction of the sparse-system count from this contraction
sum, and the complete general-density counter, remain separate obligations.

## Main definitions

* `Cslib.Circuits.Frontier.IncidenceNetwork.buildArray`: compute one network from input and index.
* `Cslib.Circuits.Frontier.IncidenceNetwork.sumArrays`: modular sum of all actual contractions.

## Main results

* `Cslib.Circuits.Frontier.IncidenceNetwork.buildArray_polytime`: binary network writer from the
  original sparse system and binary array index, without supplied network parameters.
* `Cslib.Circuits.Frontier.IncidenceNetwork.exists_sumArrays_certificate`: native streamed sum,
  with actual array count times the sharp contraction bound and polynomial original-input space.
* `Cslib.Circuits.Frontier.IncidenceNetwork.degreeCount_le`: explicit array traversal overhead.

## References

* [OpenAI2026ETH], Appendix D.3, Lemma D.2, PDF pp. 55–57.
* [ChenJiangZhu2027], Lemma 3.2 (p. 11) and Proposition 4.2 (p. 14).
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open Cslib.Complexity Cslib.GenericRAM Turing.MultiTapeTM ComputableInPolyTime
open CountingSimulation

/-- Original declared size and the actual sparse polynomial equations. -/
abbrev ArrayInput := ℕ × List (List (List ℕ))

/-- Unary declared size and binary monomial variable indices. -/
@[expose] def encArrayInput : ArrayInput ↪ List Bool :=
  encPair encUnary (encList (encList (encList encNat)))

/-- The source degree cap `k(a+2n)`, computed from the equation list. -/
@[expose] def degreeCap (k : ℕ) (p : ArrayInput) : ℕ := k * (p.2.length + 2 * p.1)

/-- Number of actual array indices visited, in binary. -/
@[expose] def degreeCount (k : ℕ) (p : ArrayInput) : ℕ :=
  arrayCount (degreeCap k p) (Nat.ceilQuarter p.1)

/-- Compute the network at one array index, with precision and truncation order `n+1`. -/
@[expose] def buildArray (k : ℕ) (q : ArrayInput × ℕ) :
    ℕ × ℕ × ℕ × DescribedNetwork Desc :=
  let p := q.1
  let d := arrayAt (degreeCap k p) (Nat.ceilQuarter p.1) q.2
  (p.1 + 1, p.1 + 1, lemmaNetwork (degreeCap k p) p.1 p.2 d)

/-- The actual quarter-root grouping is computed in binary polynomial time, with unary output. -/
@[fun_prop] theorem ceilQuarter_polytime :
    ComputableInPolyTime Nat.ceilQuarter encUnary encUnary := by
  have hsq : ComputableInPolyTime Nat.sqrt encUnary encUnary :=
    binary_to_unary_bounded (binary_sqrt.comp unary_to_binary) id' Nat.sqrt_le_self
  have hprev : ComputableInPolyTime (fun n : ℕ => n - 1) encUnary encUnary := by fun_prop
  have hroot := hsq.comp (hsq.comp hprev)
  have hanswer : ComputableInPolyTime (fun n : ℕ => (n - 1).sqrt.sqrt + 1)
      encUnary encUnary := by fun_prop
  have htest : ComputableInPolyTime (fun n : ℕ => decide (n = 0)) encUnary encBool := by fun_prop
  exact (htest.ite' (const 0) hanswer).of_enc_eq fun n => by
    simp only [Nat.ceilQuarter_eq_sqrt, decide_eq_true_eq]

@[fun_prop] theorem degreeCap_polytime (k : ℕ) :
    ComputableInPolyTime (degreeCap k) encArrayInput encUnary := by
  unfold degreeCap encArrayInput
  fun_prop

@[fun_prop] theorem degreeCount_polytime (k : ℕ) :
    ComputableInPolyTime (degreeCount k) encArrayInput encNat :=
  arrayCount_polytime.comp ((degreeCap_polytime k).prod
    (ceilQuarter_polytime.comp (fst _ _)))

private theorem sizeParam_polytime : ComputableInPolyTime sizeParam encUnary encUnary := by
  have hclog := binary_clog_two.comp unary_to_binary
  exact unary_mul' id' (hclog.comp hclog)

/-- One complete actual network, including its decoded array and every output write, is
polynomial-time in the original encoded input and binary index. -/
@[fun_prop] theorem buildArray_polytime (k : ℕ) :
    ComputableInPolyTime (buildArray k) (encPair encArrayInput encNat) (encTrunc encDesc) := by
  have hp := fst encArrayInput encNat
  have hn := (fst encUnary (encList (encList (encList encNat)))).comp hp
  have hsys := (snd encUnary (encList (encList (encList encNat)))).comp hp
  have hK := (degreeCap_polytime k).comp hp
  have hJ := ceilQuarter_polytime.comp hn
  have hd := arrayAt_polytime.comp ((hK.prod hJ).prod (snd encArrayInput encNat))
  have hP : ComputableInPolyTime (fun q : ArrayInput × ℕ => q.1.1 + 1)
      (encPair encArrayInput encNat) encUnary := by fun_prop
  exact hP.prod (hP.prod (network_polytime hP hP hJ hK (sizeParam_polytime.comp hn) hn hsys hd))

private theorem modulus_polytime :
    ComputableInPolyTime (fun p : ArrayInput => 2 ^ (p.1 + 1)) encArrayInput encNat :=
  (of_tidy ComputableTidilyInPolyTime.binary_pow).comp
    ((const 2).prod (show ComputableInPolyTime (fun p : ArrayInput => p.1 + 1)
      encArrayInput encUnary by fun_prop))

/-- Stream the actual decoded degree arrays and sum the native truncated contractions modulo
`2^(n+1)`. This is not yet asserted to equal the sparse-system solution count. -/
@[expose] noncomputable def sumArrays (k : ℕ) : ArrayInput → ℕ :=
  truncSum incEntry (buildArray k) (fun p => 2 ^ (p.1 + 1)) (degreeCount k)

/-- Exact semantics of the actual binary-index traversal: every fitting index occurs once. -/
theorem sumArrays_eq (k : ℕ) (p : ArrayInput) :
    sumArrays k p =
      (∑ i ∈ Finset.range (degreeCount k p), truncCoeffSum incEntry (buildArray k (p, i))) %
        2 ^ (p.1 + 1) := truncSum_eq p

private theorem exists_arrays_admissible (k c : ℕ) (hk : 1 ≤ k) :
    ∃ C n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (sys : List (List (List ℕ))),
    SubexponentialSAT.IncidenceBranching.IsSparseBranch k c n sys → ∀ i,
    let (P, ℓ, r, G) := buildArray k ((n, sys), i)
    1 ≤ P ∧ P ≤ 2 * sizeParam n ∧ 1 ≤ ℓ ∧ ℓ ≤ 2 * sizeParam n ∧
      TruncEntryAdmissible incCertificate C (sizeParam n) (r, G) := by
  let b := k * (c + 2) + c + 1
  obtain ⟨C, n₀, hC⟩ := exists_entry_admissible b
  refine ⟨C, n₀ + 5, fun n hn sys hs i => ?_⟩
  have hlam : 1 ≤ Nat.clog 2 n := Nat.clog_pos Nat.one_lt_two (by omega)
  have hnu : 1 ≤ Nat.clog 2 (Nat.clog 2 n) := by
    have h := Nat.clog_mono_right 2 (show 2 ^ 2 ≤ n by omega)
    simp only [Nat.clog_pow 2 2 Nat.one_lt_two] at h
    exact Nat.clog_pos Nat.one_lt_two (by omega)
  have hns : n ≤ sizeParam n := Nat.le_mul_of_pos_right _ hnu
  change 1 ≤ n + 1 ∧ n + 1 ≤ 2 * sizeParam n ∧ 1 ≤ n + 1 ∧
    n + 1 ≤ 2 * sizeParam n ∧ _
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  have hcb : c ≤ b := by dsimp only [b]; omega
  have hpow : Nat.clog 2 n ^ c ≤ Nat.clog 2 n ^ b := Nat.pow_le_pow_right hlam hcb
  apply hC n (by omega) (degreeCap k (n, sys)) sys _
  · exact hs.length_le.trans (Nat.mul_le_mul_right _ hcb)
  · change n ≤ k * (sys.length + 2 * n)
    exact (show n ≤ sys.length + 2 * n by omega).trans (Nat.le_mul_of_pos_left _ hk)
  · change k * (sys.length + 2 * n) ≤ b * n
    calc k * (sys.length + 2 * n) ≤ k * (c * n + 2 * n) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add_right hs.length_le _)
      _ = (k * (c + 2)) * n := by ring
      _ ≤ b * n := Nat.mul_le_mul_right _ (by dsimp only [b]; omega)
  · exact fun eq heq => (hs.scope_le eq heq).trans hpow
  · exact hs.vars_lt
  · exact fun v hv => (hs.varDegree_le v hv).trans hpow

/-- One native binary machine constructs, contracts and accumulates all actual degree arrays.
Admissibility, cap, group count and all resource bounds are derived from sparse-branch inputs.
Workspace is polynomial in the original encoded input, independently of the array count. -/
theorem exists_sumArrays_certificate (k c : ℕ) (hk : 1 ≤ k) :
    ∃ (cs : NativeCertificate (sumArrays k) encArrayInput encNat) (A n₀ : ℕ),
      ∀ n, n₀ ≤ n → ∀ (sys : List (List (List ℕ))),
      SubexponentialSAT.IncidenceBranching.IsSparseBranch k c n sys →
      let L := (encArrayInput (n, sys)).length
      cs.time (n, sys) ≤ (degreeCount k (n, sys) + 1) *
          (A * (L + 1) ^ A * 2 ^ (A * sizeParam n / Nat.sqrt (Nat.log 2 (sizeParam n)))) ∧
        cs.space (n, sys) ≤ A * (L + 1) ^ A := by
  obtain ⟨C, n₀, hC⟩ := exists_arrays_admissible k c hk
  obtain ⟨cs, A, hA⟩ := exists_truncSum_certificate
    (CountingSimulation.truncEntryContractionAlgorithm incCertificate)
    (buildArray_polytime k) modulus_polytime (degreeCount_polytime k) (fun _ => by positivity)
    C 2 (fun p : ArrayInput => sizeParam p.1)
  refine ⟨cs, A, n₀ + 5, fun n hn sys hs => hA (n, sys) ?_ (fun i _ => ?_)⟩
  · have hnu : 1 ≤ Nat.clog 2 (Nat.clog 2 n) := by
      apply Nat.clog_pos Nat.one_lt_two
      have h := Nat.clog_mono_right 2 (show 2 ^ 2 ≤ n by omega)
      simp only [Nat.clog_pow 2 2 Nat.one_lt_two] at h
      omega
    exact (show 2 ≤ n by omega).trans (Nat.le_mul_of_pos_right _ hnu)
  · exact hC n (by omega) sys hs i

/-- The source's array-enumeration overhead bounds the actual binary loop count. It is explicit
and separate from the per-network contraction exponent, rather than hidden in an oracle cost. -/
theorem degreeCount_le (k : ℕ) {c n : ℕ} {sys : List (List (List ℕ))}
    (hn : 1 ≤ n) (hs : sys.length ≤ c * n) :
    degreeCount k (n, sys) ≤
      2 ^ (4 * n.sqrt * (Nat.clog 2 (k * (c + 2) + 1) + Nat.clog 2 n)) := by
  apply arrayCount_quarter_le hn
  change k * (sys.length + 2 * n) ≤ (k * (c + 2)) * n
  calc _ ≤ k * (c * n + 2 * n) := Nat.mul_le_mul_left _ (Nat.add_le_add_right hs _)
    _ = _ := by ring

end Cslib.Circuits.Frontier.IncidenceNetwork
