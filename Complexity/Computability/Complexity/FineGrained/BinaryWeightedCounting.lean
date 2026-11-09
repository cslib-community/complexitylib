/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.BinaryWeights
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.CSPBinaryWeights
public import Complexity.Computability.Complexity.FineGrained.ContractionPartitionFunction
import Complexity.Logics.Propositional.CSP.Vars
import Mathlib.Data.Fintype.BigOperators

/-!
# Native weighted counting with polynomially many weight bits

For fixed arity and polynomial bit-budget parameters, one native machine computes the partition
function of a Boolean CSP with input-dependent natural weights. The reduction constructs its
existing constraint network and applies exact binary-weight tensor contraction. The weight
magnitudes have no constant bound: only the total encoded length of the network's tables must
be polynomial in the number of occurrences.

The counter checks the arity, excludes empty scopes, and checks this bit budget before invoking
contraction. It returns one on the empty instance and zero on other rejected inputs. Thus its
resource certificate holds on every encoded input. On the promised inputs the answer is the
partition function, in polynomial space and time
`poly(L) * 2 ^ O(N / √log(N + 2))`, where `N` counts occurrences, `n` counts variables, and `L`
is the complete encoded input length. Bounded occurrence gives the corresponding variable bound.

## Main definitions

* `BinaryWeightedCounting.guard`: the scope and polynomial table-bit checks.
* `BinaryWeightedCounting.count`: the total counting function.
* `BinaryWeightedCounting.certificate`: its ordinary native machine certificate.

## Main results

* `BinaryWeightedCounting.count_eq`: correctness on the promised inputs.
* `BinaryWeightedCounting.exists_partitionFunctionCounter`: the uniform occurrence bound.
* `BinaryWeightedCounting.exists_partitionFunctionCounter_boundedDegree`: the variable bound.
* `BinaryWeightedCounting.exists_partitionFunctionCounter_of_weightBits`: the same counter under
  a polynomial bit-length bound on each relevant local weight, with the network budget derived.
-/

public section

namespace Cslib.Complexity.BinaryWeightedCounting

open Cslib.Logic.PL Cslib.Circuits.Frontier Cslib.Circuits.Frontier.ClauseNetwork
  Turing.MultiTapeTM Cslib.GenericRAM ComputableInPolyTime

variable {Rel : Type}

/-- The existing scope check together with the polynomial bound on all table bits. -/
@[expose] def guard (k D d : ℕ) (wt : Rel → List Bool → ℕ) (F : CSP Rel ℕ) : Bool :=
  ContractionPartitionFunction.guard k F &&
    decide ((cspNetwork k wt F).2.binaryTableBound ≤
      D * ((cspNetwork k wt F).2.numEdges + 1) ^ d)

/-- Exact contraction on the guarded instances, with one on the empty instance and zero on
other rejected instances. -/
@[expose] def count (k D d : ℕ) (wt : Rel → List Bool → ℕ) (F : CSP Rel ℕ) : ℕ :=
  if guard k D d wt F then (cspNetwork k wt F).2.contraction
  else ContractionPartitionFunction.fallback F

theorem guard_eq_true_iff {k D d : ℕ} {wt : Rel → List Bool → ℕ} {F : CSP Rel ℕ} :
    guard k D d wt F = true ↔ F ≠ [] ∧
      (∀ c ∈ F, 1 ≤ c.2.length ∧ c.2.length ≤ k) ∧
      (cspNetwork k wt F).2.binaryTableBound ≤
        D * ((cspNetwork k wt F).2.numEdges + 1) ^ d := by
  simp only [guard, Bool.and_eq_true, decide_eq_true_eq,
    ContractionPartitionFunction.guard_eq_true_iff, and_assoc]

/-- The empty input always has answer one, independently of the bit budget. -/
@[simp] theorem count_nil (k D d : ℕ) (wt : Rel → List Bool → ℕ) :
    count k D d wt [] = 1 := by
  simp [count, guard, ContractionPartitionFunction.guard, ContractionPartitionFunction.fallback]

/-- The counter computes the partition function whenever its arity and bit-budget promises hold. -/
theorem count_eq {k D d : ℕ} {wt : Rel → List Bool → ℕ} {F : CSP Rel ℕ}
    (hk : ∀ c ∈ F, 1 ≤ c.2.length ∧ c.2.length ≤ k)
    (hB : (cspNetwork k wt F).2.binaryTableBound ≤
      D * ((cspNetwork k wt F).2.numEdges + 1) ^ d) :
    count k D d wt F = F.partitionFunction wt := by
  by_cases hF : F = []
  · subst F
    rw [count_nil, CSP.partitionFunction]
    change 1 = ∑ _ : (CSP.vars ([] : CSP Rel ℕ)).toFinset → Bool, (1 : ℕ)
    rw [Finset.sum_const, Finset.card_univ]
    have hc : Fintype.card ((CSP.vars ([] : CSP Rel ℕ)).toFinset → Bool) = 1 := by
      rw [Fintype.card_fun, Fintype.card_coe]
      simp [CSP.vars]
    rw [hc, one_nsmul]
  · rw [count, ite_eq_left (guard_eq_true_iff.mpr ⟨hF, hk, hB⟩),
      contraction_cspNetwork (fun c hc => (hk c hc).2)]

variable (encRel : Rel ↪ List Bool) (k D d : ℕ) (wt : Rel → List Bool → ℕ)
  (hwt : ∀ w : List Bool, w.length ≤ k →
    ComputableInPolyTime (fun R : Rel => wt R w) encRel encNat)

include hwt

/-- The scope and bit-budget checks are polynomial-time for the fixed parameters. -/
theorem guard_polyTime :
    ComputableInPolyTime (guard k D d wt) (encCSP encRel encNat) encBool := by
  have hnet := computableInPolyTime_cspNetwork encRel k wt hwt
  have hG := hnet.snd'
  have hB := ExplicitTensorNetwork.binaryTableBound_polyTime.comp hG
  have hM := DescribedNetwork.numEdges_polyTime.comp hG
  have hbudget := unary_mul' (const D)
    ((unary_pow d).comp (unary_add' hM (const 1)))
  exact bool_and.comp ((ContractionPartitionFunction.computableInPolyTime_guard encRel k).prod
    (binary_le' (unary_to_binary.comp hB) (unary_to_binary.comp hbudget)))

/-- Native construction of the constraint network followed by exact binary-weight contraction. -/
noncomputable def coreCertificate :
    NativeCertificate (fun F : CSP Rel ℕ => (cspNetwork k wt F).2.contraction)
      (encCSP encRel encNat) encNat :=
  (BinaryWeights.certificate (max k 4)).comp
    (NativeCertificate.ofPolyTime (computableInPolyTime_cspNetwork encRel k wt hwt))

/-- The guarded native counter. Both the guard and the rejected-input answer have polynomial
time certificates in the original input encoding. -/
noncomputable def certificate :
    NativeCertificate (count k D d wt) (encCSP encRel encNat) encNat :=
  (NativeCertificate.branch (NativeCertificate.ofPolyTime (guard_polyTime encRel k D d wt hwt))
    (coreCertificate encRel k wt hwt)
    (NativeCertificate.ofPolyTime
      (ContractionPartitionFunction.computableInPolyTime_fallback encRel))).congr fun _ => rfl

private theorem coreCertificate_bound :
    ∃ A H : ℕ, ∀ F : CSP Rel ℕ, guard k D d wt F = true →
      (coreCertificate encRel k wt hwt).time F ≤
          H * ((encCSP encRel encNat F).length + 1) ^ H *
            2 ^ (A * (F.vars.length + 1) / Nat.sqrt (Nat.log 2 (F.vars.length + 2))) ∧
        (coreCertificate encRel k wt hwt).space F ≤
          H * ((encCSP encRel encNat F).length + 1) ^ H := by
  obtain ⟨K, hK⟩ := BinaryWeights.certificate_bound (max k 4) 1 D d
  have hnet := computableInPolyTime_cspNetwork encRel k wt hwt
  obtain ⟨H, hH⟩ := NativeCertificate.exists_polynomial_overhead
    (BinaryWeights.certificate (max k 4)) hnet (id' (encIn := encNat)) K
  refine ⟨3 * K, H, fun F hg => ?_⟩
  obtain ⟨hne, hcl, hB⟩ := guard_eq_true_iff.mp hg
  have hm := CSP.length_le_length_vars fun c hc => (hcl c hc).1
  have h1 : 1 ≤ F.length := List.length_pos_iff.mpr hne
  have hN : 1 ≤ F.vars.length := h1.trans hm
  have hs : 2 ≤ (cspNetwork k wt F).2.numEdges := by rw [numEdges_cspNetwork]; omega
  have hv : (cspNetwork k wt F).2.vertices.length ≤ 1 * (cspNetwork k wt F).2.numEdges := by
    rw [length_vertices_cspNetwork, numEdges_cspNetwork]
    omega
  obtain ⟨ht, hspace⟩ := hK (cspNetwork k wt F).1 (cspNetwork k wt F).2 hs
    (isRowsFirstBipartite_cspNetwork k wt F) hv
    (maxDegree_cspNetwork_le fun c hc => (hcl c hc).2) hB
  have hexp := ContractionCounting.exponent_le_occurrences (K := K) hN
  rw [numEdges_cspNetwork] at ht
  have htime := ht.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hexp))
  obtain ⟨hT, hS⟩ := hH F
    (2 ^ (3 * K * (F.vars.length + 1) / Nat.sqrt (Nat.log 2 (F.vars.length + 2))))
    Nat.one_le_two_pow htime hspace
  exact ⟨(Nat.le_add_right _ _).trans hT, (Nat.le_add_right _ _).trans hS⟩

/-- One fixed occurrence exponent and polynomial bound control the total guarded machine,
including inputs rejected by either check. -/
theorem certificate_bound :
    ∃ A C e : ℕ, ∀ F : CSP Rel ℕ,
      (certificate encRel k D d wt hwt).time F ≤
          C * ((encCSP encRel encNat F).length + 1) ^ e *
            2 ^ (A * (F.vars.length + 1) / Nat.sqrt (Nat.log 2 (F.vars.length + 2))) ∧
        (certificate encRel k D d wt hwt).space F ≤
          C * ((encCSP encRel encNat F).length + 1) ^ e := by
  obtain ⟨A, H, hcore⟩ := coreCertificate_bound encRel k D d wt hwt
  obtain ⟨p, hp, -, hguard⟩ := exists_mono_poly_cert (guard_polyTime encRel k D d wt hwt)
  obtain ⟨q, hq, -, hfallback⟩ := exists_mono_poly_cert
    (ContractionPartitionFunction.computableInPolyTime_fallback encRel)
  let Q : ℕ → ℕ := fun n => p n + q n + H * (n + 1) ^ H
  have hQ : PolyBounded id Q :=
    ((PolyBounded.of_polynomiallyBounded id hp).add
      (PolyBounded.of_polynomiallyBounded id hq)).add
      ((PolyBounded.const H).mul ((PolyBounded.self.add (PolyBounded.const 1)).pow H))
  obtain ⟨C, e, hCe⟩ := hQ.exists_le
  refine ⟨A, C, e, fun F => ?_⟩
  let n := (encCSP encRel encNat F).length
  let X := 2 ^ (A * (F.vars.length + 1) / Nat.sqrt (Nat.log 2 (F.vars.length + 2)))
  have hX : 1 ≤ X := Nat.one_le_two_pow
  have hpX : p n ≤ p n * X := Nat.le_mul_of_pos_right _ hX
  have hqX : q n ≤ q n * X := Nat.le_mul_of_pos_right _ hX
  have htime : (certificate encRel k D d wt hwt).time F ≤ Q n * X := by
    change (NativeCertificate.ofPolyTime (guard_polyTime encRel k D d wt hwt)).time F +
      (if guard k D d wt F then (coreCertificate encRel k wt hwt).time F else
        (NativeCertificate.ofPolyTime
          (ContractionPartitionFunction.computableInPolyTime_fallback encRel)).time F) ≤ _
    split
    · next hg =>
      have hc := (hcore F hg).1
      calc _ ≤ p n * X + (H * (n + 1) ^ H) * X :=
          Nat.add_le_add ((hguard F).1.trans hpX) hc
        _ = (p n + H * (n + 1) ^ H) * X := by ring
        _ ≤ Q n * X := Nat.mul_le_mul_right _ (by dsimp only [Q]; omega)
    · calc _ ≤ p n * X + q n * X :=
          Nat.add_le_add ((hguard F).1.trans hpX) ((hfallback F).1.trans hqX)
        _ = (p n + q n) * X := by ring
        _ ≤ Q n * X := Nat.mul_le_mul_right _ (by dsimp only [Q]; omega)
  have hspace : (certificate encRel k D d wt hwt).space F ≤ Q n := by
    change (NativeCertificate.ofPolyTime (guard_polyTime encRel k D d wt hwt)).space F +
      (if guard k D d wt F then (coreCertificate encRel k wt hwt).space F else
        (NativeCertificate.ofPolyTime
          (ContractionPartitionFunction.computableInPolyTime_fallback encRel)).space F) ≤ _
    split
    · next hg =>
      calc _ ≤ p n + H * (n + 1) ^ H := Nat.add_le_add (hguard F).2 (hcore F hg).2
        _ ≤ Q n := by dsimp only [Q]; omega
    · calc _ ≤ p n + q n := Nat.add_le_add (hguard F).2 (hfallback F).2
        _ ≤ Q n := by dsimp only [Q]; omega
  exact ⟨htime.trans (Nat.mul_le_mul_right _ (hCe n)), hspace.trans (hCe n)⟩

/-- Exact natural weighted counting with a fixed polynomial table-bit budget. The relation
symbol, including its potentially large numeric weights, is part of the input encoding. -/
theorem exists_partitionFunctionCounter :
    ∃ (counter : CSP Rel ℕ → ℕ) (A e b : ℕ),
      (∀ F : CSP Rel ℕ, (∀ c ∈ F, 1 ≤ c.2.length ∧ c.2.length ≤ k) →
        (cspNetwork k wt F).2.binaryTableBound ≤
          D * ((cspNetwork k wt F).2.numEdges + 1) ^ d →
        counter F = F.partitionFunction wt) ∧
      ComputableInO counter (encCSP encRel encNat) encNat
        (fun F => 2 ^ (A * (F.vars.length + 1) / Nat.sqrt (Nat.log 2 (F.vars.length + 2))) *
          ((encCSP encRel encNat F).length + 1) ^ e)
        (fun F => ((encCSP encRel encNat F).length + 1) ^ b) := by
  obtain ⟨A, C, e, h⟩ := certificate_bound encRel k D d wt hwt
  refine ⟨count k D d wt, A, e, e, fun F hk hB => count_eq hk hB,
    (certificate encRel k D d wt hwt).computes.mono C (fun F => ?_) (fun F => ?_)⟩
  · have hT := (h F).1
    calc _ ≤ C * (2 ^ (A * (F.vars.length + 1) / Nat.sqrt (Nat.log 2 (F.vars.length + 2))) *
        ((encCSP encRel encNat F).length + 1) ^ e) := by
          simpa only [mul_assoc, mul_comm, mul_left_comm] using hT
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_succ _)
  · exact (h F).2.trans (Nat.mul_le_mul_left _ (Nat.le_succ _))

/-- Bounded variable occurrence converts the occurrence numerator to a variable numerator.
The machine and polynomial exponents are selected before the occurrence bound. -/
theorem exists_partitionFunctionCounter_boundedDegree :
    ∃ (counter : CSP Rel ℕ → ℕ) (T S : CSP Rel ℕ → ℕ) (e b : ℕ),
      (∀ F : CSP Rel ℕ, (∀ c ∈ F, 1 ≤ c.2.length ∧ c.2.length ≤ k) →
        (cspNetwork k wt F).2.binaryTableBound ≤
          D * ((cspNetwork k wt F).2.numEdges + 1) ^ d →
        counter F = F.partitionFunction wt) ∧
      ComputableInO counter (encCSP encRel encNat) encNat T S ∧
      (∀ F, S F = ((encCSP encRel encNat F).length + 1) ^ b) ∧
      ∀ Δ : ℕ, ∃ A : ℕ, ∀ F : CSP Rel ℕ, (∀ v, F.vars.count v ≤ Δ) →
        T F ≤ 2 ^ (A * (F.numVars + 1) / Nat.sqrt (Nat.log 2 (F.numVars + 2))) *
          ((encCSP encRel encNat F).length + 1) ^ e := by
  obtain ⟨counter, A, e, b, hcorrect, hc⟩ :=
    exists_partitionFunctionCounter encRel k D d wt hwt
  refine ⟨counter, _, _, e, b, hcorrect, hc, fun _ => rfl,
    fun Δ => ⟨A * (Δ + 1), fun F hF => ?_⟩⟩
  have hn : F.numVars ≤ F.vars.length := List.toFinset_card_le _
  refine Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide)
    (Nat.div_le_div ?_ (Nat.sqrt_le_sqrt (Nat.log_mono_right (by omega))) ?_))
  · have h := CSP.length_vars_le_mul_numVars hF
    have hN : F.vars.length + 1 ≤ (Δ + 1) * (F.numVars + 1) := by nlinarith
    calc A * (F.vars.length + 1) ≤ A * ((Δ + 1) * (F.numVars + 1)) := Nat.mul_le_mul_left _ hN
      _ = A * (Δ + 1) * (F.numVars + 1) := by ring
  · exact Nat.sqrt_eq_zero.not.mpr (Nat.log_pos (by decide) (by omega)).ne'

/-- Polynomially many bits per local weight suffice: the total network bit budget follows with
the explicit coefficient `3 * 2 ^ (max k 4) + 1` and exponent `d + 1`. The natural weight
magnitudes may be exponential in `(N + 1) ^ d`. -/
theorem exists_partitionFunctionCounter_of_weightBits :
    ∃ (counter : CSP Rel ℕ → ℕ) (A e b : ℕ),
      (∀ F : CSP Rel ℕ, (∀ c ∈ F, 1 ≤ c.2.length ∧ c.2.length ≤ k) →
        (∀ c ∈ F, ∀ w : List Bool, w.length = c.2.length →
          (wt c.1 w).size ≤ (F.vars.length + 1) ^ d) →
        counter F = F.partitionFunction wt) ∧
      ComputableInO counter (encCSP encRel encNat) encNat
        (fun F => 2 ^ (A * (F.vars.length + 1) / Nat.sqrt (Nat.log 2 (F.vars.length + 2))) *
          ((encCSP encRel encNat F).length + 1) ^ e)
        (fun F => ((encCSP encRel encNat F).length + 1) ^ b) := by
  obtain ⟨counter, A, e, b, hcorrect, hc⟩ := exists_partitionFunctionCounter encRel k
    (3 * 2 ^ (max k 4) + 1) (d + 1) wt hwt
  exact ⟨counter, A, e, b, fun F hk hw =>
    hcorrect F hk (binaryTableBound_cspNetwork_le d hk hw), hc⟩

/-- The polynomial-bit counter has the variable bound on bounded-occurrence inputs. Its machine
and polynomial exponents are independent of the occurrence bound `Δ`. -/
theorem exists_partitionFunctionCounter_boundedDegree_of_weightBits :
    ∃ (counter : CSP Rel ℕ → ℕ) (T S : CSP Rel ℕ → ℕ) (e b : ℕ),
      (∀ F : CSP Rel ℕ, (∀ c ∈ F, 1 ≤ c.2.length ∧ c.2.length ≤ k) →
        (∀ c ∈ F, ∀ w : List Bool, w.length = c.2.length →
          (wt c.1 w).size ≤ (F.vars.length + 1) ^ d) →
        counter F = F.partitionFunction wt) ∧
      ComputableInO counter (encCSP encRel encNat) encNat T S ∧
      (∀ F, S F = ((encCSP encRel encNat F).length + 1) ^ b) ∧
      ∀ Δ : ℕ, ∃ A : ℕ, ∀ F : CSP Rel ℕ, (∀ v, F.vars.count v ≤ Δ) →
        T F ≤ 2 ^ (A * (F.numVars + 1) / Nat.sqrt (Nat.log 2 (F.numVars + 2))) *
          ((encCSP encRel encNat F).length + 1) ^ e := by
  obtain ⟨counter, T, S, e, b, hcorrect, hc, hS, hT⟩ :=
    exists_partitionFunctionCounter_boundedDegree encRel k (3 * 2 ^ (max k 4) + 1) (d + 1) wt hwt
  exact ⟨counter, T, S, e, b, fun F hk hw =>
    hcorrect F hk (binaryTableBound_cspNetwork_le d hk hw), hc, hS, hT⟩

end Cslib.Complexity.BinaryWeightedCounting
