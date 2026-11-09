/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.BinaryDigitsPolyTime
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.BinaryWeightBounds
public import Complexity.Computability.Complexity.Classes.CountingSimulation.TruncatedBoundedDegree
public import Complexity.Computability.GenericRAM.Native.PolynomialOverhead

/-!
# Exact native contraction of large natural weights

The binary-digit reduction, polynomial truncation, and logarithmic-linear precision give a
native exact contraction of natural-number tensor tables. The certificate is correct on every
network. On rows-first networks of fixed degree, with linearly many vertices and a polynomial
total table bit length, it uses time `poly(L) 2 ^ O(s / √⌊log₂ s⌋)` and polynomial space, where
`s` is the number of edges and `L` the complete encoded input length.

The input bound is on the binary lengths of weights; the weights' numeric magnitudes may be
exponential in a fixed power of `s`. All constants and polynomial exponents are selected before
the network. Polynomial preprocessing and Horner decoding preserve the exponential rate because
the contraction's space bound charges its encoded output.

## Main definitions

* `BinaryWeights.input`: derived precision, truncation order, and original table network.
* `BinaryWeights.certificate`: the native exact natural contraction.

## Main results

* `BinaryWeights.certificate_bound`: the subexponential time and polynomial space bound.
-/

public section

namespace Cslib.Circuits.Frontier.BinaryWeights

open Cslib.GenericRAM Turing.MultiTapeTM Cslib.Complexity.CountingSimulation
open ExplicitTensorNetwork

/-- The native input encoding: a binary row count and the existing explicit natural network. -/
abbrev encInput : ℕ × ExplicitTensorNetwork ℕ ↪ List Bool :=
  encPair encNat ExplicitTensorNetwork.encExplicitNetwork

/-- Derived precision and truncation order from the table bit bound. -/
@[expose] def input (x : ℕ × ExplicitTensorNetwork ℕ) :
    ℕ × ℕ × ℕ × DescribedNetwork (List ℕ) :=
  (x.2.binaryPrecision x.2.binaryTableBound, x.2.binaryDegreeBound x.2.binaryTableBound + 1,
    x.1, x.2)

theorem input_polyTime :
    ComputableInPolyTime input encInput (encTrunc (encList encNat)) := by
  have hG : ComputableInPolyTime (fun x : ℕ × ExplicitTensorNetwork ℕ => x.2)
      encInput (DescribedNetwork.encDescribed (encList encNat)) := ComputableInPolyTime.snd _ _
  have hB := binaryTableBound_polyTime.comp hG
  have hM := DescribedNetwork.numEdges_polyTime.comp hG
  have hV := (ComputableInPolyTime.length_list _).comp
    (DescribedNetwork.vertices_polyTime.comp hG)
  have hS := ComputableInPolyTime.binary_size.comp (ComputableInPolyTime.unary_to_binary.comp hB)
  have hP := ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_add' hM (ComputableInPolyTime.unary_mul' hV hS))
    (ComputableInPolyTime.const 1)
  have hL := ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_mul'
      (ComputableInPolyTime.unary_sub' hB (ComputableInPolyTime.const 1)) hV)
    (ComputableInPolyTime.const 1)
  exact hP.prod (hL.prod ComputableInPolyTime.id')

/-- The fixed polynomial-time binary-digit entry evaluator. -/
@[expose] noncomputable def entryCertificate :
    NativeCertificate (fun q : List ℕ × List Bool => binaryEntry q.1 q.2)
      (encPair (encList encNat) encBits) (encList encNat) :=
  NativeCertificate.ofPolyTime binaryEntry_polyTime

/-- Exact natural contraction. The degree parameter selects a finite-size fallback only;
correctness holds for every input network and every row count. -/
@[expose] noncomputable def certificate (k : ℕ) :
    NativeCertificate (fun x : ℕ × ExplicitTensorNetwork ℕ => x.2.contraction) encInput encNat :=
  ((NativeCertificate.ofPolyTime ComputableInPolyTime.evalCoeffList_two).comp
    ((truncBoundedDegreeCertificate entryCertificate k).comp
      (NativeCertificate.ofPolyTime input_polyTime))).congr fun x =>
        evalCoeffList_truncContraction_binaryTableBound x.2

/-- Native exact contraction of fixed-degree natural networks with a polynomial number of
weight bits. The encoded output is included in the polynomial space bound. -/
theorem certificate_bound (k C D d : ℕ) :
    ∃ K : ℕ, ∀ (r : ℕ) (G : ExplicitTensorNetwork ℕ), 2 ≤ G.numEdges →
      G.IsRowsFirstBipartite r → G.vertices.length ≤ C * G.numEdges → G.maxDegree ≤ k →
      G.binaryTableBound ≤ D * (G.numEdges + 1) ^ d →
      (certificate k).time (r, G) ≤ K * ((encInput (r, G)).length + 1) ^ K *
          2 ^ (K * G.numEdges / Nat.sqrt (Nat.log 2 G.numEdges)) ∧
        (certificate k).space (r, G) ≤ K * ((encInput (r, G)).length + 1) ^ K := by
  let D' := C * (D.size + 2 * d + 1) + 2 + (C * D + 1)
  obtain ⟨K₀, hK₀⟩ := truncBoundedDegreeCertificate_bound entryCertificate
    (NativeCertificate.ofPolyTime_isPolynomial binaryEntry_polyTime) k C D' (d + 1)
  obtain ⟨K₁, hK₁⟩ := NativeCertificate.exists_polynomial_overhead
    (truncBoundedDegreeCertificate entryCertificate k) input_polyTime
    ComputableInPolyTime.evalCoeffList_two K₀
  refine ⟨K₀ + K₁, fun r G hs hrows hv hk hB => ?_⟩
  obtain ⟨hP, hℓ⟩ := binaryWeight_parameters_le (by omega : 1 ≤ G.numEdges) hv hB
  have hPD : G.binaryPrecision G.binaryTableBound ≤
      D' * G.numEdges * (Nat.log 2 G.numEdges + 1) :=
    hP.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by dsimp only [D']; omega)))
  have hℓD : G.binaryDegreeBound G.binaryTableBound + 1 ≤ D' * (G.numEdges + 1) ^ (d + 1) :=
    hℓ.trans (Nat.mul_le_mul_right _ (by dsimp only [D']; omega))
  obtain ⟨ht, hs'⟩ := hK₀ (G.binaryPrecision G.binaryTableBound)
    (G.binaryDegreeBound G.binaryTableBound + 1) r G hs hrows hv
    (G.maxDegree_le_iff.mp hk) (by simp only [binaryPrecision]; omega) hPD
    (by omega) hℓD
  obtain ⟨hT, hS⟩ := hK₁ (r, G)
    (2 ^ (K₀ * G.numEdges / Nat.sqrt (Nat.log 2 G.numEdges))) Nat.one_le_two_pow ht hs'
  have hpoly : K₁ * ((encInput (r, G)).length + 1) ^ K₁ ≤
      (K₀ + K₁) * ((encInput (r, G)).length + 1) ^ (K₀ + K₁) :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
  have hpow : 2 ^ (K₀ * G.numEdges / Nat.sqrt (Nat.log 2 G.numEdges)) ≤
      2 ^ ((K₀ + K₁) * G.numEdges / Nat.sqrt (Nat.log 2 G.numEdges)) :=
    Nat.pow_le_pow_right (by norm_num)
      (Nat.div_le_div_right (Nat.mul_le_mul_right _ (by omega)))
  exact ⟨hT.trans (Nat.mul_le_mul hpoly hpow), hS.trans hpoly⟩

end Cslib.Circuits.Frontier.BinaryWeights
