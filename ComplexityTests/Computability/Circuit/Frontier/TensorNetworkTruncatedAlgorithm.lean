/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.TruncatedAlgorithm
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Tests for the interface of Theorem D.1 at truncation order `ℓ`

The interface is not vacuous: for networks with at most `C` edges and descriptors that are their
own entries, direct summation meets its bound (`boundedAlgorithm`). The guard holds on a small
network, and on admissible inputs from the size `4 (C D + 1)` on.
-/

@[expose] public section

namespace ComplexityTests.TensorNetworkTruncatedAlgorithm

open Cslib Cslib.GenericRAM Cslib.Circuits.Frontier Turing.MultiTapeTM

/-- A descriptor is its own entry, whatever the bits. -/
def constEntry (t : List ℕ) (_ : List Bool) : List ℕ := t

/-- The entry certificate of constant descriptors. -/
noncomputable def constCert :
    NativeCertificate (fun q : List ℕ × List Bool => constEntry q.1 q.2)
      (encPair (encList encNat) encBits) (encList encNat) :=
  NativeCertificate.ofPolyTime (ComputableInPolyTime.fst _ _)

/-- Networks with at most `C` edges. -/
def BoundedEdges (C _s : ℕ) (G : ℕ × DescribedNetwork (List ℕ)) : Prop := G.2.numEdges ≤ C

/-- **The interface is not vacuous**: direct summation is a truncated contraction algorithm for
networks with boundedly many edges. -/
noncomputable def boundedAlgorithm :
    TruncatedContractionAlgorithm (encList encNat) constEntry BoundedEdges where
  certificate := truncDirectCertificate constEntry constCert
  bound C _ := by
    obtain ⟨K, hK⟩ := truncDirectCertificate_le (encT := encList encNat) constEntry constCert
    obtain ⟨p, hp, hm, hb⟩ := exists_mono_poly_cert
      (ComputableInPolyTime.fst (encList encNat) encBits)
    let F : ℕ → ℕ := fun n => K * (n + p (3 * n + 1) + 1) ^ K * 2 ^ C * (p (3 * n + 1) + 1)
    have hF : PolyBounded id F :=
      ((((PolyBounded.const K).mul (((PolyBounded.self.add
        ((PolyBounded.of_polynomiallyBounded id hp).comp (((PolyBounded.const 3).mul
          PolyBounded.self).add (PolyBounded.const 1)))).add (PolyBounded.const 1)).pow K)).mul
        (PolyBounded.const (2 ^ C))).mul
        (((PolyBounded.of_polynomiallyBounded id hp).comp (((PolyBounded.const 3).mul
          PolyBounded.self).add (PolyBounded.const 1))).add (PolyBounded.const 1)))
    obtain ⟨a, d, had⟩ := hF.exists_le
    refine ⟨a + d, fun s P ℓ r G _ _ _ _ _ hA => ?_⟩
    set n := (encTrunc (encList encNat) (P, ℓ, r, G)).length with hn
    have hv : ∀ v ∈ G.vertices, ∀ bs : List Bool, bs.length = v.1.length →
        constCert.time (v.2, bs) ≤ p (3 * n + 1) ∧ constCert.space (v.2, bs) ≤ p (3 * n + 1) := by
      intro v hv bs hbs
      have h1 := List.le_sum_of_mem
        (List.mem_map_of_mem (f := fun a => (encPair (encList encNat) (encList encNat) a).length)
          hv)
      have h2 := sum_length_le_length_encList (encPair (encList encNat) (encList encNat))
        G.vertices
      have h3 := length_le_length_encList encNat v.1
      have hG : (encList (encPair (encList encNat) (encList encNat)) G.vertices).length ≤ n := by
        simp only [hn, encTrunc, DescribedNetwork.encDescribed, DescribedNetwork.equivProd,
          encOfEquiv_apply, length_encPair]
        simp
        omega
      have hvl : (encPair (encList encNat) (encList encNat) v).length ≤ n := by
        omega
      have hlen : (encPair (encList encNat) encBits (v.2, bs)).length ≤ 3 * n + 1 := by
        simp only [length_encPair, encBits_apply] at hvl ⊢
        omega
      exact ⟨(hb _).1.trans (hm hlen), (hb _).2.trans (hm hlen)⟩
    obtain ⟨hT, hS⟩ := hK P ℓ r G _ _ hv
    have h2 : 2 ^ G.numEdges ≤ 2 ^ C := Nat.pow_le_pow_right (by norm_num) hA
    have hFn := had n
    simp only [id] at hFn
    have hK' : a * (n + 1) ^ d ≤ (a + d) * (n + 1) ^ (a + d) :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
    have hX : (a + d) * (n + 1) ^ (a + d) ≤ (a + d) * (n + 1) ^ (a + d) *
        2 ^ ((a + d) * s / Nat.sqrt (Nat.log 2 s)) :=
      Nat.le_mul_of_pos_right _ Nat.one_le_two_pow
    have hT' : (truncDirectCertificate constEntry constCert).time (P, ℓ, r, G) ≤ F n :=
      hT.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2))
    have hS' : (truncDirectCertificate constEntry constCert).space (P, ℓ, r, G) ≤ F n := by
      refine hS.trans ?_
      have h1 : 1 ≤ 2 ^ C * (p (3 * n + 1) + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      calc K * (n + p (3 * n + 1) + 1) ^ K ≤ K * (n + p (3 * n + 1) + 1) ^ K *
            (2 ^ C * (p (3 * n + 1) + 1)) := Nat.le_mul_of_pos_right _ h1
        _ = F n := by simp only [F]; ring
    exact ⟨by omega, by omega⟩

-- The guard holds on a network with one edge and one vertex at truncation order `2`.
example : truncGuard (1, 2, 0, (⟨1, [([0], [1, 1])]⟩ : DescribedNetwork (List ℕ))) = true := by
  decide

-- Admissible inputs pass the guard from the size `4 (C D + 1)` on.
example {C D s P ℓ r : ℕ} {G : DescribedNetwork (List ℕ)} (hs : 4 * (C * D + 1) ≤ s)
    (hℓ : ℓ ≤ D * s) (hk : G.vertices.length ≤ C * s) (hm : s ≤ G.numEdges) :
    truncGuard (P, ℓ, r, G) = true :=
  truncGuard_of_le hs hℓ hk hm

end ComplexityTests.TensorNetworkTruncatedAlgorithm
