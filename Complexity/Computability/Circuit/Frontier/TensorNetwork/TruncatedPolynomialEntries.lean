/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.TruncatedEntry

/-!
# Direct truncated contraction with polynomial-time entries

For a fixed polynomial-time entry procedure, direct truncated contraction costs a polynomial in
the encoded input times `2 ^ m`, where `m` is the number of edges, and polynomial space. This is
the finite-size fallback for bounded-degree weighted counting.

## Main results

* `truncDirectCertificate_le_of_isPolynomial`: uniform direct-contraction bounds without a
  degree or bipartition hypothesis.
-/

public section

namespace Cslib.Circuits.Frontier

open Cslib.GenericRAM Turing.MultiTapeTM

variable {T : Type} {encT : T ↪ List Bool} {entry : T → List Bool → List ℕ}

/-- The encoded argument of an entry on a vertex is at most three times the encoded network
length plus a constant. -/
theorem DescribedNetwork.length_entryInput_le (G : DescribedNetwork T)
    {v : List ℕ × T} (hv : v ∈ G.vertices) {bs : List Bool} (hbs : bs.length = v.1.length) :
    (encPair encT encBits (v.2, bs)).length + 1 ≤
      3 * ((DescribedNetwork.encDescribed encT G).length + 1) := by
  have h1 := length_le_encList_of_mem (encPair (encList encNat) encT) hv
  have h2 : (encList (encPair (encList encNat) encT) G.vertices).length ≤
      (DescribedNetwork.encDescribed encT G).length := by
    change _ ≤ (encPair encUnary (encList (encPair (encList encNat) encT))
      (G.numEdges, G.vertices)).length
    rw [length_encPair]
    dsimp only
    omega
  have h3 := length_le_length_encList encNat v.1
  simp only [length_encPair, encBits_apply] at h1 ⊢
  omega

/-- Direct truncated contraction with a polynomial entry procedure has only the `2 ^ m`
enumeration factor. The result includes its encoded output in the space bound. -/
theorem truncDirectCertificate_le_of_isPolynomial
    (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
      (encList encNat)) (hce : ce.IsPolynomial) :
    ∃ K : ℕ, ∀ (P ℓ r : ℕ) (G : DescribedNetwork T),
      (truncDirectCertificate entry ce).time (P, ℓ, r, G) ≤
          K * ((encTrunc encT (P, ℓ, r, G)).length + 1) ^ K * 2 ^ G.numEdges ∧
        (truncDirectCertificate entry ce).space (P, ℓ, r, G) ≤
          K * ((encTrunc encT (P, ℓ, r, G)).length + 1) ^ K := by
  obtain ⟨a, d, ha⟩ := (hce.1.add hce.2).exists_le
  obtain ⟨Kd, hKd⟩ := truncDirectCertificate_le entry ce
  let E : ℕ → ℕ := fun n => a * 3 ^ d * (n + 1) ^ d
  let F : ℕ → ℕ := fun n => Kd * (n + E n + 1) ^ Kd * (E n + 1)
  have hEp : PolyBounded id E :=
    (PolyBounded.const (a * 3 ^ d)).mul ((PolyBounded.self.add (PolyBounded.const 1)).pow d)
  have hFp : PolyBounded id F :=
    ((PolyBounded.const Kd).mul (((PolyBounded.self.add hEp).add
      (PolyBounded.const 1)).pow Kd)).mul (hEp.add (PolyBounded.const 1))
  obtain ⟨aF, dF, hF⟩ := hFp.exists_le
  refine ⟨aF + dF, fun P ℓ r G => ?_⟩
  set n := (encTrunc encT (P, ℓ, r, G)).length
  have hL : (DescribedNetwork.encDescribed encT G).length ≤ n := by
    simp only [n, length_encPair]
    omega
  have he : ∀ v ∈ G.vertices, ∀ bs : List Bool, bs.length = v.1.length →
      ce.time (v.2, bs) ≤ E n ∧ ce.space (v.2, bs) ≤ E n := by
    intro v hv bs hbs
    have h1 := G.length_entryInput_le (encT := encT) hv hbs
    have h2 := ha (v.2, bs)
    have h3 : a * ((encPair encT encBits (v.2, bs)).length + 1) ^ d ≤ E n := by
      calc _ ≤ a * (3 * (n + 1)) ^ d :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) d)
        _ = E n := by simp only [E, mul_pow]; ring
    exact ⟨by omega, by omega⟩
  obtain ⟨hT, hS⟩ := hKd P ℓ r G (E n) (E n) he
  have hbound : F n ≤ (aF + dF) * (n + 1) ^ (aF + dF) :=
    (hF n).trans (Nat.mul_le_mul (by omega)
      (Nat.pow_le_pow_right (by omega) (by omega)))
  refine ⟨?_, ?_⟩
  · calc (truncDirectCertificate entry ce).time (P, ℓ, r, G)
        ≤ Kd * (n + E n + 1) ^ Kd * 2 ^ G.numEdges * (E n + 1) := hT
      _ = F n * 2 ^ G.numEdges := by simp only [F]; ring
      _ ≤ (aF + dF) * (n + 1) ^ (aF + dF) * 2 ^ G.numEdges :=
        Nat.mul_le_mul_right _ hbound
  · calc (truncDirectCertificate entry ce).space (P, ℓ, r, G)
        ≤ Kd * (n + E n + 1) ^ Kd := hS
      _ ≤ F n := Nat.le_mul_of_pos_right _ (by omega)
      _ ≤ (aF + dF) * (n + 1) ^ (aF + dF) := hbound

end Cslib.Circuits.Frontier
