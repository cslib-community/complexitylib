/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.TruncatedEntry
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope

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
  obtain ⟨KF, hF⟩ := hFp.exists_le_succ_pow
  refine ⟨KF, fun P ℓ r G => ?_⟩
  set n := (encTrunc encT (P, ℓ, r, G)).length
  have hL : (DescribedNetwork.encDescribed encT G).length ≤ n := by
    enc_len [n]
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
  have hbound : F n ≤ KF * (n + 1) ^ KF := hF _ le_rfl n
  refine ⟨?_, ?_⟩
  · calc (truncDirectCertificate entry ce).time (P, ℓ, r, G)
        ≤ Kd * (n + E n + 1) ^ Kd * 2 ^ G.numEdges * (E n + 1) := hT
      _ = F n * 2 ^ G.numEdges := by simp only [F]; ring
      _ ≤ KF * (n + 1) ^ KF * 2 ^ G.numEdges := by gcongr
  · calc (truncDirectCertificate entry ce).space (P, ℓ, r, G)
        ≤ Kd * (n + E n + 1) ^ Kd := hS
      _ ≤ F n := Nat.le_mul_of_pos_right _ (by omega)
      _ ≤ KF * (n + 1) ^ KF := hbound

end Cslib.Circuits.Frontier
