/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.DirectContraction

/-!
# Tests for direct summation

Hand-checked direct summations of small explicit networks modulo `2 ^ P`, including a precision
that reduces the result, a precision zero, a port naming no edge, a table that is too short, and
a network without edges. The last tests derive the unconditional contract form of the bounds
and check the shape of the binary-precision certificate.
-/

@[expose] public section

namespace ComplexityTests.Computability.Circuit.Frontier.DirectContraction

open Cslib.Circuits.Frontier ExplicitTensorNetwork

/-- Edges `0` and `1`; vertex `A` reads both, with table `(1, 2, 3, 4)` at positions `x₀ + 2 x₁`,
and vertex `B` reads edge `0`, with table `(5, 7)`. By hand,
`Z = (A₀₀ + A₀₁) B₀ + (A₁₀ + A₁₁) B₁ = (1 + 3)·5 + (2 + 4)·7 = 62`. -/
def path : ExplicitTensorNetwork ℕ :=
  ⟨2, [([0, 1], [1, 2, 3, 4]), ([0], [5, 7])]⟩

example : path.contraction = 62 := by decide

/-- `62 = 3·16 + 14`, `62 < 2 ^ 6`, and every number is `0` modulo `2 ^ 0 = 1`. -/
example : directContraction (4, 1, path) = 14 ∧ directContraction (6, 1, path) = 62 ∧
    directContraction (0, 1, path) = 0 := by
  decide

/-- The number `r` of row vertices does not change direct summation. -/
example : directContraction (4, 0, path) = directContraction (4, 2, path) := by decide

/-- The correctness theorem on this instance. -/
example : directContraction (4, 1, path) = 62 % 2 ^ 4 := by
  rw [directContraction_eq]
  decide

/-- Port `5` names no edge and reads `false`; the table `(3)` of the last vertex has no entry at
position `1`, which reads `0`. So only `x₀ = 0` contributes: `Z = 3 · 3 = 9`. -/
def ragged : ExplicitTensorNetwork ℕ :=
  ⟨1, [([5], [3, 4]), ([0], [3])]⟩

example : ragged.contraction = 9 ∧ directContraction (10, 0, ragged) = 9 := by decide

/-- A network without edges has one assignment, the empty one, and its contraction is the product
of the entries at position `0`. -/
def noEdges : ExplicitTensorNetwork ℕ :=
  ⟨0, [([], [6]), ([], [7])]⟩

example : directContraction (5, 0, noEdges) = 42 % 32 := by decide

/-- The bounds give the unconditional contract form `K (n + 1) ^ K 2 ^ (K m)` on every input. -/
example : ∃ K : ℕ, ∀ x : ℕ × ℕ × ExplicitTensorNetwork ℕ,
    directContractionCertificate.time x ≤
        K * ((encContractionInput x).length + 1) ^ K * 2 ^ (K * x.2.2.numEdges) ∧
      directContractionCertificate.space x ≤ K * ((encContractionInput x).length + 1) ^ K := by
  obtain ⟨K, hK⟩ := exists_directContractionCertificate_le
  refine ⟨K + 1, fun x => ⟨(hK x).1.trans ?_, (hK x).2.trans ?_⟩⟩
  · exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_succ K)
      (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ K)))
      (Nat.pow_le_pow_right two_pos (Nat.le_mul_of_pos_left _ (Nat.succ_pos K)))
  · exact Nat.mul_le_mul (Nat.le_succ K) (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ K))

/-- With the precision in binary, the certificate has the shape the counting simulation's
contraction interface asks for: `(P, G) ↦ value G % 2 ^ P` on `encPair encNat encN`, with `G`
the row count and the network, `value G` its contraction and
`encN = encPair encNat encExplicitNetwork`. -/
noncomputable example : Cslib.GenericRAM.NativeCertificate
    (fun p : ℕ × (ℕ × ExplicitTensorNetwork ℕ) =>
      (fun G : ℕ × ExplicitTensorNetwork ℕ => G.2.contraction) p.2 % 2 ^ p.1)
    (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encNat
      (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encNat encExplicitNetwork))
    Turing.MultiTapeTM.encNat :=
  directContractionBinaryCertificate

end ComplexityTests.Computability.Circuit.Frontier.DirectContraction
