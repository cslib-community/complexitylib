/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Frontier.TensorNetwork.DescribedContraction
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives

/-! # Direct summation over described networks

Tables as descriptors, with table lookup as the evaluator: the stack machine on a one-edge
network modulo `2 ^ P` and over coefficient lists of `(ℤ / 4)[U] / (U ^ 2 + U + 1)`, the agreement
with explicit networks, and one native machine for the contraction with its resource theorem. -/

namespace ComplexityTests.DescribedContraction

open Cslib.Circuits.Frontier Cslib.Circuits.Frontier.DescribedNetwork Cslib.BitString
  Turing.MultiTapeTM

/-- One edge between two vertices with tables `[2, 3]` and `[5, 7]`: contraction
`2 * 5 + 3 * 7 = 31`. -/
def oneEdge : DescribedNetwork (List ℕ) := ⟨1, [([0], [2, 3]), ([0], [5, 7])]⟩

example : oneEdge.contraction ExplicitTensorNetwork.entry = 31 := by decide

-- The stack machine modulo `2 ^ 4`, with fuel `2 (2 ^ 1 * 3) + 1 = 13`, returns `31 % 16 = 15`.
example : (sumScheme SumOps.mod ExplicitTensorNetwork.entry).run fuel sumRoot (4, oneEdge) =
    some 15 := by
  decide

-- With one step fewer, the sum still waits for the second assignment's weight
-- `3 * 7 = 21 ≡ 5`.
example : (sumScheme SumOps.mod ExplicitTensorNetwork.entry).run (fun _ => 12) sumRoot
    (4, oneEdge) = some 5 := by
  decide

-- On every input, the run modulo `2 ^ P` is the contraction modulo `2 ^ P`, for any evaluator.
example {T : Type} (eval : T → List Bool → ℕ) (q : ℕ × DescribedNetwork T) :
    (sumScheme SumOps.mod eval).run fuel sumRoot q = some (q.2.contraction eval % 2 ^ q.1) := by
  rw [run_sumScheme, sumValue_mod]

/-- One edge between two vertices whose entries are coefficient lists of
`(ℤ / 4)[U] / (U ^ 2 + U + 1)`: `U, 1` and `U, 3`. The contraction is
`U ^ 2 + 3 = 2 - U`, the list `[2, 3]`. -/
def galoisEdge : DescribedNetwork (List (List ℕ)) :=
  ⟨1, [([0], [[0, 1], [1, 0]]), ([0], [[0, 1], [3, 0]])]⟩

/-- Table lookup on coefficient lists. -/
def galoisEntry (t : List (List ℕ)) (bs : List Bool) : List ℕ :=
  t.getD (lsbValue bs) []

-- The stack machine over coefficient lists at the precision `(2, [1, 1])`.
example : (sumScheme SumOps.galois galoisEntry).run fuel sumRoot ((2, [1, 1]), galoisEdge) =
    some [2, 3] := by
  decide

-- On every input, the value of the run in `A_p` is the contraction of the values of the entries.
example {T : Type} (eval : T → List Bool → List ℕ) (q : (ℕ × List ℕ) × DescribedNetwork T) :
    (sumScheme SumOps.galois eval).run fuel sumRoot q =
        some (sumValue SumOps.galois eval q.1 q.2) ∧
      Cslib.GaloisRingArith.val q.1.1 q.1.2 (sumValue SumOps.galois eval q.1 q.2) =
        q.2.contraction fun t bs => Cslib.GaloisRingArith.val q.1.1 q.1.2 (eval t bs) :=
  ⟨run_sumScheme q, val_sumValue_galois eval q.1 q.2⟩

-- Explicit networks are described networks with their tables.
example (d : ExplicitTensorNetwork ℕ) :
    DescribedNetwork.contraction ExplicitTensorNetwork.entry d = d.contraction :=
  contraction_entry d

/-- Table lookup is polynomial-time. -/
theorem entry_polyTime : ComputableInPolyTime (fun q : List ℕ × List Bool =>
    ExplicitTensorNetwork.entry q.1 q.2) (encPair (encList encNat) encBits) encNat := by
  have hindex := ComputableInPolyTime.bitsBinaryValue.comp
    (ComputableInPolyTime.bitsReverse.comp (ComputableInPolyTime.snd (encList encNat) encBits))
  refine (ComputableInPolyTime.listGetD_binary (encA := encNat) (encL := encList encNat) 0
    (ComputableInPolyTime.fst (encList encNat) encBits) hindex).of_enc_eq fun q => ?_
  simp only [Function.comp_def, ExplicitTensorNetwork.entry, lsbValue_eq_binaryValue_reverse]

/-- **One native machine contracts explicit networks** modulo `2 ^ P`, given as described
networks with their tables, from the table-lookup certificate. -/
noncomputable def tableCertificate :
    Cslib.GenericRAM.NativeCertificate
      (fun q : ℕ × DescribedNetwork (List ℕ) =>
        q.2.contraction ExplicitTensorNetwork.entry % 2 ^ q.1)
      (encInput encUnary (encList encNat)) encNat :=
  modContractionCertificate ExplicitTensorNetwork.entry
    (Cslib.GenericRAM.NativeCertificate.ofPolyTime entry_polyTime)

-- The resource theorem applies to it, with residues of at most `P` bits.
example : ∃ K : ℕ, ∀ (q : ℕ × DescribedNetwork (List ℕ)) (E ES Ev : ℕ),
    (∀ v ∈ q.2.vertices, ∀ bs : List Bool, bs.length = v.1.length →
      (Cslib.GenericRAM.NativeCertificate.ofPolyTime entry_polyTime).time (v.2, bs) ≤ E ∧
        (Cslib.GenericRAM.NativeCertificate.ofPolyTime entry_polyTime).space (v.2, bs) ≤ ES ∧
        (encNat (ExplicitTensorNetwork.entry v.2 bs)).length ≤ Ev) →
    tableCertificate.time q ≤ (2 ^ q.2.numEdges * (q.2.vertices.length + 1) + 1) *
        (K * ((encInput encUnary (encList encNat) q).length + Ev + q.1 + 1) ^ K + 2 * E) ∧
      tableCertificate.space q ≤
        K * ((encInput encUnary (encList encNat) q).length + Ev + q.1 + 1) ^ K + ES := by
  obtain ⟨K, hK⟩ := contractionCertificate_le (ops := SumOps.mod)
    (encT := encList encNat) SumOps.mod_polyTime
    (Cslib.GenericRAM.NativeCertificate.ofPolyTime entry_polyTime)
  refine ⟨K, fun q E ES Ev hE => hK q E ES Ev q.1 hE fun y hy => ?_⟩
  have h := Nat.size_le.mpr (show y < 2 ^ q.1 from hy)
  rw [← Nat.size_eq_bits_len] at h
  exact h

-- Coefficient lists are polynomial-time operations, with `p` in unary.
example : SumOps.galois.PolyTime (encPair encUnary (encList encNat)) (encList encNat) :=
  SumOps.galois_polyTime

end ComplexityTests.DescribedContraction
