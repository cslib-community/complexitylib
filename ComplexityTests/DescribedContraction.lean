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
network, the agreement with explicit networks, and one native machine for the contraction with
its resource theorem. -/

namespace ComplexityTests.DescribedContraction

open Cslib.Circuits.Frontier Cslib.Circuits.Frontier.DescribedNetwork Cslib.BitString
  Turing.MultiTapeTM

/-- One edge between two vertices with tables `[2, 3]` and `[5, 7]`: contraction
`2 * 5 + 3 * 7 = 31`. -/
def oneEdge : DescribedNetwork (List ℕ) := ⟨1, [([0], [2, 3]), ([0], [5, 7])]⟩

example : oneEdge.contraction ExplicitTensorNetwork.entry = 31 := by decide

-- The stack machine, with fuel `2 (2 ^ 1 * 3) + 1 = 13`, returns `31 % 16 = 15`.
example : (sumScheme ExplicitTensorNetwork.entry).run fuel sumRoot (4, oneEdge) = some 15 := by
  decide

-- With one step fewer, the sum still waits for the second assignment's weight
-- `3 * 7 = 21 ≡ 5`.
example : (sumScheme ExplicitTensorNetwork.entry).run (fun _ => 12) sumRoot (4, oneEdge) =
    some 5 := by
  decide

-- On every input, the run is the contraction modulo `2 ^ P`, for any evaluator.
example {T : Type} (eval : T → List Bool → ℕ) (q : ℕ × DescribedNetwork T) :
    (sumScheme eval).run fuel sumRoot q = some (q.2.contraction eval % 2 ^ q.1) :=
  run_sumScheme q

-- Explicit networks are described networks with their tables.
example (d : ExplicitTensorNetwork ℕ) :
    (ofExplicit d).contraction ExplicitTensorNetwork.entry = d.contraction :=
  contraction_ofExplicit d

/-- Table lookup is polynomial-time. -/
theorem entry_polyTime : ComputableInPolyTime (fun q : List ℕ × List Bool =>
    ExplicitTensorNetwork.entry q.1 q.2) (encPair (encList encNat) encBits) encNat := by
  have hindex := ComputableInPolyTime.bitsBinaryValue.comp
    (ComputableInPolyTime.bitsReverse.comp (ComputableInPolyTime.snd (encList encNat) encBits))
  refine (ComputableInPolyTime.listGetD_binary (encA := encNat) (encL := encList encNat) 0
    (ComputableInPolyTime.fst (encList encNat) encBits) hindex).of_enc_eq fun q => ?_
  simp only [Function.comp_def, ExplicitTensorNetwork.entry, lsbValue_eq_binaryValue_reverse]

/-- **One native machine contracts explicit networks** given as described networks with their
tables, from the table-lookup certificate. -/
noncomputable def tableCertificate :
    Cslib.GenericRAM.NativeCertificate
      (fun q : ℕ × DescribedNetwork (List ℕ) =>
        q.2.contraction ExplicitTensorNetwork.entry % 2 ^ q.1)
      (encInput (encList encNat)) encNat :=
  contractionCertificate ExplicitTensorNetwork.entry
    (Cslib.GenericRAM.NativeCertificate.ofPolyTime entry_polyTime)

-- The resource theorem applies to it.
example : ∃ K : ℕ, ∀ (q : ℕ × DescribedNetwork (List ℕ)) (E ES Ev : ℕ),
    (∀ v ∈ q.2.vertices, ∀ bs : List Bool, bs.length = v.1.length →
      (Cslib.GenericRAM.NativeCertificate.ofPolyTime entry_polyTime).time (v.2, bs) ≤ E ∧
        (Cslib.GenericRAM.NativeCertificate.ofPolyTime entry_polyTime).space (v.2, bs) ≤ ES ∧
        (encNat (ExplicitTensorNetwork.entry v.2 bs)).length ≤ Ev) →
    tableCertificate.time q ≤ (2 ^ q.2.numEdges * (q.2.vertices.length + 1) + 1) *
        (K * ((encInput (encList encNat) q).length + Ev + 1) ^ K + 2 * E) ∧
      tableCertificate.space q ≤ K * ((encInput (encList encNat) q).length + Ev + 1) ^ K + ES :=
  contractionCertificate_le _

end ComplexityTests.DescribedContraction
