/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BQP.Sampling
public import Complexity.Probability.RankDecoder.Native
public import Complexity.Computability.Probabilistic.Sampling
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup

/-!
# Native resources for exact quantum output sampling

The seed generator is the existing native fair-bit sampler. The deterministic decoder makes at
most one projected-gap query per distinct target wire. Its native loop retains the original
input, a prefix and a binary residual rank; the rank never increases. Polynomially many adaptive
queries therefore reuse polynomial workspace and preserve a common contraction time factor.
The final polynomial-time pass writes the entire explicit output register, including untouched
wires. The circuit width enters this polynomial cost, not the exponential factor.

The certificates apply to polynomial-time supplied circuits, explicit registers and seeds. In the
seed-decoder formulation a seed has exactly `h` bits, where `h ≤ L`; adding it to the explicit
input changes its encoded size by only a polynomial factor. Randomness refers to these sampled
seed bits, rather than unused coins of deterministic transitions in the native PTM model.
-/

public section

namespace Cslib.Complexity.QuantumContraction

open Quantum BitString Turing.MultiTapeTM Cslib.GenericRAM ComputableInPolyTime

variable {α : Type} {enc : α ↪ List Bool}

private theorem poly_targets {gs : α → List GateCode}
    (hgs : ComputableInPolyTime gs enc (encList encGateCode)) :
    ComputableInPolyTime (fun a => GateCode.targets (gs a)) enc (encList encUnary) := by
  unfold GateCode.targets GateCode.target
  apply eraseDupsByWithInput
  · fun_prop
  · fun_prop

private theorem poly_restorePositions {S : α → List ℕ} {X bits : α → List Bool}
    (hS : ComputableInPolyTime S enc (encList encUnary))
    (hX : ComputableInPolyTime X enc encBits)
    (hbits : ComputableInPolyTime bits enc encBits) :
    ComputableInPolyTime (fun a => restorePositions (S a) (X a) (bits a)) enc encBits := by
  unfold restorePositions
  refine mapToBitsWithInput (range.comp (length_bits.comp hX)) ?_
  have hpos := hS.comp (fst enc encUnary)
  have hi := snd enc encUnary
  refine ite_decide (decide_mem hpos hi) ?_ ?_
  · exact bitsGetDWithInput (hbits.comp (fst enc encUnary)) (idxOfWithInput hpos hi) false
  · exact bitsGetDWithInput (hX.comp (fst enc encUnary)) hi false

/-- The native generator samples exactly the number of bits used by the circuit's Hadamards.
The polynomial-time guarantee is only for this seed generator. -/
theorem isPPTOn_outputSeed {gs : α → List GateCode}
    (hgs : ComputableInPolyTime gs enc (encList encGateCode)) :
    Probability.IsPPTOn enc encBits (fun a => sampleList (hadamardCount (gs a))) := by
  have hh : ComputableInPolyTime (fun a => hadamardCount (gs a)) enc encUnary := by
    simp only [hadamardCount_eq_countP]
    fun_prop
  exact hh.sampleList

/-- **The complete deterministic decoder as one native certificate.** Circuits, explicit input
registers and seeds are supplied in polynomial time. For every input, including every possible
seed, the decoder has time `2 ^ O((L+1)/√log(L+2))` times a polynomial and polynomial space.
No probability or seed-validity assumption is used for this computational bound. -/
theorem exists_expTimePolySpace_decodeOutput {gs : α → List GateCode} {X seed : α → List Bool}
    (hgs : ComputableInPolyTime gs enc (encList encGateCode))
    (hX : ComputableInPolyTime X enc encBits)
    (hseed : ComputableInPolyTime seed enc encBits)
    (hwf : ∀ a, ∀ g ∈ gs a, g.WellFormed (X a).length) :
    ∃ (A : ℕ) (c : NativeCertificate (fun a => decodeOutput (gs a) (X a) (seed a)) enc encBits),
      c.ExpTimePolySpace fun a =>
        A * ((gs a).length + 1) / Nat.sqrt (Nat.log 2 ((gs a).length + 2)) := by
  have hS := poly_targets hgs
  have hd := (length_list encUnary).comp hS
  have hr := bitsBinaryValue.comp hseed
  have ha : ComputableInPolyTime (fun s : RankDecoder.State α => s.input)
      (RankDecoder.stateEncoding enc) enc := fst _ _
  have hpre : ComputableInPolyTime (fun s : RankDecoder.State α => s.prefix ++ [false])
      (RankDecoder.stateEncoding enc) encBits := by
    unfold RankDecoder.stateEncoding
    fun_prop
  obtain ⟨A, cm, hm⟩ := exists_expTimePolySpace_prefixGap (hgs.comp ha) (hX.comp ha)
    (hS.comp ha) hpre (fun s => hwf s.input)
    (fun s _ hj => GateCode.lt_of_mem_targets (hwf s.input) hj)
    (fun s => GateCode.targets_length_le (gs s.input))
  let c := RankDecoder.nativeCertificate
    (mass := fun a => prefixGap (gs a) (X a) (GateCode.targets (gs a)))
    (unary_to_binary.comp hd) hr cm
  have hc := RankDecoder.nativeCertificate_expTimePolySpace
    (E := fun a => A * ((gs a).length + 1) / Nat.sqrt (Nat.log 2 ((gs a).length + 2)))
    (mass := fun a => prefixGap (gs a) (X a) (GateCode.targets (gs a)))
    (unary_to_binary.comp hd) hr cm hd.polyBounded hm
  have hpost : ComputableInPolyTime (fun p : α × List Bool =>
      restorePositions (GateCode.targets (gs p.1)) (X p.1) p.2)
      (encPair enc encBits) encBits :=
    poly_restorePositions (hS.comp (fst _ _)) (hX.comp (fst _ _)) (snd _ _)
  have hid : ComputableInPolyTime (fun a : α => a) enc enc := of_eq fun _ => rfl
  let ci := NativeCertificate.ofPolyTime hid
  let result := ((NativeCertificate.ofPolyTime hpost).comp (ci.prod c)).congr (fun _ => rfl)
  refine ⟨A, result, ?_⟩
  have hpaired := (NativeCertificate.expTimePolySpace_ofPolyTime hid (fun _ => 0)).prod hc
  exact (hpaired.comp_ofPolyTime hpost).mono (fun _ => by simp)

/-- **Worst-case native time and simultaneous polynomial workspace for the complete decoder.**
The polynomial includes constructing prefixes, binary integer arithmetic and writing the full
explicit output register. -/
theorem exists_computableInO_decodeOutput {gs : α → List GateCode} {X seed : α → List Bool}
    (hgs : ComputableInPolyTime gs enc (encList encGateCode))
    (hX : ComputableInPolyTime X enc encBits)
    (hseed : ComputableInPolyTime seed enc encBits)
    (hwf : ∀ a, ∀ g ∈ gs a, g.WellFormed (X a).length) :
    ∃ A e : ℕ, ComputableInO (fun a => decodeOutput (gs a) (X a) (seed a)) enc encBits
      (fun a => 2 ^ (A * ((gs a).length + 1) /
        Nat.sqrt (Nat.log 2 ((gs a).length + 2))) * ((enc a).length + 1) ^ e)
      (fun a => ((enc a).length + 1) ^ e) := by
  obtain ⟨A, c, hc⟩ := exists_expTimePolySpace_decodeOutput hgs hX hseed hwf
  obtain ⟨e, he⟩ := hc.computableInO
  exact ⟨A, e, he⟩

end Cslib.Complexity.QuantumContraction
