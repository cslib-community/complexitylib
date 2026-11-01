/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BQP.OutputGap
public import Complexity.Computability.Circuit.Quantum.OutputSupport
public import Complexity.Probability.RankDecoder
public import Complexity.Languages.Probabilistic.BitString

/-!
# Exact sampling of quantum circuit outputs

The projected-gap simulator gives every output prefix an integer mass with denominator `2 ^ h`,
where `h` is the circuit's number of Hadamard gates. Sampling exactly `h` fair bits supplies a
uniform integer rank. The deterministic rank decoder then samples the measurement on the
circuit's distinct target wires, and restores all other bits from the input register.

The resulting `ProbComp` program has exactly the existing final computational-basis measurement
law, including correlations between output bits and destructive interference. No rejection loop
or approximation is used. The input register is explicit; the gate set is Hadamard, NOT, CNOT
and Toffoli. This is a formal sampling consequence of the exact simulator, with no priority claim.

## Main definitions

* `Cslib.Complexity.QuantumContraction.decodeOutput`: decode a fixed fair-bit seed to a complete
  output register.
* `Cslib.Complexity.QuantumContraction.sampleOutput`: sample `h` fair bits and decode them.

## Main results

* `Cslib.Complexity.QuantumContraction.uniformList_decode_prefixGap`: rank decoding gives the
  joint marginal on any distinct valid wire list.
* `Cslib.Complexity.QuantumContraction.uniformList_decodeOutput`: the seed pushforward is the
  full measurement distribution.
* `Cslib.Complexity.QuantumContraction.eval_sampleOutput`: exact correctness of the sampler.
-/

public section

namespace Cslib.Complexity.QuantumContraction

open Quantum BitString

/-- Decoding a uniform Hadamard-bit seed gives exactly the joint measurement on a distinct list
of valid wires. -/
theorem uniformList_decode_prefixGap {gs : List GateCode} {X : List Bool}
    (hgs : ∀ g ∈ gs, g.WellFormed X.length) {S : List ℕ} (hS : S.Nodup)
    (hvalid : ∀ j ∈ S, j < X.length) :
    (uniformList (hadamardCount gs)).map
        (fun seed => RankDecoder.decode (prefixGap gs X S) S.length [] (binaryValue seed)) =
      (Circuit.measure (Circuit.ofCodes X.length gs) (inputState X.length X)).map
        (fun y => S.map (readBit y)) := by
  ext word
  rw [RankDecoder.uniformList_decode_apply
    (fun pre hlen => prefixGap_add hgs hS hvalid pre hlen)
    (hadamardCount gs) (prefixGap_nil hgs S)]
  by_cases hlen : word.length = S.length
  · rw [ite_eq_left hlen, measure_map_readBit_apply gs X hvalid hlen,
      patternProb_eq_prefixGap hgs hS hvalid,
      ENNReal.ofReal_div_of_pos (by positivity)]
    simp
  · rw [ite_eq_right hlen]
    symm
    rw [PMF.map_apply, tsum_fintype]
    apply Finset.sum_eq_zero
    intro y _
    have hne : word ≠ S.map (readBit y) := by
      intro heq
      apply hlen
      rw [heq, List.length_map]
    simp [hne]

/-- Decode a seed by querying integer prefix masses only on distinct target wires, then restore
all untouched bits from the explicit input. The function is total on arbitrary seeds and codes;
its exact distribution guarantee requires well-formed codes and a uniform `h`-bit seed. -/
@[expose] def decodeOutput (gs : List GateCode) (X seed : List Bool) : List Bool :=
  restorePositions (GateCode.targets gs) X
    (RankDecoder.decode (prefixGap gs X (GateCode.targets gs)) (GateCode.targets gs).length []
      (binaryValue seed))

/-- Every seed decodes to an output register of the original width. -/
@[simp] theorem length_decodeOutput (gs : List GateCode) (X seed : List Bool) :
    (decodeOutput gs X seed).length = X.length := by
  simp [decodeOutput]

/-- The empty circuit returns the input, for every seed. -/
@[simp] theorem decodeOutput_nil (X seed : List Bool) : decodeOutput [] X seed = X := by
  change restorePositions [] X [] = X
  simpa [readPositions] using
    restorePositions_readPositions [] X X rfl (fun _ _ _ => rfl)

/-- The uniform Hadamard-bit seed, decoded and restored, has exactly the complete measurement
law of the circuit. -/
theorem uniformList_decodeOutput {gs : List GateCode} {X : List Bool}
    (hgs : ∀ g ∈ gs, g.WellFormed X.length) :
    (uniformList (hadamardCount gs)).map (decodeOutput gs X) =
      (Circuit.measure (Circuit.ofCodes X.length gs) (inputState X.length X)).map List.ofFn := by
  have hvalid : ∀ j ∈ GateCode.targets gs, j < X.length :=
    fun _ hj => GateCode.lt_of_mem_targets hgs hj
  change (uniformList (hadamardCount gs)).map
    (restorePositions (GateCode.targets gs) X ∘
      fun seed => RankDecoder.decode (prefixGap gs X (GateCode.targets gs))
        (GateCode.targets gs).length [] (binaryValue seed)) = _
  rw [← PMF.map_comp, uniformList_decode_prefixGap hgs (GateCode.targets_nodup gs) hvalid]
  exact measure_map_restorePositions X hgs (GateCode.targets gs) (fun _ h => h)

/-- Sample exactly one fair bit per Hadamard gate, then deterministically decode the complete
output. These are the sampled seed bits; a native-machine realization may have unused transition
coins in deterministic phases. -/
@[expose] noncomputable def sampleOutput (gs : List GateCode) (X : List Bool) :
    ProbComp (List Bool) := do
  let seed ← sampleList (hadamardCount gs)
  return decodeOutput gs X seed

/-- Exact correctness of the sampler as a probabilistic program: its output law is the existing
joint computational-basis measurement, represented as a list of bits. -/
theorem eval_sampleOutput {gs : List GateCode} {X : List Bool}
    (hgs : ∀ g ∈ gs, g.WellFormed X.length) :
    ProbComp.eval (sampleOutput gs X) =
      (Circuit.measure (Circuit.ofCodes X.length gs) (inputState X.length X)).map List.ofFn := by
  simpa [sampleOutput, bind_pure_comp, ProbComp.eval_map] using uniformList_decodeOutput hgs

end Cslib.Complexity.QuantumContraction
