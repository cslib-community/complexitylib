/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Quantum
public import CslibFrontier.Crypto.Primitives.HQC.Syndrome
import CslibFrontier.Foundations.Data.BitString.Basic

/-!
# Native quantum HQC syndrome-decoding assumptions

The finite laws are exactly the parity-constrained distributions already formalized from
[HQC2026], Definitions 2.3.6--2.3.9, pp. 12--13. This module gives their tuples canonical
fixed-width word encodings and states that the real and comparison word ensembles are
indistinguishable to the native quantum tests of `Cslib.Crypto.NativeQuantum`.

For 2-DQCSD-P, a word contains the public circulant generator followed by the syndrome. Its
length is `2 * n`. For 3-DQCSD-PT, a word contains both public generators, the complete first
syndrome and the retained prefix of the second syndrome. If the source truncates `ell` final
coordinates, its length is `3 * n + (n - ell)`. `DQCSDParameters` enforces positive block length
and weight with `weight <= n`; `DQCSDTruncatedParameters` additionally enforces
`0 < ell < n`, as in the source problem family.

The source asks whether its samples came from the structured or comparison distribution with
non-negligible advantage. It does not define this repository's exact generated gate family,
initial state or measurement convention. `NativeQuantumTwoDQCSDP` and
`NativeQuantumThreeDQCSDPT` are therefore original, explicitly narrower quantum hardness
packaging over the exact source distributions. They are assumptions, not hardness theorems.
Primitive-prime admissibility, efficient sampling, public-seed expansion, QROM simulation,
decoding failures and HQC-PKE/KEM reductions remain separate obligations.

## Main definitions

* `Cslib.Crypto.HQC.DQCSDParameters`: positive block-length and fixed-weight schedules.
* `Cslib.Crypto.HQC.DQCSDTruncatedParameters`: additionally, a positive proper truncation.
* `Cslib.Crypto.HQC.SyndromeSample.toWord`: the canonical two-block word.
* `Cslib.Crypto.HQC.TruncatedSyndromeSample.toWord`: the canonical truncated three-block word.
* `Cslib.Crypto.HQC.NativeQuantumTwoDQCSDP`: native quantum 2-DQCSD-P hardness.
* `Cslib.Crypto.HQC.NativeQuantumThreeDQCSDPT`: native quantum 3-DQCSD-PT hardness.

## Main results

* `Cslib.Crypto.HQC.nativeQuantumTwoDQCSDPWithin_iff_indistinguishableWithin`,
  `Cslib.Crypto.HQC.nativeQuantumTwoDQCSDP_iff_computationallyIndistinguishable`: the
  source-named two-block predicates expose the shared native quantum interfaces.
* `Cslib.Crypto.HQC.nativeQuantumThreeDQCSDPTWithin_iff_indistinguishableWithin`,
  `Cslib.Crypto.HQC.nativeQuantumThreeDQCSDPT_iff_computationallyIndistinguishable`: the
  analogous truncated three-block interfaces.
* `Cslib.Crypto.HQC.NativeQuantumTwoDQCSDP.of_within`: concrete-to-asymptotic transfer.
* `Cslib.Crypto.HQC.NativeQuantumThreeDQCSDPT.of_within`: its truncated three-block analogue.

## References

* [HQC specification, version 5.1][HQC2026], Definitions 2.3.6--2.3.9, pp. 12--13.
-/

public section

namespace Cslib.Crypto.HQC

open scoped NNReal

open BitString
open Quantum

/-- Positive block-length and fixed-weight schedules from the source DQCSD problem families. -/
structure DQCSDParameters where
  /-- Ambient quasi-cyclic block length. -/
  blockLength : ℕ → ℕ
  /-- Hamming weight of every secret block. -/
  weight : ℕ → ℕ
  /-- Source problem instances have positive block length. -/
  blockLength_pos : ∀ κ, 0 < blockLength κ
  /-- Source problem instances have positive secret weight. -/
  weight_pos : ∀ κ, 0 < weight κ
  /-- A fixed-weight block fits in its ambient block. -/
  weight_le : ∀ κ, weight κ ≤ blockLength κ

/-- Source 3-DQCSD-PT parameters, where `truncation` final positions are removed. -/
structure DQCSDTruncatedParameters extends DQCSDParameters where
  /-- Number `ell` of final coordinates removed from the second syndrome. -/
  truncation : ℕ → ℕ
  /-- The source truncates at least one coordinate. -/
  truncation_pos : ∀ κ, 0 < truncation κ
  /-- A nonempty prefix remains after truncation. -/
  truncation_lt : ∀ κ, truncation κ < blockLength κ

instance (params : DQCSDParameters) (κ : ℕ) : NeZero (params.blockLength κ) :=
  ⟨(params.blockLength_pos κ).ne'⟩

instance (params : DQCSDTruncatedParameters) (κ : ℕ) :
    NeZero (params.blockLength κ) :=
  ⟨(params.blockLength_pos κ).ne'⟩

namespace SyndromeSample

/-- Serialize the public circulant generator followed by the complete syndrome. -/
@[expose] def toWord {n : ℕ} (sample : SyndromeSample n) : List Bool :=
  List.ofFn (Fin.append sample.publicBlock sample.value)

/-- The two-block encoding contains exactly two ambient blocks. -/
@[simp] theorem length_toWord {n : ℕ} (sample : SyndromeSample n) :
    sample.toWord.length = 2 * n := by
  simp [toWord]
  omega

/-- The fixed-width two-block encoding preserves the complete source tuple. -/
theorem toWord_injective {n : ℕ} : Function.Injective (@toWord n) := by
  intro a b h
  have hab : Fin.append a.publicBlock a.value = Fin.append b.publicBlock b.value :=
    List.ofFn_injective h
  have hpublic : a.publicBlock = b.publicBlock := by
    simpa using congrArg BitString.fstBits hab
  have hvalue : a.value = b.value := by
    simpa using congrArg BitString.sndBits hab
  cases a
  cases b
  simp_all

end SyndromeSample

namespace TruncatedSyndromeSample

/-- Serialize both public generators, the complete first syndrome and the retained prefix of the
second syndrome, in that order. -/
@[expose] def toWord {n m : ℕ} (sample : TruncatedSyndromeSample n m) : List Bool :=
  List.ofFn (Fin.append sample.firstBlock
    (Fin.append sample.secondBlock (Fin.append sample.firstValue sample.secondValue)))

/-- The truncated three-block encoding contains three ambient blocks and the retained prefix. -/
@[simp] theorem length_toWord {n m : ℕ} (sample : TruncatedSyndromeSample n m) :
    sample.toWord.length = 3 * n + m := by
  simp [toWord]
  omega

/-- The fixed-width truncated encoding preserves all four components of the source tuple. -/
theorem toWord_injective {n m : ℕ} : Function.Injective (@toWord n m) := by
  intro a b h
  have h₀ : Fin.append a.firstBlock
      (Fin.append a.secondBlock (Fin.append a.firstValue a.secondValue)) =
      Fin.append b.firstBlock
        (Fin.append b.secondBlock (Fin.append b.firstValue b.secondValue)) :=
    List.ofFn_injective h
  have hfirst : a.firstBlock = b.firstBlock := by
    simpa using congrArg BitString.fstBits h₀
  have hrest : Fin.append a.secondBlock (Fin.append a.firstValue a.secondValue) =
      Fin.append b.secondBlock (Fin.append b.firstValue b.secondValue) := by
    simpa using congrArg BitString.sndBits h₀
  have hsecond : a.secondBlock = b.secondBlock := by
    simpa using congrArg BitString.fstBits hrest
  have hvalues : Fin.append a.firstValue a.secondValue =
      Fin.append b.firstValue b.secondValue := by
    simpa using congrArg BitString.sndBits hrest
  have hfirstValue : a.firstValue = b.firstValue := by
    simpa using congrArg BitString.fstBits hvalues
  have hsecondValue : a.secondValue = b.secondValue := by
    simpa using congrArg BitString.sndBits hvalues
  cases a
  cases b
  simp_all

end TruncatedSyndromeSample

/-- Exact encoded length of a 2-DQCSD-P sample. -/
@[expose] def twoWordLength (params : DQCSDParameters) (κ : ℕ) : ℕ :=
  2 * params.blockLength κ

/-- Exact encoded length of a 3-DQCSD-PT sample after truncating `ell` final coordinates. -/
@[expose] def threeWordLength (params : DQCSDTruncatedParameters) (κ : ℕ) : ℕ :=
  3 * params.blockLength κ + (params.blockLength κ - params.truncation κ)

/-- Encoded 2-QCSD-P real ensemble from Definition 2.3.6. -/
@[expose] noncomputable def twoRealEnsemble (params : DQCSDParameters)
    (publicParity : ℕ → Bool) (κ : ℕ) : PMF (List Bool) :=
  (realSyndromeLaw (params.blockLength κ) (params.weight κ) (params.weight_le κ)
    (publicParity κ)).map SyndromeSample.toWord

/-- Encoded 2-DQCSD-P comparison ensemble from Definition 2.3.7. The syndrome parity is the
derived value `weight + publicParity * weight mod 2`. -/
@[expose] noncomputable def twoUniformEnsemble (params : DQCSDParameters)
    (publicParity : ℕ → Bool) (κ : ℕ) : PMF (List Bool) :=
  (uniformSyndromeLaw (params.blockLength κ) (params.weight κ)
    (publicParity κ)).map SyndromeSample.toWord

/-- Encoded 3-QCSD-PT real ensemble from Definition 2.3.8. The retained second component is the
prefix of length `n - ell`, and both syndromes use the same third secret block. -/
@[expose] noncomputable def threeRealEnsemble (params : DQCSDTruncatedParameters)
    (firstParity secondParity : ℕ → Bool) (κ : ℕ) : PMF (List Bool) :=
  (realTruncatedSyndromeLaw (params.blockLength κ)
    (params.blockLength κ - params.truncation κ) (params.weight κ) (Nat.sub_le _ _)
    (params.weight_le κ) (firstParity κ) (secondParity κ)).map
      TruncatedSyndromeSample.toWord

/-- Encoded 3-DQCSD-PT comparison ensemble from Definition 2.3.9. The first syndrome keeps its
derived parity, while the retained second component is independent and uniform. -/
@[expose] noncomputable def threeUniformEnsemble (params : DQCSDTruncatedParameters)
    (firstParity secondParity : ℕ → Bool) (κ : ℕ) : PMF (List Bool) :=
  (uniformTruncatedSyndromeLaw (params.blockLength κ)
    (params.blockLength κ - params.truncation κ) (params.weight κ)
    (firstParity κ) (secondParity κ)).map TruncatedSyndromeSample.toWord

/-- Every encoded real 2-QCSD-P sample has the exact declared word length. -/
theorem supportsLength_twoRealEnsemble (params : DQCSDParameters)
    (publicParity : ℕ → Bool) :
    NativeQuantum.SupportsLength (twoRealEnsemble params publicParity)
      (twoWordLength params) := by
  intro κ word hword
  obtain ⟨sample, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hword
  exact (SyndromeSample.length_toWord sample).le

/-- Every encoded comparison 2-DQCSD-P sample has the exact declared word length. -/
theorem supportsLength_twoUniformEnsemble (params : DQCSDParameters)
    (publicParity : ℕ → Bool) :
    NativeQuantum.SupportsLength (twoUniformEnsemble params publicParity)
      (twoWordLength params) := by
  intro κ word hword
  obtain ⟨sample, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hword
  exact (SyndromeSample.length_toWord sample).le

/-- Every encoded real 3-QCSD-PT sample has the exact declared word length. -/
theorem supportsLength_threeRealEnsemble (params : DQCSDTruncatedParameters)
    (firstParity secondParity : ℕ → Bool) :
    NativeQuantum.SupportsLength (threeRealEnsemble params firstParity secondParity)
      (threeWordLength params) := by
  intro κ word hword
  obtain ⟨sample, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hword
  exact (TruncatedSyndromeSample.length_toWord sample).le

/-- Every encoded comparison 3-DQCSD-PT sample has the exact declared word length. -/
theorem supportsLength_threeUniformEnsemble (params : DQCSDTruncatedParameters)
    (firstParity secondParity : ℕ → Bool) :
    NativeQuantum.SupportsLength (threeUniformEnsemble params firstParity secondParity)
      (threeWordLength params) := by
  intro κ word hword
  obtain ⟨sample, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hword
  exact (TruncatedSyndromeSample.length_toWord sample).le

/-- Concrete native quantum 2-DQCSD-P security with exact sample lengths and separate circuit
resource budgets. -/
def NativeQuantumTwoDQCSDPWithin (params : DQCSDParameters) (publicParity : ℕ → Bool)
    (ε : ℕ → OracleCircuit.Resources → ℝ≥0) : Prop :=
  NativeQuantum.IndistinguishableWithin (twoRealEnsemble params publicParity)
    (twoUniformEnsemble params publicParity) (twoWordLength params) ε

/-- The source-named concrete two-block assumption is exactly the shared native quantum
indistinguishability interface. -/
theorem nativeQuantumTwoDQCSDPWithin_iff_indistinguishableWithin
    (params : DQCSDParameters) (publicParity : ℕ → Bool)
    (ε : ℕ → OracleCircuit.Resources → ℝ≥0) :
    NativeQuantumTwoDQCSDPWithin params publicParity ε ↔
      NativeQuantum.IndistinguishableWithin (twoRealEnsemble params publicParity)
        (twoUniformEnsemble params publicParity) (twoWordLength params) ε :=
  Iff.rfl

/-- Native quantum 2-DQCSD-P hardness for the exact source distributions. This is an assumption
under the repository's no-advice, no-useful-oracle native test convention. -/
def NativeQuantumTwoDQCSDP (params : DQCSDParameters) (publicParity : ℕ → Bool) : Prop :=
  NativeQuantum.ComputationallyIndistinguishable (twoRealEnsemble params publicParity)
    (twoUniformEnsemble params publicParity)

/-- The source-named asymptotic two-block assumption is exactly the shared native quantum
computational-indistinguishability interface. -/
theorem nativeQuantumTwoDQCSDP_iff_computationallyIndistinguishable
    (params : DQCSDParameters) (publicParity : ℕ → Bool) :
    NativeQuantumTwoDQCSDP params publicParity ↔
      NativeQuantum.ComputationallyIndistinguishable
        (twoRealEnsemble params publicParity) (twoUniformEnsemble params publicParity) :=
  Iff.rfl

/-- A concrete bound negligible along every polynomial circuit-resource schedule implies native
quantum 2-DQCSD-P hardness when the ambient block length is polynomially bounded. -/
theorem NativeQuantumTwoDQCSDP.of_within {params : DQCSDParameters}
    {publicParity : ℕ → Bool} {ε : ℕ → OracleCircuit.Resources → ℝ≥0}
    (h : NativeQuantumTwoDQCSDPWithin params publicParity ε)
    (hn : PolynomiallyBounded params.blockLength)
    (hneg : ∀ qubits gates queries : ℕ → ℕ,
      PolynomiallyBounded qubits → PolynomiallyBounded gates → PolynomiallyBounded queries →
      Negligible (fun κ => ε κ ⟨qubits κ, gates κ, queries κ⟩)) :
    NativeQuantumTwoDQCSDP params publicParity := by
  apply NativeQuantum.ComputationallyIndistinguishable.of_within h
    (supportsLength_twoRealEnsemble params publicParity)
    (supportsLength_twoUniformEnsemble params publicParity) _ hneg
  change PolynomiallyBounded (fun κ => 2 * params.blockLength κ)
  exact (PolynomiallyBounded.const 2).mul hn

/-- Concrete native quantum 3-DQCSD-PT security with exact sample lengths and separate circuit
resource budgets. -/
def NativeQuantumThreeDQCSDPTWithin (params : DQCSDTruncatedParameters)
    (firstParity secondParity : ℕ → Bool) (ε : ℕ → OracleCircuit.Resources → ℝ≥0) : Prop :=
  NativeQuantum.IndistinguishableWithin (threeRealEnsemble params firstParity secondParity)
    (threeUniformEnsemble params firstParity secondParity) (threeWordLength params) ε

/-- The source-named concrete truncated three-block assumption is exactly the shared native
quantum indistinguishability interface. -/
theorem nativeQuantumThreeDQCSDPTWithin_iff_indistinguishableWithin
    (params : DQCSDTruncatedParameters) (firstParity secondParity : ℕ → Bool)
    (ε : ℕ → OracleCircuit.Resources → ℝ≥0) :
    NativeQuantumThreeDQCSDPTWithin params firstParity secondParity ε ↔
      NativeQuantum.IndistinguishableWithin
        (threeRealEnsemble params firstParity secondParity)
        (threeUniformEnsemble params firstParity secondParity) (threeWordLength params) ε :=
  Iff.rfl

/-- Native quantum 3-DQCSD-PT hardness for the exact source distributions. This is an assumption
under the repository's no-advice, no-useful-oracle native test convention. -/
def NativeQuantumThreeDQCSDPT (params : DQCSDTruncatedParameters)
    (firstParity secondParity : ℕ → Bool) : Prop :=
  NativeQuantum.ComputationallyIndistinguishable
    (threeRealEnsemble params firstParity secondParity)
    (threeUniformEnsemble params firstParity secondParity)

/-- The source-named asymptotic truncated three-block assumption is exactly the shared native
quantum computational-indistinguishability interface. -/
theorem nativeQuantumThreeDQCSDPT_iff_computationallyIndistinguishable
    (params : DQCSDTruncatedParameters) (firstParity secondParity : ℕ → Bool) :
    NativeQuantumThreeDQCSDPT params firstParity secondParity ↔
      NativeQuantum.ComputationallyIndistinguishable
        (threeRealEnsemble params firstParity secondParity)
        (threeUniformEnsemble params firstParity secondParity) :=
  Iff.rfl

/-- A concrete bound negligible along every polynomial circuit-resource schedule implies native
quantum 3-DQCSD-PT hardness when the ambient block length is polynomially bounded. -/
theorem NativeQuantumThreeDQCSDPT.of_within {params : DQCSDTruncatedParameters}
    {firstParity secondParity : ℕ → Bool}
    {ε : ℕ → OracleCircuit.Resources → ℝ≥0}
    (h : NativeQuantumThreeDQCSDPTWithin params firstParity secondParity ε)
    (hn : PolynomiallyBounded params.blockLength)
    (hneg : ∀ qubits gates queries : ℕ → ℕ,
      PolynomiallyBounded qubits → PolynomiallyBounded gates → PolynomiallyBounded queries →
      Negligible (fun κ => ε κ ⟨qubits κ, gates κ, queries κ⟩)) :
    NativeQuantumThreeDQCSDPT params firstParity secondParity := by
  apply NativeQuantum.ComputationallyIndistinguishable.of_within h
    (supportsLength_threeRealEnsemble params firstParity secondParity)
    (supportsLength_threeUniformEnsemble params firstParity secondParity) _ hneg
  change PolynomiallyBounded
    (fun κ => 3 * params.blockLength κ +
      (params.blockLength κ - params.truncation κ))
  apply ((PolynomiallyBounded.const 4).mul hn).mono_of_le
  intro κ
  calc
    3 * params.blockLength κ + (params.blockLength κ - params.truncation κ) ≤
        3 * params.blockLength κ + params.blockLength κ :=
      Nat.add_le_add_left (Nat.sub_le _ _) _
    _ = 4 * params.blockLength κ := by omega

end Cslib.Crypto.HQC
