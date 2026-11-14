/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Formula
public import CslibFrontier.Computability.Circuit.Pi
public import CslibFrontier.Computability.Circuit.Quantum.Reversible.Sampling.Resources
public import CslibFrontier.Crypto.Primitives.HQC.SupportCircuit.Resolve
public import CslibFrontier.Crypto.Primitives.HQC.SupportProbability
public import CslibFrontier.Foundations.Data.BitString.Support.Weight

/-!
# Native circuit sampler for HQC supports

This module composes the existing multiply-high candidate circuit and descending collision circuit,
then turns the corrected word array into the indicator vector used by HQC. Under `count ≤ n` and
`n < 2 ^ bits`, applying the generic reversible sampler gives a native elementary quantum circuit
whose measured output law is exactly `sampleSupport2` mapped through
`BitString.indicatorVector`.

The finite-width law retains the source algorithm's non-dyadic bias. There is no abort branch:
under `count ≤ n` and `n < 2 ^ bits`, every output has weight `count`, while the statistical
discrepancy from the ideal fixed-weight law is bounded by
`1 - (supportLowerDensity width n 0 count).toReal`. The online qubit, gate, query, and encoded-code
bounds below do not charge the offline generator program or replace the separate XOF analysis.

## Main definitions

* `Cslib.Crypto.HQC.supportIndicatorCircuit`: membership bits of a corrected word array.
* `Cslib.Crypto.HQC.supportSamplerCircuit`: candidates, collision correction, and indicator output.
* `Cslib.Crypto.HQC.nonDyadicSupportCircuit`: the concrete `width = 1`, `n = 3`, `count = 2`
  specialization used to expose a nonzero collision.

## Main results

The semantic and distributional results below assume `count ≤ n` and `n < 2 ^ bits`.

* `Cslib.Crypto.HQC.eval_supportSamplerCircuit`: exact deterministic circuit semantics.
* `Cslib.Crypto.HQC.samplerDist_supportSamplerCircuit`: exact measured `sampleSupport2` law.
* `Cslib.Crypto.HQC.weight_eval_supportSamplerCircuit`: every output has the requested weight.
* `Cslib.Crypto.HQC.supportSamplerDist_closeTo_ideal`: finite-width discrepancy with no abort term.
* `Cslib.Crypto.HQC.supportSamplerWidth`, `Cslib.Crypto.HQC.length_supportSamplerCodes_le`,
  `Cslib.Crypto.HQC.within_supportSamplerCodes`,
  `Cslib.Crypto.HQC.length_encoding_supportSamplerCodes_le`: instantiated online resources.
* `Cslib.Crypto.HQC.eval_nonDyadicSupportCircuit_collision`: two raw candidates equal to `1` are
  corrected to the support `{0, 1}`.

## References

* [HQC specification, version 5.1][HQC2026], `SampleSupport2`, p. 19, and §6.2.3.
* [J. Watrous, *Quantum computational complexity*][Watrous2008], Section IV.3.
-/

public section

namespace Cslib.Crypto.HQC

open Finset Probability Circuits Circuits.Boolean BitString
open Quantum GateCode Quantum.Reversible Turing.MultiTapeTM

/-- Test whether corrected word `j` is the `bits`-bit representation of `value`. -/
@[expose] def supportWordFormula (bits count value : ℕ) (j : Fin count) :
    Formula signature (count * bits) :=
  Formula.andList (List.ofFn fun k : Fin bits =>
    Formula.literal (fun _ => value.testBit k.val) (finProdFinEquiv (j, k)))

/-- Test whether some corrected word equals `value`. Empty arrays give the constant `false`. -/
@[expose] def supportIndicatorFormula (bits count value : ℕ) :
    Formula signature (count * bits) :=
  Formula.orList (List.ofFn (supportWordFormula bits count value))

/-- Convert the corrected word array into the indicator of its values in `range n`. -/
@[expose] def supportIndicatorCircuit (bits n count : ℕ) :
    Circuit signature (count * bits) n :=
  Circuit.pi fun i => (supportIndicatorFormula bits count i.val).toCircuit

/-- A word-equality formula agrees with `equivFin` when the requested value fits in the word. -/
theorem eval_supportWordFormula {bits count value : ℕ} (hvalue : value < 2 ^ bits)
    (j : Fin count) (x : BitString (count * bits)) :
    (supportWordFormula bits count value j).eval interpretation x =
      decide ((equivFin bits (block x j) : ℕ) = value) := by
  rw [Bool.eq_iff_iff]
  simp only [supportWordFormula, Formula.eval_andList, List.all_eq_true,
    List.forall_mem_ofFn_iff, Formula.eval_literal, beq_iff_eq, decide_eq_true_eq]
  let valueFin : Fin (2 ^ bits) := ⟨value, hvalue⟩
  have hbits : (fun k : Fin bits => value.testBit k.val) =
      (equivFin bits).symm valueFin := by
    funext k
    exact (equivFin_symm_apply valueFin k).symm
  constructor
  · intro h
    have hx : block x j = (equivFin bits).symm valueFin := by
      rw [← hbits]
      funext k
      exact h k
    have := congrArg (equivFin bits) hx
    simpa only [Equiv.apply_symm_apply, valueFin] using congrArg Fin.val this
  · intro h
    have hx : block x j = (equivFin bits).symm valueFin := by
      apply (equivFin bits).injective
      exact Fin.ext h
    intro k
    rw [hx, ← hbits]

/-- The indicator circuit returns the finite set of values represented by the corrected words. -/
theorem eval_supportIndicatorCircuit {bits n count : ℕ} (hn : n ≤ 2 ^ bits)
    (x : BitString (count * bits)) :
    (supportIndicatorCircuit bits n count).eval interpretation x =
      indicatorVector n
        ((List.ofFn fun j => (equivFin bits (block x j) : ℕ)).toFinset) := by
  funext i
  rw [Bool.eq_iff_iff]
  simp only [supportIndicatorCircuit, Circuit.eval_pi, Formula.eval_toCircuit,
    supportIndicatorFormula, Formula.eval_orList, List.any_eq_true, indicatorVector_apply,
    decide_eq_true_eq, List.mem_toFinset]
  constructor
  · rintro ⟨F, hF, hFx⟩
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hF
    rw [eval_supportWordFormula (i.isLt.trans_le hn), decide_eq_true_eq] at hFx
    exact List.mem_ofFn.mpr ⟨j, hFx⟩
  · intro hi
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hi
    refine ⟨supportWordFormula bits count i.val j, List.mem_ofFn.mpr ⟨j, rfl⟩, ?_⟩
    rw [eval_supportWordFormula (i.isLt.trans_le hn), decide_eq_true_eq]
    exact hj

/-- Compute all multiply-high candidates independently on consecutive fair-word blocks. -/
@[expose] def supportCandidateCircuit (width bits n count : ℕ) :
    Circuit signature (count * width) (count * bits) :=
  Circuit.parallelFamily fun j => candidateCircuit width bits n j.val

/-- Each candidate block is the corresponding source multiply-high value. -/
theorem val_block_eval_supportCandidateCircuit {width bits n count : ℕ}
    (hcount : count ≤ n) (hn : n < 2 ^ bits) (x : BitString (count * width)) :
    (fun j => (equivFin bits (block
      ((supportCandidateCircuit width bits n count).eval interpretation x) j) : ℕ)) =
      fun j => j.val + (equivFin width (block x j) : ℕ) * (n - j.val) / 2 ^ width := by
  funext j
  simp only [supportCandidateCircuit, block_apply, Circuit.eval_parallelFamily_apply]
  exact val_eval_candidateCircuit (j.isLt.trans_le hcount) hn (block x j)

/-- The complete Boolean sampler: multiply-high candidates, descending collision correction, and
the `n`-bit indicator of the corrected support. -/
@[expose] def supportSamplerCircuit (width bits n count : ℕ) :
    Circuit signature (count * width) n :=
  (supportIndicatorCircuit bits n count).comp
    ((supportScanCircuit bits 0 count).comp
      (supportCandidateCircuit width bits n count))

/-- The native Boolean circuit implements the deterministic word-array form of `SampleSupport2`. -/
theorem eval_supportSamplerCircuit {width bits n count : ℕ} (hcount : count ≤ n)
    (hn : n < 2 ^ bits) (x : BitString (count * width)) :
    (supportSamplerCircuit width bits n count).eval interpretation x =
      indicatorVector n (supportFromWords width n
        (fun j => equivFin width (block x j))) := by
  have hscan := val_eval_supportScanCircuit (bits := bits) (offset := 0) (count := count)
    (show count ≤ 2 ^ bits by omega)
    (block ((supportCandidateCircuit width bits n count).eval interpretation x))
  have hcandidates := val_block_eval_supportCandidateCircuit hcount hn x
  simp only [Nat.zero_add, blocksEquiv_symm_block] at hscan
  rw [supportSamplerCircuit, Circuit.eval_comp, Circuit.eval_comp,
    eval_supportIndicatorCircuit hn.le, hscan, toFinset_scanSupport, supportFromWords,
    hcandidates]

/-- Uniform seed bits are equivalent to an independent array of bounded source words. -/
def supportSeedEquiv (width count : ℕ) :
    BitString (count * width) ≃ (Fin count → Fin (2 ^ width)) :=
  (blocksEquiv (m := count) (k := width) (α := Bool)).trans
    (Equiv.piCongrRight fun _ => equivFin width)

@[simp] theorem supportSeedEquiv_apply (width count : ℕ) (x : BitString (count * width)) :
    supportSeedEquiv width count x = fun j => equivFin width (block x j) := by
  funext j
  simp [supportSeedEquiv]

/-- Measuring the native reversible sampler gives exactly `sampleSupport2`, represented by its
`n`-bit indicator. No extra approximation or abort event is introduced. -/
theorem samplerDist_supportSamplerCircuit {width bits n count : ℕ} (hcount : count ≤ n)
    (hn : n < 2 ^ bits) :
    samplerDist (supportSamplerCircuit width bits n count) =
      (ProbComp.eval (sampleSupport2 width n count)).map (indicatorVector n) := by
  rw [samplerDist_eq_outputDist, Circuit.outputDist, eval_sampleSupport2, PMF.map_comp,
    ← Probability.PMF.uniformOfFintype_map_equiv (supportSeedEquiv width count), PMF.map_comp]
  congr 1 with x : 1
  simpa only [Function.comp_apply, supportSeedEquiv_apply] using
    eval_supportSamplerCircuit hcount hn x

/-- Every Boolean and measured basis output has the requested weight; finite-width bias changes
probabilities, not the support cardinality. -/
theorem weight_eval_supportSamplerCircuit {width bits n count : ℕ} (hcount : count ≤ n)
    (hn : n < 2 ^ bits) (x : BitString (count * width)) :
    weight ((supportSamplerCircuit width bits n count).eval interpretation x) = count := by
  rw [eval_supportSamplerCircuit hcount hn]
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp
    (supportFromWords_mem_powersetCard hcount
      (fun j => equivFin width (block x j)))
  rw [weight_indicatorVector hsub, hcard]

/-- The measured circuit inherits the existing finite-width discrepancy bound. This is a
statistical error term, not an abort probability. -/
theorem supportSamplerDist_closeTo_ideal {width bits n count : ℕ} (hcount : count ≤ n)
    (hn : n < 2 ^ bits) :
    CloseTo (samplerDist (supportSamplerCircuit width bits n count))
      ((PMF.uniformOfFinset ((range n).powersetCard count)
        (powersetCard_nonempty.mpr (by simpa only [card_range] using hcount))).map
          (indicatorVector n))
      (ENNReal.ofReal (1 - (supportLowerDensity width n 0 count).toReal)) := by
  rw [samplerDist_supportSamplerCircuit hcount hn]
  exact (sampleSupport2_closeTo hcount).map (indicatorVector n)

/-! ### Instantiated online resources -/

/-- Active qubits are the fair seeds, all Boolean gate values, one zero, and the output block. -/
theorem supportSamplerWidth (width bits n count : ℕ) :
    samplerWidth (count * width) (supportSamplerCircuit width bits n count).code =
      count * width + (supportSamplerCircuit width bits n count).size + 1 + n :=
  samplerWidth_circuit _

/-- The reversible realization uses at most three elementary classical gates per Boolean gate,
besides one Hadamard per seed and one CNOT per output. -/
theorem length_supportSamplerCodes_le (width bits n count : ℕ) :
    (samplerCodes (count * width) (supportSamplerCircuit width bits n count).code).length ≤
      count * width + 3 * (supportSamplerCircuit width bits n count).size + n := by
  simpa [Circuit.code] using
    length_samplerCodes_le (count * width) (supportSamplerCircuit width bits n count).code

/-- The native sampler has the exact active width, the construction-derived gate budget, and no
coherent oracle queries. -/
theorem within_supportSamplerCodes (width bits n count : ℕ) :
    OracleCircuit.Within
      ((samplerCodes (count * width) (supportSamplerCircuit width bits n count).code).map
        fun g => OracleGateCode.gate (false, g))
      (count * width + (supportSamplerCircuit width bits n count).size + 1 + n)
      ⟨count * width + (supportSamplerCircuit width bits n count).size + 1 + n,
        count * width + 3 * (supportSamplerCircuit width bits n count).size + n, 0⟩ := by
  simpa [Circuit.code, samplerWidth_circuit] using
    within_samplerCodes (count * width) (supportSamplerCircuit width bits n count).code

/-- Encoded instruction length, including unary wire indices and list framing. -/
theorem length_encoding_supportSamplerCodes_le (width bits n count : ℕ) :
    (encList encGateCode
      (samplerCodes (count * width) (supportSamplerCircuit width bits n count).code)).length ≤
      (count * width + 3 * (supportSamplerCircuit width bits n count).size + n) *
        (12 * (count * width + (supportSamplerCircuit width bits n count).size + 1 + n) + 1) := by
  simpa [Circuit.code, samplerWidth_circuit] using
    length_encoding_samplerCodes_le (count * width)
      (supportSamplerCircuit width bits n count).code

/-! ### Non-dyadic collision and boundary cases -/

/-- A small non-dyadic specialization: two one-bit words sample a support of size two in a
three-element universe, using two-bit corrected positions. -/
def nonDyadicSupportCircuit : Circuit signature 2 3 :=
  supportSamplerCircuit 1 2 3 2

/-- Words producing the duplicate nonzero raw candidate array `(1, 1)`. -/
def nonDyadicCollisionWords : Fin 2 → Fin 2 := fun j => if j = 0 then 1 else 0

/-- The corresponding two fair seed bits. -/
def nonDyadicCollisionSeed : BitString 2 :=
  blocksEquiv.symm fun j => (equivFin 1).symm (nonDyadicCollisionWords j)

/-- Both source candidate formulas return the nonzero value `1`. -/
theorem nonDyadicCollisionWords_candidates :
    (fun j : Fin 2 => j.val + (nonDyadicCollisionWords j).val * (3 - j.val) / 2 ^ 1) =
      fun _ => 1 := by
  decide

/-- The descending collision rule replaces the first duplicate `1` by its offset `0`. -/
theorem supportFromWords_nonDyadicCollision :
    supportFromWords 1 3 nonDyadicCollisionWords = {0, 1} := by
  decide

/-- The concrete circuit exposes a genuine nonzero collision correction, from raw candidates
`(1, 1)` to the fixed-weight output support `{0, 1}`. -/
theorem eval_nonDyadicSupportCircuit_collision :
    nonDyadicSupportCircuit.eval interpretation nonDyadicCollisionSeed =
      indicatorVector 3 {0, 1} := by
  rw [nonDyadicSupportCircuit, eval_supportSamplerCircuit (by decide) (by decide)]
  have hseed : (fun j => equivFin 1 (block nonDyadicCollisionSeed j)) =
      nonDyadicCollisionWords := by
    funext j
    simp [nonDyadicCollisionSeed]
  rw [hseed, supportFromWords_nonDyadicCollision]

/-- Exact measured law of the concrete non-dyadic client. -/
theorem samplerDist_nonDyadicSupportCircuit :
    samplerDist nonDyadicSupportCircuit =
      (ProbComp.eval (sampleSupport2 1 3 2)).map (indicatorVector 3) := by
  exact samplerDist_supportSamplerCircuit (by decide) (by decide)

/-- The concrete client's discrepancy from the ideal three-point fixed-weight law is the existing
finite-width density complement, with no abort term. -/
theorem nonDyadicSupportCircuit_closeTo_ideal :
    CloseTo (samplerDist nonDyadicSupportCircuit)
      ((PMF.uniformOfFinset ((range 3).powersetCard 2)
        (powersetCard_nonempty.mpr (by decide))).map (indicatorVector 3))
      (ENNReal.ofReal (1 - (supportLowerDensity 1 3 0 2).toReal)) := by
  simpa [nonDyadicSupportCircuit] using
    supportSamplerDist_closeTo_ideal (width := 1) (bits := 2) (n := 3) (count := 2)
      (by decide) (by decide)

/-- The concrete non-dyadic client has fixed output weight two. -/
theorem weight_eval_nonDyadicSupportCircuit (x : BitString 2) :
    weight (nonDyadicSupportCircuit.eval interpretation x) = 2 := by
  exact weight_eval_supportSamplerCircuit (by decide) (by decide) x

/-- Exact active width of the concrete non-dyadic client. -/
theorem nonDyadicSupportCircuit_width :
    samplerWidth 2 nonDyadicSupportCircuit.code =
      2 + nonDyadicSupportCircuit.size + 1 + 3 := by
  simpa [nonDyadicSupportCircuit] using supportSamplerWidth 1 2 3 2

/-- Construction-derived elementary-gate bound for the concrete non-dyadic client. -/
theorem length_nonDyadicSupportCodes_le :
    (samplerCodes 2 nonDyadicSupportCircuit.code).length ≤
      2 + 3 * nonDyadicSupportCircuit.size + 3 := by
  simpa [nonDyadicSupportCircuit] using length_supportSamplerCodes_le 1 2 3 2

/-- The concrete non-dyadic client uses no coherent oracle queries. -/
theorem within_nonDyadicSupportCodes :
    OracleCircuit.Within
      ((samplerCodes 2 nonDyadicSupportCircuit.code).map
        fun g => OracleGateCode.gate (false, g))
      (2 + nonDyadicSupportCircuit.size + 1 + 3)
      ⟨2 + nonDyadicSupportCircuit.size + 1 + 3,
        2 + 3 * nonDyadicSupportCircuit.size + 3, 0⟩ := by
  simpa [nonDyadicSupportCircuit] using within_supportSamplerCodes 1 2 3 2

/-- Encoded instruction-length bound for the concrete non-dyadic client. -/
theorem length_encoding_nonDyadicSupportCodes_le :
    (encList encGateCode (samplerCodes 2 nonDyadicSupportCircuit.code)).length ≤
      (2 + 3 * nonDyadicSupportCircuit.size + 3) *
        (12 * (2 + nonDyadicSupportCircuit.size + 1 + 3) + 1) := by
  simpa [nonDyadicSupportCircuit] using length_encoding_supportSamplerCodes_le 1 2 3 2

/-- Zero requested positions produce the all-zero indicator, with no random or abort branch. -/
theorem eval_supportSamplerCircuit_zero_count {width bits n : ℕ} (hn : n < 2 ^ bits)
    (x : BitString (0 * width)) :
    (supportSamplerCircuit width bits n 0).eval interpretation x = fun _ => false := by
  rw [eval_supportSamplerCircuit (Nat.zero_le n) hn]
  simp [supportFromWords, resolveSupport, indicatorVector]

/-- The empty universe and empty requested support give the unique empty bit string. -/
theorem eval_supportSamplerCircuit_zero_universe (width bits : ℕ) (x : BitString 0) :
    (supportSamplerCircuit width bits 0 0).eval interpretation x = fun _ => false := by
  funext i
  exact i.elim0

/-- At full requested weight, every seed produces the all-one indicator of the universe. -/
theorem eval_supportSamplerCircuit_full {width bits n : ℕ} (hn : n < 2 ^ bits)
    (x : BitString (n * width)) :
    (supportSamplerCircuit width bits n n).eval interpretation x = fun _ => true := by
  rw [eval_supportSamplerCircuit le_rfl hn, supportFromWords_full]
  funext i
  simp [indicatorVector]

/-- The full-support edge case remains exact with zero-bit source words. -/
theorem eval_supportSamplerCircuit_zero_width_full {bits n : ℕ} (hn : n < 2 ^ bits)
    (x : BitString 0) :
    (supportSamplerCircuit 0 bits n n).eval interpretation x = fun _ => true := by
  simpa using eval_supportSamplerCircuit_full (width := 0) hn x

end Cslib.Crypto.HQC
