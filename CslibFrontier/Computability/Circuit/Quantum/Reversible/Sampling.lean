/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.OutputDistribution
public import CslibFrontier.Computability.Circuit.Quantum.HadamardLayer
public import CslibFrontier.Computability.Circuit.Quantum.Reversible
public import CslibFrontier.Foundations.Quantum.Measurement.Readout
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Probability.PMF.Expect

/-!
# Reversible quantum realization of Boolean samplers

A De Morgan circuit on `n` input bits is a sampler when its inputs are fair coins. This module
realizes that sampler as an elementary quantum circuit: put Hadamard gates on `n` zero qubits,
compile the Boolean gate list with `Cslib.Quantum.Reversible.codes`, retain the seed and compiler
garbage, and copy every Boolean output into a fresh declared output block. A single final
computational-basis measurement reads that block.

The construction is exact relative to the Boolean circuit's output distribution. In particular,
it introduces no additional abort or approximation: non-dyadic error, collisions, and fixed-weight
guarantees remain properties of the Boolean sampler supplied by a client. Concrete instruction,
qubit, measurement and encoded-description costs are kept separate from the static generator
program and its offline running time.

## Main definitions

* `Cslib.Quantum.Reversible.outputCopyCodes`: CNOT gates copying Boolean output wires into a fresh
  consecutive block.
* `Cslib.Quantum.Reversible.samplerCodes`: the Hadamard preparation, reversible compilation and
  output copy.
* `Cslib.Quantum.Reversible.samplerDist`: the distribution read from the copied output block after
  one final measurement.

## Main results

* `Cslib.Quantum.Reversible.wellFormed_samplerCodes`: every emitted elementary gate is valid for
  the declared width.
* `Cslib.Quantum.Reversible.samplerDist_eq_outputDist`: the measured quantum distribution is
  exactly the Boolean circuit's distribution on uniform inputs.
* `Cslib.Quantum.Reversible.computableInPolyTime_samplerCodes`: the native gate-code generator is
  polynomial time when the Boolean circuit code is.

## References

* [J. Watrous, *Quantum computational complexity*][Watrous2008], Section IV.3.
-/

public section

namespace Cslib.Quantum.Reversible

open Circuits Circuits.Boolean GateCode Turing.MultiTapeTM
open scoped BigOperators ENNReal

/-- CNOT gates copying the listed Boolean output wires into fresh qubits starting at `base`.
Output `j` reads `outQubit z outputs[j]`, so an invalid wire reads the compiler's zero qubit. -/
@[expose] def outputCopyCodes (z base : ℕ) (outputs : List ℕ) : List GateCode :=
  outputs.zipIdx.map fun p => (false, base + p.2, [outQubit z p.1])

/-- The compiler's zero qubit. -/
@[expose] def samplerZero (n : ℕ) (code : List (Op × List ℕ) × List ℕ) : ℕ :=
  n + code.1.length

/-- The first qubit of the copied output block. -/
@[expose] def samplerOutputStart (n : ℕ) (code : List (Op × List ℕ) × List ℕ) : ℕ :=
  samplerZero n code + 1

/-- The complete register width: seeds, Boolean gates, a zero qubit, and copied outputs. -/
@[expose] def samplerWidth (n : ℕ) (code : List (Op × List ℕ) × List ℕ) : ℕ :=
  samplerOutputStart n code + code.2.length

/-- The classical suffix of the sampler: reversible Boolean evaluation followed by output copy. -/
@[expose] def samplerClassicalCodes (n : ℕ)
    (code : List (Op × List ℕ) × List ℕ) : List GateCode :=
  codes n (samplerZero n code) code.1 ++
    outputCopyCodes (samplerZero n code) (samplerOutputStart n code) code.2

/-- The elementary quantum sampler: fair seed preparation, reversible Boolean evaluation, and
copying every declared output to a fresh block. -/
@[expose] def samplerCodes (n : ℕ)
    (code : List (Op × List ℕ) × List ℕ) : List GateCode :=
  hadamardCodes 0 n ++ samplerClassicalCodes n code

/-- Read the copied output block of a typed Boolean circuit from a measured basis string. -/
@[expose] def samplerReadout {n m : ℕ} (C : Circuits.Circuit signature n m)
    (X : Fin (samplerWidth n C.code) → Bool) : BitString m :=
  fun j => readBit X (samplerOutputStart n C.code + j)

/-- The measured output distribution of the reversible realization, started with every qubit
zero. The construction performs one final computational-basis measurement and reads only the
fresh copied output block. -/
noncomputable def samplerDist {n m : ℕ} (C : Circuits.Circuit signature n m) :
    PMF (BitString m) :=
  let Q := Circuit.ofCodes (samplerWidth n C.code) (samplerCodes n C.code)
  measureOut (Circuit.run Q (inputState (samplerWidth n C.code) []))
    (Circuit.norm_run Q _) (samplerReadout C)

@[simp] theorem length_outputCopyCodes (z base : ℕ) (outputs : List ℕ) :
    (outputCopyCodes z base outputs).length = outputs.length := by
  simp [outputCopyCodes]

/-- Every copied-output CNOT is classical and well formed when the target block follows `z` and
fits in the register. -/
theorem isClassical_outputCopyCodes {W z base : ℕ} {outputs : List ℕ} (hzb : z < base)
    (hW : base + outputs.length ≤ W) : IsClassical W (outputCopyCodes z base outputs) := by
  intro g hg
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
  have hi : p.2 < outputs.length := (List.mem_zipIdx hp).2.1
  have hout : outQubit z p.1 ≤ z := by unfold outQubit; omega
  refine ⟨rfl, by simp, ?_, ?_⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
      not_false_eq_true, and_true]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    omega

/-- The classical suffix is well formed for the sampler's declared width. -/
theorem isClassical_samplerClassicalCodes (n : ℕ)
    (code : List (Op × List ℕ) × List ℕ) :
    IsClassical (samplerWidth n code) (samplerClassicalCodes n code) := by
  unfold samplerClassicalCodes
  refine IsClassical.append.mpr ⟨isClassical_codes le_rfl (by
    unfold samplerWidth samplerOutputStart samplerZero
    omega), ?_⟩
  exact isClassical_outputCopyCodes (by unfold samplerOutputStart; omega) (by rfl)

/-- A Hadamard layer whose target block fits in the register consists of well-formed gates. -/
theorem wellFormed_hadamardCodes {W o p : ℕ} (hW : o + p ≤ W) :
    ∀ g ∈ hadamardCodes o p, g.WellFormed W := by
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
  have hj := List.mem_range.mp hj
  simp only [WellFormed, and_true]
  omega

/-- Every gate emitted by the reversible sampler is valid for its declared register width. -/
theorem wellFormed_samplerCodes (n : ℕ) (code : List (Op × List ℕ) × List ℕ) :
    ∀ g ∈ samplerCodes n code, g.WellFormed (samplerWidth n code) := by
  intro g hg
  rw [samplerCodes] at hg
  rcases List.mem_append.mp hg with hg | hg
  · exact wellFormed_hadamardCodes (by unfold samplerWidth samplerOutputStart samplerZero; omega)
      g hg
  · exact (isClassical_samplerClassicalCodes n code g hg).2

@[simp] theorem length_samplerCodes (n : ℕ) (code : List (Op × List ℕ) × List ℕ) :
    (samplerCodes n code).length =
      n + (codes n (samplerZero n code) code.1).length + code.2.length := by
  simp [samplerCodes, samplerClassicalCodes, hadamardCodes]

/-! ### Classical correctness -/

/-- Copying an output block writes source `outputs[j]` into target `base + j`, provided the target
block starts after every possible source and is initially zero. -/
theorem readBit_classicalRun_outputCopyCodes {W z base : ℕ} {outputs : List ℕ}
    (hzb : z < base) (hW : base + outputs.length ≤ W) (X : Fin W → Bool)
    (hX : ∀ j < outputs.length, readBit X (base + j) = false) {j : ℕ}
    (hj : j < outputs.length) :
    readBit (classicalRun (outputCopyCodes z base outputs) X) (base + j) =
      readBit X (outQubit z (outputs.getD j 0)) := by
  have hclass := isClassical_outputCopyCodes (W := W) hzb hW
  have hlt : ∀ g ∈ outputCopyCodes z base outputs, g.2.1 < W := by
    intro g hg
    obtain ⟨b, t, cs⟩ := g
    obtain ⟨hb, hg'⟩ := hclass (b, t, cs) hg
    subst b
    exact hg'.2.2 t (List.mem_cons_self ..)
  have hnd : ((outputCopyCodes z base outputs).map fun g => g.2.1).Nodup := by
    have hshift : ((outputs.zipIdx.map Prod.snd).map fun i => base + i).Nodup :=
      (List.nodup_zipIdx_map_snd outputs).map fun i j h => by omega
    simpa only [outputCopyCodes, List.map_map, Function.comp_apply] using hshift
  have hread : ∀ g ∈ outputCopyCodes z base outputs,
      ∀ g' ∈ outputCopyCodes z base outputs, g.2.1 ∉ g'.2.2 := by
    intro g hg g' hg'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
    obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hg'
    have hout : outQubit z p'.1 ≤ z := by unfold outQubit; omega
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hmem : ((false, base + j, [outQubit z (outputs.getD j 0)]) : GateCode) ∈
      outputCopyCodes z base outputs := by
    rw [outputCopyCodes, List.mem_map]
    refine ⟨(outputs[j], j), List.mem_zipIdx_iff_getElem?.mpr ?_, ?_⟩
    · rw [List.getElem?_eq_getElem hj]
    · simp [List.getD_eq_getElem?_getD, hj]
  simpa [hX j hj] using
    (readBit_classicalRun_of_mem hlt hnd hread X hmem)

/-- **Basis-state correctness of the classical suffix**: on a seed `x` followed by zero ancillas,
the copied output block is exactly the output of the typed Boolean circuit. -/
theorem samplerReadout_classicalRun {n m : ℕ} (C : Circuits.Circuit signature n m)
    (x : BitString n) :
    samplerReadout C (classicalRun (samplerClassicalCodes n C.code)
      (inputState (samplerWidth n C.code) (List.ofFn x))) = C.eval interpretation x := by
  let W := samplerWidth n C.code
  let z := samplerZero n C.code
  let base := samplerOutputStart n C.code
  let X₀ := inputState W (List.ofFn x)
  let X₁ := classicalRun (codes n z C.code.1) X₀
  have hx : (List.ofFn x).length = n := List.length_ofFn
  have hzW : z < W := by
    dsimp only [W, z]
    unfold samplerWidth samplerOutputStart samplerZero
    omega
  have hX₀ (p : ℕ) : readBit X₀ p = (List.ofFn x).getD p false := by
    exact readBit_inputState (by
      dsimp only [W]
      unfold samplerWidth samplerOutputStart samplerZero
      omega) p
  have hcodes (p : ℕ) : readBit X₁ p =
      (evalCode interpretation false (List.ofFn x) C.code.1).getD p false := by
    exact readBit_classicalRun_codes le_rfl hzW hx hX₀ p
  have hzero (j : ℕ) (hj : j < C.code.2.length) : readBit X₁ (base + j) = false := by
    rw [hcodes]
    apply List.getD_eq_default
    have hlen : (evalCode interpretation false (List.ofFn x) C.code.1).length = z := by
      simp [hx, z, samplerZero]
    rw [hlen]
    dsimp only [base, z]
    unfold samplerOutputStart samplerZero
    omega
  funext j
  change readBit (classicalRun (samplerClassicalCodes n C.code) X₀) (base + j) =
    C.eval interpretation x j
  rw [samplerClassicalCodes, classicalRun_append]
  change readBit (classicalRun (outputCopyCodes z base C.code.2) X₁) (base + j) = _
  rw [readBit_classicalRun_outputCopyCodes (by
      dsimp only [base, z]
      unfold samplerOutputStart
      omega) (by
      dsimp only [W, base]
      unfold samplerWidth
      rfl) X₁ hzero (by simpa [Circuit.code] using j.isLt)]
  have hout : C.code.2.getD j.val 0 = (C.outputs j).toNat := by
    simp [Circuit.code, List.getD_eq_getElem?_getD]
  rw [hout, outQubit, min_eq_right (C.outputs j).toNat_lt.le, hcodes,
    Circuit.eval_eq_evalOutput]
  rfl

/-! ### Exact output law -/

/-- **Exact fair-seed realization**: measuring the copied output block of the reversible quantum
sampler gives exactly the output distribution of the Boolean circuit on uniform inputs. The
classical suffix only permutes basis states, so seed branches cannot interfere. -/
theorem samplerDist_eq_outputDist {n m : ℕ} (C : Circuits.Circuit signature n m) :
    samplerDist C = C.outputDist interpretation := by
  classical
  let W := samplerWidth n C.code
  let X₀ : Fin W → Bool := inputState W []
  let X : BitString n → Fin W → Bool := fun r => inputState W (List.ofFn r)
  let s : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
  let U : Qubits W →ₗᵢ[ℂ] Qubits W :=
    (Circuit.eval (Circuit.ofCodes W (samplerClassicalCodes n C.code))).toLinearIsometry
  have hnW : n ≤ W := by
    dsimp only [W]
    unfold samplerWidth samplerOutputStart samplerZero
    omega
  have hX (r : BitString n) : X r = glue (blockEmb 0 hnW) r X₀ := by
    dsimp only [X, X₀]
    rw [glue_blockEmb_inputState hnW [] rfl]
    rfl
  have hXinj : Function.Injective X := by
    intro r r' h
    rw [hX, hX] at h
    have := congrArg (· ∘ blockEmb 0 hnW) h
    simpa using this
  have hv : Orthonormal ℂ fun r => ket (X r) :=
    (EuclideanSpace.orthonormal_single (𝕜 := ℂ)).comp X hXinj
  have hX₀ (i : Fin n) : X₀ (blockEmb 0 hnW i) = false := by
    simp [X₀, inputState]
  have hstate :
      Circuit.run (Circuit.ofCodes W (samplerCodes n C.code)) X₀ =
        U (∑ r : BitString n, s ^ n • ket (X r)) := by
    rw [Circuit.run, samplerCodes, Circuit.ofCodes_append, Circuit.eval_append,
      eval_hadamardCodes_ket hnW X₀ hX₀]
    simp_rw [← hX]
    rfl
  have hbasis (r : BitString n) :
      U (ket (X r)) = ket (classicalRun (samplerClassicalCodes n C.code) (X r)) := by
    change Circuit.eval (Circuit.ofCodes W (samplerClassicalCodes n C.code)) (ket (X r)) = _
    exact Circuit.eval_ofCodes_ket (isClassical_samplerClassicalCodes n C.code) (X r)
  have hyr (y : BitString m) (r : BitString n) :
      measureProb (U (ket (X r))) {a | samplerReadout C a = y} =
        if C.eval interpretation r = y then 1 else 0 := by
    rw [hbasis, measureProb_ket]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show samplerReadout C
        (classicalRun (samplerClassicalCodes n C.code) (X r)) = C.eval interpretation r by
      simpa only [X, W] using samplerReadout_classicalRun C r]
  have hprob (y : BitString m) :
      measureProb (Circuit.run (Circuit.ofCodes W (samplerCodes n C.code)) X₀)
          {a | samplerReadout C a = y} =
        (Finset.dens {r : BitString n | C.eval interpretation r = y} : ℝ) := by
    rw [hstate]
    have key := measureProb_map_sum_orthonormal U hv (fun _ : BitString n => s ^ n)
      {a | samplerReadout C a = y} (fun r => C.eval interpretation r = y)
      (fun r h => by rw [hyr y r, if_pos h])
      (fun r h => by rw [hyr y r, if_neg h])
    rw [key]
    have hs : ‖s ^ n‖ ^ 2 = 1 / 2 ^ n := by
      rw [norm_pow, ← pow_mul, mul_comm, pow_mul, Complex.norm_real, Real.norm_eq_abs,
        sq_abs, inv_pow, Real.sq_sqrt (by norm_num), one_div, inv_pow]
    simp only [hs, Finset.sum_const, nsmul_eq_mul, Finset.dens_eq_card_div_card,
      NNRat.cast_div, NNRat.cast_natCast, Fintype.card_fun, Fintype.card_bool, Nat.cast_pow,
      Nat.cast_ofNat, div_eq_mul_inv]
    ring
  apply PMF.ext
  intro y
  rw [← ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
  change (measureOut (Circuit.run (Circuit.ofCodes W (samplerCodes n C.code)) X₀)
      (Circuit.norm_run _ _) (samplerReadout C) y).toReal =
    ((C.outputDist interpretation) y).toReal
  rw [measureOut_eq_ofReal_measureProb, ENNReal.toReal_ofReal (measureProb_nonneg _ _), hprob,
    Circuit.outputDist, Probability.PMF.toReal_uniformOfFintype_map_apply]

variable {γ : Type} {enc : γ ↪ List Bool}

/-- Output-copy code generation is polynomial time in the unary block positions and binary output
wire list. -/
theorem computableInPolyTime_outputCopyCodes {z base : γ → ℕ} {outputs : γ → List ℕ}
    (hz : ComputableInPolyTime z enc encUnary)
    (hbase : ComputableInPolyTime base enc encUnary)
    (houtputs : ComputableInPolyTime outputs enc (encList encNat)) :
    ComputableInPolyTime (fun a => outputCopyCodes (z a) (base a) (outputs a)) enc
      (encList encGateCode) := by
  unfold outputCopyCodes outQubit
  fun_prop

theorem computableInPolyTime_samplerWidth {n : γ → ℕ}
    {code : γ → List (Op × List ℕ) × List ℕ}
    (hn : ComputableInPolyTime n enc encUnary)
    (hcode : ComputableInPolyTime code enc encCode) :
    ComputableInPolyTime (fun a => samplerWidth (n a) (code a)) enc encUnary := by
  unfold samplerWidth samplerOutputStart samplerZero
  fun_prop

/-- The complete fair-seed reversible sampler is generated in polynomial time from the input arity
and Boolean circuit code. This is an offline generator certificate, not an online execution-time
or static generator-program-size bound. -/
theorem computableInPolyTime_samplerCodes {n : γ → ℕ}
    {code : γ → List (Op × List ℕ) × List ℕ}
    (hn : ComputableInPolyTime n enc encUnary)
    (hcode : ComputableInPolyTime code enc encCode) :
    ComputableInPolyTime (fun a => samplerCodes (n a) (code a)) enc
      (encList encGateCode) := by
  have hzero : ComputableInPolyTime (fun a => samplerZero (n a) (code a)) enc encUnary := by
    unfold samplerZero
    fun_prop
  have hstart : ComputableInPolyTime (fun a => samplerOutputStart (n a) (code a)) enc
      encUnary := by
    unfold samplerOutputStart
    fun_prop
  have hcompile := computableInPolyTime_codes hn hzero
    (gates := fun a => (code a).1) (by fun_prop)
  have hcopy := computableInPolyTime_outputCopyCodes hzero hstart
    (outputs := fun a => (code a).2) (by fun_prop)
  have hhad := computableInPolyTime_hadamardCodes (o := fun _ => 0) (p := n)
    (by fun_prop) hn
  unfold samplerCodes samplerClassicalCodes
  fun_prop

end Cslib.Quantum.Reversible
