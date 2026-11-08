/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.QMA.Amplification
import CslibFrontier.Computability.Complexity.Classes.QMA.NP
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontierTests.BQP

/-! `QMA`: a verifier whose answer depends on the witness, a language in `QMA` through it, error
reduction, the containments `NP ⊆ QMA` and `BQP ⊆ QMA`, and the amplified verifier on basis
witnesses. -/

namespace ComplexityTests.QMA

open Cslib Cslib.Quantum Cslib.Complexity Turing.MultiTapeTM
open ComplexityTests.BQP

/-! ### A verifier that reads its witness -/

/-- The verifier with one witness qubit right after the input and no gates: on the empty input it
measures the witness qubit, and otherwise the first input bit. -/
def readWitness : UniformVerifierFamily where
  width n := n + 1
  gates _ := []
  computableInPolyTime_width := by fun_prop
  computableInPolyTime_gates := ComputableInPolyTime.const _
  le_width n := Nat.le_succ n
  width_pos n := Nat.succ_pos n
  wellFormed _ _ h := by simp at h
  witnessLength _ := 1
  computableInPolyTime_witnessLength := ComputableInPolyTime.const _
  add_witnessLength_le _ := le_rfl

/-- On a basis witness `|z⟩`, `readWitness` reads the first bit of `x ++ z`. -/
theorem acceptProb_readWitness_ket (x : List Bool)
    (z : Fin (readWitness.witnessLength x.length) → Bool) :
    readWitness.acceptProb x (ket z) = if (x ++ List.ofFn z).headD false then 1 else 0 := by
  rw [UniformVerifierFamily.acceptProb_ket]
  change measureProb (Circuit.run (Circuit.ofCodes (x.length + 1) []) (inputState _ _))
    (accepting _) = _
  simp only [Circuit.ofCodes_nil, Circuit.run, Circuit.eval_nil, measureProb_ket,
    mem_accepting (Nat.succ_pos _), inputState]
  cases x <;> rfl

-- The answer depends on the witness: on the empty input, `|1⟩` is accepted with certainty and
-- `|0⟩` never.
example : readWitness.acceptProb [] (ket fun _ => true) = 1 := by
  rw [acceptProb_readWitness_ket]
  rfl
example : readWitness.acceptProb [] (ket fun _ => false) = 0 := by
  rw [acceptProb_readWitness_ket]
  rfl

/-- The words that are empty or start with one. -/
def HeadOrEmpty : Set (List Bool) := {x | x.headD true = true}

/-- `readWitness` decides `HeadOrEmpty` with perfect completeness and soundness `0`: the empty word
is a member only through its witness `|1⟩`. -/
theorem headOrEmpty_mem_PromiseQMA :
    PromiseProblem.ofSet HeadOrEmpty ∈ PromiseQMA (fun _ => 1) (fun _ => 0) encBits := by
  refine ⟨readWitness, fun x => ⟨fun hx => ⟨ket fun _ => true, norm_ket _, ?_⟩, fun hx ψ _ => ?_⟩⟩
  · rw [acceptProb_readWitness_ket]
    change x.headD true = true at hx
    cases x with
    | nil => rfl
    | cons b x =>
      change b = true at hx
      simp [encBits_apply, hx]
  · refine le_of_eq (UniformVerifierFamily.acceptProb_eq_zero_of_forall_ket _ _ (fun z => ?_) ψ)
    rw [acceptProb_readWitness_ket]
    change ¬x.headD true = true at hx
    cases x with
    | nil => exact absurd rfl hx
    | cons b x =>
      change ¬b = true at hx
      simp [encBits_apply, hx]

theorem headOrEmpty_mem_QMA : HeadOrEmpty ∈ QMA encBits :=
  PromiseQMA_mono (fun _ => by norm_num) (fun _ => by norm_num) headOrEmpty_mem_PromiseQMA

-- Error reduction: completeness `1 - 2^{-q(n)}` and soundness `2^{-q(n)}` for every polynomial `q`.
example (q : Polynomial ℕ) : PromiseProblem.ofSet HeadOrEmpty ∈
    PromiseQMA (fun n => 1 - ((2 : ℝ) ^ q.eval n)⁻¹) (fun n => ((2 : ℝ) ^ q.eval n)⁻¹) encBits :=
  mem_QMA_iff_forall_errorExponent.mp headOrEmpty_mem_QMA q

/-! ### Containments -/

private theorem head_mem_NP : {w : List Bool | w.headD false = true} ∈ NP encBits :=
  ⟨0, fun x => x.1.headD false, by fun_prop, fun _ => by simp⟩

-- `NP ⊆ QMA`, with perfect completeness and soundness `0` for promise problems.
example : {w : List Bool | w.headD false = true} ∈ QMA encBits := NP_subset_QMA head_mem_NP
example : PromiseProblem.ofSet {w : List Bool | w.headD false = true} ∈
    PromiseQMA (fun _ => 1) (fun _ => 0) encBits :=
  PromiseNP_subset_PromiseQMA (ofSet_mem_PromiseNP.mpr head_mem_NP)

-- `BQP ⊆ QMA`.
example : FirstBit ∈ QMA encBits := BQP_subset_QMA firstBit_mem_BQP

/-! ### The amplified verifier -/

-- Two copies of `readWitness` on the empty input, each reading one witness block: the strict
-- majority of the two copies accepts the basis witness `|11⟩` with certainty and rejects `|10⟩`.
example : (readWitness.amplify (fun _ => 1) (ComputableInPolyTime.const _)).acceptProb []
    (ket fun _ : Fin ((readWitness.amplify (fun _ => 1) _).witnessLength 0) => true) = 1 := by
  rw [UniformVerifierFamily.acceptProb_ket]
  change measureProb (Circuit.run (Circuit.ofCodes 16 (QMAAmplify.codes 0 1 3 1 []))
    (inputState 16 [true, true])) (accepting 16) = 1
  rw [Circuit.run_ofCodes (by unfold GateCode.IsClassical; decide), measureProb_ket,
    ite_eq_left ((mem_accepting (by norm_num)).mpr (by decide))]
example : (readWitness.amplify (fun _ => 1) (ComputableInPolyTime.const _)).acceptProb []
    (ket fun i : Fin ((readWitness.amplify (fun _ => 1) _).witnessLength 0) =>
      decide (i.val = 0)) = 0 := by
  rw [UniformVerifierFamily.acceptProb_ket]
  change measureProb (Circuit.run (Circuit.ofCodes 16 (QMAAmplify.codes 0 1 3 1 []))
    (inputState 16 [true, false])) (accepting 16) = 0
  rw [Circuit.run_ofCodes (by unfold GateCode.IsClassical; decide), measureProb_ket,
    ite_eq_right ((mem_accepting (by norm_num)).not.mpr (by decide))]

end ComplexityTests.QMA
