/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.QMA.MA
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! The quantum verifier of a Merlin–Arthur verifier: a basis proof is accepted with its classical
acceptance probability, a superposition of proofs with the weighted average, and the containments
`MA ⊆ QMA` and `BPP ⊆ BQP` on a concrete language. -/

namespace CslibFrontierTests.QMAMA

open Cslib Cslib.Quantum Cslib.Complexity Finset Turing.MultiTapeTM

/-! ### A layer of Hadamard gates -/

-- One Hadamard gate on the zero qubit of a one-qubit register gives `(|0⟩ + |1⟩) / √2`.
example : Circuit.eval (Circuit.ofCodes 1 (hadamardCodes 0 1)) (ket fun _ => false) =
    ∑ r : Fin 1 → Bool, (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ 1 •
      ket (glue (blockEmb 0 (le_refl 1)) r fun _ => false) :=
  eval_hadamardCodes_ket (le_refl 1) _ fun _ => rfl

/-! ### A verifier with a one-bit proof and one coin -/

/-- Accept when both the proof bit and the coin are one: the proof `1` is accepted with probability
`1 / 2` and the proof `0` never. -/
def andCoin : List Bool × List Bool → Bool := fun x => x.2.headD false && x.2.tail.headD false

theorem computableInPolyTime_andCoin :
    ComputableInPolyTime andCoin (encPair encBits encBits) encBool := by
  unfold andCoin
  fun_prop

/-- The exact quantum simulation of `andCoin`
(from `Cslib.Complexity.exists_uniformCircuitFamily`). -/
noncomputable def andCoinFamily : UniformCircuitFamily :=
  (exists_uniformCircuitFamily computableInPolyTime_andCoin).choose

theorem acceptProb_andCoinFamily (w : List Bool) :
    andCoinFamily.acceptProb (frame [] ++ w) = if andCoin ([], w) then 1 else 0 :=
  (exists_uniformCircuitFamily computableInPolyTime_andCoin).choose_spec ([], w)

/-- The quantum verifier of `andCoin`, with a one-qubit proof and one coin. -/
noncomputable abbrev andCoinVerifier : UniformVerifierFamily :=
  UniformVerifierFamily.ofMA andCoinFamily 1 1

/-- On the empty input, only the proof `1` is accepted, and only by the coin `1`. -/
private theorem card_andCoin {m : ℕ} (hm : m = 1) (y : Fin m → Bool) :
    (univ.filter fun r : Fin m → Bool => andCoin ([], List.ofFn y ++ List.ofFn r)).card =
      if y = fun _ => true then 1 else 0 := by
  subst hm
  revert y
  decide

private theorem eval_one_nil : (1 : Polynomial ℕ).eval ([] : List Bool).length = 1 :=
  Polynomial.eval_one

private theorem two_pow_eval_one_nil :
    (2 : ℝ) ^ (1 : Polynomial ℕ).eval ([] : List Bool).length = 2 := by
  rw [eval_one_nil, pow_one]

-- The proof `1` is accepted with probability exactly `1 / 2`: the coin is fair.
example : andCoinVerifier.acceptProb []
    (ket (fun _ => true : Fin ((1 : Polynomial ℕ).eval ([] : List Bool).length) → Bool)) =
      1 / 2 := by
  refine (UniformVerifierFamily.acceptProb_ofMA_ket andCoinFamily 1 1 [] (fun w => andCoin ([], w))
    (fun w _ => acceptProb_andCoinFamily w) _).trans ?_
  rw [card_andCoin eval_one_nil, ite_eq_left rfl, two_pow_eval_one_nil, Nat.cast_one]

-- The proof `0` is never accepted.
example : andCoinVerifier.acceptProb []
    (ket (fun _ => false : Fin ((1 : Polynomial ℕ).eval ([] : List Bool).length) → Bool)) = 0 := by
  refine (UniformVerifierFamily.acceptProb_ofMA_ket andCoinFamily 1 1 [] (fun w => andCoin ([], w))
    (fun w _ => acceptProb_andCoinFamily w) _).trans ?_
  rw [card_andCoin eval_one_nil, ite_eq_right fun h => by simpa using congrFun h ⟨0, by simp⟩,
    Nat.cast_zero, zero_div]

-- Every unit witness state, including every superposition of the two proofs, is accepted with
-- probability at most `1 / 2`.
example (ψ : Qubits (andCoinVerifier.witnessLength 0)) (hψ : ‖ψ‖ = 1) :
    andCoinVerifier.acceptProb [] ψ ≤ 1 / 2 := by
  refine UniformVerifierFamily.acceptProb_ofMA_le andCoinFamily 1 1 [] (fun w => andCoin ([], w))
    (fun w _ => acceptProb_andCoinFamily w) (fun y => ?_) ψ hψ
  rw [card_andCoin eval_one_nil, two_pow_eval_one_nil]
  split_ifs <;> norm_num

/-- On one qubit, the equal superposition of the two basis states has weight `1 / 2` on each. -/
private theorem norm_sq_plus {m : ℕ} (hm : m = 1) (y : Fin m → Bool) :
    ‖((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ket (fun _ => false) + ket (fun _ => true)) :
      Qubits m).ofLp y‖ ^ 2 = 1 / 2 := by
  subst hm
  have h1 : (ket (fun _ => false) + ket (fun _ => true) : Qubits 1).ofLp y = 1 := by
    rw [show y = fun _ => y 0 from funext fun i => by rw [Subsingleton.elim i 0]]
    generalize y 0 = b
    cases b <;> simp [funext_iff]
  rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, h1, mul_one, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (by norm_num), one_div]

/-- Weight `1 / 2` on each proof, and acceptance `1 / 2` on the proof `1` only. -/
private theorem sum_half_indicator {m : ℕ} (hm : m = 1) :
    ∑ y : Fin m → Bool, (1 / 2 : ℝ) * (((if y = fun _ => true then 1 else 0 : ℕ) : ℝ) / 2) =
      1 / 4 := by
  subst hm
  rw [Fintype.sum_eq_single (fun _ => true) fun y hy => by simp [hy]]
  norm_num

-- The equal superposition `(|0⟩ + |1⟩) / √2` of the two proofs is accepted with probability
-- exactly `1 / 4`, the average of `0` and `1 / 2` with weights `1 / 2`: no interference.
example : andCoinVerifier.acceptProb []
    ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ket (fun _ => false) + ket (fun _ => true)) :
      Qubits ((1 : Polynomial ℕ).eval ([] : List Bool).length)) = 1 / 4 := by
  refine (UniformVerifierFamily.acceptProb_ofMA andCoinFamily 1 1 [] (fun w => andCoin ([], w))
    (fun w _ => acceptProb_andCoinFamily w) _).trans ?_
  calc _ = ∑ y : Fin ((1 : Polynomial ℕ).eval ([] : List Bool).length) → Bool,
        (1 / 2 : ℝ) * (((if y = fun _ => true then 1 else 0 : ℕ) : ℝ) / 2) :=
        sum_congr rfl fun y _ => by
          rw [norm_sq_plus eval_one_nil, card_andCoin eval_one_nil, two_pow_eval_one_nil]
    _ = 1 / 4 := sum_half_indicator eval_one_nil

/-! ### The containments -/

private theorem head_mem_P : {w : List Bool | w.headD false = true} ∈ P encBits :=
  ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩

-- `MA ⊆ QMA` and `BPP ⊆ BQP`.
example : {w : List Bool | w.headD false = true} ∈ QMA encBits :=
  MA_subset_QMA (BPP_subset_MA (P_subset_BPP head_mem_P))
example : {w : List Bool | w.headD false = true} ∈ BQP encBits :=
  BPP_subset_BQP (P_subset_BPP head_mem_P)

end CslibFrontierTests.QMAMA
