/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Quantum.Classical
public import Complexity.Computability.Circuit.Quantum.Parallel
public import Complexity.Computability.Circuit.Quantum.Uniform

/-!
# Uniform families of quantum verifiers

A quantum verifier reads, besides its input word, a **witness state** on some of its qubits
[Watrous][Watrous2008], Section V.1. A polynomial-time uniform family of verifiers
(`Cslib.Quantum.UniformVerifierFamily`) is a uniform family of circuits
(`Cslib.Quantum.UniformCircuitFamily`) with a witness length `witnessLength n`, computed from `n`
in unary in polynomial time. On an input word `x` of length `n` and a witness state `ψ` on
`witnessLength n` qubits, the circuit for inputs of length `n` starts in `|x⟩ ⊗ |ψ⟩ ⊗ |0 … 0⟩`:
the input on the qubits `0, …, n - 1`, the witness on the next `witnessLength n` qubits and zeros
on the rest. It accepts when the final measurement finds qubit `0` in state `1`
(`Cslib.Quantum.UniformVerifierFamily.acceptProb`).

The initial state is the embedding of `ψ` into the larger register
(`Cslib.Quantum.embedState`): the amplitude of a basis string is that of its bits on the witness
qubits, when its other bits are those of the classical input, and zero otherwise. On a basis
witness `|z⟩` this is the input state of the word `x ++ z`
(`Cslib.Quantum.UniformVerifierFamily.acceptProb_ket`).

Witnesses are pure states, as in [Marriott, Watrous][MarriottWatrous2005], Definition 3.1. Mixed
witnesses would give the same acceptance bounds: the acceptance probability is a quadratic form in
the witness, so a mixed witness accepts with a convex combination of the acceptance probabilities of
pure witnesses. This equivalence is not formalized here.

## Main definitions

* `Cslib.Quantum.embedState`: a state on some qubits of a register whose other qubits hold a
  basis string.
* `Cslib.Quantum.UniformVerifierFamily`: polynomial-time uniform families of quantum verifiers.
* `Cslib.Quantum.UniformVerifierFamily.acceptProb`: the acceptance probability on an input word and
  a witness state.
* `Cslib.Quantum.UniformVerifierFamily.ofCircuitFamily`: a uniform family of circuits as a
  verifier reading no witness.

## Main results

* `Cslib.Quantum.UniformVerifierFamily.acceptProb_ket`: on a basis witness, the verifier is its
  circuit run on the input word followed by the witness bits.
* `Cslib.Quantum.UniformVerifierFamily.acceptProb_smul`: the acceptance probability is homogeneous
  of degree two in the witness.
* `Cslib.Quantum.GateCode.classicalRun_glue`: classical codes away from some qubits commute with
  writing bits on them.

## References

* [J. Watrous, *Quantum computational complexity*][Watrous2008]
* [C. Marriott, J. Watrous, *Quantum Arthur–Merlin games*][MarriottWatrous2005]
-/

@[expose] public section

namespace Cslib.Quantum

open Finset Turing.MultiTapeTM

variable {ι : Type*} {p N : ℕ}

/-! ### Classical codes and glued bits -/

namespace GateCode

variable [Fintype ι]

/-- Bit `c` of `glue e z x`, off the qubits `e`, is bit `c` of `x`. -/
theorem readBit_glue_of_forall_ne (e : ι ↪ Fin N) (z : ι → Bool) (x : Fin N → Bool) {c : ℕ}
    (hc : ∀ i, (e i : ℕ) ≠ c) : readBit (glue e z x) c = readBit x c := by
  by_cases hcN : c < N
  · rw [readBit_of_lt _ hcN, readBit_of_lt _ hcN,
      glue_of_not _ _ _ fun i h => hc i (congrArg Fin.val h)]
  · rw [readBit_of_le _ (not_lt.mp hcN), readBit_of_le _ (not_lt.mp hcN)]

/-- **Classical codes that neither write nor read the qubits `e` commute with writing bits on
them.** -/
theorem classicalRun_glue {gs : List GateCode} (e : ι ↪ Fin N)
    (ht : ∀ g ∈ gs, ∀ i, (e i : ℕ) ≠ g.2.1) (hc : ∀ g ∈ gs, ∀ i, (e i : ℕ) ∉ g.2.2)
    (z : ι → Bool) (x : Fin N → Bool) :
    classicalRun gs (glue e z x) = glue e z (classicalRun gs x) := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [classicalRun_cons, classicalRun_cons,
      ← ih (fun g' hg' => ht g' (List.mem_cons_of_mem _ hg'))
      (fun g' hg' => hc g' (List.mem_cons_of_mem _ hg'))]
    congr 1
    have hall : g.2.2.all (readBit (glue e z x)) = g.2.2.all (readBit x) := by
      refine Bool.eq_iff_iff.mpr ?_
      simp only [List.all_eq_true]
      refine forall₂_congr fun c hc' => ?_
      rw [readBit_glue_of_forall_ne e z x fun i h =>
        hc g (List.mem_cons_self ..) i (h ▸ hc')]
    refine funext_readBit fun c => ?_
    rw [readBit_classicalStep, hall]
    by_cases hce : ∃ i, (e i : ℕ) = c
    · obtain ⟨i, rfl⟩ := hce
      rw [readBit_fin, readBit_fin, glue_apply_emb, glue_apply_emb]
      simp [ht g (List.mem_cons_self ..) i]
    · push Not at hce
      rw [readBit_glue_of_forall_ne e z x hce, readBit_glue_of_forall_ne e z _ hce,
        readBit_classicalStep]

end GateCode

/-! ### States on part of a register -/

/-- The state `ψ` on the qubits `e` of an `N`-qubit register whose other qubits hold `x`. -/
noncomputable def embedState (e : Fin p ↪ Fin N) (x : Fin N → Bool) : Qubits p →ₗᵢ[ℂ] Qubits N where
  toFun ψ := WithLp.toLp 2 fun y => if AgreeOff e y x then ψ.ofLp (y ∘ e) else 0
  map_add' ψ φ := by
    ext y
    simp only [WithLp.ofLp_add, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c ψ := by
    ext y
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp
  norm_map' ψ := by
    have h : ‖(WithLp.toLp 2 fun y => if AgreeOff e y x then ψ.ofLp (y ∘ e) else 0 :
        Qubits N)‖ ^ 2 = ‖ψ‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      simp only [apply_ite (‖·‖ ^ 2), norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow]
      exact sum_agreeOff_comp e x fun z => ‖ψ.ofLp z‖ ^ 2
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

theorem embedState_apply (e : Fin p ↪ Fin N) (x : Fin N → Bool) (ψ : Qubits p)
    (y : Fin N → Bool) :
    (embedState e x ψ).ofLp y = if AgreeOff e y x then ψ.ofLp (y ∘ e) else 0 :=
  rfl

/-- On a basis state, the embedding writes the basis string on the qubits `e`. -/
@[simp] theorem embedState_ket (e : Fin p ↪ Fin N) (x : Fin N → Bool) (z : Fin p → Bool) :
    embedState e x (ket z) = ket (glue e z x) := by
  ext y
  rw [embedState_apply, ket_apply, ket_apply]
  by_cases hy : AgreeOff e y x
  · simp only [hy, ↓reduceIte]
    refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
    · rw [← glue_comp_of_agreeOff hy, h]
    · rw [h, glue_comp]
  · simp only [hy, ↓reduceIte]
    refine (ite_eq_right_iff.mpr fun h => absurd ?_ hy).symm
    rw [h]
    exact agreeOff_glue e z x

theorem embedState_eq_sum (e : Fin p ↪ Fin N) (x : Fin N → Bool) (ψ : Qubits p) :
    embedState e x ψ = ∑ z, ψ.ofLp z • ket (glue e z x) := by
  conv_lhs => rw [← sum_smul_ket ψ]
  simp only [map_sum, map_smul, embedState_ket]

/-- A classical circuit mapping `|glue e z x⟩` to `|glue e' z x'⟩` for every `z` maps the state
`ψ` on the qubits `e` to `ψ` on the qubits `e'`. -/
theorem Circuit.eval_ofCodes_embedState {gs : List GateCode} (h : GateCode.IsClassical N gs)
    (e e' : Fin p ↪ Fin N) (x x' : Fin N → Bool)
    (hrun : ∀ z, GateCode.classicalRun gs (glue e z x) = glue e' z x') (ψ : Qubits p) :
    Circuit.eval (Circuit.ofCodes N gs) (embedState e x ψ) = embedState e' x' ψ := by
  rw [embedState_eq_sum, embedState_eq_sum, map_sum]
  simp only [map_smul, Circuit.eval_ofCodes_ket h, hrun]

/-- The first `n` qubits of a register hold `x` and the next `p` hold `z`: writing `z` on the block
after the input is the input state of `x ++ z`. -/
theorem glue_blockEmb_inputState {n m : ℕ} (h : n + p ≤ m) (x : List Bool) (hx : x.length = n)
    (z : Fin p → Bool) :
    glue (blockEmb n h) z (inputState m x) = inputState m (x ++ List.ofFn z) := by
  funext q
  by_cases hq : ∃ i, blockEmb n h i = q
  · obtain ⟨i, rfl⟩ := hq
    rw [glue_apply_emb, inputState, blockEmb_apply_val, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega)]
    simp [hx]
  · push Not at hq
    rw [glue_of_not _ _ _ hq, inputState, inputState, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD]
    by_cases hqn : (q : ℕ) < n
    · rw [List.getElem?_append_left (by omega)]
    · have : n + p ≤ q := by
        by_contra hlt
        exact hq ⟨q - n, by omega⟩ (Fin.ext (by simp; omega))
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

/-! ### Verifier families -/

/-- A **polynomial-time uniform family of quantum verifiers**: a uniform family of circuits that,
on inputs of length `n`, also reads a witness state of `witnessLength n` qubits on the qubits
`n, …, n + witnessLength n - 1`, right after the input. The witness length is computed from `n` in
unary in polynomial time. -/
structure UniformVerifierFamily extends UniformCircuitFamily where
  /-- The number of witness qubits on inputs of length `n`. -/
  witnessLength : ℕ → ℕ
  computableInPolyTime_witnessLength : ComputableInPolyTime witnessLength encUnary encUnary
  add_witnessLength_le : ∀ n, n + witnessLength n ≤ width n

namespace UniformVerifierFamily

variable (V : UniformVerifierFamily)

/-- The witness qubits `n, …, n + witnessLength n - 1` on inputs of length `n`. -/
def witnessQubits (n : ℕ) : Fin (V.witnessLength n) ↪ Fin (V.width n) :=
  blockEmb n (V.add_witnessLength_le n)

/-- The **acceptance probability** of the verifier on the input word `x` and the witness state
`ψ`: its circuit for inputs of length `|x|` runs on `x`, the witness `ψ` and zeros, and the final
measurement finds qubit `0` in state `1`. For a unit vector `ψ` this is a probability. -/
noncomputable def acceptProb (x : List Bool) (ψ : Qubits (V.witnessLength x.length)) : ℝ :=
  measureProb (Circuit.eval (Circuit.ofCodes (V.width x.length) (V.gates x.length))
    (embedState (V.witnessQubits x.length) (inputState (V.width x.length) x) ψ))
    (accepting (V.width x.length))

theorem acceptProb_nonneg (x : List Bool) (ψ : Qubits (V.witnessLength x.length)) :
    0 ≤ V.acceptProb x ψ :=
  measureProb_nonneg _ _

theorem acceptProb_le (x : List Bool) (ψ : Qubits (V.witnessLength x.length)) :
    V.acceptProb x ψ ≤ ‖ψ‖ ^ 2 := by
  refine (measureProb_le_measureProb_univ _ _).trans_eq ?_
  rw [measureProb_univ, LinearIsometryEquiv.norm_map, LinearIsometry.norm_map]

/-- The acceptance probability is homogeneous of degree two in the witness. -/
theorem acceptProb_smul (x : List Bool) (c : ℂ) (ψ : Qubits (V.witnessLength x.length)) :
    V.acceptProb x (c • ψ) = ‖c‖ ^ 2 * V.acceptProb x ψ := by
  rw [acceptProb, map_smul, map_smul, measureProb_smul, acceptProb]

/-- On a basis witness `|z⟩`, the verifier is its circuit run on the word `x ++ z`. -/
theorem acceptProb_ket (x : List Bool) (z : Fin (V.witnessLength x.length) → Bool) :
    V.acceptProb x (ket z) =
      Quantum.acceptProb (V.width x.length) (V.gates x.length) (x ++ List.ofFn z) := by
  rw [acceptProb, embedState_ket, witnessQubits, glue_blockEmb_inputState _ _ rfl]
  rfl

/-- The verifier accepts with probability zero on every witness state if it does on every basis
witness. -/
theorem acceptProb_eq_zero_of_forall_ket (x : List Bool) (h : ∀ z, V.acceptProb x (ket z) = 0)
    (ψ : Qubits (V.witnessLength x.length)) : V.acceptProb x ψ = 0 := by
  have hz (z) (y) (hy : y ∈ accepting (V.width x.length)) :
      (Circuit.eval (Circuit.ofCodes (V.width x.length) (V.gates x.length))
        (embedState (V.witnessQubits x.length) (inputState _ x) (ket z))).ofLp y = 0 := by
    have h' := h z
    rw [acceptProb, measureProb] at h'
    have := (sum_eq_zero_iff_of_nonneg fun y _ => by positivity).mp h' y hy
    simpa using this
  rw [acceptProb, measureProb]
  refine sum_eq_zero fun y hy => ?_
  rw [← sum_smul_ket ψ, map_sum, map_sum, WithLp.ofLp_sum, Finset.sum_apply]
  simp only [map_smul, WithLp.ofLp_smul, Pi.smul_apply, hz _ y hy, smul_zero, sum_const_zero,
    norm_zero]
  norm_num

/-- A uniform family of circuits as a verifier reading no witness. -/
def ofCircuitFamily (F : UniformCircuitFamily) : UniformVerifierFamily where
  toUniformCircuitFamily := F
  witnessLength _ := 0
  computableInPolyTime_witnessLength := ComputableInPolyTime.const _
  add_witnessLength_le n := F.le_width n

/-- A family reading no witness accepts as the circuit family does, scaled by the squared norm of
the (one-dimensional) witness. -/
theorem acceptProb_ofCircuitFamily (F : UniformCircuitFamily) (x : List Bool)
    (ψ : Qubits ((ofCircuitFamily F).witnessLength x.length)) :
    (ofCircuitFamily F).acceptProb x ψ = ‖ψ‖ ^ 2 * F.acceptProb x := by
  have : Subsingleton (Fin ((ofCircuitFamily F).witnessLength x.length) → Bool) :=
    inferInstanceAs (Subsingleton (Fin 0 → Bool))
  have hψ : ψ = ψ.ofLp default • ket default := by
    ext z
    rw [Subsingleton.elim z default]
    simp
  have h0 : List.ofFn (default : Fin ((ofCircuitFamily F).witnessLength x.length) → Bool) = [] :=
    List.eq_nil_of_length_eq_zero (by rw [List.length_ofFn]; rfl)
  rw [hψ, acceptProb_smul, acceptProb_ket, norm_smul, norm_ket, mul_one, h0, List.append_nil]
  rfl

/-- A verifier reading no witness qubits on inputs of length `|x|` accepts the (unique) basis
witness as its circuit family accepts `x`. -/
theorem acceptProb_ket_of_witnessLength_eq_zero (x : List Bool) (h : V.witnessLength x.length = 0)
    (z : Fin (V.witnessLength x.length) → Bool) :
    V.acceptProb x (ket z) = V.toUniformCircuitFamily.acceptProb x := by
  rw [acceptProb_ket, List.eq_nil_of_length_eq_zero (by simp [h] : (List.ofFn z).length = 0),
    List.append_nil]
  rfl

end UniformVerifierFamily

end Cslib.Quantum
