/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Classical
public import CslibFrontier.Computability.Circuit.Quantum.Parallel

/-!
# Quantum states embedded in larger input registers

`Cslib.Quantum.embedState` places a state on selected qubits of a larger register and fixes the
remaining qubits to a basis string. It is a linear isometry: superpositions and norms are preserved.
On a basis state it writes the basis string on the selected qubits. Any state is the corresponding
linear combination of those embedded basis states.

Running a circuit on the selected qubits commutes with this embedding
(`Cslib.Quantum.Circuit.eval_mapWires_embedState`), leaving the other qubits fixed.
Classical reversible circuits can move the embedded state by acting on each basis string
(`Cslib.Quantum.Circuit.eval_ofCodes_embedState`). Codes that avoid its qubits commute with writing
bits there (`Cslib.Quantum.GateCode.classicalRun_glue`). For a contiguous block following a
classical input, writing a basis string agrees with initializing the concatenated input word
(`Cslib.Quantum.glue_blockEmb_inputState`).

## Main definitions

* `Cslib.Quantum.embedState`: a state on selected qubits with a fixed basis string elsewhere.

## Main results

* `Cslib.Quantum.ofFn_inputState`: the input basis state is the input word padded with zeros.
* `Cslib.Quantum.embedState_ket`: embedding a basis state writes its bits on the selected qubits.
* `Cslib.Quantum.embedState_eq_sum`: the expansion in embedded basis states.
* `Cslib.Quantum.Circuit.eval_mapWires_embedState`: running a circuit on the selected qubits
  commutes with embedding its input state.
* `Cslib.Quantum.Circuit.eval_ofCodes_embedState`: a classical circuit transports an embedded state
  according to its action on basis states.
* `Cslib.Quantum.GateCode.classicalRun_glue`: classical codes away from selected qubits commute
  with writing bits on them.
* `Cslib.Quantum.glue_blockEmb_inputState`: initializing a block after the input concatenates words.
-/

public section

namespace Cslib.Quantum

open Finset

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
@[expose]
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

/-- Running a circuit on selected qubits commutes with embedding its input state; the other
qubits retain their fixed basis string. -/
theorem Circuit.eval_mapWires_embedState (C : Circuit p) (e : Fin p ↪ Fin N)
    (x : Fin N → Bool) (ψ : Qubits p) :
    (Circuit.mapWires e C).eval (embedState e x ψ) = embedState e x (C.eval ψ) := by
  have hket (z : Fin p → Bool) :
      (Circuit.mapWires e C).eval (embedState e x (ket z)) = embedState e x (C.eval (ket z)) := by
    rw [embedState_ket]
    ext y
    rw [Circuit.eval_ket_apply, Circuit.matrix_mapWires, embedState_apply,
      Circuit.eval_ket_apply, glue_comp]
    exact if_congr
      ⟨fun h => h.trans (agreeOff_glue e z x), fun h => h.trans (agreeOff_glue e z x).symm⟩
      rfl rfl
  rw [← sum_smul_ket ψ]
  simp only [map_sum, map_smul, hket]

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

variable {m : ℕ}

/-- The input basis state as a bit string: the input word padded with zeros. -/
theorem ofFn_inputState {x : List Bool} (hx : x.length ≤ m) :
    List.ofFn (inputState m x) = x ++ List.replicate (m - x.length) false := by
  apply List.ext_getElem (by simp; omega)
  intro i h₁ h₂
  simp only [List.getElem_ofFn, inputState, List.getElem_append, List.getElem_replicate]
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt h)]

end Cslib.Quantum
