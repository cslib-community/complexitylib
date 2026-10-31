/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Quantum.Basic

/-!
# Quantum circuits over Hadamard and Toffoli gates, written as data

This file fixes the gate set of the class `BQP` (`Cslib.Complexity.BQP`): the Hadamard gate and the
classical reversible gates NOT, CNOT and Toffoli of
`Complexity/Computability/Circuit/Quantum/Basic.lean`. Their matrix entries lie in
`{0, ±1, ±1/√2}`.

A gate is written as a triple `(h, t, cs) : Bool × ℕ × List ℕ` (`Cslib.Quantum.GateCode`):
`(true, t, [])` is the Hadamard gate on qubit `t`, and `(false, t, cs)` with at most two control
qubits `cs` flips qubit `t` when every qubit of `cs` is one, that is NOT, CNOT or Toffoli. A code
is *well formed* on `m` qubits when its qubits are distinct and below `m`
(`Cslib.Quantum.GateCode.WellFormed`); it then denotes a placed gate
(`Cslib.Quantum.GateCode.toPlacedGate?`), and a list of codes denotes a circuit
(`Cslib.Quantum.Circuit.ofCodes`). Codes are what a polynomial-time machine outputs in the
definition of uniform circuit families.

A run starts in the basis state `|x 0^{m - n}⟩` holding the input word `x` of length `n` on the
first qubits (`Cslib.Quantum.inputState`), and accepts when the final measurement finds qubit `0`
in state `1` (`Cslib.Quantum.accepting`, `Cslib.Quantum.acceptProb`), as in
[Arora, Barak][AroraBarak09], Chapter 10.

Classical reversible gates permute basis states, updating the bit of their target
(`Cslib.Quantum.GateCode.eval_toPlacedGate_ket`). Appending a NOT gate on qubit `0` exchanges
acceptance and rejection (`Cslib.Quantum.acceptProb_append_not`).

## Main definitions

* `Cslib.Quantum.GateCode`, `Cslib.Quantum.GateCode.WellFormed`,
  `Cslib.Quantum.GateCode.toPlacedGate?`: gate codes and the gates they denote.
* `Cslib.Quantum.Circuit.ofCodes`: the circuit denoted by a list of gate codes.
* `Cslib.Quantum.inputState`, `Cslib.Quantum.accepting`, `Cslib.Quantum.acceptProb`: the input
  basis state, the accepting outcomes and the acceptance probability.

## Main results

* `Cslib.Quantum.splitEquiv_symm_update`: placing a classical gate that changes one bit.
* `Cslib.Quantum.GateCode.eval_toPlacedGate_ket`: a classical gate code updates its target bit.
* `Cslib.Quantum.acceptProb_nonneg`, `Cslib.Quantum.acceptProb_le_one`.
* `Cslib.Quantum.acceptProb_append_not`: a final NOT on qubit `0` complements the acceptance
  probability.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Quantum

open Finset

variable {m k : ℕ}

/-- Placing a bit string that differs from `x ∘ A` only at position `i` changes `x` only at the
qubit `A i`. -/
theorem splitEquiv_symm_update (A : Fin k ↪ Fin m) (x : Fin m → Bool) (i : Fin k) (b : Bool) :
    (splitEquiv A).symm (Function.update (x ∘ A) i b, (splitEquiv A x).2) =
      Function.update x (A i) b := by
  funext j
  by_cases hj : ∃ i', A i' = j
  · obtain ⟨i', rfl⟩ := hj
    rw [splitEquiv_symm_apply_wire]
    simp only [Function.update_apply, A.injective.eq_iff, Function.comp_apply]
  · rw [splitEquiv_symm_apply_of_not _ _ _ _ hj, splitEquiv_apply_snd,
      Function.update_of_ne fun h => hj ⟨i, h.symm⟩]

/-- A classical reversible gate that changes only its bit `i`, to `f z` on input `z`, maps `|x⟩` to
the basis state that changes only the qubit `A i`, to `f (x ∘ A)`. -/
theorem PlacedGate.eval_ofPerm_ket_of_update (σ : Equiv.Perm (Fin k → Bool)) (A : Fin k ↪ Fin m)
    (i : Fin k) (f : (Fin k → Bool) → Bool) (hσ : ∀ z, σ z = Function.update z i (f z))
    (x : Fin m → Bool) :
    (PlacedGate.mk k (Gate.ofPerm σ) A).eval (ket x) =
      ket (Function.update x (A i) (f (x ∘ A))) := by
  rw [eval_ofPerm_ket, hσ, splitEquiv_symm_update]

/-! ### Gate codes -/

/-- A **gate code** `(h, t, cs)`: `(true, t, [])` is the Hadamard gate on qubit `t`, and
`(false, t, cs)` with at most two controls `cs` flips qubit `t` when every qubit in `cs` is one
(the NOT, CNOT and Toffoli gates). -/
abbrev GateCode := Bool × ℕ × List ℕ

namespace GateCode

/-- The placed gate denoted by a gate code on `m` qubits, or `none` when the code is not well
formed: its qubits must be distinct and below `m`. -/
noncomputable def toPlacedGate? (m : ℕ) : GateCode → Option (PlacedGate m)
  | (true, t, []) =>
    if h : t < m then some ⟨1, Gate.hadamard, ⟨![⟨t, h⟩], fun i j _ => Subsingleton.elim i j⟩⟩
    else none
  | (false, t, []) =>
    if h : t < m then some ⟨1, Gate.not, ⟨![⟨t, h⟩], fun i j _ => Subsingleton.elim i j⟩⟩
    else none
  | (false, t, [c]) =>
    if h : c < m ∧ t < m ∧ c ≠ t then
      some ⟨2, Gate.cnot, ⟨![⟨c, h.1⟩, ⟨t, h.2.1⟩], by
        intro i j hij
        fin_cases i <;> fin_cases j <;> first | rfl | (simp [Fin.ext_iff] at hij; omega)⟩⟩
    else none
  | (false, t, [c₁, c₂]) =>
    if h : c₁ < m ∧ c₂ < m ∧ t < m ∧ c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then
      some ⟨3, Gate.toffoli, ⟨![⟨c₁, h.1⟩, ⟨c₂, h.2.1⟩, ⟨t, h.2.2.1⟩], by
        intro i j hij
        fin_cases i <;> fin_cases j <;> first | rfl | (simp [Fin.ext_iff] at hij; omega)⟩⟩
    else none
  | _ => none

/-- A gate code is **well formed** on `m` qubits: a Hadamard gate without controls, or a classical
gate with at most two controls, on distinct qubits below `m`. -/
def WellFormed (m : ℕ) : GateCode → Prop
  | (true, t, cs) => t < m ∧ cs = []
  | (false, t, cs) => cs.length ≤ 2 ∧ (t :: cs).Nodup ∧ ∀ i ∈ t :: cs, i < m

instance (m : ℕ) : DecidablePred (WellFormed m)
  | (true, _, _) => inferInstanceAs (Decidable (_ ∧ _))
  | (false, _, _) => inferInstanceAs (Decidable (_ ∧ _))

/-- **Exactly the well-formed codes denote gates.** -/
theorem isSome_toPlacedGate?_iff {g : GateCode} :
    (toPlacedGate? m g).isSome ↔ WellFormed m g := by
  match g with
  | (true, t, []) => simp [WellFormed, toPlacedGate?]
  | (true, t, _ :: _) => simp [WellFormed, toPlacedGate?]
  | (false, t, []) => simp [WellFormed, toPlacedGate?]
  | (false, t, [c]) =>
    simp only [WellFormed, toPlacedGate?]
    split_ifs with h <;> simp only [Option.isSome_some, Option.isSome_none] <;>
      simp only [List.length_singleton, List.nodup_cons, List.not_mem_nil, not_false_eq_true,
        List.nodup_nil, and_true, List.mem_cons, forall_eq_or_imp, true_iff, false_iff,
        Bool.false_eq_true] <;> grind
  | (false, t, [c₁, c₂]) =>
    simp only [WellFormed, toPlacedGate?]
    split_ifs with h <;> simp only [Option.isSome_some, Option.isSome_none] <;>
      simp only [List.length_cons, List.length_nil, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, List.nodup_nil, forall_eq_or_imp, true_iff, false_iff,
        Bool.false_eq_true] <;> grind
  | (false, t, _ :: _ :: _ :: _) => simp [WellFormed, toPlacedGate?]

/-- **A classical gate code updates its target bit**: the well-formed code `(false, t, cs)` maps
`|x⟩` to the basis state that changes only qubit `t`, flipping it when every control is one. -/
theorem eval_toPlacedGate_ket {t : ℕ} {cs : List ℕ} {g : PlacedGate m}
    (hg : toPlacedGate? m (false, t, cs) = some g) (ht : t < m) (x : Fin m → Bool) :
    g.eval (ket x) = ket (Function.update x ⟨t, ht⟩
      (x ⟨t, ht⟩ ^^ cs.all fun c => (List.ofFn x).getD c false)) := by
  have hread (i : Fin m) : (List.ofFn x).getD i false = x i := by
    simp [List.getD_eq_getElem?_getD]
  match cs, hg with
  | [], hg =>
    simp only [toPlacedGate?, ht, ↓reduceDIte, Option.some.injEq] at hg
    subst hg
    refine (PlacedGate.eval_ofPerm_ket_of_update _ _ 0 (fun z => !z 0) (fun z => ?_) x).trans ?_
    · funext i
      rw [Subsingleton.elim i 0, Function.update_self]
      rfl
    · simp only [List.all_nil, Bool.xor_true]
      rfl
  | [c], hg =>
    simp only [toPlacedGate?] at hg
    split_ifs at hg with h
    simp only [Option.some.injEq] at hg
    subst hg
    refine (PlacedGate.eval_ofPerm_ket_of_update _ _ 1 (fun z => z 1 ^^ z 0) (fun _ => rfl)
      x).trans ?_
    rw [List.all_cons, List.all_nil, Bool.and_true,
      show (List.ofFn x).getD c false = x ⟨c, h.1⟩ from hread ⟨c, h.1⟩]
    rfl
  | [c₁, c₂], hg =>
    simp only [toPlacedGate?] at hg
    split_ifs at hg with h
    simp only [Option.some.injEq] at hg
    subst hg
    refine (PlacedGate.eval_ofPerm_ket_of_update _ _ 2 (fun z => z 2 ^^ (z 0 && z 1))
      (fun _ => rfl) x).trans ?_
    rw [List.all_cons, List.all_cons, List.all_nil, Bool.and_true,
      show (List.ofFn x).getD c₁ false = x ⟨c₁, h.1⟩ from hread ⟨c₁, h.1⟩,
      show (List.ofFn x).getD c₂ false = x ⟨c₂, h.2.1⟩ from hread ⟨c₂, h.2.1⟩]
    rfl
  | _ :: _ :: _ :: _, hg => simp [toPlacedGate?] at hg

/-- **The Hadamard gate code branches on its target**: the well-formed code `(true, t, [])` maps
`|x⟩` to `∑_c (-1)^{x_t c} / √2 · |x[t ↦ c]⟩`. -/
theorem eval_toPlacedGate_hadamard_ket {t : ℕ} {g : PlacedGate m}
    (hg : toPlacedGate? m (true, t, []) = some g) (ht : t < m) (x : Fin m → Bool) :
    g.eval (ket x) = ∑ c : Bool, ((if x ⟨t, ht⟩ && c then -1 else 1) *
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) • ket (Function.update x ⟨t, ht⟩ c) := by
  simp only [toPlacedGate?, ht, ↓reduceDIte, Option.some.injEq] at hg
  subst hg
  have hupd (y : Fin m → Bool) (c : Bool) : y = Function.update x ⟨t, ht⟩ c ↔
      y ⟨t, ht⟩ = c ∧ ∀ j ≠ ⟨t, ht⟩, y j = x j := by
    constructor
    · rintro rfl
      exact ⟨Function.update_self .., fun j hj => Function.update_of_ne hj ..⟩
    · rintro ⟨h₁, h₂⟩
      funext j
      by_cases hj : j = ⟨t, ht⟩
      · rw [hj, h₁, Function.update_self]
      · rw [h₂ j hj, Function.update_of_ne hj]
  ext y
  rw [PlacedGate.eval_ket_apply, PlacedGate.matrix_apply, Fintype.sum_bool]
  simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, ket_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, hupd]
  have hcond : (∀ j, (¬∃ i, (⟨![⟨t, ht⟩], fun i j _ => Subsingleton.elim i j⟩ : Fin 1 ↪ Fin m) i =
      j) → y j = x j) ↔ ∀ j ≠ ⟨t, ht⟩, y j = x j := by
    refine forall_congr' fun j => ⟨fun h hj => h ?_, fun h hj => h ?_⟩
    · rintro ⟨i, rfl⟩
      exact hj (by rw [Subsingleton.elim i 0]; rfl)
    · rintro rfl
      exact hj ⟨0, rfl⟩
  by_cases hagree : ∀ j ≠ ⟨t, ht⟩, y j = x j
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (hcond.mpr hagree)), Gate.hadamard_apply]
    have hw (i : Fin 1) :
        (⟨![⟨t, ht⟩], fun i j _ => Subsingleton.elim i j⟩ : Fin 1 ↪ Fin m) i = ⟨t, ht⟩ := by
      rw [Subsingleton.elim i 0]
      rfl
    simp only [iff_true_intro hagree, and_true, Function.comp_apply, hw]
    cases y ⟨t, ht⟩ <;> cases x ⟨t, ht⟩ <;> simp
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (mt hcond.mp hagree))]
    simp only [iff_false_intro hagree, and_false, ite_false, add_zero]

end GateCode

/-- The circuit on `m` qubits denoted by a list of gate codes, applied first to last. Codes that are
not well formed are skipped. -/
noncomputable def Circuit.ofCodes (m : ℕ) (gs : List GateCode) : Circuit m :=
  gs.filterMap (GateCode.toPlacedGate? m)

@[simp] theorem Circuit.ofCodes_nil : Circuit.ofCodes m [] = [] := rfl

theorem Circuit.ofCodes_append (gs hs : List GateCode) :
    Circuit.ofCodes m (gs ++ hs) = Circuit.ofCodes m gs ++ Circuit.ofCodes m hs :=
  List.filterMap_append

/-! ### Input, acceptance and acceptance probability -/

/-- The basis state `|x 0^{m - n}⟩` of an `m`-qubit register holding the input word `x` on its
first qubits (truncated when `x` is longer than `m`). -/
def inputState (m : ℕ) (x : List Bool) : Fin m → Bool := fun i => x.getD i false

/-- The accepting outcomes: qubit `0` reads `1`. -/
def accepting (m : ℕ) : Finset (Fin m → Bool) :=
  univ.filter fun y => ∃ h : 0 < m, y ⟨0, h⟩ = true

/-- The **acceptance probability** of the circuit with gate codes `gs` on `m` qubits on input `x`:
started in `|x 0^{m - n}⟩`, the final measurement finds qubit `0` in state `1`. -/
noncomputable def acceptProb (m : ℕ) (gs : List GateCode) (x : List Bool) : ℝ :=
  measureProb (Circuit.run (Circuit.ofCodes m gs) (inputState m x)) (accepting m)

theorem acceptProb_nonneg (m : ℕ) (gs : List GateCode) (x : List Bool) :
    0 ≤ acceptProb m gs x :=
  measureProb_nonneg _ _

theorem acceptProb_le_one (m : ℕ) (gs : List GateCode) (x : List Bool) :
    acceptProb m gs x ≤ 1 := by
  have h := measureProb_le_measureProb_univ
    (Circuit.run (Circuit.ofCodes m gs) (inputState m x)) (accepting m)
  rwa [measureProb_univ, Circuit.norm_run, one_pow] at h

theorem mem_accepting (hm : 0 < m) {y : Fin m → Bool} :
    y ∈ accepting m ↔ y ⟨0, hm⟩ = true := by
  simp [accepting, hm]

/-- The probability of the rejecting outcomes is one minus the acceptance probability. -/
private theorem measureProb_compl_accepting (ψ : Qubits m) (hψ : ‖ψ‖ = 1) :
    measureProb ψ (accepting m)ᶜ = 1 - measureProb ψ (accepting m) := by
  have h := measureProb_univ ψ
  rw [hψ, one_pow, ← union_compl (accepting m), measureProb,
    sum_union disjoint_compl_right] at h
  rw [measureProb, measureProb]
  linarith

/-- **A final NOT on qubit `0` exchanges acceptance and rejection.** -/
theorem acceptProb_append_not (hm : 0 < m) (gs : List GateCode) (x : List Bool) :
    acceptProb m (gs ++ [(false, 0, [])]) x = 1 - acceptProb m gs x := by
  obtain ⟨g, hg⟩ : ∃ g, GateCode.toPlacedGate? m (false, 0, []) = some g :=
    Option.isSome_iff_exists.mp (GateCode.isSome_toPlacedGate?_iff.mpr
      (by simp [GateCode.WellFormed, hm]))
  set ψ := Circuit.run (Circuit.ofCodes m gs) (inputState m x)
  let flip : (Fin m → Bool) → Fin m → Bool := fun y => Function.update y ⟨0, hm⟩ (!y ⟨0, hm⟩)
  have hflip : Function.Involutive flip := by
    intro y
    funext j
    by_cases hj : j = ⟨0, hm⟩ <;> simp [flip, hj]
  have hket (z : Fin m → Bool) : g.eval (ket z) = ket (flip z) := by
    rw [GateCode.eval_toPlacedGate_ket hg hm z]
    simp only [List.all_nil, Bool.xor_true]
    rfl
  -- the NOT gate reads the amplitude of the flipped outcome
  have happly (y : Fin m → Bool) : (g.eval ψ).ofLp y = ψ.ofLp (flip y) := by
    have hrow (z : Fin m → Bool) :
        (g.matrix : Matrix _ _ ℂ) y z = if z = flip y then 1 else 0 := by
      rw [← PlacedGate.eval_ket_apply, hket, ket_apply]
      refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
      · rw [h, hflip]
      · rw [h, hflip]
    simp only [PlacedGate.eval, unitaryEquiv_apply, Matrix.mulVec, dotProduct, hrow, ite_mul,
      one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]
  have hrun : Circuit.run (Circuit.ofCodes m (gs ++ [(false, 0, [])])) (inputState m x) =
      g.eval ψ := by
    simp only [Circuit.run, Circuit.ofCodes_append, Circuit.eval_append, ψ]
    simp [Circuit.ofCodes, hg]
  rw [acceptProb, hrun, acceptProb, ← measureProb_compl_accepting ψ (Circuit.norm_run _ _)]
  simp only [measureProb, happly]
  refine sum_nbij' flip flip (fun y hy => ?_) (fun y hy => ?_) (fun y _ => hflip y)
    (fun y _ => hflip y) (fun y _ => rfl)
  · rw [mem_accepting hm] at hy
    simp [mem_accepting hm, flip, hy]
  · rw [mem_compl, mem_accepting hm] at hy
    simpa [mem_accepting hm, flip] using hy

end Cslib.Quantum
