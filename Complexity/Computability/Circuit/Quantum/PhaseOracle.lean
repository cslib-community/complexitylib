/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Quantum.Controlled
public import Complexity.Computability.Circuit.Quantum.GateMatrix

/-!
# Phase oracles and the reflection about zero

Conjugating NOT by Hadamard gives the phase flip `Z = diag(1, -1)`
(`Cslib.Quantum.Gate.hadamard_mul_not_mul_hadamard`), so the gate codes `H, X, H` on qubit `t`
negate the amplitudes of the basis strings with bit `t` set
(`Cslib.Quantum.Circuit.eval_ofCodes_zCodes`). Computing a bit with classical codes, flipping its
phase and uncomputing gives the **phase oracle** of the computation
(`Cslib.Quantum.Circuit.eval_ofCodes_phaseOracleCodes`): the amplitude of `|y⟩` is negated when
the computed bit is one, and nothing else changes.

Toffoli gates compute the AND of any number of qubits into a qubit, given zeroed scratch qubits
(`Cslib.Quantum.GateCode.readBit_classicalRun_andCodes`). After NOT gates on the inputs they test
whether the inputs are all zero (`Cslib.Quantum.GateCode.readBit_classicalRun_zeroTestCodes`). The
phase oracle of this test is the **reflection about the all-zero string** of a set of qubits
(`Cslib.Quantum.Circuit.eval_ofCodes_reflectZeroCodes`), the operator `Λ̄(σ_z)` of [Shi][Shi2003],
§4.2, realized with `Λ₂(σ_x)` and `σ_z` as Shi indicates. Here `σ_z` is exactly `H σ_x H`, so the
approximate phase flip of Shi's §4.1 is not needed with the Hadamard gate.

## Main definitions

* `Cslib.Quantum.GateCode.zCodes`: the phase flip `H X H` on one qubit.
* `Cslib.Quantum.GateCode.phaseOracleCodes`: compute, flip the phase, uncompute.
* `Cslib.Quantum.GateCode.andCodes`, `Cslib.Quantum.GateCode.zeroTestCodes`: the AND of qubits,
  and the test that qubits are all zero.
* `Cslib.Quantum.GateCode.reflectZeroCodes`: the reflection about the all-zero string.

## Main results

* `Cslib.Quantum.Gate.hadamard_mul_not_mul_hadamard`: `H X H = Z`.
* `Cslib.Quantum.unitaryEquiv_place_of_diagonal`: a placed diagonal gate acts pointwise.
* `Cslib.Quantum.Circuit.eval_ofCodes_phaseOracleCodes`: the phase oracle of classical codes.
* `Cslib.Quantum.Circuit.eval_ofCodes_reflectZeroCodes`: the reflection about zero.

## References

* [Y. Shi, *Both Toffoli and Controlled-NOT need little help to do universal quantum
  computation*][Shi2003], §4 (arXiv:quant-ph/0205115v2)
-/

@[expose] public section

namespace Cslib.Quantum

open Finset Matrix

variable {m : ℕ}

namespace Gate

/-- **`H X H = Z`**: conjugating NOT by Hadamard gives the phase flip `diag(1, -1)`. -/
theorem hadamard_mul_not_mul_hadamard :
    ((hadamard * Gate.not * hadamard : Gate 1) : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ) =
      Matrix.diagonal fun x => if x 0 then -1 else 1 := by
  have h2 : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1 / 2 := by
    rw [← sq, inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hext {x y : Fin 1 → Bool} : x = y ↔ x 0 = y 0 :=
    ⟨fun h => h ▸ rfl, fun h => funext fun i => by rwa [Subsingleton.elim i 0]⟩
  have hsum (f : (Fin 1 → Bool) → ℂ) : ∑ x, f x = f (fun _ => false) + f (fun _ => true) := by
    rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool, add_comm]
    rfl
  ext y x
  simp only [Submonoid.coe_mul, Matrix.mul_apply, hsum, hadamard_apply, not_apply,
    Matrix.diagonal_apply, hext]
  cases y 0 <;> cases x 0 <;> norm_num [h2]

end Gate

/-- **A placed diagonal unitary acts pointwise**: it multiplies each amplitude by the diagonal
entry at the qubits it acts on. -/
theorem unitaryEquiv_place_of_diagonal {k : ℕ} (A : Fin k ↪ Fin m) (U : Gate k)
    (d : (Fin k → Bool) → ℂ) (hU : (U : Matrix _ _ ℂ) = Matrix.diagonal d) (ψ : Qubits m)
    (y : Fin m → Bool) : (unitaryEquiv (place A U) ψ).ofLp y = d (y ∘ A) * ψ.ofLp y := by
  rw [unitaryEquiv_apply, mulVec, dotProduct, sum_eq_single y]
  · rw [place_apply, ite_eq_left fun _ _ => rfl, hU, diagonal_apply_eq]
  · intro x _ hxy
    rw [place_apply, hU]
    split_ifs with h
    · rw [diagonal_apply_ne _ fun hyx => hxy (funext fun j => ?_), zero_mul]
      by_cases hj : ∃ i, A i = j
      · obtain ⟨i, rfl⟩ := hj
        exact (congrFun hyx i).symm
      · exact (h j hj).symm
    · rw [zero_mul]
  · simp

namespace GateCode

/-- The codes `H, X, H` on qubit `t`: the phase flip `Z` on `t`. -/
def zCodes (t : ℕ) : List GateCode := [(true, t, []), (false, t, []), (true, t, [])]

theorem wellFormed_zCodes {t : ℕ} (ht : t < m) : ∀ g ∈ zCodes t, WellFormed m g := by
  intro g hg
  simp only [zCodes, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp [WellFormed, ht]

/-- Classical codes, the phase flip on qubit `t`, and the codes run backwards: the **phase oracle**
of bit `t` of `classicalRun gs`. -/
def phaseOracleCodes (gs : List GateCode) (t : ℕ) : List GateCode := gs ++ zCodes t ++ gs.reverse

end GateCode

open GateCode

namespace Circuit

/-- **The phase flip `Z = H X H` on qubit `t`** negates the amplitudes of the basis strings with
bit `t` set. -/
theorem eval_ofCodes_zCodes {t : ℕ} (ht : t < m) (ψ : Qubits m) (y : Fin m → Bool) :
    (eval (ofCodes m (zCodes t)) ψ).ofLp y = (if readBit y t then -1 else 1) * ψ.ofLp y := by
  simp only [zCodes, ofCodes, List.filterMap_cons, toPlacedGate?, ht, ↓reduceDIte,
    List.filterMap_nil, eval_cons, eval_nil, PlacedGate.eval, PlacedGate.matrix]
  rw [← unitaryEquiv_mul, ← unitaryEquiv_mul, ← map_mul, ← map_mul,
    unitaryEquiv_place_of_diagonal _ _ _ Gate.hadamard_mul_not_mul_hadamard, readBit_of_lt y ht]
  rfl

/-- **The phase oracle of a classical computation**: `phaseOracleCodes gs t` negates the amplitude
of each basis string `y` for which bit `t` of `classicalRun gs y` is set. -/
theorem eval_ofCodes_phaseOracleCodes {gs : List GateCode} (h : IsClassical m gs) {t : ℕ}
    (ht : t < m) (ψ : Qubits m) (y : Fin m → Bool) :
    (eval (ofCodes m (phaseOracleCodes gs t)) ψ).ofLp y =
      (if readBit (classicalRun gs y) t then -1 else 1) * ψ.ofLp y := by
  rw [phaseOracleCodes, ofCodes_append, ofCodes_append, eval_append, eval_append,
    eval_ofCodes_apply h.reverse, classicalUnrun_reverse, eval_ofCodes_zCodes ht,
    eval_ofCodes_apply h, classicalUnrun_classicalRun h]

end Circuit

namespace GateCode

/-- Toffoli gates computing into qubit `w` the AND of the qubits `cs`, using the qubits
`w + 1, …, w + |cs|` as scratch: `andCodes [] w` is NOT on `w`, and `andCodes (c :: cs) w` computes
the AND of `cs` into `w + 1` and then applies `Λ₂(σ_x)[c, w + 1; w]`. -/
def andCodes : List ℕ → ℕ → List GateCode
  | [], w => [(false, w, [])]
  | c :: cs, w => andCodes cs (w + 1) ++ [(false, w, [c, w + 1])]

/-- The codes of `andCodes cs w` target only the qubits `w, …, w + |cs|`. -/
theorem target_mem_andCodes {cs : List ℕ} {w : ℕ} :
    ∀ g ∈ andCodes cs w, w ≤ g.2.1 ∧ g.2.1 ≤ w + cs.length := by
  induction cs generalizing w with
  | nil => simp [andCodes]
  | cons c cs ih =>
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · have := ih g hg
      simp only [List.length_cons]
      omega
    · obtain rfl := List.mem_singleton.mp hg
      simp

theorem isClassical_andCodes {cs : List ℕ} {w : ℕ} (hc : ∀ c ∈ cs, c < w)
    (hw : w + cs.length < m) : IsClassical m (andCodes cs w) := by
  induction cs generalizing w with
  | nil =>
    intro g hg
    obtain rfl := List.mem_singleton.mp hg
    exact ⟨rfl, by simp, by simp, by simpa using hw⟩
  | cons c cs ih =>
    have hc' := hc c (List.mem_cons_self ..)
    simp only [List.length_cons] at hw
    refine IsClassical.append.mpr ⟨ih (fun c' hc'' => ?_) (by omega), fun g hg => ?_⟩
    · have := hc c' (List.mem_cons_of_mem _ hc'')
      omega
    · obtain rfl := List.mem_singleton.mp hg
      refine ⟨rfl, by simp, ?_, ?_⟩
      · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
          not_false_eq_true, and_true]
        omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        omega

/-- **`andCodes cs w` computes the AND of `cs` into qubit `w`** when the scratch qubits
`w, …, w + |cs|` start at zero. -/
theorem readBit_classicalRun_andCodes {cs : List ℕ} {w : ℕ} (hc : ∀ c ∈ cs, c < w)
    (hw : w + cs.length < m) (x : Fin m → Bool)
    (hx : ∀ i, w ≤ i → i ≤ w + cs.length → readBit x i = false) :
    readBit (classicalRun (andCodes cs w) x) w = cs.all (readBit x) := by
  induction cs generalizing w with
  | nil =>
    simp only [andCodes, classicalRun_cons, classicalRun_nil, readBit_classicalStep,
      List.all_nil, Bool.and_true, hx w le_rfl (by simp)]
    simp [show w < m by simpa using hw]
  | cons c cs ih =>
    have hc' := hc c (List.mem_cons_self ..)
    simp only [List.length_cons] at hw hx
    have hcs : ∀ c' ∈ cs, c' < w + 1 := fun c' h => by
      have := hc c' (List.mem_cons_of_mem _ h)
      omega
    have hne (i : ℕ) (hi : i < w + 1) : ∀ g ∈ andCodes cs (w + 1), g.2.1 ≠ i := fun g hg => by
      have := (target_mem_andCodes g hg).1
      omega
    rw [andCodes, classicalRun_append, classicalRun_cons, classicalRun_nil, readBit_classicalStep,
      readBit_classicalRun_of_forall_ne (hne w (by omega))]
    simp only [List.all_cons, List.all_nil, Bool.and_true,
      readBit_classicalRun_of_forall_ne (hne c (by omega)),
      ih hcs (by omega) fun i h₁ h₂ => hx i (by omega) (by omega), hx w le_rfl (by omega)]
    simp [show w < m by omega]

/-- NOT gates on the qubits `cs`, then `andCodes`: computes into qubit `w` whether all the qubits
`cs` are zero. -/
def zeroTestCodes (cs : List ℕ) (w : ℕ) : List GateCode :=
  cs.map (fun c => (false, c, [])) ++ andCodes cs w

theorem isClassical_zeroTestCodes {cs : List ℕ} {w : ℕ} (hc : ∀ c ∈ cs, c < w)
    (hw : w + cs.length < m) : IsClassical m (zeroTestCodes cs w) := by
  refine IsClassical.append.mpr ⟨fun g hg => ?_, isClassical_andCodes hc hw⟩
  obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hg
  have := hc c hc'
  exact ⟨rfl, by simp, by simp, by simp; omega⟩

/-- **`zeroTestCodes cs w` computes into qubit `w` whether the qubits `cs` are all zero**, when the
scratch qubits `w, …, w + |cs|` start at zero. -/
theorem readBit_classicalRun_zeroTestCodes {cs : List ℕ} (hnd : cs.Nodup) {w : ℕ}
    (hc : ∀ c ∈ cs, c < w) (hw : w + cs.length < m) (x : Fin m → Bool)
    (hx : ∀ i, w ≤ i → i ≤ w + cs.length → readBit x i = false) :
    readBit (classicalRun (zeroTestCodes cs w) x) w = cs.all fun c => !readBit x c := by
  have hread : ∀ g ∈ cs.map (fun c => ((false, c, []) : GateCode)), ∀ g' ∈ cs.map
      (fun c => ((false, c, []) : GateCode)), g.2.1 ∉ g'.2.2 := fun g _ g' hg' => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hg'
    simp
  have hflip (i : ℕ) : readBit (classicalRun (cs.map fun c => ((false, c, []) : GateCode)) x) i =
      (readBit x i ^^ decide (i ∈ cs)) := by
    by_cases hi : i ∈ cs
    · have := readBit_classicalRun_of_mem (fun g hg => by
        obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hg
        exact show c < m by have := hc c hc'; omega)
        (by simpa [List.map_map, Function.comp_def] using hnd) hread x
        (List.mem_map_of_mem (f := fun c => ((false, c, []) : GateCode)) hi)
      simpa [hi] using this
    · rw [readBit_classicalRun_of_forall_ne fun g hg h => by
        obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hg
        exact hi (h ▸ hc')]
      simp [hi]
  rw [zeroTestCodes, classicalRun_append,
    readBit_classicalRun_andCodes hc hw _ fun i h₁ h₂ => by
      rw [hflip, hx i h₁ h₂]
      simp only [Bool.false_xor, decide_eq_false_iff_not]
      intro hi
      have := hc i hi
      omega]
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact forall₂_congr fun c hc => by simp [hflip, hc]

/-- The **reflection about the all-zero string** of the qubits `cs`: negate the amplitudes of the
basis strings on which every qubit of `cs` is zero, computing the test into the scratch qubits
`w, …, w + |cs|`. -/
def reflectZeroCodes (cs : List ℕ) (w : ℕ) : List GateCode :=
  phaseOracleCodes (zeroTestCodes cs w) w

end GateCode

namespace Circuit

/-- **The reflection about the all-zero string**: on basis strings whose scratch qubits
`w, …, w + |cs|` are zero, `reflectZeroCodes cs w` negates the amplitude exactly when every qubit
of `cs` is zero. -/
theorem eval_ofCodes_reflectZeroCodes {cs : List ℕ} (hnd : cs.Nodup) {w : ℕ}
    (hc : ∀ c ∈ cs, c < w) (hw : w + cs.length < m) (ψ : Qubits m) (y : Fin m → Bool)
    (hy : ∀ i, w ≤ i → i ≤ w + cs.length → readBit y i = false) :
    (eval (ofCodes m (reflectZeroCodes cs w)) ψ).ofLp y =
      (if cs.all (fun c => !readBit y c) then -1 else 1) * ψ.ofLp y := by
  rw [reflectZeroCodes, eval_ofCodes_phaseOracleCodes (isClassical_zeroTestCodes hc hw) (by omega),
    readBit_classicalRun_zeroTestCodes hnd hc hw y hy]

end Circuit

end Cslib.Quantum
