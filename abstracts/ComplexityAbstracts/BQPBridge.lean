/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.Encoding
import ComplexityAbstracts.Computation
import Complexity.Computability.Complexity.Classes.BQP.Counting

/-!
# Bridge for the `BQP ⊆ PP` formal abstract

`BQPAbstract.lean` restates quantum states, gates, circuit runs and acceptance as explicit formulas
on amplitude functions `(Fin m → Bool) → ℂ`. This module repeats those formulas and proves that
they agree with the library's circuits:

* a well-formed gate code acts on amplitudes as its formula says
  (`ComplexityAbstracts.BQPBridge.ofLp_eval_toPlacedGate`), from the library's action on basis
  states (`Cslib.Quantum.GateCode.eval_toPlacedGate_ket`,
  `Cslib.Quantum.GateCode.eval_toPlacedGate_hadamard_ket`);
* hence a run of well-formed codes is `Cslib.Quantum.Circuit.run ∘ Cslib.Quantum.Circuit.ofCodes`
  (`ComplexityAbstracts.BQPBridge.ofLp_eval_ofCodes`), and the explicit acceptance probability is
  `Cslib.Quantum.acceptProb` (`ComplexityAbstracts.BQPBridge.acceptProb_eq`);
* the restated class is `Cslib.Complexity.BQP` (`ComplexityAbstracts.BQPBridge.mem_BQP_iff`), and
  the restated `PP` is `Cslib.Complexity.PP` by unfolding, so `Cslib.Complexity.BQP_subset_PP`
  gives the headline (`ComplexityAbstracts.BQPBridge.BQP_subset_PP`).
-/

namespace ComplexityAbstracts.BQPBridge

open ComplexityTests.Abstracts Cslib.Quantum Finset

/-! ### The explicit model, as in the abstract -/

/-- The amplitudes of an `m`-qubit state, indexed by basis strings. -/
abbrev State (m : ℕ) := (Fin m → Bool) → ℂ

/-- Bit `i` of a basis string, `false` past its end. -/
def bit {m : ℕ} (y : Fin m → Bool) (i : ℕ) : Bool := if h : i < m then y ⟨i, h⟩ else false

/-- The basis string `y` with bit `t` set to `c`. -/
def setBit {m : ℕ} (y : Fin m → Bool) (t : ℕ) (c : Bool) : Fin m → Bool :=
  fun i => if (i : ℕ) = t then c else y i

/-- The Hadamard gate on qubit `t`. -/
noncomputable def hadamard {m : ℕ} (t : ℕ) (ψ : State m) : State m := fun y =>
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ∑ c : Bool, (if c && bit y t then -1 else 1) * ψ (setBit y t c)

/-- Flip bit `t` when every bit of `cs` is one. -/
def flip {m : ℕ} (t : ℕ) (cs : List ℕ) (y : Fin m → Bool) : Fin m → Bool :=
  setBit y t (bit y t ^^ cs.all (bit y))

/-- The classical gate with target `t` and controls `cs`. -/
def classical {m : ℕ} (t : ℕ) (cs : List ℕ) (ψ : State m) : State m := ψ ∘ flip t cs

/-- The gate denoted by a gate code. -/
noncomputable def applyGate {m : ℕ} (g : GateCode) (ψ : State m) : State m :=
  if g.1 then hadamard g.2.1 ψ else classical g.2.1 g.2.2 ψ

/-- Apply gate codes first to last. -/
noncomputable def run {m : ℕ} (gs : List GateCode) (ψ : State m) : State m :=
  gs.foldl (fun ψ g => applyGate g ψ) ψ

/-- The basis state `|z⟩`. -/
def basis {m : ℕ} (z : Fin m → Bool) : State m := fun y => if y = z then 1 else 0

/-- The input word padded with zeros to `m` bits. -/
def pad (m : ℕ) (x : List Bool) : Fin m → Bool := fun i => x.getD i false

/-- The probability of reading `1` on qubit `0` after running the codes from `|x 0^{m - |x|}⟩`. -/
noncomputable def acceptProb (m : ℕ) (gs : List GateCode) (x : List Bool) : ℝ :=
  ∑ y : Fin m → Bool, if bit y 0 then ‖run gs (basis (pad m x)) y‖ ^ 2 else 0

/-! ### Gates on amplitudes -/

variable {m : ℕ}

theorem bit_of_lt (y : Fin m → Bool) {i : ℕ} (h : i < m) : bit y i = y ⟨i, h⟩ := by
  simp [bit, h]

theorem getD_ofFn (y : Fin m → Bool) (i : ℕ) : (List.ofFn y).getD i false = bit y i := by
  unfold bit
  split_ifs with h <;> simp [List.getD_eq_getElem?_getD, h]

theorem setBit_eq_update (y : Fin m → Bool) {t : ℕ} (ht : t < m) (c : Bool) :
    setBit y t c = Function.update y ⟨t, ht⟩ c := by
  funext i
  simp only [setBit, Function.update_apply, Fin.ext_iff]

theorem ofLp_ket (z : Fin m → Bool) : (ket z).ofLp = basis z := by
  funext y
  rw [ket_apply]
  rfl

/-- A placed gate reads each amplitude through the column of its matrix. -/
theorem ofLp_eval_apply (pg : PlacedGate m) (ψ : Qubits m) (y : Fin m → Bool) :
    (pg.eval ψ).ofLp y = ∑ z, (pg.eval (ket z)).ofLp y * ψ.ofLp z := by
  simp only [PlacedGate.eval_ket_apply]
  simp [PlacedGate.eval, Matrix.mulVec, dotProduct]

/-- The Hadamard formula is linear, with matrix entries its values on basis states. -/
theorem hadamard_apply_eq_sum (t : ℕ) (ψ : State m) (y : Fin m → Bool) :
    hadamard t ψ y = ∑ z, hadamard t (basis z) y * ψ z := by
  simp only [hadamard, basis, mul_ite, mul_one, mul_zero, sum_mul, mul_sum, ite_mul, zero_mul]
  rw [sum_comm]
  simp only [sum_ite_eq, mem_univ, ite_true, mul_assoc, one_mul]

/-- The Hadamard gate code agrees with the Hadamard formula on basis states. -/
theorem hadamard_basis {t : ℕ} {pg : PlacedGate m}
    (hg : GateCode.toPlacedGate? m (true, t, []) = some pg) (ht : t < m) (z y : Fin m → Bool) :
    (pg.eval (ket z)).ofLp y = hadamard t (basis z) y := by
  rw [GateCode.eval_toPlacedGate_hadamard_ket hg ht z]
  simp only [hadamard, basis, bit_of_lt _ ht, setBit_eq_update _ ht, Fintype.sum_bool,
    WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, ket_apply, smul_eq_mul,
    Function.update_eq_iff, Function.eq_update_iff]
  by_cases hP : ∀ j ≠ (⟨t, ht⟩ : Fin m), y j = z j
  · simp only [iff_true_intro hP, and_true]
    cases y ⟨t, ht⟩ <;> cases z ⟨t, ht⟩ <;> simp
  · simp [hP]

/-- A flip of target `t`, not among the controls, is an involution. -/
theorem flip_flip {t : ℕ} {cs : List ℕ} (ht : t < m) (hcs : t ∉ cs) (y : Fin m → Bool) :
    flip t cs (flip t cs y) = y := by
  have hbit (v : Bool) (c : ℕ) (hc : c ≠ t) : bit (Function.update y ⟨t, ht⟩ v) c = bit y c := by
    unfold bit
    split_ifs with h
    · exact Function.update_of_ne (fun h' => hc (congrArg Fin.val h')) _ _
    · rfl
  have hall (v : Bool) : cs.all (bit (Function.update y ⟨t, ht⟩ v)) = cs.all (bit y) := by
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    exact forall₂_congr fun c hc => by rw [hbit v c fun h => hcs (h ▸ hc)]
  simp only [flip, setBit_eq_update _ ht, bit_of_lt _ ht, Function.update_self, hall,
    Function.update_idem, Bool.xor_assoc, Bool.xor_self, Bool.xor_false, Function.update_eq_self]

/-- The classical gate code `(false, t, cs)` maps `|z⟩` to `|flip t cs z⟩`. -/
theorem classical_basis {t : ℕ} {cs : List ℕ} {pg : PlacedGate m}
    (hg : GateCode.toPlacedGate? m (false, t, cs) = some pg) (ht : t < m) (z y : Fin m → Bool) :
    (pg.eval (ket z)).ofLp y = if y = flip t cs z then 1 else 0 := by
  rw [GateCode.eval_toPlacedGate_ket hg ht z, ket_apply]
  simp only [getD_ofFn, flip, setBit_eq_update _ ht, bit_of_lt _ ht]

/-- **A well-formed gate code acts on amplitudes as its formula says.** -/
theorem ofLp_eval_toPlacedGate {g : GateCode} {pg : PlacedGate m}
    (hwf : GateCode.WellFormed m g) (hg : GateCode.toPlacedGate? m g = some pg) (ψ : Qubits m) :
    (pg.eval ψ).ofLp = applyGate g ψ.ofLp := by
  funext y
  obtain ⟨_ | _, t, cs⟩ := g
  · obtain ⟨-, hnd, hlt⟩ := hwf
    have ht : t < m := hlt t (List.mem_cons_self ..)
    have hcs : t ∉ cs := (List.nodup_cons.mp hnd).1
    have hrow (z : Fin m → Bool) : (pg.eval (ket z)).ofLp y = if z = flip t cs y then 1 else 0 :=
      (classical_basis hg ht z y).trans (if_congr ⟨fun h => by rw [h, flip_flip ht hcs],
        fun h => by rw [h, flip_flip ht hcs]⟩ rfl rfl)
    simp only [ofLp_eval_apply, hrow, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ,
      ite_true]
    rfl
  · obtain ⟨ht, rfl⟩ := hwf
    rw [ofLp_eval_apply]
    change _ = hadamard t ψ.ofLp y
    rw [hadamard_apply_eq_sum]
    exact sum_congr rfl fun z _ => by rw [hadamard_basis hg ht]

/-- **A run of well-formed gate codes is the library's circuit.** -/
theorem ofLp_eval_ofCodes {gs : List GateCode} (hwf : ∀ g ∈ gs, GateCode.WellFormed m g)
    (ψ : Qubits m) : (Circuit.eval (Circuit.ofCodes m gs) ψ).ofLp = run gs ψ.ofLp := by
  induction gs generalizing ψ with
  | nil => simp [run]
  | cons g gs ih =>
    obtain ⟨pg, hpg⟩ := Option.isSome_iff_exists.mp
      (GateCode.isSome_toPlacedGate?_iff.mpr (hwf g (List.mem_cons_self ..)))
    have hcodes : Circuit.ofCodes m (g :: gs) = pg :: Circuit.ofCodes m gs := by
      simp [Circuit.ofCodes, hpg]
    rw [hcodes, Circuit.eval_cons, ih (fun g' hg' => hwf g' (List.mem_cons_of_mem _ hg')),
      ofLp_eval_toPlacedGate (hwf g (List.mem_cons_self ..)) hpg]
    rfl

/-- **The explicit acceptance probability is the library's**, for well-formed gate codes. -/
theorem acceptProb_eq {gs : List GateCode} (hwf : ∀ g ∈ gs, GateCode.WellFormed m g)
    (x : List Bool) : acceptProb m gs x = Cslib.Quantum.acceptProb m gs x := by
  have hrun : (Circuit.run (Circuit.ofCodes m gs) (inputState m x)).ofLp =
      run gs (basis (pad m x)) := by
    rw [Circuit.run, ofLp_eval_ofCodes hwf, ofLp_ket]
    rfl
  rw [Cslib.Quantum.acceptProb, measureProb, accepting, sum_filter, hrun, acceptProb]
  refine sum_congr rfl fun y _ => if_congr ?_ rfl rfl
  unfold bit
  split_ifs with h <;> simp [h]

/-! ### The classes -/

/-- The encoding of gate codes `(h, t, cs)`: the flag bit, then the target and the controls in
unary. -/
abbrev encGateCode : GateCode ↪ List Bool :=
  Encoding.encPair Encoding.encBool
    (Encoding.encPair Encoding.encUnary (Encoding.encList Encoding.encUnary))

/-- Polynomial-time uniform families of well-formed gate codes. -/
def Uniform (width : ℕ → ℕ) (gates : ℕ → List GateCode) : Prop :=
  Computation.PolyTime width Encoding.encUnary Encoding.encUnary ∧
    Computation.PolyTime gates Encoding.encUnary (Encoding.encList encGateCode) ∧
    ∀ n, n ≤ width n ∧ 0 < width n ∧ ∀ g ∈ gates n, GateCode.WellFormed (width n) g

/-- Bounded-error quantum polynomial time, over the explicit model. -/
def BQP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (width : ℕ → ℕ) (gates : ℕ → List GateCode), Uniform width gates ∧ ∀ a,
    (a ∈ A → 2 / 3 ≤ acceptProb (width (enc a).length) (gates (enc a).length) (enc a)) ∧
    (a ∉ A → acceptProb (width (enc a).length) (gates (enc a).length) (enc a) ≤ 1 / 3)}

/-- Count the accepted binary strings of exactly `n` bits. -/
def acceptCount {α : Type} (V : α × List Bool → Bool) (a : α) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin n → Bool => V (a, List.ofFn w) = true).card

/-- Unbounded-error probabilistic polynomial time, by a strict majority of certificates. -/
def PP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool), Computation.PolyTimeVerifier enc V ∧
    ∀ a, a ∈ A ↔ 2 ^ p.eval (enc a).length < 2 * acceptCount V a (p.eval (enc a).length)}

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- **The explicit class is the library's `BQP`.** -/
theorem mem_BQP_iff : A ∈ BQP enc ↔ A ∈ Cslib.Complexity.BQP enc := by
  constructor
  · rintro ⟨width, gates, ⟨hw, hg, hn⟩, hdec⟩
    let F : UniformCircuitFamily :=
      { width, gates
        computableInPolyTime_width := hw
        computableInPolyTime_gates := hg
        le_width := fun n => (hn n).1
        width_pos := fun n => (hn n).2.1
        wellFormed := fun n => (hn n).2.2 }
    refine ⟨F, fun a => ?_⟩
    rw [UniformCircuitFamily.acceptProb, ← acceptProb_eq ((hn _).2.2)]
    exact hdec a
  · rintro ⟨F, hF⟩
    refine ⟨F.width, F.gates, ⟨F.computableInPolyTime_width, F.computableInPolyTime_gates,
      fun n => ⟨F.le_width n, F.width_pos n, F.wellFormed n⟩⟩, fun a => ?_⟩
    rw [acceptProb_eq (F.wellFormed _)]
    exact hF a

/-- The explicit `PP` is the library's, by unfolding. -/
theorem PP_eq : PP enc = Cslib.Complexity.PP enc := rfl

/-- **`BQP ⊆ PP`** over the explicit model, from `Cslib.Complexity.BQP_subset_PP`. -/
theorem BQP_subset_PP (enc : α ↪ List Bool) : BQP enc ⊆ PP enc := fun _ hA =>
  Cslib.Complexity.BQP_subset_PP (mem_BQP_iff.mp hA)

end ComplexityAbstracts.BQPBridge
