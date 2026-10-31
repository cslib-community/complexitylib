/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Quantum.Code

/-!
# Classical gate codes on basis states

The classical gate codes NOT, CNOT and Toffoli of
`Complexity/Computability/Circuit/Quantum/Code.lean` permute the computational basis: the code
`(false, t, cs)` flips bit `t` when every bit of `cs` is one
(`Cslib.Quantum.GateCode.classicalStep`). A list of classical codes therefore maps the basis
state `|x⟩` to the basis state of the composed permutation
(`Cslib.Quantum.Circuit.eval_ofCodes_ket`), and it acts on any state by reading amplitudes back
through the inverse permutation (`Cslib.Quantum.Circuit.eval_ofCodes_apply`). Measuring after a
classical circuit is measuring before it and then applying the permutation to the outcome
(`Cslib.Quantum.Circuit.measureProb_eval_ofCodes`).

Bits of a basis string are read by their number (`Cslib.Quantum.readBit`), as in gate codes.

## Main definitions

* `Cslib.Quantum.readBit`: bit `c` of a basis string, `false` past its end.
* `Cslib.Quantum.GateCode.classicalStep`: the permutation of a classical gate code.
* `Cslib.Quantum.GateCode.IsClassical`: a list of well-formed classical gate codes.
* `Cslib.Quantum.GateCode.classicalRun`, `Cslib.Quantum.GateCode.classicalUnrun`: the composed
  permutation of a list of classical codes and its inverse.
* `Cslib.Quantum.GateCode.swapCodes`: three CNOT gates moving a qubit into qubit `0`.

## Main results

* `Cslib.Quantum.GateCode.readBit_classicalStep`: a classical code changes only its target.
* `Cslib.Quantum.Circuit.eval_ofCodes_ket`, `Cslib.Quantum.Circuit.eval_ofCodes_apply`: classical
  circuits permute basis states.
* `Cslib.Quantum.Circuit.measureProb_eval_ofCodes`: measuring after a classical circuit.
-/

@[expose] public section

namespace Cslib.Quantum

open Finset

variable {m : ℕ}

/-- Bit number `c` of a basis string, and `false` past its end. -/
def readBit (x : Fin m → Bool) (c : ℕ) : Bool := (List.ofFn x).getD c false

theorem readBit_of_lt (x : Fin m → Bool) {c : ℕ} (h : c < m) : readBit x c = x ⟨c, h⟩ := by
  simp [readBit, List.getD_eq_getElem?_getD, h]

theorem readBit_of_le (x : Fin m → Bool) {c : ℕ} (h : m ≤ c) : readBit x c = false := by
  simp [readBit, List.getD_eq_getElem?_getD, h]

@[simp] theorem readBit_fin (x : Fin m → Bool) (i : Fin m) : readBit x i = x i :=
  readBit_of_lt x i.2

/-- Basis strings are equal when they have the same bits. -/
theorem funext_readBit {x y : Fin m → Bool} (h : ∀ c, readBit x c = readBit y c) : x = y :=
  funext fun i => by simpa using h i

namespace GateCode

/-- The permutation of basis strings of the classical gate code `(false, t, cs)`: bit `t` flips when
every bit of `cs` is one. It is the identity when `t` is out of range. -/
def classicalStep (g : GateCode) (x : Fin m → Bool) : Fin m → Bool :=
  if h : g.2.1 < m then Function.update x ⟨g.2.1, h⟩ (x ⟨g.2.1, h⟩ ^^ g.2.2.all (readBit x))
  else x

/-- **A classical code changes only its target bit**, flipping it when all its controls are one. -/
theorem readBit_classicalStep (g : GateCode) (x : Fin m → Bool) (c : ℕ) :
    readBit (classicalStep g x) c =
      (readBit x c ^^ (decide (c = g.2.1 ∧ g.2.1 < m) && g.2.2.all (readBit x))) := by
  unfold classicalStep
  split_ifs with h
  · by_cases hc : c < m
    · rw [readBit_of_lt _ hc, readBit_of_lt _ hc]
      by_cases hct : c = g.2.1
      · subst hct
        simp [h]
      · rw [Function.update_of_ne (fun h' => hct (congrArg Fin.val h'))]
        simp [hct]
    · rw [readBit_of_le _ (not_lt.mp hc), readBit_of_le _ (not_lt.mp hc)]
      have : c ≠ g.2.1 := fun h' => hc (h' ▸ h)
      simp [this]
  · simp [h]

/-- Bits other than the target of a classical code read the same after it acts. -/
theorem all_readBit_classicalStep {g : GateCode} (x : Fin m → Bool)
    (cs : List ℕ) (hcs : g.2.1 ∉ cs) :
    cs.all (readBit (classicalStep g x)) = cs.all (readBit x) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.all_cons, List.all_cons, ih (fun h => hcs (List.mem_cons_of_mem _ h)),
      readBit_classicalStep]
    have : c ≠ g.2.1 := fun h => hcs (h ▸ List.mem_cons_self ..)
    simp [this]

/-- **A classical code is an involution** when its target is not one of its controls. -/
theorem classicalStep_classicalStep {g : GateCode} (hg : g.2.1 ∉ g.2.2) (x : Fin m → Bool) :
    classicalStep g (classicalStep g x) = x := by
  refine funext_readBit fun c => ?_
  rw [readBit_classicalStep, all_readBit_classicalStep x _ hg, readBit_classicalStep,
    Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- A list of **classical gate codes**, well formed on `m` qubits: NOT, CNOT and Toffoli gates. -/
def IsClassical (m : ℕ) (gs : List GateCode) : Prop :=
  ∀ g ∈ gs, g.1 = false ∧ WellFormed m g

theorem IsClassical.cons {g : GateCode} {gs : List GateCode} :
    IsClassical m (g :: gs) ↔ (g.1 = false ∧ WellFormed m g) ∧ IsClassical m gs :=
  List.forall_mem_cons

theorem IsClassical.append {gs hs : List GateCode} :
    IsClassical m (gs ++ hs) ↔ IsClassical m gs ∧ IsClassical m hs :=
  List.forall_mem_append

theorem IsClassical.flatMap {β : Type*} {l : List β} {f : β → List GateCode}
    (h : ∀ b ∈ l, IsClassical m (f b)) : IsClassical m (l.flatMap f) := by
  intro g hg
  obtain ⟨b, hb, hg⟩ := List.mem_flatMap.mp hg
  exact h b hb g hg

/-- The target of a well-formed classical code is not one of its controls. -/
theorem target_notMem_of_wellFormed {g : GateCode} (h₁ : g.1 = false) (h₂ : WellFormed m g) :
    g.2.1 ∉ g.2.2 := by
  obtain ⟨b, t, cs⟩ := g
  subst h₁
  exact (List.nodup_cons.mp h₂.2.1).1

/-- The composed permutation of a list of classical codes, applied first to last. -/
def classicalRun (gs : List GateCode) (x : Fin m → Bool) : Fin m → Bool :=
  gs.foldl (fun y g => classicalStep g y) x

/-- The inverse of `classicalRun`: the permutations applied last to first. -/
def classicalUnrun (gs : List GateCode) (y : Fin m → Bool) : Fin m → Bool :=
  gs.foldr (fun g y => classicalStep g y) y

@[simp] theorem classicalRun_nil (x : Fin m → Bool) : classicalRun [] x = x := rfl

@[simp] theorem classicalRun_cons (g : GateCode) (gs : List GateCode) (x : Fin m → Bool) :
    classicalRun (g :: gs) x = classicalRun gs (classicalStep g x) := rfl

theorem classicalRun_append (gs hs : List GateCode) (x : Fin m → Bool) :
    classicalRun (gs ++ hs) x = classicalRun hs (classicalRun gs x) :=
  List.foldl_append

@[simp] theorem classicalUnrun_nil (y : Fin m → Bool) : classicalUnrun [] y = y := rfl

@[simp] theorem classicalUnrun_cons (g : GateCode) (gs : List GateCode) (y : Fin m → Bool) :
    classicalUnrun (g :: gs) y = classicalStep g (classicalUnrun gs y) := rfl

theorem classicalUnrun_classicalRun {gs : List GateCode} (h : IsClassical m gs)
    (x : Fin m → Bool) : classicalUnrun gs (classicalRun gs x) = x := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨⟨h₁, h₂⟩, h⟩ := IsClassical.cons.mp h
    rw [classicalRun_cons, classicalUnrun_cons, ih h,
      classicalStep_classicalStep (target_notMem_of_wellFormed h₁ h₂)]

theorem classicalRun_classicalUnrun {gs : List GateCode} (h : IsClassical m gs)
    (y : Fin m → Bool) : classicalRun gs (classicalUnrun gs y) = y := by
  induction gs generalizing y with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨⟨h₁, h₂⟩, h⟩ := IsClassical.cons.mp h
    rw [classicalUnrun_cons, classicalRun_cons,
      classicalStep_classicalStep (target_notMem_of_wellFormed h₁ h₂), ih h]

theorem classicalRun_flatMap {β : Type*} (l : List β) (f : β → List GateCode)
    (x : Fin m → Bool) :
    classicalRun (l.flatMap f) x = l.foldl (fun y b => classicalRun (f b) y) x :=
  List.foldl_flatMap

/-- **Classical codes that never read a written bit** add to each bit the controls' values on the
initial string, one for each code writing that bit. -/
theorem readBit_classicalRun_of_forall_notMem {gs : List GateCode} (h : IsClassical m gs)
    (hread : ∀ g ∈ gs, ∀ g' ∈ gs, g.2.1 ∉ g'.2.2) (x : Fin m → Bool) (p : ℕ) :
    readBit (classicalRun gs x) p =
      gs.foldl (fun b g => b ^^ (decide (p = g.2.1) && g.2.2.all (readBit x))) (readBit x p) := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨⟨h₁, h₂⟩, h⟩ := IsClassical.cons.mp h
    have ht : g.2.1 < m := by
      obtain ⟨b, t, cs⟩ := g
      subst h₁
      exact h₂.2.2 t (List.mem_cons_self ..)
    rw [classicalRun_cons, ih h (fun g₁ hg₁ g₂ hg₂ => hread g₁ (List.mem_cons_of_mem _ hg₁) g₂
      (List.mem_cons_of_mem _ hg₂)), List.foldl_cons, readBit_classicalStep]
    simp only [ht, and_true]
    refine List.foldl_ext _ _ _ fun b g' hg' => ?_
    rw [all_readBit_classicalStep x _ (hread g (List.mem_cons_self ..) g'
      (List.mem_cons_of_mem _ hg'))]

/-- An exclusive or over a range in which only the term `i₀` can be nonzero. -/
theorem foldl_xor_range (T i₀ : ℕ) (f : ℕ → Bool) (b : Bool) (hf : ∀ i < T, i ≠ i₀ → f i = false) :
    (List.range T).foldl (fun b i => b ^^ f i) b = (b ^^ (decide (i₀ < T) && f i₀)) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [List.range_succ, List.foldl_append, ih fun i hi hne => hf i (by omega) hne]
    simp only [List.foldl_cons, List.foldl_nil]
    by_cases hT : T = i₀
    · subst hT
      simp
    · rw [hf T (by omega) hT]
      by_cases hlt : i₀ < T
      · simp [hlt, show i₀ < T + 1 by omega]
      · simp [hlt, show ¬i₀ < T + 1 by omega]

/-- A well-formed classical code denotes a gate that maps `|x⟩` to `|classicalStep g x⟩`. -/
theorem exists_toPlacedGate?_eval_ket {g : GateCode} (h₁ : g.1 = false) (h₂ : WellFormed m g) :
    ∃ pg, toPlacedGate? m g = some pg ∧ ∀ x, pg.eval (ket x) = ket (classicalStep g x) := by
  obtain ⟨pg, hpg⟩ := Option.isSome_iff_exists.mp (isSome_toPlacedGate?_iff.mpr h₂)
  obtain ⟨b, t, cs⟩ := g
  subst h₁
  have ht : t < m := h₂.2.2 t (List.mem_cons_self ..)
  refine ⟨pg, hpg, fun x => ?_⟩
  rw [eval_toPlacedGate_ket hpg ht]
  simp only [classicalStep, ht, ↓reduceDIte]
  rfl

/-- A well-formed classical code reads each amplitude at the permuted basis string. -/
theorem exists_toPlacedGate?_eval_apply {g : GateCode} (h₁ : g.1 = false) (h₂ : WellFormed m g) :
    ∃ pg, toPlacedGate? m g = some pg ∧
      ∀ (ψ : Qubits m) y, (pg.eval ψ).ofLp y = ψ.ofLp (classicalStep g y) := by
  obtain ⟨pg, hpg, hket⟩ := exists_toPlacedGate?_eval_ket h₁ h₂
  refine ⟨pg, hpg, fun ψ y => ?_⟩
  have hinv := classicalStep_classicalStep (m := m) (target_notMem_of_wellFormed h₁ h₂)
  have hrow (z : Fin m → Bool) :
      (pg.matrix : Matrix _ _ ℂ) y z = if z = classicalStep g y then 1 else 0 := by
    rw [← PlacedGate.eval_ket_apply, hket, ket_apply]
    refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
    · rw [h, hinv]
    · rw [h, hinv]
  simp only [PlacedGate.eval, unitaryEquiv_apply, Matrix.mulVec, dotProduct, hrow, ite_mul,
    one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]


/-! ### Swapping a qubit into qubit `0` -/

/-- Three CNOT gates swapping qubit `a` into qubit `0`. -/
def swapCodes (a : ℕ) : List GateCode := [(false, 0, [a]), (false, a, [0]), (false, 0, [a])]

theorem isClassical_swapCodes {N a : ℕ} (ha : 0 < a) (hN : a < N) :
    IsClassical N (swapCodes a) := by
  have h₀ : WellFormed N ((false, 0, [a]) : GateCode) :=
    ⟨by simp, by simp; omega, by simp; omega⟩
  have h₁ : WellFormed N ((false, a, [0]) : GateCode) :=
    ⟨by simp, by simp; omega, by simp; omega⟩
  intro g hg
  simp only [swapCodes, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact ⟨rfl, h₀⟩
  · exact ⟨rfl, h₁⟩
  · exact ⟨rfl, h₀⟩

/-- **The swap moves qubit `a` into qubit `0`.** -/
theorem readBit_classicalRun_swapCodes {N a : ℕ} (ha : 0 < a) (hN : a < N) (X : Fin N → Bool) :
    readBit (classicalRun (swapCodes a) X) 0 = readBit X a := by
  simp only [swapCodes, classicalRun_cons, classicalRun_nil, readBit_classicalStep,
    List.all_cons, List.all_nil, Bool.and_true]
  have h0 : (0 : ℕ) < N := by omega
  simp [h0, hN, show a ≠ 0 by omega, show (0 : ℕ) ≠ a by omega]

end GateCode

open GateCode

namespace Circuit

/-- **A classical circuit permutes basis states.** -/
theorem eval_ofCodes_ket {gs : List GateCode} (h : IsClassical m gs) (x : Fin m → Bool) :
    eval (ofCodes m gs) (ket x) = ket (classicalRun gs x) := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    obtain ⟨⟨h₁, h₂⟩, h⟩ := IsClassical.cons.mp h
    obtain ⟨pg, hpg, hket⟩ := exists_toPlacedGate?_eval_ket h₁ h₂
    simp only [ofCodes, List.filterMap_cons, hpg, eval_cons, hket, classicalRun_cons]
    exact ih h _

/-- A classical circuit started in `|x⟩` ends in `|classicalRun gs x⟩`. -/
theorem run_ofCodes {gs : List GateCode} (h : IsClassical m gs) (x : Fin m → Bool) :
    run (ofCodes m gs) x = ket (classicalRun gs x) :=
  eval_ofCodes_ket h x

/-- **A classical circuit reads amplitudes through the inverse permutation.** -/
theorem eval_ofCodes_apply {gs : List GateCode} (h : IsClassical m gs) (ψ : Qubits m)
    (y : Fin m → Bool) : (eval (ofCodes m gs) ψ).ofLp y = ψ.ofLp (classicalUnrun gs y) := by
  induction gs generalizing ψ with
  | nil => simp
  | cons g gs ih =>
    obtain ⟨⟨h₁, h₂⟩, h⟩ := IsClassical.cons.mp h
    obtain ⟨pg, hpg, happly⟩ := exists_toPlacedGate?_eval_apply h₁ h₂
    simp only [ofCodes, List.filterMap_cons, hpg, eval_cons, classicalUnrun_cons]
    rw [← happly]
    exact ih h _

/-- **Measuring after a classical circuit** is measuring before it and permuting the outcome. -/
theorem measureProb_eval_ofCodes {gs : List GateCode} (h : IsClassical m gs) (ψ : Qubits m)
    (S : Finset (Fin m → Bool)) :
    measureProb (eval (ofCodes m gs) ψ) S =
      ∑ x, if classicalRun gs x ∈ S then ‖ψ.ofLp x‖ ^ 2 else 0 := by
  rw [measureProb, ← sum_filter]
  simp only [eval_ofCodes_apply h]
  refine sum_nbij' (classicalUnrun gs) (classicalRun gs) (fun y hy => ?_) (fun x hx => ?_)
    (fun y _ => classicalRun_classicalUnrun h y) (fun x _ => classicalUnrun_classicalRun h x)
    (fun y _ => rfl)
  · simpa [classicalRun_classicalUnrun h] using hy
  · simpa using (mem_filter.mp hx).2

end Circuit

end Cslib.Quantum
