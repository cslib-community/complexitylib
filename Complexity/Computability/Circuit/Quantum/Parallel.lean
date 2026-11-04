/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Quantum.Code

/-!
# Circuits on parts of a larger register

A circuit on `m` qubits runs on the qubits `e : Fin m ↪ Fin N` of a larger register
(`Cslib.Quantum.Circuit.mapWires`). Its entries are those of the small circuit on the qubits `e`,
provided the basis strings agree off `e` (`Cslib.Quantum.Circuit.matrix_mapWires`). Copies of one
circuit on pairwise disjoint sets of qubits act independently: an entry of the whole is the product
of the entries of the copies (`Cslib.Quantum.Circuit.matrix_flatMap_mapWires`). This is the tensor
product structure behind running independent copies of a quantum computation in parallel.

For gate codes, shifting every qubit number by `o` (`Cslib.Quantum.GateCode.shift`) places the
circuit on the block of qubits `o, …, o + m - 1` (`Cslib.Quantum.Circuit.ofCodes_map_shift`).

## Main definitions

* `Cslib.Quantum.AgreeOff`: two basis strings agree off the range of an embedding.
* `Cslib.Quantum.glue`: a basis string with part of it replaced.
* `Cslib.Quantum.PlacedGate.mapWires`, `Cslib.Quantum.Circuit.mapWires`: running on a part of a
  larger register.
* `Cslib.Quantum.GateCode.shift`, `Cslib.Quantum.blockEmb`: shifted gate codes and blocks of qubits.

## Main results

* `Cslib.Quantum.sum_agreeOff`: summing over the basis strings that agree with `x` off `e`.
* `Cslib.Quantum.Circuit.matrix_mapWires`: the entries of a circuit on part of a register.
* `Cslib.Quantum.Circuit.matrix_flatMap_mapWires`: copies on disjoint parts act independently.
* `Cslib.Quantum.Circuit.ofCodes_map_shift`: shifted gate codes denote a circuit on a block.
* `Cslib.Quantum.GateCode.WellFormed.shift`: shifted gate codes are well formed on a larger
  register.
-/

@[expose] public section

namespace Cslib.Quantum

open Finset

variable {ι : Type*} {m N : ℕ}

/-! ### Agreeing off part of a register -/


/-- The basis strings `y` and `x` **agree off** the qubits `e`. -/
def AgreeOff (e : ι ↪ Fin N) (y x : Fin N → Bool) : Prop :=
  ∀ j, (∀ i, e i ≠ j) → y j = x j

instance [Fintype ι] (e : ι ↪ Fin N) (y x : Fin N → Bool) : Decidable (AgreeOff e y x) := by
  unfold AgreeOff; infer_instance

theorem AgreeOff.refl (e : ι ↪ Fin N) (x : Fin N → Bool) : AgreeOff e x x := fun _ _ => rfl

theorem AgreeOff.symm {e : ι ↪ Fin N} {y x : Fin N → Bool} (h : AgreeOff e y x) :
    AgreeOff e x y := fun j hj => (h j hj).symm

theorem AgreeOff.trans {e : ι ↪ Fin N} {z y x : Fin N → Bool} (h₁ : AgreeOff e z y)
    (h₂ : AgreeOff e y x) : AgreeOff e z x := fun j hj => (h₁ j hj).trans (h₂ j hj)

section Glue

variable [Fintype ι]

/-- The basis string `x` with the bits `z` on the qubits `e`. -/
noncomputable def glue (e : ι ↪ Fin N) (z : ι → Bool) (x : Fin N → Bool) : Fin N → Bool :=
  fun j => if h : ∃ i, e i = j then z h.choose else x j

@[simp] theorem glue_apply_emb (e : ι ↪ Fin N) (z : ι → Bool) (x : Fin N → Bool) (i : ι) :
    glue e z x (e i) = z i := by
  have h : ∃ i', e i' = e i := ⟨i, rfl⟩
  rw [glue, dite_eq_left h, e.injective h.choose_spec]

theorem glue_of_not (e : ι ↪ Fin N) (z : ι → Bool) (x : Fin N → Bool) {j : Fin N}
    (hj : ∀ i, e i ≠ j) : glue e z x j = x j := by
  rw [glue, dite_eq_right (by simpa using hj)]

@[simp] theorem glue_comp (e : ι ↪ Fin N) (z : ι → Bool) (x : Fin N → Bool) :
    glue e z x ∘ e = z :=
  funext fun i => glue_apply_emb e z x i

theorem agreeOff_glue (e : ι ↪ Fin N) (z : ι → Bool) (x : Fin N → Bool) :
    AgreeOff e (glue e z x) x := fun _ hj => glue_of_not e z x hj

theorem glue_comp_of_agreeOff {e : ι ↪ Fin N} {y x : Fin N → Bool} (h : AgreeOff e y x) :
    glue e (y ∘ e) x = y := by
  funext j
  by_cases hj : ∃ i, e i = j
  · obtain ⟨i, rfl⟩ := hj
    simp
  · push Not at hj
    rw [glue_of_not e _ x hj, h j hj]

/-- **Summing over the basis strings that agree with `x` off `e`** is summing over their bits on
`e`. -/
theorem sum_agreeOff [DecidableEq ι] {R : Type*} [AddCommMonoid R] (e : ι ↪ Fin N)
    (x : Fin N → Bool) (H : (Fin N → Bool) → R) :
    ∑ y, (if AgreeOff e y x then H y else 0) = ∑ z : ι → Bool, H (glue e z x) := by
  rw [← sum_filter]
  refine sum_nbij' (· ∘ e) (glue e · x) (fun _ _ => mem_univ _)
    (fun z _ => mem_filter.mpr ⟨mem_univ _, agreeOff_glue e z x⟩)
    (fun y hy => glue_comp_of_agreeOff (mem_filter.mp hy).2) (fun z _ => glue_comp e z x)
    (fun y hy => by rw [glue_comp_of_agreeOff (mem_filter.mp hy).2])

/-- Summing a function of the bits on `e` over the basis strings that agree with `x` off `e`. -/
theorem sum_agreeOff_comp [DecidableEq ι] {R : Type*} [AddCommMonoid R]
    (e : ι ↪ Fin N) (x : Fin N → Bool) (F : (ι → Bool) → R) :
    ∑ y, (if AgreeOff e y x then F (y ∘ e) else 0) = ∑ z, F z := by
  rw [sum_agreeOff e x fun y => F (y ∘ e)]
  simp

end Glue

/-! ### Circuits on part of a register -/

/-- The placed gate `g` on the qubits `e` of a larger register. -/
def PlacedGate.mapWires (e : Fin m ↪ Fin N) (g : PlacedGate m) : PlacedGate N :=
  ⟨g.arity, g.gate, g.wires.trans e⟩

/-- **The entries of a gate on part of a register** are those of the gate on the qubits `e`, when
the basis strings agree off `e`. -/
theorem PlacedGate.matrix_mapWires (e : Fin m ↪ Fin N) (g : PlacedGate m) (y x : Fin N → Bool) :
    ((g.mapWires e).matrix : Matrix _ _ ℂ) y x =
      if AgreeOff e y x then (g.matrix : Matrix _ _ ℂ) (y ∘ e) (x ∘ e) else 0 := by
  rw [matrix_apply, matrix_apply]
  have hiff : (∀ j, (¬∃ i, (g.mapWires e).wires i = j) → y j = x j) ↔
      AgreeOff e y x ∧ ∀ j, (¬∃ i, g.wires i = j) → (y ∘ e) j = (x ∘ e) j := by
    constructor
    · intro h
      refine ⟨fun j hj => h j ?_, fun j hj => h (e j) ?_⟩
      · rintro ⟨i, rfl⟩
        exact hj _ rfl
      · rintro ⟨i, hi⟩
        exact hj ⟨i, e.injective hi⟩
    · rintro ⟨h₁, h₂⟩ j hj
      by_cases hj' : ∃ j', e j' = j
      · obtain ⟨j', rfl⟩ := hj'
        exact h₂ j' fun ⟨i, hi⟩ => hj ⟨i, by rw [← hi]; rfl⟩
      · exact h₁ j fun i hi => hj' ⟨i, hi⟩
  rw [if_congr hiff rfl rfl, ite_and]
  rfl

/-- A circuit maps the basis state `|x⟩` to its column `x`. -/
theorem Circuit.eval_ket_apply (C : Circuit m) (x y : Fin m → Bool) :
    (Circuit.eval C (ket x)).ofLp y = (Circuit.matrix C : Matrix _ _ ℂ) y x := by
  simp [Circuit.eval, Matrix.mulVec, dotProduct]

/-- A circuit on `m` qubits with a list of gate codes; the codes of a concatenation of lists. -/
theorem Circuit.ofCodes_flatMap {β : Type*} (l : List β) (f : β → List GateCode) :
    Circuit.ofCodes m (l.flatMap f) = l.flatMap fun b => Circuit.ofCodes m (f b) := by
  induction l with
  | nil => rfl
  | cons b l ih => rw [List.flatMap_cons, List.flatMap_cons, Circuit.ofCodes_append, ih]

/-- The circuit `C` on the qubits `e` of a larger register. -/
def Circuit.mapWires (e : Fin m ↪ Fin N) (C : Circuit m) : Circuit N :=
  C.map (PlacedGate.mapWires e)

@[simp] theorem Circuit.mapWires_nil (e : Fin m ↪ Fin N) : Circuit.mapWires e [] = [] := rfl

@[simp] theorem Circuit.mapWires_cons (e : Fin m ↪ Fin N) (g : PlacedGate m) (C : Circuit m) :
    Circuit.mapWires e (g :: C) = g.mapWires e :: Circuit.mapWires e C := rfl

/-- **The entries of a circuit on part of a register** are those of the circuit on the qubits `e`,
when the basis strings agree off `e`. -/
theorem Circuit.matrix_mapWires (e : Fin m ↪ Fin N) (C : Circuit m) (y x : Fin N → Bool) :
    (Circuit.matrix (Circuit.mapWires e C) : Matrix _ _ ℂ) y x =
      if AgreeOff e y x then (Circuit.matrix C : Matrix _ _ ℂ) (y ∘ e) (x ∘ e) else 0 := by
  induction C generalizing y x with
  | nil =>
    simp only [mapWires_nil, matrix_nil, OneMemClass.coe_one, Matrix.one_apply]
    by_cases hyx : y = x
    · subst hyx
      simp [AgreeOff.refl]
    · rw [ite_eq_right hyx]
      split_ifs with h h'
      · exact absurd (by rw [← glue_comp_of_agreeOff h, h', glue_comp_of_agreeOff
          (AgreeOff.refl e x)]) hyx
      · rfl
      · rfl
  | cons g C ih =>
    simp only [mapWires_cons, matrix_cons, Submonoid.coe_mul, Matrix.mul_apply, ih,
      PlacedGate.matrix_mapWires, ite_mul, zero_mul, mul_ite, mul_zero]
    split_ifs with hyx
    · have hiff (z : Fin N → Bool) : AgreeOff e y z ↔ AgreeOff e z x :=
        ⟨fun h => h.symm.trans hyx, fun h => hyx.trans h.symm⟩
      simp only [hiff, ← ite_and, and_self]
      exact sum_agreeOff_comp e x fun w => (Circuit.matrix C : Matrix _ _ ℂ) (y ∘ e) w *
        (g.matrix : Matrix _ _ ℂ) w (x ∘ e)
    · refine sum_eq_zero fun z _ => ?_
      split_ifs with h₁ h₂ <;> first | rfl | exact absurd (h₂.trans h₁) hyx

/-- **Copies of a circuit on disjoint parts of a register act independently**: an entry of the
whole is the product of the entries of the copies, when the basis strings agree off all parts. -/
theorem Circuit.matrix_flatMap_mapWires (C : Circuit m) (L : List (Fin m ↪ Fin N))
    (hL : L.Pairwise fun e e' => ∀ i i', e i ≠ e' i') (y x : Fin N → Bool) :
    (Circuit.matrix (L.flatMap (Circuit.mapWires · C)) : Matrix _ _ ℂ) y x =
      if ∀ j, (∀ e ∈ L, ∀ i, e i ≠ j) → y j = x j then
        (L.map fun e : Fin m ↪ Fin N => (Circuit.matrix C : Matrix _ _ ℂ) (y ∘ ⇑e) (x ∘ ⇑e)).prod
      else 0 := by
  induction L generalizing y x with
  | nil =>
    simp only [List.flatMap_nil, matrix_nil, OneMemClass.coe_one, Matrix.one_apply,
      List.not_mem_nil, IsEmpty.forall_iff, implies_true, forall_const, List.map_nil,
      List.prod_nil, funext_iff]
  | cons e L ih =>
    obtain ⟨he, hL⟩ := List.pairwise_cons.mp hL
    rw [List.flatMap_cons, matrix_append, Submonoid.coe_mul, Matrix.mul_apply]
    simp only [ih hL, matrix_mapWires, ite_mul, zero_mul, mul_ite, mul_zero, ← ite_and]
    -- the only intermediate basis string is `y` on `e` and `x` elsewhere
    set z₀ : Fin N → Bool := fun j => if ∃ i, e i = j then y j else x j
    have hdisj (e' : Fin m ↪ Fin N) (he' : e' ∈ L) (i i' : Fin m) : e' i ≠ e i' :=
      fun h => he e' he' i' i h.symm
    rw [sum_eq_single z₀]
    · have hz₀e : z₀ ∘ e = y ∘ e := funext fun i => ite_eq_left ⟨i, rfl⟩
      have hz₀x : AgreeOff e z₀ x := fun j hj => ite_eq_right (by simpa using hj)
      have hz₀L (e' : Fin m ↪ Fin N) (he' : e' ∈ L) : z₀ ∘ e' = x ∘ e' :=
        funext fun i => ite_eq_right fun ⟨i', hi'⟩ => hdisj e' he' i i' hi'.symm
      have hcond : (∀ j, (∀ e' ∈ L, ∀ i, e' i ≠ j) → y j = z₀ j) ↔
          ∀ j, (∀ e' ∈ e :: L, ∀ i, e' i ≠ j) → y j = x j := by
        constructor
        · intro h j hj
          have := h j fun e' he' => hj e' (List.mem_cons_of_mem _ he')
          rwa [show z₀ j = x j from
            ite_eq_right (by simpa using fun i => hj e (List.mem_cons_self ..) i)] at this
        · intro h j hj
          by_cases hj' : ∃ i, e i = j
          · exact (ite_eq_left hj').symm
          · rw [show z₀ j = x j from ite_eq_right hj']
            refine h j fun e' he' => ?_
            rcases List.mem_cons.mp he' with rfl | he'
            · simpa using hj'
            · exact hj e' he'
      simp only [hz₀x, true_and, hcond, hz₀e, List.map_cons, List.prod_cons]
      split_ifs
      · rw [List.map_congr_left fun e' he' => by rw [hz₀L e' he'], mul_comm]
      · rfl
    · intro z _ hz
      refine ite_eq_right fun ⟨h₁, h₂⟩ => hz (funext fun j => ?_)
      by_cases hj : ∃ i, e i = j
      · rw [show z₀ j = y j from ite_eq_left hj]
        obtain ⟨i, rfl⟩ := hj
        exact (h₂ (e i) fun e' he' i' => hdisj e' he' i' i).symm
      · rw [show z₀ j = x j from ite_eq_right hj]
        exact h₁ j (by simpa using hj)
    · exact fun h => absurd (mem_univ _) h

/-! ### Shifted gate codes -/

/-- The gate code `g` with every qubit number increased by `o`. -/
def GateCode.shift (o : ℕ) (g : GateCode) : GateCode := (g.1, g.2.1 + o, g.2.2.map (· + o))

/-- The block of qubits `o, …, o + m - 1` of an `N`-qubit register. -/
def blockEmb (o : ℕ) (h : o + m ≤ N) : Fin m ↪ Fin N :=
  ⟨fun i => ⟨i + o, by omega⟩, fun i j hij => Fin.ext (by simpa using congrArg Fin.val hij)⟩

@[simp] theorem blockEmb_apply_val (o : ℕ) (h : o + m ≤ N) (i : Fin m) :
    (blockEmb o h i : ℕ) = i + o := rfl

/-- **A shifted well-formed gate code denotes the gate on the shifted block.** -/
theorem GateCode.toPlacedGate?_shift {o : ℕ} (h : o + m ≤ N) {g : GateCode}
    (hg : WellFormed m g) :
    toPlacedGate? N (g.shift o) = (toPlacedGate? m g).map (PlacedGate.mapWires (blockEmb o h)) := by
  have key {k : ℕ} (U : Gate k) (A : Fin k ↪ Fin m) (A' : Fin k ↪ Fin N)
      (hA : ∀ i, (A' i : ℕ) = A i + o) :
      (⟨k, U, A'⟩ : PlacedGate N) = PlacedGate.mapWires (blockEmb o h) ⟨k, U, A⟩ := by
    simp only [PlacedGate.mapWires, PlacedGate.mk.injEq, heq_eq_eq, true_and]
    exact Function.Embedding.ext fun i => Fin.ext (hA i)
  match g, hg with
  | (true, t, []), hg =>
    have ht : t < m := hg.1
    simp only [shift, toPlacedGate?, ht, ↓reduceDIte, show t + o < N by omega, Option.map_some,
      List.map_nil, Option.some.injEq]
    exact key _ _ _ fun i => by fin_cases i; rfl
  | (true, t, _ :: _), hg => exact absurd hg.2 (List.cons_ne_nil _ _)
  | (false, t, []), hg =>
    have ht : t < m := hg.2.2 t (List.mem_cons_self ..)
    simp only [shift, toPlacedGate?, ht, ↓reduceDIte, show t + o < N by omega, Option.map_some,
      List.map_nil, Option.some.injEq]
    exact key _ _ _ fun i => by fin_cases i; rfl
  | (false, t, [c]), hg =>
    obtain ⟨-, hnd, hlt⟩ := hg
    have ht : t < m := hlt t (by simp)
    have hc : c < m := hlt c (by simp)
    have hct : c ≠ t := by simp at hnd; omega
    simp only [shift, toPlacedGate?, List.map_cons, List.map_nil,
      dite_eq_left (show c < m ∧ t < m ∧ c ≠ t from ⟨hc, ht, hct⟩),
      dite_eq_left (show c + o < N ∧ t + o < N ∧ c + o ≠ t + o by omega), Option.map_some,
      Option.some.injEq]
    exact key _ _ _ fun i => by fin_cases i <;> rfl
  | (false, t, [c₁, c₂]), hg =>
    obtain ⟨-, hnd, hlt⟩ := hg
    have ht : t < m := hlt t (by simp)
    have hc₁ : c₁ < m := hlt c₁ (by simp)
    have hc₂ : c₂ < m := hlt c₂ (by simp)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
      not_false_eq_true, and_true] at hnd
    simp only [shift, toPlacedGate?, List.map_cons, List.map_nil,
      dite_eq_left (show c₁ < m ∧ c₂ < m ∧ t < m ∧ c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t by omega),
      dite_eq_left (show c₁ + o < N ∧ c₂ + o < N ∧ t + o < N ∧ c₁ + o ≠ c₂ + o ∧ c₁ + o ≠ t + o ∧
        c₂ + o ≠ t + o by omega), Option.map_some, Option.some.injEq]
    exact key _ _ _ fun i => by fin_cases i <;> rfl
  | (false, t, _ :: _ :: _ :: _), hg => exact absurd hg.1 (by simp)

/-- A well-formed gate code, shifted by `o`, is well formed on a register of at least `o + m`
qubits. -/
theorem GateCode.WellFormed.shift {o : ℕ} (h : o + m ≤ N) {g : GateCode} (hg : WellFormed m g) :
    WellFormed N (g.shift o) := by
  obtain ⟨_ | _, t, cs⟩ := g
  · obtain ⟨hlen, hnd, hlt⟩ := hg
    refine ⟨by simpa [GateCode.shift] using hlen, ?_, ?_⟩
    · simpa [GateCode.shift, List.map_cons] using
        hnd.map (f := (· + o)) (fun a b hab => by simpa using hab)
    · intro i hi
      simp only [List.mem_cons, List.mem_map] at hi
      rcases hi with rfl | ⟨c, hc, rfl⟩
      · have := hlt t (List.mem_cons_self ..)
        omega
      · have := hlt c (List.mem_cons_of_mem _ hc)
        omega
  · obtain ⟨ht, rfl⟩ := hg
    exact ⟨show t + o < N by omega, rfl⟩

/-- **Shifted gate codes denote the circuit on a block**: shifting a well-formed circuit's qubit
numbers by `o` runs it on the qubits `o, …, o + m - 1`. -/
theorem Circuit.ofCodes_map_shift {o : ℕ} (h : o + m ≤ N) {gs : List GateCode}
    (hgs : ∀ g ∈ gs, GateCode.WellFormed m g) :
    Circuit.ofCodes N (gs.map (GateCode.shift o)) =
      (Circuit.ofCodes m gs).mapWires (blockEmb o h) := by
  simp only [ofCodes, mapWires, List.filterMap_map, List.map_filterMap]
  exact List.filterMap_congr fun g hg => GateCode.toPlacedGate?_shift h (hgs g hg)

end Cslib.Quantum
