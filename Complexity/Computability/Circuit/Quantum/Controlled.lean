/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Quantum.Classical
public import Complexity.Foundations.Quantum.Measurement.Restrict

/-!
# Controlled circuits

A circuit whose gates never act on qubit `j` never changes it: its entries vanish between basis
strings that differ at `j` (`Cslib.Quantum.Circuit.matrix_eq_zero_of_ne`). Such a circuit therefore
commutes with projecting onto a value of `j` (`Cslib.Quantum.Circuit.eval_projOutcomes_bit`). Every
well-formed gate code is its own inverse, so running a list of codes backwards undoes it
(`Cslib.Quantum.Circuit.eval_ofCodes_reverse`).

A circuit `C` is the circuit `D` **controlled by qubit `c`** (`Cslib.Quantum.Circuit.IsControlled`)
when it does nothing on the basis strings with `c = 0` and runs `D` on those with `c = 1`. Adding
the control `c` to classical codes (NOT becomes CNOT, CNOT becomes Toffoli) controls their circuit
(`Cslib.Quantum.Circuit.isControlled_addControl`). Conjugating a controlled circuit by codes that
do not touch `c` gives the controlled conjugate (`Cslib.Quantum.Circuit.IsControlled.conj`). This
is how [Shi][Shi2003], §4.2, realizes `Λ(T_θ)` from `Λ₂(σ_x)` and single-qubit gates: with
`T = H[a] Λ(σ_x)[a, b] H[a]`, the codes `H[a] Λ₂(σ_x)[c, a; b] H[a]` are `T` controlled by `c`.
This `T` is a variant of Shi's `T_{π/4} = U_{-π/4}[a] Λ(σ_x)[a, b] U_{π/4}[a] = σ_x[b] T`, without
the final `σ_x` on the target: a real involution with the same entry `⟨00|T|00⟩ = cos² (π/4)`.
Controlled circuits compose (`Cslib.Quantum.Circuit.IsControlled.append`).

## Main definitions

* `Cslib.Quantum.Circuit.IsControlled`: one circuit is another controlled by a qubit.
* `Cslib.Quantum.GateCode.addControl`: a classical gate code with an extra control.

## Main results

* `Cslib.Quantum.Circuit.matrix_eq_zero_of_ne`: a circuit never changes a qubit it does not act on.
* `Cslib.Quantum.Circuit.eval_projOutcomes`, `Cslib.Quantum.Circuit.eval_projOutcomes_bit`:
  circuits commute with projections they respect.
* `Cslib.Quantum.Circuit.eval_ofCodes_reverse`: running well-formed codes backwards undoes them.
* `Cslib.Quantum.Circuit.IsControlled.append`, `Cslib.Quantum.Circuit.IsControlled.conj`,
  `Cslib.Quantum.Circuit.isControlled_addControl`: building controlled circuits.

## References

* [Y. Shi, *Both Toffoli and Controlled-NOT need little help to do universal quantum
  computation*][Shi2003], §4.2 (arXiv:quant-ph/0205115v2)
-/

@[expose] public section

namespace Cslib.Quantum

open Finset Matrix

variable {m : ℕ}

/-! ### Qubits a circuit does not act on -/

/-- A placed gate's entry vanishes between basis strings that differ at a qubit it does not act
on. -/
theorem PlacedGate.matrix_eq_zero_of_ne (g : PlacedGate m) {j : Fin m} (hj : ∀ i, g.wires i ≠ j)
    {y x : Fin m → Bool} (h : y j ≠ x j) : (g.matrix : Matrix _ _ ℂ) y x = 0 := by
  rw [matrix_apply, ite_eq_right]
  exact fun hall => h (hall j fun ⟨i, hi⟩ => hj i hi)

/-- **A circuit never changes a qubit none of its gates acts on**: its entries vanish between
basis strings that differ there. -/
theorem Circuit.matrix_eq_zero_of_ne {C : Circuit m} {j : Fin m}
    (hC : ∀ g ∈ C, ∀ i, g.wires i ≠ j) {y x : Fin m → Bool} (h : y j ≠ x j) :
    (matrix C : Matrix _ _ ℂ) y x = 0 := by
  induction C generalizing y x with
  | nil =>
    rw [matrix_nil, Submonoid.coe_one, Matrix.one_apply_ne fun hyx => h (congrFun hyx j)]
  | cons g C ih =>
    rw [matrix_cons, Submonoid.coe_mul, Matrix.mul_apply]
    refine sum_eq_zero fun z _ => ?_
    by_cases hz : y j = z j
    · rw [g.matrix_eq_zero_of_ne (hC g (List.mem_cons_self ..)) (hz ▸ h), mul_zero]
    · rw [ih (fun g' hg' => hC g' (List.mem_cons_of_mem _ hg')) hz, zero_mul]

/-- **A circuit commutes with projecting onto `p`** when its nonzero entries connect only basis
strings on which `p` agrees. -/
theorem Circuit.eval_projOutcomes {C : Circuit m} (p : (Fin m → Bool) → Prop) [DecidablePred p]
    (hp : ∀ y x, (matrix C : Matrix _ _ ℂ) y x ≠ 0 → (p y ↔ p x)) (ψ : Qubits m) :
    eval C (projOutcomes p ψ) = projOutcomes p (eval C ψ) := by
  ext y
  simp only [eval, unitaryEquiv_apply, projOutcomes_apply, mulVec, dotProduct]
  split_ifs with hy
  · refine sum_congr rfl fun x _ => ?_
    by_cases hx : p x
    · rw [ite_eq_left hx]
    · rw [ite_eq_right hx, not_imp_comm.mp (hp y x) (fun h => hx (h.mp hy)), zero_mul, zero_mul]
  · refine sum_eq_zero fun x _ => ?_
    by_cases hx : p x
    · rw [not_imp_comm.mp (hp y x) (fun h => hy (h.mpr hx)), zero_mul]
    · rw [ite_eq_right hx, mul_zero]

/-- A circuit none of whose gates acts on qubit `j` commutes with projecting onto a value of
`j`. -/
theorem Circuit.eval_projOutcomes_bit {C : Circuit m} {j : Fin m}
    (hC : ∀ g ∈ C, ∀ i, g.wires i ≠ j) (b : Bool) (ψ : Qubits m) :
    eval C (projOutcomes (fun y => y j = b) ψ) = projOutcomes (fun y => y j = b) (eval C ψ) :=
  eval_projOutcomes _ (fun y x hyx => by
    rw [not_not.mp (mt (matrix_eq_zero_of_ne hC) hyx)]) ψ

namespace GateCode

/-- The qubits of the gate denoted by a code are among the qubits the code names. -/
theorem wires_mem_of_toPlacedGate? {g : GateCode} {pg : PlacedGate m}
    (h : toPlacedGate? m g = some pg) (i : Fin pg.arity) :
    (pg.wires i : ℕ) ∈ g.2.1 :: g.2.2 := by
  match g, h with
  | (true, t, []), h =>
    simp only [toPlacedGate?] at h
    split_ifs at h with ht
    cases h
    fin_cases i
    exact List.mem_cons_self ..
  | (false, t, []), h =>
    simp only [toPlacedGate?] at h
    split_ifs at h with ht
    cases h
    fin_cases i
    exact List.mem_cons_self ..
  | (false, t, [c]), h =>
    simp only [toPlacedGate?] at h
    split_ifs at h with ht
    cases h
    fin_cases i <;> simp
  | (false, t, [c₁, c₂]), h =>
    simp only [toPlacedGate?] at h
    split_ifs at h with ht
    cases h
    fin_cases i <;> simp
  | (true, t, _ :: _), h => simp [toPlacedGate?] at h
  | (false, t, _ :: _ :: _ :: _), h => simp [toPlacedGate?] at h

/-- **A well-formed gate is its own inverse.** -/
theorem eval_eval_of_toPlacedGate? {g : GateCode} {pg : PlacedGate m} (hg : WellFormed m g)
    (h : toPlacedGate? m g = some pg) (ψ : Qubits m) : pg.eval (pg.eval ψ) = ψ := by
  obtain ⟨_ | _, t, cs⟩ := g
  · obtain ⟨pg', hpg', happly⟩ := exists_toPlacedGate?_eval_apply rfl hg
    obtain rfl : pg = pg' := Option.some.inj (h.symm.trans hpg')
    ext y
    rw [happly, happly, classicalStep_classicalStep (target_notMem_of_wellFormed rfl hg)]
  · obtain ⟨ht, rfl⟩ := hg
    simp only [toPlacedGate?, ht, ↓reduceDIte, Option.some.injEq] at h
    subst h
    rw [PlacedGate.eval, ← unitaryEquiv_mul, PlacedGate.matrix, ← map_mul, Gate.hadamard_mul_self,
      map_one, unitaryEquiv_one]

/-! ### Classical codes run backwards -/

theorem IsClassical.reverse {gs : List GateCode} (h : IsClassical m gs) :
    IsClassical m gs.reverse := fun g hg => h g (List.mem_reverse.mp hg)

/-- Undoing classical codes is running them backwards. -/
theorem classicalUnrun_eq_classicalRun_reverse (gs : List GateCode) (y : Fin m → Bool) :
    classicalUnrun gs y = classicalRun gs.reverse y := by
  rw [classicalRun, List.foldl_reverse]
  rfl

/-- Undoing classical codes run backwards is running them. -/
theorem classicalUnrun_reverse (gs : List GateCode) (y : Fin m → Bool) :
    classicalUnrun gs.reverse y = classicalRun gs y := by
  rw [classicalUnrun, List.foldr_reverse]
  rfl

/-- Classical codes none of which targets `q` leave bit `q` unchanged when undone. -/
theorem readBit_classicalUnrun_of_forall_ne {gs : List GateCode} {q : ℕ}
    (h : ∀ g ∈ gs, g.2.1 ≠ q) (y : Fin m → Bool) :
    readBit (classicalUnrun gs y) q = readBit y q := by
  rw [classicalUnrun_eq_classicalRun_reverse]
  exact readBit_classicalRun_of_forall_ne (fun g hg => h g (List.mem_reverse.mp hg)) y

end GateCode

open GateCode

namespace Circuit

/-- The gates of `ofCodes m gs` act only on qubits that the codes `gs` name. -/
theorem wires_ne_of_ofCodes {gs : List GateCode} {j : Fin m}
    (h : ∀ g ∈ gs, (j : ℕ) ∉ g.2.1 :: g.2.2) : ∀ pg ∈ ofCodes m gs, ∀ i, pg.wires i ≠ j := by
  intro pg hpg i hi
  obtain ⟨g, hg, hpg⟩ := List.mem_filterMap.mp hpg
  exact h g hg (hi ▸ wires_mem_of_toPlacedGate? hpg i)

/-- **Running well-formed codes backwards undoes them.** -/
theorem eval_ofCodes_reverse {gs : List GateCode} (h : ∀ g ∈ gs, WellFormed m g)
    (ψ : Qubits m) : eval (ofCodes m gs.reverse) (eval (ofCodes m gs) ψ) = ψ := by
  induction gs generalizing ψ with
  | nil => simp
  | cons g gs ih =>
    obtain ⟨pg, hpg⟩ := Option.isSome_iff_exists.mp
      (isSome_toPlacedGate?_iff.mpr (h g (List.mem_cons_self ..)))
    rw [List.reverse_cons, ofCodes_append, eval_append]
    simp only [ofCodes, List.filterMap_cons, hpg, eval_cons, List.filterMap_nil, eval_nil]
    rw [show eval (List.filterMap (toPlacedGate? m) gs.reverse)
      (eval (List.filterMap (toPlacedGate? m) gs) (pg.eval ψ)) = pg.eval ψ from
      ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) _]
    exact eval_eval_of_toPlacedGate? (h g (List.mem_cons_self ..)) hpg ψ

/-- Running well-formed codes forwards undoes running them backwards. -/
theorem eval_ofCodes_of_reverse {gs : List GateCode} (h : ∀ g ∈ gs, WellFormed m g)
    (ψ : Qubits m) : eval (ofCodes m gs) (eval (ofCodes m gs.reverse) ψ) = ψ := by
  simpa using eval_ofCodes_reverse (gs := gs.reverse)
    (fun g hg => h g (List.mem_reverse.mp hg)) ψ

/-! ### Controlled circuits -/

/-- The circuit `C` is the circuit `D` **controlled by qubit `c`**: it does nothing on the basis
strings with `c = 0` and runs `D` on those with `c = 1`. -/
def IsControlled (c : Fin m) (C D : Circuit m) : Prop :=
  ∀ ψ, eval C ψ =
    projOutcomes (fun y => y c = false) ψ + eval D (projOutcomes (fun y => y c = true) ψ)

theorem IsControlled.nil (c : Fin m) : IsControlled c [] [] := fun ψ => by
  rw [eval_nil, eval_nil]
  convert (projOutcomes_add_projOutcomes_not (fun y => y c = false) ψ).symm using 3
  simp

private theorem projOutcomes_bit_projOutcomes_bit (c : Fin m) (b b' : Bool) (ψ : Qubits m) :
    projOutcomes (fun y => y c = b) (projOutcomes (fun y => y c = b') ψ) =
      if b = b' then projOutcomes (fun y => y c = b) ψ else 0 := by
  ext y
  simp only [projOutcomes_apply]
  split_ifs <;> simp_all

/-- **Controlled circuits compose**, provided the first circuit being controlled does not act on
the control. -/
theorem IsControlled.append {c : Fin m} {C₁ C₂ D₁ D₂ : Circuit m} (h₁ : IsControlled c C₁ D₁)
    (h₂ : IsControlled c C₂ D₂) (hD₁ : ∀ g ∈ D₁, ∀ i, g.wires i ≠ c) :
    IsControlled c (C₁ ++ C₂) (D₁ ++ D₂) := fun ψ => by
  rw [eval_append, h₁, h₂, map_add, map_add, ← eval_projOutcomes_bit hD₁,
    ← eval_projOutcomes_bit hD₁]
  simp [projOutcomes_bit_projOutcomes_bit, eval_append]

/-- **Conjugating a controlled circuit** by well-formed codes that do not touch the control qubit
gives the conjugated circuit, controlled. -/
theorem IsControlled.conj {c : Fin m} {A : List GateCode} {C D : Circuit m}
    (hA : ∀ g ∈ A, WellFormed m g) (hAc : ∀ g ∈ A, (c : ℕ) ∉ g.2.1 :: g.2.2)
    (h : IsControlled c C D) :
    IsControlled c (ofCodes m A ++ C ++ ofCodes m A.reverse)
      (ofCodes m A ++ D ++ ofCodes m A.reverse) := fun ψ => by
  have hw := wires_ne_of_ofCodes hAc
  rw [eval_append, eval_append, h, ← eval_projOutcomes_bit hw, ← eval_projOutcomes_bit hw,
    map_add, eval_ofCodes_reverse hA, eval_append, eval_append]

end Circuit

namespace GateCode

/-- The classical code `g` with the extra control qubit `c`: NOT becomes CNOT and CNOT becomes
Toffoli. -/
def addControl (c : ℕ) (g : GateCode) : GateCode := (g.1, g.2.1, c :: g.2.2)

/-- An extra control qubit `c` makes a classical code act only when `c` is one. -/
theorem classicalStep_addControl (g : GateCode) (c : Fin m) (y : Fin m → Bool) :
    classicalStep (addControl c g) y = if y c then classicalStep g y else y := by
  refine funext_readBit fun j => ?_
  rw [readBit_classicalStep]
  by_cases hc : y c
  · rw [ite_eq_left hc, readBit_classicalStep]
    by_cases h₁ : j = g.2.1 <;> by_cases h₂ : g.2.1 < m <;> simp [addControl, hc, h₁, h₂]
  · rw [ite_eq_right hc]
    simp [addControl, hc]

theorem classicalUnrun_addControl {gs : List GateCode} {c : Fin m}
    (h : ∀ g ∈ gs, g.2.1 ≠ c) (y : Fin m → Bool) :
    classicalUnrun (gs.map (addControl c)) y = if y c then classicalUnrun gs y else y := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    rw [List.map_cons, classicalUnrun_cons, classicalUnrun_cons,
      ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')), classicalStep_addControl]
    by_cases hc : y c
    · have hU : classicalUnrun gs y c = y c := by
        simpa using readBit_classicalUnrun_of_forall_ne
          (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) y
      simp only [hc, ite_true, hU]
    · simp only [hc, Bool.false_eq_true, ite_false]

/-- Classical codes with an extra control are classical only if the codes without it are, and
then no code targets the control. -/
theorem isClassical_of_addControl {gs : List GateCode} {c : ℕ}
    (h : IsClassical m (gs.map (addControl c))) : IsClassical m gs ∧ ∀ g ∈ gs, g.2.1 ≠ c := by
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩ <;>
  · obtain ⟨b, t, cs⟩ := g
    obtain ⟨h₁, hw⟩ := h _ (List.mem_map_of_mem hg)
    simp only [addControl] at h₁ hw
    subst h₁
    obtain ⟨hlen, hnd, hlt⟩ := hw
    simp only [List.length_cons, List.nodup_cons, List.mem_cons, not_or, List.mem_cons,
      forall_eq_or_imp] at hlen hnd hlt
    first
    | exact ⟨rfl, by omega, List.nodup_cons.mpr ⟨hnd.1.2, hnd.2.2⟩,
        List.forall_mem_cons.mpr ⟨hlt.1, hlt.2.2⟩⟩
    | exact hnd.1.1

end GateCode

namespace Circuit

/-- **Adding a control qubit to classical codes controls their circuit.** -/
theorem isControlled_addControl {gs : List GateCode} {c : Fin m}
    (h : IsClassical m (gs.map (addControl c))) :
    IsControlled c (ofCodes m (gs.map (addControl c))) (ofCodes m gs) := fun ψ => by
  obtain ⟨hgs, hne⟩ := isClassical_of_addControl h
  ext y
  rw [eval_ofCodes_apply h, WithLp.ofLp_add, Pi.add_apply, projOutcomes_apply,
    eval_ofCodes_apply hgs, projOutcomes_apply, classicalUnrun_addControl hne]
  have hU : classicalUnrun gs y c = y c := by
    simpa using readBit_classicalUnrun_of_forall_ne hne y
  by_cases hc : y c <;> simp [hc, hU]

end Circuit

end Cslib.Quantum
