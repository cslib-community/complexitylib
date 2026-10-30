/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.Query
public import Mathlib.SetTheory.Cardinal.Finite
import Complexity.Computability.Circuit.Boolean.FirstOrder.Ordered
import Complexity.Computability.Circuit.Boolean.FirstOrder.Parity
import Complexity.Computability.Circuit.Boolean.AC0
import Complexity.Computability.Languages.Slice
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-!
# Parity is not definable in the canonical ordered vocabulary

No sentence with the canonical numeric constants `0`, `1`, and `max`, weak order, and `BIT`
defines even cardinality of a unary input relation on all ordered structures of size at least
two. This states the parity separation directly in `FO.Ordered.Definable`.

The proof compiles a hypothetical defining sentence with `ModelChecking.Ordered.toUnbounded`,
fixes the other input relations, and obtains polynomial-size constant-depth formulas for parity.
Their circuits contradict the existing `parity_notMem_AC0` theorem. The two input lengths excluded
by the ordered-structure convention are supplied by a constant circuit and an input wire.
Numeric constants are genuine function symbols with interpretations determined by the universe
size; only original relation tables supply input bits. No uniformity theorem is used.

## Main results

* `Cslib.Circuits.Boolean.ModelChecking.Ordered.not_definable_even_card`: even cardinality of a
  unary input relation is not definable by a canonical ordered first-order sentence.

## References

* [M. Furst, J. B. Saxe, M. Sipser, *Parity, circuits, and the polynomial-time
  hierarchy*][FurstSaxeSipser1984]
* [M. Ajtai, *Σ¹₁-formulae on finite structures*][Ajtai1983]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]

The result here is the canonical-structure corollary of the library's parity circuit lower bound;
it includes the genuine numeric constants excluded by the relational-only separation.
-/

public section

namespace Cslib.Circuits.Boolean.ModelChecking.Ordered

open FirstOrder FirstOrder.Language Finset
open Cslib.Logic.FO.Ordered (language)

variable {L : Language} [L.IsRelational] [Finite (Σ l, L.Relations l)] {n : ℕ}

/-- Compiling and restricting an ordered sentence defining even cardinality gives small,
bounded-depth formulas for parity. -/
private theorem exists_formula_computes_parity [Fact (2 ≤ n)] (P : L.Relations 1)
    (N : L.Structure (Fin n)) (φ : (language L).Sentence)
    (h : ∀ S : Finset (Fin n),
      letI : L.Structure (Fin n) := inferInstanceAs (L.Structure (Expansion P N S));
      Fin n ⊨ φ ↔ Even #S) :
    ∃ F : Circuits.Formula Unbounded.signature n,
      F.Computes Unbounded.interpretation (parity n) ∧ F.depth ≤ foDepth φ + 2 ∧
        F.size ≤ (foSize φ + 2) * (n + 2) ^ foSize φ := by
  classical
  have := Fintype.ofFinite (Σ l, L.Relations l)
  let e : Atom L n ≃ Fin (Fintype.card (Atom L n)) := Fintype.equivFin _
  let G := toUnbounded e φ Fin.elim0
  let sub : Fin (Fintype.card (Atom L n)) → Circuits.Formula Unbounded.signature n := fun j =>
    if (e.symm j).1 = ⟨1, P⟩ then .gate (.and _) fun i => .input ((e.symm j).2 i)
    else constUnbounded (decide (N.RelMap (e.symm j).1.2 (e.symm j).2))
  have hsubd : ∀ j, (sub j).depth ≤ 1 := fun j => by
    simp only [sub, constUnbounded]
    split_ifs <;> simp
  have hsubs : ∀ j, (sub j).size ≤ 1 := fun j => by
    simp only [sub, constUnbounded]
    split_ifs <;> simp
  refine ⟨.gate .not ![G.bind sub], fun y => ?_, ?_, ?_⟩
  · set S : Finset (Fin n) := {i | y i = true}
    let : L.Structure (Fin n) := inferInstanceAs (L.Structure (Expansion P N S))
    have hatoms : (fun j => (sub j).eval Unbounded.interpretation y) =
        atomsOf (L := L) (M := Expansion P N S) (Equiv.refl _) ∘ e.symm := by
      funext j
      simp only [sub, Function.comp_apply, atomsOf]
      obtain ⟨⟨l, R⟩, t⟩ := e.symm j
      by_cases hR : (⟨l, R⟩ : Σ l, L.Relations l) = ⟨1, P⟩
      · rw [ite_eq_left hR]
        refine Bool.eq_iff_iff.2 ?_
        simp only [Circuits.Formula.eval_gate, Circuits.Formula.eval_input,
          Unbounded.interpretation_and, decide_eq_true_iff]
        change _ ↔ (if _ then _ else _)
        rw [ite_eq_left hR]
        refine forall_congr' fun i => ?_
        change _ ↔ t i ∈ S
        simp [S]
      · rw [ite_eq_right hR]
        refine Bool.eq_iff_iff.2 ?_
        simp only [eval_constUnbounded, decide_eq_true_iff]
        exact (Expansion.relMap_of_ne hR _).symm
    have hreal : (G.bind sub).eval Unbounded.interpretation y = true ↔ Even #S := by
      rw [Circuits.Formula.eval_bind, hatoms]
      refine (eval_toUnbounded_atomsOf e φ Fin.elim0).trans ?_
      rw [Subsingleton.elim (Empty.elim : Empty → Fin n) default,
        Subsingleton.elim (Fin.elim0 : Fin 0 → Fin n) default]
      exact h S
    simp only [Circuits.Formula.eval_gate, Unbounded.interpretation_not, Matrix.cons_val_zero]
    change _ = decide (#S % 2 = 1)
    rw [Nat.even_iff] at hreal
    cases hv : (G.bind sub).eval Unbounded.interpretation y
    · rw [hv] at hreal
      have : #S % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one #S with h0 | h1
        · exact absurd (hreal.2 h0) (by simp)
        · exact h1
      simp [this]
    · have := hreal.1 hv
      simp [this]
  · have h := Circuits.Formula.depth_bind_le hsubd G
    have hG : G.depth ≤ foDepth φ := depth_toUnbounded_le e φ Fin.elim0
    simp only [Circuits.Formula.depth_gate, Finset.univ_unique, Finset.sup_singleton,
      Fin.default_eq_zero, Matrix.cons_val_zero]
    omega
  · have h := Circuits.Formula.size_bind_le hsubs G
    have hs : G.size ≤ foSize φ * (n + 2) ^ foSize φ := size_toUnbounded_le e φ Fin.elim0
    have hl : G.leafSize ≤ (n + 2) ^ foSize φ := leafSize_toUnbounded_le e φ Fin.elim0
    have hpos : 1 ≤ (n + 2) ^ foSize φ := Nat.one_le_pow _ _ (by omega)
    simp only [Circuits.Formula.size_gate, Fin.sum_univ_one, Matrix.cons_val_zero]
    nlinarith

/-- **Parity is not definable in canonical ordered first-order logic.** In any finite relational
input vocabulary with a unary relation `P`, no sentence using canonical `≤`, `BIT`, `0`, `1`, and
`max` defines even cardinality of `P` on all ordered structures of size at least two. -/
theorem not_definable_even_card (P : L.Relations 1) :
    ¬ Cslib.Logic.FO.Ordered.Definable {M : Cslib.Logic.FO.Ordered.Structure L |
      Even (Nat.card {x : M // Structure.RelMap P ![x]})} := by
  classical
  rintro ⟨φ, hφ⟩
  apply parity_notMem_AC0
  refine ConstDepth.mem_iff.2
    ⟨foDepth φ + 2, fun n => (foSize φ + 2) * (n + 2) ^ foSize φ, by fun_prop, fun n => ?_⟩
  rw [_root_.Language.slice_ofSlices]
  suffices ∃ F : Circuits.Formula Unbounded.signature n,
      F.Computes Unbounded.interpretation (parity n) ∧ F.depth ≤ foDepth φ + 2 ∧
        F.size ≤ (foSize φ + 2) * (n + 2) ^ foSize φ by
    obtain ⟨F, hF, hd, hs⟩ := this
    exact ⟨F.toCircuit, hF.toCircuit, F.depth_toCircuit_le.trans hd, by simpa using hs⟩
  by_cases hn : 2 ≤ n
  · let : Fact (2 ≤ n) := ⟨hn⟩
    let N : L.Structure (Fin n) := ⟨fun f => isEmptyElim f, fun _ _ => False⟩
    refine exists_formula_computes_parity P N φ fun S => ?_
    let : L.Structure (Fin n) := inferInstanceAs (L.Structure (Expansion P N S))
    let M : Cslib.Logic.FO.Ordered.Structure L :=
      ⟨n, hn, inferInstanceAs (L.Structure (Expansion P N S))⟩
    have hcard : Nat.card {x : M // Structure.RelMap P ![x]} = #S := by
      rw [← Nat.card_eq_finsetCard S]
      refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
      exact Expansion.relMap_self (P := P) (N := N) (S := S) ![x]
    have hM := (hφ M).symm
    change (Fin n ⊨ φ) ↔ Even (Nat.card {x : M // Structure.RelMap P ![x]}) at hM
    rwa [hcard] at hM
  · have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl
    · refine ⟨constUnbounded false, ?_, ?_, ?_⟩
      · intro x
        simp [parity]
      · simp [constUnbounded]
      · have hpow : 1 ≤ (0 + 2) ^ foSize φ := Nat.one_le_pow _ _ (by omega)
        simp only [constUnbounded, Bool.false_eq_true, ↓reduceIte, Circuits.Formula.size_gate]
        simpa using (show 1 ≤ (foSize φ + 2) * (0 + 2) ^ foSize φ by nlinarith)
    · refine ⟨.input 0, ?_, by simp, by simp⟩
      intro x
      simp [parity, Finset.univ_unique, Fin.default_eq_zero]

end Cslib.Circuits.Boolean.ModelChecking.Ordered
