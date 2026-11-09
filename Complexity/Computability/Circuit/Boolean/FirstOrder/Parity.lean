/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.FirstOrder
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Fin
import Complexity.Computability.Circuit.Boolean.Hastad
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential
import Mathlib.Tactic.Linarith

/-!
# Parity is not first-order definable

**Parity is not first-order definable** [FurstSaxeSipser1984], [Ajtai1983], [Immerman1999],
even with arbitrary numerical relations: for a relational
language `L` with finitely many relation symbols and a unary relation symbol `P`, and any
interpretation `N n` of the symbols of `L` on each universe `Fin n`, no first-order sentence `φ`
of `L` holds, for all large `n` and all sets `S` of elements, in the structure interpreting `P`
as `S` and the other symbols as `N n` (`ModelChecking.Expansion`) exactly when `S` has an even
number of elements (`ModelChecking.not_eventually_forall_realize_expansion_iff_even`). The
numerical relations may be an order, `BIT`, or any relations at all, chosen separately for each
size of universe, so parity is not in `FO[Arb]`, the logical counterpart of nonuniform AC⁰
[Immerman1999]. In particular no sentence defines the even cardinality of `P` on all large finite
structures (`ModelChecking.not_forall_realize_iff_even_card`).

The proof combines the two directions of the correspondence between first-order logic and
constant-depth circuits. A sentence is decided on the structures with `n` elements, given by
their atomic facts, by an unbounded fan-in formula of depth independent of `n` and size
polynomial in `n` (`ModelChecking.toUnbounded`). Substituting the input bits for the facts
`P(a)` and constants for the facts about the numerical relations (`Formula.bind`,
`Formula.depth_bind_le`, `Formula.size_bind_le`, `ModelChecking.leafSize_toUnbounded_le`) gives
formulas of constant depth and polynomial size on `n` inputs computing parity, against Håstad's
theorem (`Unbounded.two_pow_le_size_of_formula_computes_parity`).

The language is relational, as in `ModelChecking.toUnbounded`, and has finitely many relation
symbols, so that a structure on `Fin n` has finitely many atomic facts. Constant symbols, such as
`min` and `max` in [Immerman1999], are not covered; a numerical constant can be expressed by a
unary numerical relation holding of one element.
The separation with genuine canonical `0`, `1`, and `max` constants, stated directly through
`FO.Ordered.Definable`, is in `Complexity.Computability.Circuit.Boolean.FirstOrder.Ordered.Parity`.

## Main definitions

* `Cslib.Circuits.Boolean.ModelChecking.Expansion`: the structure on `Fin n` interpreting `P` as a
  given set and the other relation symbols as a given structure.

## Main results

* `Cslib.Circuits.Boolean.ModelChecking.not_eventually_forall_realize_expansion_iff_even`: parity
  is not first-order definable with arbitrary numerical relations.
* `Cslib.Circuits.Boolean.ModelChecking.not_forall_realize_iff_even_card`: parity is not
  first-order definable on finite structures.

## References

* [M. Furst, J. B. Saxe, M. Sipser, *Parity, circuits, and the polynomial-time
  hierarchy*][FurstSaxeSipser1984]
* [M. Ajtai, *Σ¹₁-formulae on finite structures*][Ajtai1983]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.ModelChecking

open FirstOrder FirstOrder.Language Finset

variable {L : Language} [L.IsRelational] {n : ℕ}

/-! ### Expansions by a unary relation -/

/-- The universe `Fin n` with the structure interpreting the unary relation symbol `P` as the set
`S` and every other relation symbol as the structure `N` does: the expansion of the numerical
relations `N` by the input `S`. -/
@[nolint unusedArguments]
def Expansion (_P : L.Relations 1) (_N : L.Structure (Fin n)) (_S : Finset (Fin n)) : Type :=
  Fin n

namespace Expansion

variable {P : L.Relations 1} {N : L.Structure (Fin n)} {S : Finset (Fin n)}

open Classical in
/-- The `L`-structure on `Expansion P N S` interpreting `P` as `S` and all other relations as in
`N`. -/
instance : L.Structure (Expansion P N S) where
  funMap f := isEmptyElim f
  RelMap {l} R t :=
    if (⟨l, R⟩ : Σ l, L.Relations l) = ⟨1, P⟩ then ∀ i, (t i : Fin n) ∈ S else N.RelMap R t

open Classical in
/-- `P` holds of the elements of `S`. -/
@[simp] theorem relMap_self (t : Fin 1 → Expansion P N S) :
    Structure.RelMap P t ↔ (t 0 : Fin n) ∈ S := by
  change (if _ then _ else _) ↔ _
  rw [ite_eq_left rfl, Fin.forall_fin_one]

open Classical in
/-- The other relation symbols are interpreted as in `N`. -/
theorem relMap_of_ne {l : ℕ} {R : L.Relations l} (h : (⟨l, R⟩ : Σ l, L.Relations l) ≠ ⟨1, P⟩)
    (t : Fin l → Expansion P N S) : Structure.RelMap R t ↔ N.RelMap R t := by
  change (if _ then _ else _) ↔ _
  rw [ite_eq_right h]

end Expansion

/-! ### Parity is not first-order definable -/

open Classical in
/-- A sentence defining even cardinality of `P` over the numerical relations `N` on `Fin n` gives a
formula on `n` inputs computing parity, of depth at most `foDepth φ + 2` and polynomial size: the
translation of the sentence, reading the facts `P(a)` from the input bits and the other facts from
`N`, followed by a negation. -/
private theorem exists_formula_computes_parity [Finite (Σ l, L.Relations l)] (P : L.Relations 1)
    (N : L.Structure (Fin n)) (φ : L.Sentence)
    (h : ∀ S : Finset (Fin n), Expansion P N S ⊨ φ ↔ Even #S) :
    ∃ F : Circuits.Formula Unbounded.signature n,
      F.Computes Unbounded.interpretation (parity n) ∧ F.depth ≤ foDepth φ + 2 ∧
        F.size ≤ (foSize φ + 2) * (n + 2) ^ foSize φ := by
  have := Fintype.ofFinite (Σ l, L.Relations l)
  let e : Atom L n ≃ Fin (Fintype.card (Atom L n)) := Fintype.equivFin _
  let G := toUnbounded e φ Fin.elim0
  -- the facts `P(a)` are read from the input bits, the other facts from `N`
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
  · -- the formula computes parity
    set S : Finset (Fin n) := {i | y i = true}
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
      exact (eval_toUnbounded_atomsOf e (M := Expansion P N S) (Equiv.refl _) φ).trans (h S)
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
  · -- depth
    have h := Circuits.Formula.depth_bind_le hsubd G
    have hG : G.depth ≤ foDepth φ := depth_toUnbounded_le e φ Fin.elim0
    simp only [Circuits.Formula.depth_gate, Finset.univ_unique, Finset.sup_singleton,
      Fin.default_eq_zero, Matrix.cons_val_zero]
    omega
  · -- size
    have h := Circuits.Formula.size_bind_le hsubs G
    have hs : G.size ≤ foSize φ * (n + 2) ^ foSize φ := size_toUnbounded_le e φ Fin.elim0
    have hl : G.leafSize ≤ (n + 2) ^ foSize φ := leafSize_toUnbounded_le e φ Fin.elim0
    have hpos : 1 ≤ (n + 2) ^ foSize φ := Nat.one_le_pow _ _ (by omega)
    simp only [Circuits.Formula.size_gate, Fin.sum_univ_one, Matrix.cons_val_zero]
    nlinarith

/-- **Parity is not first-order definable, with arbitrary numerical relations**
[FurstSaxeSipser1984], [Ajtai1983], [Immerman1999]. Let `L` be a relational
language with finitely many relation symbols, `P` a unary relation symbol of `L`, and `N n` any
interpretation of the symbols of `L` on `Fin n`, for each `n`. No first-order sentence `φ` of `L`
satisfies, for all large `n` and all sets `S` of elements of `Fin n`, that the structure
interpreting `P` as `S` and the other symbols as `N n` satisfies `φ` exactly when `S` has an even
number of elements. -/
theorem not_eventually_forall_realize_expansion_iff_even [Finite (Σ l, L.Relations l)]
    (P : L.Relations 1) (N : ∀ n, L.Structure (Fin n)) (φ : L.Sentence) :
    ¬ ∀ᶠ n in Filter.atTop, ∀ S : Finset (Fin n), Expansion P (N n) S ⊨ φ ↔ Even #S := by
  intro h
  -- the lengths `s (16 s + 1) ^ (foDepth φ + 2)` grow without bound
  have htend : Filter.Tendsto (fun s => s * (16 * s + 1) ^ (foDepth φ + 2)) Filter.atTop
      Filter.atTop :=
    Filter.tendsto_atTop_mono (fun s => Nat.le_mul_of_pos_right s (by positivity))
      Filter.tendsto_id
  -- the size bound at those lengths is a polynomial in `s`
  have hpoly : PolynomiallyBounded fun s =>
      (foSize φ + 2) * (s * (16 * s + 1) ^ (foDepth φ + 2) + 2) ^ foSize φ := by
    fun_prop
  obtain ⟨s, hlt, hs, hS⟩ := (hpoly.eventually_lt_two_pow.and
    ((Filter.eventually_ge_atTop 2).and (htend.eventually h))).exists
  obtain ⟨F, hF, hFd, hFs⟩ :=
    exists_formula_computes_parity P (N (s * (16 * s + 1) ^ (foDepth φ + 2))) φ hS
  have := Unbounded.two_pow_le_size_of_formula_computes_parity hF hs
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hFd))
  omega

/-- **Parity is not first-order definable** [FurstSaxeSipser1984], [Ajtai1983], [Immerman1999].
For a relational language `L` with finitely many relation symbols and a unary relation symbol
`P`, no first-order sentence of `L` holds, among the finite structures with at least `n₀`
elements, in exactly those in which `P` holds of an even number of elements. -/
theorem not_forall_realize_iff_even_card [Finite (Σ l, L.Relations l)] (P : L.Relations 1)
    (φ : L.Sentence) (n₀ : ℕ) :
    ¬ ∀ (M : Type) [L.Structure M] [Finite M], n₀ ≤ Nat.card M →
      (M ⊨ φ ↔ Even (Nat.card {m : M // Structure.RelMap P ![m]})) := by
  intro h
  -- the numerical relations are all empty
  let N : ∀ n, L.Structure (Fin n) := fun _ => ⟨fun f => isEmptyElim f, fun _ _ => False⟩
  refine not_eventually_forall_realize_expansion_iff_even P N φ
    (Filter.eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩)
  intro S
  have : Finite (Expansion P (N n) S) := inferInstanceAs (Finite (Fin n))
  have hcard : Nat.card {m : Expansion P (N n) S // Structure.RelMap P ![m]} = #S := by
    rw [← Nat.card_eq_finsetCard S]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun m => ?_)
    rw [Expansion.relMap_self]
    rfl
  have hn' : Nat.card (Expansion P (N n) S) = n :=
    (Nat.card_eq_fintype_card (α := Fin n)).trans (Fintype.card_fin n)
  rw [← hcard]
  exact h _ (hn'.symm ▸ hn)

end Cslib.Circuits.Boolean.ModelChecking
