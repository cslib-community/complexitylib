/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Data.BitString.Parity.Weight
import CslibFrontier.Computability.Circuit.Boolean.Hastad.Sharp
import CslibFrontier.Computability.Circuit.Boolean.FirstOrder.Parity
import CslibFrontier.Computability.Circuit.Boolean.ShallowSymmetric
import CslibFrontier.Foundations.Data.BitString.Weight

/-!
# Tests for Håstad's sharp bound and the first-order undefinability of parity

Non-vacuity checks for `CslibFrontier.Computability.Circuit.Boolean.Hastad.Sharp` and
`CslibFrontier.Computability.Circuit.Boolean.FirstOrder.Parity`. Parity has circuits of every AND/OR
depth `d ≥ 2` (Lecomte–Ramakrishnan), so the hypotheses of the lower bound are satisfiable, and
together they pin the size at `2 ^ Θ(n ^ (1 / (d - 1)))`. The first-order statements are
instantiated for a concrete language with a unary predicate and an order.
-/

namespace CslibFrontierTests.HastadSharp

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

/-! ### Håstad's theorem with the sharp exponent -/

/-- **Håstad's bound is tight up to the constant in the exponent**: for every `d ≥ 2`, parity has
circuits of AND/OR depth `d` with `2 ^ O(n ^ (1 / (d - 1)))` gates, and all of them have at least
`2 ^ (n ^ (1 / (d - 1)) / 17) / 2` gates once `n ≥ 34 ^ (d - 1)`. -/
example {d : ℕ} (hd : 2 ≤ d) : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 34 ^ (d - 1) ≤ n →
    ∃ c : Circuit Unbounded.signature n 1,
      c.Computes Unbounded.interpretation (single (parity n)) ∧
        c.depthWith Unbounded.andOrCost ≤ d ∧
        (2 : ℝ) ^ ((n : ℝ) ^ (((d - 1 : ℕ) : ℝ)⁻¹) / 17) ≤ 2 * c.size ∧
        (c.size : ℝ) ≤ 2 ^ (C * (n : ℝ) ^ (((d - 1 : ℕ) : ℝ)⁻¹)) + n := by
  obtain ⟨C, hC, h⟩ := Unbounded.exists_circuit_of_isSymmetric hd
  refine ⟨C, hC, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := (Nat.one_le_pow _ _ (by norm_num)).trans hn
  obtain ⟨c, hc, hcd, -, hcs⟩ := h n hn1 _ isSymmetric_parity
  exact ⟨c, hc, hcd, Unbounded.two_rpow_le_two_mul_size_of_computes_parity hc hd hcd hn, hcs⟩

/-- Formulas in disjunctive or conjunctive normal form, and more generally circuits of AND/OR depth
two, for the parity of `1700` bits have at least `2 ^ 100` gates. -/
example (C : Circuit Unbounded.signature 1700 1)
    (hC : C.Computes Unbounded.interpretation (single (parity 1700)))
    (hd : C.depthWith Unbounded.andOrCost ≤ 2) : 2 ^ 100 ≤ C.size :=
  Unbounded.two_pow_le_size_of_computes_parity_of_pow_le hC (by norm_num) le_rfl hd (by norm_num)

/-- Circuits of AND/OR depth three for the parity of `17 ^ 2 * 100 ^ 2` bits have at least
`2 ^ 100` conjunctions and disjunctions; negations are not counted. -/
example (C : Circuit Unbounded.signature (17 ^ 2 * 100 ^ 2) 1)
    (hC : C.Computes Unbounded.interpretation (single (parity _)))
    (hd : C.depthWith Unbounded.andOrCost ≤ 3) :
    2 ^ 100 ≤ (Finset.univ.filter fun k => (C.program.lines k).op ≠ .not).card :=
  Unbounded.two_pow_le_card_andOr_of_computes_parity hC (by norm_num) hd (by norm_num)

/-- The number of conjunctions and disjunctions is the AND/OR cost of the program. -/
example (C : Circuit Unbounded.signature (17 ^ 2 * 100 ^ 2) 1)
    (hC : C.Computes Unbounded.interpretation (single (parity _)))
    (hd : C.depthWith Unbounded.andOrCost ≤ 3) :
    2 ^ 100 ≤ C.program.cost Unbounded.andOrCost :=
  Unbounded.cost_andOrCost_eq_card C.program ▸
    Unbounded.two_pow_le_card_andOr_of_computes_parity hC (by norm_num) hd (by norm_num)

/-- When depth counts negations, the bound has the same form. -/
example (C : Circuit Unbounded.signature 1700 1)
    (hC : C.Computes Unbounded.interpretation (single (parity 1700)))
    (hd : C.depth ≤ 2) : 2 ^ 100 ≤ C.size :=
  Unbounded.two_pow_le_size_of_computes_parity_of_depth_le hC (by norm_num) hd (by norm_num)

/-- When depth counts negations, in round numbers. -/
example (C : Circuit Unbounded.signature ((17 * 100) ^ 3) 1)
    (hC : C.Computes Unbounded.interpretation (single (parity _)))
    (hd : C.depth ≤ 4) : 2 ^ 100 ≤ C.size :=
  Unbounded.two_pow_le_size_of_computes_parity_of_depth_le_of_pow_le hC (by norm_num) (by norm_num)
    hd le_rfl

/-- Formulas of AND/OR depth three for the parity of `(17 · 100) ^ 2` bits have at least `2 ^ 100`
operation nodes. -/
example (F : Formula Unbounded.signature ((17 * 100) ^ 2))
    (hF : F.Computes Unbounded.interpretation (parity _))
    (hd : F.depthWith Unbounded.andOrCost ≤ 3) : 2 ^ 100 ≤ F.size :=
  Unbounded.two_pow_le_size_of_formula_computes_parity_of_pow_le hF (by norm_num) (by norm_num) hd
    le_rfl

/-- The step that ends the argument: a formula in disjunctive normal form with terms of at most
two literals does not compute the parity of three free bits, up to negation. -/
example (D : Logic.PL.DNF (Fin 3)) (hD : ∀ t ∈ D, t.length ≤ 2) (c : Bool) :
    ¬ ∀ y, D.eval y = (parity 3 y != c) := by
  have h := Logic.PL.DNF.not_forall_eval_eq_parity_fill_bne
    (ρ := BitString.PartialAssignment.empty) (D := D)
    (fun t ht => by simpa using Nat.lt_succ_of_le (hD t ht)) (by simp) c
  simpa using h

/-! ### Parity is not first-order definable -/

/-- A unary relation symbol and a binary one. -/
inductive Rel : ℕ → Type
  /-- The input predicate. -/
  | P : Rel 1
  /-- The order. -/
  | lt : Rel 2

/-- The language of a unary predicate over an order. -/
def ordLang : FirstOrder.Language :=
  ⟨fun _ => Empty, Rel⟩

instance : ordLang.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

instance : Finite (Σ l, ordLang.Relations l) :=
  Finite.of_surjective (fun b : Bool => if b then ⟨2, Rel.lt⟩ else ⟨1, Rel.P⟩) fun
    | ⟨_, .P⟩ => ⟨false, rfl⟩
    | ⟨_, .lt⟩ => ⟨true, rfl⟩

/-- The order of `Fin n`, interpreting the predicate as empty. -/
@[instance_reducible]
def order (n : ℕ) : ordLang.Structure (Fin n) where
  funMap f := isEmptyElim f
  RelMap
    | .P, _ => False
    | .lt, t => t 0 < t 1

/-- **No first-order sentence over an order defines the even subsets** of `Fin n`, for all `n`. -/
example : ¬ ∃ φ : ordLang.Sentence, ∀ n, ∀ S : Finset (Fin n),
    ModelChecking.Expansion Rel.P (order n) S ⊨ φ ↔ Even S.card := fun ⟨φ, hφ⟩ =>
  ModelChecking.not_eventually_forall_realize_expansion_iff_even Rel.P order φ
    (Filter.Eventually.of_forall hφ)

/-- The expansion interprets the predicate as the given set and keeps the order. -/
example (n : ℕ) (S : Finset (Fin n)) (a b : Fin n) :
    (FirstOrder.Language.Structure.RelMap (L := ordLang)
        (M := ModelChecking.Expansion Rel.P (order n) S) Rel.P ![a] ↔ a ∈ S) ∧
      (FirstOrder.Language.Structure.RelMap (L := ordLang)
        (M := ModelChecking.Expansion Rel.P (order n) S) Rel.lt ![a, b] ↔ a < b) :=
  ⟨ModelChecking.Expansion.relMap_self _,
    (ModelChecking.Expansion.relMap_of_ne (fun h => absurd (congrArg Sigma.fst h) (by decide))
      _).trans Iff.rfl⟩

/-- **No first-order sentence defines even cardinality of a unary predicate** on the finite
structures, even with an order symbol in the language. -/
example (φ : ordLang.Sentence) : ¬ ∀ (M : Type) [ordLang.Structure M] [Finite M],
    0 ≤ Nat.card M →
      (M ⊨ φ ↔ Even (Nat.card {m : M //
        FirstOrder.Language.Structure.RelMap (L := ordLang) Rel.P ![m]})) :=
  ModelChecking.not_forall_realize_iff_even_card Rel.P φ 0

end CslibFrontierTests.HastadSharp
