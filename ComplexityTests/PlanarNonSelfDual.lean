/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Logics.Propositional.CSP.Planar.OneInThree

/-! Concrete clients of the arbitrary-arity construction and the ordered NAND triangle.
No geometric embedding or running-time certificate is asserted by these tests. -/

namespace ComplexityTests.PlanarNonSelfDual

open Cslib Cslib.BitString Cslib.Logic Cslib.Logic.PL Cslib.Logic.PL.CSP
open Cslib.Logic.PL.CSP.RelationMinor Cslib.Logic.PL.CSP.NonSelfDual

private inductive Symbol where
  | zero | one | positive | negative | nullary | empty
  deriving DecidableEq

private def arity : Symbol → ℕ
  | .zero | .one => 1
  | .positive | .negative => 3
  | .nullary => 0
  | .empty => 4

private def sem : Symbol → List Bool → Bool
  | .zero, [a] => !a
  | .one, [a] => a
  | .positive, [a, b, c] => a || b || c
  | .negative, [a, b, c] => !(a && b && c)
  | .nullary, [] => true
  | _, _ => false

private instance (s : Symbol) : DecidablePred (· ∈ booleanRelation arity sem s) := fun x =>
  inferInstanceAs (Decidable (sem s (List.ofFn x) = true))

-- Separate relations witness the six failures. In particular no single symbol fails both
-- unary constants. Empty and nullary symbols remain in the language.
private theorem not_schaefer : ¬HasSchaeferPolymorphism arity sem := by
  intro h
  rcases h with h | h | h | h | h | h
  · have hh := h .one (fun _ => ![true]) (by intro j; rfl)
    exact Bool.false_ne_true hh
  · have hh := h .zero (fun _ => ![false]) (by intro j; rfl)
    exact Bool.false_ne_true hh
  · have hh := h .positive ![![true, false, false], ![false, true, false]] (by decide)
    exact Bool.false_ne_true hh
  · have hh := h .negative ![![true, true, false], ![false, false, true]] (by decide)
    exact Bool.false_ne_true hh
  · have hh := h .positive
      ![![true, false, false], ![false, true, false], ![false, false, true]] (by decide)
    exact Bool.false_ne_true hh
  · have hh := h .positive
      ![![true, false, false], ![false, true, false], ![true, true, false]] (by decide)
    exact Bool.false_ne_true hh

private theorem not_complement : ¬HasPolymorphism arity sem
    (fun a : Fin 1 → Bool => !(a 0)) := by
  intro h
  have hh := h .zero (fun _ => ![false]) (by intro j; rfl)
  exact Bool.false_ne_true hh

example : Available arity sem nand := (witnesses not_schaefer not_complement).2.2.1

example : ∀ b, Available arity sem (pin b) :=
  (witnesses not_schaefer not_complement).2.1

-- A concrete trace, rather than just an invocation of the existence theorem: pin the last
-- input of NAND3 to one and retain the order of the first two ports.
private theorem negative_cofactor :
    cofactor (booleanRelation arity sem .negative) (2 : Fin 3) true = nand := by
  ext x
  have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
  rw [hx]
  generalize x 0 = a, x 1 = b
  cases a <;> cases b <;> unfold cofactor booleanRelation nand <;> decide

example : Nonempty (Trace (booleanRelation arity sem .negative) nand) :=
  ⟨negative_cofactor ▸ Trace.cofactor .refl 2 true⟩

-- Sparse original variable labels and repeated scopes use the original CSP evaluator.
example : CSP.eval sem
    (F := ([(Symbol.negative, [7, 7, 2 ^ 80])] : CSP Symbol ℕ))
    (fun i => i == 7) = true := by decide

example : CSP.eval sem
    (F := ([(Symbol.negative, [7, 7, 7])] : CSP Symbol ℕ))
    (fun _ => true) = false := by decide

example : IsPolymorphism (parity 3) (∅ : Set (Fin 17 → Bool)) := by
  intro a ha
  exact (ha 0).elim

example (R : Set (Fin 0 → Bool)) : IsPolymorphism (majority 3) R :=
  majority_preserves_of_arity_le_two (by decide)

example : project (∅ : Set (Fin 8 → Bool)) 3 = ∅ := by
  ext x
  simp [project]

example : cofactor (Set.univ : Set (Fin 1 → Bool)) 0 true = Set.univ := by
  ext x
  simp [cofactor]

-- Adjacent restriction deletes the first port immediately and keeps the remaining order.
example : ![true, false] ∈ adjacent
    ({x : Fin 3 → Bool | x 0 = false ∧ x 1 = true}) true := by
  unfold adjacent
  decide

example : ![true, false] ∉ adjacent
    ({x : Fin 3 → Bool | x 0 = false ∧ x 1 = true}) false := by
  unfold adjacent
  decide

example : ![true, true] ∈ twist nand (Pi.single 0 true) := by decide
example : ![false, true] ∉ twist nand (Pi.single 0 true) := by decide

-- Rotation is cyclic, rather than a reversal of the ordered ports.
example : ![false, true, false] ∈ rotate
    ({x : Fin 3 → Bool | x 0 = true ∧ x 1 = false}) := by
  unfold rotate
  decide

-- The same API applies to a sparse seventeen-port relation, with no bounded-arity premise.
private def largeRelation : Set (Fin 17 → Bool) := {x | (x 0 || x 7 || x 16) = true}

private instance : DecidablePred (· ∈ largeRelation) := fun x =>
  inferInstanceAs (Decidable ((x 0 || x 7 || x 16) = true))

example : Nonempty (Trace largeRelation nand) := by
  apply exists_nand_trace
  intro h
  have hh := h ![Pi.single 0 true, Pi.single 7 true,
      Pi.single 0 true + Pi.single 7 true] (by decide)
  exact Bool.false_ne_true hh

example : ∃ R : Set (Fin 3 → Bool), Nonempty (Trace largeRelation R) ∧
    (0 : Fin 3 → Bool) ∉ R ∧ (∀ i, Pi.single i true ∈ R) := by
  apply exists_majority_minor
  intro h
  have hh := h ![Pi.single 0 true, Pi.single 7 true, Pi.single 16 true] (by decide)
  exact Bool.false_ne_true hh

-- The gate forbids zero and pairs of true bits, and accepts every single true bit.
private abbrev positive : Set (Fin 3 → Bool) := booleanRelation arity sem .positive

private instance : DecidablePred (· ∈ positive) := fun x =>
  inferInstanceAs (Decidable (sem .positive (List.ofFn x) = true))

private theorem positive_zero : (0 : Fin 3 → Bool) ∉ positive := by decide

private theorem positive_units : ∀ i, Pi.single i true ∈ positive := by decide

example : ∃ b, (triangle positive positive_zero positive_units).body.eval
    (triangleSem positive) (Sum.elim ![false, true, false] b) = true := by
  apply ((triangle positive positive_zero positive_units).correct _).mp
  exact ⟨1, by decide⟩

example : triangleBody.eval (triangleSem positive)
    (Sum.elim ![true, false, false] (fun _ => false)) = true := by decide

example : triangleBody.eval (triangleSem positive)
    (Sum.elim ![false, true, false] (fun _ => false)) = true := by decide

example : triangleBody.eval (triangleSem positive)
    (Sum.elim ![false, false, true] (fun _ => false)) = true := by decide

example : triangleBody.eval (triangleSem positive)
    (Sum.elim ![false, false, false] (fun _ => false)) = false := by decide

example : triangleBody.eval (triangleSem positive)
    (Sum.elim ![true, false, true] (fun _ => false)) = false := by decide

-- The final pair is (2,0); rejecting 101 checks the cyclic wraparound edge.
example : triangleBody[3] = (.nand, [.inl 2, .inl 0]) := rfl

end ComplexityTests.PlanarNonSelfDual
