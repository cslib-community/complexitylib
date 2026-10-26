/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Pi
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Option


import Diag1155.Measure
/-!
# Native tuple and retained-input option clients

Tests include empty dimensions and payload types, repeated gathering indices, stored updates,
arbitrary component bounds, and a concrete option client using both input and payload.
-/


diag1155_install
@[expose] public section

open Turing.MultiTapeTM

namespace ComplexityTests.NativeProducts

example (empty : Empty ↪ List Bool) :
    ComputableTidilyInO (fun _ : ℕ => fun i : Fin 0 => Fin.elim0 i) encUnary (encPi empty)
      (fun n => (encUnary n).length) (fun n => (encUnary n).length) := by
  simpa using ComputableTidilyInO.pi (input := encUnary) (enc := empty)
    (values := fun _ : ℕ => fun i : Fin 0 => (Fin.elim0 i : Empty))
    (T := fun _ _ => 0) (S := fun _ _ => 0) (fun i => Fin.elim0 i)

example (empty : Empty ↪ List Bool) :
    ComputableTidilyInO (fun v : Fin 1 → Empty => v 0) (encPi empty) empty
      (fun v => (encPi empty v).length) (fun v => (encPi empty v).length) := by
  fun_prop

-- Repeated indices are permitted and the complete stored tuple is charged.
example : ComputableTidilyInO (fun v : Fin 2 → ℕ => fun _ : Fin 3 => v 1)
    (encPi encUnary) (encPi encUnary)
    (fun v => (encPi encUnary v).length) (fun v => (encPi encUnary v).length) :=
  ComputableTidilyInO.pi_gather encUnary (fun _ => 1)

example : ComputableTidilyInO (fun _v : Fin 2 → ℕ => fun i : Fin 0 => Fin.elim0 i)
    (encPi encUnary) (encPi encUnary)
    (fun v => (encPi encUnary v).length) (fun v => (encPi encUnary v).length) :=
  ComputableTidilyInO.pi_gather encUnary (fun i => Fin.elim0 i)

example : ComputableTidilyInO (fun p : (Fin 2 → ℕ) × ℕ => Function.update p.1 1 p.2)
    (encPair (encPi encUnary) encUnary) (encPi encUnary)
    (fun p => (encPair (encPi encUnary) encUnary p).length)
    (fun p => (encPair (encPi encUnary) encUnary p).length) := by
  fun_prop

example {f : ℕ → Fin 2 → ℕ} {T S : Fin 2 → ℕ → ℕ}
    (h : ∀ i, ComputableTidilyInO (fun n => f n i) encUnary encUnary (T i) (S i)) :
    ComputableTidilyInO f encUnary (encPi encUnary)
      (fun n => (encUnary n).length + ∑ i, T i n)
      (fun n => (encUnary n).length + ∑ i, S i n) :=
  ComputableTidilyInO.pi h

-- A genuine two-entry construction and a read-after-update compose as native certificates.
example : ComputableTidilyInO (fun n : ℕ => fun _ : Fin 2 => n) encUnary (encPi encUnary)
    (fun n => 3 * (encUnary n).length) (fun n => 3 * (encUnary n).length) := by
  have h := ComputableTidilyInO.pi
    (Index := Fin 2) (fun _ => (ComputableTidilyInDegree.id' (enc := encUnary)).inO_one)
  convert h using 1 <;> funext n <;> simp only [Fin.sum_univ_two] <;> omega

example : ComputableTidilyInO
    (fun p : (Fin 2 → ℕ) × ℕ => Function.update p.1 1 p.2 1)
    (encPair (encPi encUnary) encUnary) encUnary
    (fun p => (encPair (encPi encUnary) encUnary p).length)
    (fun p => (encPair (encPi encUnary) encUnary p).length) :=
  (ComputableTidilyInO.pi_apply encUnary (1 : Fin 2)).comp_linear
    (ComputableTidilyInO.pi_update encUnary 1)

/-- Option input with an independent number retained by both handlers. -/
def inputEncoding : ℕ × Option ℕ ↪ List Bool := encPair encUnary (encOption encUnary)

/-- The `some` handler combines the retained input and payload; `none` copies the retained input. -/
def retained (q : ℕ × Option ℕ) : ℕ × ℕ := q.2.elim (q.1, q.1) (fun n => (q.1, n))

/-- Conservative selected-handler bound supplied by the native option rule. -/
def retainedCost (q : ℕ × Option ℕ) : ℕ :=
  3 * (inputEncoding q).length + q.2.elim (2 * (inputEncoding q).length)
    (fun n => (encPair inputEncoding encUnary (q, n)).length)

/-- A nonvacuous native certificate, with input retention and payload extraction charged. -/
theorem retained_inO : ComputableTidilyInO retained inputEncoding (encPair encUnary encUnary)
    retainedCost retainedCost := by
  have hvalue := ComputableTidilyInO.snd encUnary (encOption encUnary)
  have hfst := ComputableTidilyInO.fst encUnary (encOption encUnary)
  have hbody : ComputableTidilyInDegree
      (fun p : (ℕ × Option ℕ) × ℕ => (p.1.1, p.2))
      (encPair inputEncoding encUnary) (encPair encUnary encUnary) 1 1 := by
    unfold inputEncoding
    fun_prop (disch := first | apply le_refl | omega)
  have h := ComputableTidilyInO.optionElimWithInput
    (body := fun q n => (q.1, n)) hvalue (hfst.prod hfst) hbody.inO_one
  convert h using 1 <;> first | rfl |
    (funext q; simp only [retainedCost, inputEncoding, two_mul]; omega)

example : retained (3, none) = (3, 3) := rfl
example : retained (3, some 7) = (3, 7) := rfl

-- An empty payload type does not obstruct elimination on an inhabited input type.
example (empty : Empty ↪ List Bool) : ComputableTidilyInO
    (fun n : ℕ => (none : Option Empty).elim n (fun e => Empty.elim e)) encUnary encUnary
    (fun n => 4 * (encUnary n).length) (fun n => 4 * (encUnary n).length) := by
  have hb : ComputableTidilyInO (fun p : ℕ × Empty => Empty.elim p.2)
      (encPair encUnary empty) encUnary
      (fun p => (encPair encUnary empty p).length)
      (fun p => (encPair encUnary empty p).length) :=
    (ComputableTidilyInDegree.of_finite _).inO_one
  have h := ComputableTidilyInO.optionElimWithInput (body := fun _ e => Empty.elim e)
    (ComputableTidilyInO.const (encIn := encUnary) (encMid := encOption empty) none)
    (ComputableTidilyInDegree.id' (enc := encUnary)).inO_one hb
  convert h using 1 <;> funext n <;> simp only [Option.elim_none] <;> omega

end ComplexityTests.NativeProducts
