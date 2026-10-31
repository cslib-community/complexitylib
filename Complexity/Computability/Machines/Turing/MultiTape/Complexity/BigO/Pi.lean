/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pi
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp

/-!
# Parameterized resource bounds for finite tuples

Finite tuples use `encPi`, so reading, gathering, and updating fixed entries costs linear time
and space in the complete encoded input. Dimensions and index maps are fixed independently of
the input; the hidden machine constants may depend on them. Construction retains the original
input for each component and sums the supplied time and space bounds. These are asymptotic
native-machine bounds, including encoded output size, not exact transition counts.

## Main results

* `Turing.MultiTapeTM.ComputableInO.ofFn`, `.pi`: construct fixed finite families with
  arbitrary component bounds.
* `Turing.MultiTapeTM.ComputableInO.pi_apply`, `.pi_gather`, `.pi_update`: linear fixed
  tuple selection, gathering (including repeated indices), and update.

## References

Uses Christian Reitwiessner's native degree/resource calculus and list primitives.
The finite-family construction follows Complexity/PolyTime/Pi.lean, which credits the
cslib `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInO

variable {α Index Value : Type} {input : α ↪ List Bool} {enc : Value ↪ List Bool}

/-- Construct a fixed-length list, charging each computation and retention of the input. -/
theorem ofFn {count : ℕ} {values : α → Fin count → Value} {T S : Fin count → α → ℕ}
    (hvalues : ∀ i, ComputableInO (fun a => values a i) input enc (T i) (S i)) :
    ComputableInO (fun a => List.ofFn (values a)) input (encList enc)
      (fun a => (input a).length + ∑ i, T i a)
      (fun a => (input a).length + ∑ i, S i a) := by
  induction count with
  | zero => simpa using (const (encIn := input) (encMid := encList enc) [])
  | succ count ih =>
    have htail := ih (values := fun a i => values a i.succ)
      (T := fun i => T i.succ) (S := fun i => S i.succ) (fun i => hvalues i.succ)
    have h := (ComputableInDegree.cons (enc := enc)).inO_one.comp_linear
      ((hvalues 0).prod htail)
    simpa only [Function.comp_def, List.ofFn_succ, Fin.sum_univ_succ, Nat.add_left_comm] using h

/-- Construct a finite tuple from arbitrary resource certificates for its entries. -/
theorem pi [Fintype Index] {values : α → Index → Value} {T S : Index → α → ℕ}
    (hvalues : ∀ i, ComputableInO (fun a => values a i) input enc (T i) (S i)) :
    ComputableInO values input (encPi enc)
      (fun a => (input a).length + ∑ i, T i a)
      (fun a => (input a).length + ∑ i, S i a) := by
  have h := (ofFn (fun i => hvalues ((Fintype.equivFin Index).symm i))).of_enc_eq
    (encC := encPi enc) (g := values) (fun _ => rfl)
  convert h using 1 <;> funext a <;> congr 1 <;>
    exact (Equiv.sum_comp (Fintype.equivFin Index).symm _).symm

private theorem getD_fixed (fallback : Value) (n : ℕ) :
    ComputableInDegree (fun l : List Value => l.getD n fallback)
      (encList enc) enc 1 1 := by
  induction n with
  | zero =>
    convert ComputableInDegree.listHeadD enc fallback using 1
    funext l
    cases l <;> rfl
  | succ n ih =>
    convert ih.comp (ComputableInDegree.listTail enc) using 1 <;>
      first | decide | (funext l; cases l <;> simp)

/-- Read a fixed tuple entry without assuming that the value type is inhabited. -/
@[fun_prop]
theorem pi_apply [Fintype Index] (enc : Value ↪ List Bool) (i : Index) :
    ComputableInO (fun values : Index → Value => values i) (encPi enc) enc
      (fun values => (encPi enc values).length) (fun values => (encPi enc values).length) := by
  classical
  cases isEmpty_or_nonempty Value with
  | inl hempty =>
    let : IsEmpty (Index → Value) := ⟨fun values => isEmptyElim (values i)⟩
    exact (ComputableInDegree.of_finite _).inO_one
  | inr hnonempty =>
    have hlist : ComputableInDegree (fun values : Index → Value =>
        List.ofFn (fun j => values ((Fintype.equivFin Index).symm j)))
        (encPi enc) (encList enc) 1 1 := .of_eq (fun _ => rfl)
    have h := ((getD_fixed (enc := enc) (Classical.choice hnonempty)
      (Fintype.equivFin Index i).val).comp hlist).inO_one
    simpa [Function.comp_def] using h

/-- Gather fixed entries into a fixed tuple; the map need not be injective. -/
theorem pi_gather {Target : Type} [Fintype Index] [Fintype Target]
    (enc : Value ↪ List Bool) (indices : Target → Index) :
    ComputableInO (fun values : Index → Value => values ∘ indices)
      (encPi enc) (encPi enc)
      (fun values => (encPi enc values).length) (fun values => (encPi enc values).length) := by
  have h := pi (fun i => pi_apply enc (indices i))
  apply h.mono (Fintype.card Target + 1) <;> intro values <;>
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] <;> nlinarith

/-- Replace one fixed entry of a stored tuple with a stored value, preserving all other entries. -/
@[fun_prop]
theorem pi_update [Fintype Index] [DecidableEq Index] (enc : Value ↪ List Bool) (i : Index) :
    ComputableInO (fun p : (Index → Value) × Value => Function.update p.1 i p.2)
      (encPair (encPi enc) enc) (encPi enc)
      (fun p => (encPair (encPi enc) enc p).length)
      (fun p => (encPair (encPi enc) enc p).length) := by
  have h : ∀ j, ComputableInO
      (fun p : (Index → Value) × Value => Function.update p.1 i p.2 j)
      (encPair (encPi enc) enc) enc
      (fun p => (encPair (encPi enc) enc p).length)
      (fun p => (encPair (encPi enc) enc p).length) := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa using snd (encPi enc) enc
    · simpa [Function.update_of_ne hji, Function.comp_def] using
        (pi_apply enc j).comp_linear (fst (encPi enc) enc)
  apply (pi h).mono (Fintype.card Index + 1) <;> intro p <;>
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] <;> nlinarith

end Turing.MultiTapeTM.ComputableInO
