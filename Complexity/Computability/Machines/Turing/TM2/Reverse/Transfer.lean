/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.TM2.Reverse.Bounds
public import Complexity.Computability.Machines.Turing.TM2.Recoding
public import Complexity.Computability.Complexity.Classes.Space.TM2

/-!
# Resource transfer from multi-tape machines to Mathlib stack machines

Polynomial time transfers from an ordinary binary multi-tape computation, without a tidy
normal form or a polynomial source-space hypothesis. Polynomial space transfers independently
of runtime when the output length is polynomially bounded. In particular, Boolean computations
need only termination and a polynomial work-space bound.

All stack alphabets of the resulting Mathlib certificates are finite. Target stack bounds count
the input and output, whereas native space counts only visited work-tape cells. The equivalences
preserve the caller's binary encodings and impose no computable-inverse hypothesis on them.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.exists_tm2ComputableInPolyTime`.
* `Turing.MultiTapeTM.ComputableInPolySpace.exists_tm2Computable`.
* `Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_tm2Computable_bool`.
* `Turing.MultiTapeTM.computableInPolyTime_iff_tm2`.
* `Turing.MultiTapeTM.computableInPolySpace_iff_tm2`.
* `Cslib.Complexity.mem_PSPACE_iff_tm2`.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.1][Sipser2013]
-/

public section

namespace Turing.MultiTapeTM

noncomputable section

variable {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
  {f : α → β} {t s : α → ℕ}

/-- Polynomial native time gives a Mathlib polynomial-time certificate with finite working
alphabets. No polynomial bound on native space is needed. -/
theorem ComputableInTimeAndSpace.exists_tm2ComputableInPolyTime
    (h : ComputableInTimeAndSpace f encIn encOut t s)
    (ht : PolyBounded (fun a => (encIn a).length) t) :
    ∃ h : TM2ComputableInPolyTime encIn encOut f, ∀ stack, Finite (h.tm.Γ stack) := by
  obtain ⟨k, State, hfinite, tm, htm⟩ := h
  let : Fintype State := Fintype.ofFinite State
  have htime : PolyBounded (fun a => (encIn a).length)
      (fun a => (encIn a).length + (k + 1) * (t a + 1) + (encOut (f a)).length + 3) :=
    ((PolyBounded.self.add ((PolyBounded.const (k + 1)).mul (ht.add (.const 1)))).add
      (ht.mono fun a => (htm a).length_output_le)).add (.const 3)
  obtain ⟨p, hp⟩ := htime.exists_polynomial
  let target : TM2ComputableInPolyTime encIn encOut f := {
    tm := ToTM2.machine tm.q₀ tm.tr
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := p
    outputsFun a := by
      simp only [Equiv.refl, List.map_id]
      have hrun := ToTM2.outputsInTime tm (htm a).1 (htm a).2.1
      exact ⟨hrun.toEvalsTo, hrun.steps_le_m.trans (hp a)⟩ }
  exact ⟨target, fun stack => inferInstance⟩

/-- Polynomial-time computation has a finite-alphabet Mathlib certificate under the same
binary encodings. -/
theorem ComputableInPolyTime.exists_tm2ComputableInPolyTime
    (h : ComputableInPolyTime f encIn encOut) :
    ∃ h : TM2ComputableInPolyTime encIn encOut f, ∀ stack, Finite (h.tm.Γ stack) := by
  obtain ⟨t, s, ht, _, h⟩ := h
  exact h.exists_tm2ComputableInPolyTime (.of_polynomiallyBounded _ ht)

/-- Polynomial native space and explicitly polynomial output length give a terminating Mathlib
certificate with polynomially bounded reachable stacks. Runtime is unrestricted. -/
theorem ComputableInTimeAndSpace.exists_tm2Computable
    (h : ComputableInTimeAndSpace f encIn encOut t s)
    (hs : PolyBounded (fun a => (encIn a).length) s)
    (hout : PolyBounded (fun a => (encIn a).length) fun a => (encOut (f a)).length) :
    ∃ h : TM2Computable encIn encOut f, (∀ stack, Finite (h.tm.Γ stack)) ∧
      ∃ space : α → ℕ, PolyBounded (fun a => (encIn a).length) space ∧
        h.StacksBounded space := by
  obtain ⟨k, State, hfinite, tm, htm⟩ := h
  let : Fintype State := Fintype.ofFinite State
  let target : TM2Computable encIn encOut f := {
    tm := ToTM2.machine tm.q₀ tm.tr
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    outputsFun a := by
      simpa only [Equiv.refl, List.map_id] using
        ToTM2.outputs tm (htm a).1 }
  refine ⟨target, fun stack => inferInstance,
    (fun a => (encIn a).length + s a + (encOut (f a)).length),
    (PolyBounded.self.add hs).add hout, ?_⟩
  intro a i stack
  have htotal := ToTM2.reachable_stack_bound tm (htm a).1 (htm a).2.2 i
  have hsingle : (((TM2.stepTotal (ToTM2.machine tm.q₀ tm.tr).m)^[i]
      (initList (ToTM2.machine tm.q₀ tm.tr) (encIn a))).stk stack).length ≤
      ToTM2.totalStackLength ((TM2.stepTotal (ToTM2.machine tm.q₀ tm.tr).m)^[i]
        (initList (ToTM2.machine tm.q₀ tm.tr) (encIn a))) := by
    unfold ToTM2.totalStackLength
    exact Finset.single_le_sum (f := fun stack =>
      (((TM2.stepTotal (ToTM2.machine tm.q₀ tm.tr).m)^[i]
        (initList (ToTM2.machine tm.q₀ tm.tr) (encIn a))).stk stack).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ stack)
  simpa only [target, Equiv.refl_symm, Equiv.coe_refl, List.map_id] using hsingle.trans htotal

/-- For a Boolean computation the output is one bit, so only the native work-space bound needs
to be supplied. The native time bound may be arbitrary. -/
theorem ComputableInTimeAndSpace.exists_tm2Computable_bool {f : α → Bool}
    (h : ComputableInTimeAndSpace f encIn encBool t s)
    (hs : PolyBounded (fun a => (encIn a).length) s) :
    ∃ h : TM2Computable encIn encBool f, (∀ stack, Finite (h.tm.Γ stack)) ∧
      ∃ space : α → ℕ, PolyBounded (fun a => (encIn a).length) space ∧
        h.StacksBounded space :=
  h.exists_tm2Computable hs (by simpa using (PolyBounded.const (size :=
    fun a => (encIn a).length) 1))

/-- A polynomial-space computation transfers with all target stacks polynomially bounded.
The source notion explicitly bounds the encoded output length. -/
theorem ComputableInPolySpace.exists_tm2Computable
    (h : ComputableInPolySpace f encIn encOut) :
    ∃ h : TM2Computable encIn encOut f, (∀ stack, Finite (h.tm.Γ stack)) ∧
      ∃ space : α → ℕ, PolyBounded (fun a => (encIn a).length) space ∧
        h.StacksBounded space := by
  obtain ⟨t, s, hs, h, hout⟩ := h
  have hspace := PolyBounded.of_polynomiallyBounded (fun a => (encIn a).length) hs
  exact h.exists_tm2Computable hspace (hspace.mono hout)

/-- Polynomial-time computability is the same for native multi-tape machines and Mathlib stack
machines with finite working alphabets, under the original binary encodings. -/
theorem computableInPolyTime_iff_tm2 :
    ComputableInPolyTime f encIn encOut ↔
      ∃ h : TM2ComputableInPolyTime encIn encOut f, ∀ stack, Finite (h.tm.Γ stack) := by
  refine ⟨ComputableInPolyTime.exists_tm2ComputableInPolyTime, ?_⟩
  rintro ⟨h, hfinite⟩
  let := hfinite
  exact h.computableInPolyTime

/-- Polynomial-space computability is equivalent to termination with polynomially bounded
reachable Mathlib stacks. This equivalence also applies to functions with non-Boolean outputs:
the stack bound already includes the entire output. -/
theorem computableInPolySpace_iff_tm2 :
    ComputableInPolySpace f encIn encOut ↔
      ∃ h : TM2Computable encIn encOut f, (∀ stack, Finite (h.tm.Γ stack)) ∧
        ∃ space : α → ℕ, PolyBounded (fun a => (encIn a).length) space ∧
          h.StacksBounded space := by
  refine ⟨ComputableInPolySpace.exists_tm2Computable, ?_⟩
  rintro ⟨h, hfinite, space, hspace, hstacks⟩
  let := hfinite
  exact h.computableInPolySpace hspace hstacks

end

end Turing.MultiTapeTM

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

/-- PSPACE is exactly Boolean Mathlib stack-machine computation with finite alphabets and a
polynomial bound on every reachable stack, under the original binary input encoding. -/
theorem mem_PSPACE_iff_tm2 {α : Type} {encIn : α ↪ List Bool} {A : Set α} :
    A ∈ PSPACE encIn ↔ ∃ (f : α → Bool) (h : TM2Computable encIn encBool f),
      (∀ stack, Finite (h.tm.Γ stack)) ∧
        (∃ space : α → ℕ, PolyBounded (fun a => (encIn a).length) space ∧
          h.StacksBounded space) ∧ (∀ a, a ∈ A ↔ f a = true) := by
  rw [mem_PSPACE_iff_computableInPolySpace]
  constructor
  · rintro ⟨f, hf, hA⟩
    obtain ⟨h, hfinite, hspace⟩ := hf.exists_tm2Computable
    exact ⟨f, h, hfinite, hspace, hA⟩
  · rintro ⟨f, h, hfinite, ⟨space, hspace, hstacks⟩, hA⟩
    let := hfinite
    exact ⟨f, h.computableInPolySpace hspace hstacks, hA⟩

end Cslib.Complexity
