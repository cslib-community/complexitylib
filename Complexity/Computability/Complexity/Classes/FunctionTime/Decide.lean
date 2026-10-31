/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.FunctionTime
public import Complexity.Computability.Complexity.Classes.Time
import Complexity.Computability.Complexity.Classes.FunctionTime.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts

/-!
# Deciding by a polynomial-time test of function-time outputs

A function in `Cslib.Complexity.FTIME enc encOut t` writes its encoded output within time
`O(t n)`, so the output has length `O(t n)` (`Cslib.Complexity.FTIME.exists_computableInO`).
A polynomial-time test of the outputs of two such functions therefore runs within time polynomial
in `t n`: the problem it decides lies in `DTIME[(t + 1) ^ e]` for some `e`. This is how decision
classes defined by counts, such as parity or equality of counts, follow from computing the counts.

## Main results

* `Cslib.Complexity.setOf_mem_DTIME_of_mem_FTIME`: a polynomial-time test of two function-time
  outputs decides a problem in `DTIME[(t + 1) ^ e]`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β β₁ β₂ : Type} {enc : α ↪ List Bool} {t : ℕ → ℕ}

/-- **A polynomial-time test of two function-time outputs.** If `f` and `g` are in `FTIME[t]`
and `rule` is a polynomial-time test of their encoded pair, then the instances where
`rule (f a, g a)` holds form a problem in `DTIME[(t + 1) ^ e]` for some `e`. -/
theorem setOf_mem_DTIME_of_mem_FTIME {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {f : α → β₁} {g : α → β₂} (hf : f ∈ FTIME enc enc₁ t) (hg : g ∈ FTIME enc enc₂ t)
    {rule : β₁ × β₂ → Bool} (hrule : ComputableInPolyTime rule (encPair enc₁ enc₂) encBool) :
    ∃ e, {a | rule (f a, g a) = true} ∈ DTIME enc fun n => (t n + 1) ^ e := by
  obtain ⟨c₁, s₁, h₁, hl₁⟩ := FTIME.exists_computableInO hf
  obtain ⟨c₂, s₂, h₂, hl₂⟩ := FTIME.exists_computableInO hg
  obtain ⟨e, e', hr⟩ := hrule.tidy.exists_degree
  have h := (ComputableInO.of_tidy hr.inO).comp (h₁.prod h₂)
  set c := c₁ + c₂ + 1 with hc
  have hmem := setOf_mem_DTIME_of_computableInO h
    (t := fun n => (2 + (3 * c) ^ e) * (t n + 1) ^ (e + 1)) fun a => by
      have hlen : (encPair enc₁ enc₂ (f a, g a)).length + 1 ≤
          3 * c * (t (enc a).length + 1) := by
        rw [length_encPair]
        have := hl₁ a
        have := hl₂ a
        dsimp only
        rw [hc]
        nlinarith
      have hpow : ((encPair enc₁ enc₂ (f a, g a)).length + 1) ^ e ≤
          (3 * c) ^ e * (t (enc a).length + 1) ^ (e + 1) :=
        calc _ ≤ (3 * c * (t (enc a).length + 1)) ^ e := Nat.pow_le_pow_left hlen e
          _ = (3 * c) ^ e * (t (enc a).length + 1) ^ e := mul_pow _ _ _
          _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ e))
      have ht : t (enc a).length + 1 ≤ (t (enc a).length + 1) ^ (e + 1) :=
        Nat.le_self_pow (Nat.succ_ne_zero e) _
      calc _ ≤ t (enc a).length + t (enc a).length +
            (3 * c) ^ e * (t (enc a).length + 1) ^ (e + 1) := by omega
        _ ≤ _ := by nlinarith
  exact ⟨e + 1, DTIME_mono_of_le_mul_add (C := 2 + (3 * c) ^ e) (fun _ => Nat.le_add_right _ _)
    (by simpa only [Function.comp_apply] using hmem)⟩

end Cslib.Complexity
