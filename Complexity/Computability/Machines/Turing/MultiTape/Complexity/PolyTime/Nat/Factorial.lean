/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
public import Mathlib.Data.Nat.Factorial.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Factorials in binary

`n !` is computable in binary from `n` in unary in polynomial time, by multiplying `1, 2, …, n`:
each factor has at most `n` bits, so the running product grows by at most `n` bits per step
(`Turing.MultiTapeTM.ComputableInPolyTime.foldlWith_of_bounded_growth`).

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.binary_factorial`: `n !` in binary.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- `n !` in binary, from `n` in unary, by multiplying `1, 2, …, n`. -/
@[fun_prop]
theorem binary_factorial : ComputableInPolyTime Nat.factorial encUnary encNat := by
  have hfold (n : ℕ) : (List.range n).foldl (fun acc i => acc * (i + 1)) 1 = n.factorial := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
        Nat.factorial_succ, Nat.mul_comm]
  have h := foldlWith_of_bounded_growth (encP := encUnary) (encA := encUnary)
    (encL := encList encUnary) (encB := encNat) (par := id) (list := List.range)
    (init := fun _ => 1) (step := fun (_ : ℕ) acc i => acc * (i + 1))
    id' range (const 1)
    (binary_mul' ((snd _ _).comp (fst _ _))
      (computableTidilyInPolyTime_succ.computableInPolyTime.comp (unary_to_binary.comp (snd _ _))))
    (growth := id)
    (PolyBounded.of_forall_le 1 1 fun n => by simp)
    (fun n acc i hi => by
      rw [encNat_apply, encNat_apply, Nat.size_eq_bits_len, Nat.size_eq_bits_len, id]
      have := Nat.size_mul_le acc (i + 1)
      have := Nat.size_le_self (i + 1)
      have := List.mem_range.1 hi
      omega)
  simpa only [hfold] using h

end Turing.MultiTapeTM.ComputableInPolyTime
